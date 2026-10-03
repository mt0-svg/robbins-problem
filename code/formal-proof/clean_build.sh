#!/bin/bash
# Clean build of the Lean package: the build directory .lake/build is moved aside and every module of
# Robbins/ and RobbinsSO/ (the data modules that code/formal-proof/gen.sh writes) is compiled again, in dependency
# order. Mathlib keeps its build (from `lake exe cache get` or an earlier build); only the package is compiled.
#
# Order: coreutils tsort of the import lines of the package's modules (imports from outside the package
# dropped), grouped by import depth so that heavy and light modules form long runs. A module is heavy when its
# name contains Check or Place, or is Chain, Final or Main of the run (peaks near 8 GB), its file is over 100 KB (a
# table of RobbinsSO/N300/Data aside: its peak is near 0.5 GB), or it has more than 20 `decide +kernel`. The step
# modules of the run (.Step.S, peaks near 2.5 GB) form a third kind. Each lake call builds up to HB consecutive
# heavy modules, SB consecutive step modules or LB consecutive light ones, all at once; every other module they
# import was built by an earlier call. A failed call is retried module by module; a failure that remains counts.
#
# Memory guard (lake runs one lean process per module it builds; a heavy one peaks near 8 GB): before each call
# MemAvailable must reach the expected peak (PEAK_HEAVY per heavy module, PEAK_STEP per step module, PEAK_LIGHT
# per light call) plus MEM_MARGIN. While short the script polls every MEM_POLL s; after MEM_LOWER s short, a heavy
# or step call loses one module and HB or SB keeps that size for the rest of the run. Every wait goes to
# clean_build.out.
# Disk guard: the run stops when the build filesystem has under MIN_DISK_GB GB free (rerun with RESUME=1).
#
# Knobs (environment), defaults in brackets:
#   RUN_WRAP     command prefix of every lake call, e.g. a memory and CPU cap [empty]
#   LOCK         file held with flock for the whole run [empty: no lock]
#   HB, SB, LB   heavy, step and light modules per call [1, 4, 12]
#   PEAK_HEAVY, PEAK_STEP, PEAK_LIGHT, MEM_MARGIN   sizes with a suffix K, M or G, binary units [9G, 3G, 4G, 4G]
#   MEM_POLL, MEM_LOWER                  seconds [60, 600]
#   MIN_DISK_GB  [8]
#   RESUME=1     continue on the present build directory (not a clean build), appending to the outputs
#   DRY=1        print the header, the calls and the guard decisions (the waits included); no lake call,
#                no lock, nothing moved, no output file written
# Usage: [knobs] code/formal-proof/clean_build.sh, from any directory. The package root is ../.. from this
# directory when it holds lakefile.toml, else ../../lean. Outputs next to this script: clean_build.out (one line
# per lake call with its wall time and memory peak, the waits, the result on the last line) and
# clean_build_modules.txt (lake's "Built M (t)" lines, the time of every module). The old build directory stays
# in .lake/build.prev until a run ends with no failure.
# Exit: 0 all built; 1 setup error; 2 modules failed; 3 stopped on disk space; 130 or 143 interrupted.
set -u
here=$(cd "$(dirname "$0")" && pwd)
if [ -f "$here/../../lakefile.toml" ]; then pkg=$(cd "$here/../.." && pwd); else pkg=$(cd "$here/../../lean" && pwd); fi
[ -f "$pkg/lakefile.toml" ] || { echo "clean_build.sh: no lakefile.toml in ../.. or ../../lean from $here"; exit 1; }
cd "$pkg" || exit 1

HB=${HB:-1}; SB=${SB:-4}; LB=${LB:-12}; PEAK_HEAVY=${PEAK_HEAVY:-9G}; PEAK_STEP=${PEAK_STEP:-3G}; PEAK_LIGHT=${PEAK_LIGHT:-4G}; MEM_MARGIN=${MEM_MARGIN:-4G}
MEM_POLL=${MEM_POLL:-60}; MEM_LOWER=${MEM_LOWER:-600}; MIN_DISK_GB=${MIN_DISK_GB:-8}; RESUME=${RESUME:-0}; DRY=${DRY:-0}
read -r -a wrap <<< "${RUN_WRAP:-}"

kib() { # a size with a suffix K, M or G (binary units), in KiB
  local v=${1%[KkMmGg]}
  [[ $v =~ ^[0-9]+$ ]] || { echo "clean_build.sh: bad size $1" >&2; exit 1; }
  case ${1: -1} in [Kk]) echo "$v";; [Mm]) echo $((v * 1024));; *) echo $((v * 1048576));; esac
}
peak_heavy=$(kib "$PEAK_HEAVY") || exit 1; peak_step=$(kib "$PEAK_STEP") || exit 1; peak_light=$(kib "$PEAK_LIGHT") || exit 1; margin=$(kib "$MEM_MARGIN") || exit 1
gib() { awk -v k="$1" 'BEGIN { printf "%.1f GiB", k / 1048576 }'; }
avail_kib() { awk '/^MemAvailable:/ { print $2 }' /proc/meminfo; }

if [ "$DRY" = 1 ]; then out=/dev/null; mods=/dev/null
else out=$here/clean_build.out; mods=$here/clean_build_modules.txt; fi
tmp=$(mktemp -d)
finished=0
log() { printf '%s\n' "$*" | tee -a "$out"; }
finish() { log "$2"; finished=1; exit "$1"; } # $1 exit code, $2 the last line of clean_build.out
trap 'finish 130 "# result: interrupted (SIGINT); rerun with RESUME=1 to continue"' INT
trap 'finish 143 "# result: interrupted (SIGTERM); rerun with RESUME=1 to continue"' TERM
trap 'rm -rf "$tmp"; [ "$finished" = 1 ] || log "# result: stopped on an unexpected error"' EXIT
clean() { # lake output with the package root and the home directory taken out of paths
  if [ -n "${HOME:-}" ]; then sed -e "s|$pkg/||g" -e "s|$HOME|~|g"; else sed -e "s|$pkg/||g"; fi
}

lean_files() { { find Robbins RobbinsSO -name '*.lean' -type f; [ -f Robbins.lean ] && echo Robbins.lean; } | LC_ALL=C sort; }

import_pairs() { # "dep mod" for every import of a package module by a package module, and "mod mod" for every module
  awk '
    BEGIN { for (i = 1; i < ARGC; i++) { m = ARGV[i]; sub(/\.lean$/, "", m); gsub("/", ".", m); name[ARGV[i]] = m; inpkg[m] = 1; print m, m } }
    FNR == 1 { m = name[FILENAME]; com = 0 }
    com { if (index($0, "-/")) com = 0; next }
    { sub(/^[ \t]+/, "") }
    /^$/ || /^--/ { next }
    /^\/-/ { if (!index(substr($0, 3), "-/")) com = 1; next }
    /^(module|prelude)[ \t]*$/ { next }
    /^((public|private)[ \t]+)?(meta[ \t]+)?import[ \t]/ {
      sub(/--.*/, ""); sub(/^((public|private)[ \t]+)?(meta[ \t]+)?import[ \t]+(all[ \t]+)?/, "")
      if ($1 in inpkg) print $1, m
      next }
    { nextfile }' "$@"
}

module_order() { # "h module" or "l module" (heavy or light), one per line, in build order
  local files
  mapfile -t files < <(lean_files)
  import_pairs "${files[@]}" | LC_ALL=C sort -u > "$tmp/pairs"
  tsort "$tmp/pairs" > "$tmp/tsort" 2> "$tmp/tsort.err" || return 1
  stat -c '%s %n' "${files[@]}" > "$tmp/sizes"
  grep -Hc 'decide +kernel' "${files[@]}" > "$tmp/kernel"
  awk '
    function mod(p) { sub(/\.lean$/, "", p); gsub("/", ".", p); return p }
    FILENAME == ARGV[1] { if ($1 > 100000 && $2 !~ /^RobbinsSO\/N300\/Data\//) heavy[mod($2)] = 1; next }
    FILENAME == ARGV[2] { c = $0; sub(/.*:/, "", c); p = $0; sub(/:[^:]*$/, "", p); if (c + 0 > 20) heavy[mod(p)] = 1; next }
    FILENAME == ARGV[3] { if ($1 != $2) deps[$2] = deps[$2] " " $1; next }
    { m = $1; d = 0; k = split(deps[m], a, " ")
      for (i = 1; i <= k; i++) if (depth[a[i]] + 1 > d) d = depth[a[i]] + 1
      depth[m] = d; s = (m ~ /\.Step\.S/) ? 1 : 0; h = (s || m ~ /Check|Place|^RobbinsSO\.N300\.(Chain|Final)$|^Robbins\.Main$/ || (m in heavy)) ? 1 : 0
      # light before heavy at an even depth, heavy before light at an odd one: runs continue across depths
      print d, (d % 2 ? 1 - h : h), FNR, (s ? "s" : h ? "h" : "l"), m }' "$tmp/sizes" "$tmp/kernel" "$tmp/pairs" "$tmp/tsort" \
    | sort -k1,1n -k2,2n -k3,3n | awk '{ print $4, $5 }'
}

set_hash() { sha256sum "$@" | sha256sum | cut -c1-64; }
header() { # $1 comment prefix
  local c=$1 lf all
  mapfile -t lf < <(lean_files)
  mapfile -t all < <(printf '%s\n' "${lf[@]}" lakefile.toml lake-manifest.json | LC_ALL=C sort)
  echo "$c clean_build.sh at $(date -u '+%F %H:%M') UTC"
  echo "$c $(lean --version 2>&1 | head -1)"
  echo "$c $(lake --version 2>&1 | head -1)"
  echo "$c machine: $(sed -n 's/^model name[[:space:]]*: //p' /proc/cpuinfo | head -1), $(grep -c '^processor' /proc/cpuinfo) logical CPUs, $(gib "$(awk '/^MemTotal:/ { print $2 }' /proc/meminfo)") RAM"
  echo "$c package: ${#lf[@]} modules; sources sha256 $(set_hash "${all[@]}"); Lean sources $(set_hash "${lf[@]}"), lakefile.toml $(sha256sum lakefile.toml | cut -c1-64), lake-manifest.json $(sha256sum lake-manifest.json | cut -c1-64)"
  echo "$c (sha256 of a set of files: that of the sha256sum listing of the files, paths from the package root in LC_ALL=C order; Lean sources: the .lean files of Robbins/ and RobbinsSO/, and Robbins.lean if present)"
}

# The memory peak of a call: the cgroup of the wrapper when it makes one, else ru_maxrss from /usr/bin/time.
inner='p=$1; shift; lake build -v "$@"; r=$?; cg=$(sed -n "s/^0:://p" /proc/self/cgroup); cat "/sys/fs/cgroup$cg/memory.peak" > "$p" 2> /dev/null; exit $r'
peak_method=none
if [ ${#wrap[@]} -gt 0 ]; then
  cg_in=$("${wrap[@]}" bash -c 'cg=$(sed -n "s/^0:://p" /proc/self/cgroup); [ -r "/sys/fs/cgroup$cg/memory.peak" ] && echo "$cg"' 2> /dev/null)
  [ -n "$cg_in" ] && [ "$cg_in" != "$(sed -n 's/^0:://p' /proc/self/cgroup)" ] && peak_method=cgroup
fi
[ $peak_method = none ] && [ -x /usr/bin/time ] && peak_method=rusage
case $peak_method in
  cgroup) peak_what="memory.peak of the cgroup of RUN_WRAP (all processes of the call)";;
  rusage) peak_what="ru_maxrss from /usr/bin/time (the largest single process of the call, a lower bound for the call)";;
  none) peak_what="not recorded (RUN_WRAP makes no cgroup and /usr/bin/time is missing)";;
esac
if [ ${#wrap[@]} -gt 0 ]; then wrap_show="${wrap[0]##*/}${wrap[1]:+ ${wrap[*]:1}}"; else wrap_show=none; fi

if [ -n "${LOCK:-}" ] && [ "$DRY" != 1 ]; then
  exec 9> "$LOCK" || exit 1
  flock -n 9 || { echo "clean_build.sh: waiting for the lock"; flock 9; }
fi
if [ "$DRY" != 1 ] && [ "$RESUME" != 1 ] && [ -e .lake/build.prev ]; then # before the outputs are overwritten
  echo "clean_build.sh: .lake/build.prev exists (an earlier run did not end); rerun with RESUME=1, or remove it"; finished=1; exit 1
fi
hdr=$(header "#")
if [ "$DRY" = 1 ]; then printf '%s\n# DRY=1: no lake call\n' "$hdr"
elif [ "$RESUME" = 1 ]; then printf '%s\n' "$hdr" | tee -a "$out"; printf '%s\n# RESUME=1\n' "$hdr" >> "$mods"
else printf '%s\n' "$hdr" | tee "$out"; printf '%s\n' "$hdr" > "$mods"; fi
log "# settings: HB=$HB SB=$SB LB=$LB PEAK_HEAVY=$PEAK_HEAVY PEAK_STEP=$PEAK_STEP PEAK_LIGHT=$PEAK_LIGHT MEM_MARGIN=$MEM_MARGIN MEM_POLL=$MEM_POLL MEM_LOWER=$MEM_LOWER MIN_DISK_GB=$MIN_DISK_GB; RUN_WRAP: $wrap_show; lock: $([ -n "${LOCK:-}" ] && echo held for the run || echo none)"
log "# memory peak per call: $peak_what"
log "# at start: MemAvailable $(gib "$(avail_kib)"), load average $(cut -d' ' -f1-3 /proc/loadavg)"

mapfile -t order < <(module_order)
[ -s "$tmp/tsort.err" ] && finish 1 "# result: setup error, tsort: $(tr '\n' ' ' < "$tmp/tsort.err" | clean)"
n=${#order[@]}; kind=("${order[@]%% *}"); mod=("${order[@]#* }")
[ "$n" -gt 0 ] || finish 1 "# result: setup error, no module found"

if [ "$DRY" != 1 ]; then
  if [ "$RESUME" = 1 ]; then log "# RESUME=1: continues on the present build directory (not a clean build)"
  elif [ -e .lake/build ]; then mv .lake/build .lake/build.prev || finish 1 "# result: setup error, cannot move .lake/build"; log "# .lake/build moved to .lake/build.prev"
  else log "# no .lake/build before the run"; fi
fi

hb=$HB; sb=$SB; gc=0; gnote=""; ncalls=0; failed=()
need_kib() { case $1 in h) echo $(($2 * peak_heavy + margin));; s) echo $(($2 * peak_step + margin));; *) echo $((peak_light + margin));; esac; }
word() { case $1 in h) echo heavy;; s) echo step;; *) echo light;; esac; }
guard() { # $1 kind (h, s or l), $2 modules in the call; sets gc, the modules to build now (fewer once HB or SB drops)
  local k=$1 need avail t0 ts
  gc=$2; need=$(need_kib "$k" "$gc"); avail=$(avail_kib)
  gnote="$(word "$k") $gc, MemAvailable $(gib "$avail") for a need of $(gib "$need")"
  [ "$avail" -ge "$need" ] && return 0
  t0=$(date +%s); ts=$t0
  log "# wait from $(date -u +%T) UTC: MemAvailable $(gib "$avail"), need $(gib "$need"), $(word "$k") call of $gc"
  while [ "$avail" -lt "$need" ]; do
    if [ $(($(date +%s) - ts)) -ge "$MEM_LOWER" ]; then
      ts=$(date +%s)
      if [ "$k" != l ] && [ "$gc" -gt 1 ]; then
        gc=$((gc - 1)); if [ "$k" = h ]; then hb=$gc; else sb=$gc; fi; need=$(need_kib "$k" "$gc")
        log "# $( [ "$k" = h ] && echo HB || echo SB) lowered to $gc after $MEM_LOWER s short: MemAvailable $(gib "$avail"), need now $(gib "$need")"
        avail=$(avail_kib); continue
      fi
      log "# still short at $(date -u +%T) UTC: MemAvailable $(gib "$avail"), need $(gib "$need")"
    fi
    sleep "$MEM_POLL"; avail=$(avail_kib)
  done
  log "# wait ended at $(date -u +%T) UTC after $(($(date +%s) - t0)) s: MemAvailable $(gib "$avail"), need $(gib "$need"), $(word "$k") call of $gc"
  gnote="$(word "$k") $gc, MemAvailable $(gib "$avail") for a need of $(gib "$need") after a wait"
}

call() { # one lake call on the modules "$@"; true when it built them
  local s r peak free d=.
  [ -d .lake ] && d=.lake
  free=$(df -P -B1G "$d" | awk 'NR == 2 { print $4 }')
  [ "$free" -lt "$MIN_DISK_GB" ] && finish 3 "# result: stopped, $free GB free on the build filesystem (under $MIN_DISK_GB GB) before building $*; rerun with RESUME=1 once there is room"
  ncalls=$((ncalls + 1))
  if [ "$DRY" = 1 ]; then log "call $ncalls ($gnote; $free GB free): $*"; return 0; fi
  rm -f "$tmp/peak"; s=$(date +%s)
  case $peak_method in
    cgroup) "${wrap[@]}" bash -c "$inner" _ "$tmp/peak" "$@";;
    rusage) /usr/bin/time -f %M -o "$tmp/peak" "${wrap[@]}" lake build -v "$@";;
    none) "${wrap[@]}" lake build -v "$@";;
  esac > "$tmp/log" 2>&1
  if [ $? -eq 0 ]; then r=ok; else r=FAILED; fi
  peak=$(tail -1 "$tmp/peak" 2> /dev/null)
  if [[ $peak =~ ^[0-9]+$ ]]; then
    if [ $peak_method = cgroup ]; then peak=$(gib $((peak / 1024))); else peak=$(gib "$peak"); fi
  else peak="not recorded"; fi
  log "$r $(($(date +%s) - s)) s, peak $peak: $*"
  [ $r = ok ] || grep -E 'error|oom|Killed|signal' "$tmp/log" | head -5 | clean | tee -a "$out"
  grep -F '] Built ' "$tmp/log" | clean >> "$mods"
  [ $r = ok ]
}

run() { # $1 kind, then the modules of one call; on failure each module again, alone
  local k=$1 m
  shift
  call "$@" && return
  if [ $# -eq 1 ]; then failed+=("$1"); return; fi
  log "# retry module by module"
  for m in "$@"; do guard "$k" 1; call "$m" || failed+=("$m"); done
}

t0=$(date +%s); i=0; nh=0; ns=0; nl=0
while [ "$i" -lt "$n" ]; do
  k=${kind[i]}
  case $k in h) lim=$hb;; s) lim=$sb;; *) lim=$LB;; esac
  c=0
  while [ $((i + c)) -lt "$n" ] && [ "${kind[i + c]}" = "$k" ] && [ "$c" -lt "$lim" ]; do c=$((c + 1)); done
  guard "$k" "$c"; c=$gc
  case $k in h) nh=$((nh + 1));; s) ns=$((ns + 1));; *) nl=$((nl + 1));; esac
  run "$k" "${mod[@]:i:c}"
  i=$((i + c))
done

log "# done in $((($(date +%s) - t0) / 60)) min: $n modules, $((nh + ns + nl)) batches ($nh heavy, $ns step, $nl light), $ncalls lake calls, ${#failed[@]} modules failed"
[ "$DRY" = 1 ] && finish 0 "# result: dry run, no module built"
if [ ${#failed[@]} -eq 0 ]; then
  [ -e .lake/build.prev ] && rm -rf .lake/build.prev && log "# .lake/build.prev removed"
else log "# .lake/build.prev kept (rerun with RESUME=1 after a fix)"; fi
if [ -d .lake/build ]; then
  find .lake/build -type f -printf '%s %f\n' \
    | awk '{ n = $2; if (!sub(/^[^.]*\./, "", n)) n = "(no suffix)"; s[n] += $1 } END { for (k in s) print s[k], k }' | sort -rn \
    | awk '{ t += $1; l = l sprintf(", %s %.1f MiB", $2, $1 / 1048576) } END { printf "# size of .lake/build: %.1f MiB in all%s\n", t / 1048576, l }' \
    | tee -a "$out"
fi
if [ ${#failed[@]} -eq 0 ]; then finish 0 "# result: ok, all $n modules built"
else finish 2 "# result: FAILED, modules that did not build (${#failed[@]}): ${failed[*]}"; fi
