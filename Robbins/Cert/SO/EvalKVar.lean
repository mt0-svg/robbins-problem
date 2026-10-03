import Robbins.Cert.SO.EvalKChain
import Robbins.Cert.SO.EvalKCtx

/-!
# The states of a kernel step and their record lists

`checkStep g t Nn Nt` runs `checkState` on the states of `Y_t` in rank order (`states`), against
the decoded states of `Nt`, and `checkState` runs `checkVar` on every record list of section 6
built from the state (`variants`). Here:

* `lkOf_rank`: at the rank of a state of `G_{t+1}`, the lookup reads the decoded state of `Nn`;
* `checkStep_states`: a passed step gives `TableOK` of `Nt`, and for every state `k` of `G_t` and
  every valid choice `x`, the check `checkVar` of the claimed state `k` against the record list
  `recList DS g t k x`.
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-! ## The states of a step in rank order -/

theorem lmapIdx_snoc {α β : Type} (f : ℕ → α → β) (k : ℕ) (xs : List α) (y : α) :
    lmapIdx f k (xs ++ [y]) = lmapIdx f k xs ++ [f (k + xs.length) y] := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    show f k x :: lmapIdx f (k + 1) (xs ++ [y]) = (f k x :: lmapIdx f (k + 1) xs) ++ _
    rw [ih, List.cons_append, List.length_cons, show k + 1 + xs.length = k + (xs.length + 1) by ring]

theorem lmapIdx_congr {α β : Type} (f f' : ℕ → α → β) (k : ℕ) (xs : List α)
    (h : ∀ j, j < k + xs.length → ∀ a, f j a = f' j a) : lmapIdx f k xs = lmapIdx f' k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    show f k x :: lmapIdx f (k + 1) xs = f' k x :: lmapIdx f' (k + 1) xs
    rw [h k (by simp) x, ih (k + 1) (fun j hj a => h j (by simp at hj ⊢; omega) a)]

/-- The states of `Y_t` in rank order: the sorted `(k + 2)`-tuples over the records, the last
record the largest entry and the prefix the others. -/
theorem states_tupG (f : List SR → Pre) (k : ℕ) (recs : List SR) (a : SR) :
    states recs (lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k recs)) =
      (tupR (k + 2) recs).map (fun tp => (f tp.tail.reverse, tp.headD a)) := by
  induction recs using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    unfold states at ih ⊢
    have hPG : lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k (ys ++ [y])) =
        lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k ys) ++
          [(tupR k (ys ++ [y])).map (fun tp => f (y :: tp).reverse)] := by
      rw [tupG_snoc, lmap_eq, lmap_eq, List.map_append, List.map_singleton, lmap_eq, List.map_map]
      congr 2
      refine List.map_congr_left (fun tp _ => ?_)
      simp [lrevOnto_eq]
    have hlen : (lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k ys)).length = ys.length := by
      rw [lmap_eq, List.length_map, tupG_length]
    rw [hPG, lmapIdx_snoc, lflat_eq, List.flatten_append, ← lflat_eq]
    rw [lmapIdx_congr _ (fun j r => lmap (fun p => (p, r))
      (lflat (ltake (Nat.succ j) (lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k ys))))) 0 ys
      (fun j hj r => by
        rw [ltake_eq, ltake_eq, List.take_append_of_le_length (by rw [hlen]; omega)])]
    rw [ih, tupR_snoc, List.map_append]
    congr 1
    have hfun : lmap (fun tp => f (lrevOnto tp [])) = List.map (fun tp => f (lrevOnto tp [])) :=
      funext (lmap_eq _)
    rw [← hPG]
    simp only [hfun, lmap_eq, lflat_eq, ltake_eq, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [List.take_of_length_le (by simp [tupG_length])]
    rw [← List.map_flatten, ← tupR_succ, List.map_map, List.map_map]
    refine List.map_congr_left (fun tp _ => ?_)
    simp [lrevOnto_eq]

theorem lkF_eq (f : ℕ → SV) (idx : ℕ) : lkF f idx = f idx := by
  cases idx <;> rfl

theorem decAll_length_le (d : ℕ) (T : List ℕ) : (decAll d T).length ≤ 16 * T.length := by
  unfold decAll
  induction T with
  | nil => simp [lfoldr]
  | cons x xs ih =>
    show (decLit (Wd d) (2 ^ Wd d - 1) x (lfoldr (decLit (Wd d) (2 ^ Wd d - 1)) [] xs)).length ≤ _
    rw [decLit_append, List.length_append, List.length_cons]
    have := decLit_length_le (Wd d) (2 ^ Wd d - 1) x
    omega

/-! ## The record lists of section 6 -/

theorem lall_iff {α : Type} (p : α → Bool) (l : List α) : lall p l = true ↔ ∀ v ∈ l, p v = true := by
  induction l with
  | nil => simp [lall]
  | cons a l ih =>
    show bsel (p a) (lall p l) false = true ↔ _
    rw [bsel_eq]
    by_cases ha : p a = true
    · simp [ha, ih]
    · simp [ha]

theorem nfg_split (cs : List SR) (a : ℕ) (ha : a ≤ cs.length)
    (h1 : ∀ i (hi : i < cs.length), i < a → cs[i].fg = false)
    (h2 : ∀ i (hi : i < cs.length), a ≤ i → cs[i].fg = true) : nfg cs = cs.length - a := by
  induction cs generalizing a with
  | nil => simp at ha; subst ha; rfl
  | cons r cs ih =>
    show bsel r.fg (Nat.succ (nfg cs)) (nfg cs) = _
    rw [bsel_eq]
    cases a with
    | zero =>
      have hr : r.fg = true := h2 0 (by simp) le_rfl
      simp only [hr, ↓reduceIte]
      rw [ih 0 (by simp) (fun i _ hi => absurd hi (by omega))
        (fun i hi _ => h2 (i + 1) (by simp; omega) (by omega))]
      simp
    | succ a =>
      have hr : r.fg = false := h1 0 (by simp) (by omega)
      simp only [hr, Bool.false_eq_true, ↓reduceIte]
      rw [ih a (by simp at ha; omega)
        (fun i hi hia => h1 (i + 1) (by simp; omega) (by omega))
        (fun i hi hia => h2 (i + 1) (by simp; omega) (by omega))]
      simp

theorem idxOf_mono {l : List ℕ} (hl : l.Pairwise (· < ·)) {v w : ℕ} (hv : v ∈ l) (hw : w ∈ l)
    (hvw : v ≤ w) : l.idxOf v ≤ l.idxOf w := by
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  have hvl := List.idxOf_lt_length_of_mem hv
  have hwl := List.idxOf_lt_length_of_mem hw
  have := List.pairwise_iff_getElem.1 hl _ _ hwl hvl hlt
  rw [List.getElem_idxOf, List.getElem_idxOf] at this
  omega

theorem ofFn_castSucc_append {α : Type} {d : ℕ} (R : Fin (d + 1) → α) :
    List.ofFn (fun l : Fin d => R l.castSucc) ++ [R (Fin.last d)] = List.ofFn R := by
  rw [List.ofFn_succ', List.concat_eq_append]

theorem take_ofFn_castSucc {α : Type} {d : ℕ} (R : Fin (d + 1) → α) :
    (List.ofFn R).take d = List.ofFn (fun l : Fin d => R l.castSucc) := by
  rw [← ofFn_castSucc_append R, List.take_append_of_le_length (by simp)]
  simp

theorem getLastD_ofFn {α : Type} {d : ℕ} (R : Fin (d + 1) → α) (a : α) :
    (List.ofFn R).getLastD a = R (Fin.last d) := by
  rw [← ofFn_castSucc_append R, List.getLastD_eq_getLast?, List.getLast?_concat]
  rfl

theorem variants_eq (c : Ctx) (lk : ℕ → SV) (p : Pre) (top : SR) :
    variants c lk p top = if top.fg = true ∧ c.newp ≠ [] then
      variants.variants1 c lk (p.rs ++ [top]) (nfg (p.rs ++ [top])) else [(p, top)] := by
  unfold variants
  rw [bsel_eq, bsel_eq, lapp_eq]
  cases top.fg <;> cases c.newp <;> simp

theorem newPts_pairwise (g : Grid) (t : ℕ) : (newPts g t).Pairwise (· < ·) :=
  List.Pairwise.filter _ (List.pairwise_lt_range)

theorem newPts_lt (g : Grid) (t j : ℕ) (hj : j ∈ newPts g t) : j < g.J := by
  unfold newPts at hj
  rw [List.mem_filter, List.mem_range] at hj
  exact hj.1

theorem mem_variants (g : Grid) (hg : ok DS g = true) {d : ℕ} (hd : g.m = d + 1) {t : ℕ} (ht1 : 1 ≤ t)
    (htn : t < g.n) (lk : ℕ → SV) (k : Fin (d + 1) → ℕ) (hk : g.IsState t k) (x : Fin (d + 1) → ℕ)
    (hx : ValidChoice g t x) :
    (mkPre (mkCtx g t) lk (List.ofFn fun l : Fin d => toSR g t (recList DS g t k x l.castSucc)),
      toSR g t (recList DS g t k x (Fin.last d))) ∈
    variants (mkCtx g t) lk
      (mkPre (mkCtx g t) lk (List.ofFn fun l : Fin d => toSR g t (locRec DS g t (k l.castSucc))))
      (toSR g t (locRec DS g t (k (Fin.last d)))) := by
  have hnewp := mkCtx_newp g hg ht1 htn
  set c := mkCtx g t with hc
  set NP := newPts g t with hNP
  set R : Fin (d + 1) → SR := fun l => toSR g t (locRec DS g t (k l)) with hR
  set Rx : Fin (d + 1) → SR := fun l => toSR g t (recList DS g t k x l) with hRx
  have hRfg : ∀ l, (R l).fg = decide (k l = g.cnt t) := fun l => rfl
  have hklast : ∀ l, k l ≤ k (Fin.last d) := fun l => hk.1 (Fin.le_last l)
  rw [variants_eq]
  change (mkPre c lk (List.ofFn fun l : Fin d => Rx l.castSucc), Rx (Fin.last d)) ∈
    if (R (Fin.last d)).fg = true ∧ c.newp ≠ [] then
      variants.variants1 c lk (List.ofFn (fun l : Fin d => R l.castSucc) ++ [R (Fin.last d)])
        (nfg (List.ofFn (fun l : Fin d => R l.castSucc) ++ [R (Fin.last d)]))
    else [(mkPre c lk (List.ofFn fun l : Fin d => R l.castSucc), R (Fin.last d))]
  rw [ofFn_castSucc_append R]
  by_cases hcase : (R (Fin.last d)).fg = true ∧ c.newp ≠ []
  · simp only [hcase, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    obtain ⟨hfg, hne⟩ := hcase
    have hkl_eq : k (Fin.last d) = g.cnt t := by simpa [hRfg] using hfg
    have hex : ∃ i, ∃ h : i < d + 1, k ⟨i, h⟩ = g.cnt t := ⟨d, by omega, hkl_eq⟩
    classical
    set a := Nat.find hex with ha_def
    obtain ⟨ha_lt, ha_k⟩ : ∃ h : a < d + 1, k ⟨a, h⟩ = g.cnt t := Nat.find_spec hex
    have hk_iff : ∀ l : Fin (d + 1), k l = g.cnt t ↔ a ≤ (l : ℕ) := by
      intro l
      constructor
      · intro h; exact Nat.find_min' hex ⟨l.isLt, h⟩
      · intro h
        have h1 : k ⟨a, ha_lt⟩ ≤ k l := hk.1 (Fin.mk_le_of_le_val h)
        have h2 := hk.2 l
        omega
    have hnfg : nfg (List.ofFn R) = d + 1 - a := by
      rw [nfg_split (List.ofFn R) a (by simp; omega) ?_ ?_]
      · simp
      · intro i hi hia
        rw [List.getElem_ofFn, hRfg]
        simp only [decide_eq_false_iff_not]
        rw [hk_iff]; simp; omega
      · intro i hi hia
        rw [List.getElem_ofFn, hRfg]
        simp only [decide_eq_true_eq]
        rw [hk_iff]; simpa using hia
    rw [hnfg]
    unfold variants.variants1
    rw [lmap_eq, List.mem_map, llast_eq, getLastD_ofFn, lapp_eq]
    set idxN : ℕ → ℕ := fun v => if v ∈ NP then NP.idxOf v else NP.length with hidxN
    have hidxN_le : ∀ v, idxN v ≤ NP.length := by
      intro v
      simp only [hidxN]
      split_ifs with h
      · exact (List.idxOf_lt_length_of_mem h).le
      · exact le_rfl
    have hidxN_mono : ∀ v w, (v ∈ NP ∨ v = g.J) → (w ∈ NP ∨ w = g.J) → v ≤ w → idxN v ≤ idxN w := by
      intro v w hv hw hvw
      by_cases hwN : w ∈ NP
      · have hwJ := newPts_lt g t w hwN
        have hvN : v ∈ NP := by
          rcases hv with hv | hv
          · exact hv
          · omega
        simp only [hidxN, hvN, hwN, ↓reduceIte]
        exact idxOf_mono (newPts_pairwise g t) hvN hwN hvw
      · have : idxN w = NP.length := by simp only [hidxN, hwN, ↓reduceIte]
        rw [this]
        exact hidxN_le v
    set y : Fin (d + 1 - a) → ℕ := fun i => idxN (x ⟨a + i, by omega⟩) with hy
    have hy_mono : Monotone y := by
      intro i j hij
      exact hidxN_mono _ _ (hx.2 _) (hx.2 _) (hx.1 (Fin.mk_le_mk.2 (by
        have := Fin.le_def.1 hij; omega)))
    have hy_le : ∀ i, y i ≤ NP.length := fun i => hidxN_le _
    set ys := c.newp ++ [R (Fin.last d)] with hys
    have hnp_len : c.newp.length = NP.length := by rw [hnewp, List.length_map]
    have hys_len : ys.length = NP.length + 1 := by rw [hys, List.length_append, hnp_len]; rfl
    have hrank : rank y < (tupR (d + 1 - a) ys).length := by
      rw [tupR_length, hys_len]
      have := rank_lt y hy_mono NP.length hy_le
      have e : NP.length + 1 + (d + 1 - a) - 1 = NP.length + (d + 1 - a) := by omega
      rw [e]; exact this
    refine ⟨(tupR (d + 1 - a) ys).getD (rank y) [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hrank]; exact List.getElem_mem _
    · rw [tupR_getD_rank (d + 1 - a) ys (R (Fin.last d)) y hy_mono
        (fun i => by rw [hys_len]; have := hy_le i; omega), lrevOnto_eq, List.append_nil,
        List.reverse_reverse, ltake_eq, lapp_eq]
      have hm : Nat.sub c.m (d + 1 - a) = a := by
        show g.m - (d + 1 - a) = a
        rw [hd]; omega
      rw [hm]
      have hta : ((List.ofFn R).take a).length = a := by
        rw [List.length_take, List.length_ofFn]; omega
      have hlist : (List.ofFn R).take a ++ (List.ofFn y).map (fun i => ys.getD i (R (Fin.last d))) =
          List.ofFn Rx := by
        apply List.ext_getElem
        · rw [List.length_append, hta, List.length_map, List.length_ofFn, List.length_ofFn]; omega
        · intro i h1 h2
          rw [List.getElem_ofFn]
          by_cases hia : i < a
          · rw [List.getElem_append_left (by rw [hta]; exact hia), List.getElem_take, List.getElem_ofFn]
            simp only [hR, hRx, recList]
            rw [ite_eq_right_iff.2]
            rintro ⟨hki, _⟩
            rw [hk_iff] at hki
            exact absurd hki (by simp; omega)
          · rw [List.getElem_append_right (by rw [hta]; omega)]
            simp only [List.getElem_map, List.getElem_ofFn, hta]
            have hi' : i < d + 1 := by rw [List.length_ofFn] at h2; exact h2
            have hxe : ∀ (j : ℕ) (hj : j < d + 1), j = i → x ⟨j, hj⟩ = x ⟨i, hi'⟩ := by
              rintro j hj rfl; rfl
            have hyi : y ⟨i - a, by omega⟩ = idxN (x ⟨i, hi'⟩) := by
              simp only [hy]
              rw [hxe _ _ (by omega)]
            rw [hyi]
            have hki : k ⟨i, hi'⟩ = g.cnt t := (hk_iff _).2 (by simp; omega)
            by_cases hxN : x ⟨i, hi'⟩ ∈ NP
            · have hidx : idxN (x ⟨i, hi'⟩) = NP.idxOf (x ⟨i, hi'⟩) := by
                simp only [hidxN, hxN, ↓reduceIte]
              have hlt := List.idxOf_lt_length_of_mem hxN
              rw [hidx, hys, List.getD_append _ _ _ _ (by rw [hnp_len]; exact hlt),
                List.getD_eq_getElem _ _ (by rw [hnp_len]; exact hlt)]
              simp only [hnewp, List.getElem_map, List.getElem_idxOf, hRx, recList]
              rw [ite_eq_left ⟨hki, hxN⟩]
            · have hidx : idxN (x ⟨i, hi'⟩) = NP.length := by
                simp only [hidxN, hxN, ↓reduceIte]
              rw [hidx, hys, List.getD_append_right _ _ _ _ (by rw [hnp_len]), hnp_len, Nat.sub_self]
              simp only [List.getD_cons_zero, hR, hRx, recList]
              rw [ite_eq_right_iff.2 (fun h => absurd h.2 hxN), hki, hkl_eq]
      rw [hlist]
      show (mkPre c lk (ltake (Nat.sub c.m 1) (List.ofFn Rx)), llast _ (List.ofFn Rx)) = _
      rw [ltake_eq, llast_eq, getLastD_ofFn, show Nat.sub c.m 1 = d by
        show g.m - 1 = d
        rw [hd]; rfl, take_ofFn_castSucc]
  · simp only [hcase, ↓reduceIte, List.mem_singleton]
    have hrl : ∀ l, Rx l = R l := by
      intro l
      simp only [hRx, hR, recList]
      rw [ite_eq_right_iff.2]
      rintro ⟨hkl, hxl⟩
      exfalso
      apply hcase
      refine ⟨?_, ?_⟩
      · rw [hRfg]; have := hklast l; have := hk.2 (Fin.last d); simp; omega
      · rw [hnewp]; intro hnil; rw [List.map_eq_nil_iff] at hnil; rw [← hNP, hnil] at hxl; simp at hxl
    simp only [hrl]

/-! ## The step -/

variable (g : Grid)

/-- At the rank of a state `H` of `G_{t+1}`, the lookup reads the decoded state of `Nn`. -/
theorem lkOf_rank {d : ℕ} (hd : g.m = d + 1) {t : ℕ} {Nn : List ℕ} (hNn : TableOK g d (t + 1) Nn)
    {H : Fin (d + 1) → ℕ} (hH : g.IsState (t + 1) H) :
    lkOf g Nn (rank H) = ⟨stOf d Nn H % 2 ^ 48, slopes g.m (stOf d Nn H)⟩ := by
  obtain ⟨hlen, hget⟩ := hNn
  have hr : rank H < (decAll d Nn).length := by
    rw [hlen]
    have := rank_lt H hH.1 (g.cnt (t + 1)) hH.2
    simpa [add_assoc] using this
  have hdl := decAll_length_le d Nn
  have hn1 : 1 ≤ Nn.length := by omega
  have hdep := depth_spec Nn.length hn1
  have hidx : rank H / 16 < 2 ^ depth Nn.length := by
    have : rank H / 16 < Nn.length := by omega
    omega
  unfold lkOf
  rw [lkF_eq, shiftLeft_one_sub_one, Wd_eq_mul g hd]
  show lk0.lk1 g.m (lkSt (bld (depth Nn.length) Nn) (depth Nn.length) (Wd d) (2 ^ Wd d - 1) (rank H)) = _
  rw [lkSt_eq _ _ Nn hdep (rank H) hidx, ← hget _ hr]
  show SV.mk (Nat.land _ M48) (slopes g.m _) = _
  rw [land_M48]
  rfl

/-- A passed step: the table `Nt` has the shape of `G_t`, and every state `k` of `G_t` passes
`checkVar` against the record list of every valid choice `x`. -/
theorem checkStep_states (hg : ok DS g = true) {d : ℕ} (hd1 : 1 ≤ d) (hd : g.m = d + 1) {t : ℕ}
    (ht1 : 1 ≤ t) (htn : t < g.n) {Nn Nt : List ℕ} (h : checkStep g t Nn Nt = true) :
    TableOK g d t Nt ∧ ∀ k : Fin (d + 1) → ℕ, g.IsState t k → ∀ x : Fin (d + 1) → ℕ,
      ValidChoice g t x →
      checkVar (mkCtx g t) (lkOf g Nn) (uhOf d Nt k) (slopes g.m (stOf d Nt k))
        (mkPre (mkCtx g t) (lkOf g Nn)
          (List.ofFn fun l : Fin d => toSR g t (recList DS g t k x l.castSucc)))
        (toSR g t (recList DS g t k x (Fin.last d))) = true := by
  have hrecs := mkCtx_recs g hg ht1 htn
  rw [checkStep_eq, shiftLeft_one_sub_one, Wd_eq_mul g hd] at h
  set c := mkCtx g t with hc
  set lk := lkOf g Nn with hlk
  set dflt : SR := SR.mk 0 0 0 0 true 0 0 0 0 [] 0
  set F : List SR → Pre × SR := fun tp => (mkPre c lk tp.tail.reverse, tp.headD dflt) with hF
  have hst : states c.recs (lmap (lmap fun tp => mkPre c lk (lrevOnto tp [])) (tupG (Nat.sub g.m 2) c.recs)) =
      (tupR (d + 1) c.recs).map F := by
    rw [states_tupG _ _ _ dflt]
    congr 2
    show g.m - 2 + 2 = d + 1
    omega
  rw [hst] at h
  obtain ⟨hall, halign⟩ := chunkCheck_aligned _ (Wd d) (by simp [Wd]) Nt _ h
  change lall2 _ _ (decAll d Nt) = true at hall
  obtain ⟨hlen, hpair⟩ := (lall2_iff _ _ _).1 hall
  have hrecs_len : c.recs.length = g.cnt t + 1 := by rw [hrecs, List.length_map, List.length_range]
  have hstlen : ((tupR (d + 1) c.recs).map F).length = (g.cnt t + d + 1).choose (d + 1) := by
    rw [List.length_map, tupR_length, hrecs_len]
    congr 1
    omega
  have hTab : TableOK g d t Nt :=
    ⟨by rw [← hlen, hstlen], fun idx hidx => halign idx (by rw [hlen]; exact hidx)⟩
  refine ⟨hTab, fun k hk x hx => ?_⟩
  have hrk : rank k < ((tupR (d + 1) c.recs).map F).length := by
    rw [hstlen]
    have := rank_lt k hk.1 (g.cnt t) hk.2
    simpa [add_assoc] using this
  have hck := hpair (rank k) hrk (by rw [← hlen]; exact hrk)
  set R : Fin (d + 1) → SR := fun l => toSR g t (locRec DS g t (k l)) with hR
  have htp : (tupR (d + 1) c.recs)[rank k]'(by simpa using hrk) = (List.ofFn R).reverse := by
    rw [← List.getD_eq_getElem _ [], tupR_getD_rank (d + 1) c.recs dflt k hk.1
      (fun l => by rw [hrecs_len]; have := hk.2 l; omega), List.map_ofFn]
    congr 2
    funext l
    simp only [Function.comp, hR, hrecs]
    rw [List.getD_eq_getElem _ _ (by simp; have := hk.2 l; omega), List.getElem_map, List.getElem_range]
  rw [List.getElem_map, htp] at hck
  have hF' : F (List.ofFn R).reverse = (mkPre c lk (List.ofFn fun l : Fin d => R l.castSucc), R (Fin.last d)) := by
    rw [hF, ← ofFn_castSucc_append R, List.reverse_append]
    simp
  rw [hF'] at hck
  have hdec : (decAll d Nt)[rank k]'(by rw [← hlen]; exact hrk) = stOf d Nt k := by
    rw [stOf, List.getD_eq_getElem]
  rw [hdec] at hck
  unfold checkState at hck
  rw [lall_iff] at hck
  have hv := hck _ (mem_variants g hg hd ht1 htn lk k hk x hx)
  rw [land_M48] at hv
  exact hv

end Robbins.Cert.SO.K
