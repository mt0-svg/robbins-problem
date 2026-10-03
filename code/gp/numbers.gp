\\ The numbers of the paper derived from the certificate data, by exact arithmetic.
\\ Run from code/gp: gp -q numbers.gp < /dev/null > numbers.out
\\ Reads the grid file of the run n = 300 (Section 5.1) and the value at time 1 printed by soq.
g = readstr("../soq/out/grid-m5-n300-r1.3-w0.35-14.txt");
num(s) = apply(eval, select(x -> x != "", strsplit(s, " ")));
h = num(g[2]); n = h[1]; m = h[2]; SH = h[3]; K = h[4]; J = h[5];
P = num(g[3]); j = num(g[4]);
Q = 2^SH;
printf("n = %d, m = %d, Q = 2^%d, K = %d, J = %d\n", n, m, SH, K, J);
\\ J is the number of j with 0.35 rho^j < n, rho = 13/10, 0.35 = 7/20
printf("J recomputed: %d\n", #select(i -> 7/20*(13/10)^i < n, [0..60]));
printf("P_j: %d values, increasing in (0,Q): %d\n", #P, P[1] > 0 && P[#P] < Q && vecsort(P) == P && #Set(P) == #P);
printf("j_t: %d values (t = 1..n), nondecreasing: %d, j_n = %d < J: %d\n", #j, vecsort(j) == j, j[n], j[n] < J);
printf("times t < n with j_t = j_(t+1): %d; with j_t < j_(t+1): %d\n", sum(t = 1, n - 1, j[t] == j[t+1]), sum(t = 1, n - 1, j[t] < j[t+1]));
printf("grid states at one time, at most binomial(K+m, m) = %d\n", binomial(K + m, m));
printf("0.35 rho^(K-1) = %.4f\n", 7/20*(13/10)^(K-1));
s = readstr("../soq/out/soq-m5-n300-r1.3-w0.35-14.txt");
l = select(x -> #x > 12 && strsplit(x, " ")[1] == "uhat_1(1..1)", s)[1];
u = eval(strsplit(l, " ")[3]);
printf("u_1 numerator = %d\n", u);
printf("u_1 = %d / 2^%d, floor(10^8 u_1) = %d\n", u, SH, floor(u / Q * 10^8));
printf("2 Q = %d, u_1 numerator > 2 Q: %d\n", 2 * Q, u > 2 * Q);
quit
