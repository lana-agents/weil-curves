# MR3 — Weights: plan (2026-10-16)

Roadmap: `~/iut` origin/main, `Iut/Multiradial/ROADMAP.md` §6.1 MR3: (a) RH for curves over
finite fields, (b) ℓ-adic weight filtration of Δ_X^ab for curves over p-adic fields with
semistable reduction, (c) discharge of the weight hypotheses `hu`, `hl` of
`Iut.Reconstruction.powEquiv_mul_of_weights` (`Iut/Reconstruction/Cusp/Weights.lean:121`).

## Step 0 — reuse check (default branches fetched 2026-10-16)

| where | what exists | usable? |
|---|---|---|
| Mathlib (iut pin, 81a5d257, 2026-07-13) | `FunctionField` (only the def), `RatFunc` valuations (`inftyValuation`), Dedekind/`HeightOneSpectrum`, `Ideal.sum_ramification_inertia_eq_finrank`, `IsIntegralClosure.isDedekindDomain` (**needs separable** ext.), `LocalSubring.exists_le_valuationSubring`, Noether normalisation, `WeierstrassCurve.LFunction` (definition only, `a_p := q+1-#E` with no bound), Gauss/Jacobi sums | infrastructure only. **No** Hasse–Weil, Riemann–Roch, zeta of curves, Jacobians of curves. |
| `elliptic-curves` origin/main | ~140 `FunctionField/*` files: places of `F(W)` and of `F(X)` over **arbitrary** `F` (`RatFunc.valuationSubring_eq_adic_or_infty`, `IsDedekindDomain.exists_valuationSubringAtPrime_eq`), divisor degree-zero theorem for `F(W)`, Weil pairing, Tate modules | elliptic-specific; no Hasse bound (grep: only a comment). Reusable lemmas: classification of valuation subrings over a Dedekind ring. |
| `belyi` origin/main | `Belyi/CurveField/*` (~2.9k lines core): function fields **over ℚ** (`[CharZero K]`) after Stichtenoth Ch. 1: places as valuation subrings, DVR property, residue degrees (Zariski), `ord`, divisors, `deg (x)_0 = [K:ℚ(x)]` (Dedekind chart ring + `sum_ramification_inertia`), `L(A)`, `ℓ(A)` finite, **Riemann's theorem** (`ℓ(A) = deg A − riemannConst` for `deg A` large) | **best starting point**: port with `ℚ` ↦ arbitrary base field `k`. Char-0 use: only (i) Dedekind-ness of chart rings (Mathlib needs separability), (ii) "ℚ-space is no finite union of proper subspaces" (polar-divisor corollaries, not needed). |
| `heights`, `generalized-albanese`, `formal-schemes`, `local-class-field-theory`, `cm-globalization`, `elliptic-reduction` | `GeneralizedJacobian.lean` is an interface-level object; nothing on curves over `F_q` | no |

Conclusion: no Hasse/Hasse–Weil anywhere; the general function-field + Riemann theory exists
only over ℚ (belyi). Mathlib has no Riemann–Roch.

## Route (literature looked up)

Kedlaya, *Weil cohomology* notes ch. 5 (kskedlaya.org/weil-cohom/chapter-5.html) and
van Frankenhuijsen, arXiv:0806.0044 §3 (looked up 2026-10-16):

1. Zeta rationality + functional equation: `Z(T) = P(T)/((1-T)(1-qT))`, `deg P = 2g`,
   `P(0)=1`, leading coeff `q^g`, `α ↦ q/α` symmetry (Kedlaya Prop 5.1.1; vF eq. 2.22, §2.2.5).
   Needs full Riemann–Roch `ℓ(D) − ℓ(W−D) = deg D + 1 − g` (vF: Pellikaan two-variable zeta).
   `#X(F_{q^N}) = q^N + 1 − Σ α_i^N` (Kedlaya Def 5.1.3).
2. Bombieri upper bound (Kedlaya Thm 5.1.5; vF Thm 3.6): `q` a square, `q > (g+1)^4` ⇒
   `#X(F_q) ≤ q + 1 + (2g+1)√q`. RR input: `m+1−g ≤ ℓ(m∞) ≤ m+1`, equality for `m > 2g−2`.
3. Lower bound via Galois closure `Z → X → P^1` and twisted Frobenius counts `N(Z/S,σ)`
   (Kedlaya Lemmas 5.1.7–5.1.9; vF Thm 3.7, 3.8). **A one-sided bound is not enough**
   (vF Lemma 3.1 needs the two-sided bound).
4. Deduction (Kedlaya Lemma 5.1.4; vF Lemma 3.1 + functional equation): two-sided
   `O(q^{dN/2})` bound for all `N` ⇒ `|α_i| = √q`; hence Hasse–Weil `|N − q − 1| ≤ 2g√q`.

Frobenius on `T_ℓ Jac`: the identification `det(1 − Frob T | T_ℓ Jac) = P(T)` needs the
Jacobian (`Jac[ℓ] ≅ (ℤ/ℓ)^{2g}`), absent everywhere; MR3(a) is stated on the reciprocal roots
of the L-polynomial (`P(T) = Π(1 − α_i T)`), with the Tate-module form as a later milestone.

## Milestones (new repo, Mathlib only, same toolchain v4.32.0 / mathlib v4.32.0 as iut)

| # | content | est. lines |
|---|---|---|
| W1 | Function fields `K/k` over an arbitrary field (class `IsFunctionField k K`: `K` finite separable over `k(t)`), places, DVR, residue degree, `ord`, divisors; port of belyi `Basic/Chart/Place/Residue/ZerosPoles` | 1.2k |
| W2 | Degree of principal divisors = 0 (`deg (x)_0 = deg (x)_∞ = [K:k(x)]`) for separating `x`, then all `x` (perfect `k`: `x = h^{p^e}`, `h ∉ K^p` separating) | 1k |
| W3 | `L(A)`, `ℓ(A)`, Riemann's theorem; genus `g := 1 + ... ` via `riemannConst` over the full constant field | 0.8k |
| W4 | Repartitions/Weil differentials, `ι(A) = ℓ(W−A)`, full Riemann–Roch, `deg W = 2g−2` (Stichtenoth 1.5) | 3k |
| W5 | Finite `k = F_q`: finitely many places/effective divisors of each degree, class number, zeta rational, `L`-polynomial `deg 2g`, functional equation, `N_r` formula | 2.5k |
| W6 | Constant field extensions `F_{q^r}K`: genus, `N_1(F_{q^r}K) = Σ_{d∣r} d B_d`, `L_r(T) = Π(1−α_i^r T)` | 2.5k |
| W7 | Bombieri upper bound | 1.5k |
| W8 | Galois closure, `N(Z/S,σ)`, lower bound | 3k |
| W9 | RH `|α_i| = √q`, Hasse–Weil | 0.5k |
| W10 | (MR3a′) Tate module of `Pic⁰(K F̄_q)`, `det(1 − Frob T) = P(T)` | research-size |
| W11 | (MR3b) ℓ-adic weights of `Δ_X^ab` for semistable `X/K_v`: graded pieces weight 0 (graph), 1 (abelian part, via W9 on components), 2 (torus/cusps) | research-size (Raynaud/Grothendieck SGA7 IX) |
| W12 | (MR3c) discharge `hu`, `hl` in iut (consumer edit in iut, not by this repo) | small after W11 |

Total for (a) (W1–W9): ≈ 15–17k lines. (b) needs semistable models and Néron-model/monodromy
theory not available anywhere in the stack; (c) depends on (b).

## Suggested repo name

`lana-agents/weil-curves` (local: `~/weil-curves`, lib `WeilCurves`).

## Session plan

W1–W3 first (port + generalise belyi), committing after each validated increment.
