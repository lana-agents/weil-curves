# weil-curves

The Riemann hypothesis for curves over finite fields (Weil), formalised along the elementary
route of Stepanov–Bombieri, as input for the weights in the multiradial algorithm of
IUT III, Theorem 3.11 (roadmap item **MR3** of the `iut` repository,
`Iut/Multiradial/ROADMAP.md` §6.1).

## Route

Algebraic function fields of one variable over a field `k` (Stichtenoth, *Algebraic Function
Fields and Codes*, Ch. 1), generalising the theory over `ℚ` of the `belyi` repository
(`Belyi/CurveField/`) to an arbitrary (perfect) base field; Riemann–Roch; over `k = F_q` the
zeta function, its rationality and functional equation; Bombieri's upper bound
`#X(F_q) ≤ q + 1 + (2g+1)√q` for square `q > (g+1)^4`; the lower bound via Galois covers; and
the deduction `|α_i| = √q` for the reciprocal roots of the `L`-polynomial (Kedlaya, *Weil
cohomology* notes, §5.1; van Frankenhuijsen, arXiv:0806.0044, §3).

## Status

No `sorry`, no `axiom`. Proved so far (`WeilCurves/FunctionField/`):

* `Basic`: the class `IsFunctionField k K` (`K` finite over `k(t)`, `t` transcendental);
  `K` is finite over `k(s)` for *every* transcendental `s`; transcendence degree one.
* `Chart`: the chart ring `A_t = chartRing k t` (integral closure of `k[t]` in `K`).
  **Over a perfect field `k`, `A_t` is finite over `k[t]` and a Dedekind domain for every
  transcendental `t`** (`finite_chartRing`), also when `K / k(t)` is inseparable: the
  `q = p^e`-th power map sends `A_t` into the integral closure of `k[t]` in the separable
  closure of `k(t)`, and `k[t^q]` is the image of `k[t]` because `k` is perfect.
* `Place`: places (valuation subrings `O ⊊ K` containing `k`), their description by the
  charts (`Place.chartEquiv`), the DVR property, the normalised order `Place.ord` and its laws.
* `Residue`: residue fields `κ(P)`, finite over `k` (Zariski), the degree
  `Place.deg P = [κ(P) : k]`.
* `ZerosPoles`: a transcendental element has a zero and a pole; finitely many zeros and poles;
  the constants are the elements lying in every place.
* `Degree`: `∑_{ord_P t > 0} ord_P(t) deg P = [K : k(t)]` and the same for the poles, for every
  transcendental `t` (`Place.sum_ord_mul_deg_zeros`, `Place.sum_ord_mul_deg_poles`).
* `Divisor`: divisors, degree, principal divisors `div k f`, and **`deg (div k f) = 0`**
  (`Divisor.deg_div`).
* `RiemannRochSpace`: `L(A)` and `ℓ(A) = dim_k L(A)` (finite), invariance under linear
  equivalence, `ℓ(A) = 0` for `deg A < 0`, `ℓ(A) ≤ max 0 (deg A + ℓ(0))`, `ℓ(0) = [k' : k]`.
* `Riemann`: **Riemann's theorem** — `deg A − ℓ(A)` is bounded above with maximum
  `Divisor.riemannConst k K`, and `ℓ(A) = deg A − riemannConst k K` for `deg A` large
  (`Divisor.riemann_equality`).
* `LinearAlgebra/RelRank`: relative ranks `dim (X + Y)/Y` of subspaces of an arbitrary
  (possibly infinite-dimensional) vector space: additivity along chains and
  `dim X/Y = dim (X+D)/(Y+D) + dim (X∩D)/(Y∩D)`.
* `Adeles`: repartitions `A_K`, the subspaces `A_K(A)`, `A_K(A) ∩ K = L(A)`,
  `dim A_K(A + D)/A_K(A) = deg D` for `D ≥ 0`, and
  `dim (A_K(B) + K)/(A_K(A) + K) = (deg B − ℓ(B)) − (deg A − ℓ(A))` for `A ≤ B`.
* `Specialty`: `A_K = A_K(B) + K` for `B` of large degree; the **index of specialty**
  `i(A) = dim A_K/(A_K(A) + K)` is finite and **`ℓ(A) − i(A) = deg A − riemannConst k K`**
  (`Divisor.ell_sub_iSpec`).
* `WeilDifferential`: functionals on `A_K`, the spaces `Ω(A)` with `dim Ω(A) = i(A)`, the
  action of `K`, `Ω(A) ∩ Ω(B) ⊆ Ω(A ⊔ B)`.
* `RiemannRoch`: the Weil differentials form a **one-dimensional `K`-space**
  (`exists_smulW_eq`); divisors of Weil differentials with `(x ω) = (x) + (ω)`; a canonical
  divisor `W`, `i(A) = ℓ(W − A)`, and the **Riemann–Roch theorem**
  `ℓ(A) − ℓ(W − A) = deg A + 1 − g` (`riemannRoch`), with `g = riemannConst k K + 1`;
  `deg W = 2g − 2`, `ℓ(W) = ℓ(0) + g − 1`, and `ℓ(A) = deg A + 1 − g` for `deg A > 2g − 2`.

## Plan

See `Blueprint.md` (reuse check, route, milestones W1–W12).
