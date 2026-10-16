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

## Plan

See `Blueprint.md` (reuse check, route, milestones W1–W12).
