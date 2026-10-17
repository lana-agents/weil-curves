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
* `Picard`: principal divisors, the divisor class group `Pic k K`, degree and `ℓ` on classes.

Over a finite field `k` (`WeilCurves/FiniteField/`):

* `Finiteness`: finitely many places of degree `≤ d`, finitely many effective divisors of each
  degree.
* `Counting`: if `k` is the full constant field, `#{E ≥ 0 | E ∼ A} · (q − 1) + 1 = q^{ℓ(A)}`.
* `ClassNumber`: each `Cl(n)` is finite, the class number `h = #Cl(0)`, `#Cl(n) = h` when a
  divisor of degree `n` exists, and the number `A_n` of effective divisors of degree `n`
  satisfies `A_n (q − 1) = ∑_{c ∈ Cl(n)} (q^{ℓ(c)} − 1)`, hence
  `A_n (q − 1) = #Cl(n) (q^{n+1−g} − 1)` for `n > 2g − 2`.
* `Zeta`: the zeta function `Z(t) = ∑ A_n t^n ∈ ℤ⟦t⟧`; `ℓ(0) = 1` and `g ≥ 0` for `k` the
  full constant field. **Rationality** (`exists_LPolynomial'`): given a divisor of degree 1
  (discharged by Schmidt's theorem below, `exists_LPolynomial_of_full`),
  `(1 − t)(1 − qt) Z(t) = L(t)` with `L ∈ ℤ[t]` of degree exactly `2g`, `L(0) = 1` and leading
  coefficient `q^g` (computed from `ℓ` on the classes of degree `2g − 2`: `g` for the canonical
  class, `g − 1` for the others).

Constant field extensions (`WeilCurves/ConstantExtension/`):

* `Basic`: a finite extension of a function field over `k` is a function field over `k`
  (`IsFunctionField.of_finite`); an irreducible polynomial over `k` stays irreducible over `K`
  when `k` is the full constant field (`irreducible_map_of_full`); the constant field extension
  `ConstExt k K r = K[X]/(f)` of degree `r` (`f` the minimal polynomial of a primitive element of
  the degree-`r` extension of `k`), with `[ConstExt k K r : K] = r`.
* `ExtPlaces` (for any finite extension `L / K` of function fields): restriction of places,
  `ord_Q x = e(Q) ord_P x`, `deg P ≤ deg Q`, `[L : k(x)] = [L : K][K : k(x)]`, an element whose
  only zero is a given place, and the **fundamental inequality**
  `∑_{Q ∈ S} e(Q) deg Q ≤ [L : K] deg P` for places `Q` above `P`.
* `Split`: Chevalley's extension theorem in the form needed; for `r ∣ deg P`, the `r` embeddings
  of the degree-`r` extension of `k` into `κ(P)` give `r` distinct places of `ConstExt k K r`
  above `P` (via the subring `O_P[θ] ≅ O_P[X]/(f)`), and with the fundamental inequality: **above
  `P` there are exactly `r` places, each of degree `deg P`** (`places_above`).
* `Schmidt`: `A_n ≤ h q^{n − riemannConst}` for large `n` (any function field over a finite
  field); the index `δ` (smallest positive divisor degree); **F. K. Schmidt's theorem**
  `δ = 1` (`index_eq_one`, `exists_deg_eq_one`) by the coefficient-growth argument (two places
  above each place of `K` in `K_δ` give `A'(δm) ≥ (m − c) q^{δm − 2g}`, against `A'(n) ≤ C q^n`);
  hence the **unconditional rationality** of the zeta function (`exists_LPolynomial_of_full`).
* `FiniteField/PlaceCount`: `B_d` (places of degree `d`), `N_r = ∑_{d∣r} d B_d`, and the Euler
  product in the form `n A_n = ∑_{r=1}^n N_r A_{n−r}`, i.e. `t Z'(t) = Z(t) ∑ N_r t^r`
  (`mul_effCount_eq_sum`, `X_mul_derivative_zeta`), proved by counting.
* `FiniteField/Roots`: over `ℂ`, `L(t) = ∏_{i=1}^{2g} (1 − α_i t)` for the reciprocal roots
  `α_i` (`recRoots`, `LPolyC_eq_prod`), `∏ α_i = q^g` (`prod_recRoots`), and
  **`N_r = q^r + 1 − ∑_i α_i^r`** (`pointCount_eq`), by comparing logarithmic derivatives.
* `ConstantExtension/OverKr`: `K_r` is a function field over `k_r` (embedding `k_r → K_r`,
  generator ↦ `θ`); places over `k` and over `k_r` coincide, with `deg_k Q = r · deg_{k_r} Q`.
* `ConstantExtension/Split2`: for `deg P ∣ r`, Chevalley's theorem applied to `O_P[θ] → E`
  (`E ⊇ κ(P)` of degree `r / deg P`) gives at least `deg P` places above `P`; every place of
  `K_r` has degree `≥ r` and `deg(Q|_K) ∣ deg Q`; so **above `P` there are exactly `deg P` places,
  each of degree `r`** (`places_above_of_dvd`), and **`N_r` is the number of places of `K_r` of
  degree one over `k_r`** (`ncard_deg_one_kr`).
* `ConstantExtension/OverKr` (cont.): **`k_r` is the full constant field of `K_r`**
  (`isFullConstantField_constExt`; a primitive element of `k_r(x)` has a minimal polynomial over
  `k` that stays irreducible over `K`, so `[k_r(x) : k] ≤ [K_r : K] = r`).
* `ConstantExtension/Genus`: `k_r` and `K` are linearly disjoint in `K_r`
  (`linearIndependent_constExt`); with the conorm `B' = ∑ e(Q) A(Q|_K) Q`,
  `ℓ_{k_r}(B') ≥ ℓ_k(A)` and `deg_{k_r} B' ≤ deg A` (fundamental inequality), hence
  **`g(K_r) ≤ g(K)`** (`riemannConst_constExt_le`, `genus_constExt_le`).

Bombieri's bound (`WeilCurves/Bombieri/`), after Nivedita (CMI 2009, §3.2.2, Thm 3.6, Lemma 3.7)
and Kedlaya (*Weil cohomology* notes, Thm 5.1.5, Lemma 5.1.7):

* `Automorphism`: a `k`-automorphism `τ` acts on places (`Place.map`), preserving `ord` and
  degrees; `τ L(m Q) ⊆ L(m · τQ)`.
* `PoleOrder`: the set `J` of pole orders at a rational place `α` realised in `L(m α)` has
  `#J ≥ ℓ(m α)`.
* `Bound`: the space of `p^b`-th powers of `L(l α)` (dimension `≥ ℓ(l α)`), `L(A)L(B) ⊆ L(A+B)`,
  and Lemma 3.7 (`∑ g_j^{p^b} h_j^Q ≠ 0` if `l p^b < Q`).
* `Main`: **Bombieri's bound, twisted form** (`bombieri`): for `(g+1)^4 < Q = p^{2b}`, a rational
  place `α`, `τ ∈ Aut_k F` and a finite set `S` of places `β ≠ α, τα` with `x^Q ≡ τ x (mod β)`,
  `∑_{β ∈ S} deg β ≤ Q + (2g + 1) p^b`.

The lower bound and the Riemann hypothesis (`WeilCurves/PointBound/`, `WeilCurves/Galois/`,
`WeilCurves/RH/`), after Nivedita (§3.2.3–3.2.4, eq. 3.4, Prop. 3.8–3.9, Thm. 3.10) and Kedlaya
(Lemmas 5.1.4, 5.1.7–5.1.9), in function-field language (Frobenius *places* instead of
geometric points):

* `PointBound/Upper`: **`N_r ≤ q^r + 1 + (2g + 1) q^{r/2}`** for `q^r = p^{2b} > (g + 1)^4`
  (`pointCount_le`; `bombieri` on `K_r / k_r` with `τ = id`).
* `Galois/Frobenius`: for `M / k(x)` Galois and a place `β ∋ x` with `x^{q^n} ≡ x (mod β)`, a
  **Frobenius element** `σ ∈ Gal(M / k(x))` with `y^{q^n} ≡ σ y (mod β)` on `O_β`
  (`exists_frobenius_place`; Mathlib's `Ideal.Quotient.stabilizerHom_surjective` on the chart
  ring).
* `Galois/Ramification`: a nonzero `δ ∈ k[x]` with `ord_β(x^Q − x) ≤ ord_β δ` whenever
  `ord_β(x^Q − x) ≥ 2` (`exists_ramification_bound`; Mathlib's different ideal instead of
  Riemann–Hurwitz).
* `Galois/BaseField`: places over `k` and over a finite `k' ⊇ k`, `deg_k = [k' : k] deg_{k'}`;
  `∑_{zeros} ord(t^Q − t) deg = Q [M : k(t)]`.
* `Galois/Count`: **the twisted count** (`pointCount_ge_of_galois`): for `M ⊇ F` Galois over
  `k'(x)` and over `F`, `k'` the full constant field of `M` with a rational place,
  `N_{dm}(F) ≥ Q − (|G| − 1)((2g(M) + 1)√Q + 2) − C` for `Q = |k'|^m = p^{2b} > (g(M) + 1)^4`.
* `Galois/Closure`: the construction (separating element, splitting field `M₁`, its constant
  field `k₁`, `M = ConstExt k₁ M₁ D` with a rational place, Galois over `F` and `k'(x)`) and
  **`exists_lower_bound`**.
* `RH/RootTest`: Kedlaya's Lemma 5.1.4 as an algebraic root test for power sums.
* `RH/Conditional`, `RH/Main`: **the Riemann hypothesis `|α_i| = √q`** (`riemannHypothesis`)
  and **the Hasse–Weil bound `|N_r − q^r − 1| ≤ 2g q^{r/2}`** (`hasseWeil`).

## Plan

See `Blueprint.md` (reuse check, route, milestones W1–W12).
