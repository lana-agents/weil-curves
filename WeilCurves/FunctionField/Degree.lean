/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.ZerosPoles
import WeilCurves.FunctionField.Residue
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# The degree of the divisor of zeros (and of poles) of a function

For `t` in a function field `K`, transcendental over `k`,
`∑_{P, ord_P t > 0} ord_P(t) · deg P = [K : k(t)]` and likewise for the poles
(`WeilCurves.FunctionField.Place.sum_ord_mul_deg_zeros`,
`WeilCurves.FunctionField.Place.sum_ord_mul_deg_poles`).

This is the fundamental identity `∑ e f = [L : K]` for the Dedekind extension
`k[t] ⊆ A_t` at the prime `(t)` (Mathlib's `Ideal.sum_ramification_inertia`), translated to
places via the chart description: at a place `P = ofChart t v`, the order `ord_P` is the
`v`-adic valuation (`WeilCurves.FunctionField.Place.ord_ofChart`), and `κ(P) ≅ A_t ⧸ v`
(`WeilCurves.FunctionField.Place.quotientEquivResidueField`).

## Main results

* `WeilCurves.FunctionField.Place.ord_eq_neg_log`: `ord_P` is the unique normalised valuation with
  valuation ring `O_P`.
* `WeilCurves.FunctionField.Place.ord_ofChart`,
  `WeilCurves.FunctionField.Place.ord_ofChart_algebraMap`.
* `WeilCurves.FunctionField.Place.finrank_quotient_eq_deg`: `[A_t ⧸ v : k] = deg (ofChart t v)`.
* `WeilCurves.FunctionField.Place.sum_ord_mul_deg_zeros`,
  `WeilCurves.FunctionField.Place.sum_ord_mul_deg_poles`.
-/

open IsDedekindDomain IsLocalRing Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin WithZero

namespace WeilCurves.FunctionField.Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

section Normalised

variable (P : Place k K) (w : Valuation K ℤᵐ⁰) (hw : ∀ x, x ∈ P.1 ↔ w x ≤ 1)
include hw

theorem ord_eq_zero_of_valuation_eq_one {y : K} (hy : w y = 1) : P.ord y = 0 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  refine (P.ord_eq_zero_iff hy0).mpr ⟨(hw y).mpr hy.le, (hw _).mpr ?_⟩
  rw [map_inv₀, hy, inv_one]

/-- `ord_P` is the unique normalised discrete valuation with valuation ring `O_P`. -/
theorem ord_eq_neg_log (hπ : ∃ π, w π = WithZero.exp (-1)) (x : K) :
    P.ord x = -WithZero.log (w x) := by
  obtain ⟨π, hπ⟩ := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  -- the order of `π` is `1`
  have hm : P.ord π = 1 := by
    have hpos : 0 < P.ord π := by
      have hmem : π ∈ P.1 := (hw π).mpr (by rw [hπ]; decide)
      have hinv : π⁻¹ ∉ P.1 := by
        rw [hw, map_inv₀, hπ, ← WithZero.exp_neg, neg_neg]; decide
      have h0 := P.ord_nonneg_of_mem hmem
      rcases h0.lt_or_eq with h | h
      · exact h
      · exact absurd ((P.ord_eq_zero_iff hπ0).mp h.symm).2 hinv
    obtain ⟨ϖ, hϖ⟩ := P.exists_ord_eq_one
    have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp at hϖ
    set kk := WithZero.log (w ϖ)
    have hwϖ : w ϖ = WithZero.exp kk := (WithZero.exp_log (by simpa using hϖ0)).symm
    have hy : w (ϖ * π ^ kk) = 1 := by
      rw [map_mul, map_zpow₀, hwϖ, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    have := P.ord_eq_zero_of_valuation_eq_one w hw hy
    rw [P.ord_mul hϖ0 (zpow_ne_zero _ hπ0), ord_zpow, hϖ] at this
    have hkm : (-kk) * P.ord π = 1 := by linarith
    exact Int.eq_one_of_mul_eq_one_left hpos.le hkm
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  set n := WithZero.log (w x)
  have hwx : w x = WithZero.exp n := (WithZero.exp_log (by simpa using hx0)).symm
  have hy : w (x * π ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hwx, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have := P.ord_eq_zero_of_valuation_eq_one w hw hy
  rw [P.ord_mul hx0 (zpow_ne_zero _ hπ0), ord_zpow, hm] at this
  linarith

end Normalised

section Chart

variable (t : K) [Fact (Transcendental k t)]

/-- At the place attached to a height-one prime `v` of the chart ring, `ord` is the `v`-adic
valuation. -/
theorem ord_ofChart (v : HeightOneSpectrum (chartRing k t)) (x : K) :
    (ofChart t v).ord x = -WithZero.log (v.valuation K x) := by
  refine (ofChart t v).ord_eq_neg_log (v.valuation K) (fun y ↦ ?_)
    (HeightOneSpectrum.valuation_exists_uniformizer K v) x
  rw [ofChart_val, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

theorem ord_ofChart_algebraMap (v : HeightOneSpectrum (chartRing k t)) {r : chartRing k t}
    (hr : r ≠ 0) :
    (ofChart t v).ord (algebraMap (chartRing k t) K r) =
      multiplicity v.asIdeal (Ideal.span {r}) := by
  rw [ord_ofChart, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hr, WithZero.log_exp, neg_neg]

/-- The residue map of the chart ring onto the residue field of `ofChart t v`. -/
noncomputable def chartResidue (v : HeightOneSpectrum (chartRing k t)) :
    chartRing k t →+* (ofChart t v).ResidueField :=
  (ofChart t v).residue.comp ((algebraMap (chartRing k t) K).codRestrict
    (ofChart t v).1 ((ofChart t v).algebraMap_chartRing_mem t (self_mem_ofChart t v)))

theorem chartResidue_surjective (v : HeightOneSpectrum (chartRing k t)) :
    Function.Surjective (chartResidue t v) :=
  (ofChart t v).residue_comp_surjective t (self_mem_ofChart t v)

theorem ker_chartResidue (v : HeightOneSpectrum (chartRing k t)) :
    RingHom.ker (chartResidue t v) = v.asIdeal := by
  ext r
  rw [RingHom.mem_ker, chartResidue, RingHom.comp_apply, residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  conv_rhs => rw [← toChart_ofChart t v]
  rw [mem_toChart_iff]
  rfl

/-- The residue field of the place attached to `v` is `A_t ⧸ v`. -/
noncomputable def quotientEquivResidueField (v : HeightOneSpectrum (chartRing k t)) :
    (chartRing k t ⧸ v.asIdeal) ≃+* (ofChart t v).ResidueField :=
  (Ideal.quotEquivOfEq (ker_chartResidue t v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (chartResidue_surjective t v))

theorem finrank_quotient_eq_deg (v : HeightOneSpectrum (chartRing k t)) :
    Module.finrank k (chartRing k t ⧸ v.asIdeal) = (ofChart t v).deg := by
  let e : (chartRing k t ⧸ v.asIdeal) ≃ₐ[k] (ofChart t v).ResidueField :=
    AlgEquiv.ofRingEquiv (f := quotientEquivResidueField t v)
      (fun _ ↦ rfl)
  exact e.toLinearEquiv.finrank_eq

end Chart

section Zeros

variable (k) (t : K) [Fact (Transcendental k t)]

/-- `t` as an element of `k[t]`. -/
private noncomputable def tR : Algebra.adjoin k {t} := ⟨t, Algebra.self_mem_adjoin_singleton k t⟩

omit [PerfectField k] [IsFunctionField k K] in
private theorem algEquiv_X :
    Polynomial.algEquivOfTranscendental k t Fact.out X = tR k t := by
  rw [Polynomial.algEquivOfTranscendental_apply, aeval_X]; rfl

omit [PerfectField k] [IsFunctionField k K] in
private theorem irreducible_tR : Irreducible (tR k t) := by
  rw [← algEquiv_X]
  exact (MulEquiv.irreducible_iff
    (Polynomial.algEquivOfTranscendental k t Fact.out).toMulEquiv).mpr Polynomial.irreducible_X

omit [PerfectField k] [IsFunctionField k K] in
private theorem isMaximal_span_tR : (Ideal.span {tR k t}).IsMaximal := by
  have : IsPrincipalIdealRing (Algebra.adjoin k {t}) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k t Fact.out).toRingHom
      (Polynomial.algEquivOfTranscendental k t Fact.out).surjective
  exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_tR k t)

omit [PerfectField k] [IsFunctionField k K] in
private theorem span_tR_ne_bot : Ideal.span {tR k t} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact (irreducible_tR k t).ne_zero

omit [PerfectField k] [IsFunctionField k K] in
/-- `k[t] ⧸ (t) = k`. -/
private theorem finrank_quotient_span_tR :
    Module.finrank k (Algebra.adjoin k {t} ⧸ Ideal.span {tR k t}) = 1 := by
  have := isMaximal_span_tR k t
  letI := Ideal.Quotient.field (Ideal.span {tR k t})
  let e := Polynomial.algEquivOfTranscendental k t Fact.out
  have he : e X = tR k t := algEquiv_X k t
  have hsurj : Function.Surjective (algebraMap k (Algebra.adjoin k {t} ⧸ Ideal.span {tR k t})) := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨q, rfl⟩ := e.surjective r
    obtain ⟨q', hq'⟩ := Polynomial.X_dvd_sub_C (p := q)
    refine ⟨q.coeff 0, ?_⟩
    rw [IsScalarTower.algebraMap_apply k (Algebra.adjoin k {t}), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq, ← AlgEquiv.commutes e, ← map_sub, Polynomial.algebraMap_eq,
      ← neg_sub, map_neg, neg_mem_iff, hq', map_mul, he]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hbij : Function.Bijective (Algebra.ofId k (Algebra.adjoin k {t} ⧸ Ideal.span {tR k t})) :=
    ⟨(algebraMap k _).injective, hsurj⟩
  rw [← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- `t` as an element of the chart ring `A_t`. -/
private noncomputable def tS : chartRing k t :=
  algebraMap (Algebra.adjoin k {t}) (chartRing k t) (tR k t)

omit [PerfectField k] [IsFunctionField k K] in
private theorem tS_ne_zero : tS k t ≠ 0 := by
  intro h
  exact ne_zero_of_transcendental (Fact.out : Transcendental k t) (congrArg Subtype.val h)

omit [PerfectField k] [IsFunctionField k K] [Fact (Transcendental k t)] in
private theorem map_span_tR :
    (Ideal.span {tR k t}).map (algebraMap (Algebra.adjoin k {t}) (chartRing k t)) =
      Ideal.span {tS k t} := by
  rw [Ideal.map_span, Set.image_singleton]; rfl

omit [PerfectField k] [IsFunctionField k K] in
private theorem mem_primesOver_iff (v : HeightOneSpectrum (chartRing k t)) :
    v.asIdeal ∈ (Ideal.span {tR k t}).primesOver (chartRing k t) ↔ tS k t ∈ v.asIdeal := by
  constructor
  · rintro ⟨-, hlo⟩
    have h1 : tR k t ∈ v.asIdeal.under (Algebra.adjoin k {t}) := by
      rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
    exact h1
  · intro h
    refine ⟨v.isPrime, ⟨(isMaximal_span_tR k t).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h

private theorem mem_asIdeal_iff (v : HeightOneSpectrum (chartRing k t)) :
    tS k t ∈ v.asIdeal ↔ 0 < (ofChart t v).ord t := by
  have h := mem_toChart_iff t (ofChart t v) (self_mem_ofChart t v) (r := tS k t)
  rw [toChart_ofChart] at h
  rw [ord_pos_iff, h]
  exact ⟨fun h' ↦ ⟨ne_zero_of_transcendental (Fact.out : Transcendental k t), h'⟩, fun h' ↦ h'.2⟩

omit [PerfectField k] [IsFunctionField k K] in
private theorem inertiaDeg'_eq_finrank (P : Ideal (chartRing k t)) [P.IsPrime]
    [P.LiesOver (Ideal.span {tR k t})] :
    Ideal.inertiaDeg' (Ideal.span {tR k t}) P = Module.finrank k (chartRing k t ⧸ P) := by
  have := isMaximal_span_tR k t
  letI := Ideal.Quotient.field (Ideal.span {tR k t})
  have : Module.Free k (Algebra.adjoin k {t} ⧸ Ideal.span {tR k t}) :=
    Module.Free.of_divisionRing _ _
  have : Module.Free (Algebra.adjoin k {t} ⧸ Ideal.span {tR k t}) (chartRing k t ⧸ P) :=
    Module.Free.of_divisionRing _ _
  rw [Ideal.inertiaDeg'_algebraMap,
    ← Module.finrank_mul_finrank k (Algebra.adjoin k {t} ⧸ Ideal.span {tR k t}),
    finrank_quotient_span_tR, one_mul]

end Zeros

/-- **Degree of the divisor of zeros.** For `t` transcendental over `k`,
`∑_{P : ord_P t > 0} ord_P(t) · deg P = [K : k(t)]`. -/
theorem sum_ord_mul_deg_zeros (t : K) (ht : Transcendental k t) :
    ∑ P ∈ (finite_setOf_ord_pos (k := k) t).toFinset, P.ord t * (P.deg : ℤ) =
      Module.finrank k⟮t⟯ K := by
  have : Fact (Transcendental k t) := ⟨ht⟩
  have hpm := isMaximal_span_tR k t
  have hp0 := span_tR_ne_bot k t
  have key := Ideal.sum_ramification_inertia (chartRing k t) k⟮t⟯ K hp0
  rw [← key]
  push_cast
  symm
  refine Finset.sum_bij' (fun P hP ↦ ofChart t ⟨P, ?_, ?_⟩)
    (fun Q hQ ↦ (Q.toChart t (Q.mem_of_ord_nonneg ?_)).asIdeal) ?_ ?_ ?_ ?_ ?_
  · exact ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).1
  · exact Ideal.ne_bot_of_mem_primesOver hp0
      ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP)
  · exact ((Set.Finite.mem_toFinset _).mp hQ).le
  · intro P hP
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ← mem_asIdeal_iff k t, ← mem_primesOver_iff k t]
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP
  · intro Q hQ
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp0 _]
    have hQ' := (Set.Finite.mem_toFinset _).mp hQ
    refine (mem_primesOver_iff k t (Q.toChart t (Q.mem_of_ord_nonneg hQ'.le))).mpr ?_
    rw [mem_toChart_iff]
    exact ((Q.ord_pos_iff).mp hQ').2
  · intro P hP
    exact congrArg HeightOneSpectrum.asIdeal (toChart_ofChart t _)
  · intro Q hQ
    exact ofChart_toChart t Q (Q.mem_of_ord_nonneg ((Set.Finite.mem_toFinset _).mp hQ).le)
  · intro P hP
    have hmem := (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP
    set v : HeightOneSpectrum (chartRing k t) :=
      ⟨P, hmem.1, Ideal.ne_bot_of_mem_primesOver hp0 hmem⟩
    have : P.LiesOver (Ideal.span {tR k t}) := hmem.2
    have : P.IsPrime := hmem.1
    have hram : Ideal.ramificationIdx' (Ideal.span {tR k t}) P = (ofChart t v).ord t := by
      rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity _ hmem.1, map_span_tR]
      · exact (ord_ofChart_algebraMap t v (tS_ne_zero k t)).symm
      · rw [map_span_tR, Ne, Ideal.span_singleton_eq_bot]; exact tS_ne_zero k t
    have hin : Ideal.inertiaDeg' (Ideal.span {tR k t}) P = (ofChart t v).deg := by
      rw [inertiaDeg'_eq_finrank k t P, ← finrank_quotient_eq_deg t v]
    rw [hram, hin]

end WeilCurves.FunctionField.Place

namespace WeilCurves.FunctionField

theorem adjoin_inv_eq {k K : Type*} [Field k] [Field K] [Algebra k K] (t : K) : k⟮t⁻¹⟯ = k⟮t⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  · rw [IntermediateField.adjoin_simple_le_iff]
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

/-- **Degree of the divisor of poles.** For `t` transcendental over `k`,
`∑_{P : ord_P t < 0} (-ord_P t) · deg P = [K : k(t)]`. -/
theorem sum_ord_mul_deg_poles (t : K) (ht : Transcendental k t) :
    ∑ P ∈ (finite_setOf_ord_neg (k := k) t).toFinset, (-P.ord t) * (P.deg : ℤ) =
      Module.finrank k⟮t⟯ K := by
  have h := sum_ord_mul_deg_zeros t⁻¹ (transcendental_inv ht)
  rw [adjoin_inv_eq] at h
  rw [← h]
  refine Finset.sum_congr ?_ fun P _ ↦ by rw [ord_inv]
  ext P
  simp [ord_inv]

end Place

end WeilCurves.FunctionField
