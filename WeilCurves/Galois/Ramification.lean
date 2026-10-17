/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Degree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# A uniform bound for ramification over `k(x)`

Let `M` be a function field over a perfect field `k`, `x ∈ M` transcendental with `M / k(x)`
separable. Kedlaya (Lemma 5.1.8) controls the places of `k(x)` over which `M` ramifies by the
Riemann–Hurwitz formula. We use instead the different ideal of the chart ring `A_x` over `k[x]`
(Mathlib): if `𝔓² ∣ 𝔭 A_x` then `𝔓` divides the different (`pow_sub_one_dvd_differentIdeal_aux`),
which contains `f'(y)` for a primitive element `y ∈ A_x` with minimal polynomial `f`
(`aeval_derivative_mem_differentIdeal`). With `δ ∈ k[x]` the constant coefficient of the minimal
polynomial of `f'(y)` (nonzero), every ramified prime contains `δ`.

Applied to `z = x^Q − x` (`Q` divisible by the characteristic, so `z` is squarefree in `k[x]`):
for every place `β ∋ x`, `ord_β z ≥ 2` implies `ord_β z ≤ ord_β δ`
(`WeilCurves.FunctionField.exists_ramification_bound`). Hence the places where `z` has a multiple
zero contribute at most `∑_{ord_β δ > 0} ord_β(δ) deg β` to `deg (z)_0`, independently of `Q`.
-/

open Polynomial IsDedekindDomain
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace WeilCurves.FunctionField

open Place

variable {k M : Type*} [Field k] [PerfectField k] [Field M] [Algebra k M] [IsFunctionField k M]
  (x : M) [hx : Fact (Transcendental k x)]

omit [PerfectField k] in
/-- A primitive element of `M / k(x)` integral over `k[x]`. -/
theorem exists_primitive_chart [Algebra.IsSeparable k⟮x⟯ M] :
    ∃ y : chartRing k x, Algebra.adjoin k⟮x⟯ {(y : M)} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k⟮x⟯ M
  obtain ⟨c, hc0, hc⟩ := exists_integral_multiples (Algebra.adjoin k {x}) k⟮x⟯ (L := M) {α}
  have hci := hc α (Finset.mem_singleton_self α)
  refine ⟨⟨c • α, hci⟩, ?_⟩
  set c' : k⟮x⟯ := algebraMap (Algebra.adjoin k {x}) k⟮x⟯ c
  have hc' : c' ≠ 0 := by
    intro h
    apply hc0
    exact (IsFractionRing.injective (Algebra.adjoin k {x}) k⟮x⟯) (h.trans (map_zero _).symm)
  have hsmul : (c • α : M) = c' • α := by
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply
      (Algebra.adjoin k {x}) k⟮x⟯ M]
  have hint : IsIntegral k⟮x⟯ (c • α : M) := Algebra.IsIntegral.isIntegral _
  change Algebra.adjoin k⟮x⟯ {(c • α : M)} = ⊤
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
  have heq : k⟮x⟯⟮(c • α : M)⟯ = k⟮x⟯⟮α⟯ := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff, hsmul]
      exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self _ α)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have hmem := IntermediateField.mem_adjoin_simple_self k⟮x⟯ (c • α : M)
      have : α = c'⁻¹ • (c • α : M) := by rw [hsmul, smul_smul, inv_mul_cancel₀ hc', one_smul]
      exact (congrArg (fun z ↦ z ∈ k⟮x⟯⟮(c • α : M)⟯) this).mpr
        (IntermediateField.smul_mem _ hmem)
  rw [heq, hα, IntermediateField.top_toSubalgebra]

set_option maxHeartbeats 1000000 in
-- the proof unfolds many coercions between `k[x]`, `A_x` and `M`
/-- The **ramification bound**: there is a nonzero `δ ∈ k[x]` such that for every place `β ∋ x`
and every `Q` divisible by the characteristic `p`, `ord_β (x^Q − x) ≥ 2` implies
`ord_β (x^Q − x) ≤ ord_β δ`. -/
theorem exists_ramification_bound [Algebra.IsSeparable k⟮x⟯ M] (p : ℕ) [CharP k p] :
    ∃ δ : M, δ ≠ 0 ∧ δ ∈ Algebra.adjoin k {x} ∧ ∀ β : Place k M, x ∈ β.1 → ∀ Q : ℕ, p ∣ Q →
      2 ≤ β.ord (x ^ Q - x) → β.ord (x ^ Q - x) ≤ β.ord δ := by
  classical
  set A := Algebra.adjoin k {x}
  set B := chartRing k x
  have : IsPrincipalIdealRing A := isPrincipalIdealRing_adjoin hx.out
  obtain ⟨y, hy⟩ := exists_primitive_chart (k := k) x
  set f := minpoly A y
  have hyint : IsIntegral A y := IsIntegralClosure.isIntegral A M y
  set δ0 : B := aeval y (derivative f)
  have hδ0mem : δ0 ∈ differentIdeal A B :=
    aeval_derivative_mem_differentIdeal A k⟮x⟯ M y hy
  have hδ0 : δ0 ≠ 0 := by
    intro h0
    have hsep : (minpoly k⟮x⟯ (y : M)).Separable := Algebra.IsSeparable.isSeparable k⟮x⟯ (y : M)
    have hmin : minpoly k⟮x⟯ (y : M) = f.map (algebraMap A k⟮x⟯) := by
      have := minpoly.isIntegrallyClosed_eq_field_fractions k⟮x⟯ M hyint
      exact this
    have h1 := hsep.aeval_derivative_ne_zero (minpoly.aeval k⟮x⟯ (y : M))
    apply h1
    rw [hmin, derivative_map, aeval_map_algebraMap]
    have : (aeval (y : M)) (derivative f) = ((aeval y (derivative f) : B) : M) :=
      aeval_algebraMap_apply M y (derivative f)
    rw [this]
    change ((δ0 : B) : M) = 0
    rw [h0]; rfl
  have hδ0int : IsIntegral A δ0 := IsIntegralClosure.isIntegral A M δ0
  set c0 : A := (minpoly A δ0).coeff 0
  have hc0 : c0 ≠ 0 := by
    intro h0
    have hδM : (δ0 : M) ≠ 0 := fun h ↦ hδ0 (Subtype.ext h)
    have hK := minpoly.coeff_zero_ne_zero (A := k⟮x⟯)
      (Algebra.IsIntegral.isIntegral (δ0 : M)) hδM
    apply hK
    have hm := minpoly.isIntegrallyClosed_eq_field_fractions k⟮x⟯ M hδ0int
    change (minpoly k⟮x⟯ (algebraMap B M δ0)).coeff 0 = 0
    rw [hm, coeff_map]
    change algebraMap A k⟮x⟯ c0 = 0
    rw [h0, map_zero]
  -- `c0 ∈ (δ0)`
  have hc0mem : ∀ I : Ideal B, δ0 ∈ I → algebraMap A B c0 ∈ I := by
    intro I hI
    have h := minpoly.aeval A δ0
    rw [← X_mul_divX_add (minpoly A δ0), map_add, map_mul, aeval_X, aeval_C] at h
    have : algebraMap A B c0 = -(δ0 * aeval δ0 (divX (minpoly A δ0))) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [this]
    exact I.neg_mem (I.mul_mem_right _ hI)
  refine ⟨(c0 : M), fun h ↦ hc0 (Subtype.ext h), c0.2, ?_⟩
  intro β hxβ Q hpQ h2
  set z := x ^ Q - x
  have hz0 : z ≠ 0 := by
    intro h; rw [h, β.ord_zero] at h2; omega
  set v := β.toChart x hxβ
  have hβ : β = ofChart x v := (ofChart_toChart x β hxβ).symm
  have hmemv : ∀ b : B, b ∈ v.asIdeal ↔ (b : M) ∈ β.1.nonunits := fun b ↦ mem_toChart_iff x β hxβ
  -- `ord_β` of an element of `B` outside `v` vanishes
  have hord0 : ∀ b : B, b ∉ v.asIdeal → β.ord (b : M) = 0 := by
    intro b hb
    have hbmem : (b : M) ∈ β.1 := β.algebraMap_chartRing_mem x hxβ b
    have hnn := β.ord_nonneg_of_mem hbmem
    by_contra hne
    apply hb
    rw [hmemv]
    exact ((β.ord_pos_iff).mp (lt_of_le_of_ne hnn (Ne.symm hne))).2
  have hordnn : ∀ b : B, 0 ≤ β.ord (b : M) := fun b ↦
    β.ord_nonneg_of_mem (β.algebraMap_chartRing_mem x hxβ b)
  -- the prime of `k[x]` below `β`
  set P : Ideal A := v.asIdeal.comap (algebraMap A B)
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  set zA : A := ⟨z, Subalgebra.sub_mem _ (Subalgebra.pow_mem _
    (Algebra.self_mem_adjoin_singleton k x) _) (Algebra.self_mem_adjoin_singleton k x)⟩
  have hzA : (algebraMap A B zA : M) = z := rfl
  have hzP : zA ∈ P := by
    change algebraMap A B zA ∈ v.asIdeal
    rw [hmemv, hzA]
    exact ((β.ord_pos_iff).mp (by omega)).2
  have hzA0 : zA ≠ 0 := fun h ↦ hz0 (congrArg Subtype.val h)
  have hPbot : P ≠ ⊥ := fun h ↦ hzA0 (by rw [h] at hzP; exact hzP)
  obtain ⟨w, hw⟩ := (Submodule.IsPrincipal.principal P : ∃ w, P = Ideal.span {w})
  have hw0 : w ≠ 0 := by rintro rfl; apply hPbot; rw [hw, Ideal.span_singleton_eq_bot]
  have hw' : P = Ideal.span {w} := hw
  have hwprime : Prime w := (Ideal.span_singleton_prime hw0).mp (by rw [← hw']; exact hPprime)
  obtain ⟨u, hu⟩ := (Ideal.mem_span_singleton.mp (by rw [← hw']; exact hzP) : w ∣ zA)
  -- `zA` is squarefree
  have hsq : Squarefree zA := by
    let e := Polynomial.algEquivOfTranscendental k x hx.out
    have he : e (X ^ Q - X) = zA := by
      apply Subtype.ext
      simp [e, Polynomial.algEquivOfTranscendental_apply, zA, z]
    rw [← he]
    have hsep : (X ^ Q - X : k[X]).Separable := galois_poly_separable p Q hpQ
    intro a ha
    have ha' : e.symm a * e.symm a ∣ X ^ Q - X := by
      obtain ⟨b, hb⟩ := ha
      refine ⟨e.symm b, ?_⟩
      apply e.injective
      rw [hb, map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    have := hsep.squarefree _ ha'
    have := this.map e.toRingHom
    simpa using this
  have hu_notin : u ∉ P := by
    intro huP
    rw [hw'] at huP
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp huP
    have : w * w ∣ zA := ⟨t, by rw [hu, ht]; ring⟩
    exact hwprime.not_unit (hsq w this)
  have hwB0 : (algebraMap A B w : M) ≠ 0 := by
    intro h; apply hw0; exact Subtype.ext h
  have huB0 : (algebraMap A B u : M) ≠ 0 := by
    intro h; apply hu_notin
    have : u = 0 := Subtype.ext h
    rw [this]; exact P.zero_mem
  have hordz : β.ord z = β.ord (algebraMap A B w : M) := by
    have : z = (algebraMap A B w : M) * (algebraMap A B u : M) := by
      rw [← hzA, hu, map_mul]; rfl
    rw [this, β.ord_mul hwB0 huB0, hord0 _ hu_notin, add_zero]
  -- `w ∈ v²`, so `v² ∣ P B`
  have hPmax : P.IsMaximal := hPprime.isMaximal hPbot
  have hwv2 : v.asIdeal ^ 2 ∣ P.map (algebraMap A B) := by
    rw [hw', Ideal.map_span, Set.image_singleton]
    have hmult : (2 : ℕ) ≤ multiplicity v.asIdeal (Ideal.span {algebraMap A B w}) := by
      have h := ord_ofChart_algebraMap x v (r := algebraMap A B w)
        (fun h ↦ hwB0 (by rw [h]; rfl))
      rw [← hβ] at h
      have h2' : (2 : ℤ) ≤ β.ord (algebraMap A B w : M) := hordz ▸ h2
      have : ((algebraMap (chartRing k x) M) (algebraMap A B w)) =
          (algebraMap A B w : M) := rfl
      rw [this] at h
      omega
    exact pow_dvd_of_le_multiplicity hmult
  have hdiff : v.asIdeal ^ (2 - 1) ∣ differentIdeal A B :=
    pow_sub_one_dvd_differentIdeal_aux A k⟮x⟯ M v.asIdeal two_ne_zero hPbot hwv2
  rw [pow_one, Ideal.dvd_iff_le] at hdiff
  have hc0P : c0 ∈ P := hc0mem _ (hdiff hδ0mem)
  rw [hw'] at hc0P
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hc0P
  have htB0 : (algebraMap A B t : M) ≠ 0 := by
    intro h; apply hc0
    have : t = 0 := Subtype.ext h
    rw [ht, this, mul_zero]
  have hc0eq : (c0 : M) = (algebraMap A B w : M) * (algebraMap A B t : M) := by
    rw [ht]; rfl
  rw [hordz, hc0eq, β.ord_mul hwB0 htB0]
  linarith [hordnn (algebraMap A B t)]

end WeilCurves.FunctionField
