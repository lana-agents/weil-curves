/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FiniteField.Zeta
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Constant field extensions

Let `K` be a function field over a finite field `k` which is the full constant field of `K`, and
let `r ≥ 1`. Let `f ∈ k[X]` be the minimal polynomial over `k` of a primitive element of the
extension `k_r = FiniteField.Extension k p r` of degree `r`. Since `k` is algebraically closed in
`K`, `f` stays irreducible over `K` (`WeilCurves.FunctionField.irreducible_map_of_full`: the
coefficients of a monic factor of `f` over `K` are integral over `k`, hence lie in `k`). The
*constant field extension of degree `r`* is the field `K_r = K[X]/(f)`
(`WeilCurves.FunctionField.ConstExt K r`), of degree `r` over `K`; it is again a function field
over `k` (`WeilCurves.FunctionField.IsFunctionField.of_finite`).
-/

open Polynomial

namespace WeilCurves.FunctionField

open scoped IntermediateField

/-! ### Function fields are stable under finite extensions -/

section Transfer

variable {k K L : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra K L] [Algebra k L]
  [IsScalarTower k K L]

/-- A finite extension of a function field over `k` is a function field over `k`. -/
theorem IsFunctionField.of_finite [IsFunctionField k K] [FiniteDimensional K L] :
    IsFunctionField k L := by
  obtain ⟨t, ht, hfin⟩ := IsFunctionField.exists_finite (k := k) (K := K)
  set φ : K →ₐ[k] L := IsScalarTower.toAlgHom k K L
  refine ⟨⟨φ t, ?_, ?_⟩⟩
  · exact (transcendental_algebraMap_iff (algebraMap K L).injective).mpr ht
  · set E := k⟮t⟯
    set E' := k⟮φ t⟯
    have hmap : E.map φ = E' := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    let ψ : E ≃ₐ[k] E' := (IntermediateField.equivMap E φ).trans (IntermediateField.equivOfEq hmap)
    have h1 : (algebraMap E K).Finite := RingHom.finite_algebraMap.mpr hfin
    have h2 : (algebraMap K L).Finite := RingHom.finite_algebraMap.mpr inferInstance
    have h3 : ((algebraMap K L).comp (algebraMap E K)).Finite := h2.comp h1
    have h4 : (algebraMap E' L) =
        ((algebraMap K L).comp (algebraMap E K)).comp (ψ.symm : E' →+* E) := by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply]
      have : ψ (ψ.symm x) = x := ψ.apply_symm_apply x
      conv_lhs => rw [← this]
      rfl
    have h5 : (algebraMap E' L).Finite := by
      rw [h4]
      exact h3.comp (RingHom.Finite.of_surjective _ ψ.symm.surjective)
    exact RingHom.finite_algebraMap.mp h5

end Transfer

/-! ### Irreducibility over a function field with full constant field -/

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]

omit [Finite k] [IsFunctionField k K] in
/-- A polynomial over `K` whose coefficients are integral over `k` comes from `k[X]`. -/
theorem exists_map_eq_of_isIntegral_coeff (hk : IsFullConstantField k K) {g : K[X]}
    (hg : ∀ i, IsIntegral k (g.coeff i)) : ∃ g₀ : k[X], g₀.map (algebraMap k K) = g := by
  have : g ∈ Polynomial.lifts (algebraMap k K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    obtain ⟨c, hc⟩ := hk _ (hg i).isAlgebraic
    exact ⟨c, hc⟩
  obtain ⟨g₀, hg₀⟩ := this
  exact ⟨g₀, hg₀⟩

omit [Finite k] [IsFunctionField k K] in
/-- **An irreducible polynomial over `k` stays irreducible over `K`** when `k` is the full
constant field of `K`. -/
theorem irreducible_map_of_full (hk : IsFullConstantField k K) {f : k[X]} (hf : Irreducible f)
    (hm : f.Monic) : Irreducible (f.map (algebraMap k K)) := by
  have hm' : (f.map (algebraMap k K)).Monic := hm.map _
  rw [hm'.irreducible_iff_natDegree]
  rw [hm.irreducible_iff_natDegree] at hf
  refine ⟨fun h ↦ hf.1 ?_, fun g₁ g₂ hg₁ hg₂ hprod ↦ ?_⟩
  · apply Polynomial.map_injective _ (algebraMap k K).injective
    rw [h, Polynomial.map_one]
  have hint : ∀ (g : K[X]), g.Monic → g ∣ f.map (algebraMap k K) → ∀ i, IsIntegral k (g.coeff i) :=
    fun g hg hdvd i ↦ Polynomial.isIntegral_coeff_of_dvd f g hm hg hdvd i
  obtain ⟨h₁, rfl⟩ := exists_map_eq_of_isIntegral_coeff hk (hint g₁ hg₁ ⟨g₂, hprod.symm⟩)
  obtain ⟨h₂, rfl⟩ := exists_map_eq_of_isIntegral_coeff hk
    (hint _ hg₂ ⟨h₁.map (algebraMap k K), by rw [← hprod, mul_comm]⟩)
  have hinj := (algebraMap k K).injective
  have hh₁ : h₁.Monic := by
    rw [Polynomial.Monic, ← (algebraMap k K).injective.eq_iff,
      ← Polynomial.leadingCoeff_map_of_injective hinj, map_one]
    exact hg₁
  have hh₂ : h₂.Monic := by
    rw [Polynomial.Monic, ← (algebraMap k K).injective.eq_iff,
      ← Polynomial.leadingCoeff_map_of_injective hinj, map_one]
    exact hg₂
  have hprod' : h₁ * h₂ = f := by
    apply Polynomial.map_injective _ hinj
    rw [Polynomial.map_mul, hprod]
  rcases hf.2 h₁ h₂ hh₁ hh₂ hprod' with h | h
  · left; rw [Polynomial.natDegree_map_eq_of_injective hinj]; exact h
  · right; rw [Polynomial.natDegree_map_eq_of_injective hinj]; exact h

/-! ### The constant field extension of degree `r` -/

instance fact_ringChar_prime : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩

variable (k) in
/-- The finite field extension of `k` of degree `r`. -/
abbrev BaseExt (r : ℕ) [NeZero r] : Type :=
  FiniteField.Extension k (ringChar k) r

variable (k) in
/-- A primitive element of the degree-`r` extension of `k`. -/
noncomputable def basePB (r : ℕ) [NeZero r] : PowerBasis k (BaseExt k r) :=
  Field.powerBasisOfFiniteOfSeparable k (BaseExt k r)

variable (k) in
/-- The minimal polynomial over `k` of a primitive element of the degree-`r` extension. -/
noncomputable def basePoly (r : ℕ) [NeZero r] : k[X] := minpoly k (basePB k r).gen

theorem basePoly_monic (r : ℕ) [NeZero r] : (basePoly k r).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral (basePB k r).gen)

theorem basePoly_irreducible (r : ℕ) [NeZero r] : Irreducible (basePoly k r) :=
  minpoly.irreducible (Algebra.IsIntegral.isIntegral (basePB k r).gen)

theorem natDegree_basePoly (r : ℕ) [NeZero r] : (basePoly k r).natDegree = r := by
  rw [basePoly, PowerBasis.natDegree_minpoly, ← PowerBasis.finrank, FiniteField.finrank_extension]

variable (k K) in
/-- The constant field extension `K_r = K[X]/(f)` of degree `r`. -/
abbrev ConstExt (r : ℕ) [NeZero r] : Type _ := AdjoinRoot ((basePoly k r).map (algebraMap k K))

variable [hk : Fact (IsFullConstantField k K)] (r : ℕ) [NeZero r]

instance fact_irreducible_basePoly :
    Fact (Irreducible ((basePoly k r).map (algebraMap k K))) :=
  ⟨irreducible_map_of_full hk.out (basePoly_irreducible r) (basePoly_monic r)⟩

omit [IsFunctionField k K] hk in
theorem basePoly_map_ne_zero : (basePoly k r).map (algebraMap k K) ≠ 0 :=
  ((basePoly_monic r).map _).ne_zero

instance : FiniteDimensional K (ConstExt k K r) :=
  (AdjoinRoot.powerBasis (basePoly_map_ne_zero (K := K) r)).finite

omit [IsFunctionField k K] in
theorem finrank_constExt : Module.finrank K (ConstExt k K r) = r := by
  rw [(AdjoinRoot.powerBasis (basePoly_map_ne_zero (K := K) r)).finrank,
    AdjoinRoot.powerBasis_dim, Polynomial.natDegree_map, natDegree_basePoly]

instance : IsFunctionField k (ConstExt k K r) := IsFunctionField.of_finite (K := K)

end WeilCurves.FunctionField
