/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.ConstantExtension.Schmidt

/-!
# The constant field extension as a function field over `k_r`

The degree-`r` extension `k_r` of `k` embeds into `K_r = K[X]/(f)` by sending the primitive
element of `k_r` to the root `θ` (`WeilCurves.FunctionField.baseLift`); this makes `K_r` an
algebraic function field over `k_r` (`IsFunctionField (BaseExt k r) (ConstExt k K r)`).
-/

open Polynomial

namespace WeilCurves.FunctionField

open scoped IntermediateField

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]
  [hk : Fact (IsFullConstantField k K)] (r : ℕ) [NeZero r]

omit [IsFunctionField k K] in
theorem aeval_theta : aeval (theta (k := k) (K := K) r) (basePoly k r) = 0 := by
  rw [aeval_def, IsScalarTower.algebraMap_eq k K (ConstExt k K r), ← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root _

/-- The embedding `k_r → K_r`, `gen ↦ θ`. -/
noncomputable def baseLift : BaseExt k r →ₐ[k] ConstExt k K r :=
  (basePB k r).lift (theta r) (aeval_theta r)

omit [IsFunctionField k K] in
theorem baseLift_gen : baseLift (K := K) r (basePB k r).gen = theta r := PowerBasis.lift_gen _ _ _

noncomputable instance : Algebra (BaseExt k r) (ConstExt k K r) :=
  (baseLift (K := K) r).toRingHom.toAlgebra

instance : IsScalarTower k (BaseExt k r) (ConstExt k K r) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ ((baseLift (K := K) r).commutes c).symm

omit [IsFunctionField k K] in
theorem algebraMap_baseExt (x : BaseExt k r) :
    algebraMap (BaseExt k r) (ConstExt k K r) x = baseLift r x := rfl

instance : IsFunctionField (BaseExt k r) (ConstExt k K r) := by
  obtain ⟨t, ht⟩ := exists_transcendental k K
  set t' : ConstExt k K r := algebraMap K (ConstExt k K r) t
  have ht' : Transcendental k t' :=
    (transcendental_algebraMap_iff (algebraMap K (ConstExt k K r)).injective).mpr ht
  have htr : Transcendental (BaseExt k r) t' := fun h ↦ ht' (h.restrictScalars (R := k))
  refine ⟨⟨t', htr, ?_⟩⟩
  have : FiniteDimensional k⟮t'⟯ (ConstExt k K r) := finiteDimensional_adjoin ht'
  have hle : k⟮t'⟯ ≤ (IntermediateField.adjoin (BaseExt k r) {t'}).restrictScalars k := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.mem_adjoin_simple_self _ t'
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := k⟮t'⟯) (M := ConstExt k K r)
  refine ⟨⟨S, eq_top_iff.mpr fun x hxt ↦ ?_⟩⟩
  clear hxt
  have hx : x ∈ Submodule.span k⟮t'⟯ (S : Set (ConstExt k K r)) := by rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy =>
    have : c • y = (⟨(c : ConstExt k K r), hle c.2⟩ :
        IntermediateField.adjoin (BaseExt k r) {t'}) • y := rfl
    rw [this]
    exact Submodule.smul_mem _ _ hy
/-! ### Places over `k` and over `k_r` -/

omit [IsFunctionField k K] in
theorem isIntegral_algebraMap_baseExt (c : BaseExt k r) :
    IsIntegral k (algebraMap (BaseExt k r) (ConstExt k K r) c) :=
  (Algebra.IsIntegral.isIntegral (R := k) c).map (IsScalarTower.toAlgHom k _ _)

/-- A place of `K_r` over `k` is a place over `k_r`. -/
def Place.toKr (Q : Place k (ConstExt k K r)) : Place (BaseExt k r) (ConstExt k K r) :=
  ⟨Q.1, Q.ne_top, fun c ↦ Q.mem_of_isIntegral (isIntegral_algebraMap_baseExt r c)⟩

/-- A place of `K_r` over `k_r` is a place over `k`. -/
def Place.ofKr (Q : Place (BaseExt k r) (ConstExt k K r)) : Place k (ConstExt k K r) :=
  ⟨Q.1, Q.ne_top, fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k (BaseExt k r)]; exact Q.algebraMap_mem _⟩

/-- Places of `K_r` over `k` and over `k_r` are the same. -/
def placeKrEquiv : Place k (ConstExt k K r) ≃ Place (BaseExt k r) (ConstExt k K r) where
  toFun := Place.toKr r
  invFun := Place.ofKr r
  left_inv _ := rfl
  right_inv _ := rfl

theorem ord_toKr (Q : Place k (ConstExt k K r)) (x : ConstExt k K r) :
    (Q.toKr r).ord x = Q.ord x := rfl

/-- **`deg_k Q = r · deg_{k_r} Q`**. -/
theorem deg_eq_mul_deg_toKr (Q : Place k (ConstExt k K r)) : Q.deg = r * (Q.toKr r).deg := by
  letI : Algebra (BaseExt k r) Q.ResidueField :=
    (inferInstance : Algebra (BaseExt k r) (Q.toKr r).ResidueField)
  have : IsScalarTower k (BaseExt k r) Q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
    change Q.residue (Q.baseHom c) = (Q.toKr r).residue ((Q.toKr r).baseHom _)
    congr 1
    apply Subtype.ext
    simp only [Place.coe_baseHom]
    exact IsScalarTower.algebraMap_apply k (BaseExt k r) _ c
  have : FiniteDimensional (BaseExt k r) Q.ResidueField :=
    (inferInstance : FiniteDimensional (BaseExt k r) (Q.toKr r).ResidueField)
  rw [Place.deg, Place.deg, ← Module.finrank_mul_finrank k (BaseExt k r) Q.ResidueField,
    FiniteField.finrank_extension]
  rfl

/-! ### `k_r` is the full constant field of `K_r` -/

omit [IsFunctionField k K] in
/-- **`k_r` is algebraically closed in `K_r`.** -/
theorem isFullConstantField_constExt :
    IsFullConstantField (BaseExt k r) (ConstExt k K r) := by
  intro x hx
  have hxk : IsAlgebraic k x := hx.restrictScalars (R := k)
  set Kr' : IntermediateField k (ConstExt k K r) := (baseLift (K := K) r).fieldRange
  have hKr' : Module.finrank k Kr' = r := by
    rw [← IntermediateField.finrank_eq_finrank_subalgebra, AlgHom.fieldRange_toSubalgebra,
      ← (AlgEquiv.ofInjective _ (baseLift (K := K) r).injective).toLinearEquiv.finrank_eq,
      FiniteField.finrank_extension]
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have : FiniteDimensional k Kr' := Module.finite_of_finrank_pos (by rw [hKr']; exact hr0)
  have : FiniteDimensional k k⟮x⟯ := IntermediateField.adjoin.finiteDimensional hxk.isIntegral
  set M := Kr' ⊔ k⟮x⟯
  have : Finite k := inferInstance
  -- a primitive element of `M`
  set pb := Field.powerBasisOfFiniteOfSeparable k M
  set y : ConstExt k K r := (pb.gen : ConstExt k K r)
  have hyint : IsIntegral k y := (Algebra.IsIntegral.isIntegral (R := k) pb.gen).map M.val
  set h := minpoly k y
  have hirr : Irreducible (h.map (algebraMap k K)) :=
    irreducible_map_of_full hk.out (minpoly.irreducible hyint) (minpoly.monic hyint)
  have hminK : minpoly K y = h.map (algebraMap k K) := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ ((minpoly.monic hyint).map _)).symm
    rw [Polynomial.aeval_map_algebraMap, minpoly.aeval]
  have hyK : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have h1 : Module.finrank k M = h.natDegree := by
    rw [pb.finrank, ← PowerBasis.natDegree_minpoly, IntermediateField.minpoly_eq]
  have h2 : h.natDegree ≤ r := by
    have := IntermediateField.adjoin.finrank hyK
    rw [hminK, Polynomial.natDegree_map] at this
    rw [← this]
    calc Module.finrank K K⟮y⟯ ≤ Module.finrank K (⊤ : IntermediateField K (ConstExt k K r)) :=
          IntermediateField.finrank_le_of_le_right le_top
      _ = Module.finrank K (ConstExt k K r) := IntermediateField.finrank_top'
      _ = r := finrank_constExt (K := K) r
  have heq : Kr' = M := IntermediateField.eq_of_le_of_finrank_le le_sup_left (by omega)
  have hxM : x ∈ M := le_sup_right (a := Kr') (IntermediateField.mem_adjoin_simple_self k x)
  rw [← heq] at hxM
  obtain ⟨c, hc⟩ := hxM
  exact ⟨c, hc⟩

end WeilCurves.FunctionField
