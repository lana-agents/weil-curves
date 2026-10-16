/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Place
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Residue fields and degrees of places

The residue field `κ(P)` of a place `P` of a function field `K / k` is finite over `k`: by the chart
description, it is a quotient of the chart ring `A_t` (a `k`-algebra of finite type) by a
maximal ideal, hence finite over `k` by Zariski's lemma. The degree of `P` is `[κ(P) : k]`.

## Main definitions

* `WeilCurves.FunctionField.Place.ResidueField P`: the residue field of `P`, with its canonical
  `k`-algebra structure.
* `WeilCurves.FunctionField.Place.residue P : P.1 →+* P.ResidueField`.
* `WeilCurves.FunctionField.Place.deg P : ℕ := Module.finrank k P.ResidueField`.

## Main results

* `FiniteDimensional k P.ResidueField` (`k` perfect), `0 < P.deg`.
-/

open IsLocalRing

namespace WeilCurves.FunctionField.Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (P : Place k K)

/-- The residue field of a place. -/
def ResidueField (P : Place k K) : Type _ := IsLocalRing.ResidueField P.1

noncomputable instance : Field P.ResidueField :=
  inferInstanceAs (Field (IsLocalRing.ResidueField P.1))

noncomputable instance : Algebra P.1 P.ResidueField :=
  inferInstanceAs (Algebra P.1 (IsLocalRing.ResidueField P.1))

/-- The residue map `O_P → κ(P)`. -/
noncomputable def residue : P.1 →+* P.ResidueField := IsLocalRing.residue P.1

theorem algebraMap_eq_residue : algebraMap P.1 P.ResidueField = P.residue := rfl

theorem residue_surjective : Function.Surjective P.residue := IsLocalRing.residue_surjective

theorem residue_eq_zero_iff {a : P.1} : P.residue a = 0 ↔ a ∈ maximalIdeal P.1 :=
  IsLocalRing.residue_eq_zero_iff a

/-- The inclusion `k → O_P`. -/
noncomputable def baseHom : k →+* P.1 := (algebraMap k K).codRestrict P.1 P.algebraMap_mem

@[simp]
theorem coe_baseHom (c : k) : (P.baseHom c : K) = algebraMap k K c := rfl

noncomputable instance : Algebra k P.ResidueField := (P.residue.comp P.baseHom).toAlgebra

theorem algebraMap_residueField (c : k) :
    algebraMap k P.ResidueField c = P.residue (P.baseHom c) := rfl

theorem residue_mk_algebraMap (c : k) :
    P.residue ⟨algebraMap k K c, P.algebraMap_mem c⟩ = algebraMap k P.ResidueField c := rfl

variable [PerfectField k] [IsFunctionField k K]

instance : FiniteDimensional k P.ResidueField := by
  obtain ⟨t, ht, htP⟩ := P.exists_transcendental_mem
  have : Fact (Transcendental k t) := ⟨ht⟩
  let φ : chartRing k t →+* P.ResidueField := (IsLocalRing.residue P.1).comp
    ((algebraMap (chartRing k t) K).codRestrict P.1 (P.algebraMap_chartRing_mem t htP))
  have hφ : Function.Surjective φ := P.residue_comp_surjective t htP
  let φ' : chartRing k t →ₐ[k] P.ResidueField := { φ with commutes' := fun _ ↦ rfl }
  have : Algebra.FiniteType k P.ResidueField := Algebra.FiniteType.of_surjective φ' hφ
  exact finite_of_finite_type_of_isJacobsonRing k P.ResidueField

/-- The degree `[κ(P) : k]` of a place. -/
noncomputable def deg : ℕ := Module.finrank k P.ResidueField

theorem deg_pos : 0 < P.deg := Module.finrank_pos

end WeilCurves.FunctionField.Place
