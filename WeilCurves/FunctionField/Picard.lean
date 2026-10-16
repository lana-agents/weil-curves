/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.RiemannRoch

/-!
# Principal divisors and the divisor class group

The principal divisors `div f` (`f ∈ Kˣ`) form a subgroup `WeilCurves.FunctionField.principal k K`
of the divisors; the quotient is the divisor class group `WeilCurves.FunctionField.Pic k K`.
Degree and `ℓ` are invariant under linear equivalence and descend to `Pic k K`.
-/

namespace WeilCurves.FunctionField

open Divisor

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

variable (k K) in
/-- `f ↦ div f` as a homomorphism `Kˣ → Div(K)`. -/
noncomputable def divHom : Additive Kˣ →+ Divisor k K where
  toFun u := div k ((Additive.toMul u : Kˣ) : K)
  map_zero' := by simp [Divisor.div_one]
  map_add' u v := by
    simp only [toMul_add, Units.val_mul]
    exact div_mul (Additive.toMul u).ne_zero (Additive.toMul v).ne_zero

variable (k K) in
/-- The principal divisors. -/
noncomputable def principal : AddSubgroup (Divisor k K) := (divHom k K).range

theorem mem_principal {D : Divisor k K} : D ∈ principal k K ↔ ∃ f : K, f ≠ 0 ∧ div k f = D := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, (Additive.toMul u).ne_zero, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨Additive.ofMul (Units.mk0 f hf), rfl⟩

theorem div_mem_principal {f : K} (hf : f ≠ 0) : div k f ∈ principal k K :=
  mem_principal.mpr ⟨f, hf, rfl⟩

theorem deg_eq_zero_of_mem_principal {D : Divisor k K} (hD : D ∈ principal k K) : D.deg = 0 := by
  obtain ⟨f, _, rfl⟩ := mem_principal.mp hD
  exact deg_div f

theorem ell_eq_of_sub_mem_principal {A B : Divisor k K} (h : B - A ∈ principal k K) :
    ell B = ell A := by
  obtain ⟨f, hf, hfd⟩ := mem_principal.mp h
  have : B = A + div k f := by rw [hfd]; abel
  rw [this, ell_add_div A hf]

variable (k K) in
/-- The divisor class group. -/
abbrev Pic : Type _ := Divisor k K ⧸ principal k K

namespace Pic

variable (k K) in
/-- The degree of a divisor class. -/
noncomputable def deg : Pic k K →+ ℤ :=
  QuotientAddGroup.lift _ degHom fun _ hD ↦ deg_eq_zero_of_mem_principal hD

@[simp]
theorem deg_mk (A : Divisor k K) : deg k K (QuotientAddGroup.mk A) = A.deg := rfl

/-- `ℓ` of a divisor class. -/
noncomputable def ell (c : Pic k K) : ℕ :=
  Quotient.liftOn' c Divisor.ell fun A B h ↦ by
    have h' : -A + B ∈ principal k K := QuotientAddGroup.leftRel_apply.mp h
    exact (ell_eq_of_sub_mem_principal (by rwa [sub_eq_neg_add])).symm

@[simp]
theorem ell_mk (A : Divisor k K) : ell (QuotientAddGroup.mk A : Pic k K) = Divisor.ell A := rfl

end Pic

end WeilCurves.FunctionField
