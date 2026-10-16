/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FiniteField.Finiteness
import WeilCurves.FunctionField.Picard

/-!
# Counting effective divisors in a divisor class

Let `K` be a function field over a finite field `k` with `q` elements, and assume that `k` is the
full constant field of `K` (`WeilCurves.FunctionField.IsFullConstantField`). Then the effective
divisors linearly equivalent to a divisor `A` are the `A + div f` for `f ∈ L(A) \ {0}`, and
`A + div f = A + div g` iff `f / g ∈ kˣ`. Hence (`WeilCurves.FunctionField.card_effClass`)

`#{E ≥ 0 | E ∼ A} · (q - 1) + 1 = q ^ ℓ(A)`.
-/

namespace WeilCurves.FunctionField

open Divisor

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]

variable (k K) in
/-- `k` is the full constant field of `K`: every element of `K` algebraic over `k` lies in `k`. -/
def IsFullConstantField : Prop := ∀ f : K, IsAlgebraic k f → ∃ c : k, algebraMap k K c = f

theorem exists_eq_algebraMap_of_div_eq_zero (hk : IsFullConstantField k K) {f : K}
    (h : div k f = 0) : ∃ c : k, algebraMap k K c = f := by
  refine hk f (Place.isAlgebraic_iff_forall_ord_eq_zero.mpr fun P ↦ ?_)
  have := congrArg (· P) h
  simpa using this

/-- The effective divisors linearly equivalent to `A`. -/
def effClass (A : Divisor k K) : Set (Divisor k K) := {E | 0 ≤ E ∧ E - A ∈ principal k K}

theorem finite_effClass (A : Divisor k K) : (effClass A).Finite :=
  (finite_setOf_effective_deg_eq A.deg).subset fun E ⟨hE, hEA⟩ ↦ ⟨hE, by
    have := deg_eq_zero_of_mem_principal hEA
    rw [deg_sub] at this
    omega⟩

theorem div_algebraMap_mul {c : k} (hc : c ≠ 0) {f : K} (hf : f ≠ 0) :
    div k (algebraMap k K c * f) = div k f := by
  rw [Divisor.div_mul ((map_ne_zero _).mpr hc) hf,
    div_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap c),
    zero_add]

/-- **`#{E ≥ 0 | E ∼ A} · (q - 1) + 1 = q ^ ℓ(A)`**. -/
theorem card_effClass (hk : IsFullConstantField k K) (A : Divisor k K) :
    Nat.card (effClass A) * (Nat.card k - 1) + 1 = Nat.card k ^ ell A := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Fintype (effClass A) := (finite_effClass A).fintype
  have : Finite (L A) := Module.finite_of_finite k
  have : Fintype (L A) := Fintype.ofFinite _
  let S := {f : L A // f ≠ 0}
  have hS0 : ∀ s : S, ((s.1 : K)) ≠ 0 := fun s h ↦ s.2 (Subtype.ext h)
  let Ψ : S → effClass A := fun s ↦ ⟨A + div k (s.1 : K),
    (mem_L_of_ne_zero (hS0 s)).mp s.1.2, by
      rw [add_sub_cancel_left]; exact div_mem_principal (hS0 s)⟩
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨E, hE, hEA⟩
    obtain ⟨f, hf, hfd⟩ := mem_principal.mp hEA
    have hEq : E = A + div k f := by rw [hfd]; abel
    have hfL : f ∈ L A := (mem_L_of_ne_zero hf).mpr (hEq ▸ hE)
    exact ⟨⟨⟨f, hfL⟩, fun h ↦ hf (congrArg Subtype.val h)⟩, Subtype.ext hEq.symm⟩
  -- each fibre is a `kˣ`-torsor
  have hfib : ∀ E : effClass A, Nat.card {s : S // Ψ s = E} = Nat.card k - 1 := by
    intro E
    obtain ⟨s0, hs0⟩ := hΨ E
    have hs0' : (s0.1 : K) ≠ 0 := hS0 s0
    let φ : kˣ → {s : S // Ψ s = E} := fun c ↦ ⟨⟨(c : k) • s0.1, fun h ↦ by
        have := congrArg Subtype.val h
        simp only [Submodule.coe_smul, ZeroMemClass.coe_zero, Algebra.smul_def] at this
        exact mul_ne_zero ((map_ne_zero _).mpr c.ne_zero) hs0' this⟩, by
      rw [← hs0]; apply Subtype.ext
      simp only [Ψ, Submodule.coe_smul, Algebra.smul_def]
      rw [div_algebraMap_mul c.ne_zero hs0']⟩
    have hφ : Function.Bijective φ := by
      constructor
      · intro c d hcd
        have := congrArg (fun x : {s : S // Ψ s = E} ↦ ((x.1.1 : K))) hcd
        simp only [φ, Submodule.coe_smul, Algebra.smul_def] at this
        exact Units.ext ((algebraMap k K).injective (mul_right_cancel₀ hs0' this))
      · rintro ⟨s, hs⟩
        have hdiv : div k ((s.1 : K) / s0.1) = 0 := by
          have h1 := congrArg Subtype.val (hs.trans hs0.symm)
          simp only [Ψ, add_right_inj] at h1
          rw [Divisor.div_div (hS0 s) hs0', h1, sub_self]
        obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_div_eq_zero hk hdiv
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [map_zero, eq_comm, div_eq_zero_iff] at hc
          exact hc.elim (hS0 s) hs0'
        refine ⟨Units.mk0 c hc0, ?_⟩
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        simp only [φ, Units.val_mk0, Submodule.coe_smul, Algebra.smul_def, hc]
        field_simp
    rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card,
      Fintype.card_units, Nat.card_eq_fintype_card]
  have hcardS : Nat.card S = Nat.card k ^ ell A - 1 := by
    have h1 : Fintype.card {f : L A // f ≠ 0} = Fintype.card (L A) - 1 := by
      rw [Fintype.card_subtype_compl (p := fun f : L A ↦ f = 0), Fintype.card_subtype_eq]
    change Nat.card {f : L A // f ≠ 0} = _
    rw [Nat.card_eq_fintype_card, h1, ell, Module.card_eq_pow_finrank (K := k) (V := L A),
      Nat.card_eq_fintype_card]
  have hsum : Nat.card S = Nat.card (effClass A) * (Nat.card k - 1) := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv Ψ), Nat.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card (α := effClass A)]
  have hpos : 0 < Nat.card k ^ ell A := pow_pos Nat.card_pos _
  omega

end WeilCurves.FunctionField
