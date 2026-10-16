/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Degree

/-!
# Divisors of a function field

A *divisor* of a function field `K` is a finitely supported function `Place k K → ℤ`
(`WeilCurves.FunctionField.Divisor`). Its degree is `deg A = ∑_P A(P) · deg P`. The divisor of a
function `f` is `div f = ∑_P ord_P(f) · P`; it is the difference of the divisor of zeros and
the divisor of poles of `f`. Principal divisors have degree `0`
(`WeilCurves.FunctionField.Divisor.deg_div`): this is the fundamental identity
`WeilCurves.FunctionField.Place.sum_ord_mul_deg_zeros` /
`WeilCurves.FunctionField.Place.sum_ord_mul_deg_poles`.

We follow H. Stichtenoth, *Algebraic Function Fields and Codes*, Ch. 1 §1.4, with the base
field `k` (which need not be the full constant field of `K`); degrees are taken over `k`.

## Main definitions

* `WeilCurves.FunctionField.Divisor k K := Place k K →₀ ℤ`.
* `WeilCurves.FunctionField.Divisor.deg`, bundled as `WeilCurves.FunctionField.Divisor.degHom`.
* `WeilCurves.FunctionField.Divisor.div f`, `WeilCurves.FunctionField.Divisor.zeroDivisor f`,
  `WeilCurves.FunctionField.Divisor.polarDivisor f`.

## Main results

* `WeilCurves.FunctionField.Divisor.deg_add`, `deg_neg`, `deg_sub`, `deg_nsmul`, `deg_zsmul`,
  `deg_single`, `deg_mono`.
* `WeilCurves.FunctionField.Divisor.div_mul`, `div_inv`, `div_div`, `div_one`.
* `WeilCurves.FunctionField.Divisor.div_eq_zeroDivisor_sub_polarDivisor`.
* `WeilCurves.FunctionField.Divisor.deg_polarDivisor`, `deg_zeroDivisor`: for `x` transcendental,
  both have degree `[K : k(x)]`.
* `WeilCurves.FunctionField.Divisor.deg_div`: `deg (div k f) = 0`.
-/

open scoped IntermediateField

namespace WeilCurves.FunctionField

/-- The divisors of a function field: finitely supported `ℤ`-valued functions on the places. -/
abbrev Divisor (k K : Type*) [Field k] [Field K] [Algebra k K] : Type _ := Place k K →₀ ℤ

namespace Divisor

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Degree -/

/-- The degree `∑_P A(P) · deg P` of a divisor (degrees over `k`). -/
noncomputable def deg (A : Divisor k K) : ℤ := A.sum fun P n ↦ n * (P.deg : ℤ)

theorem deg_add (A B : Divisor k K) : (A + B).deg = A.deg + B.deg :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)

@[simp]
theorem deg_zero : (0 : Divisor k K).deg = 0 := Finsupp.sum_zero_index

/-- The degree as an additive homomorphism. -/
noncomputable def degHom : Divisor k K →+ ℤ where
  toFun := deg
  map_zero' := deg_zero
  map_add' := deg_add

@[simp]
theorem degHom_apply (A : Divisor k K) : degHom A = A.deg := rfl

@[simp]
theorem deg_neg (A : Divisor k K) : (-A).deg = -A.deg := map_neg degHom A

theorem deg_sub (A B : Divisor k K) : (A - B).deg = A.deg - B.deg := map_sub degHom A B

theorem deg_nsmul (n : ℕ) (A : Divisor k K) : (n • A).deg = n * A.deg := by
  rw [← degHom_apply, map_nsmul, degHom_apply, nsmul_eq_mul]

theorem deg_zsmul (n : ℤ) (A : Divisor k K) : (n • A).deg = n * A.deg := by
  rw [← degHom_apply, map_zsmul, degHom_apply, smul_eq_mul]

@[simp]
theorem deg_single (P : Place k K) (n : ℤ) : deg (Finsupp.single P n) = n * P.deg :=
  Finsupp.sum_single_index (h := fun (P : Place k K) (n : ℤ) ↦ n * (P.deg : ℤ)) (zero_mul _)

theorem deg_eq_sum_of_support_subset (A : Divisor k K) {s : Finset (Place k K)}
    (hs : A.support ⊆ s) : A.deg = ∑ P ∈ s, A P * (P.deg : ℤ) :=
  Finsupp.sum_of_support_subset A hs _ fun _ _ ↦ zero_mul _

theorem deg_nonneg {A : Divisor k K} (hA : 0 ≤ A) : 0 ≤ A.deg :=
  Finset.sum_nonneg fun P _ ↦ mul_nonneg (hA P) (Int.natCast_nonneg _)

theorem deg_mono {A B : Divisor k K} (h : A ≤ B) : A.deg ≤ B.deg := by
  have := deg_nonneg (sub_nonneg.mpr h)
  rw [deg_sub] at this
  omega

theorem deg_pos_of_nonneg_of_ne_zero [PerfectField k] [IsFunctionField k K] {A : Divisor k K}
    (hA : 0 ≤ A)
    (h0 : A ≠ 0) : 0 < A.deg := by
  obtain ⟨P, hP⟩ := Finsupp.ne_iff.mp h0
  have hPpos : 0 < A P := lt_of_le_of_ne (hA P) (Ne.symm hP)
  have hsplit : A = Finsupp.single P (A P) + (A - Finsupp.single P (A P)) := by abel
  have hrest : 0 ≤ A - Finsupp.single P (A P) := by
    classical
    intro Q
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply]
    by_cases h : P = Q
    · subst h; simp
    · rw [Finsupp.single_apply, if_neg h, sub_zero]; exact hA Q
  rw [hsplit, deg_add, deg_single]
  have := deg_nonneg hrest
  have := P.deg_pos
  positivity

/-! ### Principal divisors -/

variable [PerfectField k] [IsFunctionField k K]

variable (k) in
/-- The divisor `∑_P ord_P(f) · P` of a function `f` (and `0` for `f = 0`). -/
noncomputable def div (f : K) : Divisor k K :=
  Finsupp.ofSupportFinite (fun P ↦ P.ord f) (Place.finite_setOf_ord_ne_zero f)

@[simp]
theorem div_apply (f : K) (P : Place k K) : div k f P = P.ord f := rfl

@[simp]
theorem div_zero : div k (0 : K) = 0 := by ext P; simp

@[simp]
theorem div_one : div k (1 : K) = 0 := by ext P; simp

theorem div_mul {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) : div k (f * g) = div k f + div k g := by
  ext P; simp [P.ord_mul hf hg]

@[simp]
theorem div_inv (f : K) : div k f⁻¹ = -div k f := by ext P; simp

theorem div_div {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) : div k (f / g) = div k f - div k g := by
  ext P; simp [P.ord_div hf hg]

@[simp]
theorem div_pow (f : K) (n : ℕ) : div k (f ^ n) = n • div k f := by ext P; simp

@[simp]
theorem div_neg (f : K) : div k (-f) = div k f := by ext P; simp

theorem div_eq_zero_of_isAlgebraic {c : K} (hc : IsAlgebraic k c) : div k c = 0 := by
  ext P; simp [P.ord_eq_zero_of_isAlgebraic hc]

variable (k) in
/-- The divisor of zeros `∑_P max(0, ord_P f) · P`. -/
noncomputable def zeroDivisor (f : K) : Divisor k K :=
  Finsupp.ofSupportFinite (fun P ↦ max 0 (P.ord f))
    ((Place.finite_setOf_ord_ne_zero f).subset fun P hP ↦ by
      simp only [Function.mem_support] at hP
      simp only [Set.mem_setOf_eq]
      omega)

variable (k) in
/-- The divisor of poles `∑_P max(0, -ord_P f) · P`. -/
noncomputable def polarDivisor (f : K) : Divisor k K :=
  Finsupp.ofSupportFinite (fun P ↦ max 0 (-P.ord f))
    ((Place.finite_setOf_ord_ne_zero f).subset fun P hP ↦ by
      simp only [Function.mem_support] at hP
      simp only [Set.mem_setOf_eq]
      omega)

@[simp]
theorem zeroDivisor_apply (f : K) (P : Place k K) : zeroDivisor k f P = max 0 (P.ord f) := rfl

@[simp]
theorem polarDivisor_apply (f : K) (P : Place k K) : polarDivisor k f P = max 0 (-P.ord f) := rfl

theorem zeroDivisor_nonneg (f : K) : 0 ≤ zeroDivisor k f := fun P ↦ by simp

theorem polarDivisor_nonneg (f : K) : 0 ≤ polarDivisor k f := fun P ↦ by simp

theorem div_eq_zeroDivisor_sub_polarDivisor (f : K) :
    div k f = zeroDivisor k f - polarDivisor k f := by
  ext P; simp only [div_apply, Finsupp.coe_sub, Pi.sub_apply, zeroDivisor_apply,
    polarDivisor_apply]; omega

@[simp]
theorem polarDivisor_inv (f : K) : polarDivisor k f⁻¹ = zeroDivisor k f := by ext P; simp

@[simp]
theorem zeroDivisor_inv (f : K) : zeroDivisor k f⁻¹ = polarDivisor k f := by ext P; simp

theorem neg_polarDivisor_le_div (f : K) : -polarDivisor k f ≤ div k f := fun P ↦ by
  simp only [Finsupp.coe_neg, Pi.neg_apply, polarDivisor_apply, div_apply]; omega

/-- The divisor of zeros of a transcendental `x` has degree `[K : k(x)]`. -/
theorem deg_zeroDivisor {x : K} (hx : Transcendental k x) :
    (zeroDivisor k x).deg = Module.finrank k⟮x⟯ K := by
  rw [← Place.sum_ord_mul_deg_zeros x hx, deg_eq_sum_of_support_subset (zeroDivisor k x)
    (s := (Place.finite_setOf_ord_pos (k := k) x).toFinset)]
  · refine Finset.sum_congr rfl fun P hP ↦ ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
    rw [zeroDivisor_apply, max_eq_right hP.le]
  · intro P hP
    rw [Finsupp.mem_support_iff, zeroDivisor_apply] at hP
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega

/-- The divisor of poles of a transcendental `x` has degree `[K : k(x)]`. -/
theorem deg_polarDivisor {x : K} (hx : Transcendental k x) :
    (polarDivisor k x).deg = Module.finrank k⟮x⟯ K := by
  rw [← Place.sum_ord_mul_deg_poles x hx, deg_eq_sum_of_support_subset (polarDivisor k x)
    (s := (Place.finite_setOf_ord_neg (k := k) x).toFinset)]
  · refine Finset.sum_congr rfl fun P hP ↦ ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
    rw [polarDivisor_apply, max_eq_right (by omega)]
  · intro P hP
    rw [Finsupp.mem_support_iff, polarDivisor_apply] at hP
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega

/-- **Principal divisors have degree zero.** -/
theorem deg_div (f : K) : (div k f).deg = 0 := by
  by_cases hf : IsAlgebraic k f
  · rw [div_eq_zero_of_isAlgebraic hf, deg_zero]
  · rw [div_eq_zeroDivisor_sub_polarDivisor, deg_sub, deg_zeroDivisor hf, deg_polarDivisor hf,
      sub_self]

/-- A transcendental element has a nonzero divisor of poles. -/
theorem polarDivisor_ne_zero {x : K} (hx : Transcendental k x) : polarDivisor k x ≠ 0 := by
  obtain ⟨P, hP⟩ := Place.exists_ord_neg hx
  intro h
  have := congrArg (· P) h
  simp only [polarDivisor_apply, Finsupp.coe_zero, Pi.zero_apply] at this
  omega

end Divisor

end WeilCurves.FunctionField
