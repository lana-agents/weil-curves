/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FiniteField.PlaceCount
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The reciprocal roots of the `L`-polynomial and `N_r = q^r + 1 - ∑ α_i^r`

Let `K` be a function field over a finite field `k` with `q` elements, `k` the full constant
field, and `L(t) ∈ ℤ[t]` its `L`-polynomial (`(1 - t)(1 - qt) Z(t) = L(t)`, `deg L = 2g`,
`L(0) = 1`, leading coefficient `q^g`). Over `ℂ`, `L(t) = ∏_{i=1}^{2g} (1 - α_i t)` for the
multiset `α` of reciprocal roots (`WeilCurves.FunctionField.recRoots`), with `∏ α_i = q^g`.
Comparing the logarithmic derivatives `t L'/L = -∑_i ∑_{r ≥ 1} α_i^r t^r` and
`t L'/L = t Z'/Z - t/(1-t) - qt/(1-qt) = ∑_{r ≥ 1} (N_r - 1 - q^r) t^r` gives

`N_r = q^r + 1 - ∑_i α_i^r`  (`WeilCurves.FunctionField.pointCount_eq`).
-/

namespace WeilCurves.FunctionField

open Divisor PowerSeries

/-! ### Formal power series lemmas -/

section Series

/-- `∑_{r ≥ 1} a^r t^r`. -/
noncomputable def geom (a : ℂ) : PowerSeries ℂ := PowerSeries.mk fun r ↦ if r = 0 then 0 else a ^ r

theorem one_sub_mul_geom (a : ℂ) : (1 - C a * X) * geom a = C a * X := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc]
  rcases n with _ | n
  · simp [geom]
  · rw [coeff_C_mul, coeff_succ_X_mul, coeff_C_mul, coeff_X]
    rcases n with _ | n
    · simp [geom]
    · simp [geom, pow_succ]; ring

/-- `t d/dt`. -/
noncomputable def tD (f : PowerSeries ℂ) : PowerSeries ℂ := X * d⁄dX ℂ f

theorem tD_mul (f g : PowerSeries ℂ) : tD (f * g) = tD f * g + f * tD g := by
  simp only [tD, Derivation.leibniz, smul_eq_mul]; ring

theorem tD_one_sub (a : ℂ) : tD (1 - C a * X) = -((1 - C a * X) * geom a) := by
  rw [one_sub_mul_geom, tD, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
    derivative_X, derivative_C]
  simp; ring

theorem tD_prod (s : Multiset ℂ) :
    tD (s.map fun a ↦ 1 - C a * X).prod =
      -((s.map fun a ↦ 1 - C a * X).prod * (s.map geom).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp [tD]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, tD_mul, tD_one_sub, ih, Multiset.map_cons,
      Multiset.sum_cons]
    ring

theorem coeff_tD (f : PowerSeries ℂ) (n : ℕ) : coeff n (tD f) = n * coeff n f :=
  coeff_X_mul_derivative f n

end Series

/-! ### The `L`-polynomial and its reciprocal roots -/

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]
  [hk : Fact (IsFullConstantField k K)]

variable (k K) in
/-- The `L`-polynomial: `(1 - t)(1 - qt) Z(t) = L(t)`. -/
noncomputable def LPoly : Polynomial ℤ :=
  (exists_LPolynomial_of_full (k := k) (K := K) hk.out).choose

theorem LPoly_spec :
    (LPoly k K).natDegree = 2 * (genus k K).toNat ∧ (LPoly k K).coeff 0 = 1 ∧
      (LPoly k K).coeff (2 * (genus k K).toNat) = (Nat.card k : ℤ) ^ (genus k K).toNat ∧
      ((LPoly k K : Polynomial ℤ) : PowerSeries ℤ) =
        (1 - X) * ((1 - PowerSeries.C (Nat.card k : ℤ) * X) * zeta k K) :=
  (exists_LPolynomial_of_full (k := k) (K := K) hk.out).choose_spec

variable (k K) in
/-- `L` over `ℂ`. -/
noncomputable def LPolyC : Polynomial ℂ := (LPoly k K).map (Int.castRingHom ℂ)

theorem natDegree_LPolyC : (LPolyC k K).natDegree = 2 * (genus k K).toNat := by
  rw [LPolyC, Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _), LPoly_spec.1]

theorem eval_zero_LPolyC : (LPolyC k K).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, LPolyC, Polynomial.coeff_map, LPoly_spec.2.1]
  simp

theorem leadingCoeff_LPolyC :
    (LPolyC k K).leadingCoeff = (Nat.card k : ℂ) ^ (genus k K).toNat := by
  rw [LPolyC, Polynomial.leadingCoeff_map_of_injective (RingHom.injective_int _),
    Polynomial.leadingCoeff, LPoly_spec.1, LPoly_spec.2.2.1]
  simp

variable (k K) in
/-- The reciprocal roots `α_i` of the `L`-polynomial (with multiplicity). -/
noncomputable def recRoots : Multiset ℂ := (LPolyC k K).roots.map (·⁻¹)

theorem card_recRoots : Multiset.card (recRoots k K) = 2 * (genus k K).toNat := by
  rw [recRoots, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, natDegree_LPolyC]

theorem ne_zero_of_mem_roots {β : ℂ} (hβ : β ∈ (LPolyC k K).roots) : β ≠ 0 := by
  rintro rfl
  have := (Polynomial.mem_roots'.mp hβ).2
  rw [Polynomial.IsRoot, eval_zero_LPolyC] at this
  exact one_ne_zero this

theorem lc_mul_prod_roots :
    (LPolyC k K).leadingCoeff * ((LPolyC k K).roots.map fun β ↦ -β).prod = 1 := by
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := LPolyC k K))
  have := congrArg (Polynomial.eval 0) h
  rw [eval_zero_LPolyC, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
    Multiset.map_map] at this
  simpa using this

/-- **`L(t) = ∏ (1 - α_i t)`** over `ℂ`. -/
theorem LPolyC_eq_prod :
    LPolyC k K = ((recRoots k K).map fun a ↦ 1 - Polynomial.C a * Polynomial.X).prod := by
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := LPolyC k K))
  set R := (LPolyC k K).roots
  have hfac : ∀ β ∈ R, (1 - Polynomial.C β⁻¹ * Polynomial.X : Polynomial ℂ) =
      Polynomial.C (-β⁻¹) * (Polynomial.X - Polynomial.C β) := by
    intro β hβ
    have := ne_zero_of_mem_roots hβ
    rw [mul_sub, ← Polynomial.C_mul, neg_mul, inv_mul_cancel₀ this, Polynomial.C_neg,
      Polynomial.C_neg, Polynomial.C_1]
    ring
  have hmap : Multiset.map ((fun a : ℂ ↦ (1 - Polynomial.C a * Polynomial.X : Polynomial ℂ)) ∘
      fun x ↦ x⁻¹) (LPolyC k K).roots =
      R.map fun β ↦ Polynomial.C (-β⁻¹) * (Polynomial.X - Polynomial.C β) :=
    Multiset.map_congr rfl hfac
  rw [recRoots, Multiset.map_map, hmap, Multiset.prod_map_mul]
  have hC : (R.map fun β ↦ Polynomial.C (-β⁻¹)).prod =
      Polynomial.C ((R.map fun β ↦ -β⁻¹).prod) := by
    rw [map_multiset_prod, Multiset.map_map]; rfl
  have hinv : (R.map fun β ↦ -β⁻¹).prod = (LPolyC k K).leadingCoeff := by
    have h1 : (R.map fun β ↦ -β⁻¹) = R.map fun β ↦ (-β)⁻¹ := by
      congr 1; ext β; rw [neg_inv]
    rw [h1, Multiset.prod_map_inv]
    exact inv_eq_of_mul_eq_one_left (lc_mul_prod_roots (k := k) (K := K))
  rw [hC, hinv]
  exact h.symm

/-- **`∏ α_i = q^g`**. -/
theorem prod_recRoots : (recRoots k K).prod = (Nat.card k : ℂ) ^ (genus k K).toNat := by
  have h := lc_mul_prod_roots (k := k) (K := K)
  have hcard := IsAlgClosed.card_roots_eq_natDegree (p := LPolyC k K)
  rw [natDegree_LPolyC] at hcard
  have hneg : ((LPolyC k K).roots.map fun β ↦ -β).prod = ((LPolyC k K).roots).prod := by
    rw [Multiset.prod_map_neg, hcard, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [hneg] at h
  rw [recRoots, Multiset.prod_map_inv', ← leadingCoeff_LPolyC]
  exact inv_eq_of_mul_eq_one_left h

/-! ### `N_r = q^r + 1 - ∑ α_i^r` -/

/-- The polynomial `L` as a power series over `ℂ`. -/
theorem coe_LPolyC :
    ((LPolyC k K : Polynomial ℂ) : PowerSeries ℂ) =
      (1 - X) * ((1 - C (Nat.card k : ℂ) * X) *
        PowerSeries.map (Int.castRingHom ℂ) (zeta k K)) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℂ)) (LPoly_spec (k := k) (K := K)).2.2.2
  simp only [map_mul, map_sub, map_one, PowerSeries.map_X, map_natCast] at h
  simp only [map_natCast]
  rw [← h]
  ext n
  simp [LPolyC, Polynomial.coeff_coe]

omit hk in
theorem tD_map_zeta :
    tD (PowerSeries.map (Int.castRingHom ℂ) (zeta k K)) =
      PowerSeries.map (Int.castRingHom ℂ) (zeta k K) *
        PowerSeries.map (Int.castRingHom ℂ) (pointSeries k K) := by
  rw [← map_mul, ← X_mul_derivative_zeta]
  ext n
  rw [coeff_tD, coeff_map, coeff_map, coeff_X_mul_derivative]
  simp

/-- **`N_r = q^r + 1 - ∑_i α_i^r`** for `r ≥ 1`. -/
theorem pointCount_eq {r : ℕ} (hr : r ≠ 0) :
    (pointCount k K r : ℂ) = (Nat.card k : ℂ) ^ r + 1 - ((recRoots k K).map (· ^ r)).sum := by
  set q : ℂ := (Nat.card k : ℂ)
  set Zc := PowerSeries.map (Int.castRingHom ℂ) (zeta k K)
  set Nc := PowerSeries.map (Int.castRingHom ℂ) (pointSeries k K)
  set Lc : PowerSeries ℂ := ((LPolyC k K : Polynomial ℂ) : PowerSeries ℂ)
  -- `t L' = L (N - geom 1 - geom q)`
  have hA : tD Lc = Lc * (Nc - geom 1 - geom q) := by
    have h1 : (1 - X : PowerSeries ℂ) = 1 - C 1 * X := by simp
    rw [show Lc = (1 - X) * ((1 - C q * X) * Zc) from coe_LPolyC, h1, tD_mul, tD_mul,
      tD_one_sub, tD_one_sub, tD_map_zeta]
    ring
  -- `t L' = - L ∑ geom α_i`
  have hB : tD Lc = -(Lc * ((recRoots k K).map geom).sum) := by
    have : Lc = ((recRoots k K).map fun a ↦ 1 - C a * X).prod := by
      simp only [Lc]
      conv_lhs => rw [LPolyC_eq_prod]
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro a _
      simp [Polynomial.coeToPowerSeries.ringHom_apply]
    rw [this, tD_prod]
  have hunit : IsUnit Lc := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply]
    simp only [Lc, Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, eval_zero_LPolyC]
    exact isUnit_one
  have hC : Nc - geom 1 - geom q = -((recRoots k K).map geom).sum := by
    apply hunit.mul_left_cancel
    rw [← hA, hB]; ring
  have := congrArg (coeff r) hC
  simp only [map_sub, map_neg, map_multiset_sum, Multiset.map_map, Nc, coeff_map, pointSeries,
    coeff_mk, geom, if_neg hr, one_pow] at this
  rw [Function.comp_def] at this
  simp only [coeff_mk, if_neg hr] at this
  linear_combination this

end WeilCurves.FunctionField
