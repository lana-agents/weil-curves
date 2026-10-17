/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The root test for power sums

Kedlaya (*Weil cohomology* notes, Lemma 5.1.4): if the power sums `s_N = ∑_i β_i^N` of finitely
many complex numbers satisfy `|s_N| ≤ C R^N` for all large `N`, then `|β_i| ≤ R` for all `i`.
Kedlaya argues with the poles of `∑_i (1 - β_i T)⁻¹`; we give the algebraic form of that
argument. Let `γ` be one of the `β_i`, with `|γ| > R`, of multiplicity `μ`, and let `β'` be the
others. With `P(T) = ∏_{β'} (1 - β' T)` the formal identity

`(1 - γ T) P(T) ∑_N s_N T^N = μ P(T) + (1 - γ T) ∑_{β'} ∏_{β'' ≠ β'} (1 - β'' T)`

can be evaluated at `T = γ⁻¹`, where `∑ s_N T^N` converges absolutely: the left side vanishes,
the right side is `μ P(γ⁻¹) ≠ 0`.

## Main result

* `WeilCurves.RootTest.norm_le_of_sum_pow_le`.
-/

namespace WeilCurves.RootTest

open PowerSeries

/-- The geometric series `∑_N a^N X^N`. -/
noncomputable def G (a : ℂ) : PowerSeries ℂ := PowerSeries.mk fun N ↦ a ^ N

theorem one_sub_mul_G (a : ℂ) : (1 - C a * X) * G a = 1 := by
  ext N
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  rcases N with _ | N
  · simp [G]
  · rw [coeff_succ_X_mul]
    simp [G, pow_succ, mul_comm]

/-- Evaluation of a power series at `z`, as a sum. -/
noncomputable def ev (z : ℂ) (F : PowerSeries ℂ) : ℂ := ∑' N, coeff N F * z ^ N

/-- `F(z)` converges absolutely... or at least summably. -/
def Conv (z : ℂ) (F : PowerSeries ℂ) : Prop := Summable fun N ↦ coeff N F * z ^ N

theorem conv_X_mul {z : ℂ} {F : PowerSeries ℂ} (h : Conv z F) :
    Conv z (X * F) ∧ ev z (X * F) = z * ev z F := by
  have hs : ∀ N, coeff (N + 1) (X * F) * z ^ (N + 1) = z * (coeff N F * z ^ N) := by
    intro N; rw [coeff_succ_X_mul, pow_succ]; ring
  have hc : Conv z (X * F) := by
    unfold Conv
    rw [← summable_nat_add_iff 1]
    simp only [hs]
    exact h.mul_left z
  refine ⟨hc, ?_⟩
  unfold ev
  rw [hc.tsum_eq_zero_add]
  simp only [hs, coeff_zero_X_mul, zero_mul, zero_add]
  exact tsum_mul_left

theorem conv_C_mul {z : ℂ} {F : PowerSeries ℂ} (h : Conv z F) (a : ℂ) :
    Conv z (C a * F) ∧ ev z (C a * F) = a * ev z F := by
  have hs : ∀ N, coeff N (C a * F) * z ^ N = a * (coeff N F * z ^ N) := by
    intro N; rw [coeff_C_mul]; ring
  refine ⟨?_, ?_⟩
  · unfold Conv; simp only [hs]; exact h.mul_left a
  · unfold ev; simp only [hs]; exact tsum_mul_left

theorem conv_add {z : ℂ} {F F' : PowerSeries ℂ} (h : Conv z F) (h' : Conv z F') :
    Conv z (F + F') ∧ ev z (F + F') = ev z F + ev z F' := by
  have hs : ∀ N, coeff N (F + F') * z ^ N = coeff N F * z ^ N + coeff N F' * z ^ N := by
    intro N; rw [map_add]; ring
  refine ⟨?_, ?_⟩
  · unfold Conv; simp only [hs]; exact h.add h'
  · unfold ev; simp only [hs]; exact h.tsum_add h'

/-- Multiplying a convergent series by a polynomial. -/
theorem conv_poly_mul {z : ℂ} {F : PowerSeries ℂ} (h : Conv z F) (p : Polynomial ℂ) :
    Conv z ((p : PowerSeries ℂ) * F) ∧ ev z ((p : PowerSeries ℂ) * F) = p.eval z * ev z F := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.coe_C, Polynomial.eval_C]
    exact conv_C_mul h a
  | add p p' hp hp' =>
    rw [Polynomial.coe_add, add_mul, Polynomial.eval_add, add_mul]
    obtain ⟨h1, h2⟩ := conv_add hp.1 hp'.1
    exact ⟨h1, h2.trans (by rw [hp.2, hp'.2])⟩
  | monomial n a hp =>
    have he : (((Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial ℂ)) : PowerSeries ℂ) * F =
        X * (((Polynomial.C a * Polynomial.X ^ n : Polynomial ℂ) : PowerSeries ℂ) * F) := by
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X]
      ring
    rw [he]
    obtain ⟨h1, h2⟩ := conv_X_mul hp.1
    refine ⟨h1, ?_⟩
    rw [h2, hp.2]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

theorem conv_one (z : ℂ) : Conv z 1 ∧ ev z 1 = 1 := by
  have hs : (fun N ↦ coeff N (1 : PowerSeries ℂ) * z ^ N) = fun N ↦ if N = 0 then 1 else 0 := by
    funext N; rcases N with _ | N <;> simp [coeff_one]
  refine ⟨?_, ?_⟩
  · unfold Conv; rw [hs]; exact summable_of_ne_finset_zero (s := {0}) (by simp)
  · unfold ev; rw [hs, tsum_ite_eq]

theorem ev_coe (z : ℂ) (p : Polynomial ℂ) : ev z (p : PowerSeries ℂ) = p.eval z := by
  have := (conv_poly_mul (conv_one z).1 p).2
  rwa [mul_one, (conv_one z).2, mul_one] at this

/-- **Root test for power sums** (Kedlaya, Lemma 5.1.4). -/
theorem norm_le_of_sum_pow_le (s : Multiset ℂ) {R B : ℝ} (hR : 0 ≤ R) (N₀ : ℕ)
    (h : ∀ N, N₀ ≤ N → ‖(s.map (· ^ N)).sum‖ ≤ B * R ^ N) {γ : ℂ} (hγ : γ ∈ s) :
    ‖γ‖ ≤ R := by
  classical
  by_contra hlt
  push Not at hlt
  have hγ0 : γ ≠ 0 := by
    rintro rfl; simp at hlt; linarith
  have hnγ : 0 < ‖γ‖ := norm_pos_iff.mpr hγ0
  set z := γ⁻¹ with hz
  -- the generating series of the power sums
  set f : PowerSeries ℂ := PowerSeries.mk fun N ↦ (s.map (· ^ N)).sum with hf
  have hconv : Conv z f := by
    unfold Conv
    refine Summable.of_norm_bounded_eventually_nat (g := fun N ↦ B * (R / ‖γ‖) ^ N) ?_ ?_
    · exact (summable_geometric_of_lt_one (div_nonneg hR hnγ.le)
        ((div_lt_one hnγ).mpr hlt)).mul_left B
    · rw [Filter.eventually_atTop]
      refine ⟨N₀, fun N hN ↦ ?_⟩
      rw [hf, coeff_mk, norm_mul, norm_pow, hz, norm_inv, div_pow, inv_pow, mul_div_assoc']
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (h N hN) (by positivity)
  -- split off `γ`
  set μ := s.count γ
  set s' := s.filter (· ≠ γ)
  have hsplit : s = Multiset.replicate μ γ + s' := by
    rw [← Multiset.filter_eq']
    exact (Multiset.filter_add_not (· = γ) s).symm
  have hfG : f = C (μ : ℂ) * G γ + (s'.map G).sum := by
    ext N
    conv_lhs => rw [hf, coeff_mk, hsplit, Multiset.map_add, Multiset.sum_add,
      Multiset.map_replicate, Multiset.sum_replicate]
    rw [map_add, coeff_C_mul, map_multiset_sum, Multiset.map_map]
    simp only [G, coeff_mk, Function.comp_def, nsmul_eq_mul]
  -- the polynomials
  set lin : ℂ → Polynomial ℂ := fun a ↦ 1 - Polynomial.C a * Polynomial.X
  set P : Polynomial ℂ := (s'.map lin).prod
  set W : Polynomial ℂ := Polynomial.C (μ : ℂ) * P +
    lin γ * (s'.map fun a ↦ ((s'.erase a).map lin).prod).sum
  have hlin : ∀ a, ((lin a : Polynomial ℂ) : PowerSeries ℂ) = 1 - C a * X := by
    intro a; simp [lin, Polynomial.coe_C, Polynomial.coe_X]
  have hPG : ∀ a ∈ s', (P : PowerSeries ℂ) * G a =
      (((s'.erase a).map lin).prod : Polynomial ℂ) := by
    intro a ha
    simp only [P]
    rw [← Multiset.prod_map_erase ha, Polynomial.coe_mul, mul_comm (lin a : PowerSeries ℂ),
      mul_assoc, hlin, one_sub_mul_G, mul_one]
  have hcoeSum : (((s'.map fun a ↦ ((s'.erase a).map lin).prod).sum : Polynomial ℂ) :
      PowerSeries ℂ) =
      (s'.map fun a ↦ ((((s'.erase a).map lin).prod : Polynomial ℂ) : PowerSeries ℂ)).sum := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_sum, Multiset.map_map]
    rfl
  have hid : (((lin γ * P : Polynomial ℂ)) : PowerSeries ℂ) * f = (W : PowerSeries ℂ) := by
    rw [hfG, Polynomial.coe_mul, hlin]
    simp only [W, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, hlin, hcoeSum]
    rw [mul_add]
    congr 1
    · rw [show ((1 - C γ * X) * (P : PowerSeries ℂ)) * (C (μ : ℂ) * G γ) =
          C (μ : ℂ) * (P : PowerSeries ℂ) * ((1 - C γ * X) * G γ) by ring,
        one_sub_mul_G, mul_one]
    · rw [mul_assoc]
      congr 1
      rw [← Multiset.sum_map_mul_left]
      congr 1
      exact Multiset.map_congr rfl hPG
  -- evaluate at `z = γ⁻¹`
  have h1 := (conv_poly_mul hconv (lin γ * P)).2
  rw [hid, ev_coe] at h1
  have hlinγ : (lin γ).eval z = 0 := by
    simp [lin, hz, mul_inv_cancel₀ hγ0]
  rw [Polynomial.eval_mul, hlinγ, zero_mul, zero_mul] at h1
  simp only [W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hlinγ, zero_mul,
    add_zero] at h1
  have hμ : (μ : ℂ) ≠ 0 := by
    have : 0 < μ := Multiset.count_pos.mpr hγ
    exact_mod_cast this.ne'
  have hP : P.eval z ≠ 0 := by
    simp only [P, Polynomial.eval_multiset_prod, Multiset.map_map]
    refine Multiset.prod_ne_zero fun hmem ↦ ?_
    obtain ⟨a, ha, h0⟩ := Multiset.mem_map.mp hmem
    have hne : a ≠ γ := (Multiset.mem_filter.mp ha).2
    simp only [Function.comp_apply, lin, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hz] at h0
    apply hne
    have : a * γ⁻¹ = 1 := by linear_combination -h0
    field_simp at this
    exact this
  exact mul_ne_zero hμ hP h1

end WeilCurves.RootTest
