/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FiniteField.Roots
import WeilCurves.RH.RootTest

/-!
# The Riemann hypothesis from a two-sided point-count bound

Kedlaya (*Weil cohomology* notes, Lemma 5.1.4): if `|N_{dN} − q^{dN} − 1| ≤ C q^{dN/2}` for some
`d ≥ 1` and all large `N`, then the reciprocal roots `α_i` of the `L`-polynomial satisfy
`|α_i| ≤ √q` (root test applied to the power sums `∑_i (α_i^d)^N = q^{dN} + 1 − N_{dN}`).
Since there are `2g` of them and `∏ α_i = q^g` (`prod_recRoots`), in fact `|α_i| = √q`, and
`N_r = q^r + 1 − ∑ α_i^r` gives the Hasse–Weil bound `|N_r − q^r − 1| ≤ 2g q^{r/2}`.

## Main results

* `WeilCurves.FunctionField.norm_recRoots_le_of_bound`: `|α_i| ≤ √q` from the bound.
* `WeilCurves.FunctionField.norm_recRoots_eq_of_bound`: `|α_i| = √q`.
* `WeilCurves.FunctionField.hasseWeil_of_bound`: `|N_r − q^r − 1| ≤ 2g √q^r` for all `r ≥ 1`.
-/

namespace WeilCurves.FunctionField

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]
  [hk : Fact (IsFullConstantField k K)]

/-- The power sums of the reciprocal roots: `∑ α_i^r = q^r + 1 − N_r`. -/
theorem sum_recRoots_pow {r : ℕ} (hr : r ≠ 0) :
    ((recRoots k K).map (· ^ r)).sum =
      (((Nat.card k : ℝ) ^ r + 1 - (pointCount k K r : ℝ) : ℝ) : ℂ) := by
  have := pointCount_eq (k := k) (K := K) hr
  push_cast
  linear_combination this

/-- **`|α_i| ≤ √q`** from a two-sided bound `|N_{dN} − q^{dN} − 1| ≤ C √q^{dN}` for large `N`. -/
theorem norm_recRoots_le_of_bound {d : ℕ} (hd : 0 < d) {C : ℝ} {N₀ : ℕ}
    (h : ∀ N, N₀ ≤ N → |(pointCount k K (d * N) : ℝ) - (Nat.card k : ℝ) ^ (d * N) - 1| ≤
      C * Real.sqrt (Nat.card k) ^ (d * N))
    {α : ℂ} (hα : α ∈ recRoots k K) : ‖α‖ ≤ Real.sqrt (Nat.card k) := by
  set sq := Real.sqrt (Nat.card k)
  have hsq : 0 ≤ sq := Real.sqrt_nonneg _
  have key := RootTest.norm_le_of_sum_pow_le ((recRoots k K).map (· ^ d)) (R := sq ^ d) (B := C)
    (pow_nonneg hsq d) (max N₀ 1) (fun N hN ↦ ?_) (Multiset.mem_map_of_mem _ hα)
  · rw [norm_pow] at key
    exact (pow_le_pow_iff_left₀ (norm_nonneg α) hsq hd.ne').mp key
  · have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hdN : d * N ≠ 0 := (Nat.mul_pos hd hN1).ne'
    rw [Multiset.map_map]
    have : ((recRoots k K).map ((· ^ N) ∘ (· ^ d))) = (recRoots k K).map (· ^ (d * N)) := by
      congr 1; funext a; simp [pow_mul]
    rw [this, sum_recRoots_pow hdN, Complex.norm_real, Real.norm_eq_abs, ← pow_mul]
    rw [show (Nat.card k : ℝ) ^ (d * N) + 1 - (pointCount k K (d * N) : ℝ) =
      -((pointCount k K (d * N) : ℝ) - (Nat.card k : ℝ) ^ (d * N) - 1) by ring, abs_neg]
    exact h N (le_of_max_le_left hN)

/-- A product of numbers in `[0, R]` is at most `R ^ card`. -/
theorem prod_le_pow_card_of_mem (t : Multiset ℝ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ x ∈ t, 0 ≤ x ∧ x ≤ R) : 0 ≤ t.prod ∧ t.prod ≤ R ^ Multiset.card t := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha := h a (Multiset.mem_cons_self a t)
    have ih' := ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact ⟨mul_nonneg ha.1 ih'.1, mul_le_mul ha.2 ih'.2 ih'.1 hR⟩

/-- A product of numbers in `[0, R]`, one of them `< R`, is `< R ^ card`. -/
theorem prod_lt_pow_card_of_mem (t : Multiset ℝ) {R : ℝ} (hR : 0 < R)
    (h : ∀ x ∈ t, 0 ≤ x ∧ x ≤ R) {x₀ : ℝ} (hx₀ : x₀ ∈ t) (hlt : x₀ < R) :
    t.prod < R ^ Multiset.card t := by
  obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hx₀
  have h' := prod_le_pow_card_of_mem t' hR.le fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)
  have h0 := (h x₀ (Multiset.mem_cons_self _ _)).1
  rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
  calc x₀ * t'.prod ≤ x₀ * R ^ Multiset.card t' := mul_le_mul_of_nonneg_left h'.2 h0
    _ < R * R ^ Multiset.card t' := mul_lt_mul_of_pos_right hlt (pow_pos hR _)

/-- **The Riemann hypothesis `|α_i| = √q`** from a two-sided bound. -/
theorem norm_recRoots_eq_of_bound {d : ℕ} (hd : 0 < d) {C : ℝ} {N₀ : ℕ}
    (h : ∀ N, N₀ ≤ N → |(pointCount k K (d * N) : ℝ) - (Nat.card k : ℝ) ^ (d * N) - 1| ≤
      C * Real.sqrt (Nat.card k) ^ (d * N))
    {α : ℂ} (hα : α ∈ recRoots k K) : ‖α‖ = Real.sqrt (Nat.card k) := by
  set sq := Real.sqrt (Nat.card k)
  have hq : (0 : ℝ) < Nat.card k := by exact_mod_cast Nat.card_pos
  have hsq : 0 < sq := Real.sqrt_pos.mpr hq
  have hle : ∀ β ∈ recRoots k K, ‖β‖ ≤ sq := fun β hβ ↦ norm_recRoots_le_of_bound hd h hβ
  refine le_antisymm (hle α hα) (not_lt.mp fun hlt ↦ ?_)
  set t := (recRoots k K).map (‖·‖)
  have ht : ∀ x ∈ t, 0 ≤ x ∧ x ≤ sq := by
    intro x hx
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hx
    exact ⟨norm_nonneg _, hle β hβ⟩
  have hlt' := prod_lt_pow_card_of_mem t hsq ht (Multiset.mem_map_of_mem _ hα) hlt
  have hprod : t.prod = ‖(recRoots k K).prod‖ :=
    (map_multiset_prod (normHom : ℂ →*₀ ℝ) (recRoots k K)).symm
  rw [hprod, prod_recRoots, Multiset.card_map, card_recRoots, norm_pow, Complex.norm_natCast,
    pow_mul, Real.sq_sqrt hq.le] at hlt'
  exact lt_irrefl _ hlt'

/-- **The Hasse–Weil bound** `|N_r − q^r − 1| ≤ 2g √q^r` from a two-sided bound. -/
theorem hasseWeil_of_bound {d : ℕ} (hd : 0 < d) {C : ℝ} {N₀ : ℕ}
    (h : ∀ N, N₀ ≤ N → |(pointCount k K (d * N) : ℝ) - (Nat.card k : ℝ) ^ (d * N) - 1| ≤
      C * Real.sqrt (Nat.card k) ^ (d * N))
    {r : ℕ} (hr : r ≠ 0) :
    |(pointCount k K r : ℝ) - (Nat.card k : ℝ) ^ r - 1| ≤
      2 * (genus k K).toNat * Real.sqrt (Nat.card k) ^ r := by
  have hs := sum_recRoots_pow (k := k) (K := K) hr
  have hn := norm_multiset_sum_le ((recRoots k K).map (· ^ r))
  rw [hs, Complex.norm_real, Real.norm_eq_abs, Multiset.map_map] at hn
  have hc : ((recRoots k K).map ((‖·‖) ∘ (· ^ r))) =
      Multiset.replicate (Multiset.card (recRoots k K)) (Real.sqrt (Nat.card k) ^ r) := by
    rw [Multiset.eq_replicate]
    refine ⟨Multiset.card_map _ _, fun x hx ↦ ?_⟩
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hx
    simp only [Function.comp_apply, norm_pow, norm_recRoots_eq_of_bound hd h hβ]
  rw [hc, Multiset.sum_replicate, card_recRoots, nsmul_eq_mul] at hn
  rw [show (pointCount k K r : ℝ) - (Nat.card k : ℝ) ^ r - 1 =
    -((Nat.card k : ℝ) ^ r + 1 - (pointCount k K r : ℝ)) by ring, abs_neg]
  push_cast at hn
  linarith

end WeilCurves.FunctionField
