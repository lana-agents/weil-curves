/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.ConstantExtension.Schmidt
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The numbers `N_r` and the logarithmic derivative of the zeta function

For a function field `K` over a finite field `k`, let `B_d` be the number of places of degree `d`
(`WeilCurves.FunctionField.placeCount`) and `N_r = ∑_{d ∣ r} d B_d`
(`WeilCurves.FunctionField.pointCount`); for the constant field extension of degree `r`, `N_r` is
the number of places of degree one. The Euler product `Z(t) = ∏_P (1 - t^{deg P})⁻¹` amounts to
the identity `t Z'(t) = Z(t) ∑_{r ≥ 1} N_r t^r`, i.e.

`n A_n = ∑_{r=1}^n N_r A_{n-r}`  (`WeilCurves.FunctionField.mul_effCount_eq_sum`),

proved directly by counting: `n A_n = ∑_{E} deg E = ∑_P ∑_{j ≥ 1} deg P · #{E | E(P) ≥ j}` and
`#{E ∈ Eff_n | E(P) ≥ j} = A_{n - j deg P}`.
-/

namespace WeilCurves.FunctionField

open Divisor PowerSeries

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]

variable (k K) in
/-- The number `B_d` of places of degree `d`. -/
noncomputable def placeCount (d : ℕ) : ℕ := {P : Place k K | P.deg = d}.ncard

variable (k K) in
/-- `N_r = ∑_{d ∣ r} d B_d`. -/
noncomputable def pointCount (r : ℕ) : ℕ := ∑ d ∈ r.divisors, d * placeCount k K d

/-- The effective divisors of degree `n`, as a finset. -/
noncomputable def effFinset (n : ℤ) : Finset (Divisor k K) :=
  (finite_setOf_effective_deg_eq (k := k) (K := K) n).toFinset

theorem mem_effFinset {n : ℤ} {E : Divisor k K} : E ∈ effFinset n ↔ 0 ≤ E ∧ E.deg = n :=
  Set.Finite.mem_toFinset _

theorem effCount_eq_card (n : ℤ) : effCount k K n = (effFinset (k := k) (K := K) n).card :=
  Nat.card_eq_card_finite_toFinset _

theorem effCount_neg {n : ℤ} (hn : n < 0) : effCount k K n = 0 := by
  rw [effCount_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro E hE
  obtain ⟨hE, hdeg⟩ := mem_effFinset.mp hE
  have := deg_nonneg hE
  omega

/-- `#{E ∈ Eff_n | E(P) ≥ j} = A_{n - j deg P}`. -/
theorem card_filter_le_eq (n : ℤ) (P : Place k K) (j : ℕ) :
    ((effFinset (k := k) (K := K) n).filter fun E ↦ (j : ℤ) ≤ E P).card =
      effCount k K (n - j * P.deg) := by
  classical
  rw [effCount_eq_card]
  refine Finset.card_nbij' (fun E ↦ E - Finsupp.single P (j : ℤ))
    (fun F ↦ F + Finsupp.single P (j : ℤ)) ?_ ?_ ?_ ?_
  · intro E hE
    rw [Finset.mem_coe, Finset.mem_filter, mem_effFinset] at hE
    rw [Finset.mem_coe, mem_effFinset]
    refine ⟨fun Q ↦ ?_, by rw [deg_sub, deg_single, hE.1.2]⟩
    by_cases hQ : Q = P
    · subst hQ; simp; omega
    · simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply,
        Finsupp.single_apply, if_neg (Ne.symm hQ), sub_zero]
      exact hE.1.1 Q
  · intro F hF
    rw [Finset.mem_coe, mem_effFinset] at hF
    rw [Finset.mem_coe, Finset.mem_filter, mem_effFinset]
    refine ⟨⟨fun Q ↦ ?_, by rw [deg_add, deg_single, hF.2]; ring⟩, ?_⟩
    · have := hF.1 Q
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply] at this ⊢
      have : 0 ≤ Finsupp.single P (j : ℤ) Q := by
        simp only [Finsupp.single_apply]; split_ifs <;> omega
      omega
    · have := hF.1 P
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_eq_same] at this ⊢
      omega
  · intro E _; simp
  · intro F _; simp

/-- `B_d` as a sum over the places of degree `≤ n`, for `d ≤ n`. -/
theorem placeCount_eq_card {n d : ℕ} (hd : d ≤ n) :
    placeCount k K d =
      ((finite_setOf_deg_le (k := k) (K := K) n).toFinset.filter fun P ↦ P.deg = d).card := by
  rw [placeCount, ← Set.ncard_coe_finset]
  congr 1
  ext P
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  constructor
  · intro h; exact ⟨h ▸ hd, h⟩
  · exact fun h ↦ h.2

/-- `N_r = ∑_{P, deg P ∣ r} deg P`. -/
theorem pointCount_eq_sum {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    (pointCount k K r : ℤ) = ∑ P ∈ (finite_setOf_deg_le (k := k) (K := K) n).toFinset,
      if P.deg ∣ r then (P.deg : ℤ) else 0 := by
  classical
  set S := (finite_setOf_deg_le (k := k) (K := K) n).toFinset
  rw [← Finset.sum_filter, pointCount]
  push_cast
  rw [← Finset.sum_fiberwise_of_maps_to (s := S.filter fun P ↦ P.deg ∣ r) (t := r.divisors)
    (g := fun P ↦ P.deg)]
  · refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hdn : d ≤ n := (Nat.divisor_le hd).trans hrn
    rw [placeCount_eq_card hdn, Finset.filter_filter]
    have : (S.filter fun P ↦ P.deg ∣ r ∧ P.deg = d) = S.filter fun P ↦ P.deg = d := by
      apply Finset.filter_congr
      intro P _
      constructor
      · exact fun h ↦ h.2
      · intro h; exact ⟨h ▸ Nat.dvd_of_mem_divisors hd, h⟩
    rw [this, Finset.sum_congr rfl (g := fun _ ↦ (d : ℤ)) (fun P hP ↦ by
      rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro P hP
    rw [Finset.mem_filter] at hP
    exact Nat.mem_divisors.mpr ⟨hP.2, by omega⟩

/-- **`n A_n = ∑_{r=1}^n N_r A_{n-r}`** (the Euler product in logarithmic-derivative form). -/
theorem mul_effCount_eq_sum (n : ℕ) :
    (n : ℤ) * effCount k K n =
      ∑ r ∈ Finset.Icc 1 n, (pointCount k K r : ℤ) * effCount k K ((n : ℤ) - r) := by
  classical
  set S := (finite_setOf_deg_le (k := k) (K := K) n).toFinset
  have hmemS : ∀ {E : Divisor k K}, E ∈ effFinset (n : ℤ) → ∀ P, E P ≠ 0 → P ∈ S := by
    intro E hE P hP
    have h := deg_le_of_effective (mem_effFinset.mp hE).1 hP
    rw [(mem_effFinset.mp hE).2] at h
    rw [Set.Finite.mem_toFinset]
    exact_mod_cast h
  have hEP : ∀ {E : Divisor k K}, E ∈ effFinset (n : ℤ) → ∀ P, 0 ≤ E P ∧ E P ≤ n := by
    intro E hE P
    obtain ⟨hE0, hdeg⟩ := mem_effFinset.mp hE
    refine ⟨hE0 P, ?_⟩
    have h1 : Finsupp.single P (E P) ≤ E := by
      intro Q
      by_cases hQ : Q = P
      · subst hQ; simp
      · simp only [Finsupp.single_apply, if_neg (Ne.symm hQ)]; exact hE0 Q
    have h2 := deg_mono h1
    rw [deg_single, hdeg] at h2
    have hP1 : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
    have := hE0 P
    nlinarith
  -- Step A
  have stepA : (n : ℤ) * effCount k K n =
      ∑ E ∈ effFinset (n : ℤ), ∑ P ∈ S, E P * (P.deg : ℤ) := by
    rw [effCount_eq_card, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun E hE ↦ ?_
    rw [← (mem_effFinset.mp hE).2]
    exact deg_eq_sum_of_support_subset E fun P hP ↦ hmemS hE P (Finsupp.mem_support_iff.mp hP)
  -- Step B
  have stepB : ∀ E ∈ effFinset (n : ℤ), ∀ P ∈ S, E P * (P.deg : ℤ) =
      ∑ j ∈ Finset.Icc 1 n, if (j : ℤ) ≤ E P then (P.deg : ℤ) else 0 := by
    intro E hE P _
    obtain ⟨h0, hn⟩ := hEP hE P
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.Icc 1 n).filter fun j : ℕ ↦ (j : ℤ) ≤ E P) = Finset.Icc 1 (E P).toNat := by
      ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this, Nat.card_Icc, Nat.add_sub_cancel, Int.toNat_of_nonneg h0]
  -- Step C
  have stepC : (n : ℤ) * effCount k K n = ∑ P ∈ S, ∑ j ∈ Finset.Icc 1 n,
      (P.deg : ℤ) * effCount k K ((n : ℤ) - j * P.deg) := by
    rw [stepA, Finset.sum_congr rfl fun E hE ↦ Finset.sum_congr rfl fun P hP ↦ stepB E hE P hP,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_filter_le_eq, mul_comm]
  -- Step D
  have stepD : ∀ P ∈ S, ∑ j ∈ Finset.Icc 1 n, (P.deg : ℤ) * effCount k K ((n : ℤ) - j * P.deg) =
      ∑ r ∈ Finset.Icc 1 n, if P.deg ∣ r then (P.deg : ℤ) * effCount k K ((n : ℤ) - r) else 0 := by
    intro P _
    have hd := P.deg_pos
    rw [← Finset.sum_filter]
    have himg : ((Finset.Icc 1 n).filter fun r ↦ P.deg ∣ r) =
        ((Finset.Icc 1 n).filter fun j ↦ j * P.deg ≤ n).image (· * P.deg) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, j, rfl⟩
        refine ⟨j, ⟨⟨?_, ?_⟩, ?_⟩, by ring⟩
        · rcases Nat.eq_zero_or_pos j with h | h
          · subst h; simp at h1
          · exact h
        · nlinarith
        · rw [mul_comm]; exact h2
      · rintro ⟨j, ⟨⟨h1, _⟩, h3⟩, rfl⟩
        exact ⟨⟨by nlinarith, h3⟩, Dvd.intro_left _ rfl⟩
    rw [himg, Finset.sum_image (fun a _ b _ h ↦ Nat.eq_of_mul_eq_mul_right hd h)]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun j ↦ j * P.deg ≤ n)]
    have hzero : ∑ j ∈ (Finset.Icc 1 n).filter (fun j ↦ ¬ j * P.deg ≤ n),
        (P.deg : ℤ) * effCount k K ((n : ℤ) - j * P.deg) = 0 := by
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have := (Finset.mem_filter.mp hj).2
      rw [effCount_neg (by omega), Nat.cast_zero, mul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast; rfl
  -- Steps E, F
  rw [stepC, Finset.sum_congr rfl stepD, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  obtain ⟨hr1, hrn⟩ := Finset.mem_Icc.mp hr
  rw [pointCount_eq_sum hr1 hrn, Finset.sum_mul]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  split_ifs <;> ring

/-! ### Power series form -/

variable (k K) in
/-- `∑_{r ≥ 1} N_r t^r`. -/
noncomputable def pointSeries : PowerSeries ℤ :=
  PowerSeries.mk fun r ↦ if r = 0 then 0 else (pointCount k K r : ℤ)

theorem coeff_X_mul_derivative {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    coeff n (X * d⁄dX R f) = n * coeff n f := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

/-- **`t Z'(t) = Z(t) ∑_{r ≥ 1} N_r t^r`**. -/
theorem X_mul_derivative_zeta :
    X * d⁄dX ℤ (zeta k K) = zeta k K * pointSeries k K := by
  ext n
  rw [coeff_X_mul_derivative, coeff_zeta, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ coeff i (zeta k K) *
      coeff j (pointSeries k K))]
  have h := mul_effCount_eq_sum (k := k) (K := K) n
  rw [h, ← Finset.sum_range_reflect]
  have hIcc : Finset.Icc 1 n = (Finset.range (n + 1)).filter (fun r ↦ r ≠ 0) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
  rw [hIcc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr' : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  simp only [pointSeries, coeff_mk, coeff_zeta, show n + 1 - 1 - r = n - r by omega,
    show n - (n - r) = r by omega]
  by_cases h0 : r = 0
  · simp [h0]
  · rw [if_pos h0, if_neg h0, mul_comm, Nat.cast_sub hr']

end WeilCurves.FunctionField
