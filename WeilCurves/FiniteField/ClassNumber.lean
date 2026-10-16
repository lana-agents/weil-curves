/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FiniteField.Counting

/-!
# The class number and the number of effective divisors of degree `n`

For a function field `K` over a finite field `k` with `q` elements:

* each set `Cl(n)` of divisor classes of degree `n` is finite
  (`WeilCurves.FunctionField.finite_Cl`); the *class number* is `h = #Cl(0)`, and
  `#Cl(n) = h` whenever there is a divisor of degree `n` (`WeilCurves.FunctionField.card_Cl`);
* if `k` is the full constant field, the number `A_n` of effective divisors of degree `n`
  satisfies `A_n (q - 1) = ∑_{c ∈ Cl(n)} (q^{ℓ(c)} - 1)` (`WeilCurves.FunctionField.effCount_mul`),
  hence `A_n (q - 1) = #Cl(n) (q^{n + 1 - g} - 1)` for `n > 2g - 2`
  (`WeilCurves.FunctionField.effCount_mul_of_deg_gt`).
-/

namespace WeilCurves.FunctionField

open Divisor

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]

variable (k K) in
/-- The effective divisors of degree `n`. -/
def effDeg (n : ℤ) : Set (Divisor k K) := {E | 0 ≤ E ∧ E.deg = n}

variable (k K) in
/-- The number `A_n` of effective divisors of degree `n`. -/
noncomputable def effCount (n : ℤ) : ℕ := Nat.card (effDeg k K n)

variable (k K) in
/-- The divisor classes of degree `n`. -/
def Cl (n : ℤ) : Set (Pic k K) := {c | Pic.deg k K c = n}

theorem mk_eq_mk_iff {A E : Divisor k K} :
    (QuotientAddGroup.mk A : Pic k K) = QuotientAddGroup.mk E ↔ E - A ∈ principal k K := by
  rw [QuotientAddGroup.eq, neg_add_eq_sub]

/-- Classes of degree `≥ riemannConst + 1` contain effective divisors. -/
theorem Cl_subset_image_effDeg {n : ℤ} (hn : riemannConst k K + 1 ≤ n) :
    Cl k K n ⊆ QuotientAddGroup.mk '' effDeg k K n := by
  intro c hc
  obtain ⟨A, rfl⟩ := QuotientAddGroup.mk_surjective c
  simp only [Cl, Set.mem_setOf_eq, Pic.deg_mk] at hc
  have h := riemann_inequality A
  obtain ⟨f, hf, hf0⟩ := exists_ne_zero_mem_L (A := A) (by omega)
  refine ⟨A + div k f, ⟨(mem_L_of_ne_zero hf0).mp hf, by rw [deg_add, deg_div, add_zero, hc]⟩, ?_⟩
  rw [mk_eq_mk_iff, sub_add_cancel_left]
  exact neg_mem (div_mem_principal hf0)

/-- Translation by the class of `D` maps `Cl(n)` bijectively onto `Cl(n + deg D)`. -/
theorem mem_Cl_add_iff {n : ℤ} (D : Divisor k K) (c : Pic k K) :
    c + QuotientAddGroup.mk D ∈ Cl k K (n + D.deg) ↔ c ∈ Cl k K n := by
  simp only [Cl, Set.mem_setOf_eq, map_add, Pic.deg_mk, add_left_inj]

/-- **Each `Cl(n)` is finite.** -/
theorem finite_Cl (n : ℤ) : (Cl k K n).Finite := by
  obtain P0 : Place k K := Classical.arbitrary _
  set m : ℤ := |riemannConst k K + 1 - n|
  set D : Divisor k K := Finsupp.single P0 m
  have hD : D.deg = m * P0.deg := deg_single _ _
  have hP0 : (1 : ℤ) ≤ P0.deg := by exact_mod_cast P0.deg_pos
  have hm : riemannConst k K + 1 - n ≤ m := le_abs_self _
  have hm0 : 0 ≤ m := abs_nonneg _
  have hn' : riemannConst k K + 1 ≤ n + D.deg := by rw [hD]; nlinarith
  have hfin : (Cl k K (n + D.deg)).Finite :=
    ((finite_setOf_effective_deg_eq (n + D.deg)).image _).subset (Cl_subset_image_effDeg hn')
  refine (hfin.preimage (f := fun c : Pic k K ↦ c + QuotientAddGroup.mk D)
    (add_left_injective _).injOn).subset fun c hc ↦ ?_
  exact (mem_Cl_add_iff D c).mpr hc

variable (k K) in
/-- The class number `h = #Cl(0)`. -/
noncomputable def classNumber : ℕ := Nat.card (Cl k K 0)

/-- `#Cl(n) = h` when there is a divisor of degree `n`. -/
theorem card_Cl {D : Divisor k K} : Nat.card (Cl k K D.deg) = classNumber k K := by
  symm
  refine Nat.card_congr
    { toFun := fun c ↦ ⟨c.1 + QuotientAddGroup.mk D, by
        have := (mem_Cl_add_iff (n := 0) D c.1).mpr c.2; rwa [zero_add] at this⟩
      invFun := fun c ↦ ⟨c.1 - QuotientAddGroup.mk D, by
        rw [← mem_Cl_add_iff (n := 0) D, sub_add_cancel, zero_add]; exact c.2⟩
      left_inv := fun c ↦ by simp
      right_inv := fun c ↦ by simp }

/-- `A_n = ∑_{c ∈ Cl(n)} #{E ≥ 0 | E ∼ c}`. -/
theorem effCount_eq_sum (n : ℤ) :
    effCount k K n = ∑ c ∈ (finite_Cl (k := k) (K := K) n).toFinset,
      Nat.card (effClass (Quotient.out c : Divisor k K)) := by
  classical
  have : Fintype (effDeg k K n) := (finite_setOf_effective_deg_eq n).fintype
  set T := (finite_Cl (k := k) (K := K) n).toFinset
  let cls : effDeg k K n → T := fun E ↦ ⟨QuotientAddGroup.mk E.1, by
    rw [Set.Finite.mem_toFinset]; exact E.2.2⟩
  have hfib : ∀ c : T, Nat.card {E // cls E = c} = Nat.card (effClass (Quotient.out c.1)) := by
    intro c
    refine Nat.card_congr
      { toFun := fun E ↦ ⟨E.1.1, E.1.2.1, by
          rw [← mk_eq_mk_iff, QuotientAddGroup.out_eq']
          exact (congrArg Subtype.val E.2).symm⟩
        invFun := fun E ↦ ⟨⟨E.1, E.2.1, by
            have hc := (Set.Finite.mem_toFinset _).mp c.2
            have h := deg_eq_zero_of_mem_principal E.2.2
            rw [deg_sub] at h
            have h2 : (Quotient.out c.1 : Divisor k K).deg = n := by
              rw [← Pic.deg_mk, QuotientAddGroup.out_eq']; exact hc
            omega⟩, by
          apply Subtype.ext
          change (QuotientAddGroup.mk E.1 : Pic k K) = c.1
          have h1 : (QuotientAddGroup.mk (Quotient.out c.1) : Pic k K) = QuotientAddGroup.mk E.1 :=
            mk_eq_mk_iff.mpr E.2.2
          rw [QuotientAddGroup.out_eq'] at h1
          exact h1.symm⟩
        left_inv := fun E ↦ rfl
        right_inv := fun E ↦ rfl }
  rw [effCount, ← Nat.card_congr (Equiv.sigmaFiberEquiv cls), Nat.card_sigma,
    ← Finset.sum_coe_sort T]
  exact Finset.sum_congr rfl fun c _ ↦ hfib c

/-- **`A_n (q - 1) = ∑_{c ∈ Cl(n)} (q^{ℓ(c)} - 1)`**. -/
theorem effCount_mul (hk : IsFullConstantField k K) (n : ℤ) :
    effCount k K n * (Nat.card k - 1) =
      ∑ c ∈ (finite_Cl (k := k) (K := K) n).toFinset, (Nat.card k ^ Pic.ell c - 1) := by
  rw [effCount_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have h := card_effClass hk (Quotient.out c)
  have hell : Pic.ell c = ell (Quotient.out c : Divisor k K) := by
    rw [← Pic.ell_mk, QuotientAddGroup.out_eq']
  rw [hell]
  omega

/-- **`A_n (q - 1) = #Cl(n) (q^{n + 1 - g} - 1)` for `n > 2g - 2`**. -/
theorem effCount_mul_of_deg_gt (hk : IsFullConstantField k K) {n : ℤ}
    (hn : 2 * genus k K - 2 < n) :
    effCount k K n * (Nat.card k - 1) =
      Nat.card (Cl k K n) * (Nat.card k ^ (n + 1 - genus k K).toNat - 1) := by
  rw [effCount_mul hk, Nat.card_eq_card_finite_toFinset (finite_Cl n), ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [Set.Finite.mem_toFinset] at hc
  obtain ⟨A, rfl⟩ := QuotientAddGroup.mk_surjective c
  simp only [Cl, Set.mem_setOf_eq, Pic.deg_mk] at hc
  rw [Pic.ell_mk]
  have := ell_eq_of_deg_gt (A := A) (by omega)
  congr 2
  omega

end WeilCurves.FunctionField
