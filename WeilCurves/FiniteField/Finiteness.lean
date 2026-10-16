/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.RiemannRoch
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Int.Interval

/-!
# Function fields over a finite field: finiteness

For a function field `K` over a finite field `k`:

* there are only finitely many places of degree `≤ d`
  (`WeilCurves.FunctionField.finite_setOf_deg_le`): fix a transcendental `t`; a place `P ∋ t` of
  degree `≤ d` is a zero of `p(t)` for the minimal polynomial `p` (of degree `≤ d`) of the
  residue of `t`, and there are finitely many such `p` and finitely many zeros of each `p(t)`;
  the places not containing `t` are poles of `t`;
* there are only finitely many effective divisors of each degree
  (`WeilCurves.FunctionField.finite_setOf_effective_deg_eq`).
-/

open Polynomial

namespace WeilCurves.FunctionField

open Divisor

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]

/-- Polynomials of degree `≤ d` over a finite field form a finite set. -/
theorem finite_setOf_natDegree_le (d : ℕ) : {p : k[X] | p.natDegree ≤ d}.Finite := by
  refine (Set.finite_range fun c : Fin (d + 1) → k ↦ ∑ i : Fin (d + 1), monomial i (c i)).subset
    fun p hp ↦ ⟨fun i ↦ p.coeff i, ?_⟩
  simp only [Set.mem_setOf_eq] at hp
  conv_rhs => rw [p.as_sum_range' (d + 1) (Nat.lt_succ_of_le hp)]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ monomial i (p.coeff i)) (d + 1)

/-- **There are only finitely many places of degree `≤ d`.** -/
theorem finite_setOf_deg_le (d : ℕ) : {P : Place k K | P.deg ≤ d}.Finite := by
  obtain ⟨t, ht⟩ := exists_transcendental k K
  have hpoles := Place.finite_setOf_notMem (k := k) t
  have hzeros : {P : Place k K | ∃ p ∈ {p : k[X] | p.natDegree ≤ d}, 0 < P.ord (aeval t p)}.Finite
    := by
    have : {P : Place k K | ∃ p ∈ {p : k[X] | p.natDegree ≤ d}, 0 < P.ord (aeval t p)} =
        ⋃ p ∈ {p : k[X] | p.natDegree ≤ d}, {P : Place k K | 0 < P.ord (aeval t p)} := by
      ext P; simp
    rw [this]
    exact (finite_setOf_natDegree_le d).biUnion fun p _ ↦ Place.finite_setOf_ord_pos _
  refine (hzeros.union hpoles).subset fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq] at hP
  by_cases htP : t ∈ P.1
  · left
    refine ⟨minpoly k (P.residue ⟨t, htP⟩), ?_, Divisor.ord_aeval_minpoly_residue_pos ht P htP⟩
    simp only [Set.mem_setOf_eq]
    exact (minpoly.natDegree_le _).trans hP
  · exact Or.inr htP

omit [Finite k] [IsFunctionField k K] in
/-- A place in the support of an effective divisor has degree at most its degree. -/
theorem deg_le_of_effective {E : Divisor k K} (hE : 0 ≤ E) {P : Place k K} (hP : E P ≠ 0) :
    (P.deg : ℤ) ≤ E.deg := by
  classical
  have h1 : Finsupp.single P (1 : ℤ) ≤ E := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ
      have h0 : 0 ≤ E Q := hE Q
      simp only [Finsupp.single_eq_same]
      omega
    · simp only [Finsupp.single_apply, if_neg (Ne.symm hQ)]; exact hE Q
  have := deg_mono h1
  rwa [deg_single, one_mul] at this

/-- **There are only finitely many effective divisors of degree `n`.** -/
theorem finite_setOf_effective_deg_eq (n : ℤ) :
    {E : Divisor k K | 0 ≤ E ∧ E.deg = n}.Finite := by
  classical
  have hS := finite_setOf_deg_le (k := k) (K := K) n.toNat
  set T := hS.toFinset
  set M : Divisor k K := ∑ P ∈ T, Finsupp.single P n
  refine (Set.finite_Icc (0 : Place k K →₀ ℤ) M).subset fun E ⟨hE, hdeg⟩ ↦ ⟨hE, fun P ↦ ?_⟩
  have hM : M P = if P ∈ T then n else 0 := by
    simp only [M, Finsupp.finsetSum_apply, Finsupp.single_apply]
    split_ifs with hP
    · rw [Finset.sum_eq_single P (fun Q _ hQ ↦ if_neg hQ) (fun h ↦ absurd hP h), if_pos rfl]
    · exact Finset.sum_eq_zero fun Q hQ ↦ if_neg (by rintro rfl; exact hP hQ)
  rw [hM]
  by_cases hEP : E P = 0
  · rw [hEP]; split_ifs
    · rw [← hdeg]; exact deg_nonneg hE
    · exact le_rfl
  have hdegP := deg_le_of_effective hE hEP
  have hPT : P ∈ T := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have : (P.deg : ℤ) ≤ n := hdeg ▸ hdegP
    omega
  rw [if_pos hPT]
  have h1 : Finsupp.single P (E P) ≤ E := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ; simp
    · simp only [Finsupp.single_apply, if_neg (Ne.symm hQ)]; exact hE Q
  have h2 := deg_mono h1
  rw [deg_single] at h2
  have hP1 : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hEP0 : 0 ≤ E P := hE P
  nlinarith

end WeilCurves.FunctionField
