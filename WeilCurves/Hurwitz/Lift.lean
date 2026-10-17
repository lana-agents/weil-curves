/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Hurwitz.Different
import WeilCurves.FunctionField.Specialty

/-!
# Approximation and the local trace estimates

* `exists_approx`: an approximation theorem for finitely many places (from `A = A(B) + K` for
  divisors `B` of large degree, `adeleSub_sup_diagK_eq_top`, with an auxiliary place outside the
  given set carrying the extra degree);
* the local lattices `Λ_P(B) = {z ∈ L | ∀ Q | P, ord_Q z ≥ -B(Q)}` (`InLam`) and, for a divisor
  `W` of `K` and `D = Con_{L/K} W + Diff(L/K)`, the three local facts behind the cotrace
  (Stichtenoth §III.4): `Tr(Λ_P(D)) ⊆ {ord_P ≥ -W(P)}` (`trace_ord_of_inLam`), equality
  (`exists_lift`), and `Tr(Λ_P(D + Q)) ⊄ {ord_P ≥ -W(P)}` for `Q | P`, more precisely
  `Tr(Λ_P(D + Q)) ⊇ {ord_P ≥ -W(P) - 1}` (`exists_lift_sharp`).
-/

open IsDedekindDomain Module

set_option linter.unusedSectionVars false

namespace WeilCurves.FunctionField

section Approx

variable {k M : Type*} [Field k] [Field M] [Algebra k M] [PerfectField k] [IsFunctionField k M]

/-- **Approximation**: given a finite set `T` of places, a place `Q₀ ∉ T`, a divisor `A` and
targets `α`, some `x` satisfies `ord_Q(α_Q - x) ≥ -A(Q)` for all `Q ∈ T`. -/
theorem exists_approx (A : Divisor k M) (T : Finset (Place k M)) (Q₀ : Place k M)
    (hQ₀ : Q₀ ∉ T) (α : Place k M → M) :
    ∃ x : M, ∀ Q ∈ T, α Q - x = 0 ∨ -A Q ≤ Q.ord (α Q - x) := by
  classical
  obtain ⟨B₀, -, hB₀⟩ := Divisor.exists_le_riemann k M 0
  set E : Divisor k M := ∑ Q ∈ T, Finsupp.single Q (A Q)
  have hE : ∀ Q, E Q = if Q ∈ T then A Q else 0 := by
    intro Q
    simp only [E, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  set m : ℤ := max 0 (B₀.deg - E.deg)
  set B : Divisor k M := E + Finsupp.single Q₀ m
  have hBQ : ∀ Q ∈ T, B Q = A Q := by
    intro Q hQ
    have hne : Q₀ ≠ Q := fun h ↦ hQ₀ (h ▸ hQ)
    simp only [B, Finsupp.coe_add, Pi.add_apply, hE, if_pos hQ, Finsupp.single_apply,
      if_neg hne, add_zero]
  have hdeg : B₀.deg ≤ B.deg := by
    have h1 : (1 : ℤ) ≤ Q₀.deg := by exact_mod_cast Q₀.deg_pos
    have h2 : 0 ≤ m := le_max_left _ _
    have h3 : B₀.deg - E.deg ≤ m := le_max_right _ _
    rw [Divisor.deg_add, Divisor.deg_single]
    nlinarith
  have hB : ∀ C : Divisor k M, B.deg ≤ C.deg →
      (Divisor.ell C : ℤ) = C.deg - Divisor.riemannConst k M :=
    fun C hC ↦ hB₀ C (hdeg.trans hC)
  set α' : Place k M → M := fun Q ↦ if Q ∈ T then α Q else 0
  have hα' : α' ∈ (repartitions k M).restrictScalars k := by
    refine (T.finite_toSet).subset fun Q hQ ↦ ?_
    by_contra hQT
    simp only [Set.mem_setOf_eq, α'] at hQ
    rw [if_neg (by simpa using hQT)] at hQ
    exact hQ Q.1.zero_mem
  rw [← Divisor.adeleSub_sup_diagK_eq_top hB, Submodule.mem_sup] at hα'
  obtain ⟨β, hβ, γ, ⟨x, rfl⟩, hβγ⟩ := hα'
  refine ⟨x, fun Q hQ ↦ ?_⟩
  have h := congrFun hβγ Q
  simp only [Pi.add_apply, diag_apply, α', if_pos hQ] at h
  have hβQ : β Q = α Q - x := by rw [← h]; ring
  rw [← hβQ, ← hBQ Q hQ]
  exact hβ Q

end Approx

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {L : Type*} [Field L] [Algebra K L]
  [Algebra k L] [IsScalarTower k K L] [PerfectField k] [IsFunctionField k K]
  [IsFunctionField k L] [FiniteDimensional K L]

/-- `z` lies in the local lattice `Λ_P(B) = {z | ∀ Q | P, ord_Q z ≥ -B(Q)}`. -/
def InLam (P : Place k K) (B : Divisor k L) (z : L) : Prop :=
  ∀ Q : Place k L, Q.restrict (K := K) = P → z = 0 ∨ -B Q ≤ Q.ord z

theorem InLam.mono {P : Place k K} {B B' : Divisor k L} (h : B ≤ B') {z : L}
    (hz : InLam P B z) : InLam P B' z := fun Q hQ ↦
  (hz Q hQ).imp_right fun h' ↦ (neg_le_neg (h Q)).trans h'

/-- `ord_Q (y z) = e(Q|P) ord_P y + ord_Q z`. -/
theorem ord_algebraMap_mul (Q : Place k L) {y : K} (hy : y ≠ 0) {z : L} (hz : z ≠ 0) :
    Q.ord (algebraMap K L y * z) = ramIndex K Q * (Q.restrict (K := K)).ord y + Q.ord z := by
  rw [Q.ord_mul ((map_ne_zero _).mpr hy) hz, ord_algebraMap_eq_ramIndex_mul]


section Separable

variable [Algebra.IsSeparable K L]

theorem InLam.mem_intClo {P : Place k K} {B : Divisor k L}
    (hB : ∀ Q : Place k L, Q.restrict (K := K) = P → B Q ≤ 0) {z : L} (hz : InLam P B z) :
    z ∈ intClo L P := by
  refine mem_intClo_iff.mpr fun Q hQ ↦ ?_
  rcases hz Q hQ with h | h
  · rw [h]; exact Q.1.zero_mem
  · exact Q.mem_of_ord_nonneg (by have := hB Q hQ; omega)

/-- The bound `-D(Q)` for `D = Con W + Diff`, rewritten. -/
theorem conormOf_add_different_apply (W : Divisor k K) (Q : Place k L) :
    (conormOf L W + different k K L) Q =
      ramIndex K Q * W (Q.restrict (K := K)) - Q.ord (codiffGen L (Q.restrict (K := K))) := by
  simp only [Finsupp.coe_add, Pi.add_apply, conormOf_apply, different_apply, diffExp]
  ring

/-- `Tr(Λ_P(Con W + Diff)) ⊆ {ord_P ≥ -W(P)}`. -/
theorem trace_ord_of_inLam {P : Place k K} (W : Divisor k K) {z : L}
    (hz : InLam P (conormOf L W + different k K L) z) :
    Algebra.trace K L z = 0 ∨ -W P ≤ P.ord (Algebra.trace K L z) := by
  set π := unifier P
  have hπ0 : π ≠ 0 := by intro h; have := ord_unifier P; rw [← show π = unifier P from rfl, h,
    P.ord_zero] at this; omega
  set y : K := π ^ (W P)
  have hy0 : y ≠ 0 := zpow_ne_zero _ hπ0
  have hyord : P.ord y = W P := by rw [Place.ord_zpow, ord_unifier, mul_one]
  have hcod : IsCodiff L P (algebraMap K L y * z) := by
    rw [isCodiff_iff_ord]
    intro Q hQ
    by_cases hz0 : z = 0
    · exact Or.inl (by rw [hz0, mul_zero])
    refine Or.inr ?_
    rcases hz Q hQ with h | h
    · exact absurd h hz0
    rw [ord_algebraMap_mul Q hy0 hz0, hQ, hyord]
    rw [conormOf_add_different_apply, hQ] at h
    linarith
  have htr := trace_mem_of_isCodiff hcod
  rw [trace_algebraMap_mul] at htr
  by_cases ht : Algebra.trace K L z = 0
  · exact Or.inl ht
  refine Or.inr ?_
  have := P.ord_nonneg_of_mem htr
  rw [P.ord_mul hy0 ht, hyord] at this
  omega

/-- `Tr(Λ_P(Con W + Diff)) ⊇ {ord_P ≥ -W(P)}`. -/
theorem exists_lift {P : Place k K} (W : Divisor k K) {u : K} (hu : u = 0 ∨ -W P ≤ P.ord u) :
    ∃ z : L, Algebra.trace K L z = u ∧ InLam P (conormOf L W + different k K L) z := by
  set π := unifier P
  have hπ0 : π ≠ 0 := by intro h; have := ord_unifier P; rw [← show π = unifier P from rfl, h,
    P.ord_zero] at this; omega
  have hyord : ∀ n : ℤ, P.ord (π ^ n) = n := fun n ↦ by
    rw [Place.ord_zpow, ord_unifier, mul_one]
  have hv : π ^ (W P) * u ∈ P.1 := by
    rcases hu with h | h
    · rw [h, mul_zero]; exact P.1.zero_mem
    by_cases hu0 : u = 0
    · rw [hu0, mul_zero]; exact P.1.zero_mem
    refine P.mem_of_ord_nonneg ?_
    rw [P.ord_mul (zpow_ne_zero _ hπ0) hu0, hyord]
    omega
  obtain ⟨z₀, hz₀, htr⟩ := exists_isCodiff_trace_eq (L := L) hv
  refine ⟨algebraMap K L (π ^ (-W P)) * z₀, ?_, fun Q hQ ↦ ?_⟩
  · rw [trace_algebraMap_mul, htr, ← mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero,
      one_mul]
  by_cases hz0 : z₀ = 0
  · exact Or.inl (by rw [hz0, mul_zero])
  refine Or.inr ?_
  rcases isCodiff_iff_ord.mp hz₀ Q hQ with h | h
  · exact absurd h hz0
  rw [ord_algebraMap_mul Q (zpow_ne_zero _ hπ0) hz0, hQ, hyord, conormOf_add_different_apply, hQ]
  linarith

/-- `Tr(Λ_P(Con W + Diff + Q₀)) ⊇ {ord_P ≥ -W(P) - 1}` for `Q₀ | P`. -/
theorem exists_lift_sharp {P : Place k K} (W : Divisor k K) {Q₀ : Place k L}
    (hQ₀ : Q₀.restrict (K := K) = P) {u : K} (hu : u = 0 ∨ -(W P + 1) ≤ P.ord u) :
    ∃ z : L, Algebra.trace K L z = u ∧
      InLam P (conormOf L W + different k K L + Finsupp.single Q₀ 1) z := by
  set π := unifier P
  have hπ0 : π ≠ 0 := by intro h; have := ord_unifier P; rw [← show π = unifier P from rfl, h,
    P.ord_zero] at this; omega
  have hyord : ∀ n : ℤ, P.ord (π ^ n) = n := fun n ↦ by
    rw [Place.ord_zpow, ord_unifier, mul_one]
  obtain ⟨z₁, hz₁', hz₁Q, htr₁⟩ := exists_sharp (L := L) hQ₀
  set t := Algebra.trace K L z₁
  have ht0 : t ≠ 0 := fun h ↦ htr₁ (by rw [h]; exact P.1.zero_mem)
  have ht1 : P.ord t ≤ -1 := by
    by_contra h
    exact htr₁ (P.mem_of_ord_nonneg (by omega))
  have hz₁0 : z₁ ≠ 0 := by rintro h; apply ht0; simp [t, h]
  set v := π ^ (W P) * u
  by_cases hv0 : v = 0
  · refine ⟨0, ?_, fun Q _ ↦ Or.inl rfl⟩
    rw [map_zero]
    have : u = 0 := by
      rcases mul_eq_zero.mp hv0 with h | h
      · exact absurd h (zpow_ne_zero _ hπ0)
      · exact h
    exact this.symm
  have hu0 : u ≠ 0 := by rintro rfl; exact hv0 (mul_zero _)
  have hvord : -1 ≤ P.ord v := by
    rcases hu with h | h
    · exact absurd h hu0
    rw [P.ord_mul (zpow_ne_zero _ hπ0) hu0, hyord]
    omega
  have hst : 0 ≤ P.ord (v / t) := by rw [P.ord_div hv0 ht0]; omega
  have hst0 : v / t ≠ 0 := div_ne_zero hv0 ht0
  set z₀ := algebraMap K L (v / t) * z₁
  have hz₀0 : z₀ ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hst0) hz₁0
  refine ⟨algebraMap K L (π ^ (-W P)) * z₀, ?_, fun Q hQ ↦ Or.inr ?_⟩
  · rw [trace_algebraMap_mul, trace_algebraMap_mul, div_mul_cancel₀ _ ht0, ← mul_assoc,
      ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, one_mul]
  have he := ramIndex_pos (K := K) Q
  have hz₀Q : Q.ord z₀ = ramIndex K Q * P.ord (v / t) + Q.ord z₁ := by
    rw [ord_algebraMap_mul Q hst0 hz₁0, hQ]
  have hnn : 0 ≤ ramIndex K Q * P.ord (v / t) := mul_nonneg he.le hst
  rw [ord_algebraMap_mul Q (zpow_ne_zero _ hπ0) hz₀0, hQ, hyord, hz₀Q]
  classical
  rw [Finsupp.add_apply, conormOf_add_different_apply, hQ, Finsupp.single_apply]
  split_ifs with hQQ
  · subst hQQ
    linarith
  · have := hz₁' Q hQ (Ne.symm hQQ)
    linarith

end Separable

end WeilCurves.FunctionField
