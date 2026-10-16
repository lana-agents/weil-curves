/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Adeles

/-!
# The index of specialty

For a divisor `A` of `K / k` the *index of specialty* is
`i(A) = dim_k A_K / (A_K(A) + K)` (Stichtenoth, §1.5). We show that
this quotient is finite-dimensional and that

`ℓ(A) - i(A) = deg A - riemannConst k K`

(Stichtenoth, §1.5, where `riemannConst k K = g - 1` when `k` is the full constant field).
The key step is that `A_K = A_K(B) + K` as soon as `ℓ(B) = deg B - riemannConst k K`
(Stichtenoth, §1.5): for a repartition `α` choose `B' ≥ B` with `α ∈ A_K(B')`; then
`dim (A_K(B') + K) / (A_K(B) + K) = (deg B' - ℓ(B')) - (deg B - ℓ(B)) = 0`.

## Main definitions and results

* `WeilCurves.FunctionField.Divisor.iSpec A`: the index of specialty `i(A)`.
* `WeilCurves.FunctionField.Divisor.adeleSub_sup_diagK_eq_top`: `A_K(B) + K = A_K` when `B` has
  large degree.
* `WeilCurves.FunctionField.Divisor.relRank_repartitions`: `i(A)` is finite, equal to
  `ℓ(A) - deg A + riemannConst k K`.
* `WeilCurves.FunctionField.Divisor.ell_sub_iSpec`: `ℓ(A) - i(A) = deg A - riemannConst k K`.
-/

namespace WeilCurves.FunctionField

namespace Divisor

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

/-- Every repartition lies in some `A_K(B')` with `B' ≥ B`. -/
theorem exists_le_mem_adeleSub (B : Divisor k K) {α : Place k K → K}
    (hα : α ∈ repartitions k K) : ∃ B' : Divisor k K, B ≤ B' ∧ α ∈ adeleSub B' := by
  classical
  set S : Finset (Place k K) := (mem_repartitions.mp hα).toFinset ∪ B.support
  set E : Divisor k K := ∑ P ∈ S, Finsupp.single P (max 0 (-P.ord (α P) - B P))
  have hE : ∀ P, E P = if P ∈ S then max 0 (-P.ord (α P) - B P) else 0 := by
    intro P
    simp only [E, Finsupp.finsetSum_apply, Finsupp.single_apply]
    split_ifs with hP
    · rw [Finset.sum_eq_single P]
      · simp
      · intro Q _ hQ; simp [hQ]
      · intro h; exact absurd hP h
    · refine Finset.sum_eq_zero fun Q hQ ↦ ?_
      rw [if_neg]
      rintro rfl; exact hP hQ
  have hE0 : 0 ≤ E := fun P ↦ by rw [hE]; split_ifs <;> simp
  refine ⟨B + E, le_add_of_nonneg_right hE0, fun P ↦ ?_⟩
  by_cases h0 : α P = 0
  · exact Or.inl h0
  refine Or.inr ?_
  simp only [Finsupp.coe_add, Pi.add_apply, hE]
  split_ifs with hP
  · omega
  · have hS : P ∉ B.support ∧ α P ∈ P.1 := by
      simp only [S, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or,
        not_not] at hP
      exact ⟨hP.2, hP.1⟩
    rw [Finsupp.notMem_support_iff.mp hS.1]
    have := P.ord_nonneg_of_mem hS.2
    omega

/-- **`A_K = A_K(B) + K`** when `ℓ(B) = deg B - riemannConst k K` holds for all divisors of degree
at least `deg B` (Stichtenoth, §1.5). -/
theorem adeleSub_sup_diagK_eq_top {B : Divisor k K}
    (hB : ∀ C : Divisor k K, B.deg ≤ C.deg → (ell C : ℤ) = C.deg - riemannConst k K) :
    adeleSub B ⊔ diagK k K = (repartitions k K).restrictScalars k := by
  refine le_antisymm (sup_le (adeleSub_le B) diagK_le) fun α hα ↦ ?_
  obtain ⟨B', hBB', hαB'⟩ := exists_le_mem_adeleSub B hα
  have h := relRank_adeleSub_sup_diagK hBB'
  have h1 := hB B le_rfl
  have h2 := hB B' (deg_mono hBB')
  have h0 : ((B'.deg - ell B') - (B.deg - ell B)).toNat = 0 := by omega
  rw [h0, Nat.cast_zero] at h
  exact le_of_relRank_eq_zero h (Submodule.mem_sup_left hαB')

variable (k K) in
/-- A divisor `B ≥ A` beyond which Riemann's theorem holds. -/
theorem exists_le_riemann (A : Divisor k K) :
    ∃ B : Divisor k K, A ≤ B ∧
      ∀ C : Divisor k K, B.deg ≤ C.deg → (ell C : ℤ) = C.deg - riemannConst k K := by
  obtain ⟨N0, hN0⟩ := riemann_equality (k := k) (K := K)
  obtain P0 : Place k K := Classical.arbitrary _
  set m : ℤ := max 0 (N0 - A.deg)
  refine ⟨A + Finsupp.single P0 m, le_add_of_nonneg_right
    (Finsupp.single_nonneg.mpr (le_max_left _ _)), fun C hC ↦ hN0 C ?_⟩
  rw [deg_add, deg_single] at hC
  have h1 : (1 : ℤ) ≤ P0.deg := by exact_mod_cast P0.deg_pos
  have h2 : 0 ≤ m := le_max_left _ _
  have h3 : N0 - A.deg ≤ m := le_max_right _ _
  nlinarith

/-- **`i(A) = dim_k A_K / (A_K(A) + K)` is finite**, equal to `ℓ(A) - deg A + riemannConst k K`
(Stichtenoth, §1.5). -/
theorem relRank_repartitions (A : Divisor k K) :
    relRank (adeleSub A ⊔ diagK k K) ((repartitions k K).restrictScalars k) =
      (((ell A : ℤ) - A.deg + riemannConst k K).toNat : Cardinal) := by
  obtain ⟨B, hAB, hB⟩ := exists_le_riemann k K A
  rw [← adeleSub_sup_diagK_eq_top hB, relRank_adeleSub_sup_diagK hAB]
  have := hB B le_rfl
  congr 2
  omega

/-- The index of specialty `i(A) = dim_k A_K / (A_K(A) + K)`. -/
noncomputable def iSpec (A : Divisor k K) : ℕ :=
  Cardinal.toNat (relRank (adeleSub A ⊔ diagK k K) ((repartitions k K).restrictScalars k))

theorem iSpec_eq (A : Divisor k K) :
    (iSpec A : ℤ) = (ell A : ℤ) - A.deg + riemannConst k K := by
  rw [iSpec, relRank_repartitions, Cardinal.toNat_natCast]
  have := riemann_inequality A
  omega

/-- **`ℓ(A) - i(A) = deg A - riemannConst k K`** (Stichtenoth, §1.5; with
`riemannConst k K = g - 1` this is `ℓ(A) - i(A) = deg A + 1 - g`). -/
theorem ell_sub_iSpec (A : Divisor k K) :
    (ell A : ℤ) - iSpec A = A.deg - riemannConst k K := by
  rw [iSpec_eq]
  ring

end Divisor

end WeilCurves.FunctionField
