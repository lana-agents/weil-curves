/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Bombieri.Automorphism

/-!
# Elements with prescribed pole orders at a rational place

Let `α` be a place of degree one of a function field `F` over a finite field `k` which is the
full constant field, and `R_t = L(t α)`. Since `ℓ(R_t) ≤ ℓ(R_{t-1}) + 1`, with equality only if
some element of `R_t` has a pole of exact order `t` at `α`, the set `J` of pole orders
`j ∈ [0, m]` realised in `R_m` has at least `ℓ(R_m)` elements
(`WeilCurves.FunctionField.ell_le_card_poleOrders`). This is the basis with strictly increasing
pole orders used in Bombieri's proof (Nivedita, §3.2.2, proof of Lemma 3.7).
-/

namespace WeilCurves.FunctionField

open Divisor

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k] [IsFunctionField k F]

/-- The ultrametric inequality for finite sums. -/
theorem Place.ord_sum_ge (P : Place k F) {ι : Type*} (s : Finset ι) (f : ι → F) (M : ℤ)
    (h : ∀ j ∈ s, f j = 0 ∨ M ≤ P.ord (f j)) : ∑ j ∈ s, f j = 0 ∨ M ≤ P.ord (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have ih' := ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
    have ha' := h a (Finset.mem_insert_self a s)
    by_cases hs : f a + ∑ j ∈ s, f j = 0
    · exact Or.inl hs
    refine Or.inr ?_
    rcases ha' with h1 | h1
    · rw [h1, zero_add] at hs ⊢
      rcases ih' with h2 | h2
      · exact absurd h2 hs
      · exact h2
    rcases ih' with h2 | h2
    · rw [h2, add_zero]; exact h1
    exact (le_min h1 h2).trans (P.min_le_ord_add hs)

variable (α : Place k F) (m : ℕ)

open Classical in
/-- The pole orders `j ∈ [0, m]` realised by elements of `L(m α)`. -/
noncomputable def poleOrders : Finset ℕ :=
  (Finset.range (m + 1)).filter fun j ↦
    ∃ h ∈ L (Finsupp.single α (m : ℤ)), h ≠ 0 ∧ α.ord h = -(j : ℤ)

theorem mem_poleOrders {j : ℕ} : j ∈ poleOrders α m ↔
    j ≤ m ∧ ∃ h ∈ L (Finsupp.single α (m : ℤ)), h ≠ 0 ∧ α.ord h = -(j : ℤ) := by
  classical
  simp only [poleOrders, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/-- Without a pole of exact order `t`, `L(t α) = L((t-1) α)`. -/
theorem L_eq_of_notMem_poleOrders {t : ℕ} (_ht1 : 1 ≤ t) (htm : t ≤ m)
    (ht : t ∉ poleOrders α m) :
    L (Finsupp.single α (t : ℤ)) = L (Finsupp.single α ((t : ℤ) - 1)) := by
  classical
  apply le_antisymm _ (L_mono (Finsupp.single_le_single.mpr (by omega)))
  intro h hh
  by_cases h0 : h = 0
  · rw [h0]; exact zero_mem _
  rw [mem_L_of_ne_zero h0] at hh ⊢
  intro β
  have hβ := hh β
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply, div_apply] at hβ ⊢
  split_ifs at hβ ⊢ with hα
  · subst hα
    rcases (by omega : α.ord h = -(t : ℤ) ∨ -(t : ℤ) + 1 ≤ α.ord h) with h1 | h1
    · exfalso
      apply ht
      rw [mem_poleOrders]
      refine ⟨htm, h, L_mono (Finsupp.single_le_single.mpr (by exact_mod_cast htm : (t : ℤ) ≤ m))
        ((mem_L_of_ne_zero h0).mpr fun β' ↦ ?_), h0, h1⟩
      exact hh β'
    · omega
  · exact hβ

variable [Finite k]

/-- **`ℓ(L(t α)) ≤ #{j ∈ J | j ≤ t}`** for `t ≤ m`. -/
theorem ell_le_card_poleOrders_le (hk : IsFullConstantField k F) (hα : α.deg = 1) :
    ∀ t : ℕ, t ≤ m →
      ell (Finsupp.single α (t : ℤ)) ≤ ((poleOrders α m).filter fun j ↦ j ≤ t).card := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    rw [Nat.cast_zero, Finsupp.single_zero, ell_zero_eq_one hk]
    apply Finset.card_pos.mpr
    refine ⟨0, Finset.mem_filter.mpr ⟨(mem_poleOrders α m).mpr ⟨Nat.zero_le _, 1, ?_,
      one_ne_zero, by simp⟩, le_rfl⟩⟩
    refine (mem_L_of_ne_zero one_ne_zero).mpr fun β ↦ ?_
    simp only [Finsupp.coe_add, Pi.add_apply, div_apply, Place.ord_one, add_zero]
    exact Finsupp.single_nonneg.mpr (by positivity) β
  | succ t ih =>
    intro htm
    have ih' := ih (by omega)
    have hstep := (step (Finsupp.single α (t : ℤ)) α).2
    rw [← Finsupp.single_add, hα] at hstep
    push_cast at hstep ⊢
    by_cases hmem : t + 1 ∈ poleOrders α m
    · have : ((poleOrders α m).filter fun j ↦ j ≤ t + 1) =
          insert (t + 1) ((poleOrders α m).filter fun j ↦ j ≤ t) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge t j with h | h
          · left; omega
          · right; exact ⟨h1, h⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hmem, le_rfl⟩
          · exact ⟨h1, by omega⟩
      rw [this, Finset.card_insert_of_notMem (by simp)]
      omega
    · have hL := L_eq_of_notMem_poleOrders α m (t := t + 1) (by omega) htm hmem
      have : ell (Finsupp.single α ((t : ℤ) + 1)) = ell (Finsupp.single α (t : ℤ)) := by
        rw [ell, ell]
        push_cast at hL
        rw [hL, add_sub_cancel_right]
      have hfilt : ((poleOrders α m).filter fun j ↦ j ≤ t + 1) =
          ((poleOrders α m).filter fun j ↦ j ≤ t) := by
        ext j; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases Nat.lt_or_ge t j with h | h
          · exact absurd (show j = t + 1 by omega ▸ h1) hmem
          · exact h
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      rw [this, hfilt]
      exact ih'

/-- **`ℓ(L(m α)) ≤ #J`**. -/
theorem ell_le_card_poleOrders (hk : IsFullConstantField k F) (hα : α.deg = 1) :
    ell (Finsupp.single α (m : ℤ)) ≤ (poleOrders α m).card := by
  have := ell_le_card_poleOrders_le α m hk hα m le_rfl
  refine this.trans (Finset.card_le_card (Finset.filter_subset _ _))

end WeilCurves.FunctionField
