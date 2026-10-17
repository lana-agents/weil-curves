/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Bombieri.PoleOrder

/-!
# Bombieri's bound

Following Nivedita (*Riemann hypothesis for function fields*, CMI 2009), §3.2.2, Theorem 3.6 and
Lemma 3.7, and Kedlaya (*Weil cohomology* notes), Theorem 5.1.5 and Lemma 5.1.7 (twisted form):

Let `F` be a function field over a finite field `k` with `Q = p^{2b}` elements (`k` the full
constant field), of genus `g` with `(g + 1)^4 < Q`, `α` a place of degree one and `τ` a
`k`-automorphism of `F`. If `S` is a finite set of places `β ≠ α, τα` at which `τ` acts as the
`Q`-th power map (`x^Q ≡ τ x mod β`), then `∑_{β ∈ S} deg β ≤ Q + (2g + 1) √Q`
(`WeilCurves.FunctionField.bombieri`).

This file contains the preliminaries: the space `L(l α)^{p^b}` of `p^b`-th powers, the
product rule `L(A) L(B) ⊆ L(A + B)`, and Lemma 3.7 (the map `∑ u_j h_j^Q` is injective on
`(L(l α)^{p^b})^J` when `l p^b < Q`).
-/

namespace WeilCurves.FunctionField

open Divisor

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem mul_mem_L_add [PerfectField k] [IsFunctionField k F] {A B : Divisor k F} {f g : F}
    (hf : f ∈ L A) (hg : g ∈ L B) : f * g ∈ L (A + B) := by
  rcases mem_L.mp hf with rfl | hf
  · rw [zero_mul]; exact zero_mem _
  rcases mem_L.mp hg with rfl | hg
  · rw [mul_zero]; exact zero_mem _
  by_cases h0 : f * g = 0
  · rw [h0]; exact zero_mem _
  refine mem_L.mpr (Or.inr fun P ↦ ?_)
  rw [P.ord_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0)]
  simp only [Finsupp.coe_add, Pi.add_apply, neg_add]
  linarith [hf P, hg P]

variable [Finite k] (p b : ℕ) [Fact p.Prime] [CharP k p]

/-- The `k`-subspace `{g^{p^b} | g ∈ V}` of `p^b`-th powers of a `k`-subspace `V`. -/
def powSub (V : Submodule k F) : Submodule k F where
  carrier := {x | ∃ g ∈ V, g ^ p ^ b = x}
  zero_mem' := ⟨0, zero_mem _, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
  add_mem' := by
    have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
    rintro _ _ ⟨g₁, h₁, rfl⟩ ⟨g₂, h₂, rfl⟩
    exact ⟨g₁ + g₂, add_mem h₁ h₂, by rw [add_pow_char_pow]⟩
  smul_mem' := by
    rintro c _ ⟨g, hg, rfl⟩
    refine ⟨(iterateFrobeniusEquiv k p b).symm c • g, V.smul_mem _ hg, ?_⟩
    rw [smul_pow, ← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]

theorem mem_powSub {V : Submodule k F} {x : F} : x ∈ powSub p b V ↔ ∃ g ∈ V, g ^ p ^ b = x :=
  Iff.rfl

/-- `dim V ≤ dim V^{p^b}`. -/
theorem finrank_le_finrank_powSub (V : Submodule k F) [FiniteDimensional k V]
    [FiniteDimensional k (powSub p b V)] :
    Module.finrank k V ≤ Module.finrank k (powSub p b V) := by
  have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  set bas := Module.finBasis k V
  have hmem : ∀ i, ((bas i : F)) ^ p ^ b ∈ powSub p b V := fun i ↦ ⟨_, (bas i).2, rfl⟩
  let w : Fin (Module.finrank k V) → powSub p b V := fun i ↦ ⟨_, hmem i⟩
  have hw : LinearIndependent k w := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    have hsum : (∑ j ∈ s, ((iterateFrobeniusEquiv k p b).symm (c j)) • (bas j : F)) ^ p ^ b
        = 0 := by
      rw [sum_pow_char_pow]
      have := congrArg Subtype.val hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, w, ZeroMemClass.coe_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [smul_pow, ← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
    have h0 := pow_eq_zero_iff (n := p ^ b) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp hsum
    have hli := bas.linearIndependent
    rw [linearIndependent_iff'] at hli
    have := hli s (fun j ↦ (iterateFrobeniusEquiv k p b).symm (c j))
      (Subtype.ext (by simpa using h0)) i hi
    simpa using this
  have := hw.fintype_card_le_finrank
  rwa [Fintype.card_fin] at this

variable [PerfectField k] [IsFunctionField k F]

/-- `L(l α)^{p^e} ⊆ L(l p^e α)`. -/
theorem powSub_le (α : Place k F) (l : ℤ) :
    powSub p b (L (Finsupp.single α l)) ≤ L (Finsupp.single α (l * (p ^ b : ℕ))) := by
  classical
  rintro _ ⟨g, hg, rfl⟩
  rcases mem_L.mp hg with rfl | hg
  · rw [zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]; exact zero_mem _
  refine mem_L.mpr (Or.inr fun β ↦ ?_)
  rw [Place.ord_pow]
  have := hg β
  have hp : (0 : ℤ) ≤ (p ^ b : ℕ) := by positivity
  by_cases hβ : β = α
  · subst hβ
    simp only [Finsupp.single_eq_same] at this ⊢
    nlinarith
  · have h1 : (Finsupp.single α l) β = 0 := by
      rw [Finsupp.single_apply, if_neg (Ne.symm hβ)]
    have h2 : (Finsupp.single α (l * ((p ^ b : ℕ) : ℤ))) β = 0 := by
      rw [Finsupp.single_apply, if_neg (Ne.symm hβ)]
    rw [h1, neg_zero] at this
    rw [h2, neg_zero]
    exact mul_nonneg hp this

omit [Finite k] [CharP k p] in
/-- **Lemma 3.7** (Nivedita): if `l p^e < Q`, the elements `h_j` (`j ∈ J`) have pairwise
distinct pole orders `j` at `α`, and the `g_j ∈ L(l α)` are not all zero, then
`∑_j g_j^{p^e} h_j^Q ≠ 0`. -/
theorem sum_pow_mul_pow_ne_zero (α : Place k F) {l Q : ℕ} (hlQ : l * p ^ b < Q)
    (J : Finset ℕ) (h g : ℕ → F) (hh : ∀ j ∈ J, h j ≠ 0 ∧ α.ord (h j) = -(j : ℤ))
    (hg : ∀ j ∈ J, g j ∈ L (Finsupp.single α (l : ℤ))) (hne : ∃ j ∈ J, g j ≠ 0) :
    ∑ j ∈ J, g j ^ p ^ b * h j ^ Q ≠ 0 := by
  classical
  intro hsum
  set J' := J.filter fun j ↦ g j ≠ 0
  have hJ' : J'.Nonempty := by
    obtain ⟨j, hj, hj0⟩ := hne; exact ⟨j, Finset.mem_filter.mpr ⟨hj, hj0⟩⟩
  set j₀ := J'.max' hJ'
  have hj₀ := Finset.mem_filter.mp (J'.max'_mem hJ')
  have hpb : 0 < p ^ b := pow_pos (Fact.out : p.Prime).pos _
  have hg₀ : g j₀ ≠ 0 := hj₀.2
  have hh₀ := hh j₀ hj₀.1
  -- the order of the leading term
  have hord₀ : α.ord (g j₀ ^ p ^ b * h j₀ ^ Q) = (p ^ b : ℕ) * α.ord (g j₀) - Q * j₀ := by
    rw [α.ord_mul (pow_ne_zero _ hg₀) (pow_ne_zero _ hh₀.1), Place.ord_pow, Place.ord_pow, hh₀.2]
    push_cast; ring
  -- the other terms have order `≥ -l p^e - Q (j₀ - 1)`
  have hrest := α.ord_sum_ge (J.erase j₀) (fun j ↦ g j ^ p ^ b * h j ^ Q)
    (-(l : ℤ) * (p ^ b : ℕ) - Q * ((j₀ : ℤ) - 1)) (by
      intro j hj
      by_cases hgj : g j = 0
      · left; rw [hgj, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), zero_mul]
      right
      have hjJ := (Finset.mem_erase.mp hj).2
      have hjJ' : j ∈ J' := Finset.mem_filter.mpr ⟨hjJ, hgj⟩
      have hjlt : j < j₀ := lt_of_le_of_ne (J'.le_max' j hjJ') (Finset.mem_erase.mp hj).1
      have hhj := hh j hjJ
      rw [α.ord_mul (pow_ne_zero _ hgj) (pow_ne_zero _ hhj.1), Place.ord_pow, Place.ord_pow,
        hhj.2]
      have hga : -(l : ℤ) ≤ α.ord (g j) := by
        have := (mem_L.mp (hg j hjJ)).resolve_left hgj α
        simpa using this
      push_cast
      have : (j : ℤ) ≤ j₀ - 1 := by omega
      nlinarith)
  rw [← Finset.add_sum_erase J _ hj₀.1] at hsum
  have heq : ∑ j ∈ J.erase j₀, g j ^ p ^ b * h j ^ Q = -(g j₀ ^ p ^ b * h j₀ ^ Q) :=
    eq_neg_of_add_eq_zero_right hsum
  rw [heq] at hrest
  have hne0 : -(g j₀ ^ p ^ b * h j₀ ^ Q) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hg₀) (pow_ne_zero _ hh₀.1))
  have hlow := hrest.resolve_left hne0
  rw [Place.ord_neg, hord₀] at hlow
  -- hence `ord_α g_{j₀} > 0`, impossible for a nonzero element of `L(l α)` with no other poles
  have hpos : 0 < α.ord (g j₀) := by
    have hQj : (Q : ℤ) * ((j₀ : ℤ) - 1) = Q * j₀ - Q := by ring
    have h1 : ((p ^ b : ℕ) : ℤ) * α.ord (g j₀) ≥ (Q : ℤ) - l * (p ^ b : ℕ) := by
      rw [hQj] at hlow; linarith
    have h2 : (l : ℤ) * ((p ^ b : ℕ) : ℤ) < Q := by exact_mod_cast hlQ
    have h3 : (0 : ℤ) < (p ^ b : ℕ) := by exact_mod_cast hpb
    by_contra hc
    push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos h3.le hc
    linarith
  have hmem : g j₀ ∈ L (-(Finsupp.single α (1 : ℤ))) := by
    refine (mem_L_of_ne_zero hg₀).mpr fun β ↦ ?_
    have := (mem_L.mp (hg j₀ hj₀.1)).resolve_left hg₀ β
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_neg, Pi.neg_apply, Finsupp.coe_zero,
      Pi.zero_apply, Finsupp.single_apply, div_apply] at this ⊢
    split_ifs at this ⊢ with hβ
    · subst hβ; omega
    · simpa using this
  have hbot := L_eq_bot_of_deg_neg (A := -(Finsupp.single α (1 : ℤ))) (by
    rw [deg_neg, deg_single, one_mul]
    have := α.deg_pos
    omega)
  rw [hbot, Submodule.mem_bot] at hmem
  exact hg₀ hmem

end WeilCurves.FunctionField
