/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Specialty
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Weil differentials

A *Weil differential* of `K / k` is a `k`-linear functional `ω` on the repartitions `A_K`
vanishing on `A_K(A) + K` for some divisor `A` (Stichtenoth, §1.5). For a divisor `A` the Weil
differentials vanishing on `A_K(A) + K` form the `k`-space `Ω(A)`, the dual of
`A_K / (A_K(A) + K)`; hence `dim_k Ω(A) = i(A)`. Repartitions are a `K`-vector space, so `K` acts on
functionals by `(x ω)(α) = ω(x α)`.

## Main definitions and results

* `WeilCurves.FunctionField.Rep k K`: the repartitions, as a type with its `k`-module structure.
* `WeilCurves.FunctionField.weilSub A`: the space `Ω(A)`; `finrank_weilSub : dim Ω(A) = i(A)`.
* `WeilCurves.FunctionField.smulW x ω`: the action of `K` on functionals;
  `smulW_mem_weilSub`: `ω ∈ Ω(A) → x ω ∈ Ω(A + div x)`.
* `WeilCurves.FunctionField.weilSub_inf_le`: `Ω(A) ∩ Ω(B) ⊆ Ω(A ⊔ B)`.
-/

namespace WeilCurves.FunctionField

open Divisor Module

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

variable (k K) in
/-- The repartitions of `K / k`, as a `k`-vector space. -/
abbrev Rep : Type _ := ↥((repartitions k K).restrictScalars k)

/-- `A_K(A) + K`, as a subspace of the repartitions. -/
noncomputable def repSub (A : Divisor k K) : Submodule k (Rep k K) :=
  (adeleSub A ⊔ diagK k K).comap ((repartitions k K).restrictScalars k).subtype

theorem repSub_mono {A B : Divisor k K} (h : A ≤ B) : repSub A ≤ repSub B :=
  Submodule.comap_mono (sup_le_sup_right (adeleSub_mono h) _)

instance finiteDimensional_quotient_repSub (A : Divisor k K) :
    FiniteDimensional k (Rep k K ⧸ repSub A) := by
  have h := relRank_repartitions A
  rw [relRank_eq_rank_quotient] at h
  exact Module.finite_of_rank_eq_nat h

theorem finrank_quotient_repSub (A : Divisor k K) :
    finrank k (Rep k K ⧸ repSub A) = iSpec A := by
  have h := relRank_repartitions A
  rw [iSpec, h, Cardinal.toNat_natCast]
  rw [relRank_eq_rank_quotient] at h
  exact Module.finrank_eq_of_rank_eq h

/-- The space `Ω(A)` of Weil differentials vanishing on `A_K(A) + K`. -/
noncomputable def weilSub (A : Divisor k K) : Submodule k (Dual k (Rep k K)) :=
  (repSub A).dualAnnihilator

theorem mem_weilSub {A : Divisor k K} {ω : Dual k (Rep k K)} :
    ω ∈ weilSub A ↔ ∀ α ∈ repSub A, ω α = 0 := Submodule.mem_dualAnnihilator ω

theorem weilSub_anti {A B : Divisor k K} (h : A ≤ B) : weilSub B ≤ weilSub A :=
  Submodule.dualAnnihilator_anti (repSub_mono h)

instance (A : Divisor k K) : FiniteDimensional k (weilSub A) :=
  (Submodule.dualQuotEquivDualAnnihilator (repSub A)).finiteDimensional

/-- **`dim_k Ω(A) = i(A)`**. -/
theorem finrank_weilSub (A : Divisor k K) : finrank k (weilSub A) = iSpec A := by
  rw [weilSub, ← (Submodule.dualQuotEquivDualAnnihilator (repSub A)).finrank_eq,
    Subspace.dual_finrank_eq, finrank_quotient_repSub]

/-! ### The action of `K` -/

/-- Multiplication by `x ∈ K` on the repartitions. -/
noncomputable def mulRep (x : K) : Rep k K →ₗ[k] Rep k K where
  toFun α := ⟨x • (α : Place k K → K), (repartitions k K).smul_mem x α.2⟩
  map_add' α β := by ext1; simp [smul_add]
  map_smul' c α := by ext1; simp [smul_comm x c]

@[simp]
theorem coe_mulRep (x : K) (α : Rep k K) : (mulRep x α : Place k K → K) = x • (α : _) := rfl

/-- The action `(x ω)(α) = ω(x α)` of `K` on functionals on the repartitions. -/
noncomputable def smulW (x : K) (ω : Dual k (Rep k K)) : Dual k (Rep k K) := ω ∘ₗ mulRep x

@[simp]
theorem smulW_apply (x : K) (ω : Dual k (Rep k K)) (α : Rep k K) :
    smulW x ω α = ω (mulRep x α) := rfl

theorem smulW_smulW (x y : K) (ω : Dual k (Rep k K)) : smulW x (smulW y ω) = smulW (y * x) ω := by
  ext α
  simp only [smulW_apply]
  congr 1
  ext1
  simp [mul_smul]

theorem smulW_one (ω : Dual k (Rep k K)) : smulW 1 ω = ω := by
  ext α
  simp only [smulW_apply]
  congr 1
  ext1
  simp

theorem smulW_add (x : K) (ω ω' : Dual k (Rep k K)) :
    smulW x (ω + ω') = smulW x ω + smulW x ω' := rfl

theorem add_smulW (x y : K) (ω : Dual k (Rep k K)) :
    smulW (x + y) ω = smulW x ω + smulW y ω := by
  ext α
  simp only [smulW_apply, LinearMap.add_apply, ← map_add]
  congr 1
  ext1
  simp [add_smul]

theorem smulW_zero_left (ω : Dual k (Rep k K)) : smulW 0 ω = 0 := by
  ext α
  simp only [smulW_apply, LinearMap.zero_apply]
  have : mulRep (0 : K) α = 0 := by ext1; simp
  rw [this, map_zero]

theorem smulW_zero (x : K) : smulW x (0 : Dual k (Rep k K)) = 0 := rfl

theorem smulW_smul (x : K) (c : k) (ω : Dual k (Rep k K)) : smulW x (c • ω) = c • smulW x ω :=
  rfl

theorem smulW_algebraMap (c : k) (ω : Dual k (Rep k K)) :
    smulW (algebraMap k K c) ω = c • ω := by
  ext α
  simp only [smulW_apply, LinearMap.smul_apply, ← map_smul]
  congr 1
  ext1
  simp [algebraMap_smul]

/-- `x · A_K(A) ⊆ A_K(A - div x)`. -/
theorem smul_mem_adeleSub {A : Divisor k K} {x : K} (hx : x ≠ 0) {α : Place k K → K}
    (hα : α ∈ adeleSub A) : x • α ∈ adeleSub (A - div k x) := by
  intro P
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases hα P with h | h
  · simp [h]
  by_cases h0 : α P = 0
  · simp [h0]
  refine Or.inr ?_
  rw [P.ord_mul hx h0]
  simp only [Finsupp.coe_sub, Pi.sub_apply, div_apply]
  omega

theorem mulRep_mem_repSub {A : Divisor k K} {x : K} (hx : x ≠ 0) {α : Rep k K}
    (hα : α ∈ repSub A) : mulRep x α ∈ repSub (A - div k x) := by
  change x • (α : Place k K → K) ∈ adeleSub (A - div k x) ⊔ diagK k K
  have hα' : (α : Place k K → K) ∈ adeleSub A ⊔ diagK k K := hα
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hα'
  rw [← hβγ, smul_add]
  refine Submodule.add_mem_sup (smul_mem_adeleSub hx hβ) ?_
  obtain ⟨f, rfl⟩ := hγ
  exact ⟨x * f, rfl⟩

/-- **`ω ∈ Ω(A) → x ω ∈ Ω(A + div x)`**. -/
theorem smulW_mem_weilSub {A : Divisor k K} {x : K} (hx : x ≠ 0) {ω : Dual k (Rep k K)}
    (hω : ω ∈ weilSub A) : smulW x ω ∈ weilSub (A + div k x) := by
  rw [mem_weilSub] at hω ⊢
  intro α hα
  have := mulRep_mem_repSub hx hα
  rw [add_sub_cancel_right] at this
  exact hω _ this

/-! ### `Ω(A) ∩ Ω(B) ⊆ Ω(A ⊔ B)` -/

theorem adeleSub_sup_le (A B : Divisor k K) : adeleSub (A ⊔ B) ≤ adeleSub A ⊔ adeleSub B := by
  classical
  intro α hα
  set α₁ : Place k K → K := fun P ↦ if B P ≤ A P then α P else 0
  have h₁ : α₁ ∈ adeleSub A := by
    intro P
    simp only [α₁]
    split_ifs with h
    · rcases hα P with h' | h'
      · exact Or.inl h'
      · right; rw [Finsupp.sup_apply, sup_eq_left.mpr h] at h'; exact h'
    · exact Or.inl rfl
  have h₂ : α - α₁ ∈ adeleSub B := by
    intro P
    simp only [α₁, Pi.sub_apply]
    split_ifs with h
    · exact Or.inl (sub_self _)
    · rw [sub_zero]
      rcases hα P with h' | h'
      · exact Or.inl h'
      · right; rw [Finsupp.sup_apply, sup_eq_right.mpr (le_of_lt (not_le.mp h))] at h'
        exact h'
  have : α = α₁ + (α - α₁) := by abel
  rw [this]
  exact Submodule.add_mem_sup h₁ h₂

theorem repSub_sup_le (A B : Divisor k K) : repSub (A ⊔ B) ≤ repSub A ⊔ repSub B := by
  intro α hα
  have hα' : (α : Place k K → K) ∈ adeleSub (A ⊔ B) ⊔ diagK k K := hα
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hα'
  obtain ⟨β₁, hβ₁, β₂, hβ₂, rfl⟩ := Submodule.mem_sup.mp (adeleSub_sup_le A B hβ)
  have hR : ∀ {δ}, δ ∈ adeleSub A ⊔ diagK k K → δ ∈ (repartitions k K).restrictScalars k :=
    fun h ↦ sup_le (adeleSub_le A) diagK_le h
  have hR' : ∀ {δ}, δ ∈ adeleSub B ⊔ diagK k K → δ ∈ (repartitions k K).restrictScalars k :=
    fun h ↦ sup_le (adeleSub_le B) diagK_le h
  have m₁ : β₁ + γ ∈ adeleSub A ⊔ diagK k K := Submodule.add_mem_sup hβ₁ hγ
  have m₂ : β₂ ∈ adeleSub B ⊔ diagK k K := Submodule.mem_sup_left hβ₂
  have : α = ⟨β₁ + γ, hR m₁⟩ + ⟨β₂, hR' m₂⟩ := by
    ext1
    simp only [Submodule.coe_add]
    rw [← hβγ]; abel
  rw [this]
  exact Submodule.add_mem_sup m₁ m₂

theorem weilSub_inf_le (A B : Divisor k K) : weilSub A ⊓ weilSub B ≤ weilSub (A ⊔ B) := by
  rw [weilSub, weilSub, weilSub, ← Submodule.dualAnnihilator_sup_eq]
  exact Submodule.dualAnnihilator_anti (repSub_sup_le A B)

/-- `Ω(A) = 0` when `deg A` is large. -/
theorem exists_weilSub_eq_bot : ∃ N : ℤ, ∀ A : Divisor k K, N ≤ A.deg → weilSub A = ⊥ := by
  obtain ⟨N, hN⟩ := riemann_equality (k := k) (K := K)
  refine ⟨N, fun A hA ↦ ?_⟩
  have h := iSpec_eq A
  rw [hN A hA] at h
  have h0 : iSpec A = 0 := by omega
  rw [← finrank_weilSub] at h0
  exact Submodule.finrank_eq_zero.mp h0

end WeilCurves.FunctionField
