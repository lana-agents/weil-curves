/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Riemann
import WeilCurves.LinearAlgebra.RelRank

/-!
# Repartitions (adeles) of a function field

We follow H. Stichtenoth, *Algebraic Function Fields and Codes*, §1.5. A *repartition* of `K / k`
is a family `α = (α_P)_P ∈ ∏_P K` with `α_P ∈ O_P` for almost all places `P`; they form a
`K`-subspace `WeilCurves.FunctionField.repartitions k K` of `Place k K → K`, containing `K`
diagonally. For a divisor `A`,
`A_K(A) = {α | ord_P α_P ≥ -A(P) for all P}` (`WeilCurves.FunctionField.adeleSub A`).

## Main results

* `WeilCurves.FunctionField.adeleSub_inf_diag`: `A_K(A) ∩ K = L(A)`.
* `WeilCurves.FunctionField.relRank_adeleSub_add_single`: `dim_k A_K(A + P) / A_K(A) = deg P`,
  and `WeilCurves.FunctionField.relRank_adeleSub_of_le`: `dim_k A_K(B) / A_K(A) = deg B - deg A`
  for `A ≤ B`.
-/

open IsLocalRing

namespace WeilCurves.FunctionField

open Divisor

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Repartitions -/

variable (k K) in
/-- The diagonal embedding `K → ∏_P K`. -/
noncomputable def diag : K →ₗ[k] (Place k K → K) where
  toFun f _ := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem diag_apply (f : K) (P : Place k K) : diag k K f P = f := rfl

variable [PerfectField k] [IsFunctionField k K]

theorem diag_injective : Function.Injective (diag k K) := fun _ _ h ↦
  congrFun h (Classical.arbitrary (Place k K))


variable (k K) in
/-- The repartitions (adeles) of `K / k`: the families `α` with `α_P ∈ O_P` for almost all
`P`. -/
noncomputable def repartitions : Submodule K (Place k K → K) where
  carrier := {α | {P : Place k K | α P ∉ P.1}.Finite}
  zero_mem' := by
    change Set.Finite _
    convert Set.finite_empty
    ext P
    simp
  add_mem' := by
    intro α β hα hβ
    refine (hα.union hβ).subset fun P hP ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.add_apply] at hP ⊢
    by_contra h
    push Not at h
    exact hP (P.1.add_mem _ _ h.1 h.2)
  smul_mem' := by
    intro c α hα
    refine ((Place.finite_setOf_notMem c).union hα).subset fun P hP ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.smul_apply, smul_eq_mul] at hP ⊢
    by_contra h
    push Not at h
    exact hP (P.1.mul_mem _ _ h.1 h.2)

theorem mem_repartitions {α : Place k K → K} :
    α ∈ repartitions k K ↔ {P : Place k K | α P ∉ P.1}.Finite := Iff.rfl

variable (k K) in
/-- The diagonal copy of `K` inside `∏_P K`, as a `k`-subspace. -/
noncomputable def diagK : Submodule k (Place k K → K) := LinearMap.range (diag k K)

theorem diagK_le : diagK k K ≤ (repartitions k K).restrictScalars k := by
  rintro _ ⟨f, rfl⟩
  exact (Place.finite_setOf_notMem f).subset fun P hP ↦ hP

/-- The `k`-subspace `A_K(A) = {α | ∀ P, α_P = 0 ∨ -A(P) ≤ ord_P α_P}`. -/
noncomputable def adeleSub (A : Divisor k K) : Submodule k (Place k K → K) where
  carrier := {α | ∀ P, α P = 0 ∨ -A P ≤ P.ord (α P)}
  zero_mem' := fun _ ↦ Or.inl rfl
  add_mem' := by
    intro α β hα hβ P
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hα hβ ⊢
    by_cases h : α P + β P = 0
    · exact Or.inl h
    refine Or.inr ?_
    rcases hα P with h1 | h1
    · rw [h1, zero_add] at h ⊢
      rcases hβ P with h2 | h2
      · exact absurd h2 h
      · exact h2
    rcases hβ P with h2 | h2
    · rw [h2, add_zero]; exact h1
    exact (le_min h1 h2).trans (P.min_le_ord_add h)
  smul_mem' := by
    intro c α hα P
    simp only [Set.mem_setOf_eq, Pi.smul_apply] at hα ⊢
    rw [Algebra.smul_def]
    by_cases hc : c = 0
    · simp [hc]
    rcases hα P with h | h
    · simp [h]
    by_cases h0 : α P = 0
    · simp [h0]
    refine Or.inr ?_
    rw [P.ord_mul ((map_ne_zero _).mpr hc) h0, Place.ord_algebraMap_base, zero_add]
    exact h

theorem mem_adeleSub {A : Divisor k K} {α : Place k K → K} :
    α ∈ adeleSub A ↔ ∀ P, α P = 0 ∨ -A P ≤ P.ord (α P) := Iff.rfl

theorem adeleSub_mono {A B : Divisor k K} (h : A ≤ B) : adeleSub A ≤ adeleSub B := by
  intro α hα P
  rcases hα P with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ((neg_le_neg (h P)).trans h1)

theorem adeleSub_le (A : Divisor k K) : adeleSub A ≤ (repartitions k K).restrictScalars k := by
  intro α hα
  refine A.support.finite_toSet.subset fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq] at hP
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  rcases hα P with h | h
  · exact absurd (h ▸ P.1.zero_mem) hP
  · have := (P.ord_neg_iff).mpr hP
    omega

/-- `A_K(A) ∩ K = L(A)`. -/
theorem diag_mem_adeleSub {A : Divisor k K} {f : K} : diag k K f ∈ adeleSub A ↔ f ∈ L A := by
  rw [mem_adeleSub, mem_L]
  simp only [diag_apply]
  by_cases hf : f = 0
  · simp [hf]
  simp [hf]

theorem adeleSub_inf_diagK (A : Divisor k K) :
    adeleSub A ⊓ diagK k K = (L A).map (diag k K) := by
  ext α
  constructor
  · rintro ⟨hα, f, rfl⟩
    exact ⟨f, diag_mem_adeleSub.mp hα, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨diag_mem_adeleSub.mpr hf, f, rfl⟩

/-! ### Adding a place -/

section Step

variable {A : Divisor k K} {P : Place k K} {π : K}

theorem zpow_mul_mem_of_adeleSub (hπ : P.ord π = 1) {α : Place k K → K}
    (hα : α ∈ adeleSub (A + Finsupp.single P 1)) : π ^ (A P + 1) * α P ∈ P.1 := by
  rcases hα P with h | h
  · simp [h]
  by_cases h0 : α P = 0
  · simp [h0]
  apply P.mem_of_ord_nonneg
  rw [P.ord_mul (zpow_ne_zero _ (ne_zero_of_ord_eq_one hπ)) h0, Place.ord_zpow, hπ]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at h
  omega

variable (A P) in
/-- The `k`-linear map `A_K(A + P) → κ(P)`, `α ↦ (π^{A(P)+1} α_P)(P)`. -/
noncomputable def adeleResidueMap (hπ : P.ord π = 1) :
    adeleSub (A + Finsupp.single P 1) →ₗ[k] P.ResidueField where
  toFun α := P.residue ⟨π ^ (A P + 1) * (α : Place k K → K) P, zpow_mul_mem_of_adeleSub hπ α.2⟩
  map_add' f g := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp [mul_add]
  map_smul' q f := by
    rw [RingHom.id_apply, Algebra.smul_def q (P.residue _), Place.algebraMap_residueField,
      ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, Pi.smul_apply, Algebra.smul_def, MulMemClass.coe_mul,
      Place.coe_baseHom]
    ring

theorem mem_ker_adeleResidueMap (hπ : P.ord π = 1) (α : adeleSub (A + Finsupp.single P 1)) :
    α ∈ LinearMap.ker (adeleResidueMap A P hπ) ↔ (α : Place k K → K) ∈ adeleSub A := by
  classical
  have hπ0 := ne_zero_of_ord_eq_one hπ
  have hα := α.2
  rw [LinearMap.mem_ker]
  change P.residue _ = 0 ↔ _
  rw [P.residue_eq_zero_iff]
  set a := (α : Place k K → K) P with ha
  have hrest : ∀ Q, Q ≠ P → ((α : Place k K → K) Q = 0 ∨
      -A Q ≤ Q.ord ((α : Place k K → K) Q)) := by
    intro Q hQ
    have := hα Q
    simpa [Finsupp.single_apply, Ne.symm hQ] using this
  by_cases ha0 : a = 0
  · have h0 : (⟨π ^ (A P + 1) * a, zpow_mul_mem_of_adeleSub hπ α.2⟩ : P.1) = 0 := by
      apply Subtype.ext; simp [ha0]
    rw [h0]
    refine ⟨fun _ Q ↦ ?_, fun _ ↦ Ideal.zero_mem _⟩
    by_cases hQ : Q = P
    · subst hQ; exact Or.inl ha0
    · exact hrest Q hQ
  have hne : π ^ (A P + 1) * a ≠ 0 := mul_ne_zero (zpow_ne_zero _ hπ0) ha0
  rw [← P.ord_pos_iff_mem_maximalIdeal (a := ⟨_, zpow_mul_mem_of_adeleSub hπ α.2⟩) hne]
  change 0 < P.ord (π ^ (A P + 1) * a) ↔ _
  rw [P.ord_mul (zpow_ne_zero _ hπ0) ha0, Place.ord_zpow, hπ]
  constructor
  · intro h Q
    by_cases hQ : Q = P
    · subst hQ; exact Or.inr (by rw [← ha]; omega)
    · exact hrest Q hQ
  · intro h
    rcases h P with h | h
    · exact absurd h ha0
    · rw [← ha] at h; omega

theorem adeleResidueMap_surjective (hπ : P.ord π = 1) :
    Function.Surjective (adeleResidueMap A P hπ) := by
  classical
  have hπ0 := ne_zero_of_ord_eq_one hπ
  intro r
  obtain ⟨a, rfl⟩ := P.residue_surjective r
  set y : K := π ^ (-(A P + 1)) * (a : K)
  have hy : Pi.single P y ∈ adeleSub (A + Finsupp.single P 1) := by
    intro Q
    by_cases hQ : Q = P
    · rw [hQ, Pi.single_eq_same]
      by_cases ha0 : (a : K) = 0
      · left; simp [y, ha0]
      right
      rw [P.ord_mul (zpow_ne_zero _ hπ0) ha0, Place.ord_zpow, hπ]
      have := P.ord_nonneg_of_mem a.2
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      omega
    · left; exact Pi.single_eq_of_ne hQ _
  refine ⟨⟨_, hy⟩, ?_⟩
  change P.residue _ = P.residue a
  congr 1
  apply Subtype.ext
  change π ^ (A P + 1) * (Pi.single P y : Place k K → K) P = a
  rw [Pi.single_eq_same, ← mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, one_mul]

/-- **`dim_k A_K(A + P) / A_K(A) = deg P`**. -/
theorem relRank_adeleSub_add_single (A : Divisor k K) (P : Place k K) :
    relRank (adeleSub A) (adeleSub (A + Finsupp.single P 1)) = P.deg := by
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  rw [relRank_eq_rank_quotient]
  have hker : LinearMap.ker (adeleResidueMap A P hπ) =
      (adeleSub A).comap (adeleSub (A + Finsupp.single P 1)).subtype := by
    ext α
    exact mem_ker_adeleResidueMap hπ α
  rw [← hker, (LinearMap.quotKerEquivRange _).rank_eq,
    LinearMap.range_eq_top.mpr (adeleResidueMap_surjective hπ), rank_top,
    ← Module.finrank_eq_rank]
  rfl

end Step

/-! ### Dimension of `A_K(B) / A_K(A)` -/

theorem relRank_adeleSub_add_single_nat (A : Divisor k K) (P : Place k K) (m : ℕ) :
    relRank (adeleSub A) (adeleSub (A + Finsupp.single P (m : ℤ))) = ((m * P.deg : ℕ) :
      Cardinal) := by
  induction m with
  | zero => simp [relRank_self]
  | succ m ih =>
    have h1 : A + Finsupp.single P ((m + 1 : ℕ) : ℤ) =
        (A + Finsupp.single P (m : ℤ)) + Finsupp.single P 1 := by
      rw [add_assoc, ← Finsupp.single_add]; push_cast; rfl
    have hle1 : adeleSub A ≤ adeleSub (A + Finsupp.single P (m : ℤ)) :=
      adeleSub_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.mpr (by positivity)))
    have hle2 : adeleSub (A + Finsupp.single P (m : ℤ)) ≤
        adeleSub ((A + Finsupp.single P (m : ℤ)) + Finsupp.single P 1) :=
      adeleSub_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.mpr zero_le_one))
    rw [h1, relRank_trans hle1 hle2, ih, relRank_adeleSub_add_single]
    push_cast
    ring

/-- **`dim_k A_K(A + D) / A_K(A) = deg D`** for `D ≥ 0`. -/
theorem relRank_adeleSub_add (A D : Divisor k K) (hD : 0 ≤ D) :
    relRank (adeleSub A) (adeleSub (A + D)) = (D.deg.toNat : Cardinal) := by
  classical
  induction D using Finsupp.induction generalizing A with
  | zero => simp [relRank_self]
  | single_add P b f hPf _ ih =>
    have hfP : f P = 0 := Finsupp.notMem_support_iff.mp hPf
    have hb : 0 ≤ b := by
      have := hD P
      simpa [hfP] using this
    have hf : 0 ≤ f := by
      intro Q
      by_cases hQ : Q = P
      · subst hQ; simp [hfP]
      · have := hD Q
        simpa [Finsupp.single_apply, Ne.symm hQ] using this
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    have hle1 : adeleSub A ≤ adeleSub (A + Finsupp.single P (m : ℤ)) :=
      adeleSub_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.mpr (by positivity)))
    have hle2 : adeleSub (A + Finsupp.single P (m : ℤ)) ≤
        adeleSub (A + Finsupp.single P (m : ℤ) + f) :=
      adeleSub_mono (le_add_of_nonneg_right hf)
    rw [← add_assoc, relRank_trans hle1 hle2, relRank_adeleSub_add_single_nat, ih _ hf,
      deg_add, deg_single]
    have hfd := deg_nonneg hf
    have : ((m : ℤ) * P.deg + Divisor.deg f).toNat = m * P.deg + (Divisor.deg f).toNat := by omega
    rw [this]
    push_cast
    rfl

/-- `dim_k (L(B) / L(A)) = ℓ(B) - ℓ(A)`, inside the repartitions. -/
theorem relRank_map_L {A B : Divisor k K} (h : A ≤ B) :
    relRank ((L A).map (diag k K)) ((L B).map (diag k K)) = ((ell B - ell A : ℕ) : Cardinal) := by
  have hle : (L A).map (diag k K) ≤ (L B).map (diag k K) := Submodule.map_mono (L_mono h)
  have htr := relRank_trans (bot_le : ⊥ ≤ (L A).map (diag k K)) hle
  have hrk : ∀ C : Divisor k K, relRank ⊥ ((L C).map (diag k K)) = (ell C : Cardinal) := by
    intro C
    rw [relRank_bot, ← (Submodule.equivMapOfInjective _ diag_injective (L C)).rank_eq,
      ell, Module.finrank_eq_rank]
  rw [hrk, hrk] at htr
  have hfin : relRank ((L A).map (diag k K)) ((L B).map (diag k K)) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt ?_ (Cardinal.natCast_lt_aleph0 (n := ell B))
    rw [htr]; exact le_add_self
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at htr ⊢
  have : ell B = ell A + n := by exact_mod_cast htr
  congr 1
  omega

/-- **`dim_k (A_K(B) + K) / (A_K(A) + K) = (deg B - ℓ(B)) - (deg A - ℓ(A))`** for `A ≤ B`
(Stichtenoth, §1.5). -/
theorem relRank_adeleSub_sup_diagK {A B : Divisor k K} (h : A ≤ B) :
    relRank (adeleSub A ⊔ diagK k K) (adeleSub B ⊔ diagK k K) =
      (((B.deg - ell B) - (A.deg - ell A)).toNat : Cardinal) := by
  have h1 := relRank_eq_sup_add_inf (diagK k K) (adeleSub_mono h)
  rw [adeleSub_inf_diagK, adeleSub_inf_diagK, relRank_map_L h] at h1
  have hBA : B = A + (B - A) := by abel
  have hD : 0 ≤ B - A := sub_nonneg.mpr h
  rw [hBA, relRank_adeleSub_add A (B - A) hD, ← hBA] at h1
  have hfin : relRank (adeleSub A ⊔ diagK k K) (adeleSub B ⊔ diagK k K) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt ?_ (Cardinal.natCast_lt_aleph0 (n := (B - A).deg.toNat))
    rw [h1]; exact self_le_add_right _ _
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at h1 ⊢
  have h2 : (B - A).deg.toNat = n + (ell B - ell A) := by exact_mod_cast h1
  have h3 := ell_mono h
  have h4 := deg_sub_ell_mono h
  rw [deg_sub] at h2
  congr 1
  omega

end WeilCurves.FunctionField
