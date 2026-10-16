/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.WeilDifferential

/-!
# The Riemann–Roch theorem

Following H. Stichtenoth, *Algebraic Function Fields and Codes*, §1.5:

* the Weil differentials form a one-dimensional `K`-vector space
  (`WeilCurves.FunctionField.exists_smulW_eq`): if `ω₁ ≠ 0`, every Weil differential is `x ω₁`.
  Otherwise `(x, y) ↦ x ω₁ + y ω₂` would embed `L(A₁ + B) × L(A₂ + B)` into `Ω(-B)`, which has
  dimension `deg B + riemannConst` only, while the source has dimension
  `≥ 2 deg B + O(1)` by Riemann's inequality;
* a nonzero Weil differential `ω` has a *divisor* `(ω)`, the largest `A` with `ω ∈ Ω(A)`
  (`WeilCurves.FunctionField.weilDiv`), and `(x ω) = (x) + (ω)`;
* for a canonical divisor `W = (ω₀)`, multiplication by `ω₀` is an isomorphism
  `L(W - A) ≃ Ω(A)`, so `i(A) = ℓ(W - A)`;
* **Riemann–Roch**: `ℓ(A) - ℓ(W - A) = deg A + 1 - g`, with the genus
  `g = riemannConst k K + 1`; and `deg W = 2g - 2`, `ℓ(W) = ℓ(0) + g - 1`.

(If `k` is not the full constant field `k'` of `K`, then `ℓ(0) = [k' : k]` and `g` here is
`[k' : k]` times the usual genus minus `[k' : k] - 1`; for `k = k'` it is the usual genus.)
-/

namespace WeilCurves.FunctionField

open Divisor Module

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

/-- `ω` is a Weil differential: it vanishes on `A_K(A) + K` for some divisor `A`. -/
def IsWeil (ω : Dual k (Rep k K)) : Prop := ∃ A : Divisor k K, ω ∈ weilSub A

theorem smulW_neg (x : K) (ω : Dual k (Rep k K)) : smulW (-x) ω = -smulW x ω := by
  have h := add_smulW x (-x) ω
  rw [add_neg_cancel, smulW_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem smulW_inv_smulW {x : K} (hx : x ≠ 0) (ω : Dual k (Rep k K)) :
    smulW x⁻¹ (smulW x ω) = ω := by
  rw [smulW_smulW, mul_inv_cancel₀ hx, smulW_one]

theorem smulW_ne_zero {x : K} (hx : x ≠ 0) {ω : Dual k (Rep k K)} (hω : ω ≠ 0) :
    smulW x ω ≠ 0 := by
  intro h
  apply hω
  rw [← smulW_inv_smulW hx ω, h, smulW_zero]

theorem mem_L_add_iff_le {A B : Divisor k K} {x : K} (hx : x ≠ 0) :
    x ∈ L (A + B) ↔ -B ≤ A + div k x := by
  rw [mem_L, or_iff_right hx]
  constructor
  · intro h P
    have := h P
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_neg, Pi.neg_apply, div_apply] at this ⊢
    omega
  · intro h P
    have := h P
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_neg, Pi.neg_apply, div_apply] at this ⊢
    omega

/-- `x ↦ x ω` as a `k`-linear map `L(A + B) → Ω(-B)`, for `ω ∈ Ω(A)`. -/
noncomputable def smulWLin {A : Divisor k K} (ω : Dual k (Rep k K)) (hω : ω ∈ weilSub A)
    (B : Divisor k K) : L (A + B) →ₗ[k] weilSub (-B) where
  toFun x := ⟨smulW x ω, by
    by_cases hx : (x : K) = 0
    · rw [hx, smulW_zero_left]; exact zero_mem _
    exact weilSub_anti ((mem_L_add_iff_le hx).mp x.2) (smulW_mem_weilSub hx hω)⟩
  map_add' x y := by ext1; exact add_smulW _ _ _
  map_smul' c x := by
    ext1
    change smulW (c • (x : K)) ω = c • smulW (x : K) ω
    rw [Algebra.smul_def, ← smulW_smulW, smulW_algebraMap, smulW_smul]

@[simp]
theorem coe_smulWLin {A : Divisor k K} (ω : Dual k (Rep k K)) (hω : ω ∈ weilSub A)
    (B : Divisor k K) (x : L (A + B)) :
    (smulWLin ω hω B x : Dual k (Rep k K)) = smulW (x : K) ω :=
  rfl

/-- **The Weil differentials form a one-dimensional `K`-space** (Stichtenoth, §1.5). -/
theorem exists_smulW_eq {ω₁ ω₂ : Dual k (Rep k K)} (h₁ : IsWeil ω₁) (h₂ : IsWeil ω₂)
    (hω₁ : ω₁ ≠ 0) : ∃ x : K, ω₂ = smulW x ω₁ := by
  by_contra hne
  push Not at hne
  obtain ⟨A₁, hA₁⟩ := h₁
  obtain ⟨A₂, hA₂⟩ := h₂
  obtain P0 : Place k K := Classical.arbitrary _
  set c := riemannConst k K
  set m : ℤ := (3 * c - A₁.deg - A₂.deg).toNat + 1
  set B : Divisor k K := Finsupp.single P0 m
  have hm : 1 ≤ m := by simp [m]
  have hP0 : (1 : ℤ) ≤ P0.deg := by exact_mod_cast P0.deg_pos
  have hdegB : B.deg = m * P0.deg := deg_single P0 m
  have hBm : m ≤ B.deg := by rw [hdegB]; nlinarith
  set Φ := (smulWLin ω₁ hA₁ B).coprod (smulWLin ω₂ hA₂ B)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hxy
    have h : smulW (x : K) ω₁ + smulW (y : K) ω₂ = 0 := by
      have := congrArg Subtype.val hxy
      simpa [Φ] using this
    by_cases hy : (y : K) = 0
    · rw [hy, smulW_zero_left, add_zero] at h
      by_cases hx : (x : K) = 0
      · exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
      · exact absurd h (smulW_ne_zero hx hω₁)
    · refine (hne (-((y : K)⁻¹ * x)) ?_).elim
      have h' := congrArg (smulW (y : K)⁻¹) h
      rw [smulW_add, smulW_inv_smulW hy, smulW_zero, smulW_smulW] at h'
      rw [smulW_neg, mul_comm]
      exact eq_neg_of_add_eq_zero_right h'
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, finrank_weilSub] at hle
  have hi := iSpec_eq (-B)
  have hneg : ell (-B) = 0 := ell_eq_zero_of_deg_neg (by rw [deg_neg]; omega)
  rw [hneg, deg_neg] at hi
  have r1 := riemann_inequality (A₁ + B)
  have r2 := riemann_inequality (A₂ + B)
  rw [deg_add] at r1 r2
  have hm' : 3 * c - A₁.deg - A₂.deg < m := by
    have := Int.self_le_toNat (3 * c - A₁.deg - A₂.deg); omega
  have : ((ell (A₁ + B) + ell (A₂ + B) : ℕ) : ℤ) ≤ iSpec (-B) := by exact_mod_cast hle
  push_cast at this
  omega

/-! ### The divisor of a Weil differential -/

theorem exists_weilDiv {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) :
    ∃ W : Divisor k K, ω ∈ weilSub W ∧ ∀ A : Divisor k K, ω ∈ weilSub A → A ≤ W := by
  obtain ⟨N, hN⟩ := exists_weilSub_eq_bot (k := k) (K := K)
  set S : Set ℤ := Divisor.deg '' {A : Divisor k K | ω ∈ weilSub A}
  have hbdd : BddAbove S := by
    refine ⟨N, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    by_contra h
    have := hN A (by push Not at h; omega)
    rw [Set.mem_setOf_eq, this, Submodule.mem_bot] at hA
    exact h0 hA
  obtain ⟨A0, hA0⟩ := hω
  obtain ⟨W, hW, hWdeg⟩ := Int.csSup_mem (⟨A0.deg, ⟨A0, hA0, rfl⟩⟩ : S.Nonempty) hbdd
  refine ⟨W, hW, fun A hA ↦ ?_⟩
  have hsup : ω ∈ weilSub (W ⊔ A) := weilSub_inf_le W A ⟨hW, hA⟩
  have hdeg : (W ⊔ A).deg ≤ W.deg := by
    rw [hWdeg]; exact le_csSup hbdd ⟨_, hsup, rfl⟩
  have hnn : 0 ≤ W ⊔ A - W := sub_nonneg.mpr le_sup_left
  by_contra hAW
  have hne : W ⊔ A - W ≠ 0 := by
    intro h
    apply hAW
    rw [sub_eq_zero] at h
    rw [← h]; exact le_sup_right
  have := deg_pos_of_nonneg_of_ne_zero hnn hne
  rw [deg_sub] at this
  omega

open Classical in
/-- The divisor `(ω)` of a Weil differential: the largest `A` with `ω ∈ Ω(A)` (junk value `0` for
`ω = 0` or `ω` not a Weil differential). -/
noncomputable def weilDiv (ω : Dual k (Rep k K)) : Divisor k K :=
  if h : IsWeil ω ∧ ω ≠ 0 then (exists_weilDiv h.1 h.2).choose else 0

theorem mem_weilSub_weilDiv {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) :
    ω ∈ weilSub (weilDiv ω) := by
  rw [weilDiv, dif_pos ⟨hω, h0⟩]
  exact (exists_weilDiv hω h0).choose_spec.1

/-- `ω ∈ Ω(A) ↔ A ≤ (ω)` for a nonzero Weil differential. -/
theorem mem_weilSub_iff {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) {A : Divisor k K} :
    ω ∈ weilSub A ↔ A ≤ weilDiv ω := by
  refine ⟨fun h ↦ ?_, fun h ↦ weilSub_anti h (mem_weilSub_weilDiv hω h0)⟩
  rw [weilDiv, dif_pos ⟨hω, h0⟩]
  exact (exists_weilDiv hω h0).choose_spec.2 A h

theorem IsWeil.smulW {ω : Dual k (Rep k K)} (hω : IsWeil ω) (x : K) : IsWeil (smulW x ω) := by
  obtain ⟨A, hA⟩ := hω
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, smulW_zero_left]; exact zero_mem _⟩
  exact ⟨_, smulW_mem_weilSub hx hA⟩

/-- **`(x ω) = (x) + (ω)`**. -/
theorem weilDiv_smulW {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) {x : K} (hx : x ≠ 0) :
    weilDiv (smulW x ω) = weilDiv ω + div k x := by
  have hxω := hω.smulW x
  have hx0 := smulW_ne_zero hx h0
  apply le_antisymm
  · have h := (mem_weilSub_iff hω h0).mp (by
      have := smulW_mem_weilSub (inv_ne_zero hx) (mem_weilSub_weilDiv hxω hx0)
      rwa [smulW_inv_smulW hx] at this)
    rw [div_inv] at h
    intro P
    have := h P
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_neg, Pi.neg_apply] at this ⊢
    omega
  · exact (mem_weilSub_iff hxω hx0).mp (smulW_mem_weilSub hx (mem_weilSub_weilDiv hω h0))

/-! ### Canonical divisors and the Riemann–Roch theorem -/

variable (k K) in
/-- There is a nonzero Weil differential. -/
theorem exists_isWeil_ne_zero : ∃ ω : Dual k (Rep k K), IsWeil ω ∧ ω ≠ 0 := by
  obtain P0 : Place k K := Classical.arbitrary _
  set A : Divisor k K := Finsupp.single P0 (-(|riemannConst k K| + 1))
  have hi := iSpec_eq A
  have hdeg : A.deg = -(|riemannConst k K| + 1) * P0.deg := deg_single _ _
  have hP0 : (1 : ℤ) ≤ P0.deg := by exact_mod_cast P0.deg_pos
  have hpos : 0 < iSpec A := by
    have := abs_nonneg (riemannConst k K)
    have := neg_abs_le (riemannConst k K)
    have : (0 : ℤ) < iSpec A := by rw [hi, hdeg]; nlinarith
    exact_mod_cast this
  rw [← finrank_weilSub] at hpos
  have hnb : weilSub A ≠ ⊥ := by
    intro hb; rw [hb, finrank_bot] at hpos; exact lt_irrefl _ hpos
  obtain ⟨ω, hω, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
  exact ⟨ω, ⟨A, hω⟩, hne⟩

variable (k K) in
/-- A fixed nonzero Weil differential. -/
noncomputable def omega0 : Dual k (Rep k K) := (exists_isWeil_ne_zero k K).choose

theorem isWeil_omega0 : IsWeil (omega0 k K) := (exists_isWeil_ne_zero k K).choose_spec.1

theorem omega0_ne_zero : omega0 k K ≠ 0 := (exists_isWeil_ne_zero k K).choose_spec.2

variable (k K) in
/-- A canonical divisor `W = (ω₀)`. -/
noncomputable def canonical : Divisor k K := weilDiv (omega0 k K)

/-- **`i(A) = ℓ(W - A)`** (Stichtenoth, §1.5). -/
theorem iSpec_eq_ell (A : Divisor k K) : iSpec A = ell (canonical k K - A) := by
  have hω := mem_weilSub_weilDiv (isWeil_omega0 (k := k) (K := K)) omega0_ne_zero
  set φ := smulWLin (omega0 k K) hω (-A)
  have hA : -(-A) = A := neg_neg A
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hx0' : (x : K) ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
    have := congrArg Subtype.val hx
    exact smulW_ne_zero hx0' omega0_ne_zero this
  have hsurj : Function.Surjective φ := by
    rintro ⟨ω, hω'⟩
    have hW : IsWeil ω := ⟨_, hω'⟩
    obtain ⟨x, rfl⟩ := exists_smulW_eq isWeil_omega0 hW omega0_ne_zero
    by_cases hx : x = 0
    · refine ⟨0, ?_⟩
      ext1; simp [φ, hx, smulW_zero_left]
    have hmem : x ∈ L (canonical k K + -A) := by
      rw [mem_L_add_iff_le hx, hA]
      have := (mem_weilSub_iff (isWeil_omega0.smulW x) (smulW_ne_zero hx omega0_ne_zero)).mp
        (by rw [hA] at hω'; exact hω')
      rw [weilDiv_smulW isWeil_omega0 omega0_ne_zero hx] at this
      exact this
    exact ⟨⟨x, hmem⟩, rfl⟩
  have e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have := e.finrank_eq
  rw [finrank_weilSub, hA] at this
  rw [ell, sub_eq_add_neg, ← this]
  rfl

variable (k K) in
/-- The genus `g = riemannConst k K + 1` (the usual genus when `k` is the full constant field). -/
noncomputable def genus : ℤ := riemannConst k K + 1

/-- **The Riemann–Roch theorem** (Stichtenoth, §1.5): `ℓ(A) - ℓ(W - A) = deg A + 1 - g`. -/
theorem riemannRoch (A : Divisor k K) :
    (ell A : ℤ) - ell (canonical k K - A) = A.deg + 1 - genus k K := by
  rw [← iSpec_eq_ell, ell_sub_iSpec, genus]
  ring

/-- **`deg W = 2g - 2`**. -/
theorem deg_canonical : (canonical k K).deg = 2 * genus k K - 2 := by
  have h1 := riemannRoch (0 : Divisor k K)
  have h2 := riemannRoch (canonical k K)
  rw [sub_zero] at h1
  rw [sub_self] at h2
  rw [deg_zero] at h1
  linarith

/-- `ℓ(W) = ℓ(0) + g - 1`. -/
theorem ell_canonical : (ell (canonical k K) : ℤ) = ell (0 : Divisor k K) + genus k K - 1 := by
  have h1 := riemannRoch (0 : Divisor k K)
  rw [sub_zero, deg_zero] at h1
  linarith

/-- For `deg A > 2g - 2`: `ℓ(A) = deg A + 1 - g`. -/
theorem ell_eq_of_deg_gt {A : Divisor k K} (hA : 2 * genus k K - 2 < A.deg) :
    (ell A : ℤ) = A.deg + 1 - genus k K := by
  have h := riemannRoch A
  have h0 : ell (canonical k K - A) = 0 :=
    ell_eq_zero_of_deg_neg (by rw [deg_sub, deg_canonical]; omega)
  rw [h0] at h
  simpa using h

end WeilCurves.FunctionField
