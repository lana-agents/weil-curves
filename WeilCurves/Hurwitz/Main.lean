/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Hurwitz.Cotrace

/-!
# The Hurwitz genus formula

For a finite separable extension `L / K` of function fields over a perfect field `k`
(Stichtenoth, *Algebraic Function Fields and Codes*, Theorem 3.4.6 and the Hurwitz genus
formula Theorem 3.4.13; statement as quoted in Chen–Hu, arXiv:2603.23930, Thm. 2.1):

* `weilDiv_cotrace`: the divisor of the cotrace of a nonzero Weil differential `ω` of `K` is
  `Con_{L/K} (ω) + Diff(L/K)`;
* `canonical_linearEquiv`: `Con_{L/K} W_K + Diff(L/K)` is a canonical divisor of `L`;
* **`riemannHurwitz`**: `2 g_L - 2 = [L : K] (2 g_K - 2) + deg Diff(L/K)`.

Here `g = genus k ·` and all degrees are taken over the common base field `k`; when `k` is the
full constant field of `K` and of `L` these are the usual genera (no constant field correction
is needed in this normalisation).
-/

open Module

set_option linter.unusedSectionVars false

namespace WeilCurves.FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {L : Type*} [Field L] [Algebra K L]
  [Algebra k L] [IsScalarTower k K L] [PerfectField k] [IsFunctionField k K]
  [IsFunctionField k L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem cotrace_ne_zero {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) :
    cotrace K L ω ≠ 0 := by
  intro h
  obtain Q₀ : Place k L := Classical.arbitrary _
  apply cotrace_notMem_weilSub (L := L) hω h0 Q₀
  rw [h]
  exact zero_mem _

theorem isWeil_cotrace {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) :
    IsWeil (cotrace K L ω) :=
  ⟨_, cotrace_mem_weilSub hω h0⟩

/-- **`(Cotr ω) = Con_{L/K} (ω) + Diff(L/K)`** (Stichtenoth, Theorem 3.4.6). -/
theorem weilDiv_cotrace {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) :
    weilDiv (cotrace K L ω) = conormOf L (weilDiv ω) + different k K L := by
  classical
  have hW := isWeil_cotrace (L := L) hω h0
  have hne := cotrace_ne_zero (L := L) hω h0
  have hle := (mem_weilSub_iff hW hne).mp (cotrace_mem_weilSub hω h0)
  refine le_antisymm (fun Q ↦ ?_) hle
  by_contra hlt
  push Not at hlt
  apply cotrace_notMem_weilSub (L := L) hω h0 Q
  rw [mem_weilSub_iff hW hne]
  intro Q'
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h
    simp only [Finsupp.coe_add, Pi.add_apply] at hlt
    omega
  · have := hle Q'
    simp only [Finsupp.coe_add, Pi.add_apply] at this
    omega

/-- The divisor of any nonzero Weil differential of `L` has degree `2 g_L - 2`. -/
theorem deg_weilDiv {φ : Dual k (Rep k L)} (hφ : IsWeil φ) (h0 : φ ≠ 0) :
    (weilDiv φ).deg = 2 * genus k L - 2 := by
  obtain ⟨x, rfl⟩ := exists_smulW_eq (isWeil_omega0 (k := k) (K := L)) hφ omega0_ne_zero
  have hx : x ≠ 0 := by
    rintro rfl
    exact h0 (smulW_zero_left _)
  rw [weilDiv_smulW isWeil_omega0 omega0_ne_zero hx, Divisor.deg_add, Divisor.deg_div,
    add_zero]
  exact deg_canonical

/-- **`Con_{L/K} W_K + Diff(L/K)` is a canonical divisor of `L`**: it is the divisor of the
Weil differential `Cotr(ω₀)`, and `Con W_K + Diff = W_L + (x)` for some `x ∈ L^×`. -/
theorem canonical_linearEquiv :
    ∃ x : L, x ≠ 0 ∧
      conormOf L (canonical k K) + different k K L = canonical k L + Divisor.div k x := by
  have hω := isWeil_omega0 (k := k) (K := K)
  have h0 := omega0_ne_zero (k := k) (K := K)
  obtain ⟨x, hx⟩ := exists_smulW_eq (isWeil_omega0 (k := k) (K := L))
    (isWeil_cotrace (L := L) hω h0) omega0_ne_zero
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact cotrace_ne_zero (L := L) hω h0 (hx.trans (smulW_zero_left _))
  refine ⟨x, hx0, ?_⟩
  rw [canonical, ← weilDiv_cotrace hω h0, hx, weilDiv_smulW isWeil_omega0 omega0_ne_zero hx0]
  rfl

/-- **The Hurwitz genus formula** (Stichtenoth, Theorem 3.4.13):
`2 g_L - 2 = [L : K] (2 g_K - 2) + deg Diff(L/K)`. -/
theorem riemannHurwitz :
    2 * genus k L - 2 = finrank K L * (2 * genus k K - 2) + (different k K L).deg := by
  have hω := isWeil_omega0 (k := k) (K := K)
  have h0 := omega0_ne_zero (k := k) (K := K)
  have h := deg_weilDiv (isWeil_cotrace (L := L) hω h0) (cotrace_ne_zero hω h0)
  rw [weilDiv_cotrace hω h0, Divisor.deg_add, deg_conormOf] at h
  rw [← h, ← deg_canonical (k := k) (K := K)]
  rfl

end WeilCurves.FunctionField
