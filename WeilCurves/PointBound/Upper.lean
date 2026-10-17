/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Bombieri.Main
import WeilCurves.ConstantExtension.Genus
import WeilCurves.ConstantExtension.Split2

/-!
# The upper bound `N_r ≤ q^r + 1 + (2g + 1) q^{r/2}`

Kedlaya (*Weil cohomology* notes), Theorem 5.1.5, applied after the base change to `k_r`:
`N_r` is the number of places of degree one of `K_r = ConstExt k K r` over `k_r`
(`ncard_deg_one_kr`), `g(K_r) ≤ g(K)` (`genus_constExt_le`), and Bombieri's bound (`bombieri`,
with `τ = id`) applies to `K_r / k_r` when `q^r = p^{2b} > (g + 1)^4`: every rational place `β`
satisfies `x^{q^r} ≡ x (mod β)` on `O_β`, since its residue field is `k_r`.

## Main result

* `WeilCurves.FunctionField.pointCount_le`.
-/

namespace WeilCurves.FunctionField

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]

omit [Finite k] [IsFunctionField k K] in
theorem Place.map_refl {F : Type*} [Field F] [Algebra k F] (Q : Place k F) :
    Q.map (AlgEquiv.refl : F ≃ₐ[k] F) = Q := by
  apply Place.ext
  ext x
  rw [Place.mem_map]
  rfl

/-- For a place of degree one over a finite field `k`, `x^{|k|} ≡ x (mod β)` on `O_β`. -/
theorem Place.pow_card_sub_mem {F : Type*} [Field F] [Algebra k F] [IsFunctionField k F]
    (β : Place k F) (hβ : β.deg = 1) {x : F} (hx : x ∈ β.1) :
    x ^ Nat.card k - x = 0 ∨ 0 < β.ord (x ^ Nat.card k - x) := by
  by_cases h0 : x ^ Nat.card k - x = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have : Finite β.ResidueField := Module.finite_of_finite k
  have hcard : Nat.card β.ResidueField = Nat.card k := by
    rw [Module.natCard_eq_pow_finrank (K := k)]
    change Nat.card k ^ β.deg = _
    rw [hβ, pow_one]
  set a : β.1 := ⟨x, hx⟩
  have hres : β.residue (a ^ Nat.card k - a) = 0 := by
    rw [map_sub, map_pow, ← hcard]
    cases nonempty_fintype β.ResidueField
    rw [Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  have hmem := (β.residue_eq_zero_iff).mp hres
  have h0' : ((a ^ Nat.card k - a : β.1) : F) ≠ 0 := h0
  exact (β.ord_pos_iff_mem_maximalIdeal h0').mpr hmem

variable (p b : ℕ) [Fact p.Prime] [CharP k p]

/-- **Upper bound** (Kedlaya, Theorem 5.1.5): if `q^r = p^{2b}` and `(g + 1)^4 < p^{2b}`, then
`N_r ≤ q^r + 1 + (2g + 1) p^b`. -/
theorem pointCount_le (hk : IsFullConstantField k K) {r : ℕ} [NeZero r]
    (hq : Nat.card k ^ r = p ^ (2 * b)) (hg : (genus k K + 1) ^ 4 < (p : ℤ) ^ (2 * b)) :
    (pointCount k K r : ℤ) ≤ (p : ℤ) ^ (2 * b) + 1 + (2 * genus k K + 1) * p ^ b := by
  classical
  have : Fact (IsFullConstantField k K) := ⟨hk⟩
  set k' := BaseExt k r
  set K' := ConstExt k K r
  have hk' : IsFullConstantField k' K' := isFullConstantField_constExt r
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have hcard' : Nat.card k' = p ^ (2 * b) := by
    rw [Module.natCard_eq_pow_finrank (K := k), FiniteField.finrank_extension, hq]
  have hgle : genus k' K' ≤ genus k K := genus_constExt_le r
  have hg0 : 0 ≤ genus k' K' := genus_nonneg hk'
  have hg' : (genus k' K' + 1) ^ 4 < (p : ℤ) ^ (2 * b) :=
    lt_of_le_of_lt (pow_le_pow_left₀ (by linarith) (by linarith) 4) hg
  have hfin : {Q : Place k' K' | Q.deg = 1}.Finite :=
    (finite_setOf_deg_le (k := k') (K := K') 1).subset fun Q hQ ↦ le_of_eq hQ
  rw [← ncard_deg_one_kr (k := k) (K := K) r, Set.ncard_eq_toFinset_card _ hfin]
  set T := hfin.toFinset
  have hpb : (0 : ℤ) ≤ (2 * genus k K + 1) * p ^ b := by
    have : (0 : ℤ) ≤ genus k K := by linarith
    positivity
  rcases T.eq_empty_or_nonempty with hT | ⟨α, hα⟩
  · rw [hT, Finset.card_empty]
    push_cast
    have : (0 : ℤ) ≤ (p : ℤ) ^ (2 * b) := by positivity
    linarith
  have hαdeg : α.deg = 1 := hfin.mem_toFinset.mp hα
  have hb := bombieri (k := k') (F := K') p b hk' hg' α hαdeg AlgEquiv.refl (T.erase α)
    (fun β hβ ↦ by
      rw [Place.map_refl]
      exact ⟨Finset.ne_of_mem_erase hβ, Finset.ne_of_mem_erase hβ⟩)
    (fun β hβ x hx _ ↦ by
      have hβdeg : β.deg = 1 := hfin.mem_toFinset.mp (Finset.mem_of_mem_erase hβ)
      have := Place.pow_card_sub_mem β hβdeg hx
      rwa [hcard'] at this)
  have hsum : ∑ β ∈ T.erase α, (β.deg : ℤ) = ((T.erase α).card : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun β hβ ↦ ?_
    rw [hfin.mem_toFinset.mp (Finset.mem_of_mem_erase hβ)]
  rw [hsum, Finset.card_erase_of_mem hα] at hb
  have h1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨α, hα⟩
  have : ((T.card - 1 : ℕ) : ℤ) = (T.card : ℤ) - 1 := by push_cast [Nat.cast_sub h1]; ring
  rw [this] at hb
  have : (2 * genus k' K' + 1) * (p : ℤ) ^ b ≤ (2 * genus k K + 1) * p ^ b :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

end WeilCurves.FunctionField
