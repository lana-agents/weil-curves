/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Bombieri.Bound

/-!
# Bombieri's bound (twisted form)

Nivedita (*Riemann hypothesis for function fields*, CMI 2009), §3.2.2, Theorem 3.6 and
Proposition 3.8; Kedlaya (*Weil cohomology* notes), Theorem 5.1.5 and Lemma 5.1.7.

Let `F` be a function field over a finite field `k` of characteristic `p`, `k` the full
constant field, `g` its genus, `Q = p^{2b}` with `(g + 1)^4 < Q`, `α` a place of degree one and `τ`
a
`k`-automorphism of `F`. If `S` is a finite set of places `β ≠ α, τα` with
`x^Q ≡ τ x (mod β)` for all `x` with `x, τ x ∈ O_β`, then
`∑_{β ∈ S} deg β ≤ Q + (2g + 1) p^b` (`WeilCurves.FunctionField.bombieri`). (When `|k| = Q`
and `τ = id`, every rational place `β ≠ α` satisfies the hypothesis, so this is
`N_1 ≤ Q + 1 + (2g + 1) √Q`.)

The choice of parameters is Nivedita's: `e = b`, `m = p^b + 2g`, `l = ⌊g p^b/(g+1)⌋ + g + 1`.
-/

namespace WeilCurves.FunctionField

open Divisor

/-- The parameter inequalities: `l < p^b` and `g (p^b + g + 1) < l (g + 1)`. -/
theorem bombieri_params (G pe : ℕ) (h : (G + 1) ^ 2 < pe) :
    G * pe / (G + 1) + G + 1 < pe ∧
      (G : ℤ) * (pe + G + 1) < ((G * pe / (G + 1) + G + 1 : ℕ) : ℤ) * (G + 1) := by
  have h1 := Nat.div_mul_le_self (G * pe) (G + 1)
  have h2 := Nat.lt_mul_div_succ (G * pe) (Nat.succ_pos G)
  set d := G * pe / (G + 1)
  constructor
  · by_contra hc
    push Not at hc
    have : (G + 1) * pe ≤ (G + 1) * (d + G + 1) := Nat.mul_le_mul_left _ hc
    nlinarith
  · push_cast
    have h2' : ((G * pe : ℕ) : ℤ) < ((G + 1) * (d + 1) : ℕ) := by exact_mod_cast h2
    push_cast at h2'
    nlinarith

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F] [IsFunctionField k F]
  (p b : ℕ) [Fact p.Prime] [CharP k p]

set_option maxHeartbeats 4000000 in
-- The proof is one long declaration with many intermediate linear-algebra steps.
/-- **Bombieri's bound** (twisted form). -/
theorem bombieri (hk : IsFullConstantField k F)
    (hg : (genus k F + 1) ^ 4 < (p : ℤ) ^ (2 * b)) (α : Place k F) (hα : α.deg = 1)
    (τ : F ≃ₐ[k] F) (S : Finset (Place k F)) (hS : ∀ β ∈ S, β ≠ α ∧ β ≠ α.map τ)
    (hFrob : ∀ β ∈ S, ∀ x : F, x ∈ β.1 → τ x ∈ β.1 →
      x ^ p ^ (2 * b) - τ x = 0 ∨ 0 < β.ord (x ^ p ^ (2 * b) - τ x)) :
    ∑ β ∈ S, (β.deg : ℤ) ≤ (p : ℤ) ^ (2 * b) + (2 * genus k F + 1) * p ^ b := by
  classical
  have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  have hp := (Fact.out : p.Prime)
  -- numerical setup
  have hg0 := genus_nonneg hk
  set G := (genus k F).toNat with hG
  have hGg : (G : ℤ) = genus k F := Int.toNat_of_nonneg hg0
  set pe := p ^ b with hpe
  set Q := p ^ (2 * b) with hQdef
  have hQpe : Q = pe * pe := by rw [hQdef, hpe, ← pow_add, two_mul]
  have hpe0 : 0 < pe := pow_pos hp.pos _
  have hG2 : (G + 1) ^ 2 < pe := by
    have h1 : ((G + 1 : ℕ) : ℤ) ^ 4 < ((pe * pe : ℕ) : ℤ) := by
      rw [← hQpe, hQdef]; push_cast; rw [hGg]; exact hg
    have h1' : (G + 1) ^ 4 < pe * pe := by exact_mod_cast h1
    have h2 : ((G + 1) ^ 2) ^ 2 < pe ^ 2 := by
      rw [← pow_mul, sq]; exact h1'
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h2
  obtain ⟨hlpe, hlker⟩ := bombieri_params G pe hG2
  set l := G * pe / (G + 1) + G + 1
  set m := pe + 2 * G
  have hlpeQ : l * pe < Q := by rw [hQpe]; exact Nat.mul_lt_mul_of_pos_right hlpe hpe0
  have hrc : riemannConst k F = (G : ℤ) - 1 := by rw [hGg, genus]; ring
  -- the pole orders at `α`
  set J := poleOrders α m
  have hJ : (m : ℤ) + 1 - G ≤ J.card := by
    have h1 := ell_le_card_poleOrders α m hk hα
    have h2 := riemann_inequality (Finsupp.single α (m : ℤ))
    rw [deg_single, hα, hrc] at h2
    push_cast at h2
    have : (ell (Finsupp.single α (m : ℤ)) : ℤ) ≤ J.card := by exact_mod_cast h1
    linarith
  have hmemJ : ∀ j ∈ J, ∃ h ∈ L (Finsupp.single α (m : ℤ)), h ≠ 0 ∧ α.ord h = -(j : ℤ) :=
    fun j hj ↦ ((mem_poleOrders α m).mp hj).2
  choose! hh hhL hh0 hhord using hmemJ
  -- the space of `p^b`-th powers of `L(l α)`
  set V := L (Finsupp.single α (l : ℤ))
  set PV := powSub p b V
  have hPVle : PV ≤ L (Finsupp.single α ((l : ℤ) * (pe : ℕ))) := powSub_le p b α l
  have : FiniteDimensional k PV := Submodule.finiteDimensional_of_le hPVle
  have hPVdim : (l : ℤ) + 1 - G ≤ Module.finrank k PV := by
    have h1 := finrank_le_finrank_powSub p b V
    have h2 := riemann_inequality (Finsupp.single α (l : ℤ))
    rw [deg_single, hα, hrc] at h2
    push_cast at h2
    have : (ell (Finsupp.single α (l : ℤ)) : ℤ) ≤ Module.finrank k PV := by exact_mod_cast h1
    linarith
  -- the target space
  set Wd : Divisor k F := Finsupp.single α ((l * pe : ℕ) : ℤ) + Finsupp.single (α.map τ) (m : ℤ)
  have hdegW : Wd.deg = (l * pe : ℕ) + (m : ℤ) := by
    rw [deg_add, deg_single, deg_single, hα, Place.deg_map, hα]; push_cast; ring
  have hWdim : (ell Wd : ℤ) = (l * pe : ℕ) + (m : ℤ) + 1 - G := by
    rw [ell_eq_of_deg_gt (by rw [hdegW, ← hGg]; push_cast; nlinarith), hdegW, ← hGg]
  -- the linear map `Ψ(u) = ∑ u_j τ(h_j)`
  let Ψ : (J → PV) →ₗ[k] F := ∑ j : J,
    (LinearMap.mulRight k (τ (hh j))).comp (PV.subtype.comp (LinearMap.proj j))
  have hΨ : ∀ u, Ψ u = ∑ j : J, (u j : F) * τ (hh j) := by
    intro u; simp [Ψ]
  have hΨW : ∀ u, Ψ u ∈ L Wd := by
    intro u
    rw [hΨ]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have h1 : (u j : F) ∈ L (Finsupp.single α ((l * pe : ℕ) : ℤ)) := by
      have := hPVle (u j).2; push_cast; exact this
    have h2 : τ (hh j) ∈ L (Finsupp.single (α.map τ) (m : ℤ)) :=
      Place.apply_mem_L_single (hhL j j.2)
    exact mul_mem_L_add h1 h2
  let Ψ' : (J → PV) →ₗ[k] L Wd := Ψ.codRestrict (L Wd) hΨW
  have hlt : Module.finrank k (L Wd) < Module.finrank k (J → PV) := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, smul_eq_mul, Finset.card_univ,
      Fintype.card_coe]
    have hWd : (Module.finrank k (L Wd) : ℤ) = _ := hWdim
    have h0 : (0 : ℤ) ≤ (m : ℤ) + 1 - G := by simp only [m]; push_cast; omega
    have hlG : G + 1 ≤ l := by
      change G + 1 ≤ G * pe / (G + 1) + G + 1
      rw [add_assoc]; exact Nat.le_add_left _ _
    have h0' : (0 : ℤ) ≤ (l : ℤ) + 1 - G := by
      have : ((G + 1 : ℕ) : ℤ) ≤ l := by exact_mod_cast hlG
      push_cast at this; linarith
    have hprod : ((m : ℤ) + 1 - G) * ((l : ℤ) + 1 - G) ≤ J.card * Module.finrank k PV :=
      mul_le_mul hJ hPVdim h0' (by positivity)
    have : (Module.finrank k (L Wd) : ℤ) < (J.card * Module.finrank k PV : ℕ) := by
      push_cast
      rw [hWd]
      simp only [m] at hprod ⊢
      push_cast at hprod ⊢
      nlinarith [hlker]
    exact_mod_cast this
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt hlt (f := Ψ'))
  have hΨu : Ψ u = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hu)
  -- `u_j = g_j^{p^b}` with `g_j ∈ L(l α)`
  have hgex : ∀ j : J, ∃ g ∈ V, g ^ pe = (u j : F) := fun j ↦ (u j).2
  choose gg hggV hgg using hgex
  let g' : ℕ → F := fun j ↦ if hj : j ∈ J then gg ⟨j, hj⟩ else 0
  have hg'J : ∀ j (hj : j ∈ J), g' j = gg ⟨j, hj⟩ := fun j hj ↦ dif_pos hj
  have hg'V : ∀ j ∈ J, g' j ∈ V := fun j hj ↦ by rw [hg'J j hj]; exact hggV _
  have hΨu' : ∑ j ∈ J, g' j ^ pe * τ (hh j) = 0 := by
    rw [← hΨu, hΨ, ← Finset.sum_coe_sort J]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hg'J j j.2, hgg]
  -- the function `f = ∑ g_j^{p^b} h_j^Q`
  set f := ∑ j ∈ J, g' j ^ pe * hh j ^ Q with hf
  have hne : ∃ j ∈ J, g' j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hu0
    funext j
    apply Subtype.ext
    rw [← hgg, ← hg'J j j.2, hall j j.2, zero_pow hpe0.ne']
    rfl
  have hf0 : f ≠ 0 := sum_pow_mul_pow_ne_zero p b α hlpeQ J hh g'
    (fun j hj ↦ ⟨hh0 j hj, hhord j hj⟩) hg'V hne
  set F0 := ∑ j ∈ J, g' j * hh j ^ pe
  have hfF0 : f = F0 ^ pe := by
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_pow, ← pow_mul, ← hQpe]
  -- `f` vanishes to order `≥ p^b` at each `β ∈ S`
  have hord : ∀ β ∈ S, (pe : ℤ) ≤ β.ord f := by
    intro β hβ
    obtain ⟨hβα, hβτ⟩ := hS β hβ
    have hdiff : f = ∑ j ∈ J, g' j ^ pe * (hh j ^ Q - τ (hh j)) := by
      rw [show f = f - ∑ j ∈ J, g' j ^ pe * τ (hh j) by rw [hΨu', sub_zero], hf,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hmemβ : ∀ {A : Divisor k F} {x : F}, x ∈ L A → A β = 0 → x ∈ β.1 := by
      intro A x hx hAβ
      rcases mem_L.mp hx with h0 | h0
      · rw [h0]; exact β.1.zero_mem
      · exact β.mem_of_ord_nonneg (by have := h0 β; omega)
    have hge := β.ord_sum_ge J (fun j ↦ g' j ^ pe * (hh j ^ Q - τ (hh j))) 1 (by
      intro j hj
      have hgβ : g' j ∈ β.1 := hmemβ (hg'V j hj) (by simp [Ne.symm hβα])
      have hhβ : hh j ∈ β.1 := hmemβ (hhL j hj) (by simp [Ne.symm hβα])
      have hτβ : τ (hh j) ∈ β.1 := hmemβ (Place.apply_mem_L_single (hhL j hj))
        (by simp [Ne.symm hβτ])
      rcases hFrob β hβ (hh j) hhβ hτβ with h0 | h0
      · left; rw [h0, mul_zero]
      by_cases hg0 : g' j = 0
      · left; rw [hg0, zero_pow hpe0.ne', zero_mul]
      right
      have hd0 : hh j ^ Q - τ (hh j) ≠ 0 := by
        intro h; rw [h, Place.ord_zero] at h0; exact lt_irrefl _ h0
      rw [β.ord_mul (pow_ne_zero _ hg0) hd0, Place.ord_pow]
      have := β.ord_nonneg_of_mem hgβ
      have : (0 : ℤ) ≤ (pe : ℕ) * β.ord (g' j) := by positivity
      omega)
    rw [← hdiff] at hge
    have h1 := hge.resolve_left hf0
    rw [hfF0, Place.ord_pow] at h1 ⊢
    have hpe' : (0 : ℤ) < (pe : ℕ) := by exact_mod_cast hpe0
    have : 1 ≤ β.ord F0 := by
      by_contra hc
      push Not at hc
      have := mul_nonpos_of_nonneg_of_nonpos hpe'.le (by omega : β.ord F0 ≤ 0)
      omega
    nlinarith
  -- `f ∈ L((l p^b + m Q) α)`
  have hfL : f ∈ L (Finsupp.single α ((l * pe + m * Q : ℕ) : ℤ)) := by
    refine Submodule.sum_mem _ fun j hj ↦ ?_
    have h1 : g' j ^ pe ∈ L (Finsupp.single α ((l : ℤ) * (pe : ℕ))) :=
      powSub_le p b α l ⟨_, hg'V j hj, rfl⟩
    have h2 : hh j ^ Q ∈ L (Finsupp.single α ((m : ℤ) * (Q : ℕ))) :=
      powSub_le p (2 * b) α m ⟨_, hhL j hj, rfl⟩
    have := mul_mem_L_add h1 h2
    rw [← Finsupp.single_add] at this
    have e : ((l * pe + m * Q : ℕ) : ℤ) = (l : ℤ) * (pe : ℕ) + (m : ℤ) * (Q : ℕ) := by
      push_cast; ring
    rw [e]; exact this
  -- degrees
  have hzero : ∑ β ∈ S, (pe : ℤ) * β.deg ≤ (zeroDivisor k f).deg := by
    refine le_trans ?_ (sum_le_deg (zeroDivisor_nonneg f) S)
    refine Finset.sum_le_sum fun β hβ ↦ ?_
    rw [zeroDivisor_apply]
    exact mul_le_mul_of_nonneg_right (le_max_of_le_right (hord β hβ)) (by positivity)
  have hpolar : (polarDivisor k f).deg ≤ ((l * pe + m * Q : ℕ) : ℤ) := by
    have hle : polarDivisor k f ≤ Finsupp.single α ((l * pe + m * Q : ℕ) : ℤ) := by
      intro β
      rw [polarDivisor_apply]
      have := (mem_L.mp hfL).resolve_left hf0 β
      exact max_le (Finsupp.single_nonneg.mpr (by positivity) β) (by linarith)
    have := deg_mono hle
    rwa [deg_single, hα, Nat.cast_one, mul_one] at this
  have hdeg0 : (zeroDivisor k f).deg = (polarDivisor k f).deg := by
    have := deg_div (k := k) f
    rw [div_eq_zeroDivisor_sub_polarDivisor, deg_sub, sub_eq_zero] at this
    exact this
  have hsum : (pe : ℤ) * ∑ β ∈ S, (β.deg : ℤ) ≤ (pe : ℤ) * ((l : ℤ) + m * pe) := by
    rw [Finset.mul_sum]
    calc ∑ β ∈ S, (pe : ℤ) * β.deg ≤ ((l * pe + m * Q : ℕ) : ℤ) := by
          rw [← hdeg0] at hpolar; exact hzero.trans hpolar
      _ = (pe : ℤ) * ((l : ℤ) + m * pe) := by rw [hQpe]; push_cast; ring
  have hfin := le_of_mul_le_mul_left hsum (by exact_mod_cast hpe0)
  have hQ' : ((p : ℤ) ^ (2 * b)) = (pe : ℤ) * pe := by
    rw [← Nat.cast_pow, ← hQdef, hQpe]; push_cast; ring
  have hpe' : ((p : ℤ) ^ b) = (pe : ℤ) := by rw [hpe]; push_cast; ring
  rw [hQ', hpe', ← hGg]
  have hl' : (l : ℤ) < pe := by exact_mod_cast hlpe
  simp only [m] at hfin
  push_cast at hfin
  nlinarith

end WeilCurves.FunctionField
