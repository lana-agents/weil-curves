/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.RiemannRochSpace
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.AlgebraTower

/-!
# Riemann's theorem

For a function field `K` (with degrees and dimensions taken over `k`), the function
`A ↦ deg A - ℓ(A)` on divisors is bounded above (*Riemann's inequality*); its maximum
`WeilCurves.FunctionField.Divisor.riemannConst k K` is attained, and `ℓ(A) = deg A - riemannConst k
K`
as soon as `deg A` is large (*Riemann's theorem*). (If `k'` is the constant field of `K` and
`g` the genus, then `riemannConst k K = [k' : k] (g - 1)`.)

We follow H. Stichtenoth, *Algebraic Function Fields and Codes*, Ch. 1 §1.4
(Proposition 1.4.14, Lemma 1.4.15, Proposition 1.4.16, Theorem 1.4.17), with the following
simplifications: for `x ∈ K` transcendental with divisor of poles `B = (x)_∞`, a basis
`u_1, …, u_n` of `K / k(x)` and `C = ∑ (u_i)_∞`, the `(l + 1) n` elements `x^j u_i`
(`j ≤ l`) are `k`-linearly independent elements of `L(l B + C)`; this bounds
`deg (l B) - ℓ(l B)` uniformly in `l`. Every divisor `A` is linearly equivalent to a divisor
`≤ l B` for some `l`: add the places one at a time, using `B` at the poles of `x` and the
function `p(x)`, `p` the minimal polynomial over `k` of the residue of `x`, at the others.

The corollaries of `Belyi/CurveField/Riemann.lean` on the realisation of polar divisors use
that a vector space over the infinite field `ℚ` is not a finite union of proper subspaces; they
are not ported (over a finite base field they need a different argument).
-/

open Polynomial IsLocalRing
open scoped IntermediateField

namespace WeilCurves.FunctionField

namespace Divisor

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

/-! ### Polynomials in a function -/

theorem pow_mem_L (x : K) (kk : ℕ) : x ^ kk ∈ L (kk • polarDivisor k x) := by
  refine Or.inr fun P ↦ ?_
  simp only [Finsupp.coe_smul, Pi.smul_apply, polarDivisor_apply, nsmul_eq_mul, Place.ord_pow]
  have h1 := le_max_right 0 (-P.ord x)
  have h2 : (0 : ℤ) ≤ kk := Int.natCast_nonneg kk
  nlinarith

/-- A polynomial of degree `≤ d` in `x` lies in `L(d (x)_∞)`. -/
theorem aeval_mem_L (x : K) (p : k[X]) : aeval x p ∈ L (p.natDegree • polarDivisor k x) := by
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (L_mono ?_ (pow_mem_L x i))
  exact nsmul_le_nsmul_left (polarDivisor_nonneg x)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- At a place `P` where `x` is regular, `p(x)` vanishes for `p` the minimal polynomial of the
residue of `x`. -/
theorem ord_aeval_minpoly_residue_pos {x : K} (hx : Transcendental k x) (P : Place k K)
    (hxP : x ∈ P.1) : 0 < P.ord (aeval x (minpoly k (P.residue ⟨x, hxP⟩))) := by
  set r := P.residue ⟨x, hxP⟩
  have hint : IsIntegral k r := Algebra.IsIntegral.isIntegral r
  set p := minpoly k r
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hy0 : aeval x p ≠ 0 := fun h ↦ hx ⟨p, hp0, h⟩
  set e : P.1 := p.eval₂ P.baseHom ⟨x, hxP⟩
  have hcomp : P.1.subtype.comp P.baseHom = algebraMap k K := by
    ext q; rfl
  have he : (e : K) = aeval x p := by
    have := Polynomial.hom_eval₂ p P.baseHom P.1.subtype ⟨x, hxP⟩
    rw [hcomp] at this
    rw [aeval_def]
    exact this
  have hcomp' : P.residue.comp P.baseHom = algebraMap k P.ResidueField := by
    ext q; rfl
  have hres : P.residue e = 0 := by
    rw [Polynomial.hom_eval₂, hcomp', ← aeval_def]
    exact minpoly.aeval k r
  rw [← he]
  refine (P.ord_pos_iff_mem_maximalIdeal (a := e) (by rw [he]; exact hy0)).mpr ?_
  exact P.residue_eq_zero_iff.mp hres

/-- At a place `P` where `x` is regular, some `p(x) ≠ 0` with `p ∈ k[X]` vanishes. -/
theorem exists_aeval_ord_pos {x : K} (hx : Transcendental k x) (P : Place k K) (hxP : x ∈ P.1) :
    ∃ p : k[X], aeval x p ≠ 0 ∧ 0 < P.ord (aeval x p) :=
  ⟨_, fun h ↦ hx ⟨_, minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := k)
    (P.residue ⟨x, hxP⟩)), h⟩, ord_aeval_minpoly_residue_pos hx P hxP⟩

/-! ### Reduction to multiples of a polar divisor -/

section Reduction

variable {x : K} (hx : Transcendental k x)
include hx

omit hx in
theorem single_le_polarDivisor {P : Place k K} (hP : P.ord x < 0) :
    Finsupp.single P 1 ≤ polarDivisor k x := by
  classical
  intro Q
  by_cases hQ : P = Q
  · subst hQ; simp only [Finsupp.single_eq_same, polarDivisor_apply]; omega
  · rw [Finsupp.single_apply, if_neg hQ]; exact polarDivisor_nonneg x Q

theorem exists_add_single_add_div_le {A : Divisor k K} (P : Place k K)
    (h : ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div k z ≤ l • polarDivisor k x) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + Finsupp.single P 1 + div k z ≤ l • polarDivisor k x := by
  classical
  obtain ⟨z, hz, l, hl⟩ := h
  by_cases hP : P.ord x < 0
  · refine ⟨z, hz, l + 1, ?_⟩
    rw [succ_nsmul, show A + Finsupp.single P 1 + div k z = (A + div k z) + Finsupp.single P 1 by
      abel]
    exact add_le_add hl (single_le_polarDivisor hP)
  obtain ⟨p, hy0, hypos⟩ := exists_aeval_ord_pos hx P (P.mem_of_ord_nonneg (not_lt.mp hP))
  have hyL := (mem_L.mp (aeval_mem_L x p)).resolve_left hy0
  refine ⟨z / aeval x p, div_ne_zero hz hy0, l + p.natDegree, ?_⟩
  rw [div_div hz hy0, add_nsmul, show A + Finsupp.single P 1 + (div k z - div k (aeval x p)) =
    (A + div k z) + (Finsupp.single P 1 - div k (aeval x p)) by abel]
  refine add_le_add hl fun Q ↦ ?_
  have h1 := hyL Q
  have h2 := (nsmul_nonneg (polarDivisor_nonneg x) p.natDegree) Q
  simp only [Finsupp.coe_sub, Pi.sub_apply, div_apply, Finsupp.coe_zero,
    Pi.zero_apply] at h1 h2 ⊢
  by_cases hQ : P = Q
  · subst hQ; rw [Finsupp.single_eq_same]; omega
  · rw [Finsupp.single_apply, if_neg hQ]; omega

theorem exists_add_single_nat_add_div_le {A : Divisor k K} (P : Place k K) (m : ℕ)
    (h : ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div k z ≤ l • polarDivisor k x) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + Finsupp.single P (m : ℤ) + div k z ≤ l • polarDivisor k x := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have := exists_add_single_add_div_le hx P ih
    rwa [Nat.cast_succ, Finsupp.single_add, ← add_assoc]

/-- Every divisor is linearly equivalent to a divisor `≤ l (x)_∞` for some `l`
(Stichtenoth, proof of Proposition 1.4.14). -/
theorem exists_add_div_le (A : Divisor k K) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div k z ≤ l • polarDivisor k x := by
  classical
  induction A using Finsupp.induction with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | single_add P b f _ _ ih =>
    rcases le_or_gt b 0 with hb | hb
    · obtain ⟨z, hz, l, hl⟩ := ih
      refine ⟨z, hz, l, le_trans ?_ hl⟩
      rw [add_assoc]
      refine add_le_of_nonpos_left fun Q ↦ ?_
      rw [Finsupp.single_apply]
      split_ifs <;> simp [hb]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb.le
      rw [add_comm]
      exact exists_add_single_nat_add_div_le hx P m ih

/-- For `B = (x)_∞`, `deg (l B) - ℓ(l B)` is bounded independently of `l`. -/
theorem exists_deg_sub_ell_nsmul_le :
    ∃ γ : ℤ, ∀ l : ℕ, (l • polarDivisor k x).deg - ell (l • polarDivisor k x) ≤ γ := by
  have := finiteDimensional_adjoin hx
  set n := Module.finrank k⟮x⟯ K
  let u := Module.finBasis k⟮x⟯ K
  set B := polarDivisor k x
  set C : Divisor k K := ∑ i, polarDivisor k (u i : K)
  have hC : 0 ≤ C := fun Q ↦ by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun i _ ↦ polarDivisor_nonneg _ Q
  have hx0 : x ≠ 0 := ne_zero_of_transcendental hx
  refine ⟨C.deg - n, fun l ↦ ?_⟩
  -- the elements `x^kk u_i` lie in `L(l B + C)`
  have hmem : ∀ p : Fin (l + 1) × Fin n, x ^ (p.1 : ℕ) * u p.2 ∈ L (l • B + C) := by
    rintro ⟨kk, i⟩
    refine Or.inr fun Q ↦ ?_
    rw [Q.ord_mul (pow_ne_zero _ hx0) (u.ne_zero i), Place.ord_pow]
    have hk : ((kk : ℕ) : ℤ) ≤ l := by exact_mod_cast Nat.lt_succ_iff.mp kk.2
    have hk0 : (0 : ℤ) ≤ (kk : ℕ) := Int.natCast_nonneg _
    have h1 := le_max_right 0 (-Q.ord x)
    have h1' := le_max_left 0 (-Q.ord x)
    have h2 := le_max_right 0 (-Q.ord (u i))
    have h3 : max 0 (-Q.ord (u i)) ≤ C Q := by
      rw [Finsupp.finsetSum_apply]
      exact Finset.single_le_sum (f := fun j ↦ polarDivisor k (u j : K) Q)
        (fun j _ ↦ polarDivisor_nonneg _ Q) (Finset.mem_univ i)
    simp only [B, Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, polarDivisor_apply,
      nsmul_eq_mul]
    nlinarith
  -- they are linearly independent over `k`
  have hpow : LinearIndependent k (fun kk : ℕ ↦ x ^ kk) := by
    have := (Polynomial.basisMonomials k).linearIndependent.map' (aeval x).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hx))
    simpa [Function.comp_def, Polynomial.coe_basisMonomials] using this
  let b : Fin (l + 1) → k⟮x⟯ := fun kk ↦ (IntermediateField.AdjoinSimple.gen k x) ^ (kk : ℕ)
  have hb : LinearIndependent k b := by
    refine LinearIndependent.of_comp (IsScalarTower.toAlgHom k k⟮x⟯ K).toLinearMap ?_
    convert hpow.comp (Fin.val) Fin.val_injective using 1
    ext kk
    simp [b]
  have hli := linearIndependent_smul hb u.linearIndependent
  have hv : ∀ p : Fin (l + 1) × Fin n, b p.1 • (u p.2 : K) = x ^ (p.1 : ℕ) * u p.2 := by
    intro p
    simp [b, Algebra.smul_def]
  let w : Fin (l + 1) × Fin n → L (l • B + C) := fun p ↦ ⟨x ^ (p.1 : ℕ) * u p.2, hmem p⟩
  have hw : LinearIndependent k w := by
    refine LinearIndependent.of_comp (L (l • B + C)).subtype ?_
    convert hli using 1
    ext p
    exact (hv p).symm
  have hcard := hw.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hdegD : (l • B + C).deg = l * n + C.deg := by
    rw [deg_add, deg_nsmul, deg_polarDivisor hx]
  have hmono := deg_sub_ell_mono (le_add_of_nonneg_right hC : l • B ≤ l • B + C)
  have hcard' : ((l : ℤ) + 1) * n ≤ ell (l • B + C) := by exact_mod_cast hcard
  have : ((l : ℤ) + 1) * n = l * n + n := by ring
  omega

end Reduction

/-! ### Riemann's theorem -/

/-- **Riemann's inequality** (Stichtenoth, Proposition 1.4.14): `deg A - ℓ(A)` is bounded
above. -/
theorem exists_deg_sub_ell_le : ∃ γ : ℤ, ∀ A : Divisor k K, A.deg - ell A ≤ γ := by
  obtain ⟨x, hx⟩ := exists_transcendental k K
  obtain ⟨γ, hγ⟩ := exists_deg_sub_ell_nsmul_le hx
  refine ⟨γ, fun A ↦ ?_⟩
  obtain ⟨z, hz, l, hl⟩ := exists_add_div_le hx A
  have h := deg_sub_ell_mono hl
  rw [deg_add, deg_div, add_zero, ell_add_div A hz] at h
  exact h.trans (hγ l)

variable (k K) in
/-- The constant `max_A (deg A - ℓ(A))` of Riemann's theorem (it equals `[k' : k](g - 1)`,
for `k'` the constant field and `g` the genus). -/
noncomputable def riemannConst : ℤ :=
  sSup (Set.range fun A : Divisor k K ↦ A.deg - (ell A : ℤ))

theorem bddAbove_range_deg_sub_ell :
    BddAbove (Set.range fun A : Divisor k K ↦ A.deg - (ell A : ℤ)) := by
  obtain ⟨γ, hγ⟩ := exists_deg_sub_ell_le (k := k) (K := K)
  exact ⟨γ, by rintro _ ⟨A, rfl⟩; exact hγ A⟩

theorem deg_sub_ell_le_riemannConst (A : Divisor k K) : A.deg - ell A ≤ riemannConst k K :=
  le_csSup bddAbove_range_deg_sub_ell ⟨A, rfl⟩

/-- **Riemann's inequality**: `ℓ(A) ≥ deg A - riemannConst k K`. -/
theorem riemann_inequality (A : Divisor k K) : A.deg - riemannConst k K ≤ ell A := by
  have := deg_sub_ell_le_riemannConst A
  omega

theorem exists_deg_sub_ell_eq_riemannConst :
    ∃ A : Divisor k K, A.deg - ell A = riemannConst k K := by
  obtain ⟨A, hA⟩ :=
    Int.csSup_mem (Set.range_nonempty _) (bddAbove_range_deg_sub_ell (k := k) (K := K))
  exact ⟨A, hA⟩

/-- **Riemann's theorem** (Stichtenoth, Theorem 1.4.17, with `riemannConst k K` in place of
`g - 1`): `ℓ(A) = deg A - riemannConst k K` for all `A` of sufficiently large degree. -/
theorem riemann_equality :
    ∃ N0 : ℤ, ∀ A : Divisor k K, N0 ≤ A.deg → (ell A : ℤ) = A.deg - riemannConst k K := by
  obtain ⟨A0, hA0⟩ := exists_deg_sub_ell_eq_riemannConst (k := k) (K := K)
  refine ⟨A0.deg + riemannConst k K + 1, fun A hA ↦ ?_⟩
  have h1 := riemann_inequality (A - A0)
  rw [deg_sub] at h1
  obtain ⟨z, hz, hle⟩ := exists_nonneg_add_div (A := A - A0) (by omega)
  have hle' : A0 ≤ A + div k z := by
    intro Q
    have := hle Q
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    omega
  have h2 := deg_sub_ell_mono hle'
  rw [deg_add, deg_div, add_zero, ell_add_div A hz] at h2
  have h3 := deg_sub_ell_le_riemannConst A
  omega

/-- **Riemann's theorem**, existential form. -/
theorem exists_riemann :
    ∃ g0 N0 : ℤ, ∀ A : Divisor k K, N0 ≤ A.deg → (ell A : ℤ) = A.deg - g0 :=
  ⟨riemannConst k K, riemann_equality⟩

/-! ### Positive parts -/

/-- The positive part `max A 0` of a divisor. -/
noncomputable def posPart (A : Divisor k K) : Divisor k K :=
  Finsupp.mapRange (fun n ↦ max n 0) (by simp) A

omit [PerfectField k] [IsFunctionField k K] in
theorem posPart_apply (A : Divisor k K) (P : Place k K) : posPart A P = max (A P) 0 :=
  Finsupp.mapRange_apply ..

omit [PerfectField k] [IsFunctionField k K] in
theorem posPart_nonneg (A : Divisor k K) : 0 ≤ posPart A := fun P ↦ by
  simp [posPart_apply]

omit [PerfectField k] [IsFunctionField k K] in
theorem posPart_sub_posPart_neg (A : Divisor k K) : posPart A - posPart (-A) = A := by
  ext P
  simp only [Finsupp.coe_sub, Pi.sub_apply, posPart_apply, Finsupp.coe_neg, Pi.neg_apply]
  omega

end Divisor

end WeilCurves.FunctionField
