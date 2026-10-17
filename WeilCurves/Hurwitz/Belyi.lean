/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Hurwitz.Tame

/-!
# The genus of a Belyi cover

Let `k` be algebraically closed of characteristic zero, `L` a function field over `k` and
`x ∈ L` transcendental, unramified outside `0, 1, ∞`: for every place `Q` of `L` and every
`a ∈ k ∖ {0, 1}`, `ord_Q (x - a) ≤ 1`. With `d = [L : k(x)]` and the fibre counts
`c₀ = #{Q | ord_Q x > 0}`, `c₁ = #{Q | ord_Q (x - 1) > 0}`, `c_∞ = #{Q | ord_Q x < 0}`,

  `2 g_L - 2 = d - c₀ - c₁ - c_∞`   (`genus_belyi`).

Proof: the Riemann–Hurwitz formula in characteristic zero (`riemannHurwitz_charZero`) for
`L / k(x)`, with `g(k(x)) = 0` (`genus_eq_zero_of_finrank_eq_one`), all places of degree one
(`k` algebraically closed), `e(Q) = ord_Q (x - a)` above `a ∈ k` and `e(Q) = -ord_Q x` above `∞`,
and `∑_{x(Q) = a} e(Q) = d = ∑_{x(Q) = ∞} e(Q)` (`sum_ord_mul_deg_zeros`,
`sum_ord_mul_deg_poles`).
-/

open Module
open scoped IntermediateField

set_option linter.unusedSectionVars false

namespace WeilCurves.FunctionField

section Rational

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [PerfectField k] [IsFunctionField k F]

/-- If `[F : k(s)] = 1`, every zero of `s` is simple. -/
theorem ord_eq_one_of_finrank_eq_one {s : F} (hs : Transcendental k s)
    (h1 : finrank k⟮s⟯ F = 1) {P : Place k F} (hP : 0 < P.ord s) : P.ord s = 1 ∧ P.deg = 1 := by
  classical
  have hsum := Place.sum_ord_mul_deg_zeros s hs
  rw [h1, Nat.cast_one] at hsum
  set T := (Place.finite_setOf_ord_pos (k := k) s).toFinset
  have hPT : P ∈ T := by simpa [T] using hP
  have hle : P.ord s * (P.deg : ℤ) ≤ 1 := by
    rw [← hsum]
    refine Finset.single_le_sum (f := fun P : Place k F ↦ P.ord s * (P.deg : ℤ))
      (fun Q hQ ↦ ?_) hPT
    have : 0 < Q.ord s := by simpa [T] using hQ
    positivity
  have hd : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have h1' : P.ord s = 1 := by nlinarith
  refine ⟨h1', ?_⟩
  rw [h1', one_mul] at hle
  exact_mod_cast le_antisymm hle hd

/-- If `ℓ(0) = 1` and `[F : k(t)] = 1`, then `F` has genus `0`. -/
theorem genus_eq_zero_of_finrank_eq_one (hell : Divisor.ell (0 : Divisor k F) = 1) {t : F}
    (ht : Transcendental k t) (h1 : finrank k⟮t⟯ F = 1) : genus k F = 0 := by
  classical
  -- the pole divisor of `t` is a single place of degree one
  obtain ⟨P₀, hP₀⟩ := Place.exists_ord_neg ht
  have hinv : finrank k⟮t⁻¹⟯ F = 1 := by rw [adjoin_inv_eq]; exact h1
  have hP₀' : 0 < P₀.ord t⁻¹ := by rw [Place.ord_inv]; omega
  obtain ⟨hord, hdeg⟩ := ord_eq_one_of_finrank_eq_one (transcendental_inv ht) hinv hP₀'
  have hpolar : Divisor.polarDivisor k t = Finsupp.single P₀ 1 := by
    have hsum := Place.sum_ord_mul_deg_poles t ht
    rw [h1] at hsum
    set T := (Place.finite_setOf_ord_neg (k := k) t).toFinset
    have hP₀T : P₀ ∈ T := by simpa [T] using hP₀
    rw [← Finset.add_sum_erase T _ hP₀T] at hsum
    rw [Place.ord_inv] at hord
    rw [show -P₀.ord t = 1 by omega, hdeg] at hsum
    have hrest : ∀ Q ∈ T.erase P₀, 1 ≤ -Q.ord t * (Q.deg : ℤ) := by
      intro Q hQ
      have : Q.ord t < 0 := by simpa [T] using Finset.mem_of_mem_erase hQ
      have : (1 : ℤ) ≤ Q.deg := by exact_mod_cast Q.deg_pos
      nlinarith
    have hcard := Finset.card_nsmul_le_sum (T.erase P₀) _ 1 hrest
    have hempty : T.erase P₀ = ∅ := by
      rw [← Finset.card_eq_zero]
      simp only [nsmul_eq_mul, mul_one] at hcard
      push_cast at hsum
      omega
    ext Q
    rw [Divisor.polarDivisor_apply, Finsupp.single_apply]
    split_ifs with hQ
    · subst hQ; omega
    · by_contra hne
      have hneg : Q.ord t < 0 := by omega
      have : Q ∈ T.erase P₀ := Finset.mem_erase.mpr ⟨Ne.symm hQ, by simpa [T] using hneg⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty _)
  -- `ℓ(m P₀) = m + 1`
  have hell_eq : ∀ m : ℕ, (Divisor.ell (m • Divisor.polarDivisor k t) : ℤ) = m + 1 := by
    intro m
    apply le_antisymm
    · have := Divisor.ell_le_max (m • Divisor.polarDivisor k t)
      have hd : (m • Divisor.polarDivisor k t).deg = m := by
        rw [Divisor.deg_nsmul, hpolar, Divisor.deg_single, hdeg]; simp
      rw [hd, hell] at this
      push_cast at this
      omega
    · have hmem : ∀ j : Fin (m + 1), t ^ (j : ℕ) ∈ Divisor.L (m • Divisor.polarDivisor k t) :=
        fun j ↦ Divisor.L_mono (nsmul_le_nsmul_left (Divisor.polarDivisor_nonneg t)
          (Nat.lt_succ_iff.mp j.2)) (Divisor.pow_mem_L t j)
      have hli : LinearIndependent k (fun j : Fin (m + 1) ↦ t ^ (j : ℕ)) := by
        have h0 : LinearIndependent k (fun j : ℕ ↦ (Polynomial.X : Polynomial k) ^ j) := by
          simpa [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow] using
            (Polynomial.basisMonomials k).linearIndependent
        have h2 := (h0.map' (Polynomial.aeval t).toLinearMap (by
          rw [LinearMap.ker_eq_bot]
          exact transcendental_iff_injective.mp ht)).comp (Fin.val : Fin (m + 1) → ℕ)
          Fin.val_injective
        simpa [Function.comp_def] using h2
      have hli' : LinearIndependent k
          (fun j : Fin (m + 1) ↦
            (⟨t ^ (j : ℕ), hmem j⟩ : Divisor.L (m • Divisor.polarDivisor k t))) :=
        LinearIndependent.of_comp (Divisor.L _).subtype hli
      have := hli'.fintype_card_le_finrank
      rw [Fintype.card_fin] at this
      have : m + 1 ≤ Divisor.ell (m • Divisor.polarDivisor k t) := this
      omega
  obtain ⟨N, hN⟩ := Divisor.riemann_equality (k := k) (K := F)
  have hdegm : ((N.toNat • Divisor.polarDivisor k t).deg) = N.toNat := by
    rw [Divisor.deg_nsmul, hpolar, Divisor.deg_single, hdeg]; simp
  have h := hN (N.toNat • Divisor.polarDivisor k t) (by rw [hdegm]; exact Int.self_le_toNat N)
  rw [hell_eq, hdegm] at h
  rw [genus]
  omega

/-- Over an algebraically closed field, `ℓ(0) = 1`. -/
theorem ell_zero_eq_one_of_isAlgClosed [IsAlgClosed k] : Divisor.ell (0 : Divisor k F) = 1 := by
  rw [Divisor.ell_zero, Subalgebra.finrank_eq_one_iff]
  refine eq_bot_iff.mpr fun y hy ↦ ?_
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := integralClosure k F)).2 ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc⟩

/-- Over an algebraically closed field, every place has degree one. -/
theorem Place.deg_eq_one [IsAlgClosed k] (P : Place k F) : P.deg = 1 := by
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := P.ResidueField)
  have e := LinearEquiv.ofBijective (Algebra.linearMap k P.ResidueField) hb
  rw [Place.deg, ← e.finrank_eq, Module.finrank_self]

/-- Over an algebraically closed field, a function regular at `P` takes a value `a ∈ k` there. -/
theorem Place.exists_ord_sub_pos [IsAlgClosed k] (P : Place k F) {x : F} (hx : Transcendental k x)
    (hxP : x ∈ P.1) : ∃ a : k, 0 < P.ord (x - algebraMap k F a) := by
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := P.ResidueField)
  obtain ⟨a, ha⟩ := hb.2 (P.residue ⟨x, hxP⟩)
  refine ⟨a, (P.ord_pos_iff).mpr ⟨fun h ↦ ?_, ?_⟩⟩
  · exact hx (by
      rw [sub_eq_zero] at h
      rw [h]; exact isAlgebraic_algebraMap a)
  · have hmem : x - algebraMap k F a ∈ P.1 := P.1.sub_mem hxP (P.algebraMap_mem a)
    have h0 : P.residue ⟨_, hmem⟩ = 0 := by
      have h1 : (⟨_, hmem⟩ : P.1) = ⟨x, hxP⟩ - P.baseHom a := rfl
      rw [h1, map_sub, ← Place.algebraMap_residueField, ← ha, sub_self]
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmem⟩)).mpr
      ((P.residue_eq_zero_iff).mp h0)

end Rational


section Belyi

theorem adjoin_sub_algebraMap_eq {k F : Type*} [Field k] [Field F] [Algebra k F] (s : F) (a : k) :
    k⟮s - algebraMap k F a⟯ = k⟮s⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact sub_mem (IntermediateField.mem_adjoin_simple_self k s)
      (IntermediateField.algebraMap_mem _ a)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := add_mem (IntermediateField.mem_adjoin_simple_self k (s - algebraMap k F a))
      (IntermediateField.algebraMap_mem k⟮s - algebraMap k F a⟯ a)
    simpa using this

theorem transcendental_sub_algebraMap {k F : Type*} [Field k] [Field F] [Algebra k F] {s : F}
    (hs : Transcendental k s) (a : k) : Transcendental k (s - algebraMap k F a) := fun h ↦
  hs (by simpa using h.add (isAlgebraic_algebraMap a))

variable {k L : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Field L] [Algebra k L]
  [IsFunctionField k L]

/-- **The genus of a Belyi cover**: if `x ∈ L` is transcendental and unramified outside
`0, 1, ∞` (`ord_Q (x - a) ≤ 1` for `a ≠ 0, 1`), then
`2 g_L - 2 = [L : k(x)] - c₀ - c₁ - c_∞` with `c₀, c₁, c_∞` the numbers of places of `L` over
`0, 1, ∞`. -/
theorem genus_belyi {x : L} (hx : Transcendental k x)
    (hunr : ∀ Q : Place k L, ∀ a : k, a ≠ 0 → a ≠ 1 → Q.ord (x - algebraMap k L a) ≤ 1) :
    2 * genus k L - 2 = (finrank k⟮x⟯ L : ℤ) - {Q : Place k L | 0 < Q.ord x}.ncard -
      {Q : Place k L | 0 < Q.ord (x - 1)}.ncard - {Q : Place k L | Q.ord x < 0}.ncard := by
  classical
  set K := k⟮x⟯
  set t : K := IntermediateField.AdjoinSimple.gen k x
  have htx : algebraMap K L t = x := rfl
  have ht : Transcendental k t := by
    rw [← transcendental_algebraMap_iff (algebraMap K L).injective, htx]; exact hx
  have htop : k⟮t⟯ = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  have hK1 : ∀ a : k, finrank k⟮t - algebraMap k K a⟯ K = 1 := fun a ↦ by
    rw [adjoin_sub_algebraMap_eq, IntermediateField.finrank_eq_one_iff_eq_top]; exact htop
  have hK1' : finrank k⟮t⟯ K = 1 := by
    rw [IntermediateField.finrank_eq_one_iff_eq_top]; exact htop
  haveI : FiniteDimensional k⟮t⟯ K := Module.finite_of_finrank_eq_succ hK1'
  haveI : IsFunctionField k K := ⟨⟨t, ht, inferInstance⟩⟩
  haveI : FiniteDimensional K L := finiteDimensional_adjoin hx
  have hgK : genus k K = 0 := genus_eq_zero_of_finrank_eq_one ell_zero_eq_one_of_isAlgClosed ht hK1'
  -- ramification indices above `a ∈ k` and above `∞`
  have hram : ∀ (Q : Place k L) (a : k), 0 < Q.ord (x - algebraMap k L a) →
      ramIndex K Q = Q.ord (x - algebraMap k L a) := by
    intro Q a hQ
    have hxa : x - algebraMap k L a = algebraMap K L (t - algebraMap k K a) := by
      rw [map_sub, htx, ← IsScalarTower.algebraMap_apply]
    rw [hxa, ord_algebraMap_eq_ramIndex_mul] at hQ ⊢
    have he := ramIndex_pos (K := K) Q
    have hpos : 0 < (Q.restrict (K := K)).ord (t - algebraMap k K a) :=
      pos_of_mul_pos_right hQ he.le
    obtain ⟨h1, -⟩ := ord_eq_one_of_finrank_eq_one (transcendental_sub_algebraMap ht a)
      (hK1 a) hpos
    rw [h1, mul_one]
  have hramInf : ∀ Q : Place k L, Q.ord x < 0 → ramIndex K Q = -Q.ord x := by
    intro Q hQ
    have hxi : x⁻¹ = algebraMap K L t⁻¹ := by rw [map_inv₀, htx]
    have hQ' : 0 < Q.ord (algebraMap K L t⁻¹) := by rw [← hxi, Place.ord_inv]; omega
    rw [ord_algebraMap_eq_ramIndex_mul] at hQ'
    have he := ramIndex_pos (K := K) Q
    have hpos := pos_of_mul_pos_right hQ' he.le
    have hinv : finrank k⟮t⁻¹⟯ K = 1 := by rw [adjoin_inv_eq]; exact hK1'
    obtain ⟨h1, -⟩ := ord_eq_one_of_finrank_eq_one (transcendental_inv ht) hinv hpos
    have := congrArg Q.ord hxi
    rw [Place.ord_inv, ord_algebraMap_eq_ramIndex_mul, h1, mul_one] at this
    omega
  -- the finite sets of places over `0`, `1`, `∞`
  set Z0 := (Place.finite_setOf_ord_pos (k := k) x).toFinset
  set Z1 := (Place.finite_setOf_ord_pos (k := k) (x - 1)).toFinset
  set Zi := (Place.finite_setOf_ord_neg (k := k) x).toFinset
  have hmem0 : ∀ Q, Q ∈ Z0 ↔ 0 < Q.ord x := fun Q ↦ by simp [Z0]
  have hmem1 : ∀ Q, Q ∈ Z1 ↔ 0 < Q.ord (x - 1) := fun Q ↦ by simp [Z1]
  have hmemi : ∀ Q, Q ∈ Zi ↔ Q.ord x < 0 := fun Q ↦ by simp [Zi]
  have hx1 : x - 1 = x - algebraMap k L 1 := by rw [map_one]
  have hunram : ∀ Q : Place k L, Q ∉ Z0 ∪ Z1 ∪ Zi → ramIndex K Q = 1 := by
    intro Q hQ
    simp only [Finset.mem_union, hmem0, hmem1, hmemi, not_or] at hQ
    obtain ⟨⟨h0, h1⟩, hi⟩ := hQ
    have hxQ : x ∈ Q.1 := Q.mem_of_ord_nonneg (by omega)
    obtain ⟨a, ha⟩ := Q.exists_ord_sub_pos hx hxQ
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha; omega
    have ha1 : a ≠ 1 := by rintro rfl; rw [← hx1] at ha; omega
    have := hunr Q a ha0 ha1
    rw [hram Q a ha]
    omega
  have hRH := riemannHurwitz_charZero (K := K) (Z0 ∪ Z1 ∪ Zi) hunram
  rw [hgK] at hRH
  -- disjointness
  have hd01 : Disjoint Z0 Z1 := by
    rw [Finset.disjoint_left]
    intro Q h0 h1
    rw [hmem0] at h0; rw [hmem1] at h1
    have hne : x + -(x - 1) ≠ 0 := by simp
    have := Q.min_le_ord_add hne
    rw [Place.ord_neg, show x + -(x - 1) = 1 by ring, Place.ord_one] at this
    omega
  have hdi : Disjoint (Z0 ∪ Z1) Zi := by
    rw [Finset.disjoint_left]
    intro Q h hi
    rw [hmemi] at hi
    rcases Finset.mem_union.mp h with h0 | h1
    · rw [hmem0] at h0; omega
    · rw [hmem1] at h1
      have hne : (x - 1) + 1 ≠ 0 := by simpa using ne_zero_of_transcendental hx
      have := Q.min_le_ord_add hne
      rw [Place.ord_one, show x - 1 + 1 = x by ring] at this
      omega
  rw [Finset.sum_union hdi, Finset.sum_union hd01] at hRH
  have hdeg : ∀ Q : Place k L, (Q.deg : ℤ) = 1 := fun Q ↦ by rw [Place.deg_eq_one]; rfl
  have hs0 : ∑ Q ∈ Z0, (ramIndex K Q - 1) * (Q.deg : ℤ) = finrank k⟮x⟯ L - Z0.card := by
    have h := Place.sum_ord_mul_deg_zeros x hx
    rw [Finset.sum_congr rfl fun Q hQ ↦ by
      rw [hdeg, mul_one, show ramIndex K Q = Q.ord x by
        have := hram Q 0 (by simpa using (hmem0 Q).mp hQ); simpa using this]]
    simp only [hdeg, mul_one] at h
    rw [Finset.sum_sub_distrib, h]
    simp
  have hs1 : ∑ Q ∈ Z1, (ramIndex K Q - 1) * (Q.deg : ℤ) = finrank k⟮x⟯ L - Z1.card := by
    have h := Place.sum_ord_mul_deg_zeros (x - 1)
      (by rw [hx1]; exact transcendental_sub_algebraMap hx 1)
    rw [Finset.sum_congr rfl fun Q hQ ↦ by
      rw [hdeg, mul_one, show ramIndex K Q = Q.ord (x - 1) by
        have := hram Q 1 (by rw [← hx1]; exact (hmem1 Q).mp hQ); rwa [← hx1] at this]]
    simp only [hdeg, mul_one] at h
    rw [Finset.sum_sub_distrib, h, hx1, adjoin_sub_algebraMap_eq]
    simp
  have hsi : ∑ Q ∈ Zi, (ramIndex K Q - 1) * (Q.deg : ℤ) = finrank k⟮x⟯ L - Zi.card := by
    have h := Place.sum_ord_mul_deg_poles x hx
    rw [Finset.sum_congr rfl fun Q hQ ↦ by
      rw [hdeg, mul_one, hramInf Q ((hmemi Q).mp hQ)]]
    simp only [hdeg, mul_one] at h
    rw [Finset.sum_sub_distrib, h]
    simp
  rw [hs0, hs1, hsi] at hRH
  have hc0 : {Q : Place k L | 0 < Q.ord x}.ncard = Z0.card := Set.ncard_eq_toFinset_card _ _
  have hc1 : {Q : Place k L | 0 < Q.ord (x - 1)}.ncard = Z1.card := Set.ncard_eq_toFinset_card _ _
  have hci : {Q : Place k L | Q.ord x < 0}.ncard = Zi.card := Set.ncard_eq_toFinset_card _ _
  rw [hc0, hc1, hci, hRH]
  change (finrank K L : ℤ) * (2 * 0 - 2) + _ = _
  ring

end Belyi

end WeilCurves.FunctionField
