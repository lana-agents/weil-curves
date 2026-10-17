/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Bombieri.Main
import WeilCurves.ConstantExtension.ExtPlaces
import WeilCurves.FiniteField.PlaceCount
import WeilCurves.Galois.BaseField
import WeilCurves.Galois.Frobenius
import WeilCurves.Galois.Ramification

/-!
# The lower bound for `N_r` from a Galois cover of `k'(x)`

Nivedita (*Riemann hypothesis for function fields*, CMI 2009), §3.2.3, eq. (3.4),
Propositions 3.8–3.9 and Theorem 3.10; Kedlaya (*Weil cohomology* notes), Lemmas 5.1.7–5.1.9.

Setting: `F` a function field over a finite field `k` (`q` elements, full constant field), `M ⊇ F`
a finite extension which is a function field over a finite extension `k' ⊇ k` (`d = [k' : k]`)
with full constant field `k'` and a place `α` of degree one over `k'`, `x ∈ F` such that `M` is
Galois over `k'(x)` (group `G`) and over `F`. For `Q = |k'|^m = q^{dm} = p^{2b}` with
`(g(M) + 1)^4 < Q`:

* the zeros `β` of `z = x^Q − x` in `M` (places over `k'(x)`-places of degree dividing `m`) have
  `∑ ord_β(z) deg β = |G| Q`, and those with `ord_β z ≥ 2` contribute at most a constant
  `C` independent of `Q` (`exists_ramification_bound`);
* each simple zero `β` has a Frobenius `σ_β ∈ G` with `y^Q ≡ σ_β y (mod β)`
  (`exists_frobenius_place`); for each `σ`, Bombieri's twisted bound gives
  `N(σ) = ∑_{σ_β = σ} deg β ≤ Q + (2g + 1) p^b + 2`;
* for `σ` in `H = Gal(M / F k'(x))` the places with `σ_β = σ` lie over places of `F` of degree
  dividing `dm` and the fundamental inequality gives `d ∑_{σ ∈ H} N(σ) ≤ [M : F] N_{dm}(F)`,
  with `[M : F] ≤ d |H|`.

Hence `N_{dm}(F) ≥ Q − (|G| − 1)((2g + 1) p^b + 2) − C` (`pointCount_ge_of_galois`).
-/

open Polynomial
open scoped IntermediateField

namespace WeilCurves.FunctionField

open Place

section HBound

variable {k F k' M : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
  [Field k'] [Finite k'] [Algebra k k'] [Field M] [Algebra k' M] [Algebra k M]
  [IsScalarTower k k' M] [Algebra F M] [IsScalarTower k F M] [FiniteDimensional F M]

/-- The automorphisms of `M` fixing `F` and `k'` (pointwise), as elements of `Gal(M / k'(x))`. -/
def fixF (x : F) : Set Gal(M/k'⟮algebraMap F M x⟯) :=
  {σ | ∀ f : F, σ (algebraMap F M f) = algebraMap F M f}

/-- **`[M : F] ≤ [k' : k] · |Gal(M / F k'(x))|`** (when `M / F` is Galois). -/
theorem finrank_le_mul_card_fixF [IsGalois F M] (x : F)
    [FiniteDimensional k'⟮algebraMap F M x⟯ M] :
    Module.finrank F M ≤ Module.finrank k k' *
      Nat.card (fixF (k' := k') (M := M) x) := by
  classical
  set xM := algebraMap F M x
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k k'
  set θM := algebraMap k' M θ
  set E := IntermediateField.adjoin F {θM}
  have hθint : IsIntegral k θ := Algebra.IsIntegral.isIntegral θ
  -- every element of `k'` is a polynomial in `θ` over `k`
  have hpoly : ∀ c : k', ∃ g : k[X], aeval θ g = c := by
    intro c
    have hc : c ∈ (k⟮θ⟯).toSubalgebra := by rw [hθ]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨g, hg⟩ := hc
    exact ⟨g, hg⟩
  -- `[E : F] ≤ [k' : k]`
  have hE : Module.finrank F E ≤ Module.finrank k k' := by
    have hθM : IsIntegral F θM := Algebra.IsIntegral.isIntegral θM
    rw [IntermediateField.adjoin.finrank hθM]
    have hdvd : minpoly F θM ∣ (minpoly k θ).map (algebraMap k F) := by
      apply minpoly.dvd
      rw [aeval_map_algebraMap]
      change aeval (algebraMap k' M θ) (minpoly k θ) = 0
      rw [aeval_algebraMap_apply, minpoly.aeval, map_zero]
    have hne : (minpoly k θ).map (algebraMap k F) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hθint)
    calc (minpoly F θM).natDegree ≤ ((minpoly k θ).map (algebraMap k F)).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hne
      _ = (minpoly k θ).natDegree := Polynomial.natDegree_map _
      _ = Module.finrank k k' := by
          rw [← IntermediateField.adjoin.finrank hθint, hθ, IntermediateField.finrank_top']
  -- the restriction map `Aut(M / E) → Gal(M / k'(x))`
  have hfixθ : ∀ e : M ≃ₐ[E] M, ∀ c : k', e (algebraMap k' M c) = algebraMap k' M c := by
    intro e c
    obtain ⟨g, rfl⟩ := hpoly c
    rw [← aeval_algebraMap_apply]
    have h1 : e θM = θM := e.commutes ⟨θM, IntermediateField.mem_adjoin_simple_self F θM⟩
    have h2 : ∀ a : k, e (algebraMap k M a) = algebraMap k M a := by
      intro a
      have := e.commutes ⟨algebraMap k M a, by
        rw [IsScalarTower.algebraMap_apply k F M]
        exact IntermediateField.algebraMap_mem E (algebraMap k F a)⟩
      exact this
    induction g using Polynomial.induction_on with
    | C a => rw [aeval_C, h2]
    | add g h hg hh => rw [map_add, map_add, hg, hh]
    | monomial n a _ =>
      rw [map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow, h2, h1]
  have hfixF : ∀ e : M ≃ₐ[E] M, ∀ f : F, e (algebraMap F M f) = algebraMap F M f := by
    intro e f
    have := e.commutes ⟨algebraMap F M f, IntermediateField.algebraMap_mem E f⟩
    exact this
  -- `e` as a `k'`-algebra automorphism
  let toK' : (M ≃ₐ[E] M) → (M ≃ₐ[k'] M) := fun e ↦
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun c ↦ hfixθ e c)
  have hfixx : ∀ e : M ≃ₐ[E] M, ∀ m ∈ k'⟮xM⟯, toK' e m = m := by
    intro e m hm
    have hext : (toK' e).toAlgHom.comp (k'⟮xM⟯).val = (k'⟮xM⟯).val := by
      apply IntermediateField.adjoin_algHom_ext
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hfixF e x
    exact DFunLike.congr_fun hext ⟨m, hm⟩
  let ι : (M ≃ₐ[E] M) → Gal(M/k'⟮xM⟯) := fun e ↦
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun c ↦ hfixx e c c.2)
  have hι : Function.Injective ι := by
    intro e₁ e₂ h
    ext m
    exact DFunLike.congr_fun h m
  have hιH : ∀ e, ι e ∈ fixF (k' := k') (M := M) x := fun e f ↦ hfixF e f
  have hcard : Nat.card (M ≃ₐ[E] M) ≤ Nat.card (fixF (k' := k') (M := M) x) := by
    have : Finite (fixF (k' := k') (M := M) x) := Subtype.finite
    exact Nat.card_le_card_of_injective (fun e ↦ ⟨ι e, hιH e⟩)
      fun e₁ e₂ h ↦ hι (congrArg Subtype.val h)
  have hgal : Nat.card (M ≃ₐ[E] M) = Module.finrank E M := IsGalois.card_aut_eq_finrank E M
  rw [← Module.finrank_mul_finrank F E M, ← hgal]
  exact Nat.mul_le_mul hE hcard

end HBound

section Helpers

theorem Finset.sum_le_sum_erase_add {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i, 0 ≤ f i) (a : ι) : ∑ i ∈ s, f i ≤ ∑ i ∈ s.erase a, f i + f a := by
  by_cases ha : a ∈ s
  · rw [← Finset.sum_erase_add s f ha]
  · rw [Finset.erase_eq_of_notMem ha]; linarith [hf a]

variable {k M : Type*} [Field k] [Field M] [Algebra k M] [PerfectField k] [IsFunctionField k M]

theorem Place.eq_zero_or_ord_pos_of_mem_nonunits (β : Place k M) {f : M}
    (hf : f ∈ β.1.nonunits) : f = 0 ∨ 0 < β.ord f := by
  by_cases h0 : f = 0
  · exact Or.inl h0
  · exact Or.inr ((β.ord_pos_iff).mpr ⟨h0, hf⟩)

end Helpers

section Main

variable {k F k' M : Type*} [Field k] [Finite k] [Field F] [Algebra k F] [IsFunctionField k F]
  [Field k'] [Finite k'] [Algebra k k'] [Field M] [Algebra k' M] [Algebra k M]
  [IsScalarTower k k' M] [Algebra F M] [IsScalarTower k F M] [FiniteDimensional F M]
  [IsFunctionField k' M] [IsFunctionField k M]

omit [Finite k'] [IsFunctionField k' M] [IsFunctionField k M] in
/-- Places of `M` with a Frobenius in `Gal(M / F k'(x))` lie over places of `F` of degree
dividing `r`, where `Q = q^r`. -/
theorem deg_restrict_dvd_of_frob (x : F) (β : Place k' M) (σ : Gal(M/k'⟮algebraMap F M x⟯))
    (hσ : σ ∈ fixF x) {Q r : ℕ} (hQr : Q = Nat.card k ^ r)
    (hfr : ∀ y ∈ β.1, y ^ Q - σ y ∈ β.1.nonunits) :
    ((β.toBase (k := k)).restrict (K := F)).deg ∣ r := by
  set P' := (β.toBase (k := k)).restrict (K := F)
  have : Finite P'.ResidueField := Module.finite_of_finite k
  apply finrank_dvd_of_forall_pow_eq
  intro y
  obtain ⟨a, rfl⟩ := P'.residue_surjective y
  rw [← hQr, ← map_pow, eq_comm, ← sub_eq_zero, ← map_sub, Place.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  have ha : algebraMap F M (a : F) ∈ β.1 :=
    (Place.mem_restrict (K := F) (Q := β.toBase (k := k))).mp a.2
  have hm := hfr _ ha
  rw [hσ (a : F)] at hm
  rw [ValuationSubring.mem_nonunits_iff_or] at hm ⊢
  push_cast
  rcases hm with h | h
  · left
    apply (algebraMap F M).injective
    rw [map_sub, map_pow, map_zero]
    linear_combination -h
  · right
    intro hin
    apply h
    have := (Place.mem_restrict (K := F) (Q := β.toBase (k := k))).mp hin
    rw [map_inv₀, map_sub, map_pow] at this
    rw [show algebraMap F M (a : F) - algebraMap F M (a : F) ^ Q =
      -(algebraMap F M (a : F) ^ Q - algebraMap F M (a : F)) by ring, inv_neg] at this
    exact neg_mem_iff.mp this

/-- The fundamental inequality for the places of `M` (over `k'`) above a place `P'` of `F`:
`[k' : k] ∑ deg_{k'} β ≤ [M : F] deg P'`. -/
theorem finrank_mul_sum_deg_le (P' : Place k F) (S : Finset (Place k' M))
    (hS : ∀ β ∈ S, (β.toBase (k := k)).restrict (K := F) = P') :
    (Module.finrank k k' : ℤ) * ∑ β ∈ S, (β.deg : ℤ) ≤ Module.finrank F M * P'.deg := by
  classical
  obtain ⟨π, hπ⟩ := P'.exists_ord_eq_one
  set S' := S.map ⟨Place.toBase (k := k), Place.toBase_injective⟩
  have h := Place.sum_le_finrank_mul_deg (L := M) P' hπ S' (by
    intro Q hQ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_map.mp hQ
    exact hS β hβ)
  rw [Finset.sum_map] at h
  refine le_trans ?_ h
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun β hβ ↦ ?_
  have hπQ : ((β.toBase (k := k)).restrict (K := F)).ord π = 1 := by rw [hS β hβ]; exact hπ
  have hpos := (β.toBase (k := k)).ord_algebraMap_uniformizer_pos hπQ
  simp only [Function.Embedding.coeFn_mk]
  rw [Place.deg_toBase]
  push_cast
  have : (0 : ℤ) ≤ (Module.finrank k k' : ℤ) * β.deg := by positivity
  nlinarith

set_option maxHeartbeats 4000000 in
-- one long counting argument
/-- **The lower bound** (Nivedita, Theorem 3.10; Kedlaya, Lemma 5.1.9). -/
theorem pointCount_ge_of_galois (hkM : IsFullConstantField k' M)
    (x : F) [hxM : Fact (Transcendental k' (algebraMap F M x))]
    [IsGalois k'⟮algebraMap F M x⟯ M] [IsGalois F M]
    (α : Place k' M) (hα : α.deg = 1) (p : ℕ) [Fact p.Prime] [CharP k' p] :
    ∃ C : ℤ, ∀ m b : ℕ, Nat.card k' ^ m = p ^ (2 * b) →
      (genus k' M + 1) ^ 4 < (p : ℤ) ^ (2 * b) →
      (p : ℤ) ^ (2 * b) - ((Nat.card Gal(M/k'⟮algebraMap F M x⟯) : ℤ) - 1) *
          ((2 * genus k' M + 1) * p ^ b + 2) - C ≤
        pointCount k F (Module.finrank k k' * m) := by
  classical
  set xM := algebraMap F M x
  set G := Gal(M/k'⟮xM⟯)
  have : Fintype G := Fintype.ofFinite G
  set g := genus k' M
  have hg0 : 0 ≤ g := genus_nonneg hkM
  have hp := (Fact.out : p.Prime)
  obtain ⟨δ, hδ0, -, hδ⟩ := exists_ramification_bound (k := k') xM p
  set Dδ := (Place.finite_setOf_ord_pos (k := k') δ).toFinset
  set C : ℤ := ∑ β ∈ Dδ, β.ord δ * (β.deg : ℤ)
  refine ⟨C, fun m b hQ hgQ ↦ ?_⟩
  set Q := Nat.card k' ^ m with hQdef
  have hQZ : (Q : ℤ) = (p : ℤ) ^ (2 * b) := by rw [hQ]; push_cast; rfl
  -- `m ≥ 1`
  have hm : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hQdef, hm0, pow_zero] at hQ
    have h1 : (p : ℤ) ^ (2 * b) = 1 := by exact_mod_cast hQ.symm
    rw [h1] at hgQ
    have : (1 : ℤ) ≤ (g + 1) ^ 4 := one_le_pow₀ (by linarith)
    linarith
  have hk'1 : 1 < Nat.card k' := Finite.one_lt_card
  have hQ2 : 2 ≤ Q := by
    calc 2 ≤ Nat.card k' := hk'1
      _ = Nat.card k' ^ 1 := (pow_one _).symm
      _ ≤ Q := Nat.pow_le_pow_right (by omega) hm
  have hpQ : p ∣ Q := by
    have : Fintype k' := Fintype.ofFinite k'
    obtain ⟨n, -, hcard⟩ := FiniteField.card k' p
    have : p ∣ Nat.card k' := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self p n.ne_zero
    exact dvd_pow this (by omega)
  set z := xM ^ Q - xM with hz
  set Z := (Place.finite_setOf_ord_pos (k := k') z).toFinset
  have hmemZ : ∀ β, β ∈ Z ↔ 0 < β.ord z := fun β ↦ by simp [Z]
  have hZsum : ∑ β ∈ Z, β.ord z * (β.deg : ℤ) = Q * Module.finrank k'⟮xM⟯ M :=
    sum_ord_mul_deg_zeros_pow_sub hxM.out hQ2
  have hNG : (Module.finrank k'⟮xM⟯ M : ℤ) = Nat.card G := by
    rw [IsGalois.card_aut_eq_finrank]
  -- zeros of `z` contain `x`
  have hZx : ∀ β ∈ Z, xM ∈ β.1 := by
    intro β hβ
    by_contra hx
    have hneg : β.ord xM < 0 := (β.ord_neg_iff).mpr hx
    have := β.ord_pow_sub_of_neg hneg hQ2
    have hpos := (hmemZ β).mp hβ
    rw [this] at hpos
    have : (0 : ℤ) < Q := by omega
    nlinarith
  -- good and bad zeros
  set Good := Z.filter fun β ↦ β.ord z = 1
  set Bad := Z.filter fun β ↦ β.ord z ≠ 1
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun β ↦ β.ord z = 1)
    (fun β ↦ β.ord z * (β.deg : ℤ))
  have hGood : ∑ β ∈ Good, β.ord z * (β.deg : ℤ) = ∑ β ∈ Good, (β.deg : ℤ) :=
    Finset.sum_congr rfl fun β hβ ↦ by rw [(Finset.mem_filter.mp hβ).2, one_mul]
  have hBad : ∑ β ∈ Bad, β.ord z * (β.deg : ℤ) ≤ C := by
    calc ∑ β ∈ Bad, β.ord z * (β.deg : ℤ) ≤ ∑ β ∈ Bad, β.ord δ * (β.deg : ℤ) := by
          refine Finset.sum_le_sum fun β hβ ↦ ?_
          obtain ⟨hβZ, hne⟩ := Finset.mem_filter.mp hβ
          have hpos := (hmemZ β).mp hβZ
          have h2 : 2 ≤ β.ord z := by omega
          exact mul_le_mul_of_nonneg_right (hδ β (hZx β hβZ) Q hpQ h2) (by positivity)
      _ ≤ C := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro β hβ
            obtain ⟨hβZ, hne⟩ := Finset.mem_filter.mp hβ
            have hpos := (hmemZ β).mp hβZ
            have h2 : 2 ≤ β.ord z := by omega
            have : β.ord z ≤ β.ord δ := hδ β (hZx β hβZ) Q hpQ h2
            simp only [Dδ, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
            omega
          · intro β hβ _
            have : 0 < β.ord δ := by simpa [Dδ] using hβ
            positivity
  have hGoodsum : (Nat.card G : ℤ) * Q - C ≤ ∑ β ∈ Good, (β.deg : ℤ) := by
    rw [← hGood]
    rw [hNG] at hZsum
    have : ∑ β ∈ Z, β.ord z * (β.deg : ℤ) = ∑ β ∈ Good, β.ord z * (β.deg : ℤ) +
        ∑ β ∈ Bad, β.ord z * (β.deg : ℤ) := hsplit.symm
    linarith
  -- Frobenius elements
  have hfrob : ∀ β ∈ Z, ∃ σ : G, ∀ y ∈ β.1, y ^ Q - σ y ∈ β.1.nonunits := by
    intro β hβ
    have hzn : z ∈ β.1.nonunits := ((β.ord_pos_iff).mp ((hmemZ β).mp hβ)).2
    exact exists_frobenius_place (k := k') xM β (hZx β hβ) m hzn
  let φ : Place k' M → G := fun β ↦ if h : β ∈ Z then (hfrob β h).choose else 1
  have hφ : ∀ β ∈ Z, ∀ y ∈ β.1, y ^ Q - φ β y ∈ β.1.nonunits := by
    intro β hβ
    simp only [φ, dif_pos hβ]
    exact (hfrob β hβ).choose_spec
  let N : G → ℤ := fun σ ↦ ∑ β ∈ Good with φ β = σ, (β.deg : ℤ)
  have hsumN : ∑ σ, N σ = ∑ β ∈ Good, (β.deg : ℤ) := Finset.sum_fiberwise Good φ _
  -- Bombieri's bound for each `σ`
  set B' : ℤ := (2 * g + 1) * p ^ b + 2
  have hNle : ∀ σ : G, N σ ≤ Q + B' := by
    intro σ
    set τ : M ≃ₐ[k'] M := σ.restrictScalars k'
    set S := ((Good.filter fun β ↦ φ β = σ).erase α).erase (α.map τ)
    have hbomb := bombieri (k := k') (F := M) p b hkM hgQ α hα τ S
      (fun β hβ ↦ ⟨(Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hβ)),
        Finset.ne_of_mem_erase hβ⟩)
      (fun β hβ y hy _ ↦ by
        have hβ' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hβ)
        obtain ⟨hβG, hφβ⟩ := Finset.mem_filter.mp hβ'
        have hβZ := (Finset.mem_filter.mp hβG).1
        have := hφ β hβZ y hy
        rw [hφβ] at this
        rw [← show (Q : ℕ) = p ^ (2 * b) from hQ]
        exact β.eq_zero_or_ord_pos_of_mem_nonunits this)
    have h1 := Finset.sum_le_sum_erase_add (Good.filter fun β ↦ φ β = σ)
      (fun β ↦ (β.deg : ℤ)) (fun _ ↦ by positivity) α
    have h2 := Finset.sum_le_sum_erase_add ((Good.filter fun β ↦ φ β = σ).erase α)
      (fun β ↦ (β.deg : ℤ)) (fun _ ↦ by positivity) (α.map τ)
    have hατ : ((α.map τ).deg : ℤ) = 1 := by rw [Place.deg_map, hα]; rfl
    simp only [hα, hατ] at h1 h2
    change ∑ β ∈ Good with φ β = σ, (β.deg : ℤ) ≤ _
    rw [← hQZ] at hbomb
    simp only [B']
    push_cast at h1 h2 hbomb ⊢
    linarith
  -- lower bound for each `σ` fixing `F`
  have hNge : ∀ σ : G, (Q : ℤ) - C - ((Nat.card G : ℤ) - 1) * B' ≤ N σ := by
    intro σ
    have hrest : ∑ τ ∈ Finset.univ.erase σ, N τ ≤ ((Nat.card G : ℤ) - 1) * (Q + B') := by
      calc ∑ τ ∈ Finset.univ.erase σ, N τ ≤ ∑ τ ∈ Finset.univ.erase σ, ((Q : ℤ) + B') :=
            Finset.sum_le_sum fun τ _ ↦ hNle τ
        _ = ((Nat.card G : ℤ) - 1) * (Q + B') := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ σ),
              Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
            have : 1 ≤ Fintype.card G := Fintype.card_pos
            push_cast [Nat.cast_sub this]
            ring
    have := Finset.add_sum_erase Finset.univ N (Finset.mem_univ σ)
    rw [hsumN] at this
    nlinarith
  -- the automorphisms fixing `F`
  set Hs := fixF (k' := k') (M := M) x
  set Hf : Finset G := Finset.univ.filter (· ∈ Hs)
  have hHcard : Nat.card Hs = Hf.card := by
    have hset : ((Hf : Set G)) = Hs := by ext σ; simp [Hf]
    rw [← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have h1H : (1 : G) ∈ Hf := by
    simp only [Hf, Finset.mem_filter, Finset.mem_univ, true_and]
    intro f; rfl
  have hHpos : 0 < Hf.card := Finset.card_pos.mpr ⟨1, h1H⟩
  -- restriction to `F`
  set d := Module.finrank k k'
  have hd : 0 < d := Module.finrank_pos
  set r := d * m
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd.ne' (by omega))
  have hQr : Q = Nat.card k ^ r := by
    rw [hQdef, Module.natCard_eq_pow_finrank (K := k) (V := k'), ← pow_mul]
  set GH := Good.filter fun β ↦ φ β ∈ Hs
  have hsumH : ∑ σ ∈ Hf, N σ = ∑ β ∈ GH, (β.deg : ℤ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := GH) (t := Hf) (g := φ)
      (fun β hβ ↦ by simpa [Hf] using (Finset.mem_filter.mp hβ).2)]
    refine Finset.sum_congr rfl fun σ hσ ↦ ?_
    have hσH : σ ∈ Hs := by simpa [Hf] using hσ
    simp only [N, GH, Finset.filter_filter]
    congr 1
    ext β
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 ▸ hσH, h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  set res : Place k' M → Place k F := fun β ↦ (β.toBase (k := k)).restrict (K := F)
  set D := (finite_setOf_deg_le (k := k) (K := F) r).toFinset.filter fun P ↦ P.deg ∣ r
  have hres : ∀ β ∈ GH, res β ∈ D := by
    intro β hβ
    obtain ⟨hβG, hβH⟩ := Finset.mem_filter.mp hβ
    have hβZ := (Finset.mem_filter.mp hβG).1
    have hdvd := deg_restrict_dvd_of_frob (k := k) x β (φ β) hβH hQr (hφ β hβZ)
    simp only [D, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨Nat.le_of_dvd (by omega) hdvd, hdvd⟩
  have hDbound : (d : ℤ) * ∑ β ∈ GH, (β.deg : ℤ) ≤
      Module.finrank F M * (pointCount k F r : ℤ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hres, Finset.mul_sum,
      pointCount_eq_sum (k := k) (K := F) (n := r) hr1 le_rfl, ← Finset.sum_filter,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun P _ ↦
      finrank_mul_sum_deg_le P _ fun β hβ ↦ (Finset.mem_filter.mp hβ).2
  have hlow : (Hf.card : ℤ) * ((Q : ℤ) - C - ((Nat.card G : ℤ) - 1) * B') ≤ ∑ σ ∈ Hf, N σ := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum Hf N _ fun σ _ ↦ hNge σ
  have hMF : (Module.finrank F M : ℤ) ≤ d * Hf.card := by
    have := finrank_le_mul_card_fixF (k := k) (k' := k') (M := M) x
    rw [hHcard] at this
    exact_mod_cast this
  have hNr : (0 : ℤ) ≤ pointCount k F r := by positivity
  have hkey : (d : ℤ) * Hf.card * ((Q : ℤ) - C - ((Nat.card G : ℤ) - 1) * B') ≤
      (d : ℤ) * Hf.card * pointCount k F r := by
    calc (d : ℤ) * Hf.card * ((Q : ℤ) - C - ((Nat.card G : ℤ) - 1) * B')
        ≤ (d : ℤ) * ∑ σ ∈ Hf, N σ := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = (d : ℤ) * ∑ β ∈ GH, (β.deg : ℤ) := by rw [hsumH]
      _ ≤ Module.finrank F M * (pointCount k F r : ℤ) := hDbound
      _ ≤ (d : ℤ) * Hf.card * pointCount k F r := mul_le_mul_of_nonneg_right hMF hNr
  have hdh : (0 : ℤ) < (d : ℤ) * Hf.card := by positivity
  have := le_of_mul_le_mul_left hkey hdh
  rw [hQZ] at this
  simp only [B'] at this
  linarith

end Main

end WeilCurves.FunctionField
