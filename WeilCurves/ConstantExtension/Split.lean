/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.ConstantExtension.ExtPlaces
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Places of a constant field extension above a place of degree divisible by `r`

Let `K_r = K[X]/(f)` be the constant field extension of degree `r` and `P` a place of `K` with
`r ∣ deg P`. The degree-`r` extension `k_r` of `k` embeds into `κ(P)` in exactly `r` ways, giving
`r` distinct roots `β` of `f` in `κ(P)`. For each of them, `θ ↦ β` defines a surjection
`O_P[θ] → κ(P)` from the subring `O_P[θ] ≅ O_P[X]/(f)` of `K_r`; by Chevalley's extension theorem
(`LocalSubring.exists_le_valuationSubring`) its kernel is dominated by a valuation ring of `K_r`,
a place `Q_β` above `P`. Distinct roots give distinct places (`θ - b_β` is a nonunit at `Q_β`
and a unit at `Q_γ`). With the fundamental inequality there are exactly `r` places above `P`,
each of degree `deg P` (`WeilCurves.FunctionField.card_places_above`).
-/

namespace WeilCurves.FunctionField

/-! ### Chevalley's extension theorem in the form used here -/

section Chevalley

variable {L : Type*} [Field L]

/-- A prime ideal `𝔪` of a subring `R` of a field is dominated by a valuation subring `V`:
elements of `𝔪` are nonunits of `V`, elements of `R` outside `𝔪` are units of `V`. -/
theorem exists_valuationSubring_of_prime (R : Subring L) (𝔪 : Ideal R) [𝔪.IsPrime] :
    ∃ V : ValuationSubring L, R ≤ V.toSubring ∧
      (∀ x : R, x ∈ 𝔪 → ∀ hx : (x : L) ∈ V, ¬ IsUnit (⟨x, hx⟩ : V)) ∧
      (∀ x : R, x ∉ 𝔪 → ∀ hx : (x : L) ∈ V, IsUnit (⟨x, hx⟩ : V)) := by
  set B := LocalSubring.ofPrime R 𝔪
  obtain ⟨V, hBV⟩ := B.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hBV
  have hRB := LocalSubring.le_ofPrime R 𝔪
  refine ⟨V, hRB.trans hle, fun x hx hxV hu ↦ ?_, fun x hx hxV ↦ ?_⟩
  · -- `x` maps into the maximal ideal of `B`, so it is a nonunit of `B`, hence of `V`
    have hmax : algebraMap R B.toSubring x ∈ IsLocalRing.maximalIdeal B.toSubring :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff B.toSubring 𝔪 x).mpr hx
    apply hmax
    have hu' : IsUnit (Subring.inclusion hle (algebraMap R B.toSubring x)) := hu
    exact hloc.map_nonunit _ hu'
  · have hu : IsUnit (algebraMap R B.toSubring x) :=
      IsLocalization.map_units B.toSubring (⟨x, hx⟩ : 𝔪.primeCompl)
    exact hu.map (Subring.inclusion hle)

end Chevalley

/-! ### The subring `O_P[θ]` and its residue maps -/

open Polynomial

section Split

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
  [hk : Fact (IsFullConstantField k K)] (r : ℕ) [NeZero r]

/-- The generator `θ` of `K_r = K[X]/(f)`. -/
noncomputable abbrev theta : ConstExt k K r := AdjoinRoot.root _

variable (P : Place k K)

/-- `f` with coefficients in `O_P`. -/
noncomputable abbrev polyAt : P.1[X] := (basePoly k r).map P.baseHom

omit hk in
theorem polyAt_monic : (polyAt r P).Monic := (basePoly_monic r).map _

omit hk in
theorem polyAt_map : (polyAt r P).map (algebraMap P.1 K) = (basePoly k r).map (algebraMap k K) := by
  rw [Polynomial.map_map]; rfl

/-- `O_P[X]/(f) → K_r`, `X ↦ θ`. -/
noncomputable def lam : AdjoinRoot (polyAt r P) →+* ConstExt k K r :=
  AdjoinRoot.lift ((algebraMap K (ConstExt k K r)).comp (algebraMap P.1 K)) (theta r) (by
    rw [← Polynomial.eval₂_map, polyAt_map]
    exact AdjoinRoot.eval₂_root _)

theorem lam_mk (g : P.1[X]) :
    lam r P (AdjoinRoot.mk _ g) = AdjoinRoot.mk _ (g.map (algebraMap P.1 K)) := by
  rw [lam, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq,
    Polynomial.aeval_def]

theorem lam_injective : Function.Injective (lam r P) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    rw [lam_mk, AdjoinRoot.mk_eq_zero] at hx
    have hx' : (polyAt r P).map (algebraMap P.1 K) ∣ g.map (algebraMap P.1 K) := by
      rw [polyAt_map]; exact hx
    rw [AdjoinRoot.mk_eq_zero]
    exact (Polynomial.map_dvd_map _ (FaithfulSMul.algebraMap_injective P.1 K)
      (polyAt_monic r P)).mp hx'

/-- `O_P[θ] ≅ O_P[X]/(f)`. -/
noncomputable def lamEquiv : AdjoinRoot (polyAt r P) ≃+* (lam r P).range :=
  RingEquiv.ofBijective (lam r P).rangeRestrict
    ⟨fun _ _ h ↦ lam_injective r P (congrArg Subtype.val h), (lam r P).rangeRestrict_surjective⟩

@[simp]
theorem coe_lamEquiv (x : AdjoinRoot (polyAt r P)) :
    (lamEquiv r P x : ConstExt k K r) = lam r P x :=
  rfl

variable {r P} in
/-- For a root `β` of `f` in `κ(P)`: `O_P[X]/(f) → κ(P)`, `X ↦ β`. -/
noncomputable def resAt {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) :
    AdjoinRoot (polyAt r P) →+* P.ResidueField :=
  AdjoinRoot.lift P.residue β (by
    rw [Polynomial.eval₂_map]
    exact hβ)

omit hk in
variable {r P} in
theorem resAt_of {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) (a : P.1) :
    resAt hβ (AdjoinRoot.of _ a) = P.residue a := AdjoinRoot.lift_of _

omit hk in
variable {r P} in
theorem resAt_root {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) :
    resAt hβ (AdjoinRoot.root _) = β := AdjoinRoot.lift_root _

variable {r P} in
/-- The kernel of `O_P[θ] → κ(P)`, `θ ↦ β`, a prime ideal of the subring `O_P[θ]` of `K_r`. -/
noncomputable def kerAt {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) :
    Ideal (lam r P).range :=
  RingHom.ker ((resAt hβ).comp (lamEquiv r P).symm.toRingHom)

variable {r P} in
instance {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) : (kerAt hβ).IsPrime :=
  RingHom.ker_isPrime _

variable {r P} in
theorem mem_kerAt {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0)
    (x : AdjoinRoot (polyAt r P)) : lamEquiv r P x ∈ kerAt hβ ↔ resAt hβ x = 0 := by
  rw [kerAt, RingHom.mem_ker, RingHom.comp_apply]
  simp

variable [IsFunctionField k K]

variable {r P} in
/-- The place `Q_β` of `K_r` above `P` attached to a root `β` of `f` in `κ(P)`. -/
theorem exists_place_at {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) :
    ∃ Q : Place k (ConstExt k K r), (lam r P).range ≤ Q.1.toSubring ∧
      (∀ x : AdjoinRoot (polyAt r P), resAt hβ x = 0 →
        ∀ h : lam r P x ∈ Q.1, ¬ IsUnit (⟨lam r P x, h⟩ : Q.1)) ∧
      (∀ x : AdjoinRoot (polyAt r P), resAt hβ x ≠ 0 →
        ∀ h : lam r P x ∈ Q.1, IsUnit (⟨lam r P x, h⟩ : Q.1)) := by
  obtain ⟨V, hRV, hnon, hunit⟩ := exists_valuationSubring_of_prime (lam r P).range (kerAt hβ)
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have hπP : π ∈ P.1 := P.mem_of_ord_nonneg (by omega)
  have hres : P.residue ⟨π, hπP⟩ = 0 := by
    rw [P.residue_eq_zero_iff, ← P.ord_pos_iff_mem_maximalIdeal (a := ⟨π, hπP⟩) hπ0]
    simp [hπ]
  have hlamπ : lam r P (AdjoinRoot.of _ ⟨π, hπP⟩) = algebraMap K (ConstExt k K r) π := by
    rw [lam, AdjoinRoot.lift_of]; rfl
  have hVtop : V ≠ ⊤ := by
    intro htop
    have hmem : lam r P (AdjoinRoot.of _ ⟨π, hπP⟩) ∈ V := by rw [htop]; trivial
    apply hnon (lamEquiv r P (AdjoinRoot.of _ ⟨π, hπP⟩))
      ((mem_kerAt hβ _).mpr (by rw [resAt_of]; exact hres)) hmem
    have hne : lam r P (AdjoinRoot.of _ ⟨π, hπP⟩) ≠ 0 := by
      rw [hlamπ]; exact (_root_.map_ne_zero _).mpr hπ0
    have hinv : (lam r P (AdjoinRoot.of _ ⟨π, hπP⟩))⁻¹ ∈ V := by rw [htop]; trivial
    exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hne))
  have hk' : ∀ c : k, algebraMap k (ConstExt k K r) c ∈ V := fun c ↦ by
    apply hRV
    refine ⟨AdjoinRoot.of _ (P.baseHom c), ?_⟩
    rw [lam, AdjoinRoot.lift_of, IsScalarTower.algebraMap_apply k K (ConstExt k K r)]
    rfl
  exact ⟨⟨V, hVtop, hk'⟩, hRV, fun x hx h ↦ hnon (lamEquiv r P x) ((mem_kerAt hβ x).mpr hx) h,
    fun x hx h ↦ hunit (lamEquiv r P x) (fun hm ↦ hx ((mem_kerAt hβ x).mp hm)) h⟩

variable {r P} in
/-- The place `Q_β`. -/
noncomputable def placeAt {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) :
    Place k (ConstExt k K r) :=
  (exists_place_at hβ).choose

variable {r P} in
theorem range_le_placeAt {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) :
    (lam r P).range ≤ (placeAt hβ).1.toSubring :=
  (exists_place_at hβ).choose_spec.1

variable {r P} in
theorem lam_mem_placeAt {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0)
    (x : AdjoinRoot (polyAt r P)) : lam r P x ∈ (placeAt hβ).1 :=
  range_le_placeAt hβ ⟨x, rfl⟩

variable {r P} in
/-- `Q_β` lies above `P`. -/
theorem restrict_placeAt {β : P.ResidueField} (hβ : aeval β (basePoly k r) = 0) :
    (placeAt hβ).restrict (K := K) = P := by
  have hle : P.1 ≤ ((placeAt hβ).restrict (K := K)).1 := by
    intro a ha
    rw [Place.mem_restrict]
    have := lam_mem_placeAt hβ (AdjoinRoot.of _ ⟨a, ha⟩)
    rwa [lam, AdjoinRoot.lift_of] at this
  exact Place.ext (ValuationSubring.eq_of_le_of_ne_top P.1 hle
    ((placeAt hβ).restrict (K := K)).ne_top).symm

variable {r P} in
/-- Distinct roots give distinct places. -/
theorem placeAt_injective {β γ : P.ResidueField} (hβ : aeval β (basePoly k r) = 0)
    (hγ : aeval γ (basePoly k r) = 0) (h : placeAt hβ = placeAt hγ) : β = γ := by
  by_contra hne
  obtain ⟨b, hb⟩ := P.residue_surjective β
  set x : AdjoinRoot (polyAt r P) := AdjoinRoot.root _ - AdjoinRoot.of _ b
  have h1 : resAt hβ x = 0 := by
    simp only [x, map_sub, resAt_root, resAt_of, hb, sub_self]
  have h2 : resAt hγ x ≠ 0 := by
    simp only [x, map_sub, resAt_root, resAt_of, hb, sub_ne_zero]
    exact Ne.symm hne
  have hnon := (exists_place_at hβ).choose_spec.2.1 x h1 (lam_mem_placeAt hβ x)
  have hunit := (exists_place_at hγ).choose_spec.2.2 x h2 (lam_mem_placeAt hγ x)
  have key : ∀ (Q₁ Q₂ : Place k (ConstExt k K r)), Q₁ = Q₂ → ∀ (y : ConstExt k K r)
      (h₁ : y ∈ Q₁.1) (h₂ : y ∈ Q₂.1), IsUnit (⟨y, h₂⟩ : Q₂.1) → IsUnit (⟨y, h₁⟩ : Q₁.1) := by
    rintro Q₁ Q₂ rfl y h₁ h₂ hu; exact hu
  exact hnon (key _ _ h _ _ _ hunit)

omit [IsFunctionField k K] hk in
variable {r P} in
theorem aeval_embedding (σ : BaseExt k r →ₐ[k] P.ResidueField) :
    aeval (σ (basePB k r).gen) (basePoly k r) = 0 := by
  rw [basePoly, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

/-- Finite sets of places above `P` have at most `r` elements, and exactly `r` only if all have
degree `deg P`. -/
theorem card_le_of_restrict_eq (S : Finset (Place k (ConstExt k K r)))
    (hS : ∀ Q ∈ S, Q.restrict (K := K) = P) :
    S.card ≤ r ∧ (S.card = r → ∀ Q ∈ S, Q.deg = P.deg) := by
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hfund := P.sum_le_finrank_mul_deg (L := ConstExt k K r) hπ S hS
  rw [finrank_constExt] at hfund
  have hPdeg : (0 : ℤ) < P.deg := by exact_mod_cast P.deg_pos
  have hterm : ∀ Q ∈ S, (P.deg : ℤ) ≤ Q.ord (algebraMap K _ π) * (Q.deg : ℤ) := by
    intro Q hQ
    have hπQ : (Q.restrict (K := K)).ord π = 1 := by rw [hS Q hQ]; exact hπ
    have he := Q.ord_algebraMap_uniformizer_pos hπQ
    have hd : (P.deg : ℤ) ≤ Q.deg := by
      have := Q.deg_restrict_le (K := K); rw [hS Q hQ] at this; exact_mod_cast this
    nlinarith
  have hsum : (S.card : ℤ) * P.deg ≤ ∑ Q ∈ S, Q.ord (algebraMap K _ π) * (Q.deg : ℤ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hterm
  refine ⟨?_, fun hcard Q hQ ↦ ?_⟩
  · have : (S.card : ℤ) * P.deg ≤ r * P.deg := hsum.trans hfund
    exact_mod_cast le_of_mul_le_mul_right this hPdeg
  · have hzero : ∑ Q ∈ S, (Q.ord (algebraMap K _ π) * (Q.deg : ℤ) - P.deg) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
        linarith
      · exact Finset.sum_nonneg fun Q hQ ↦ sub_nonneg.mpr (hterm Q hQ)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun Q hQ ↦ sub_nonneg.mpr (hterm Q hQ)).mp
      hzero Q hQ
    have hπQ : (Q.restrict (K := K)).ord π = 1 := by rw [hS Q hQ]; exact hπ
    have he := Q.ord_algebraMap_uniformizer_pos hπQ
    have hd : (P.deg : ℤ) ≤ Q.deg := by
      have := Q.deg_restrict_le (K := K); rw [hS Q hQ] at this; exact_mod_cast this
    have : (Q.deg : ℤ) ≤ P.deg := by nlinarith
    exact_mod_cast le_antisymm this hd

/-- **Above a place `P` with `r ∣ deg P` there are exactly `r` places of `K_r`, each of degree
`deg P`.** -/
theorem places_above (hr : r ∣ P.deg) :
    {Q : Place k (ConstExt k K r) | Q.restrict (K := K) = P}.Finite ∧
      {Q : Place k (ConstExt k K r) | Q.restrict (K := K) = P}.ncard = r ∧
      ∀ Q : Place k (ConstExt k K r), Q.restrict (K := K) = P → Q.deg = P.deg := by
  classical
  set T := {Q : Place k (ConstExt k K r) | Q.restrict (K := K) = P}
  have hfin : T.Finite := by
    by_contra hinf
    obtain ⟨S, hST, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (r + 1)
    have := (card_le_of_restrict_eq r P S fun Q hQ ↦ hST hQ).1
    omega
  -- `r` distinct places from the `r` embeddings `k_r → κ(P)`
  have : Finite P.ResidueField := Module.finite_of_finite k
  have hemb : Nat.card (BaseExt k r →ₐ[k] P.ResidueField) = r := by
    rw [FiniteField.natCard_algHom_of_finrank_dvd, FiniteField.finrank_extension]
    rw [FiniteField.finrank_extension]; exact hr
  let ι : (BaseExt k r →ₐ[k] P.ResidueField) → T := fun σ ↦
    ⟨placeAt (aeval_embedding σ), restrict_placeAt _⟩
  have hι : Function.Injective ι := by
    intro σ τ h
    have := placeAt_injective (aeval_embedding σ) (aeval_embedding τ) (congrArg Subtype.val h)
    exact (basePB k r).algHom_ext this
  have : Finite T := hfin.to_subtype
  have hge : r ≤ T.ncard := by
    rw [← Nat.card_coe_set_eq]
    calc r = Nat.card (BaseExt k r →ₐ[k] P.ResidueField) := hemb.symm
      _ ≤ Nat.card T := Nat.card_le_card_of_injective ι hι
  have hle := card_le_of_restrict_eq r P hfin.toFinset (fun Q hQ ↦ hfin.mem_toFinset.mp hQ)
  rw [← Set.ncard_eq_toFinset_card T hfin] at hle
  have hcard : T.ncard = r := le_antisymm hle.1 hge
  refine ⟨hfin, hcard, fun Q hQ ↦ ?_⟩
  exact hle.2 hcard Q (hfin.mem_toFinset.mpr hQ)

end Split

end WeilCurves.FunctionField
