/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.ConstantExtension.OverKr
import WeilCurves.FiniteField.PlaceCount

/-!
# Places of `K_r` above a place `P` with `deg P ∣ r`

Let `P` be a place of `K` of degree `d ∣ r`, and `E` the extension of `κ(P)` of degree `r / d`
(a field with `q^r` elements). The `r` embeddings `k_r → E` give `r` distinct roots `β` of `f` in
`E`; each gives a place `Q_β` of `K_r` above `P` (Chevalley's theorem applied to the kernel of
`O_P[θ] → E`, `θ ↦ β`). If `Q_β = Q_γ` then `γ` is a root of the minimal polynomial of `β` over
`κ(P)`, which has at most `r / d` roots; hence there are at least `d` places above `P`
(`WeilCurves.FunctionField.le_card_places_above_of_dvd`).
-/

open Polynomial

namespace WeilCurves.FunctionField

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
  [hk : Fact (IsFullConstantField k K)] (r : ℕ) [NeZero r] (P : Place k K)

variable {r} in
/-- `O_P[X]/(f) → E`, `X ↦ β`, for a root `β` of `f` in an extension `E` of `κ(P)`. -/
noncomputable def resAtE {E : Type*} [Field E] [Algebra P.ResidueField E] [Algebra k E]
    [IsScalarTower k P.ResidueField E] {β : E}
    (hβ : aeval β (basePoly k r) = 0) : AdjoinRoot (polyAt r P) →+* E :=
  AdjoinRoot.lift ((algebraMap P.ResidueField E).comp P.residue) β (by
    rw [Polynomial.eval₂_map]
    have : ((algebraMap P.ResidueField E).comp P.residue).comp P.baseHom = algebraMap k E := by
      ext c
      rw [IsScalarTower.algebraMap_apply k P.ResidueField E]
      rfl
    rw [this, ← Polynomial.aeval_def]
    exact hβ)

section E

variable {r} {E : Type*} [Field E] [Algebra P.ResidueField E] [Algebra k E]
  [IsScalarTower k P.ResidueField E]

omit hk in
theorem resAtE_of {β : E} (hβ : aeval β (basePoly k r) = 0) (a : P.1) :
    resAtE P hβ (AdjoinRoot.of _ a) = algebraMap P.ResidueField E (P.residue a) :=
  AdjoinRoot.lift_of _

omit hk in
theorem resAtE_root {β : E} (hβ : aeval β (basePoly k r) = 0) :
    resAtE P hβ (AdjoinRoot.root _) = β := AdjoinRoot.lift_root _

omit hk in
theorem resAtE_mk {β : E} (hβ : aeval β (basePoly k r) = 0) (g : P.1[X]) :
    resAtE P hβ (AdjoinRoot.mk _ g) =
      (g.map P.residue).eval₂ (algebraMap P.ResidueField E) β := by
  rw [resAtE, AdjoinRoot.lift_mk, Polynomial.eval₂_map]

/-- The kernel of `O_P[θ] → E`, `θ ↦ β`. -/
noncomputable def kerAtE {β : E} (hβ : aeval β (basePoly k r) = 0) :
    Ideal (lam r P).range :=
  RingHom.ker ((resAtE P hβ).comp (lamEquiv r P).symm.toRingHom)

instance {β : E} (hβ : aeval β (basePoly k r) = 0) : (kerAtE P hβ).IsPrime :=
  RingHom.ker_isPrime _

theorem mem_kerAtE {β : E} (hβ : aeval β (basePoly k r) = 0)
    (x : AdjoinRoot (polyAt r P)) : lamEquiv r P x ∈ kerAtE P hβ ↔ resAtE P hβ x = 0 := by
  rw [kerAtE, RingHom.mem_ker, RingHom.comp_apply]
  simp

variable [IsFunctionField k K]

theorem exists_place_atE {β : E} (hβ : aeval β (basePoly k r) = 0) :
    ∃ Q : Place k (ConstExt k K r), (lam r P).range ≤ Q.1.toSubring ∧
      (∀ x : AdjoinRoot (polyAt r P), resAtE P hβ x = 0 →
        ∀ h : lam r P x ∈ Q.1, ¬ IsUnit (⟨lam r P x, h⟩ : Q.1)) ∧
      (∀ x : AdjoinRoot (polyAt r P), resAtE P hβ x ≠ 0 →
        ∀ h : lam r P x ∈ Q.1, IsUnit (⟨lam r P x, h⟩ : Q.1)) := by
  obtain ⟨V, hRV, hnon, hunit⟩ := exists_valuationSubring_of_prime (lam r P).range (kerAtE P hβ)
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
      ((mem_kerAtE P hβ _).mpr (by rw [resAtE_of, hres, map_zero])) hmem
    have hne : lam r P (AdjoinRoot.of _ ⟨π, hπP⟩) ≠ 0 := by
      rw [hlamπ]; exact (_root_.map_ne_zero _).mpr hπ0
    have hinv : (lam r P (AdjoinRoot.of _ ⟨π, hπP⟩))⁻¹ ∈ V := by rw [htop]; trivial
    exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hne))
  have hk' : ∀ c : k, algebraMap k (ConstExt k K r) c ∈ V := fun c ↦ by
    apply hRV
    refine ⟨AdjoinRoot.of _ (P.baseHom c), ?_⟩
    rw [lam, AdjoinRoot.lift_of, IsScalarTower.algebraMap_apply k K (ConstExt k K r)]
    rfl
  exact ⟨⟨V, hVtop, hk'⟩, hRV, fun x hx h ↦ hnon (lamEquiv r P x) ((mem_kerAtE P hβ x).mpr hx) h,
    fun x hx h ↦ hunit (lamEquiv r P x) (fun hm ↦ hx ((mem_kerAtE P hβ x).mp hm)) h⟩

/-- The place `Q_β` for a root `β ∈ E`. -/
noncomputable def placeAtE {β : E} (hβ : aeval β (basePoly k r) = 0) :
    Place k (ConstExt k K r) :=
  (exists_place_atE P hβ).choose

theorem lam_mem_placeAtE {β : E} (hβ : aeval β (basePoly k r) = 0)
    (x : AdjoinRoot (polyAt r P)) : lam r P x ∈ (placeAtE P hβ).1 :=
  (exists_place_atE P hβ).choose_spec.1 ⟨x, rfl⟩

theorem restrict_placeAtE {β : E} (hβ : aeval β (basePoly k r) = 0) :
    (placeAtE P hβ).restrict (K := K) = P := by
  have hle : P.1 ≤ ((placeAtE P hβ).restrict (K := K)).1 := by
    intro a ha
    rw [Place.mem_restrict]
    have := lam_mem_placeAtE P hβ (AdjoinRoot.of _ ⟨a, ha⟩)
    rwa [lam, AdjoinRoot.lift_of] at this
  exact Place.ext (ValuationSubring.eq_of_le_of_ne_top P.1 hle
    ((placeAtE P hβ).restrict (K := K)).ne_top).symm

/-- If `Q_β = Q_γ` then `γ` is a root of the minimal polynomial of `β` over `κ(P)`. -/
theorem aeval_minpoly_of_placeAtE_eq [FiniteDimensional P.ResidueField E] {β γ : E}
    (hβ : aeval β (basePoly k r) = 0) (hγ : aeval γ (basePoly k r) = 0)
    (h : placeAtE P hβ = placeAtE P hγ) : aeval γ (minpoly P.ResidueField β) = 0 := by
  obtain ⟨g, hg⟩ := Polynomial.map_surjective P.residue P.residue_surjective
    (minpoly P.ResidueField β)
  set x : AdjoinRoot (polyAt r P) := AdjoinRoot.mk _ g
  have h1 : resAtE P hβ x = 0 := by
    rw [resAtE_mk, hg, ← Polynomial.aeval_def, minpoly.aeval]
  by_contra h2
  have h2' : resAtE P hγ x ≠ 0 := by
    rw [resAtE_mk, hg, ← Polynomial.aeval_def]; exact h2
  have hnon := (exists_place_atE P hβ).choose_spec.2.1 x h1 (lam_mem_placeAtE P hβ x)
  have hunit := (exists_place_atE P hγ).choose_spec.2.2 x h2' (lam_mem_placeAtE P hγ x)
  have key : ∀ (Q₁ Q₂ : Place k (ConstExt k K r)), Q₁ = Q₂ → ∀ (y : ConstExt k K r)
      (h₁ : y ∈ Q₁.1) (h₂ : y ∈ Q₂.1), IsUnit (⟨y, h₂⟩ : Q₂.1) → IsUnit (⟨y, h₁⟩ : Q₁.1) := by
    rintro Q₁ Q₂ rfl y h₁ h₂ hu; exact hu
  exact hnon (key _ _ h _ _ _ hunit)

end E

/-! ### Counting -/

variable [IsFunctionField k K]

/-- Every place of `K_r` has degree `≥ r` over `k`: its residue field contains a root of `f`. -/
theorem le_deg_constExt (Q : Place k (ConstExt k K r)) : r ≤ Q.deg := by
  have hθ : theta (k := k) (K := K) r ∈ Q.1 :=
    Q.mem_of_isIntegral ⟨basePoly k r, basePoly_monic r, by
      rw [← Polynomial.aeval_def]; exact aeval_theta r⟩
  set θb := Q.residue ⟨_, hθ⟩
  have h1 : (((basePoly k r).eval₂ Q.baseHom ⟨_, hθ⟩ : Q.1) : ConstExt k K r) = 0 := by
    have := Polynomial.hom_eval₂ (basePoly k r) Q.baseHom Q.1.subtype ⟨_, hθ⟩
    simp only [ValuationSubring.subtype_apply] at this
    rw [this]
    have hc : Q.1.subtype.comp Q.baseHom = algebraMap k (ConstExt k K r) := by ext c; rfl
    rw [hc, ← Polynomial.aeval_def]
    exact aeval_theta r
  have hroot : aeval θb (minpoly k (basePB k r).gen) = 0 := by
    change aeval θb (basePoly k r) = 0
    rw [Polynomial.aeval_def]
    have : algebraMap k Q.ResidueField = Q.residue.comp Q.baseHom := rfl
    rw [this, ← Polynomial.hom_eval₂]
    have h0 : ((basePoly k r).eval₂ Q.baseHom ⟨_, hθ⟩ : Q.1) = 0 := Subtype.ext h1
    rw [h0, map_zero]
  set σ := (basePB k r).lift θb hroot
  have := LinearMap.finrank_le_finrank_of_injective (f := σ.toLinearMap) σ.injective
  rwa [FiniteField.finrank_extension] at this

omit hk in
theorem aeval_embeddingE {E : Type*} [CommRing E] [Algebra k E] (σ : BaseExt k r →ₐ[k] E) :
    aeval (σ (basePB k r).gen) (basePoly k r) = 0 := by
  rw [basePoly, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

theorem finite_places_above :
    {Q : Place k (ConstExt k K r) | Q.restrict (K := K) = P}.Finite := by
  by_contra hinf
  obtain ⟨S, hST, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (r + 1)
  have := (card_le_of_restrict_eq r P S fun Q hQ ↦ hST hQ).1
  omega

/-- **At least `deg P` places above `P` when `deg P ∣ r`.** -/
theorem le_ncard_places_above (hdr : P.deg ∣ r) :
    P.deg ≤ {Q : Place k (ConstExt k K r) | Q.restrict (K := K) = P}.ncard := by
  classical
  obtain ⟨m, hm⟩ := hdr
  have hm0 : m ≠ 0 := by rintro rfl; exact NeZero.ne r (by simpa using hm)
  have : NeZero m := ⟨hm0⟩
  have : Finite P.ResidueField := Module.finite_of_finite k
  let E := FiniteField.Extension P.ResidueField (ringChar P.ResidueField) m
  letI : Algebra k E :=
    ((algebraMap P.ResidueField E).comp (algebraMap k P.ResidueField)).toAlgebra
  have : IsScalarTower k P.ResidueField E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hfinE : Module.finrank P.ResidueField E = m := FiniteField.finrank_extension _ _ _
  have hfinkE : Module.finrank k E = r := by
    rw [← Module.finrank_mul_finrank k P.ResidueField E, hfinE, hm]; rfl
  have hemb : Nat.card (BaseExt k r →ₐ[k] E) = r := by
    rw [FiniteField.natCard_algHom_of_finrank_dvd, FiniteField.finrank_extension]
    rw [FiniteField.finrank_extension, hfinkE]
  have : Fintype (BaseExt k r →ₐ[k] E) := Fintype.ofFinite _
  let Φ : (BaseExt k r →ₐ[k] E) → Place k (ConstExt k K r) := fun σ ↦
    placeAtE P (aeval_embeddingE r σ)
  have hfib : ∀ Q ∈ (Finset.univ : Finset (BaseExt k r →ₐ[k] E)).image Φ,
      (Finset.univ.filter fun σ ↦ Φ σ = Q).card ≤ m := by
    intro Q hQ
    obtain ⟨σ₀, -, rfl⟩ := Finset.mem_image.mp hQ
    set mp := minpoly P.ResidueField (σ₀ (basePB k r).gen)
    set mpE := mp.map (algebraMap P.ResidueField E)
    have hmp0 : mpE ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap P.ResidueField E).injective).mpr
        (minpoly.ne_zero (Algebra.IsIntegral.isIntegral _))
    have hsub : (Finset.univ.filter fun σ ↦ Φ σ = Φ σ₀).image (fun σ ↦ σ (basePB k r).gen) ⊆
        mpE.roots.toFinset := by
      intro β hβ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hβ
      have hσ' := (Finset.mem_filter.mp hσ).2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hmp0, Polynomial.IsRoot, Polynomial.eval_map,
        ← Polynomial.aeval_def]
      exact aeval_minpoly_of_placeAtE_eq P (aeval_embeddingE r σ₀) (aeval_embeddingE r σ)
        hσ'.symm
    have hinj : Function.Injective (fun σ : BaseExt k r →ₐ[k] E ↦ σ (basePB k r).gen) :=
      fun σ τ h ↦ (basePB k r).algHom_ext h
    calc (Finset.univ.filter fun σ ↦ Φ σ = Φ σ₀).card
        = ((Finset.univ.filter fun σ ↦ Φ σ = Φ σ₀).image
            (fun σ ↦ σ (basePB k r).gen)).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ mpE.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card mpE.roots := Multiset.toFinset_card_le _
      _ ≤ mpE.natDegree := Polynomial.card_roots' _
      _ = mp.natDegree := Polynomial.natDegree_map _
      _ ≤ Module.finrank P.ResidueField E := minpoly.natDegree_le _
      _ = m := hfinE
  have hmain : r ≤ m * (Finset.univ.image Φ).card := by
    have := Finset.card_le_mul_card_image (Finset.univ : Finset (BaseExt k r →ₐ[k] E)) m hfib
    rwa [Finset.card_univ, Fintype.card_eq_nat_card, hemb] at this
  have hmain' : m * P.deg ≤ m * (Finset.univ.image Φ).card := by
    rw [mul_comm, ← hm]; exact hmain
  have himg : (Finset.univ.image Φ) ⊆ (finite_places_above r P).toFinset := by
    intro Q hQ
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hQ
    rw [Set.Finite.mem_toFinset]
    exact restrict_placeAtE P _
  have h2 := Finset.card_le_card himg
  rw [← Set.ncard_eq_toFinset_card _ (finite_places_above r P)] at h2
  have h3 : P.deg ≤ (Finset.univ.image Φ).card :=
    le_of_mul_le_mul_left hmain' (Nat.pos_of_ne_zero hm0)
  omega

/-- **Above a place `P` with `deg P ∣ r` there are exactly `deg P` places of `K_r`, each of degree
`r` over `k`.** -/
theorem places_above_of_dvd (hdr : P.deg ∣ r) :
    {Q : Place k (ConstExt k K r) | Q.restrict (K := K) = P}.ncard = P.deg ∧
      ∀ Q : Place k (ConstExt k K r), Q.restrict (K := K) = P → Q.deg = r := by
  classical
  set T := {Q : Place k (ConstExt k K r) | Q.restrict (K := K) = P}
  have hfin := finite_places_above r P
  set S := hfin.toFinset
  have hS : ∀ Q ∈ S, Q.restrict (K := K) = P := fun Q hQ ↦ hfin.mem_toFinset.mp hQ
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hfund := P.sum_le_finrank_mul_deg (L := ConstExt k K r) hπ S hS
  rw [finrank_constExt] at hfund
  have hr0 : (0 : ℤ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hterm : ∀ Q ∈ S, (r : ℤ) ≤ Q.ord (algebraMap K _ π) * (Q.deg : ℤ) := by
    intro Q hQ
    have hπQ : (Q.restrict (K := K)).ord π = 1 := by rw [hS Q hQ]; exact hπ
    have he := Q.ord_algebraMap_uniformizer_pos hπQ
    have hd : (r : ℤ) ≤ Q.deg := by exact_mod_cast le_deg_constExt r Q
    nlinarith
  have hsum : (S.card : ℤ) * r ≤ ∑ Q ∈ S, Q.ord (algebraMap K _ π) * (Q.deg : ℤ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hterm
  have hle : S.card ≤ P.deg := by
    have : (S.card : ℤ) * r ≤ P.deg * r := by
      calc (S.card : ℤ) * r ≤ _ := hsum
        _ ≤ _ := hfund
        _ = P.deg * r := by ring
    exact_mod_cast le_of_mul_le_mul_right this hr0
  have hge := le_ncard_places_above r P hdr
  rw [Set.ncard_eq_toFinset_card T hfin] at hge ⊢
  have hcard : S.card = P.deg := le_antisymm hle hge
  refine ⟨hcard, fun Q hQ ↦ ?_⟩
  have hQS : Q ∈ S := hfin.mem_toFinset.mpr hQ
  have hzero : ∑ Q ∈ S, (Q.ord (algebraMap K _ π) * (Q.deg : ℤ) - r) = 0 := by
    apply le_antisymm
    · rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
      linarith
    · exact Finset.sum_nonneg fun Q hQ ↦ sub_nonneg.mpr (hterm Q hQ)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun Q hQ ↦ sub_nonneg.mpr (hterm Q hQ)).mp
    hzero Q hQS
  have hπQ : (Q.restrict (K := K)).ord π = 1 := by rw [hQ]; exact hπ
  have he := Q.ord_algebraMap_uniformizer_pos hπQ
  have hd : (r : ℤ) ≤ Q.deg := by exact_mod_cast le_deg_constExt r Q
  have : (Q.deg : ℤ) ≤ r := by nlinarith
  exact_mod_cast le_antisymm this hd

/-- `deg (Q|_K) ∣ deg Q`. -/
theorem deg_restrict_dvd (Q : Place k (ConstExt k K r)) :
    (Q.restrict (K := K)).deg ∣ Q.deg := by
  have : Finite Q.ResidueField := Module.finite_of_finite k
  exact FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨Place.residueAlgHom (K := K) Q⟩

/-- **The number of places of `K_r` of degree `r` over `k` is `N_r = ∑_{d ∣ r} d B_d`.** -/
theorem ncard_deg_eq (r : ℕ) [NeZero r] :
    {Q : Place k (ConstExt k K r) | Q.deg = r}.ncard = pointCount k K r := by
  classical
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero (NeZero.ne r)
  set Sr := (finite_setOf_deg_le (k := k) (K := K) r).toFinset
  set D := Sr.filter fun P ↦ P.deg ∣ r
  have hset : {Q : Place k (ConstExt k K r) | Q.deg = r} =
      ↑(D.biUnion fun P ↦ (finite_places_above r P).toFinset) := by
    ext Q
    simp only [Set.mem_setOf_eq, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Set.Finite.mem_toFinset, D, Finset.mem_filter, Sr, exists_prop]
    constructor
    · intro hQ
      refine ⟨Q.restrict (K := K), ⟨?_, ?_⟩, rfl⟩
      · exact (Q.deg_restrict_le).trans hQ.le
      · exact (deg_restrict_dvd r Q).trans (dvd_of_eq hQ)
    · rintro ⟨P, ⟨_, hP⟩, hQP⟩
      exact (places_above_of_dvd r P hP).2 Q hQP
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · have := pointCount_eq_sum (k := k) (K := K) (n := r) hr1 le_rfl
    have h2 : (∑ P ∈ D, (finite_places_above r P).toFinset.card : ℤ) =
        ∑ P ∈ Sr, if P.deg ∣ r then (P.deg : ℤ) else 0 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr rfl fun P hP ↦ ?_
      have hdvd := (Finset.mem_filter.mp hP).2
      rw [← Set.ncard_eq_toFinset_card _ (finite_places_above r P),
        (places_above_of_dvd r P hdvd).1]
    exact_mod_cast h2.trans this.symm
  · intro P _ P' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro Q hQ hQ'
    rw [Set.Finite.mem_toFinset] at hQ hQ'
    exact hne (hQ.symm.trans hQ')

/-- **`N_r` is the number of places of degree one of `K_r` over `k_r`.** -/
theorem ncard_deg_one_kr (r : ℕ) [NeZero r] :
    {Q : Place (BaseExt k r) (ConstExt k K r) | Q.deg = 1}.ncard = pointCount k K r := by
  rw [← ncard_deg_eq (k := k) (K := K) r]
  refine Set.ncard_congr (fun Q _ ↦ Place.ofKr r Q) ?_ ?_ ?_
  · intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ ⊢
    rw [deg_eq_mul_deg_toKr]
    change r * Q.deg = r
    rw [hQ, mul_one]
  · intro Q Q' _ _ h
    exact (placeKrEquiv (K := K) r).symm.injective h
  · intro Q hQ
    refine ⟨Place.toKr r Q, ?_, rfl⟩
    simp only [Set.mem_setOf_eq] at hQ ⊢
    rw [deg_eq_mul_deg_toKr] at hQ
    have hr := Nat.pos_of_ne_zero (NeZero.ne r)
    have : r * (Q.toKr r).deg = r * 1 := by rw [hQ, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hr this

end WeilCurves.FunctionField
