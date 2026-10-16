/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.ConstantExtension.Basic

/-!
# Places in a finite extension of function fields

Let `L / K` be a finite extension of function fields over a perfect field `k`.

* every place `Q` of `L` restricts to a place `Q|_K = Q ∩ K` of `K`
  (`WeilCurves.FunctionField.Place.restrict`): if `K ⊆ O_Q` then the integral extension `L` would
  lie in the integrally closed ring `O_Q`;
* `ord_Q x = e(Q) · ord_P x` for `x ∈ K`, `P = Q|_K`, with `e(Q) = ord_Q(π_P) ≥ 1`
  (`WeilCurves.FunctionField.Place.ord_algebraMap_eq`);
* `deg P ≤ deg Q`, since `κ(P)` embeds into `κ(Q)`
  (`WeilCurves.FunctionField.Place.deg_le_restrict`);
* `[L : k(x)] = [L : K] [K : k(x)]` (`WeilCurves.FunctionField.finrank_adjoin_algebraMap`).
* **the fundamental inequality** `∑_{Q ∈ S} e(Q) deg Q ≤ [L : K] deg P` for every finite set `S` of
  places of `L` above `P` (`WeilCurves.FunctionField.Place.sum_le_finrank_mul_deg`): take `x ∈ K`
  whose only zero is `P` and compare the degrees of the divisors of zeros of `x` in `K` and in `L`.
-/

namespace WeilCurves.FunctionField

open Divisor
open scoped IntermediateField

variable {k K L : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra K L] [Algebra k L]
  [IsScalarTower k K L]

namespace Place

/-- The restriction `Q ∩ K` of a place of `L` to `K`. -/
noncomputable def restrict [Algebra.IsIntegral K L] (Q : Place k L) : Place k K :=
  ⟨Q.1.comap (algebraMap K L), by
    intro htop
    apply Q.ne_top
    refine top_unique fun y _ ↦ ?_
    have hK : ∀ c : K, algebraMap K L c ∈ Q.1 := fun c ↦ by
      have : c ∈ Q.1.comap (algebraMap K L) := htop ▸ trivial
      exact ValuationSubring.mem_comap.mp this
    have : IsIntegrallyClosedIn Q.1.toSubring L := inferInstanceAs (IsIntegrallyClosedIn Q.1 L)
    have hle : (integralClosure K L).toSubring ≤ Q.1.toSubring := by
      rw [Subring.integralClosure_le_iff]
      intro c; exact hK c
    exact hle (Algebra.IsIntegral.isIntegral (R := K) y),
   fun c ↦ ValuationSubring.mem_comap.mpr (by
      rw [← IsScalarTower.algebraMap_apply]; exact Q.algebraMap_mem c)⟩

theorem mem_restrict [Algebra.IsIntegral K L] {Q : Place k L} {x : K} :
    x ∈ (Q.restrict (K := K)).1 ↔ algebraMap K L x ∈ Q.1 := ValuationSubring.mem_comap

variable [PerfectField k] [IsFunctionField k K] [IsFunctionField k L] [FiniteDimensional K L]

/-- `ord_Q x = ord_Q(π) · ord_P x` for `x ∈ K`, `P = Q|_K` and a uniformiser `π` of `P`. -/
theorem ord_algebraMap_eq (Q : Place k L) {π : K} (hπ : (Q.restrict (K := K)).ord π = 1)
    (x : K) : Q.ord (algebraMap K L x) =
      Q.ord (algebraMap K L π) * (Q.restrict (K := K)).ord x := by
  set P := Q.restrict (K := K)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  set n := P.ord x
  set u := x * π ^ (-n)
  have hu0 : u ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
  have hPu : P.ord u = 0 := by
    rw [P.ord_mul hx (zpow_ne_zero _ hπ0), ord_zpow, hπ]; ring
  obtain ⟨hu1, hu2⟩ := (P.ord_eq_zero_iff hu0).mp hPu
  have hQu : Q.ord (algebraMap K L u) = 0 := by
    refine (Q.ord_eq_zero_iff ((map_ne_zero _).mpr hu0)).mpr ⟨mem_restrict.mp hu1, ?_⟩
    rw [← map_inv₀]; exact mem_restrict.mp hu2
  have hxu : x = u * π ^ n := by
    simp only [u, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hxu, map_mul, map_zpow₀, Q.ord_mul ((map_ne_zero _).mpr hu0)
    (zpow_ne_zero _ ((map_ne_zero _).mpr hπ0)), hQu, ord_zpow]
  ring

theorem ord_algebraMap_uniformizer_pos (Q : Place k L) {π : K}
    (hπ : (Q.restrict (K := K)).ord π = 1) : 0 < Q.ord (algebraMap K L π) := by
  set P := Q.restrict (K := K)
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have h1 : π ∈ P.1 := P.mem_of_ord_nonneg (by omega)
  have h2 : π⁻¹ ∉ P.1 := by
    rw [← P.ord_neg_iff, ord_inv, hπ]; omega
  have h0 : (algebraMap K L π) ≠ 0 := (map_ne_zero _).mpr hπ0
  have hmem := mem_restrict.mp h1
  have hnn := Q.ord_nonneg_of_mem hmem
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    apply h2
    rw [mem_restrict, map_inv₀]
    exact ((Q.ord_eq_zero_iff h0).mp h.symm).2

/-- The inclusion `O_P → O_Q`. -/
noncomputable def incl (Q : Place k L) : (Q.restrict (K := K)).1 →+* Q.1 :=
  ((algebraMap K L).comp (Q.restrict (K := K)).1.subtype).codRestrict Q.1
    (fun x ↦ mem_restrict.mp x.2)

instance (Q : Place k L) : IsLocalHom (incl (K := K) Q) := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨⟨y, hy⟩, hxy⟩ := isUnit_iff_exists_inv.mp hx
  have hxy' : algebraMap K L (x : K) * y = 1 := congrArg Subtype.val hxy
  have hx0 : (x : K) ≠ 0 := by
    rintro h; rw [h, map_zero, zero_mul] at hxy'; exact zero_ne_one hxy'
  have hyeq : y = algebraMap K L (x : K)⁻¹ := by
    rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right hxy')
  have hinv : (x : K)⁻¹ ∈ (Q.restrict (K := K)).1 := mem_restrict.mpr (hyeq ▸ hy)
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  simp [hx0]

omit [IsFunctionField k K] in
/-- **`deg P ≤ deg Q`** for `P = Q|_K`. -/
theorem deg_restrict_le (Q : Place k L) : (Q.restrict (K := K)).deg ≤ Q.deg := by
  set P := Q.restrict (K := K)
  set g := IsLocalRing.ResidueField.map (incl (K := K) Q)
  let gl : P.ResidueField →ₗ[k] Q.ResidueField :=
    { toFun := g
      map_add' := map_add g
      map_smul' := fun c z ↦ by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
        erw [map_mul]
        congr 1
        rw [Place.algebraMap_residueField, Place.algebraMap_residueField]
        change IsLocalRing.ResidueField.map (incl Q) (IsLocalRing.residue _ _) = _
        rw [IsLocalRing.ResidueField.map_residue]
        congr 1
        apply Subtype.ext
        simp [incl, Place.coe_baseHom, ← IsScalarTower.algebraMap_apply] }
  exact LinearMap.finrank_le_finrank_of_injective (f := gl) g.injective

end Place

/-- The isomorphism `k(x) ≃ k(x)` between `k⟮x⟯ ⊆ K` and `k⟮x⟯ ⊆ L`. -/
noncomputable def adjoinMapEquiv (x : K) : k⟮x⟯ ≃ₐ[k] k⟮algebraMap K L x⟯ :=
  (IntermediateField.equivMap k⟮x⟯ (IsScalarTower.toAlgHom k K L)).trans
    (IntermediateField.equivOfEq (by rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl))

theorem coe_adjoinMapEquiv (x : K) (e : k⟮x⟯) :
    ((adjoinMapEquiv (L := L) x e : k⟮algebraMap K L x⟯) : L) = algebraMap K L e := rfl

/-- **`[L : k(x)] = [L : K] [K : k(x)]`**. -/
theorem finrank_adjoin_algebraMap [FiniteDimensional K L] (x : K) [FiniteDimensional k⟮x⟯ K] :
    Module.finrank k⟮algebraMap K L x⟯ L = Module.finrank K L * Module.finrank k⟮x⟯ K := by
  rw [mul_comm, Module.finrank_mul_finrank k⟮x⟯ K L]
  refine (Algebra.finrank_eq_of_equiv_equiv (adjoinMapEquiv (L := L) x).toRingEquiv
    (RingEquiv.refl L) ?_).symm
  ext e
  rfl

/-! ### The fundamental inequality -/

section ZerosOnlyAt

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k] [IsFunctionField k K]

/-- A transcendental element whose only zero is the place `P`. -/
theorem exists_zero_only_at (P : Place k K) :
    ∃ x : K, Transcendental k x ∧ 0 < P.ord x ∧ ∀ P' : Place k K, P' ≠ P → P'.ord x ≤ 0 := by
  set n : ℤ := |riemannConst k K| + ell (0 : Divisor k K) + 1
  have hP : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hn : 0 ≤ n := by positivity
  have hle : L (0 : Divisor k K) ≤ L (Finsupp.single P n) :=
    L_mono (Finsupp.single_nonneg.mpr hn)
  have hri := riemann_inequality (Finsupp.single P n)
  rw [deg_single] at hri
  have hlt : ell (0 : Divisor k K) < ell (Finsupp.single P n) := by
    have := le_abs_self (riemannConst k K)
    have : (ell (0 : Divisor k K) : ℤ) < ell (Finsupp.single P n) := by nlinarith
    exact_mod_cast this
  have hne : L (0 : Divisor k K) ≠ L (Finsupp.single P n) := by
    intro h; rw [ell, ell, h] at hlt; exact lt_irrefl _ hlt
  obtain ⟨y, hy, hy0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hyt : Transcendental k y := fun h ↦ hy0 (mem_L_zero.mpr h)
  have hyne : y ≠ 0 := ne_zero_of_transcendental hyt
  have hpole : ∀ P' : Place k K, P' ≠ P → 0 ≤ P'.ord y := by
    intro P' hP'
    have := ((mem_L_of_ne_zero hyne).mp hy) P'
    simpa [Finsupp.single_apply, Ne.symm hP', div_apply] using this
  obtain ⟨Q, hQ⟩ := Place.exists_ord_neg hyt
  have hQP : Q = P := by
    by_contra h; have := hpole Q h; omega
  refine ⟨y⁻¹, transcendental_inv hyt, ?_, fun P' hP' ↦ ?_⟩
  · rw [Place.ord_inv, ← hQP]; omega
  · rw [Place.ord_inv]; have := hpole P' hP'; omega

end ZerosOnlyAt

variable [PerfectField k] [IsFunctionField k K] [IsFunctionField k L] [FiniteDimensional K L]

omit [PerfectField k] [IsFunctionField k L] in
/-- For an effective divisor `D` and a finite set `S` of places, `∑_{Q ∈ S} D(Q) deg Q ≤ deg D`. -/
theorem sum_le_deg {D : Divisor k L} (hD : 0 ≤ D) (S : Finset (Place k L)) :
    ∑ Q ∈ S, D Q * (Q.deg : ℤ) ≤ D.deg := by
  classical
  have hle : ∑ Q ∈ S, Finsupp.single Q (D Q) ≤ D := by
    intro P
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hD P
  have := deg_mono hle
  rw [← degHom_apply, map_sum] at this
  simpa only [degHom_apply, deg_single] using this

/-- **The fundamental inequality**: for a finite set `S` of places of `L` above `P` and a
uniformiser `π` of `P`, `∑_{Q ∈ S} e(Q) deg Q ≤ [L : K] deg P`, `e(Q) = ord_Q π`. -/
theorem Place.sum_le_finrank_mul_deg (P : Place k K) {π : K} (hπ : P.ord π = 1)
    (S : Finset (Place k L)) (hS : ∀ Q ∈ S, Q.restrict (K := K) = P) :
    ∑ Q ∈ S, Q.ord (algebraMap K L π) * (Q.deg : ℤ) ≤ Module.finrank K L * P.deg := by
  classical
  obtain ⟨x, hx, hxP, hxo⟩ := exists_zero_only_at P
  set m := P.ord x
  have : FiniteDimensional k⟮x⟯ K := finiteDimensional_adjoin hx
  -- the divisor of zeros of `x` in `K` is `m P`
  have hzK : zeroDivisor k x = Finsupp.single P m := by
    ext P'
    rw [zeroDivisor_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · have := hxo P' (Ne.symm h); omega
  have hdegK := deg_zeroDivisor hx
  rw [hzK, deg_single] at hdegK
  -- in `L`
  have hxL : Transcendental k (algebraMap K L x) :=
    (transcendental_algebraMap_iff (algebraMap K L).injective).mpr hx
  have hdegL := deg_zeroDivisor (K := L) hxL
  rw [finrank_adjoin_algebraMap, Nat.cast_mul, ← hdegK] at hdegL
  have hsum := sum_le_deg (zeroDivisor_nonneg (k := k) (algebraMap K L x)) S
  rw [hdegL] at hsum
  have hterm : ∀ Q ∈ S, zeroDivisor k (algebraMap K L x) Q =
      Q.ord (algebraMap K L π) * m := by
    intro Q hQ
    rw [zeroDivisor_apply]
    have hπQ : (Q.restrict (K := K)).ord π = 1 := by rw [hS Q hQ]; exact hπ
    rw [Q.ord_algebraMap_eq hπQ x, hS Q hQ]
    have hpos := Q.ord_algebraMap_uniformizer_pos hπQ
    exact max_eq_right (mul_nonneg hpos.le hxP.le)
  rw [Finset.sum_congr rfl fun Q hQ ↦ by rw [hterm Q hQ]] at hsum
  have hm : 0 < m := hxP
  have : (∑ Q ∈ S, Q.ord (algebraMap K L π) * (Q.deg : ℤ)) * m ≤
      Module.finrank K L * P.deg * m := by
    rw [Finset.sum_mul]
    calc ∑ Q ∈ S, Q.ord (algebraMap K L π) * (Q.deg : ℤ) * m
        = ∑ Q ∈ S, Q.ord (algebraMap K L π) * m * (Q.deg : ℤ) :=
          Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ _ := hsum
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hm

end WeilCurves.FunctionField
