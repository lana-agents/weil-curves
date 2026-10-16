/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.ConstantExtension.Split2
import Mathlib.FieldTheory.LinearDisjoint

/-!
# The genus does not grow in a constant field extension

For the constant field extension `K_r / K` (a function field over `k_r`) we show
`riemannConst k_r K_r ≤ riemannConst k K`, i.e. `g(K_r) ≤ g(K)`
(`WeilCurves.FunctionField.riemannConst_constExt_le`). Given a divisor `A'` of `K_r`, take
`A = ∑_{Q ∈ supp A'} max(0, A'(Q)) · Q|_K` and `B' = ∑_{Q | P} e(Q) A(P) Q ≥ A'`. Then:

* `deg_{k_r} B' ≤ deg A` by the fundamental inequality `∑_{Q | P} e(Q) deg_{k_r} Q ≤ deg P`;
* `ℓ_{k_r}(B') ≥ ℓ_k(A)`: a `k`-basis of `L(A)` stays `k_r`-linearly independent in `K_r`
  (`k_r` and `K` are linearly disjoint inside `K_r = K ⊗_k k_r`), and lies in `L(B')`;

so `deg A' - ℓ(A') ≤ deg B' - ℓ(B') ≤ deg A - ℓ(A) ≤ riemannConst k K`.
-/

open Polynomial

namespace WeilCurves.FunctionField

open Divisor

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]
  [hk : Fact (IsFullConstantField k K)] (r : ℕ) [NeZero r]

omit [IsFunctionField k K] in
theorem minpoly_theta :
    minpoly K (theta (k := k) (K := K) r) = (basePoly k r).map (algebraMap k K) :=
  (minpoly.eq_of_irreducible_of_monic (fact_irreducible_basePoly (K := K) r).out
    (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) ((basePoly_monic r).map _)).symm

omit [IsFunctionField k K] in
/-- **`k_r` and `K` are linearly disjoint in `K_r`**: a `k`-linearly independent family of `K`
stays `k_r`-linearly independent in `K_r`. -/
theorem linearIndependent_constExt {ι : Type*} {b : ι → K} (hb : LinearIndependent k b) :
    LinearIndependent (BaseExt k r) (fun i ↦ algebraMap K (ConstExt k K r) (b i)) := by
  set A : IntermediateField k (ConstExt k K r) := (baseLift (K := K) r).fieldRange
  let e : BaseExt k r ≃ₐ[k] A := AlgEquiv.ofInjectiveField (baseLift (K := K) r)
  let bA : Module.Basis (Fin (basePB k r).dim) k A := (basePB k r).basis.map e.toLinearEquiv
  have hdim : (basePB k r).dim = (minpoly K (theta (k := k) (K := K) r)).natDegree := by
    rw [minpoly_theta, Polynomial.natDegree_map, ← PowerBasis.natDegree_minpoly]; rfl
  have hval : ∀ j, A.val (bA j) = theta (k := k) (K := K) r ^ (j : ℕ) := by
    intro j
    simp only [bA, Module.Basis.map_apply, PowerBasis.coe_basis, AlgEquiv.toLinearEquiv_apply,
      map_pow]
    change baseLift r ((basePB k r).gen) ^ (j : ℕ) = _
    rw [baseLift_gen]
  have hli : LinearIndependent K (A.val ∘ bA) := by
    have := linearIndependent_pow (K := K) (theta (k := k) (K := K) r)
    have h2 := this.comp (Fin.cast hdim) (Fin.cast_injective hdim)
    convert h2 using 1
    ext j
    exact hval j
  have hdisj : A.LinearDisjoint K := IntermediateField.LinearDisjoint.of_basis_left bA hli
  have hA := hdisj.linearIndependent_right' hb
  rw [linearIndependent_iff'] at hA ⊢
  intro s g hg i hi
  have := hA s (fun i ↦ e (g i)) (by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rfl) i hi
  exact e.injective (this.trans (map_zero e).symm)

/-! ### Places of `K_r` over `k_r` lying over places of `K` -/

/-- The place of `K` below a place of `K_r` (over `k_r`). -/
noncomputable def Place.res (Q : Place (BaseExt k r) (ConstExt k K r)) : Place k K :=
  (Place.ofKr r Q).restrict (K := K)

/-- A uniformiser at `P`. -/
noncomputable def unif (P : Place k K) : K := P.exists_ord_eq_one.choose

omit hk in
theorem ord_unif (P : Place k K) : P.ord (unif P) = 1 := P.exists_ord_eq_one.choose_spec

/-- The ramification index `e(Q) = ord_Q(π_P)`. -/
noncomputable def ramIdx (Q : Place (BaseExt k r) (ConstExt k K r)) : ℤ :=
  Q.ord (algebraMap K (ConstExt k K r) (unif (Q.res r)))

theorem ramIdx_pos (Q : Place (BaseExt k r) (ConstExt k K r)) : 0 < ramIdx r Q :=
  (Place.ofKr r Q).ord_algebraMap_uniformizer_pos (ord_unif _)

theorem ord_algebraMap_res (Q : Place (BaseExt k r) (ConstExt k K r)) (x : K) :
    Q.ord (algebraMap K (ConstExt k K r) x) = ramIdx r Q * (Q.res r).ord x :=
  (Place.ofKr r Q).ord_algebraMap_eq (ord_unif _) x

/-- **`ℓ(A) ≤ ℓ(B')`** when `B'(Q) ≥ e(Q) A(Q|_K)` for all `Q`. -/
theorem ell_le_of (A : Divisor k K) (B' : Divisor (BaseExt k r) (ConstExt k K r))
    (h : ∀ Q, ramIdx r Q * A (Q.res r) ≤ B' Q) : ell A ≤ ell B' := by
  set b := Module.finBasis k (L A)
  have hb : LinearIndependent k (fun i ↦ (b i : K)) :=
    b.linearIndependent.map' (L A).subtype (Submodule.ker_subtype _)
  have hli := linearIndependent_constExt r hb
  have hmem : ∀ i, algebraMap K (ConstExt k K r) (b i : K) ∈ L B' := by
    intro i
    rcases (mem_L.mp (b i).2) with h0 | hP
    · rw [h0, map_zero]; exact zero_mem _
    · refine mem_L.mpr (Or.inr fun Q ↦ ?_)
      rw [ord_algebraMap_res]
      have h1 := hP (Q.res r)
      have h2 := h Q
      have he := ramIdx_pos r Q
      nlinarith
  let w : Fin (Module.finrank k (L A)) → L B' := fun i ↦ ⟨_, hmem i⟩
  have hw : LinearIndependent (BaseExt k r) w := LinearIndependent.of_comp (L B').subtype hli
  have := hw.fintype_card_le_finrank
  rwa [Fintype.card_fin] at this

theorem finite_res_eq (P : Place k K) :
    {Q : Place (BaseExt k r) (ConstExt k K r) | Q.res r = P}.Finite := by
  have := (finite_places_above r P).image (Place.toKr r)
  refine this.subset fun Q hQ ↦ ⟨Place.ofKr r Q, hQ, rfl⟩

/-- `∑_{Q | P} e(Q) deg_{k_r} Q ≤ deg P`. -/
theorem sum_ramIdx_deg_le (P : Place k K) :
    ∑ Q ∈ (finite_res_eq r P).toFinset, ramIdx r Q * (Q.deg : ℤ) ≤ P.deg := by
  classical
  set S := (finite_res_eq r P).toFinset
  have hfund := P.sum_le_finrank_mul_deg (L := ConstExt k K r) (ord_unif P)
    (S.image (Place.ofKr r)) (by
      intro Q hQ
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      exact (finite_res_eq r P).mem_toFinset.mp hQ')
  have hinj : Set.InjOn (Place.ofKr (k := k) (K := K) r) (S : Set _) :=
    fun _ _ _ _ h ↦ (placeKrEquiv (K := K) r).symm.injective h
  rw [finrank_constExt, Finset.sum_image hinj] at hfund
  have hr : (0 : ℤ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have : (r : ℤ) * ∑ Q ∈ S, ramIdx r Q * (Q.deg : ℤ) ≤ r * P.deg := by
    rw [Finset.mul_sum]
    convert hfund using 2 with Q hQ
    have hres : (Place.ofKr r Q).restrict (K := K) = P := (finite_res_eq r P).mem_toFinset.mp hQ
    have := deg_eq_mul_deg_toKr r (Place.ofKr r Q)
    rw [this]
    simp only [ramIdx, Place.res, hres]
    push_cast
    rw [show Place.toKr r (Place.ofKr r Q) = Q from rfl,
      show (Place.ofKr r Q).ord = Q.ord from rfl]
    ring
  exact le_of_mul_le_mul_left this hr

/-! ### The genus bound -/

/-- The divisor `B' = ∑_{P ∈ supp A} ∑_{Q | P} e(Q) A(P) Q`. -/
noncomputable def conorm (A : Divisor k K) : Divisor (BaseExt k r) (ConstExt k K r) :=
  ∑ P ∈ A.support, ∑ Q ∈ (finite_res_eq r P).toFinset, Finsupp.single Q (ramIdx r Q * A P)

theorem conorm_apply (A : Divisor k K) (Q : Place (BaseExt k r) (ConstExt k K r)) :
    conorm r A Q = ramIdx r Q * A (Q.res r) := by
  classical
  simp only [conorm, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single (Q.res r)]
  · rw [Finset.sum_eq_single Q]
    · simp
    · intro Q' _ hne; rw [if_neg hne]
    · intro h; exact absurd ((finite_res_eq r _).mem_toFinset.mpr rfl) h
  · intro P _ hne
    refine Finset.sum_eq_zero fun Q' hQ' ↦ ?_
    rw [if_neg]
    rintro rfl
    exact hne ((finite_res_eq r P).mem_toFinset.mp hQ').symm
  · intro h
    rw [Finsupp.notMem_support_iff.mp h]
    simp

theorem deg_conorm_le {A : Divisor k K} (hA : 0 ≤ A) : (conorm r A).deg ≤ A.deg := by
  classical
  rw [conorm, ← degHom_apply, map_sum]
  rw [deg_eq_sum_of_support_subset A (s := A.support) subset_rfl]
  refine Finset.sum_le_sum fun P _ ↦ ?_
  rw [map_sum]
  simp only [degHom_apply, deg_single]
  calc ∑ Q ∈ (finite_res_eq r P).toFinset, ramIdx r Q * A P * (Q.deg : ℤ)
      = A P * ∑ Q ∈ (finite_res_eq r P).toFinset, ramIdx r Q * (Q.deg : ℤ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ A P * P.deg := mul_le_mul_of_nonneg_left (sum_ramIdx_deg_le r P) (hA P)

/-- **The genus does not grow**: `riemannConst k_r K_r ≤ riemannConst k K`. -/
theorem riemannConst_constExt_le :
    riemannConst (BaseExt k r) (ConstExt k K r) ≤ riemannConst k K := by
  classical
  obtain ⟨A', hA'⟩ := exists_deg_sub_ell_eq_riemannConst (k := BaseExt k r)
    (K := ConstExt k K r)
  set A : Divisor k K := ∑ Q ∈ A'.support, Finsupp.single (Q.res r) (max 0 (A' Q))
  have hAapp : ∀ P, A P = ∑ Q ∈ A'.support, if Q.res r = P then max 0 (A' Q) else 0 := by
    intro P
    simp only [A, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hA0 : 0 ≤ A := fun P ↦ by
    rw [hAapp]
    exact Finset.sum_nonneg fun Q _ ↦ by split_ifs <;> simp
  have hle : A' ≤ conorm r A := by
    intro Q
    rw [conorm_apply]
    have he := ramIdx_pos r Q
    have hAQ : max 0 (A' Q) ≤ A (Q.res r) := by
      by_cases hQ : Q ∈ A'.support
      · rw [hAapp]
        have := Finset.single_le_sum (f := fun Q' ↦ if Q'.res r = Q.res r then max 0 (A' Q')
          else 0) (fun Q' _ ↦ by split_ifs <;> simp) hQ
        simpa using this
      · rw [Finsupp.notMem_support_iff.mp hQ, max_self]; exact hA0 _
    have h0 : 0 ≤ A (Q.res r) := hA0 _
    have := le_max_right 0 (A' Q)
    nlinarith
  have h1 := deg_sub_ell_mono hle
  have h2 := deg_conorm_le r hA0
  have h3 : ell A ≤ ell (conorm r A) := ell_le_of r A (conorm r A) fun Q ↦ (conorm_apply r A Q).ge
  have h4 := deg_sub_ell_le_riemannConst (k := k) (K := K) A
  omega

/-- `g(K_r) ≤ g(K)`. -/
theorem genus_constExt_le : genus (BaseExt k r) (ConstExt k K r) ≤ genus k K := by
  simp only [genus]
  have := riemannConst_constExt_le (k := k) (K := K) r
  omega

end WeilCurves.FunctionField
