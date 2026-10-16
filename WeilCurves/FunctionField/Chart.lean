/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Affine charts of a function field

For `t` in a function field `K / k` transcendental over `k`, the *chart ring* `A_t` is the
integral closure of `k[t] = Algebra.adjoin k {t}` in `K`. It is the coordinate ring of the affine
open `{t ≠ ∞}` of the regular proper model of the curve.

Over a perfect field `k` the chart ring is a Dedekind domain, finite over `k[t]`, for **every**
transcendental `t` — also when `K / k(t)` is inseparable, where Mathlib's
`IsIntegralClosure.isDedekindDomain` does not apply. The proof
(`WeilCurves.FunctionField.finite_chartRing`): let `S` be the separable closure of `k(t)` in
`K`, and `q = p^e` the exponent of the purely inseparable extension `K / S`. Then `x ↦ x^q` maps
`A_t` into the integral closure of `k[t]` in `S`, which is finite over `k[t]` (separable case),
hence over `k[t^q]`; and since `k` is perfect, `k[t^q]` is exactly the image of `k[t]` under
`x ↦ x^q`. Transporting back along the injective ring map `x ↦ x^q` shows that `A_t` is finite
over `k[t]`.

Generalises `Belyi/CurveField/Chart.lean` (base field `ℚ`) of the `belyi` repository.

## Main definitions and results

* `WeilCurves.FunctionField.chartRing k t`: the integral closure of `k[t]` in `K`.
* `WeilCurves.FunctionField.finite_chartRing`: `A_t` is finite over `k[t]` (`k` perfect).
* instances `IsDedekindDomain (chartRing k t)`, `IsFractionRing (chartRing k t) K`,
  `Module.Finite (Algebra.adjoin k {t}) (chartRing k t)`, `Algebra.FiniteType k (chartRing k t)`.
* `WeilCurves.FunctionField.chartRing_le`: `A_t` is contained in every integrally closed subring
  containing `k` and `t` (e.g. valuation subrings).
* `WeilCurves.FunctionField.inv_notMem_chartRing`: `t⁻¹ ∉ A_t`, i.e. `t` is not a unit of `A_t`.
-/

open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace WeilCurves.FunctionField

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K]

/-- The chart ring `A_t`: the integral closure of `k[t]` in `K`. -/
abbrev chartRing (t : K) : Subalgebra (Algebra.adjoin k {t}) K :=
  integralClosure (Algebra.adjoin k {t}) K

variable {k} {t : K}

theorem mem_chartRing_of_mem_adjoin {x : K} (hx : x ∈ Algebra.adjoin k {t}) :
    x ∈ chartRing k t :=
  (chartRing k t).algebraMap_mem ⟨x, hx⟩

variable (k t) in
theorem self_mem_chartRing : t ∈ chartRing k t :=
  mem_chartRing_of_mem_adjoin (Algebra.self_mem_adjoin_singleton k t)

variable (t) in
theorem algebraMap_mem_chartRing (c : k) : algebraMap k K c ∈ chartRing k t :=
  mem_chartRing_of_mem_adjoin (Subalgebra.algebraMap_mem _ c)

/-- The chart ring is contained in every integrally closed subring containing `k` and `t`. -/
theorem chartRing_le {S : Subring K} [IsIntegrallyClosedIn S K]
    (hq : ∀ c : k, algebraMap k K c ∈ S) (ht : t ∈ S) : (chartRing k t).toSubring ≤ S := by
  rw [Subring.integralClosure_le_iff]
  rintro ⟨r, hr⟩
  change r ∈ S
  induction hr using Algebra.adjoin_induction with
  | mem x hx => obtain rfl := Set.mem_singleton_iff.mp hx; exact ht
  | algebraMap q => exact hq q
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | mul x y _ _ hx hy => exact S.mul_mem hx hy

/-- The chart ring is contained in every valuation subring containing `k` and `t`. -/
theorem mem_of_mem_chartRing (V : ValuationSubring K) (hq : ∀ c : k, algebraMap k K c ∈ V)
    (ht : t ∈ V) {x : K} (hx : x ∈ chartRing k t) : x ∈ V := by
  have : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  exact chartRing_le (S := V.toSubring) hq ht hx

theorem isPrincipalIdealRing_adjoin (ht : Transcendental k t) :
    IsPrincipalIdealRing (Algebra.adjoin k {t}) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k t ht).toRingHom
    (Polynomial.algEquivOfTranscendental k t ht).surjective

theorem isDedekindDomain_adjoin (ht : Transcendental k t) :
    IsDedekindDomain (Algebra.adjoin k {t}) := by
  have := isPrincipalIdealRing_adjoin ht
  infer_instance

instance [Fact (Transcendental k t)] : IsDedekindDomain (Algebra.adjoin k {t}) :=
  isDedekindDomain_adjoin Fact.out

/-- The element `t` is not a unit of the chart ring `A_t`. -/
theorem inv_notMem_chartRing (ht : Transcendental k t) : t⁻¹ ∉ chartRing k t := by
  have := isDedekindDomain_adjoin ht
  intro h
  have ht0 : t ≠ 0 := ne_zero_of_transcendental ht
  let y : k⟮t⟯ := ⟨t⁻¹, inv_mem (IntermediateField.mem_adjoin_simple_self k t)⟩
  have hy : IsIntegral (Algebra.adjoin k {t}) y := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin k {t}) k⟮t⟯ K)
      (algebraMap k⟮t⟯ K).injective]
    exact h
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  have hr' : (r : K) = t⁻¹ := congrArg Subtype.val hr
  obtain ⟨p, hp⟩ : ∃ p : k[X], aeval t p = r := by
    have : (r : K) ∈ (aeval (R := k) t).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact r.2
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp⟩
  apply ht
  refine ⟨X * p - 1, fun h0 ↦ ?_, ?_⟩
  · have := congrArg (Polynomial.coeff · 0) h0
    simp at this
  · simp [hp, hr', ht0]

/-! ### Finiteness of the chart ring over a perfect field -/

section Finite

variable (q : ℕ) (t)

/-- `k[t]` is spanned over `k[t^q]` by `1, t, …, t^{q-1}`. -/
theorem mem_span_pow_of_mem_adjoin (hq : 0 < q) {r : K} (hr : r ∈ Algebra.adjoin k {t}) :
    r ∈ Submodule.span (Algebra.adjoin k {t ^ q})
      (Set.range fun i : Fin q ↦ t ^ (i : ℕ)) := by
  set N := Submodule.span (Algebra.adjoin k {t ^ q}) (Set.range fun i : Fin q ↦ t ^ (i : ℕ))
  have hpow : ∀ n : ℕ, t ^ n ∈ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < q
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      · have h1 := ih (n - q) (by omega)
        have h2 : t ^ n = (⟨t ^ q, Algebra.self_mem_adjoin_singleton k _⟩ :
            Algebra.adjoin k {t ^ q}) • t ^ (n - q) := by
          rw [Subalgebra.smul_def, smul_eq_mul, ← pow_add]
          congr 1; omega
        rw [h2]
        exact N.smul_mem _ h1
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
  obtain ⟨P, rfl⟩ := hr
  change aeval t P ∈ N
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun n _ ↦ ?_
  have : P.coeff n • t ^ n = (algebraMap k (Algebra.adjoin k {t ^ q}) (P.coeff n)) • t ^ n := by
    rw [algebraMap_smul]
  rw [this]
  exact N.smul_mem _ (hpow n)

/-- Over a perfect field, every element of `k[t^{p^e}]` is a `p^e`-th power of an element of
`k[t]`. -/
theorem exists_pow_eq_of_mem_adjoin (p e : ℕ) [ExpChar k p] [PerfectField k] {y : K}
    (hy : y ∈ Algebra.adjoin k {t ^ p ^ e}) :
    ∃ r ∈ Algebra.adjoin k {t}, r ^ p ^ e = y := by
  have : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨t, Algebra.self_mem_adjoin_singleton k t, rfl⟩
  | algebraMap c =>
    refine ⟨algebraMap k K ((iterateFrobeniusEquiv k p e).symm c),
      Subalgebra.algebraMap_mem _ _, ?_⟩
    rw [← map_pow, ← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, add_mem hr hs, add_pow_expChar_pow r s p e⟩
  | mul x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r * s, mul_mem hr hs, mul_pow r s _⟩

variable {t}

/-- **The chart ring is finite over `k[t]`**, for every transcendental `t`, when `k` is perfect
(no separability hypothesis on `K / k(t)`). -/
theorem finite_chartRing [PerfectField k] (ht : Transcendental k t) [FiniteDimensional k⟮t⟯ K] :
    Module.Finite (Algebra.adjoin k {t}) (chartRing k t) := by
  classical
  set R := Algebra.adjoin k {t}
  set F := k⟮t⟯
  set S := separableClosure F K
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  have : ExpChar S p := expChar_of_injective_algebraMap (algebraMap k S).injective p
  set e := IsPurelyInseparable.exponent S K
  set q := p ^ e
  have hq : 0 < q := expChar_pow_pos K p e
  have hpow : ∀ x : K, x ^ q ∈ S := fun x ↦ by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' S p x
    rw [← hy]; exact y.2
  have := isDedekindDomain_adjoin ht
  -- the integral closure of `R` in the separable closure `S` is finite over `R`
  letI : Algebra R S := ((algebraMap F S).comp (algebraMap R F)).toAlgebra
  have : IsScalarTower R F S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hfin : Module.Finite R (integralClosure R S) :=
    IsIntegralClosure.finite R F S (integralClosure R S)
  obtain ⟨T, hT⟩ := hfin.fg_top
  -- its image in `K`
  set T' : Finset K := T.image fun b : integralClosure R S ↦ (b.1 : K)
  have hspan : ∀ y : K, y ∈ S → IsIntegral R y → y ∈ Submodule.span R (T' : Set K) := by
    intro y hyS hyR
    have hyR' : IsIntegral R (⟨y, hyS⟩ : S) := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R S K) (algebraMap S K).injective]
      exact hyR
    have hmem :
        (⟨⟨y, hyS⟩, hyR'⟩ : integralClosure R S) ∈ Submodule.span R (T : Set _) := by
      rw [hT]; trivial
    have := Submodule.mem_map_of_mem (f := (IsScalarTower.toAlgHom R S K).toLinearMap.comp
      (integralClosure R S).val.toLinearMap) hmem
    rw [Submodule.map_span] at this
    simpa [T', Finset.coe_image, Set.image_image] using this
  set R' := Algebra.adjoin k {t ^ q}
  -- the `R'`-module spanned by the `t^i b`
  set M : Submodule R' K := Submodule.span R'
    ((Finset.univ ×ˢ T').image fun ib : Fin q × K ↦ t ^ (ib.1 : ℕ) * ib.2 : Finset K)
  have hRM : ∀ r ∈ R, ∀ b ∈ T', r * b ∈ M := by
    intro r hr b hb
    have := mem_span_pow_of_mem_adjoin t q hq hr
    clear hr
    induction this using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      apply Submodule.subset_span
      rw [Finset.coe_image]
      exact ⟨(i, b), Finset.mem_product.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact M.add_mem hx hy
    | smul c x _ hx =>
      rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc]
      exact M.smul_mem c hx
  have hRM' : ∀ r ∈ R, ∀ y ∈ M, r * y ∈ M := by
    intro r hr y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      simp only [Finset.coe_image, Finset.coe_product, Finset.coe_univ, Set.mem_image,
        Set.mem_prod, Set.mem_univ, true_and, Finset.mem_coe] at hx
      obtain ⟨⟨i, b⟩, hb, rfl⟩ := hx
      rw [← mul_assoc]
      exact hRM _ (mul_mem hr (pow_mem (Algebra.self_mem_adjoin_singleton k t) _)) b hb
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact M.add_mem hx hy
    | smul c x _ hx =>
      rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
      exact M.smul_mem c hx
  have hpowM : ∀ x ∈ chartRing k t, x ^ q ∈ M := by
    intro x hx
    have hxi : IsIntegral R (x ^ q) := (hx : IsIntegral R x).pow q
    have := hspan _ (hpow x) hxi
    generalize x ^ q = y at this ⊢
    induction this using Submodule.span_induction with
    | mem b hb =>
      have := hRM 1 (one_mem _) b hb
      rwa [one_mul] at this
    | zero => simp
    | add x y _ _ hx hy => exact M.add_mem hx hy
    | smul c x _ hx =>
      rw [Subalgebra.smul_def, smul_eq_mul]
      exact hRM' c c.2 x hx
  -- `R'` is noetherian, so the `R'`-span of the `q`-th powers of `A_t` is finitely generated
  have ht' : Transcendental k (t ^ q) := ht.pow hq
  have := isPrincipalIdealRing_adjoin ht'
  have hMfg : M.FG := ⟨_, rfl⟩
  have : IsNoetherian R' M := isNoetherian_of_fg_of_noetherian M hMfg
  set Fr := iterateFrobenius K p e
  have hFr : Function.Injective Fr := (iterateFrobenius K p e).injective
  set Q : Submodule R' K := Submodule.span R' (Fr '' (chartRing k t))
  have hQ : Q.FG := Submodule.FG.of_le_of_isNoetherian (T := M) (Submodule.span_le.mpr (by
    rintro _ ⟨x, hx, rfl⟩; exact hpowM x hx))
  obtain ⟨G, hG⟩ := hQ
  obtain ⟨G', hG'sub, hG'⟩ := Submodule.subset_span_finite_of_subset_span (R := R')
    (s := Fr '' (chartRing k t)) (t := G) (by
      intro x hx; change x ∈ Q; rw [← hG]; exact Submodule.subset_span hx)
  -- choose preimages of the generators
  have hpre : ∀ y ∈ G', ∃ x ∈ chartRing k t, Fr x = y := fun y hy ↦ hG'sub hy
  choose! g hgC hgFr using hpre
  -- transport back along `Fr`
  have key : ∀ y ∈ Q, ∃ x ∈ Submodule.span R (G'.image g : Set K), Fr x = y := by
    intro y hy
    have hy' : y ∈ Submodule.span R' (G' : Set K) := by
      have : Q ≤ Submodule.span R' (G' : Set K) := by
        rw [← hG, Submodule.span_le]; exact hG'
      exact this hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy => exact ⟨g y, Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem g hy)), hgFr y hy⟩
    | zero => exact ⟨0, zero_mem _, map_zero Fr⟩
    | add y z _ _ hy hz =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨x + w, add_mem hx hw, map_add Fr x w⟩
    | smul c y _ hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨r, hr, hrc⟩ := exists_pow_eq_of_mem_adjoin t p e c.2
      refine ⟨r * x, ?_, ?_⟩
      · have : (⟨r, hr⟩ : R) • x ∈ Submodule.span R (G'.image g : Set K) :=
          Submodule.smul_mem _ _ hx
        simpa [Subalgebra.smul_def] using this
      · rw [map_mul, Subalgebra.smul_def, smul_eq_mul]
        congr 1
  change Module.Finite R (Subalgebra.toSubmodule (chartRing k t))
  rw [Module.Finite.iff_fg]
  refine ⟨G'.image g, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hgC y hy
  · intro x hx
    rw [Subalgebra.mem_toSubmodule] at hx
    obtain ⟨x', hx', hxx'⟩ := key (Fr x) (Submodule.subset_span ⟨x, hx, rfl⟩)
    rwa [hFr hxx'] at hx'

variable [IsFunctionField k K]

instance [Fact (Transcendental k t)] : FiniteDimensional k⟮t⟯ K :=
  finiteDimensional_adjoin Fact.out

instance [Fact (Transcendental k t)] : IsFractionRing (chartRing k t) K :=
  integralClosure.isFractionRing_of_finite_extension k⟮t⟯ K

variable [PerfectField k]

instance [Fact (Transcendental k t)] : Module.Finite (Algebra.adjoin k {t}) (chartRing k t) :=
  finite_chartRing Fact.out

instance [Fact (Transcendental k t)] : IsNoetherianRing (chartRing k t) :=
  isNoetherian_of_tower (Algebra.adjoin k {t}) inferInstance

instance [Fact (Transcendental k t)] : IsDedekindDomain (chartRing k t) :=
  { (inferInstance : IsNoetherianRing (chartRing k t)),
    Ring.DimensionLEOne.of_isIntegral (Algebra.adjoin k {t}) (chartRing k t),
    (isIntegrallyClosed_iff K).mpr fun {x} hx =>
      ⟨⟨x, isIntegral_trans (R := Algebra.adjoin k {t}) _ hx⟩, rfl⟩ with :
    IsDedekindDomain (chartRing k t) }

instance [Fact (Transcendental k t)] : Algebra.FiniteType k (chartRing k t) := by
  have : Algebra.FiniteType k (Algebra.adjoin k {t}) :=
    .adjoin_of_finite (Set.finite_singleton t)
  exact Algebra.FiniteType.trans (S := Algebra.adjoin k {t}) inferInstance inferInstance

end Finite

end WeilCurves.FunctionField
