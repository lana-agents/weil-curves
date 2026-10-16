/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Chart
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Places of a function field

A *place* of a field `K` is a valuation subring `O ⊊ K` containing `k` (the condition
`k ⊆ O` excludes e.g. the Gauss extension of a `p`-adic valuation of `k` to `k(t)`).
For a function field `K` (`WeilCurves.FunctionField.IsFunctionField`) the places are the closed
points of
the regular proper model of the curve, and they are described by the affine *charts*
`A_t = chartRing k t`: for `t` transcendental, the places containing `t` are exactly the
localisations of the Dedekind domain `A_t` at its height-one primes
(`WeilCurves.FunctionField.Place.chartEquiv`); every place contains `t` or `t⁻¹`.

## Main definitions

* `WeilCurves.FunctionField.Place k K`: the places of `K`.
* `WeilCurves.FunctionField.Place.ord P : K → ℤ`: the normalised discrete valuation at `P`
  (with the junk value `ord 0 = 0`).
* `WeilCurves.FunctionField.Place.ResidueField P`: the residue field, a finite extension of `k`.
* `WeilCurves.FunctionField.Place.deg P`: the degree `[κ(P) : k]`.
* `WeilCurves.FunctionField.Place.chartEquiv t`: places containing `t` ≃ height-one primes of `A_t`.

## Main results

* `IsDiscreteValuationRing P.1`; the valuation laws for `ord`; uniformisers.
* `WeilCurves.FunctionField.Place.finite_setOf_ord_ne_zero`,
  `WeilCurves.FunctionField.Place.finite_setOf_notMem`: finiteness of zeros and poles.
* `WeilCurves.FunctionField.Place.exists_ord_pos`, `WeilCurves.FunctionField.Place.exists_ord_neg`:
  a
  transcendental element has a zero and a pole;
  `WeilCurves.FunctionField.Place.isAlgebraic_of_forall_mem`: an element lying in every place is
  algebraic over `k`.
-/

open IsDedekindDomain IsLocalRing
open scoped IntermediateField WithZero

namespace WeilCurves.FunctionField

section Abstract

/-! ### Valuation subrings dominating a Dedekind domain -/

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {R : Type*} [CommRing R] [Algebra R K]

/-- The prime of `R` lying below a valuation subring `O` containing (the image of) `R`. -/
def primeBelow (O : ValuationSubring K) (hR : ∀ r, algebraMap R K r ∈ O) : Ideal R :=
  (maximalIdeal O).comap ((algebraMap R K).codRestrict O hR)

theorem mem_primeBelow {O : ValuationSubring K} {hR : ∀ r, algebraMap R K r ∈ O} {r : R} :
    r ∈ primeBelow O hR ↔ algebraMap R K r ∈ O.nonunits := by
  rw [primeBelow, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

instance (O : ValuationSubring K) (hR : ∀ r, algebraMap R K r ∈ O) :
    (primeBelow O hR).IsPrime := Ideal.comap_isPrime _ _

section Domain

variable [IsDomain R]

theorem primeBelow_ne_bot [IsFractionRing R K] {O : ValuationSubring K} (hO : O ≠ ⊤)
    (hR : ∀ r, algebraMap R K r ∈ O) : primeBelow O hR ≠ ⊥ := by
  intro h
  apply hO
  refine top_unique fun x _ ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : algebraMap R K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hbn : algebraMap R K b ∉ O.nonunits := by
    rw [← mem_primeBelow (hR := hR), h, Ideal.mem_bot]
    exact fun h0 ↦ hb0 (by rw [h0, map_zero])
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hbn
  rw [div_eq_mul_inv]
  exact O.mul_mem _ _ (hR a) hbn.2

/-- The height-one prime of `R` below a valuation subring `O ≠ K` containing `R`. -/
def heightOneBelow [IsFractionRing R K] (O : ValuationSubring K) (hO : O ≠ ⊤)
    (hR : ∀ r, algebraMap R K r ∈ O) : HeightOneSpectrum R :=
  ⟨primeBelow O hR, inferInstance, primeBelow_ne_bot hO hR⟩

theorem mem_heightOneBelow [IsFractionRing R K] {O : ValuationSubring K} {hO : O ≠ ⊤}
    {hR : ∀ r, algebraMap R K r ∈ O} {r : R} :
    r ∈ (heightOneBelow O hO hR).asIdeal ↔ algebraMap R K r ∈ O.nonunits :=
  mem_primeBelow

end Domain

variable [IsDedekindDomain R] [IsFractionRing R K]

theorem valuationSubringAtPrime_le (O : ValuationSubring K) (hO : O ≠ ⊤)
    (hR : ∀ r, algebraMap R K r ∈ O) :
    HeightOneSpectrum.valuationSubringAtPrime K (heightOneBelow O hO hR) ≤ O := by
  rintro x ⟨a, s, hs, rfl⟩
  have hsn : algebraMap R K s ∉ O.nonunits := by
    rw [← mem_primeBelow (hR := hR)]; exact hs
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hsn
  exact O.mul_mem _ _ (hR a) hsn.2

/-- A valuation subring `O ≠ K` containing a Dedekind domain `R` with fraction field `K` is
the localisation of `R` at the prime below `O`. -/
theorem valuationSubringAtPrime_heightOneBelow (O : ValuationSubring K) (hO : O ≠ ⊤)
    (hR : ∀ r, algebraMap R K r ∈ O) :
    HeightOneSpectrum.valuationSubringAtPrime K (heightOneBelow O hO hR) = O :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le O hO hR) hO

instance (v : HeightOneSpectrum R) :
    IsDiscreteValuationRing (HeightOneSpectrum.valuationSubringAtPrime K v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _

theorem isDiscreteValuationRing_of_le (O : ValuationSubring K) (hO : O ≠ ⊤)
    (hR : ∀ r, algebraMap R K r ∈ O) : IsDiscreteValuationRing O := by
  rw [← valuationSubringAtPrime_heightOneBelow O hO hR]; infer_instance

theorem valuationSubringAtPrime_ne_top (v : HeightOneSpectrum R) :
    HeightOneSpectrum.valuationSubringAtPrime K v ≠ ⊤ := by
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, ne_eq,
    Valuation.valuationSubring_eq_top_iff, not_not]
  infer_instance

theorem algebraMap_mem_valuationSubringAtPrime (v : HeightOneSpectrum R) (r : R) :
    algebraMap R K r ∈ HeightOneSpectrum.valuationSubringAtPrime K v := by
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff]
  exact HeightOneSpectrum.valuation_le_one _ _

theorem heightOneBelow_valuationSubringAtPrime (v : HeightOneSpectrum R) :
    heightOneBelow (HeightOneSpectrum.valuationSubringAtPrime K v)
      (valuationSubringAtPrime_ne_top v) (algebraMap_mem_valuationSubringAtPrime v) = v := by
  ext r
  rw [mem_heightOneBelow, ValuationSubring.mem_nonunits_iff,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K),
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact (Valuation.isEquiv_valuation_valuationSubring _).symm.lt_one_iff_lt_one

/-- The residue map of `O` restricted to a Dedekind domain `R ⊆ O` with fraction field `K`
is surjective (the residue field of `O` is `R ⧸ 𝔭`). -/
theorem residue_comp_surjective (O : ValuationSubring K) (hO : O ≠ ⊤)
    (hR : ∀ r, algebraMap R K r ∈ O) :
    Function.Surjective ((residue O).comp ((algebraMap R K).codRestrict O hR)) := by
  intro y
  obtain ⟨⟨x, hxO⟩, rfl⟩ := residue_surjective y
  have hx := hxO
  rw [← valuationSubringAtPrime_heightOneBelow O hO hR] at hx
  obtain ⟨a, s, hs, hxas⟩ := hx
  obtain ⟨b, i, hi, hbi⟩ := (heightOneBelow O hO hR).isMaximal.exists_inv hs
  refine ⟨a * b, ?_⟩
  rw [RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  have hs0 : algebraMap R K s ≠ 0 := by
    intro h0
    apply hs
    rw [(IsFractionRing.injective R K) (h0.trans (map_zero _).symm)]
    exact Ideal.zero_mem _
  have hin : algebraMap R K i ∈ O.nonunits := mem_heightOneBelow.mp hi
  have key : x - algebraMap R K (a * b) = x * algebraMap R K i := by
    have hbi' : algebraMap R K b * algebraMap R K s + algebraMap R K i = 1 := by
      rw [← map_mul, ← map_add, hbi, map_one]
    rw [hxas, map_mul, show algebraMap R K i = 1 - algebraMap R K b * algebraMap R K s by
      rw [← hbi']; ring]
    field_simp
  change x - algebraMap R K (a * b) ∈ O.nonunits
  rw [key, ValuationSubring.mem_nonunits_iff, map_mul]
  rw [ValuationSubring.mem_nonunits_iff] at hin
  calc O.valuation x * O.valuation (algebraMap R K i) < 1 * 1 :=
        mul_lt_mul_of_le_of_lt_of_nonneg_of_pos ((O.valuation_le_one_iff x).mpr hxO) hin
          zero_le zero_lt_one
    _ = 1 := one_mul 1

end Abstract

/-! ### Places -/

/-- A place of a field `K`: a valuation subring `O ≠ K` containing `k`.
(Reducible, so that `P.1` for `P : Place k K` is well-typed at every transparency.) -/
abbrev Place (k K : Type*) [Field k] [Field K] [Algebra k K] : Type _ :=
  {O : ValuationSubring K // O ≠ ⊤ ∧ ∀ c : k, algebraMap k K c ∈ O}

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

@[ext]
theorem ext {P Q : Place k K} (h : P.1 = Q.1) : P = Q := Subtype.ext h

theorem ne_top (P : Place k K) : P.1 ≠ ⊤ := P.2.1


theorem mem_or_inv_mem (P : Place k K) (x : K) : x ∈ P.1 ∨ x⁻¹ ∈ P.1 :=
  P.1.mem_or_inv_mem x

theorem algebraMap_mem (P : Place k K) (c : k) : algebraMap k K c ∈ P.1 := P.2.2 c

/-- Elements of `K` integral over `k` (the constants) lie in every place. -/
theorem mem_of_isIntegral (P : Place k K) {x : K} (hx : IsIntegral k x) : x ∈ P.1 := by
  have : IsIntegrallyClosedIn P.1.toSubring K := inferInstanceAs (IsIntegrallyClosedIn P.1 K)
  have hle : (integralClosure k K).toSubring ≤ P.1.toSubring :=
    Subring.integralClosure_le_iff.mpr P.algebraMap_mem
  exact hle hx

theorem mem_of_isAlgebraic (P : Place k K) {x : K} (hx : IsAlgebraic k x) : x ∈ P.1 :=
  P.mem_of_isIntegral hx.isIntegral

theorem inv_mem_of_isAlgebraic (P : Place k K) {x : K} (hx : IsAlgebraic k x) : x⁻¹ ∈ P.1 :=
  P.mem_of_isAlgebraic hx.inv

/-! ### Charts -/

section Chart

variable [IsFunctionField k K] (t : K) [Fact (Transcendental k t)]

omit [IsFunctionField k K] [Fact (Transcendental k t)] in
theorem algebraMap_chartRing_mem (P : Place k K) (ht : t ∈ P.1) (r : chartRing k t) :
    algebraMap (chartRing k t) K r ∈ P.1 :=
  mem_of_mem_chartRing P.1 P.algebraMap_mem ht r.2

/-- The height-one prime of the chart ring `A_t` below a place containing `t`. -/
noncomputable def toChart (P : Place k K) (ht : t ∈ P.1) : HeightOneSpectrum (chartRing k t) :=
  heightOneBelow P.1 P.ne_top (P.algebraMap_chartRing_mem t ht)

theorem mem_toChart_iff (P : Place k K) (ht : t ∈ P.1) {r : chartRing k t} :
    r ∈ (P.toChart t ht).asIdeal ↔ (r : K) ∈ P.1.nonunits :=
  mem_heightOneBelow

variable [PerfectField k]

/-- The place of `K` given by the localisation of `A_t` at a height-one prime. -/
noncomputable def ofChart (v : HeightOneSpectrum (chartRing k t)) : Place k K :=
  ⟨HeightOneSpectrum.valuationSubringAtPrime K v, valuationSubringAtPrime_ne_top v,
    fun q ↦ algebraMap_mem_valuationSubringAtPrime v
      ⟨algebraMap k K q, algebraMap_mem_chartRing t q⟩⟩

theorem ofChart_val (v : HeightOneSpectrum (chartRing k t)) :
    (ofChart t v).1 = HeightOneSpectrum.valuationSubringAtPrime K v := rfl

theorem self_mem_ofChart (v : HeightOneSpectrum (chartRing k t)) : t ∈ (ofChart t v).1 :=
  algebraMap_mem_valuationSubringAtPrime v ⟨t, self_mem_chartRing k t⟩

@[simp]
theorem ofChart_toChart (P : Place k K) (ht : t ∈ P.1) : ofChart t (P.toChart t ht) = P :=
  Place.ext (valuationSubringAtPrime_heightOneBelow _ _ _)

@[simp]
theorem toChart_ofChart (v : HeightOneSpectrum (chartRing k t)) :
    (ofChart t v).toChart t (self_mem_ofChart t v) = v :=
  heightOneBelow_valuationSubringAtPrime v

/-- The places containing `t` correspond to the height-one primes of the chart ring `A_t`
(the place is the localisation of `A_t` at the prime). -/
noncomputable def chartEquiv :
    {P : Place k K // t ∈ P.1} ≃ HeightOneSpectrum (chartRing k t) where
  toFun P := P.1.toChart t P.2
  invFun v := ⟨ofChart t v, self_mem_ofChart t v⟩
  left_inv P := Subtype.ext (ofChart_toChart t P.1 P.2)
  right_inv v := toChart_ofChart t v

theorem residue_comp_surjective (P : Place k K) (ht : t ∈ P.1) :
    Function.Surjective ((residue P.1).comp
      ((algebraMap (chartRing k t) K).codRestrict P.1 (P.algebraMap_chartRing_mem t ht))) :=
  FunctionField.residue_comp_surjective P.1 P.ne_top _

end Chart

section DVR

variable [IsFunctionField k K]

/-- Every place contains a transcendental element (namely `t` or `t⁻¹` for any
transcendental `t`). -/
theorem exists_transcendental_mem (P : Place k K) :
    ∃ t : K, Transcendental k t ∧ t ∈ P.1 := by
  obtain ⟨t, ht⟩ := exists_transcendental k K
  rcases P.mem_or_inv_mem t with h | h
  · exact ⟨t, ht, h⟩
  · exact ⟨t⁻¹, transcendental_inv ht, h⟩

variable [PerfectField k]

instance isDiscreteValuationRing (P : Place k K) : IsDiscreteValuationRing P.1 := by
  obtain ⟨t, ht, htP⟩ := P.exists_transcendental_mem
  have : Fact (Transcendental k t) := ⟨ht⟩
  exact isDiscreteValuationRing_of_le P.1 P.ne_top (P.algebraMap_chartRing_mem t htP)

/-- The normalised discrete valuation of `K` at the place `P`, with values in `ℤᵐ⁰`. -/
noncomputable def valuation (P : Place k K) : Valuation K ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal P.1).valuation K

/-- The order of vanishing `ord_P f ∈ ℤ` of `f` at the place `P` (junk value `ord_P 0 = 0`). -/
noncomputable def ord (P : Place k K) (f : K) : ℤ := -WithZero.log (P.valuation f)

variable (P : Place k K) {f g : K}

@[simp]
theorem valuation_eq_zero_iff : P.valuation f = 0 ↔ f = 0 := Valuation.zero_iff _

theorem valuation_ne_zero (hf : f ≠ 0) : P.valuation f ≠ 0 := by simpa using hf

theorem valuation_eq_exp (hf : f ≠ 0) : P.valuation f = WithZero.exp (-P.ord f) := by
  rw [ord, neg_neg, WithZero.exp_log (P.valuation_ne_zero hf)]

@[simp]
theorem ord_zero : P.ord 0 = 0 := by simp [ord]

@[simp]
theorem ord_one : P.ord 1 = 0 := by simp [ord]

theorem ord_mul (hf : f ≠ 0) (hg : g ≠ 0) : P.ord (f * g) = P.ord f + P.ord g := by
  simp only [ord, map_mul, WithZero.log_mul (P.valuation_ne_zero hf) (P.valuation_ne_zero hg)]
  ring

@[simp]
theorem ord_inv (f : K) : P.ord f⁻¹ = -P.ord f := by
  simp [ord, map_inv₀, WithZero.log_inv]

@[simp]
theorem ord_pow (f : K) (n : ℕ) : P.ord (f ^ n) = n * P.ord f := by
  simp [ord, map_pow, WithZero.log_pow]

@[simp]
theorem ord_zpow (f : K) (n : ℤ) : P.ord (f ^ n) = n * P.ord f := by
  simp [ord, map_zpow₀, WithZero.log_zpow]

theorem ord_div (hf : f ≠ 0) (hg : g ≠ 0) : P.ord (f / g) = P.ord f - P.ord g := by
  rw [div_eq_mul_inv, P.ord_mul hf (inv_ne_zero hg), ord_inv, sub_eq_add_neg]

@[simp]
theorem ord_neg (f : K) : P.ord (-f) = P.ord f := by simp [ord]

theorem mem_iff_valuation_le_one : f ∈ P.1 ↔ P.valuation f ≤ 1 := by
  have := IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := P.1) (K := K)
  change _ ↔ f ∈ (P.valuation.valuationSubring.toSubring)
  rw [valuation, ← this]
  simp

theorem mem_iff_ord_nonneg : f ∈ P.1 ↔ f = 0 ∨ 0 ≤ P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [P.1.zero_mem]
  rw [mem_iff_valuation_le_one, P.valuation_eq_exp hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
  simp [hf]

theorem ord_nonneg_of_mem (hf : f ∈ P.1) : 0 ≤ P.ord f := by
  rcases (P.mem_iff_ord_nonneg).mp hf with rfl | h
  · simp
  · exact h

theorem mem_of_ord_nonneg (hf : 0 ≤ P.ord f) : f ∈ P.1 :=
  (P.mem_iff_ord_nonneg).mpr (Or.inr hf)

theorem ord_neg_iff : P.ord f < 0 ↔ f ∉ P.1 := by
  rw [P.mem_iff_ord_nonneg, not_or, not_le]
  constructor
  · intro h
    refine ⟨fun h0 ↦ ?_, h⟩
    subst h0
    simp at h
  · exact fun h ↦ h.2

/-- For `a ∈ O_P` nonzero, `ord_P a > 0` iff `a` lies in the maximal ideal. -/
theorem ord_pos_iff_mem_maximalIdeal {a : P.1} (ha : (a : K) ≠ 0) :
    0 < P.ord a ↔ a ∈ maximalIdeal P.1 := by
  have h := HeightOneSpectrum.valuation_lt_one_iff_mem
    (IsDiscreteValuationRing.maximalIdeal P.1) (K := K) a
  change P.valuation a < 1 ↔ a ∈ maximalIdeal P.1 at h
  rw [← h, P.valuation_eq_exp ha, ← WithZero.exp_zero, WithZero.exp_lt_exp, Left.neg_neg_iff]

theorem ord_pos_iff : 0 < P.ord f ↔ f ≠ 0 ∧ f ∈ P.1.nonunits := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  simp only [ne_eq, hf, not_false_eq_true, true_and]
  constructor
  · intro h
    have hm : f ∈ P.1 := P.mem_of_ord_nonneg h.le
    have := (P.ord_pos_iff_mem_maximalIdeal (a := ⟨f, hm⟩) hf).mp h
    exact ValuationSubring.coe_mem_nonunits_iff.mpr this
  · intro h
    have hm : f ∈ P.1 := P.1.nonunits_subset h
    exact (P.ord_pos_iff_mem_maximalIdeal (a := ⟨f, hm⟩) hf).mpr
      (ValuationSubring.coe_mem_nonunits_iff.mp h)

theorem ord_eq_zero_iff (hf : f ≠ 0) : P.ord f = 0 ↔ f ∈ P.1 ∧ f⁻¹ ∈ P.1 := by
  rw [P.mem_iff_ord_nonneg, P.mem_iff_ord_nonneg, ord_inv]
  simp only [hf, inv_eq_zero, false_or, Left.nonneg_neg_iff]
  omega

theorem min_le_ord_add (hfg : f + g ≠ 0) : min (P.ord f) (P.ord g) ≤ P.ord (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have h := P.valuation.map_add f g
  rw [P.valuation_eq_exp hf, P.valuation_eq_exp hg, P.valuation_eq_exp hfg] at h
  rcases le_total (P.ord f) (P.ord g) with hle | hle
  · rw [max_eq_left (WithZero.exp_le_exp.mpr (neg_le_neg hle)), WithZero.exp_le_exp] at h
    rw [min_eq_left hle]; omega
  · rw [max_eq_right (WithZero.exp_le_exp.mpr (neg_le_neg hle)), WithZero.exp_le_exp] at h
    rw [min_eq_right hle]; omega

theorem ord_add_eq_of_lt (hf : f ≠ 0) (hg : g ≠ 0) (h : P.ord f < P.ord g) :
    P.ord (f + g) = P.ord f := by
  have hv : P.valuation g < P.valuation f := by
    rw [P.valuation_eq_exp hf, P.valuation_eq_exp hg, WithZero.exp_lt_exp]; omega
  have := P.valuation.map_add_eq_of_lt_left hv
  rw [ord, ord, this]

/-- Every place has a uniformiser. -/
theorem exists_ord_eq_one : ∃ π : K, P.ord π = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K
    (IsDiscreteValuationRing.maximalIdeal P.1)
  refine ⟨π, ?_⟩
  change -WithZero.log (P.valuation π) = 1
  rw [show P.valuation π = WithZero.exp (-1) from hπ, WithZero.log_exp, neg_neg]

/-- Constants (elements algebraic over `k`) have order `0` at every place. -/
theorem ord_eq_zero_of_isAlgebraic {c : K} (hc : IsAlgebraic k c) : P.ord c = 0 := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  exact (P.ord_eq_zero_iff hc0).mpr ⟨P.mem_of_isAlgebraic hc, P.inv_mem_of_isAlgebraic hc⟩

@[simp]
theorem ord_algebraMap_base (c : k) : P.ord (algebraMap k K c) = 0 :=
  P.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap c)

@[simp]
theorem ord_natCast (n : ℕ) : P.ord (n : K) = 0 := by
  simpa using P.ord_algebraMap_base (n : k)

/-- Elements of an algebraic extension `F` of `k` inside `K` (constants) have order `0`. -/
theorem ord_algebraMap {F : Type*} [Field F] [Algebra k F] [Algebra F K] [IsScalarTower k F K]
    [Algebra.IsAlgebraic k F] (c : F) : P.ord (algebraMap F K c) = 0 :=
  P.ord_eq_zero_of_isAlgebraic
    ((Algebra.IsAlgebraic.isAlgebraic (R := k) c).algHom (IsScalarTower.toAlgHom k F K))

end DVR

end Place

end WeilCurves.FunctionField
