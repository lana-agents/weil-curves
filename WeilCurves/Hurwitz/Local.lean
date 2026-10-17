/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.ConstantExtension.ExtPlaces
import WeilCurves.FunctionField.Degree
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.PID

/-!
# The complementary module above a place

Let `L / K` be a finite separable extension of function fields over a perfect field `k` and `P`
a place of `K`. Following Stichtenoth (*Algebraic Function Fields and Codes*, §III.4, the
complementary module `C_P` and the different exponents `d(Q|P)`), we consider

* the integral closure `O'_P = intClo L P` of `O_P` in `L`; it is the intersection of the
  valuation rings `O_Q` of the places `Q` of `L` above `P` (`mem_intClo_iff`), a Dedekind domain
  with finitely many primes, hence a principal ideal domain;
* the complementary module `C_P = {z ∈ L | Tr_{L/K}(z O'_P) ⊆ O_P}` (`IsCodiff`); it is Mathlib's
  dual fractional ideal `FractionalIdeal.dual O_P K 1` (whose inverse is Mathlib's
  `differentIdeal`), hence principal: `C_P = c_P O'_P` with `c_P = codiffGen L P`
  (`isCodiff_iff`), i.e. `z ∈ C_P ↔ ∀ Q | P, ord_Q z ≥ ord_Q c_P`
  (`isCodiff_iff_ord`). The different exponent is `d(Q|P) = -ord_Q c_P ≥ 0`.

Main local facts used for the Hurwitz genus formula:
* `trace_mem_of_ord`: `ord_Q z ≥ ord_Q c_P` for all `Q | P` implies `Tr z ∈ O_P`;
* `exists_isCodiff_trace_eq`: `Tr(C_P) = O_P`;
* `exists_sharp`: for `Q | P` there is `z` with `ord_Q z ≥ ord_Q c_P - 1`,
  `ord_{Q'} z ≥ ord_{Q'} c_P` for the other `Q' | P`, and `Tr z ∉ O_P`.
-/

open IsDedekindDomain Module

set_option linter.unusedSectionVars false

namespace WeilCurves.FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (L : Type*) [Field L] [Algebra K L]
  [Algebra k L] [IsScalarTower k K L] [PerfectField k] [IsFunctionField k K]
  [IsFunctionField k L] [FiniteDimensional K L]

/-- The integral closure `O'_P` of the valuation ring `O_P` in `L`. -/
abbrev intClo (P : Place k K) : Subalgebra P.1 L := integralClosure P.1 L

variable {L}

theorem algebraMap_place_apply (P : Place k K) (a : P.1) :
    algebraMap P.1 L a = algebraMap K L (a : K) :=
  IsScalarTower.algebraMap_apply P.1 K L a

/-- Elements of `O'_P` lie in every place above `P`. -/
theorem mem_of_mem_intClo {P : Place k K} {Q : Place k L} (hQ : Q.restrict (K := K) = P)
    {y : L} (hy : y ∈ intClo L P) : y ∈ Q.1 := by
  have : IsIntegrallyClosedIn Q.1.toSubring L := inferInstanceAs (IsIntegrallyClosedIn Q.1 L)
  have hle : (integralClosure P.1 L).toSubring ≤ Q.1.toSubring := by
    rw [Subring.integralClosure_le_iff]
    intro r
    have hr : (r : K) ∈ (Q.restrict (K := K)).1 := hQ ▸ r.2
    rw [algebraMap_place_apply]
    exact Place.mem_restrict.mp hr
  exact hle hy

theorem algebraMap_intClo_mem (P : Place k K) {Q : Place k L} (hQ : Q.restrict (K := K) = P)
    (r : intClo L P) : algebraMap (intClo L P) L r ∈ Q.1 :=
  mem_of_mem_intClo hQ r.2

theorem finite_setOf_restrict_eq (P : Place k K) :
    {Q : Place k L | Q.restrict (K := K) = P}.Finite := by
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  refine (Place.finite_setOf_ord_pos (algebraMap K L π)).subset fun Q hQ ↦ ?_
  have hQ' : (Q.restrict (K := K)).ord π = 1 := by rw [hQ]; exact hπ
  exact Q.ord_algebraMap_uniformizer_pos hQ'

section Dedekind

variable [Algebra.IsSeparable K L]

instance (P : Place k K) : IsDedekindDomain (intClo L P) :=
  integralClosure.isDedekindDomain P.1 K L

instance (P : Place k K) : IsFractionRing (intClo L P) L :=
  integralClosure.isFractionRing_of_finite_extension K L

instance (P : Place k K) : Module.Finite P.1 (intClo L P) :=
  IsIntegralClosure.finite P.1 K L (intClo L P)

variable {P : Place k K}

theorem algebraMap_base_mem_intClo (c : k) : algebraMap k L c ∈ intClo L P := by
  have h := (intClo L P).algebraMap_mem (⟨algebraMap k K c, P.algebraMap_mem c⟩ : P.1)
  rwa [algebraMap_place_apply, ← IsScalarTower.algebraMap_apply] at h

/-- The place of `L` above `P` attached to a height-one prime of `O'_P`. -/
noncomputable def placeOfPrime (v : HeightOneSpectrum (intClo L P)) : Place k L :=
  ⟨HeightOneSpectrum.valuationSubringAtPrime L v, valuationSubringAtPrime_ne_top v,
    fun c ↦ algebraMap_mem_valuationSubringAtPrime (K := L) v
      ⟨algebraMap k L c, algebraMap_base_mem_intClo c⟩⟩

theorem placeOfPrime_val (v : HeightOneSpectrum (intClo L P)) :
    (placeOfPrime v).1 = HeightOneSpectrum.valuationSubringAtPrime L v := rfl

theorem restrict_placeOfPrime (v : HeightOneSpectrum (intClo L P)) :
    (placeOfPrime v).restrict (K := K) = P := by
  have hle : P.1 ≤ ((placeOfPrime v).restrict (K := K)).1 := by
    intro a ha
    rw [Place.mem_restrict]
    have := algebraMap_mem_valuationSubringAtPrime (K := L) v
      (algebraMap P.1 (intClo L P) ⟨a, ha⟩)
    rwa [← IsScalarTower.algebraMap_apply, algebraMap_place_apply] at this
  exact Place.ext (ValuationSubring.eq_of_le_of_ne_top P.1 hle
    ((placeOfPrime v).restrict (K := K)).ne_top).symm

/-- The height-one prime of `O'_P` below a place `Q | P`. -/
noncomputable def toPrime {Q : Place k L} (hQ : Q.restrict (K := K) = P) :
    HeightOneSpectrum (intClo L P) :=
  heightOneBelow Q.1 Q.ne_top (algebraMap_intClo_mem P hQ)

@[simp]
theorem placeOfPrime_toPrime {Q : Place k L} (hQ : Q.restrict (K := K) = P) :
    placeOfPrime (toPrime hQ) = Q :=
  Place.ext (valuationSubringAtPrime_heightOneBelow _ _ _)

@[simp]
theorem toPrime_placeOfPrime (v : HeightOneSpectrum (intClo L P)) :
    toPrime (restrict_placeOfPrime v) = v :=
  heightOneBelow_valuationSubringAtPrime v

theorem mem_toPrime_iff {Q : Place k L} (hQ : Q.restrict (K := K) = P) {r : intClo L P} :
    r ∈ (toPrime hQ).asIdeal ↔ (r : L) ∈ Q.1.nonunits :=
  mem_heightOneBelow

/-- `ord_Q` is the `v`-adic valuation for the prime `v` of `O'_P` below `Q`. -/
theorem ord_placeOfPrime (v : HeightOneSpectrum (intClo L P)) (x : L) :
    (placeOfPrime v).ord x = -WithZero.log (v.valuation L x) := by
  refine (placeOfPrime v).ord_eq_neg_log (v.valuation L) (fun y ↦ ?_)
    (HeightOneSpectrum.valuation_exists_uniformizer L v) x
  rw [placeOfPrime_val, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

/-- **`O'_P = ⋂_{Q | P} O_Q`**. -/
theorem mem_intClo_iff {y : L} :
    y ∈ intClo L P ↔ ∀ Q : Place k L, Q.restrict (K := K) = P → y ∈ Q.1 := by
  refine ⟨fun hy Q hQ ↦ mem_of_mem_intClo hQ hy, fun h ↦ ?_⟩
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L y fun v ↦ by
    have hv := h (placeOfPrime v) (restrict_placeOfPrime v)
    rw [placeOfPrime_val, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff] at hv
    exact hv
  rw [← hr]
  exact r.2

/-- `O'_P` has only finitely many primes. -/
theorem finite_primes_intClo : {I : Ideal (intClo L P) | I.IsPrime}.Finite := by
  have hfin := (finite_setOf_restrict_eq (L := L) P)
  have : Finite {Q : Place k L // Q.restrict (K := K) = P} := hfin.to_subtype
  refine ((Set.finite_range fun Q : {Q : Place k L // Q.restrict (K := K) = P} ↦
    (toPrime Q.2).asIdeal).insert ⊥).subset fun I hI ↦ ?_
  by_cases hb : I = ⊥
  · exact Or.inl hb
  refine Or.inr ⟨⟨placeOfPrime ⟨I, hI, hb⟩, restrict_placeOfPrime _⟩, ?_⟩
  simp only [toPrime_placeOfPrime]

instance (P : Place k K) : IsPrincipalIdealRing (intClo L P) :=
  IsPrincipalIdealRing.of_finite_primes finite_primes_intClo

end Dedekind

/-! ### The complementary module -/

variable (L) in
/-- `z` lies in the complementary module `C_P = {z | Tr(z O'_P) ⊆ O_P}`. -/
def IsCodiff (P : Place k K) (z : L) : Prop :=
  ∀ y ∈ intClo L P, Algebra.trace K L (z * y) ∈ P.1

section Codiff

variable [Algebra.IsSeparable K L] {P : Place k K}

theorem isCodiff_one : IsCodiff L P 1 := by
  intro y hy
  rw [one_mul]
  have hint : IsIntegral P.1 (Algebra.trace K L y) := Algebra.isIntegral_trace hy
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hr]
  exact r.2

/-- `C_P` is Mathlib's dual of `O'_P` (the inverse of the different ideal). -/
theorem isCodiff_iff_mem_dual {z : L} : IsCodiff L P z ↔
    z ∈ FractionalIdeal.dual P.1 K (1 : FractionalIdeal (nonZeroDivisors (intClo L P)) L) := by
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (intClo L P)) L) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h1]
  constructor
  · intro h a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    exact ⟨⟨_, h s s.2⟩, rfl⟩
  · intro h y hy
    obtain ⟨⟨r, hr⟩, hre⟩ := h y ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨y, hy⟩, rfl⟩)
    change r = _ at hre
    rw [Algebra.traceForm_apply] at hre
    rw [← hre]; exact hr

variable (L P) in
theorem exists_codiffGen : ∃ c : L, c ≠ 0 ∧ ∀ z : L,
    IsCodiff L P z ↔ ∃ s ∈ intClo L P, z = c * s := by
  set S := intClo L P
  set I := FractionalIdeal.dual P.1 K (1 : FractionalIdeal (nonZeroDivisors S) L)
  obtain ⟨c, hc⟩ := (inferInstance : (I : Submodule S L).IsPrincipal)
  have hmem : ∀ z : L, z ∈ I ↔ ∃ s ∈ S, z = c * s := by
    intro z
    rw [← FractionalIdeal.mem_coe, hc, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, s.2, by rw [Algebra.smul_def, mul_comm]; rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  have hiff : ∀ z : L, IsCodiff L P z ↔ z ∈ I := fun z ↦ isCodiff_iff_mem_dual
  refine ⟨c, fun h0 ↦ ?_, fun z ↦ (hiff z).trans (hmem z)⟩
  obtain ⟨s, -, hs⟩ := (hmem 1).mp ((hiff 1).mp isCodiff_one)
  rw [h0, zero_mul] at hs
  exact one_ne_zero hs

variable (L P) in
/-- A generator `c_P` of the complementary module: `C_P = c_P O'_P`. -/
noncomputable def codiffGen : L := (exists_codiffGen L P).choose

theorem codiffGen_ne_zero : codiffGen L P ≠ 0 := (exists_codiffGen L P).choose_spec.1

theorem isCodiff_iff {z : L} : IsCodiff L P z ↔ ∃ s ∈ intClo L P, z = codiffGen L P * s :=
  (exists_codiffGen L P).choose_spec.2 z

/-- `z ∈ C_P ↔ ∀ Q | P, ord_Q z ≥ ord_Q c_P`. -/
theorem isCodiff_iff_ord {z : L} : IsCodiff L P z ↔
    ∀ Q : Place k L, Q.restrict (K := K) = P → z = 0 ∨ Q.ord (codiffGen L P) ≤ Q.ord z := by
  have hc := codiffGen_ne_zero (L := L) (P := P)
  rw [isCodiff_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩ Q hQ
    by_cases hs0 : s = 0
    · exact Or.inl (by rw [hs0, mul_zero])
    refine Or.inr ?_
    rw [Q.ord_mul hc hs0]
    have := Q.ord_nonneg_of_mem (mem_of_mem_intClo hQ hs)
    omega
  · intro h
    refine ⟨z / codiffGen L P, mem_intClo_iff.mpr fun Q hQ ↦ ?_, by field_simp⟩
    rcases h Q hQ with h0 | h1
    · rw [h0, zero_div]; exact Q.1.zero_mem
    by_cases hz : z = 0
    · rw [hz, zero_div]; exact Q.1.zero_mem
    refine Q.mem_of_ord_nonneg ?_
    rw [Q.ord_div hz hc]
    omega

theorem isCodiff_mul {z y : L} (hz : IsCodiff L P z) (hy : y ∈ intClo L P) :
    IsCodiff L P (z * y) := fun y' hy' ↦ by
  rw [mul_assoc]; exact hz _ ((intClo L P).mul_mem hy hy')

/-- `ord_Q c_P ≤ 0`, i.e. the different exponent `d(Q|P) = -ord_Q c_P` is nonnegative. -/
theorem ord_codiffGen_nonpos {Q : Place k L} (hQ : Q.restrict (K := K) = P) :
    Q.ord (codiffGen L P) ≤ 0 := by
  rcases isCodiff_iff_ord.mp isCodiff_one Q hQ with h | h
  · exact absurd h one_ne_zero
  · simpa using h

theorem trace_mem_of_isCodiff {z : L} (hz : IsCodiff L P z) : Algebra.trace K L z ∈ P.1 := by
  simpa using hz 1 (intClo L P).one_mem

theorem trace_algebraMap_mul (a : K) (x : L) :
    Algebra.trace K L (algebraMap K L a * x) = a * Algebra.trace K L x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- **`Tr(C_P) = O_P`**. -/
theorem exists_isCodiff_trace_eq {u : K} (hu : u ∈ P.1) :
    ∃ z : L, IsCodiff L P z ∧ Algebra.trace K L z = u := by
  -- first an element of `C_P` whose trace is a unit of `O_P`
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have key : ∃ z : L, IsCodiff L P z ∧ Algebra.trace K L z ≠ 0 ∧
      P.ord (Algebra.trace K L z) = 0 := by
    by_contra hcon
    push Not at hcon
    -- then `π⁻¹ C_P ⊆ C_P`
    have hsub : IsCodiff L P (algebraMap K L π⁻¹ * codiffGen L P) := by
      intro y hy
      have hzy := isCodiff_mul (isCodiff_iff.mpr ⟨1, (intClo L P).one_mem, (mul_one _).symm⟩) hy
      rw [mul_assoc, trace_algebraMap_mul]
      set t := Algebra.trace K L (codiffGen L P * y)
      have ht : t ∈ P.1 := trace_mem_of_isCodiff hzy
      by_cases ht0 : t = 0
      · rw [ht0, mul_zero]; exact P.1.zero_mem
      have ht1 := hcon _ hzy ht0
      have ht2 := P.ord_nonneg_of_mem ht
      refine P.mem_of_ord_nonneg ?_
      rw [P.ord_mul (inv_ne_zero hπ0) ht0, P.ord_inv, hπ]
      have := lt_of_le_of_ne ht2 (Ne.symm ht1)
      linarith
    obtain ⟨s, hs, hse⟩ := isCodiff_iff.mp hsub
    have hc := codiffGen_ne_zero (L := L) (P := P)
    have hsπ : s = algebraMap K L π⁻¹ := by
      rw [mul_comm] at hse
      exact (mul_left_cancel₀ hc hse).symm
    -- `π⁻¹` would be integral over `O_P`
    have hint : IsIntegral P.1 (algebraMap K L π⁻¹) := hsπ ▸ hs
    have hintK : IsIntegral P.1 π⁻¹ :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom P.1 K L)
        (algebraMap K L).injective).mp hint
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintK
    have hmem : π⁻¹ ∈ P.1 := by rw [← hr]; exact r.2
    have := P.ord_nonneg_of_mem hmem
    rw [P.ord_inv, hπ] at this
    omega
  obtain ⟨z, hz, ht0, ht⟩ := key
  set t := Algebra.trace K L z
  refine ⟨algebraMap K L (u / t) * z, ?_, ?_⟩
  · intro y hy
    rw [mul_assoc, trace_algebraMap_mul]
    refine P.1.mul_mem _ _ ?_ (hz y hy)
    by_cases hu0 : u = 0
    · rw [hu0, zero_div]; exact P.1.zero_mem
    refine P.mem_of_ord_nonneg ?_
    rw [P.ord_div hu0 ht0, ht]
    have := P.ord_nonneg_of_mem hu
    omega
  · rw [trace_algebraMap_mul, div_mul_cancel₀ _ ht0]


/-- `ord_Q q = 1` for a generator `q` of the prime of `O'_P` below `Q`, and `ord_{Q'} q = 0` for
the other places `Q'` above `P`. -/
theorem exists_prime_gen {Q : Place k L} (hQ : Q.restrict (K := K) = P) :
    ∃ q : L, q ≠ 0 ∧ q ∈ intClo L P ∧ Q.ord q = 1 ∧
      ∀ Q' : Place k L, Q'.restrict (K := K) = P → Q' ≠ Q → Q'.ord q = 0 := by
  set v := toPrime hQ
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.principal v.asIdeal :
    ∃ q, v.asIdeal = Submodule.span (intClo L P) {q})
  have hq' : v.asIdeal = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by rw [hq', Ideal.span_singleton_eq_bot.mpr rfl])
  have hqL : (q : L) ≠ 0 := fun h ↦ hq0 (Subtype.ext h)
  refine ⟨q, hqL, q.2, ?_, fun Q' hQ' hne ↦ ?_⟩
  · rw [← placeOfPrime_toPrime hQ, ord_placeOfPrime]
    change -WithZero.log (v.valuation L (algebraMap (intClo L P) L q)) = 1
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hq0, ← hq', multiplicity_self,
      WithZero.log_exp]
    simp
  · have hqv : q ∉ (toPrime hQ').asIdeal := by
      intro hmem
      apply hne
      have hle : v.asIdeal ≤ (toPrime hQ').asIdeal := by
        rw [hq', Ideal.span_le, Set.singleton_subset_iff]; exact hmem
      have heq : v = toPrime hQ' :=
        HeightOneSpectrum.ext (v.isMaximal.eq_of_le (toPrime hQ').isMaximal.ne_top hle)
      rw [← placeOfPrime_toPrime hQ', ← heq, placeOfPrime_toPrime]
    rw [mem_toPrime_iff] at hqv
    have hmem : (q : L) ∈ Q'.1 := mem_of_mem_intClo hQ' q.2
    have hnn := Q'.ord_nonneg_of_mem hmem
    by_contra h0
    exact hqv ((Q'.ord_pos_iff).mp (lt_of_le_of_ne hnn (Ne.symm h0))).2

/-- **Sharpness of `C_P` at `Q`**: an element with `ord_Q z ≥ ord_Q c_P - 1`,
`ord_{Q'} z ≥ ord_{Q'} c_P` at the other places above `P`, and `Tr z ∉ O_P`. -/
theorem exists_sharp {Q : Place k L} (hQ : Q.restrict (K := K) = P) :
    ∃ z : L, (∀ Q' : Place k L, Q'.restrict (K := K) = P → Q' ≠ Q →
        Q'.ord (codiffGen L P) ≤ Q'.ord z) ∧
      Q.ord (codiffGen L P) - 1 ≤ Q.ord z ∧ Algebra.trace K L z ∉ P.1 := by
  obtain ⟨q, hq0, -, hqQ, hqQ'⟩ := exists_prime_gen hQ
  have hc := codiffGen_ne_zero (L := L) (P := P)
  have hnot : ¬ IsCodiff L P (codiffGen L P * q⁻¹) := by
    intro h
    obtain ⟨s, hs, hse⟩ := isCodiff_iff.mp h
    have : q⁻¹ = s := mul_left_cancel₀ hc hse
    have hmem := mem_of_mem_intClo hQ hs
    rw [← this] at hmem
    have := Q.ord_nonneg_of_mem hmem
    rw [Q.ord_inv, hqQ] at this
    omega
  simp only [IsCodiff, not_forall] at hnot
  obtain ⟨y, hy, htr⟩ := hnot
  have hz0 : codiffGen L P * q⁻¹ * y ≠ 0 := by
    intro h; rw [h, map_zero] at htr; exact htr P.1.zero_mem
  have hy0 : y ≠ 0 := by rintro rfl; simp at hz0
  have hord : ∀ Q' : Place k L, Q'.restrict (K := K) = P →
      Q'.ord (codiffGen L P * q⁻¹ * y) = Q'.ord (codiffGen L P) - Q'.ord q + Q'.ord y := by
    intro Q' _
    rw [Q'.ord_mul (mul_ne_zero hc (inv_ne_zero hq0)) hy0, Q'.ord_mul hc (inv_ne_zero hq0),
      Q'.ord_inv]
    ring
  refine ⟨_, fun Q' hQ' hne ↦ ?_, ?_, htr⟩
  · rw [hord Q' hQ', hqQ' Q' hQ' hne]
    have := Q'.ord_nonneg_of_mem (mem_of_mem_intClo hQ' hy)
    omega
  · rw [hord Q hQ, hqQ]
    have := Q.ord_nonneg_of_mem (mem_of_mem_intClo hQ hy)
    omega

end Codiff

end WeilCurves.FunctionField
