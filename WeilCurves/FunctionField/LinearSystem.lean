/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Riemann
import WeilCurves.FunctionField.Residue
import WeilCurves.FunctionField.ZerosPoles

/-!
# Values of functions and linear systems over an algebraically closed field

For a function field `K / k` over an **algebraically closed** field `k` (the function field of a
proper curve `X` over `k`), this file proves the Riemann–Roch-level facts behind Uchida's
reconstruction of the additive structure of `K` ([AbsTopIII], Propositions 1.1 and 1.2; cited
from `~/iut-scratch/papers/txt/Topics in Absolute Anabelian Geometry III.txt`):

* **Values.** `Place.IsValue P f c` ("`f(P) = c`"): `f - c` lies in the maximal ideal of `P`.
  Every `f ∈ O_P` has a unique value (`Place.exists_isValue`, `Place.IsValue.unique`), values are
  additive and multiplicative, and `Place.value P : K → k` is the value function. `ord_P f = 0`
  iff the value of `f` at `P` is nonzero (`Place.ord_eq_zero_iff_isValue`).
* **Constants.** The elements of `K` algebraic over `k` are the elements of `k`
  (`isAlgebraic_iff_exists_algebraMap`), and there are infinitely many places
  (`Place.infinite`), so every finite set of places can be avoided (`Place.exists_notMem`).
* **Proposition 1.1(ii)** (l.1653–1655): "The integer `l(D) ≥ 0` is equal to the smallest
  nonnegative integer `d` such that there exists an effective divisor `E` of degree `d` on `X` for
  which `Γ×(D − E) = ∅`": `Divisor.ell_eq_sInf`.
* **Proposition 1.2(i)** (l.1660–1663): "There exist distinct points `x, y1, y2 ∈ X(k)`, together
  with a divisor `D` on `X` such that `x, y1, y2 ∉ Supp(D)` […], such that `l(D) = 2`,
  `l(D − E) = 0`, for any effective divisor `E = e1 + e2`, where `e1 ≠ e2`,
  `{e1, e2} ⊆ {x, y1, y2}`": `Divisor.exists_uchidaConfig`, following the proof (l.1680–1690).
* **Propositions 1.2(ii), (iii)** reduce to the two-point evaluation statement
  `Divisor.existsUnique_isValue_two`: if `l(D) = 2`, `y1 ≠ y2 ∉ Supp(D)` and `l(D − y1 − y2) = 0`,
  then every pair of values `(a₁, a₂) ∈ k²` is taken at `(y1, y2)` by a unique `f ∈ L(D)`.
-/

open IsLocalRing

namespace WeilCurves.FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Values of functions at places -/

namespace Place

/-- **`f(P) = c`**: `f - c` lies in the maximal ideal of the place `P`. -/
def IsValue (P : Place k K) (f : K) (c : k) : Prop := f - algebraMap k K c ∈ P.1.nonunits

variable {P : Place k K} {f g : K} {a b c : k}

variable (P) in
lemma mul_mem_nonunits {x m : K} (hx : x ∈ P.1) (hm : m ∈ P.1.nonunits) :
    x * m ∈ P.1.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hm ⊢
  rw [map_mul]
  calc P.1.valuation x * P.1.valuation m ≤ 1 * P.1.valuation m :=
        mul_le_mul_left ((P.1.valuation_le_one_iff x).mpr hx) _
    _ < 1 := by rwa [one_mul]

lemma IsValue.mem (h : P.IsValue f c) : f ∈ P.1 := by
  have := add_mem (P.1.nonunits_subset h) (P.algebraMap_mem c)
  rwa [sub_add_cancel] at this

variable (P) in
lemma isValue_algebraMap (c : k) : P.IsValue (algebraMap k K c) c := by
  simp [IsValue, zero_mem]

lemma IsValue.add (hf : P.IsValue f a) (hg : P.IsValue g b) : P.IsValue (f + g) (a + b) := by
  have := add_mem hf hg
  rw [IsValue, map_add]
  convert this using 1
  ring

lemma IsValue.neg (hf : P.IsValue f a) : P.IsValue (-f) (-a) := by
  have := neg_mem hf
  rw [IsValue, map_neg]
  convert this using 1
  ring

lemma IsValue.sub (hf : P.IsValue f a) (hg : P.IsValue g b) : P.IsValue (f - g) (a - b) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma IsValue.mul (hf : P.IsValue f a) (hg : P.IsValue g b) : P.IsValue (f * g) (a * b) := by
  have h1 := P.mul_mem_nonunits hf.mem hg
  have h2 := P.mul_mem_nonunits (P.algebraMap_mem b) hf
  have := add_mem h1 h2
  rw [IsValue, map_mul]
  convert this using 1
  ring

lemma IsValue.smul (hf : P.IsValue f a) (c : k) : P.IsValue (c • f) (c * a) := by
  rw [Algebra.smul_def]
  exact (P.isValue_algebraMap c).mul hf

variable (P) in
lemma algebraMap_mem_nonunits_iff [PerfectField k] [IsFunctionField k K] :
    algebraMap k K c ∈ P.1.nonunits ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    have h0 : algebraMap k K c ≠ 0 := by simpa using hc
    have := (P.ord_pos_iff (f := algebraMap k K c)).mpr ⟨h0, h⟩
    rw [P.ord_algebraMap_base] at this
    exact lt_irrefl _ this
  · rintro rfl
    simp [zero_mem]

lemma IsValue.unique [PerfectField k] [IsFunctionField k K] (ha : P.IsValue f a)
    (hb : P.IsValue f b) : a = b := by
  have := sub_mem hb ha
  rw [show f - algebraMap k K b - (f - algebraMap k K a) = algebraMap k K (a - b) by
    rw [map_sub]; ring, P.algebraMap_mem_nonunits_iff] at this
  exact sub_eq_zero.mp this

variable (P) in
lemma isValue_zero_iff : P.IsValue f 0 ↔ f ∈ P.1.nonunits := by
  simp [IsValue]

section AlgClosed

variable (P) [IsAlgClosed k] [IsFunctionField k K]

/-- **Every function regular at `P` has a value at `P`** (the residue field of `P` is `k`). -/
theorem exists_isValue (hf : f ∈ P.1) : ∃ c : k, P.IsValue f c := by
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := P.ResidueField)
  obtain ⟨a, ha⟩ := hb.2 (P.residue ⟨f, hf⟩)
  refine ⟨a, ?_⟩
  have hmem : f - algebraMap k K a ∈ P.1 := P.1.sub_mem hf (P.algebraMap_mem a)
  have h0 : P.residue ⟨_, hmem⟩ = 0 := by
    have h1 : (⟨_, hmem⟩ : P.1) = ⟨f, hf⟩ - P.baseHom a := rfl
    rw [h1, map_sub, ← Place.algebraMap_residueField, ← ha, sub_self]
  exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmem⟩)).mpr
    ((P.residue_eq_zero_iff).mp h0)

open Classical in
/-- **The value `f(P) ∈ k`** of a function regular at `P` (junk value `0` otherwise). -/
noncomputable def value (f : K) : k :=
  if hf : f ∈ P.1 then (P.exists_isValue hf).choose else 0

theorem isValue_value (hf : f ∈ P.1) : P.IsValue f (P.value f) := by
  rw [value, dif_pos hf]
  exact (P.exists_isValue hf).choose_spec

theorem value_eq_of_isValue (h : P.IsValue f c) : P.value f = c :=
  (P.isValue_value h.mem).unique h

theorem isValue_iff_value_eq (hf : f ∈ P.1) : P.IsValue f c ↔ P.value f = c :=
  ⟨P.value_eq_of_isValue, fun h ↦ h ▸ P.isValue_value hf⟩

/-- `ord_P f = 0` iff `f` has a nonzero value at `P`. -/
theorem ord_eq_zero_iff_isValue (hf : f ≠ 0) :
    P.ord f = 0 ↔ ∃ c : k, c ≠ 0 ∧ P.IsValue f c := by
  constructor
  · intro h
    have hmem : f ∈ P.1 := P.mem_of_ord_nonneg h.ge
    obtain ⟨c, hc⟩ := P.exists_isValue hmem
    refine ⟨c, fun hc0 ↦ ?_, hc⟩
    subst hc0
    have := (P.ord_pos_iff (f := f)).mpr ⟨hf, (P.isValue_zero_iff).mp hc⟩
    omega
  · rintro ⟨c, hc0, hc⟩
    have hmem := hc.mem
    have h0 := P.ord_nonneg_of_mem hmem
    by_contra hne
    have hpos : 0 < P.ord f := lt_of_le_of_ne h0 (Ne.symm hne)
    have hnu := ((P.ord_pos_iff (f := f)).mp hpos).2
    exact hc0 ((P.isValue_zero_iff.mpr hnu).unique hc).symm

omit [IsAlgClosed k] [IsFunctionField k K] in
/-- Values in terms of principal units: for `c ≠ 0`, `f(P) = c` iff `f / c ≡ 1` at `P`. -/
theorem isValue_iff_div_sub_one_mem (hc : c ≠ 0) :
    P.IsValue f c ↔ f / algebraMap k K c - 1 ∈ P.1.nonunits := by
  have hc' : algebraMap k K c ≠ 0 := by simpa using hc
  have hinv : (algebraMap k K c)⁻¹ ∈ P.1 := by rw [← map_inv₀]; exact P.algebraMap_mem _
  have e : f / algebraMap k K c - 1 = (algebraMap k K c)⁻¹ * (f - algebraMap k K c) := by
    field_simp
  rw [e, IsValue]
  refine ⟨P.mul_mem_nonunits hinv, fun h ↦ ?_⟩
  have := P.mul_mem_nonunits (P.algebraMap_mem c) h
  rwa [← mul_assoc, mul_inv_cancel₀ hc', one_mul] at this

end AlgClosed

end Place

/-! ### Constants and the infinitude of places -/

section AlgClosed

variable [IsAlgClosed k] [IsFunctionField k K]

omit [IsFunctionField k K] in
/-- Over an algebraically closed field, the constants of `K` are the elements of `k`. -/
theorem isAlgebraic_iff_exists_algebraMap {f : K} :
    IsAlgebraic k f ↔ ∃ c : k, algebraMap k K c = f := by
  refine ⟨fun hf ↦ ?_, fun ⟨c, hc⟩ ↦ hc ▸ isAlgebraic_algebraMap c⟩
  have hy : f ∈ integralClosure k K := hf.isIntegral
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := integralClosure k K)).2 ⟨f, hy⟩
  exact ⟨c, congrArg Subtype.val hc⟩

/-- A nonzero `f ∈ K` is a constant iff `ord_P f = 0` at every place. -/
theorem exists_algebraMap_iff_forall_ord_eq_zero {f : K} :
    (∃ c : k, algebraMap k K c = f) ↔ ∀ P : Place k K, P.ord f = 0 := by
  rw [← isAlgebraic_iff_exists_algebraMap, Place.isAlgebraic_iff_forall_ord_eq_zero]

namespace Place

/-- Over an algebraically closed field, every place has degree one. -/
theorem deg_eq_one_of_isAlgClosed (P : Place k K) : P.deg = 1 := by
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := P.ResidueField)
  have e := LinearEquiv.ofBijective (Algebra.linearMap k P.ResidueField) hb
  rw [Place.deg, ← e.finrank_eq, Module.finrank_self]

/-- **There are infinitely many places**: `c ↦` (a zero of `t - c`) is injective. -/
theorem infinite : Infinite (Place k K) := by
  obtain ⟨t, ht⟩ := exists_transcendental k K
  have hz : ∀ c : k, ∃ P : Place k K, 0 < P.ord (t - algebraMap k K c) := fun c ↦
    exists_ord_pos (fun h ↦ ht (by
      have := h.add (isAlgebraic_algebraMap (R := k) (A := K) c)
      rwa [sub_add_cancel] at this))
  choose Z hZ using hz
  refine Infinite.of_injective Z fun c c' h ↦ ?_
  have h1 := ((Z c).ord_pos_iff.mp (hZ c)).2
  have h2 := ((Z c').ord_pos_iff.mp (hZ c')).2
  rw [← h] at h2
  exact (Place.IsValue.unique h2 h1).symm

/-- Every finite set of places can be avoided. -/
theorem exists_notMem_of_finite {S : Set (Place k K)} (hS : S.Finite) : ∃ P, P ∉ S := by
  have := infinite (k := k) (K := K)
  exact (hS.infinite_compl.nonempty)

/-- There is a place outside a finite set at which finitely many given nonzero functions have
order `0`. -/
theorem exists_ord_eq_zero {S : Set (Place k K)} (hS : S.Finite) (s : Finset K) :
    ∃ P, P ∉ S ∧ ∀ f ∈ s, P.ord f = 0 := by
  have hfin : (S ∪ ⋃ f ∈ s, {P : Place k K | P.ord f ≠ 0}).Finite :=
    hS.union (s.finite_toSet.biUnion fun f _ ↦ finite_setOf_ord_ne_zero f)
  obtain ⟨P, hP⟩ := exists_notMem_of_finite hfin
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
    not_not] at hP
  exact ⟨P, hP.1, fun f hf ↦ hP.2 f hf⟩

end Place

/-! ### Linear systems -/

namespace Divisor

open Place

/-- `L(A) ⊆ O_P` if `P ∉ Supp(A)`. -/
lemma mem_place_of_mem_L {A : Divisor k K} {P : Place k K} (hA : A P = 0) {f : K}
    (hf : f ∈ L A) : f ∈ P.1 := by
  rcases hf with rfl | hf
  · exact P.1.zero_mem
  exact P.mem_of_ord_nonneg (by simpa [hA] using hf P)

/-- **Dropping a non-base point**: if `s ∈ L(B)` is nonzero with `ord_P s = -B(P)`, then
`l(B − P) = l(B) − 1`. -/
theorem ell_sub_single_add_one {B : Divisor k K} {P : Place k K} {s : K} (hs : s ∈ L B)
    (hs0 : s ≠ 0) (hP : P.ord s = -B P) : ell (B - Finsupp.single P 1) + 1 = ell B := by
  have hle : B - Finsupp.single P 1 ≤ B :=
    sub_le_self _ (Finsupp.single_nonneg.mpr zero_le_one)
  have h1 := ell_le_of_le hle
  rw [deg_sub, deg_single, deg_eq_one_of_isAlgClosed] at h1
  have hnot : s ∉ L (B - Finsupp.single P 1) := by
    intro h
    rcases h with h | h
    · exact hs0 h
    have := h P
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same] at this
    omega
  have hlt : L (B - Finsupp.single P 1) < L B :=
    lt_of_le_of_ne (L_mono hle) fun h ↦ hnot (h ▸ hs)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  change ell _ < ell _ at h2
  push_cast at h1
  omega

/-- A nonzero `s ∈ L(B)` has `ord_P s = -B(P)` away from a finite set of places. -/
lemma finite_setOf_ord_ne (B : Divisor k K) (s : K) :
    {P : Place k K | P.ord s ≠ -B P}.Finite := by
  refine ((B.support.finite_toSet).union (finite_setOf_ord_ne_zero s)).subset fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq] at hP
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq, not_or,
    not_not, Set.mem_setOf_eq] at h
  exact hP (by rw [h.1, h.2, neg_zero])

/-- For a nonzero `s ∈ L(B)` and a finite set `S`, some `P ∉ S` with `P ∉ Supp(B)` has
`ord_P s = 0`. -/
lemma exists_place_ord_eq_zero (B : Divisor k K) (s : K)
    {S : Set (Place k K)} (hS : S.Finite) : ∃ P, P ∉ S ∧ B P = 0 ∧ P.ord s = 0 := by
  obtain ⟨P, hP⟩ := exists_notMem_of_finite ((hS.union (finite_setOf_ord_ne B s)).union
    B.support.finite_toSet)
  simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq,
    not_or, not_not] at hP
  exact ⟨P, hP.1.1, hP.2, by rw [hP.1.2, hP.2, neg_zero]⟩

/-- `l(A) ≤ l(A − E) + deg E` for effective `E`. -/
theorem ell_le_ell_sub_add_deg (A : Divisor k K) {E : Divisor k K} (hE : 0 ≤ E) :
    (ell A : ℤ) ≤ ell (A - E) + E.deg := by
  have := ell_le_of_le (sub_le_self A hE)
  rw [deg_sub, sub_sub_cancel] at this
  exact this

/-- There is an effective `E` of degree `l(A)` with `L(A − E) = 0`. -/
theorem exists_nonneg_deg_eq_ell (A : Divisor k K) :
    ∃ E : Divisor k K, 0 ≤ E ∧ E.deg = ell A ∧ L (A - E) = ⊥ := by
  induction hn : ell A generalizing A with
  | zero => exact ⟨0, le_rfl, by simp, by rw [sub_zero]; exact ell_eq_zero_iff.mp hn⟩
  | succ n ih =>
    obtain ⟨s, hs, hs0⟩ := exists_ne_zero_mem_L (A := A) (by omega)
    obtain ⟨P, -, hAP, hP⟩ := exists_place_ord_eq_zero A s Set.finite_empty
    have hd := ell_sub_single_add_one hs hs0 (by rw [hP, hAP, neg_zero])
    obtain ⟨E, hE, hdeg, hL⟩ := ih (A - Finsupp.single P 1) (by omega)
    refine ⟨E + Finsupp.single P 1, add_nonneg hE (Finsupp.single_nonneg.mpr zero_le_one), ?_,
      by rwa [← sub_sub, sub_right_comm]⟩
    rw [deg_add, deg_single, deg_eq_one_of_isAlgClosed, hdeg]
    push_cast
    ring

/-- **[AbsTopIII], Proposition 1.1(ii)** (l.1653–1655): `l(D)` is the smallest `d ≥ 0` such that
`Γ×(D − E) = ∅` (i.e. `L(D − E) = 0`) for an effective divisor `E` of degree `d`. -/
theorem ell_eq_sInf (A : Divisor k K) :
    ell A = sInf {d : ℕ | ∃ E : Divisor k K, 0 ≤ E ∧ E.deg = d ∧ L (A - E) = ⊥} := by
  obtain ⟨E, hE, hdeg, hL⟩ := exists_nonneg_deg_eq_ell A
  refine le_antisymm (le_csInf ⟨_, E, hE, hdeg, hL⟩ ?_) (Nat.sInf_le ⟨E, hE, hdeg, hL⟩)
  rintro d ⟨E', hE', hdeg', hL'⟩
  have := ell_le_ell_sub_add_deg A hE'
  rw [ell_eq_zero_iff.mpr hL', hdeg'] at this
  omega

/-- From `l(A) ≥ m` one can reach `l = m` by subtracting points. -/
theorem exists_le_ell_eq (A : Divisor k K) {m : ℕ} (hm : m ≤ ell A) :
    ∃ A' : Divisor k K, ell A' = m := by
  induction hn : ell A - m generalizing A with
  | zero => exact ⟨A, by omega⟩
  | succ n ih =>
    obtain ⟨s, hs, hs0⟩ := exists_ne_zero_mem_L (A := A) (by omega)
    obtain ⟨P, -, hAP, hP⟩ := exists_place_ord_eq_zero A s Set.finite_empty
    have hd := ell_sub_single_add_one hs hs0 (by rw [hP, hAP, neg_zero])
    exact ih (A - Finsupp.single P 1) (by omega) (by omega)

/-- There is a divisor with `l = 2` (Riemann's inequality). -/
theorem exists_ell_eq_two : ∃ A : Divisor k K, ell A = 2 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Place k K))
  have h := riemann_inequality (Finsupp.single P (riemannConst k K + 2))
  rw [deg_single, deg_eq_one_of_isAlgClosed] at h
  exact exists_le_ell_eq (Finsupp.single P (riemannConst k K + 2)) (m := 2)
    (by push_cast at h; omega)

/-- **[AbsTopIII], Proposition 1.2(i)** (l.1660–1663; proof l.1680–1690): there are distinct
places `x, y₁, y₂ ∉ Supp(D)` and a divisor `D` with `l(D) = 2` and `L(D − e₁ − e₂) = 0` for all
distinct `e₁, e₂ ∈ {x, y₁, y₂}`. -/
theorem exists_uchidaConfig : ∃ (D : Divisor k K) (x y₁ y₂ : Place k K),
    x ≠ y₁ ∧ x ≠ y₂ ∧ y₁ ≠ y₂ ∧ D x = 0 ∧ D y₁ = 0 ∧ D y₂ = 0 ∧ ell D = 2 ∧
      L (D - Finsupp.single x 1 - Finsupp.single y₁ 1) = ⊥ ∧
      L (D - Finsupp.single x 1 - Finsupp.single y₂ 1) = ⊥ ∧
      L (D - Finsupp.single y₁ 1 - Finsupp.single y₂ 1) = ⊥ := by
  obtain ⟨D, hD⟩ := exists_ell_eq_two (k := k) (K := K)
  -- `x`: a point where a section of `O(D)` does not vanish
  obtain ⟨f, hf, hf0⟩ := exists_ne_zero_mem_L (A := D) (by omega)
  obtain ⟨x, -, hDx, hfx⟩ := exists_place_ord_eq_zero D f Set.finite_empty
  have hx := ell_sub_single_add_one hf hf0 (by rw [hfx, hDx, neg_zero])
  -- `y₁`: a point where a section `s` of `O(D − x)` and `f` do not vanish
  obtain ⟨s, hs, hs0⟩ := exists_ne_zero_mem_L (A := D - Finsupp.single x 1) (by omega)
  obtain ⟨y₁, hy₁S, hDy₁, hsy₁⟩ := exists_place_ord_eq_zero D s
    ((Set.finite_singleton x).union (finite_setOf_ord_ne D f))
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or, not_not] at hy₁S
  have hxy₁ : x ≠ y₁ := Ne.symm hy₁S.1
  have hy₁ := ell_sub_single_add_one hf hf0 (P := y₁) hy₁S.2
  -- `y₂`: a point where `s` and a section `t` of `O(D − y₁)` do not vanish
  obtain ⟨t, ht, ht0⟩ := exists_ne_zero_mem_L (A := D - Finsupp.single y₁ 1) (by omega)
  obtain ⟨y₂, hy₂S, hDy₂, hsy₂⟩ := exists_place_ord_eq_zero D s
    (((Set.finite_singleton x).union (Set.finite_singleton y₁)).union
      (finite_setOf_ord_ne (D - Finsupp.single y₁ 1) t))
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or, not_not] at hy₂S
  have hxy₂ : x ≠ y₂ := Ne.symm hy₂S.1.1
  have hy₁₂ : y₁ ≠ y₂ := Ne.symm hy₂S.1.2
  -- the three vanishing statements
  have e1 := ell_sub_single_add_one hs hs0 (P := y₁)
    (by simp [hxy₁, hsy₁, hDy₁])
  have e2 := ell_sub_single_add_one hs hs0 (P := y₂)
    (by simp [hxy₂, hsy₂, hDy₂])
  have e3 := ell_sub_single_add_one ht ht0 (P := y₂) hy₂S.2
  refine ⟨D, x, y₁, y₂, hxy₁, hxy₂, hy₁₂, hDx, hDy₁, hDy₂, hD, ?_, ?_, ?_⟩ <;>
    rw [← ell_eq_zero_iff] <;> omega

/-- **Two-point evaluation** (behind [AbsTopIII], Proposition 1.2(ii), (iii)): if `l(D) = 2`,
`y₁ ≠ y₂ ∉ Supp(D)` and `L(D − y₁ − y₂) = 0`, then for all `a₁, a₂ ∈ k` there is a unique
`f ∈ L(D)` with `f(y₁) = a₁` and `f(y₂) = a₂`. -/
theorem existsUnique_isValue_two {D : Divisor k K} {y₁ y₂ : Place k K} (h12 : y₁ ≠ y₂)
    (hD₁ : D y₁ = 0) (hD₂ : D y₂ = 0) (hD : ell D = 2)
    (hL : L (D - Finsupp.single y₁ 1 - Finsupp.single y₂ 1) = ⊥) (a₁ a₂ : k) :
    ∃! f, f ∈ L D ∧ y₁.IsValue f a₁ ∧ y₂.IsValue f a₂ := by
  -- uniqueness
  have huniq : ∀ f g, f ∈ L D → g ∈ L D → ∀ b₁ b₂ : k, y₁.IsValue f b₁ → y₂.IsValue f b₂ →
      y₁.IsValue g b₁ → y₂.IsValue g b₂ → f = g := by
    intro f g hf hg b₁ b₂ hf₁ hf₂ hg₁ hg₂
    have h₁ : y₁.IsValue (f - g) 0 := by simpa using hf₁.sub hg₁
    have h₂ : y₂.IsValue (f - g) 0 := by simpa using hf₂.sub hg₂
    have hfg : f - g ∈ L (D - Finsupp.single y₁ 1 - Finsupp.single y₂ 1) := by
      by_cases h0 : f - g = 0
      · rw [h0]; exact zero_mem _
      have hm := sub_mem hf hg
      rcases hm with hm | hm
      · exact absurd hm h0
      refine Or.inr fun P ↦ ?_
      have hp₁ := (y₁.ord_pos_iff (f := f - g)).mpr ⟨h0, y₁.isValue_zero_iff.mp h₁⟩
      have hp₂ := (y₂.ord_pos_iff (f := f - g)).mpr ⟨h0, y₂.isValue_zero_iff.mp h₂⟩
      have := hm P
      simp only [Finsupp.coe_sub, Pi.sub_apply]
      by_cases e1 : y₁ = P
      · subst e1; simp [h12, hD₁] at this ⊢; omega
      by_cases e2 : y₂ = P
      · subst e2; simp [e1, hD₂] at this ⊢; omega
      simp [e1, e2]; omega
    rw [hL, Submodule.mem_bot, sub_eq_zero] at hfg
    exact hfg
  -- existence: the evaluation map `L(D) → k²` is injective, hence bijective
  let φ : L D →ₗ[k] k × k :=
    { toFun := fun f ↦ (y₁.value f, y₂.value f)
      map_add' := fun f g ↦ by
        have m₁ := fun h : K => mem_place_of_mem_L (P := y₁) hD₁ (f := h)
        have m₂ := fun h : K => mem_place_of_mem_L (P := y₂) hD₂ (f := h)
        simp only [Submodule.coe_add, Prod.mk_add_mk]
        rw [y₁.value_eq_of_isValue
            ((y₁.isValue_value (m₁ f f.2)).add (y₁.isValue_value (m₁ g g.2))),
          y₂.value_eq_of_isValue
            ((y₂.isValue_value (m₂ f f.2)).add (y₂.isValue_value (m₂ g g.2)))]
      map_smul' := fun c f ↦ by
        have m₁ := mem_place_of_mem_L (P := y₁) hD₁ f.2
        have m₂ := mem_place_of_mem_L (P := y₂) hD₂ f.2
        simp only [SetLike.val_smul, RingHom.id_apply, Prod.smul_mk, smul_eq_mul]
        rw [y₁.value_eq_of_isValue ((y₁.isValue_value m₁).smul c),
          y₂.value_eq_of_isValue ((y₂.isValue_value m₂).smul c)] }
  have hinj : Function.Injective φ := by
    intro f g hfg
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at hfg
    have m₁f := mem_place_of_mem_L (P := y₁) hD₁ f.2
    have m₂f := mem_place_of_mem_L (P := y₂) hD₂ f.2
    have m₁g := mem_place_of_mem_L (P := y₁) hD₁ g.2
    have m₂g := mem_place_of_mem_L (P := y₂) hD₂ g.2
    exact Subtype.ext (huniq f g f.2 g.2 _ _ (y₁.isValue_value m₁f) (y₂.isValue_value m₂f)
      (hfg.1 ▸ y₁.isValue_value m₁g) (hfg.2 ▸ y₂.isValue_value m₂g))
  have hsurj : Function.Surjective φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_prod, Module.finrank_self]
    exact hD
  obtain ⟨f, hf⟩ := hsurj (a₁, a₂)
  simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at hf
  refine ⟨f, ⟨f.2, hf.1 ▸ y₁.isValue_value (mem_place_of_mem_L hD₁ f.2),
    hf.2 ▸ y₂.isValue_value (mem_place_of_mem_L hD₂ f.2)⟩, fun g ⟨hg, hg₁, hg₂⟩ ↦ ?_⟩
  exact (huniq _ _ f.2 hg a₁ a₂ (hf.1 ▸ y₁.isValue_value (mem_place_of_mem_L hD₁ f.2))
    (hf.2 ▸ y₂.isValue_value (mem_place_of_mem_L hD₂ f.2)) hg₁ hg₂).symm

end Divisor

end AlgClosed

end WeilCurves.FunctionField
