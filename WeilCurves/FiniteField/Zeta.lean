/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FiniteField.ClassNumber
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The zeta function of a function field over a finite field

For a function field `K` over a finite field `k` with `q` elements, the zeta function is the
formal power series `Z(t) = ∑_{n ≥ 0} A_n t^n ∈ ℤ⟦t⟧`, where `A_n` is the number of effective
divisors of degree `n` (`WeilCurves.FunctionField.zeta`).

If `k` is the full constant field and **there is a divisor of degree `1`** (an explicit hypothesis
here; it holds by F. K. Schmidt's theorem, proved later from constant field extensions), then
`#Cl(n) = h` for every `n`, so `A_n (q - 1) = h (q^{n+1-g} - 1)` for `n > 2g - 2`, and
`(1 - t)(1 - q t) Z(t)` is a polynomial `L(t)` of degree `≤ 2g` with `L(0) = 1`
(`WeilCurves.FunctionField.exists_LPolynomial`).
-/

open PowerSeries

namespace WeilCurves.FunctionField

open Divisor

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]

variable (k K) in
/-- The zeta function `Z(t) = ∑ A_n t^n` as a formal power series over `ℤ`. -/
noncomputable def zeta : PowerSeries ℤ := PowerSeries.mk fun n ↦ (effCount k K n : ℤ)

omit [Finite k] [IsFunctionField k K] in
@[simp]
theorem coeff_zeta (n : ℕ) : coeff n (zeta k K) = effCount k K n := by
  simp [zeta]

omit [Finite k] [IsFunctionField k K] in
theorem integralClosure_eq_bot (hk : IsFullConstantField k K) : integralClosure k K = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  obtain ⟨c, hc⟩ := hk x (IsIntegral.isAlgebraic hx)
  exact Algebra.mem_bot.mpr ⟨c, hc⟩

theorem ell_zero_eq_one (hk : IsFullConstantField k K) : ell (0 : Divisor k K) = 1 := by
  rw [ell_zero, integralClosure_eq_bot hk, Subalgebra.finrank_bot]

/-- The genus is nonnegative (for `k` the full constant field). -/
theorem genus_nonneg (hk : IsFullConstantField k K) : 0 ≤ genus k K := by
  have := ell_canonical (k := k) (K := K)
  rw [ell_zero_eq_one hk] at this
  omega

/-- `A_0 = 1`: the only effective divisor of degree `0` is `0`. -/
theorem effCount_zero : effCount k K 0 = 1 := by
  have : effDeg k K 0 = {0} := by
    ext E
    simp only [effDeg, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hE, hdeg⟩
      by_contra h
      have := deg_pos_of_nonneg_of_ne_zero hE h
      omega
    · rintro rfl; exact ⟨le_rfl, deg_zero⟩
  rw [effCount, this, Nat.card_unique]

/-- With a divisor of degree `1`: `A_n (q - 1) = h (q^{n+1-g} - 1)` for `n > 2g - 2`. -/
theorem effCount_mul_eq (hk : IsFullConstantField k K) (hD : ∃ D : Divisor k K, D.deg = 1)
    {n : ℤ} (hn : 2 * genus k K - 2 < n) :
    (effCount k K n : ℤ) * (Nat.card k - 1) =
      classNumber k K * ((Nat.card k : ℤ) ^ (n + 1 - genus k K).toNat - 1) := by
  obtain ⟨D, hD⟩ := hD
  have h := effCount_mul_of_deg_gt (k := k) hk hn
  have hcl : Nat.card (Cl k K n) = classNumber k K := by
    have := card_Cl (D := n • D)
    rwa [deg_zsmul, hD, mul_one] at this
  rw [hcl] at h
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  have hqe : 1 ≤ Nat.card k ^ (n + 1 - genus k K).toNat := Nat.one_le_pow _ _ hq
  have := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast [Nat.cast_sub hq, Nat.cast_sub hqe] at this
  exact this

theorem coeff_succ_one_sub_C_mul_X_mul (a : ℤ) (φ : PowerSeries ℤ) (n : ℕ) :
    coeff (n + 1) ((1 - C a * X) * φ) = coeff (n + 1) φ - a * coeff n φ := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul]

theorem coeff_zero_one_sub_C_mul_X_mul (a : ℤ) (φ : PowerSeries ℤ) :
    coeff 0 ((1 - C a * X) * φ) = coeff 0 φ := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_zero_X_mul, mul_zero, sub_zero]

variable (k K) in
/-- `(1 - t)(1 - q t) Z(t)`. -/
noncomputable def zetaNumerator : PowerSeries ℤ :=
  (1 - C 1 * X) * ((1 - C (Nat.card k : ℤ) * X) * zeta k K)

omit [Finite k] [IsFunctionField k K] in
theorem coeff_zetaNumerator_add_two (n : ℕ) :
    coeff (n + 2) (zetaNumerator k K) =
      (effCount k K (n + 2) : ℤ) - (Nat.card k + 1) * effCount k K (n + 1) +
        Nat.card k * effCount k K n := by
  rw [zetaNumerator, coeff_succ_one_sub_C_mul_X_mul, coeff_succ_one_sub_C_mul_X_mul,
    coeff_succ_one_sub_C_mul_X_mul, coeff_zeta, coeff_zeta, coeff_zeta]
  simp only [Nat.cast_add, Nat.cast_one, one_mul]
  rw [show (n : ℤ) + 1 + 1 = n + 2 by ring]
  ring

omit [Finite k] [IsFunctionField k K] in
theorem coeff_zetaNumerator_one :
    coeff 1 (zetaNumerator k K) = (effCount k K 1 : ℤ) - (Nat.card k + 1) * effCount k K 0 := by
  rw [zetaNumerator, coeff_succ_one_sub_C_mul_X_mul, coeff_succ_one_sub_C_mul_X_mul,
    coeff_zero_one_sub_C_mul_X_mul, coeff_zeta, coeff_zeta]
  simp only [Nat.cast_zero, one_mul]
  ring_nf

theorem coeff_zetaNumerator_zero : coeff 0 (zetaNumerator k K) = 1 := by
  rw [zetaNumerator, coeff_zero_one_sub_C_mul_X_mul, coeff_zero_one_sub_C_mul_X_mul, coeff_zeta]
  simp [effCount_zero]

/-- The coefficients of `(1 - t)(1 - q t) Z(t)` vanish beyond `2g`. -/
theorem coeff_zetaNumerator_eq_zero (hk : IsFullConstantField k K)
    (hD : ∃ D : Divisor k K, D.deg = 1) {n : ℕ} (hn : 2 * genus k K < n) :
    coeff n (zetaNumerator k K) = 0 := by
  have hg := genus_nonneg hk
  set q : ℤ := (Nat.card k : ℤ)
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  have hq1 : q - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ q := by simp only [q]; exact_mod_cast hq
    omega
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- `n = 1`, `g = 0`
    have hn1 : n = 1 := by omega
    have hg0 : genus k K = 0 := by omega
    subst hn1
    rw [coeff_zetaNumerator_one]
    have e0 := effCount_mul_eq hk hD (n := 0) (by omega)
    have e1 := effCount_mul_eq hk hD (n := 1) (by omega)
    rw [hg0] at e0 e1
    simp only [effCount_zero, Nat.cast_one, zero_add, sub_zero, Int.toNat_one,
      pow_one] at e0 e1
    rw [show ((1 : ℤ) + 1).toNat = 2 from rfl] at e1
    have hh : (classNumber k K : ℤ) = 1 := by
      have := mul_right_cancel₀ hq1 e0.symm
      linarith
    rw [effCount_zero, Nat.cast_one]
    apply mul_right_cancel₀ hq1
    rw [hh] at e1
    linear_combination e1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [coeff_zetaNumerator_add_two]
  have e0 := effCount_mul_eq hk hD (n := m) (by push_cast at hn; omega)
  have e1 := effCount_mul_eq hk hD (n := m + 1) (by push_cast at hn; omega)
  have e2 := effCount_mul_eq hk hD (n := m + 2) (by push_cast at hn; omega)
  set e := ((m : ℤ) + 1 - genus k K).toNat
  have h1 : ((m : ℤ) + 1 + 1 - genus k K).toNat = e + 1 := by omega
  have h2 : ((m : ℤ) + 2 + 1 - genus k K).toNat = e + 2 := by omega
  rw [h1] at e1
  rw [h2] at e2
  apply mul_right_cancel₀ hq1
  rw [zero_mul]
  linear_combination e2 - (q + 1) * e1 + q * e0

/-- **Rationality of the zeta function**: with a divisor of degree `1`,
`(1 - t)(1 - q t) Z(t) = L(t)` for a polynomial `L ∈ ℤ[t]` of degree `≤ 2g` with `L(0) = 1`. -/
theorem exists_LPolynomial (hk : IsFullConstantField k K) (hD : ∃ D : Divisor k K, D.deg = 1) :
    ∃ L : Polynomial ℤ, L.natDegree ≤ 2 * (genus k K).toNat ∧ L.coeff 0 = 1 ∧
      (L : PowerSeries ℤ) = (1 - X) * ((1 - C (Nat.card k : ℤ) * X) * zeta k K) := by
  have hg := genus_nonneg hk
  set N := 2 * (genus k K).toNat
  refine ⟨trunc (N + 1) (zetaNumerator k K), ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_trunc, if_neg (by omega)]
  · rw [coeff_trunc, if_pos (by omega), coeff_zetaNumerator_zero]
  · have : (1 - X : PowerSeries ℤ) = 1 - C 1 * X := by simp
    rw [this, ← zetaNumerator]
    ext i
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hi
    · rfl
    · exact (coeff_zetaNumerator_eq_zero hk hD (by omega)).symm

/-! ### The leading coefficient `q^g` -/

/-- A divisor of degree `0` with `ℓ ≠ 0` is principal. -/
theorem mem_principal_of_deg_eq_zero {D : Divisor k K} (hD : D.deg = 0) (h : ell D ≠ 0) :
    D ∈ principal k K := by
  obtain ⟨z, hz, hle⟩ := exists_nonneg_add_div h
  have hdeg : (D + div k z).deg = 0 := by rw [deg_add, deg_div, hD, add_zero]
  have h0 : D + div k z = 0 := by
    by_contra hne
    have := deg_pos_of_nonneg_of_ne_zero hle hne
    omega
  have : D = div k z⁻¹ := by rw [div_inv]; exact eq_neg_of_add_eq_zero_left h0
  rw [this]
  exact div_mem_principal (inv_ne_zero hz)

open Classical in
/-- `ℓ` of a class of degree `2g - 2`: `g` for the canonical class, `g - 1` otherwise. -/
theorem ell_of_deg_eq_canonical (hk : IsFullConstantField k K) {A : Divisor k K}
    (hA : A.deg = 2 * genus k K - 2) :
    (ell A : ℤ) = if A - canonical k K ∈ principal k K then genus k K else genus k K - 1 := by
  have h := riemannRoch A
  have hW : (canonical k K - A).deg = 0 := by rw [deg_sub, deg_canonical, hA]; ring
  split_ifs with hp
  · have : ell (canonical k K - A) = 1 := by
      rw [ell_eq_of_sub_mem_principal (A := 0) (by rw [sub_zero, ← neg_sub, neg_mem_iff]; exact hp),
        ell_zero_eq_one hk]
    rw [this] at h
    push_cast at h
    omega
  · have : ell (canonical k K - A) = 0 := by
      by_contra h0
      have := mem_principal_of_deg_eq_zero hW h0
      rw [← neg_sub, neg_mem_iff] at this
      exact hp this
    rw [this] at h
    push_cast at h
    omega

/-- With a divisor of degree `1` and `g ≥ 1`:
`A_{2g-2} (q - 1) = (h - 1)(q^{g-1} - 1) + (q^g - 1)`. -/
theorem effCount_canonical_mul (hk : IsFullConstantField k K)
    (hD : ∃ D : Divisor k K, D.deg = 1) (hg : 1 ≤ genus k K) :
    (effCount k K (2 * genus k K - 2) : ℤ) * (Nat.card k - 1) =
      (classNumber k K - 1) * ((Nat.card k : ℤ) ^ (genus k K - 1).toNat - 1) +
        ((Nat.card k : ℤ) ^ (genus k K).toNat - 1) := by
  classical
  obtain ⟨D, hD⟩ := hD
  set n := 2 * genus k K - 2
  have hcl : Nat.card (Cl k K n) = classNumber k K := by
    have := card_Cl (D := n • D)
    rwa [deg_zsmul, hD, mul_one] at this
  have h := effCount_mul hk n
  set T := (finite_Cl (k := k) (K := K) n).toFinset
  set w : Pic k K := QuotientAddGroup.mk (canonical k K)
  have hw : w ∈ T := by
    rw [Set.Finite.mem_toFinset]
    simp only [Cl, Set.mem_setOf_eq, w, Pic.deg_mk, deg_canonical, n]
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  have hval : ∀ c ∈ T, ((Nat.card k ^ Pic.ell c - 1 : ℕ) : ℤ) =
      (if c = w then (Nat.card k : ℤ) ^ (genus k K).toNat - 1
        else (Nat.card k : ℤ) ^ (genus k K - 1).toNat - 1) := by
    intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨A, rfl⟩ := QuotientAddGroup.mk_surjective c
    simp only [Cl, Set.mem_setOf_eq, Pic.deg_mk] at hc
    have hl := ell_of_deg_eq_canonical hk hc
    rw [Pic.ell_mk, Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    push_cast
    have hiff : (QuotientAddGroup.mk A : Pic k K) = w ↔ A - canonical k K ∈ principal k K := by
      rw [eq_comm, mk_eq_mk_iff]
    by_cases hp : A - canonical k K ∈ principal k K
    · rw [if_pos hp] at hl
      rw [if_pos (hiff.mpr hp)]
      congr 2; omega
    · rw [if_neg hp] at hl
      rw [if_neg (fun h ↦ hp (hiff.mp h))]
      congr 2; omega
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast [Nat.cast_sub hq] at h'
  rw [h', Finset.sum_congr rfl hval]
  set a := (Nat.card k : ℤ) ^ (genus k K).toNat - 1
  set b := (Nat.card k : ℤ) ^ (genus k K - 1).toNat - 1
  have hsplit : ∀ x ∈ T, (if x = w then a else b) = b + (if x = w then a - b else 0) := by
    intro x _; split_ifs <;> ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq' T w, if_pos hw, nsmul_eq_mul]
  have hT : (T.card : ℤ) = classNumber k K := by
    rw [← hcl, Nat.card_eq_card_finite_toFinset]
  rw [hT]
  ring

/-- **The coefficient of `t^{2g}` in `(1 - t)(1 - q t) Z(t)` is `q^g`** (with a divisor of
degree `1`). -/
theorem coeff_zetaNumerator_two_genus (hk : IsFullConstantField k K)
    (hD : ∃ D : Divisor k K, D.deg = 1) :
    coeff (2 * (genus k K).toNat) (zetaNumerator k K) =
      (Nat.card k : ℤ) ^ (genus k K).toNat := by
  have hg := genus_nonneg hk
  set q : ℤ := (Nat.card k : ℤ)
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  have hq1 : q - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ q := by simp only [q]; exact_mod_cast hq
    omega
  rcases eq_or_lt_of_le hg with hg0 | hg1
  · rw [← hg0]
    simp [coeff_zetaNumerator_zero]
  obtain ⟨e, he⟩ : ∃ e : ℕ, (genus k K).toNat = e + 1 := ⟨(genus k K).toNat - 1, by omega⟩
  rw [he, show 2 * (e + 1) = 2 * e + 2 by ring, coeff_zetaNumerator_add_two]
  have e0 := effCount_canonical_mul hk hD (by omega)
  have e1 := effCount_mul_eq hk hD (n := 2 * genus k K - 1) (by omega)
  have e2 := effCount_mul_eq hk hD (n := 2 * genus k K) (by omega)
  have h0 : ((2 * e : ℕ) : ℤ) = 2 * genus k K - 2 := by push_cast; omega
  rw [h0, show 2 * genus k K - 2 + 1 = 2 * genus k K - 1 by ring,
    show 2 * genus k K - 2 + 2 = 2 * genus k K by ring]
  rw [show (genus k K).toNat = e + 1 from he, show (genus k K - 1).toNat = e by omega] at e0
  rw [show (2 * genus k K - 1 + 1 - genus k K).toNat = e + 1 by omega] at e1
  rw [show (2 * genus k K + 1 - genus k K).toNat = e + 2 by omega] at e2
  apply mul_right_cancel₀ hq1
  linear_combination e2 - (q + 1) * e1 + q * e0

/-- **Rationality of the zeta function**, with the leading coefficient: with a divisor of
degree `1`, `(1 - t)(1 - q t) Z(t) = L(t)` for a polynomial `L ∈ ℤ[t]` of degree `2g`, with
`L(0) = 1` and leading coefficient `q^g`. -/
theorem exists_LPolynomial' (hk : IsFullConstantField k K) (hD : ∃ D : Divisor k K, D.deg = 1) :
    ∃ L : Polynomial ℤ, L.natDegree = 2 * (genus k K).toNat ∧ L.coeff 0 = 1 ∧
      L.coeff (2 * (genus k K).toNat) = (Nat.card k : ℤ) ^ (genus k K).toNat ∧
      (L : PowerSeries ℤ) = (1 - X) * ((1 - C (Nat.card k : ℤ) * X) * zeta k K) := by
  obtain ⟨L, hdeg, h0, hL⟩ := exists_LPolynomial hk hD
  have hcoeff : L.coeff (2 * (genus k K).toNat) = (Nat.card k : ℤ) ^ (genus k K).toNat := by
    rw [← Polynomial.coeff_coe, hL]
    have : (1 - X : PowerSeries ℤ) = 1 - C 1 * X := by simp
    rw [this, ← zetaNumerator, coeff_zetaNumerator_two_genus hk hD]
  refine ⟨L, le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero ?_), h0, hcoeff, hL⟩
  rw [hcoeff]
  have hq : (2 : ℤ) ≤ Nat.card k := by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card k)
  exact pow_ne_zero _ (by omega)

end WeilCurves.FunctionField
