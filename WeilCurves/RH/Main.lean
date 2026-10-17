/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Galois.Closure
import WeilCurves.PointBound.Upper
import WeilCurves.RH.Conditional

/-!
# The Riemann hypothesis for curves over finite fields

Let `K` be a function field over a finite field `k` with `q` elements, `k` the full constant
field, `g` its genus and `α_1, …, α_{2g}` the reciprocal roots of its `L`-polynomial. Combining

* the upper bound `N_r ≤ q^r + 1 + (2g + 1) q^{r/2}` (`pointCount_le`, Bombieri), and
* the lower bound `N_{dm} ≥ q^{dm} − A q^{dm/2} − C` (`exists_lower_bound`, via a Galois cover),

for `r = dm` with `q^r` an even power of `p` and large, gives
`|N_{2dN} − q^{2dN} − 1| ≤ C' q^{dN}` for all large `N` (`exists_two_sided_bound`), hence
(Kedlaya, Lemma 5.1.4; `norm_recRoots_eq_of_bound`):

* **`|α_i| = √q`** (`WeilCurves.FunctionField.riemannHypothesis`), and
* **the Hasse–Weil bound** `|N_r − q^r − 1| ≤ 2g q^{r/2}` (`WeilCurves.FunctionField.hasseWeil`).
-/

namespace WeilCurves.FunctionField

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]
  [hk : Fact (IsFullConstantField k K)]

omit hk in
/-- A two-sided bound in integers: for all large `N`, with `q^{2dN} = p^{2b}`,
`|N_{2dN} − p^{2b} − 1| ≤ C p^b`. -/
theorem exists_two_sided_bound_int (hkK : IsFullConstantField k K) :
    ∃ d : ℕ, 0 < d ∧ ∃ a : ℕ, 0 < a ∧ Nat.card k = ringChar k ^ a ∧ ∃ C : ℤ, ∃ N₀ : ℕ,
      ∀ N, N₀ ≤ N → |(pointCount k K (2 * d * N) : ℤ) - (ringChar k : ℤ) ^ (2 * (a * d * N)) - 1|
        ≤ C * (ringChar k : ℤ) ^ (a * d * N) := by
  classical
  set p := ringChar k
  have hp : p.Prime := (fact_ringChar_prime (k := k)).out
  have : Fact p.Prime := ⟨hp⟩
  have : CharP k p := ringChar.charP k
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨a, -, hcard⟩ := FiniteField.card k p
  have hq : Nat.card k = p ^ (a : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨d, hd, A, C, G₀, hlow⟩ := exists_lower_bound (k := k) (F := K) p
  set g := genus k K
  have hg0 : 0 ≤ g := genus_nonneg hkK
  refine ⟨d, hd, a, a.pos, hq, (2 * g + 1) + |A| + |C| + 1,
    (((g + 1) ^ 4).toNat + G₀.toNat + 1), fun N hN ↦ ?_⟩
  set b := (a : ℕ) * d * N
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  -- `p^{2b}` is large
  have hNb : N ≤ b := by
    have : 1 ≤ (a : ℕ) * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero a.ne_zero hd.ne')
    calc N = 1 * N := (one_mul N).symm
      _ ≤ (a : ℕ) * d * N := Nat.mul_le_mul_right N this
  have hbig : (N : ℤ) < (p : ℤ) ^ (2 * b) := by
    have h1 : (N : ℤ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℤ) ^ N ≤ (p : ℤ) ^ (2 * b) :=
      (pow_le_pow_left₀ (by norm_num) hp2 N).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    linarith
  have hN' : ((g + 1) ^ 4).toNat + G₀.toNat + 1 ≤ (N : ℤ) := by exact_mod_cast hN
  have hg4 : (g + 1) ^ 4 < (p : ℤ) ^ (2 * b) := by
    have := Int.self_le_toNat ((g + 1) ^ 4)
    have : (0 : ℤ) ≤ G₀.toNat := by positivity
    linarith
  have hG₀ : G₀ < (p : ℤ) ^ (2 * b) := by
    have := Int.self_le_toNat G₀
    have : (0 : ℤ) ≤ ((g + 1) ^ 4).toNat := by positivity
    linarith
  -- `q^{2dN} = p^{2b}`
  have hqr : Nat.card k ^ (2 * d * N) = p ^ (2 * b) := by
    rw [hq, ← pow_mul]; congr 1; simp only [b]; ring
  have hqr' : Nat.card k ^ (d * (2 * N)) = p ^ (2 * b) := by
    rw [show d * (2 * N) = 2 * d * N by ring]; exact hqr
  have : NeZero (2 * d * N) := ⟨by
    have : 1 ≤ N := by omega
    positivity⟩
  have hup := pointCount_le (k := k) (K := K) p b hkK hqr hg4
  have hlo := hlow (2 * N) b hqr' hG₀
  rw [show d * (2 * N) = 2 * d * N by ring] at hlo
  have hpb : (1 : ℤ) ≤ (p : ℤ) ^ b := one_le_pow₀ (by linarith)
  rw [abs_le]
  constructor
  · -- lower
    have hA : A * (p : ℤ) ^ b ≤ |A| * p ^ b := mul_le_mul_of_nonneg_right (le_abs_self A)
      (by positivity)
    have hC : C ≤ |C| * p ^ b := by
      calc C ≤ |C| := le_abs_self C
        _ = |C| * 1 := (mul_one _).symm
        _ ≤ |C| * p ^ b := mul_le_mul_of_nonneg_left hpb (abs_nonneg C)
    have : 0 ≤ (2 * g + 1) * (p : ℤ) ^ b := by positivity
    nlinarith
  · -- upper
    have : 0 ≤ (|A| + |C| + 1) * (p : ℤ) ^ b := by positivity
    nlinarith

/-- **Two-sided bound**: `|N_{dN} − q^{dN} − 1| ≤ C √q^{dN}` for all large `N` (some `d ≥ 1`). -/
theorem exists_two_sided_bound :
    ∃ d : ℕ, 0 < d ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      |(pointCount k K (d * N) : ℝ) - (Nat.card k : ℝ) ^ (d * N) - 1| ≤
        C * Real.sqrt (Nat.card k) ^ (d * N) := by
  obtain ⟨d, hd, a, -, hq, C, N₀, h⟩ := exists_two_sided_bound_int (k := k) (K := K) hk.out
  refine ⟨2 * d, by omega, C, N₀, fun N hN ↦ ?_⟩
  have h1 := h N hN
  set p := ringChar k
  have hqR : (Nat.card k : ℝ) = (p : ℝ) ^ a := by rw [hq]; push_cast; rfl
  have hsq : Real.sqrt (Nat.card k) ^ (2 * d * N) = (p : ℝ) ^ (a * d * N) := by
    rw [show 2 * d * N = 2 * (d * N) by ring, pow_mul, Real.sq_sqrt (by positivity), hqR,
      ← pow_mul, mul_assoc]
  have hqr : (Nat.card k : ℝ) ^ (2 * d * N) = (p : ℝ) ^ (2 * (a * d * N)) := by
    rw [hqR, ← pow_mul]; congr 1; ring
  rw [hsq, hqr]
  have h2 : |((pointCount k K (2 * d * N) : ℤ) - (p : ℤ) ^ (2 * (a * d * N)) - 1 : ℤ)| ≤
      C * (p : ℤ) ^ (a * d * N) := h1
  have h3 := (Int.cast_le (R := ℝ)).mpr h2
  push_cast at h3
  exact h3

/-- **The Riemann hypothesis for curves over finite fields** (Weil): the reciprocal roots of
the `L`-polynomial have absolute value `√q`. -/
theorem riemannHypothesis {α : ℂ} (hα : α ∈ recRoots k K) : ‖α‖ = Real.sqrt (Nat.card k) := by
  obtain ⟨d, hd, C, N₀, h⟩ := exists_two_sided_bound (k := k) (K := K)
  exact norm_recRoots_eq_of_bound hd h hα

/-- **The Hasse–Weil bound** `|N_r − q^r − 1| ≤ 2g q^{r/2}`. -/
theorem hasseWeil {r : ℕ} (hr : r ≠ 0) :
    |(pointCount k K r : ℝ) - (Nat.card k : ℝ) ^ r - 1| ≤
      2 * (genus k K).toNat * Real.sqrt (Nat.card k) ^ r := by
  obtain ⟨d, hd, C, N₀, h⟩ := exists_two_sided_bound (k := k) (K := K)
  exact hasseWeil_of_bound hd h hr

end WeilCurves.FunctionField
