/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Degree
import Mathlib.FieldTheory.Finite.Basic

/-!
# Places over a smaller base field; zeros of `t^Q − t`

* For a tower `k ⊆ k' ⊆ M` with `k'` algebraic over `k`, places of `M` over `k` and over `k'` are
  the same valuation subrings (`Place.toBase`, `Place.ofBase`), with the same `ord` and
  `deg_k = [k' : k] · deg_{k'}` (generalising `ConstantExtension/OverKr`).
* `∑_{ord_β (t^Q − t) > 0} ord_β(t^Q − t) deg β = Q [M : k(t)]` for `t` transcendental and
  `Q ≥ 2` (the poles of `t^Q − t` are those of `t`, with `Q` times the order).
* A finite field extension `E / k` in which every element satisfies `y^{|k|^r} = y` has
  `[E : k] ∣ r` (`finrank_dvd_of_forall_pow_eq`).
-/

open scoped IntermediateField

namespace WeilCurves.FunctionField

section Base

variable {k k' M : Type*} [Field k] [Field k'] [Field M] [Algebra k k'] [Algebra k' M]
  [Algebra k M] [IsScalarTower k k' M]

/-- A place over `k'` is a place over `k`. -/
def Place.toBase (Q : Place k' M) : Place k M :=
  ⟨Q.1, Q.ne_top, fun c ↦ by rw [IsScalarTower.algebraMap_apply k k' M]; exact Q.algebraMap_mem _⟩

/-- A place over `k` is a place over `k'` (for `k'` algebraic over `k`). -/
def Place.ofBase [Algebra.IsAlgebraic k k'] (Q : Place k M) : Place k' M :=
  ⟨Q.1, Q.ne_top, fun c ↦ Q.mem_of_isAlgebraic
    (IsAlgebraic.algebraMap (R := k) (S := k') (A := M) (Algebra.IsAlgebraic.isAlgebraic c))⟩

@[simp] theorem Place.toBase_val (Q : Place k' M) : (Q.toBase (k := k)).1 = Q.1 := rfl

@[simp] theorem Place.ofBase_toBase [Algebra.IsAlgebraic k k'] (Q : Place k' M) :
    (Q.toBase (k := k)).ofBase = Q := rfl

@[simp] theorem Place.toBase_ofBase [Algebra.IsAlgebraic k k'] (Q : Place k M) :
    (Q.ofBase (k' := k')).toBase = Q := rfl

theorem Place.toBase_injective :
    Function.Injective (Place.toBase (k := k) (k' := k') (M := M)) := by
  intro a b h
  apply Place.ext
  exact congrArg (fun P : Place k M ↦ P.1) h

theorem Place.ord_toBase [PerfectField k] [PerfectField k'] [IsFunctionField k M]
    [IsFunctionField k' M] (Q : Place k' M) (f : M) : (Q.toBase (k := k)).ord f = Q.ord f := rfl

/-- **`deg_k Q = [k' : k] · deg_{k'} Q`**. -/
theorem Place.deg_toBase [PerfectField k] [PerfectField k'] [IsFunctionField k M]
    [IsFunctionField k' M] [FiniteDimensional k k'] (Q : Place k' M) :
    (Q.toBase (k := k)).deg = Module.finrank k k' * Q.deg := by
  letI : Algebra k' (Q.toBase (k := k)).ResidueField :=
    (inferInstance : Algebra k' Q.ResidueField)
  have : IsScalarTower k k' (Q.toBase (k := k)).ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
    change (Q.toBase (k := k)).residue ((Q.toBase (k := k)).baseHom c) =
      Q.residue (Q.baseHom _)
    congr 1
    apply Subtype.ext
    simp only [Place.coe_baseHom]
    exact IsScalarTower.algebraMap_apply k k' M c
  have : FiniteDimensional k' (Q.toBase (k := k)).ResidueField :=
    (inferInstance : FiniteDimensional k' Q.ResidueField)
  rw [Place.deg, Place.deg, ← Module.finrank_mul_finrank k k' (Q.toBase (k := k)).ResidueField]
  rfl

end Base

section Zeros

variable {k M : Type*} [Field k] [PerfectField k] [Field M] [Algebra k M] [IsFunctionField k M]

/-- At a pole of `t`, `ord (t^Q − t) = Q ord t` (`Q ≥ 2`). -/
theorem Place.ord_pow_sub_of_neg (P : Place k M) {t : M} (ht : P.ord t < 0) {Q : ℕ}
    (hQ : 2 ≤ Q) : P.ord (t ^ Q - t) = Q * P.ord t := by
  have ht0 : t ≠ 0 := by rintro rfl; rw [P.ord_zero] at ht; exact lt_irrefl _ ht
  have h1 : P.ord (t ^ Q) = Q * P.ord t := P.ord_pow t Q
  have hlt : P.ord (t ^ Q) < P.ord (-t) := by
    rw [h1, P.ord_neg]
    have : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  rw [sub_eq_add_neg, P.ord_add_eq_of_lt (pow_ne_zero _ ht0) (neg_ne_zero.mpr ht0) hlt, h1]

/-- **Zeros of `t^Q − t`**: `∑_{ord_β (t^Q − t) > 0} ord_β(t^Q − t) deg β = Q [M : k(t)]`. -/
theorem sum_ord_mul_deg_zeros_pow_sub {t : M} (ht : Transcendental k t) {Q : ℕ} (hQ : 2 ≤ Q) :
    ∑ P ∈ (Place.finite_setOf_ord_pos (k := k) (t ^ Q - t)).toFinset,
      P.ord (t ^ Q - t) * (P.deg : ℤ) = Q * Module.finrank k⟮t⟯ M := by
  classical
  set z := t ^ Q - t
  -- poles of `z` are the poles of `t`
  have hpole : ∀ P : Place k M, P.ord z < 0 ↔ P.ord t < 0 := by
    intro P
    constructor
    · intro hz
      by_contra hnt
      push Not at hnt
      have htm : t ∈ P.1 := P.mem_of_ord_nonneg hnt
      have : z ∈ P.1 := P.1.sub_mem (P.1.pow_mem htm Q) htm
      exact (P.ord_neg_iff.mp hz) this
    · intro hnt
      rw [P.ord_pow_sub_of_neg hnt hQ]
      have : (0 : ℤ) < Q := by omega
      nlinarith
  have hzt : Transcendental k z := by
    obtain ⟨P, hP⟩ := Place.exists_ord_neg (k := k) ht
    intro halg
    have := (Place.isAlgebraic_iff_forall_mem.mp halg) P
    exact (P.ord_neg_iff.mp ((hpole P).mpr hP)) this
  rw [Place.sum_ord_mul_deg_zeros z hzt, ← Place.sum_ord_mul_deg_poles z hzt,
    ← Place.sum_ord_mul_deg_poles t ht, Finset.mul_sum]
  have hset : (Place.finite_setOf_ord_neg (k := k) z).toFinset =
      (Place.finite_setOf_ord_neg (k := k) t).toFinset := by
    ext P; simp [hpole P]
  rw [hset]
  refine Finset.sum_congr rfl fun P hP ↦ ?_
  have hPt : P.ord t < 0 := by simpa using hP
  rw [P.ord_pow_sub_of_neg hPt hQ]
  ring

end Zeros

section FiniteFieldDvd

/-- If every element of a finite extension `E` of the finite field `k` satisfies
`y^{|k|^r} = y`, then `[E : k] ∣ r`. -/
theorem finrank_dvd_of_forall_pow_eq {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    [Finite E] {r : ℕ} (h : ∀ y : E, y ^ (Nat.card k ^ r) = y) : Module.finrank k E ∣ r := by
  cases nonempty_fintype k
  rw [← FiniteField.orderOf_frobeniusAlgHom k E]
  apply orderOf_dvd_of_pow_eq_one
  ext y
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
    ← Nat.card_eq_fintype_card]
  exact h y

end FiniteFieldDvd

end WeilCurves.FunctionField
