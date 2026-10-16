/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Algebraic function fields of one variable

An algebraic function field of one variable over a field `k` is a field `K` with a `k`-algebra
structure which is a finite extension of `k(t)` for some `t ∈ K` transcendental over `k`
(class `WeilCurves.FunctionField.IsFunctionField`); `k` need not be the full constant field.

This file and the following ones of `WeilCurves/FunctionField/` generalise the theory of curve
fields over `ℚ` of the `belyi` repository (`Belyi/CurveField/`) to an arbitrary base field `k`.
We follow H. Stichtenoth, *Algebraic Function Fields and Codes* (2nd ed.), Chapter 1.

## Main definitions and results

* `WeilCurves.FunctionField.IsFunctionField k K`: `K` is finite over `k⟮t⟯` for some transcendental
  `t`.
* `WeilCurves.FunctionField.exists_transcendental`: a curve field has a transcendental element.
* `WeilCurves.FunctionField.trdeg_eq_one`: its transcendence degree over `k` is `1`.
* `WeilCurves.FunctionField.isAlgebraic_adjoin`,
  `WeilCurves.FunctionField.finiteDimensional_adjoin`:
  for *every* `s ∈ K` transcendental over `k`, `K` is a finite extension of `k⟮s⟯`.
-/

open scoped IntermediateField

namespace WeilCurves.FunctionField

/-- `K` is an algebraic function field of one variable over `k`: `K` is finite over `k⟮t⟯` for
some `t ∈ K` transcendental over `k`. -/
class IsFunctionField (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop where
  exists_finite : ∃ t : K, Transcendental k t ∧ FiniteDimensional k⟮t⟯ K

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem transcendental_inv_iff {t : K} : Transcendental k t⁻¹ ↔ Transcendental k t :=
  not_congr IsAlgebraic.inv_iff

theorem transcendental_inv {t : K} (ht : Transcendental k t) : Transcendental k t⁻¹ :=
  transcendental_inv_iff.mpr ht

theorem ne_zero_of_transcendental {t : K} (ht : Transcendental k t) : t ≠ 0 := by
  rintro rfl
  exact ht isAlgebraic_zero

/-- If `K` is finite over `k⟮t⟯`, then `{t}` is a transcendence basis of `K / k`. -/
theorem isTranscendenceBasis_of_finiteDimensional {t : K} (ht : Transcendental k t)
    [FiniteDimensional k⟮t⟯ K] : IsTranscendenceBasis k (fun _ : Unit ↦ t) := by
  refine (algebraicIndependent_unique_type_iff.mpr ht).isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_const, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  infer_instance

variable [IsFunctionField k K]

variable (k K) in
/-- A function field contains an element transcendental over `k`. -/
theorem exists_transcendental : ∃ t : K, Transcendental k t :=
  let ⟨t, ht, _⟩ := IsFunctionField.exists_finite (k := k) (K := K); ⟨t, ht⟩

variable (k K) in
/-- A function field has transcendence degree one over `k`. -/
theorem trdeg_eq_one : Algebra.trdeg k K = 1 := by
  obtain ⟨t, ht, _⟩ := IsFunctionField.exists_finite (k := k) (K := K)
  have := (isTranscendenceBasis_of_finiteDimensional ht).lift_cardinalMk_eq_trdeg
  simpa using this.symm

/-- Every transcendental element of a curve field is a transcendence basis. -/
theorem isTranscendenceBasis {s : K} (hs : Transcendental k s) :
    IsTranscendenceBasis k (fun _ : Unit ↦ s) :=
  (algebraicIndependent_unique_type_iff.mpr hs).isTranscendenceBasis_of_lift_trdeg_le_of_finite
    (by rw [trdeg_eq_one k K]; simp)

/-- A function field is algebraic over `k⟮s⟯` for every transcendental `s`. -/
theorem isAlgebraic_adjoin {s : K} (hs : Transcendental k s) : Algebra.IsAlgebraic k⟮s⟯ K := by
  have := (isTranscendenceBasis hs).isAlgebraic_field
  rwa [Set.range_const] at this

variable (k K) in
/-- A function field is finitely generated as a field over `k`. -/
theorem exists_finset_adjoin_eq_top :
    ∃ S : Finset K, IntermediateField.adjoin k (S : Set K) = ⊤ := by
  obtain ⟨t, ht, _⟩ := IsFunctionField.exists_finite (k := k) (K := K)
  obtain ⟨S, hS⟩ := IntermediateField.fg_top (F := k⟮t⟯) (E := K)
  classical
  refine ⟨insert t S, ?_⟩
  have := congrArg (IntermediateField.restrictScalars k) hS
  have h2 := IntermediateField.adjoin_adjoin_left k (S := {t}) (S : Set K)
  rw [IntermediateField.restrictScalars_top] at this
  rw [Finset.coe_insert, Set.insert_eq, ← h2]
  exact this

/-- A function field is a finite extension of `k⟮s⟯` for every transcendental `s`. -/
theorem finiteDimensional_adjoin {s : K} (hs : Transcendental k s) :
    FiniteDimensional k⟮s⟯ K := by
  have := isAlgebraic_adjoin hs
  obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top k K
  have htop : IntermediateField.adjoin k⟮s⟯ (S : Set K) = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := k), eq_top_iff, ← hS,
      IntermediateField.adjoin_le_iff]
    exact IntermediateField.subset_adjoin _ _
  have := IntermediateField.finiteDimensional_adjoin (K := k⟮s⟯) (S := (S : Set K))
    (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end WeilCurves.FunctionField
