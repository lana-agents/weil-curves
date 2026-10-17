/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FunctionField.Degree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois

/-!
# Frobenius automorphisms at places of a Galois extension of `k(x)`

Let `M` be a function field over a finite field `k` with `q` elements and `x ∈ M` transcendental
such that `M / k(x)` is Galois. The Galois group acts on the chart ring `A_x` (integral closure of
`k[x]`), whose invariants are `k[x]` (Mathlib, `Algebra.isInvariant_of_isGalois`), and the
stabiliser of a prime surjects onto the automorphisms of its residue field
(`Ideal.Quotient.stabilizerHom_surjective`). For a place `β ∋ x` at which `x^{q^n} ≡ x`
(i.e. `β` lies over a place of `k(x)` of degree dividing `n`), the `q^n`-th power map of the residue
field is such an automorphism, so there is `σ ∈ Gal(M / k(x))` with

`y^{q^n} ≡ σ y (mod β)` for all `y ∈ O_β`  (`WeilCurves.FunctionField.exists_frobenius_place`).

This is the existence of Frobenius elements (Nivedita, §3.2.3; Kedlaya, Definition 5.1.6) in the
form needed for the twisted Bombieri bound.
-/

open Polynomial IsDedekindDomain
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace WeilCurves.FunctionField

open Place

variable {k M : Type*} [Field k] [Finite k] [Field M] [Algebra k M] [IsFunctionField k M]
  (x : M) [hx : Fact (Transcendental k x)]

/-- The Galois group of `M / k(x)` acts on the chart ring `A_x`. -/
noncomputable instance galChartAction : MulSemiringAction Gal(M/k⟮x⟯) (chartRing k x) :=
  IsIntegralClosure.MulSemiringAction (Algebra.adjoin k {x}) k⟮x⟯ M (chartRing k x)

omit [Finite k] in
theorem coe_galChartAction_smul (σ : Gal(M/k⟮x⟯)) (b : chartRing k x) :
    ((σ • b : chartRing k x) : M) = σ (b : M) :=
  algebraMap_galRestrict_apply (A := Algebra.adjoin k {x}) (K := k⟮x⟯) (L := M)
    (B := chartRing k x) σ b

instance : SMulCommClass Gal(M/k⟮x⟯) (Algebra.adjoin k {x}) (chartRing k x) :=
  ⟨fun σ a b ↦ map_smul (galRestrict (Algebra.adjoin k {x}) k⟮x⟯ M (chartRing k x) σ) a b⟩

/-- **Frobenius elements** in the chart ring: if `x^{q^n} ≡ x` modulo a height-one prime `v` of
`A_x`, some `σ ∈ Gal(M / k(x))` satisfies `σ b ≡ b^{q^n} (mod v)` for all `b ∈ A_x`. -/
theorem exists_frobenius_chart [IsGalois k⟮x⟯ M] (v : HeightOneSpectrum (chartRing k x)) (n : ℕ)
    (hz : (⟨x, self_mem_chartRing k x⟩ : chartRing k x) ^ (Nat.card k ^ n) -
      ⟨x, self_mem_chartRing k x⟩ ∈ v.asIdeal) :
    ∃ σ : Gal(M/k⟮x⟯), ∀ b : chartRing k x, σ • b - b ^ (Nat.card k ^ n) ∈ v.asIdeal := by
  classical
  cases nonempty_fintype k
  have hinv : Algebra.IsInvariant (Algebra.adjoin k {x}) (chartRing k x) Gal(M/k⟮x⟯) :=
    Algebra.isInvariant_of_isGalois (Algebra.adjoin k {x}) k⟮x⟯ M (chartRing k x)
  have : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (chartRing k x ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have : Finite (chartRing k x ⧸ v.asIdeal) := by
    have : Finite (ofChart x v).ResidueField := Module.finite_of_finite k
    exact Finite.of_equiv _ (quotientEquivResidueField x v).symm.toEquiv
  -- the `q^n`-th power map of `A_x ⧸ v`, as a `k`-automorphism
  set φ : (chartRing k x ⧸ v.asIdeal) ≃ₐ[k] (chartRing k x ⧸ v.asIdeal) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic k (chartRing k x ⧸ v.asIdeal) ^ n with hφdef
  have hφ : ∀ y, φ y = y ^ (Nat.card k ^ n) := by
    intro y
    rw [hφdef, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Nat.card_eq_fintype_card]
  -- `φ` fixes the image of `k[x]`
  have hfix : ∀ a : Algebra.adjoin k {x}, φ (algebraMap (Algebra.adjoin k {x})
      (chartRing k x ⧸ v.asIdeal) a) = algebraMap _ (chartRing k x ⧸ v.asIdeal) a := by
    let e := Polynomial.algEquivOfTranscendental k x hx.out
    let ψ : Algebra.adjoin k {x} →ₐ[k] (chartRing k x ⧸ v.asIdeal) :=
      IsScalarTower.toAlgHom k (Algebra.adjoin k {x}) (chartRing k x ⧸ v.asIdeal)
    have hext : (φ.toAlgHom.comp ψ).comp e.toAlgHom = ψ.comp e.toAlgHom := by
      apply Polynomial.algHom_ext
      have he : e X = ⟨x, Algebra.self_mem_adjoin_singleton k x⟩ := by
        rw [Polynomial.algEquivOfTranscendental_apply, aeval_X]
      change φ (ψ (e X)) = ψ (e X)
      rw [he]
      change φ (Ideal.Quotient.mk v.asIdeal ⟨x, self_mem_chartRing k x⟩) =
        Ideal.Quotient.mk v.asIdeal ⟨x, self_mem_chartRing k x⟩
      rw [hφ, ← map_pow, Ideal.Quotient.eq]
      exact hz
    intro a
    obtain ⟨g, rfl⟩ := e.surjective a
    exact DFunLike.congr_fun hext g
  let l : (chartRing k x ⧸ v.asIdeal) ≃ₐ[Algebra.adjoin k {x} ⧸
      v.asIdeal.under (Algebra.adjoin k {x})] (chartRing k x ⧸ v.asIdeal) :=
    { φ.toRingEquiv with
      commutes' := by
        intro c
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact hfix a }
  obtain ⟨⟨σ, hσs⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(M/k⟮x⟯)
    (v.asIdeal.under (Algebra.adjoin k {x})) v.asIdeal l
  refine ⟨σ, fun b ↦ ?_⟩
  have := DFunLike.congr_fun hσ (Ideal.Quotient.mk v.asIdeal b)
  rw [Ideal.Quotient.stabilizerHom_apply] at this
  change Ideal.Quotient.mk v.asIdeal (σ • b) = φ (Ideal.Quotient.mk v.asIdeal b) at this
  rw [hφ, ← map_pow, Ideal.Quotient.eq] at this
  exact this

/-- **Frobenius elements at places**: if `β ∋ x` is a place with `x^{q^n} ≡ x (mod β)`, there is
`σ ∈ Gal(M / k(x))` with `y^{q^n} ≡ σ y (mod β)` for every `y ∈ O_β`. -/
theorem exists_frobenius_place [IsGalois k⟮x⟯ M] (β : Place k M) (hxβ : x ∈ β.1) (n : ℕ)
    (hz : x ^ (Nat.card k ^ n) - x ∈ β.1.nonunits) :
    ∃ σ : Gal(M/k⟮x⟯), ∀ y ∈ β.1, y ^ (Nat.card k ^ n) - σ y ∈ β.1.nonunits := by
  set v := β.toChart x hxβ
  set N := Nat.card k ^ n
  have hz' : (⟨x, self_mem_chartRing k x⟩ : chartRing k x) ^ N -
      ⟨x, self_mem_chartRing k x⟩ ∈ v.asIdeal := by
    rw [mem_toChart_iff]; exact hz
  obtain ⟨σ, hσ⟩ := exists_frobenius_chart (k := k) x v n hz'
  refine ⟨σ, fun y hy ↦ ?_⟩
  have hβ : β = ofChart x v := (ofChart_toChart x β hxβ).symm
  have hmemQ : ∀ b : chartRing k x, b ∈ v.asIdeal ↔ (b : M) ∈ β.1.nonunits :=
    fun b ↦ mem_toChart_iff x β hxβ
  -- write `y = a / s` with `s ∉ v`
  rw [hβ, ofChart_val] at hy
  obtain ⟨a, s, hs, rfl⟩ := hy
  have hs' : s ∉ v.asIdeal := hs
  have hσs : σ • s ∉ v.asIdeal := by
    intro h
    apply hs'
    have h2 : s ^ N ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem h (hσ s)
      rwa [sub_sub_cancel] at this
    exact v.isPrime.mem_of_pow_mem N h2
  have hnum : a ^ N * (σ • s) - (σ • a) * s ^ N ∈ v.asIdeal := by
    have : a ^ N * (σ • s) - (σ • a) * s ^ N =
        a ^ N * (σ • s - s ^ N) - (σ • a - a ^ N) * s ^ N := by ring
    rw [this]
    exact v.asIdeal.sub_mem (v.asIdeal.mul_mem_left _ (hσ s))
      (v.asIdeal.mul_mem_right _ (hσ a))
  have hden : s ^ N * (σ • s) ∉ v.asIdeal := by
    intro h
    rcases v.isPrime.mem_or_mem h with h | h
    · exact hs' (v.isPrime.mem_of_pow_mem N h)
    · exact hσs h
  have hs0 : (s : M) ≠ 0 := by
    intro h0; apply hs'
    have : s = 0 := Subtype.ext h0
    rw [this]; exact v.asIdeal.zero_mem
  have hσs0 : ((σ • s : chartRing k x) : M) ≠ 0 := by
    intro h0; apply hσs
    have : σ • s = 0 := Subtype.ext h0
    rw [this]; exact v.asIdeal.zero_mem
  have key : (algebraMap (chartRing k x) M a * (algebraMap (chartRing k x) M s)⁻¹) ^ N -
      σ (algebraMap (chartRing k x) M a * (algebraMap (chartRing k x) M s)⁻¹) =
      ((a ^ N * (σ • s) - (σ • a) * s ^ N : chartRing k x) : M) *
        (((s ^ N * (σ • s) : chartRing k x) : M))⁻¹ := by
    rw [map_mul, map_inv₀]
    change ((a : M) * (s : M)⁻¹) ^ N - σ (a : M) * (σ (s : M))⁻¹ = _
    rw [← coe_galChartAction_smul x σ a, ← coe_galChartAction_smul x σ s]
    push_cast
    rw [mul_pow, inv_pow]
    field_simp
  rw [key]
  have hnum' := (hmemQ _).mp hnum
  have hden' : ((s ^ N * (σ • s) : chartRing k x) : M) ∉ β.1.nonunits := by
    rw [← hmemQ]; exact hden
  have hdenmem : ((s ^ N * (σ • s) : chartRing k x) : M) ∈ β.1 :=
    β.algebraMap_chartRing_mem x hxβ (s ^ N * (σ • s))
  rw [ValuationSubring.mem_nonunits_iff] at hnum' hden' ⊢
  have hv1 : β.1.valuation ((s ^ N * (σ • s) : chartRing k x) : M) = 1 :=
    le_antisymm ((β.1.valuation_le_one_iff _).mpr hdenmem) (not_lt.mp hden')
  rw [map_mul, map_inv₀, hv1, inv_one, mul_one]
  exact hnum'

end WeilCurves.FunctionField
