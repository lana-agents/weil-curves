/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.FiniteField.Roots

/-!
# Automorphisms of a function field acting on places

A `k`-automorphism `τ` of a function field `F / k` maps places to places
(`WeilCurves.FunctionField.Place.map τ Q`, with valuation ring `τ(O_Q)`), preserving orders
(`ord_{τQ}(τ x) = ord_Q x`) and degrees. Consequently `τ(L(m Q)) ⊆ L(m · τQ)`.
-/

namespace WeilCurves.FunctionField

open Divisor
open scoped WithZero

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- The image `τ(Q)` of a place under an automorphism: valuation ring `τ(O_Q)`. -/
def map (τ : F ≃ₐ[k] F) (Q : Place k F) : Place k F :=
  ⟨Q.1.comap (τ.symm : F →+* F), fun h ↦ Q.ne_top (top_unique fun x _ ↦ by
      have : τ x ∈ Q.1.comap (τ.symm : F →+* F) := by rw [h]; trivial
      simpa using (ValuationSubring.mem_comap.mp this)),
    fun c ↦ ValuationSubring.mem_comap.mpr (by simp [Q.algebraMap_mem])⟩

theorem mem_map {τ : F ≃ₐ[k] F} {Q : Place k F} {x : F} : x ∈ (Q.map τ).1 ↔ τ.symm x ∈ Q.1 :=
  ValuationSubring.mem_comap

theorem apply_mem_map {τ : F ≃ₐ[k] F} {Q : Place k F} {x : F} : τ x ∈ (Q.map τ).1 ↔ x ∈ Q.1 := by
  rw [mem_map, AlgEquiv.symm_apply_apply]

theorem map_map (τ σ : F ≃ₐ[k] F) (Q : Place k F) : (Q.map τ).map σ = Q.map (τ.trans σ) := by
  ext x
  simp [mem_map]

theorem map_symm_map (τ : F ≃ₐ[k] F) (Q : Place k F) : (Q.map τ).map τ.symm = Q := by
  ext x
  simp [mem_map]

theorem map_map_symm (τ : F ≃ₐ[k] F) (Q : Place k F) : (Q.map τ.symm).map τ = Q := by
  ext x
  simp [mem_map]

variable [PerfectField k] [IsFunctionField k F]

/-- **`ord_{τQ}(τ x) = ord_Q x`**. -/
theorem ord_map_apply (τ : F ≃ₐ[k] F) (Q : Place k F) (x : F) :
    (Q.map τ).ord (τ x) = Q.ord x := by
  set w : Valuation F ℤᵐ⁰ := Q.valuation.comap (τ.symm : F →+* F)
  have hw : ∀ y, y ∈ (Q.map τ).1 ↔ w y ≤ 1 := by
    intro y
    rw [mem_map, Q.mem_iff_valuation_le_one]
    rfl
  obtain ⟨π, hπ⟩ := Q.exists_ord_eq_one
  have hπw : w (τ π) = WithZero.exp (-1) := by
    have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
    simp only [w, Valuation.comap_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply]
    rw [Q.valuation_eq_exp hπ0, hπ]
  rw [(Q.map τ).ord_eq_neg_log w hw ⟨_, hπw⟩ (τ x)]
  simp only [w, Valuation.comap_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply, ord]

theorem ord_map (τ : F ≃ₐ[k] F) (Q : Place k F) (x : F) :
    (Q.map τ).ord x = Q.ord (τ.symm x) := by
  rw [← ord_map_apply τ Q, AlgEquiv.apply_symm_apply]

/-- `O_Q ≃ O_{τQ}`. -/
def mapRingEquiv (τ : F ≃ₐ[k] F) (Q : Place k F) : Q.1 ≃+* (Q.map τ).1 where
  toFun x := ⟨τ x, apply_mem_map.mpr x.2⟩
  invFun y := ⟨τ.symm y, mem_map.mp y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

omit [PerfectField k] [IsFunctionField k F] in
/-- **`deg τQ = deg Q`**. -/
theorem deg_map (τ : F ≃ₐ[k] F) (Q : Place k F) : (Q.map τ).deg = Q.deg := by
  set e := IsLocalRing.ResidueField.mapEquiv (mapRingEquiv τ Q)
  let e' : Q.ResidueField ≃ₐ[k] (Q.map τ).ResidueField :=
    AlgEquiv.ofRingEquiv (f := e) fun c ↦ by
      change IsLocalRing.ResidueField.map ((mapRingEquiv τ Q : Q.1 →+* (Q.map τ).1))
        (Q.residue _) = _
      rw [Place.residue]
      erw [IsLocalRing.ResidueField.map_residue]
      rw [Place.algebraMap_residueField]
      congr 1
      ext
      simp [mapRingEquiv, Place.coe_baseHom]
  exact e'.toLinearEquiv.finrank_eq.symm

/-- `τ(L(m Q)) ⊆ L(m · τQ)`. -/
theorem apply_mem_L_single {τ : F ≃ₐ[k] F} {Q : Place k F} {m : ℤ} {h : F}
    (hh : h ∈ L (Finsupp.single Q m)) : τ h ∈ L (Finsupp.single (Q.map τ) m) := by
  classical
  rcases mem_L.mp hh with h0 | hP
  · rw [h0, map_zero]; exact zero_mem _
  refine mem_L.mpr (Or.inr fun β ↦ ?_)
  have := hP (β.map τ.symm)
  rw [ord_map, AlgEquiv.symm_symm] at this
  have hiff : β.map τ.symm = Q ↔ β = Q.map τ := by
    constructor
    · rintro rfl; rw [map_map_symm]
    · rintro rfl; rw [map_symm_map]
  by_cases hβ : β = Q.map τ
  · have h1 : β.map τ.symm = Q := hiff.mpr hβ
    rw [h1] at this
    rw [hβ] at this ⊢
    simpa using this
  · have h1 : β.map τ.symm ≠ Q := fun h ↦ hβ (hiff.mp h)
    have h2 : (Finsupp.single Q m) (β.map τ.symm) = 0 := by
      rw [Finsupp.single_apply, if_neg (Ne.symm h1)]
    have h3 : (Finsupp.single (Q.map τ) m) β = 0 := by
      rw [Finsupp.single_apply, if_neg (Ne.symm hβ)]
    rw [h2] at this
    rw [h3]
    exact this

end Place

end WeilCurves.FunctionField
