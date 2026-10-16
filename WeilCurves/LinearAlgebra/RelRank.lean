/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Relative dimensions of submodules

For submodules `Y, X` of a vector space `V` over a division ring `k`, the *relative rank*
`relRank Y X = dim_k ((X + Y) / Y)` is the rank of the image of `X` in `V ⧸ Y`. It is used for the
quotients of adele spaces in the proof of the Riemann–Roch theorem, where the ambient space `V` is
infinite-dimensional but the relevant quotients are finite-dimensional.

## Main results

* `WeilCurves.relRank_eq_of_inf_eq`: `relRank Y X` only depends on `X` and `X ⊓ Y`.
* `WeilCurves.relRank_trans`: for `Y ≤ X ≤ Z`, `relRank Y Z = relRank Y X + relRank X Z`.
* `WeilCurves.relRank_eq_sup_add_inf`: for `Y ≤ X` and any `D`,
  `relRank Y X = relRank (Y ⊔ D) (X ⊔ D) + relRank (Y ⊓ D) (X ⊓ D)`.
-/

namespace WeilCurves

open Submodule

variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

/-- The relative rank `dim ((X + Y) / Y)`: the rank of the image of `X` in `V ⧸ Y`. -/
noncomputable def relRank (Y X : Submodule k V) : Cardinal := Module.rank k (X.map Y.mkQ)

/-- `relRank Y X` is the rank of `X ⧸ (X ⊓ Y)`. -/
theorem relRank_eq_rank_quotient (Y X : Submodule k V) :
    relRank Y X = Module.rank k (X ⧸ Y.comap X.subtype) := by
  have hker : LinearMap.ker (Y.mkQ ∘ₗ X.subtype) = Y.comap X.subtype := by
    rw [LinearMap.ker_comp, ker_mkQ]
  have hrange : LinearMap.range (Y.mkQ ∘ₗ X.subtype) = X.map Y.mkQ := by
    rw [LinearMap.range_comp, range_subtype]
  rw [relRank, ← hrange, ← hker]
  exact (LinearMap.quotKerEquivRange _).rank_eq.symm

/-- `relRank Y X` only depends on `X` and `X ⊓ Y`. -/
theorem relRank_eq_of_inf_eq {X Y Y' : Submodule k V} (h : X ⊓ Y = X ⊓ Y') :
    relRank Y X = relRank Y' X := by
  rw [relRank_eq_rank_quotient, relRank_eq_rank_quotient]
  have : Y.comap X.subtype = Y'.comap X.subtype := by
    ext ⟨x, hx⟩
    simp only [mem_comap, subtype_apply]
    constructor
    · intro hy
      have : x ∈ X ⊓ Y' := h ▸ ⟨hx, hy⟩
      exact this.2
    · intro hy
      have : x ∈ X ⊓ Y := h.symm ▸ ⟨hx, hy⟩
      exact this.2
  rw [this]

theorem map_mkQ_eq_bot_of_le {X Y : Submodule k V} (h : X ≤ Y) : X.map Y.mkQ = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_bot, mkQ_apply, Quotient.mk_eq_zero]
  exact h hx

theorem relRank_of_le {X Y : Submodule k V} (h : X ≤ Y) : relRank Y X = 0 := by
  rw [relRank, map_mkQ_eq_bot_of_le h]
  simp

theorem relRank_self (X : Submodule k V) : relRank X X = 0 := relRank_of_le le_rfl

theorem map_mkQ_sup_of_le {X D W : Submodule k V} (hD : D ≤ W) :
    (X ⊔ D).map W.mkQ = X.map W.mkQ := by
  rw [Submodule.map_sup, map_mkQ_eq_bot_of_le hD, sup_bot_eq]

theorem relRank_sup_left {X D W : Submodule k V} (hD : D ≤ W) :
    relRank W (X ⊔ D) = relRank W X := by
  rw [relRank, relRank, map_mkQ_sup_of_le hD]

theorem ker_factor {X Y : Submodule k V} (h : Y ≤ X) :
    LinearMap.ker (factor h) = X.map Y.mkQ := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H v =>
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (p := X) v = 0 ↔ _
    rw [Quotient.mk_eq_zero]
    constructor
    · intro hv; exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, hwv⟩
      rw [mkQ_apply, Submodule.Quotient.eq] at hwv
      have := X.sub_mem hw (h hwv)
      simpa using this

/-- **Additivity** of relative ranks along a chain `Y ≤ X ≤ Z`. -/
theorem relRank_trans {X Y Z : Submodule k V} (hYX : Y ≤ X) (hXZ : X ≤ Z) :
    relRank Y Z = relRank Y X + relRank X Z := by
  set W := Z.map Y.mkQ
  set N := X.map Y.mkQ
  have hNW : N ≤ W := Submodule.map_mono hXZ
  have h1 := rank_quotient_add_rank_of_divisionRing (N.comap W.subtype)
  have h2 : Module.rank k (N.comap W.subtype) = Module.rank k N :=
    (comapSubtypeEquivOfLe hNW).rank_eq
  set g := factor hYX ∘ₗ W.subtype
  have hker : LinearMap.ker g = N.comap W.subtype := by
    rw [LinearMap.ker_comp, ker_factor]
  have hrange : LinearMap.range g = Z.map X.mkQ := by
    rw [LinearMap.range_comp, range_subtype, ← Submodule.map_comp, factor_comp_mk]
  have h3 : Module.rank k (W ⧸ N.comap W.subtype) = Module.rank k (Z.map X.mkQ) := by
    rw [← hker, ← hrange]
    exact (LinearMap.quotKerEquivRange g).rank_eq
  change Module.rank k W = Module.rank k N + Module.rank k (Z.map X.mkQ)
  rw [← h1, h2, h3, add_comm]

/-- For `Y ≤ X`: `dim X/Y = dim (X+D)/(Y+D) + dim (X∩D)/(Y∩D)`. -/
theorem relRank_eq_sup_add_inf {X Y : Submodule k V} (D : Submodule k V) (hYX : Y ≤ X) :
    relRank Y X = relRank (Y ⊔ D) (X ⊔ D) + relRank (Y ⊓ D) (X ⊓ D) := by
  have hmod : X ⊓ (Y ⊔ D) = Y ⊔ X ⊓ D := by
    rw [inf_comm, sup_inf_assoc_of_le D hYX, inf_comm D X]
  rw [relRank_trans (le_sup_left : Y ≤ Y ⊔ X ⊓ D) (sup_le hYX inf_le_left), add_comm]
  congr 1
  · -- `dim X/(Y + X∩D) = dim (X+D)/(Y+D)`
    rw [relRank_sup_left (le_sup_right : D ≤ Y ⊔ D)]
    refine relRank_eq_of_inf_eq ?_
    rw [hmod]
    exact inf_eq_right.mpr (sup_le hYX inf_le_left)
  · -- `dim (Y + X∩D)/Y = dim (X∩D)/(Y∩D)`
    rw [sup_comm Y (X ⊓ D), relRank_sup_left (le_rfl : Y ≤ Y)]
    refine relRank_eq_of_inf_eq ?_
    ext v
    simp only [mem_inf]
    tauto

/-- If `dim (X+Y)/Y = 0` then `X ≤ Y`. -/
theorem le_of_relRank_eq_zero {X Y : Submodule k V} (h : relRank Y X = 0) : X ≤ Y := by
  rw [relRank, Submodule.rank_eq_zero] at h
  intro x hx
  have : Y.mkQ x ∈ X.map Y.mkQ := ⟨x, hx, rfl⟩
  rw [h, mem_bot, mkQ_apply, Quotient.mk_eq_zero] at this
  exact this

/-- `dim (X + 0)/0 = dim X`. -/
theorem relRank_bot (X : Submodule k V) : relRank ⊥ X = Module.rank k X := by
  rw [relRank_eq_rank_quotient]
  have : (⊥ : Submodule k V).comap X.subtype = ⊥ := by
    ext x; simp
  rw [this]
  exact (Submodule.quotEquivOfEqBot ⊥ rfl).rank_eq

end WeilCurves
