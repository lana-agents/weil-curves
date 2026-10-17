/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.Hurwitz.Lift
import WeilCurves.FunctionField.RiemannRoch

/-!
# The cotrace of a Weil differential and the Hurwitz genus formula

Let `L / K` be a finite separable extension of function fields over a perfect field `k`, `ω` a
nonzero Weil differential of `K` with divisor `W`, and `D = Con_{L/K} W + Diff(L/K)`.

Stichtenoth (§III.4) defines the cotrace `Cotr(ω) = ω ∘ Tr` of `ω` using the trace of
repartitions and proves `(Cotr ω) = Con W + Diff` (his Theorem 3.4.6). Our repartitions take
values in `L` itself (not in completions), so there is no componentwise trace `A_L → A_K`.
Instead we use the space `R'` of families `(x_P)_P ∈ ∏_P L` with `x_P ∈ O'_P` for almost all
`P` (`repT`), which carries both

* the trace `Tr : R' → A_K`, `(x_P) ↦ (Tr_{L/K} x_P)_P` (`trMap`), and
* the "diagonal over each `P`" `ι : R' → A_L`, `(ι x)_Q = x_{Q|_K}` (`iotaMap`).

By approximation (`exists_approx`), `ι` is onto modulo `A_L(D)`; by the local estimate
`Tr(Λ_P(D)) ⊆ {ord_P ≥ -W(P)}` (`trace_ord_of_inLam`), `ω ∘ Tr` kills `ι⁻¹(A_L(D))`. Hence
`ω ∘ Tr` descends to a `k`-linear form `cotrace` on `A_L` vanishing on `A_L(D) + L`: a Weil
differential of `L` with divisor exactly `D` (`weilDiv_cotrace`; maximality from
`exists_lift`, `exists_lift_sharp`). Comparing with a canonical divisor of `L` gives

**the Hurwitz genus formula** (`riemannHurwitz`):
`2 g_L - 2 = [L : K] (2 g_K - 2) + deg Diff(L/K)`,

where `g = genus k ·` is the genus relative to the base field `k` (Riemann–Roch over `k`); when
`k` is the full constant field of `K` and of `L` this is the usual genus.
-/

open IsDedekindDomain Module

set_option linter.unusedSectionVars false

namespace WeilCurves.FunctionField

/-- A linear form on `W` that vanishes on `ι⁻¹(N)` extends along `ι : W → V` to a linear form on
`V` vanishing on `N`, provided `ι` is onto modulo `N`. -/
theorem exists_extend_linearMap {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (ι : W →ₗ[R] V) (N : Submodule R V)
    (hsurj : ∀ v, ∃ w, v - ι w ∈ N) (ψ : W →ₗ[R] R) (hker : ∀ w, ι w ∈ N → ψ w = 0) :
    ∃ φ : V →ₗ[R] R, (∀ w, φ (ι w) = ψ w) ∧ ∀ n ∈ N, φ n = 0 := by
  set f := N.mkQ ∘ₗ ι
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := N.mkQ_surjective q
    obtain ⟨w, hw⟩ := hsurj v
    refine ⟨w, ?_⟩
    simp only [f, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    exact ((Submodule.Quotient.eq N).mpr hw).symm
  have hle : LinearMap.ker f ≤ LinearMap.ker ψ := by
    intro w hw
    simp only [LinearMap.mem_ker, f, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw ⊢
    exact hker w hw
  set e := f.quotKerEquivOfSurjective hf
  refine ⟨(LinearMap.ker f).liftQ ψ hle ∘ₗ e.symm.toLinearMap ∘ₗ N.mkQ, fun w ↦ ?_, fun n hn ↦ ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    have : N.mkQ (ι w) = f w := rfl
    rw [this, LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).mpr hn, map_zero]

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {L : Type*} [Field L] [Algebra K L]
  [Algebra k L] [IsScalarTower k K L] [PerfectField k] [IsFunctionField k K]
  [IsFunctionField k L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

variable (k K L) in
/-- The families `(x_P)_P ∈ ∏_P L` with `x_P ∈ O'_P` for almost all `P`. -/
noncomputable def repT : Submodule k (Place k K → L) where
  carrier := {x | {P : Place k K | x P ∉ intClo L P}.Finite}
  zero_mem' := by
    change Set.Finite _
    convert Set.finite_empty
    ext P
    simp only [Set.mem_setOf_eq, Pi.zero_apply, Set.mem_empty_iff_false, iff_false, not_not]
    exact (intClo L P).zero_mem
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset fun P hP ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.add_apply] at hP ⊢
    by_contra h
    push Not at h
    exact hP ((intClo L P).add_mem h.1 h.2)
  smul_mem' := by
    intro c x hx
    refine hx.subset fun P hP ↦ ?_
    simp only [Set.mem_setOf_eq, Pi.smul_apply] at hP ⊢
    intro h
    apply hP
    rw [Algebra.smul_def]
    exact (intClo L P).mul_mem (algebraMap_base_mem_intClo c) h

theorem mem_repT {x : Place k K → L} :
    x ∈ repT k K L ↔ {P : Place k K | x P ∉ intClo L P}.Finite := Iff.rfl

variable (K L) in
/-- `ι : R' → A_L`, `(ι x)_Q = x_{Q|_K}`. -/
noncomputable def iotaMap : repT k K L →ₗ[k] Rep k L where
  toFun x := ⟨fun Q ↦ (x : Place k K → L) (Q.restrict (K := K)), by
    refine (finite_setOf_restrict_mem (L := L) _ (mem_repT.mp x.2)).subset fun Q hQ ↦ ?_
    simp only [Set.mem_setOf_eq] at hQ ⊢
    exact fun h ↦ hQ (mem_of_mem_intClo rfl h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem iotaMap_apply (x : repT k K L) (Q : Place k L) :
    (iotaMap K L x : Place k L → L) Q = (x : Place k K → L) (Q.restrict (K := K)) := rfl

variable (K L) in
/-- `Tr : R' → A_K`, `(x_P) ↦ (Tr_{L/K} x_P)_P`. -/
noncomputable def trMap : repT k K L →ₗ[k] Rep k K where
  toFun x := ⟨fun P ↦ Algebra.trace K L ((x : Place k K → L) P), by
    refine (mem_repT.mp x.2).subset fun P hP ↦ ?_
    simp only [Set.mem_setOf_eq] at hP ⊢
    intro h
    apply hP
    simpa using isCodiff_one (L := L) (P := P) _ h⟩
  map_add' x y := by ext1; funext P; simp
  map_smul' c x := by
    ext1; funext P
    simp only [RingHom.id_apply]
    change Algebra.trace K L (c • _) = c • Algebra.trace K L _
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k K L, trace_algebraMap_mul,
      ← Algebra.smul_def]

theorem trMap_apply (x : repT k K L) (P : Place k K) :
    (trMap K L x : Place k K → K) P = Algebra.trace K L ((x : Place k K → L) P) := rfl

/-- The constant family `(z)_P`. -/
noncomputable def diagT (z : L) : repT k K L :=
  ⟨fun _ ↦ z, by
    rw [mem_repT]
    refine ((Place.finite_setOf_notMem z).image (fun Q : Place k L ↦ Q.restrict (K := K))).subset
      fun P hP ↦ ?_
    simp only [Set.mem_setOf_eq, mem_intClo_iff, not_forall] at hP
    obtain ⟨Q, hQ, hz⟩ := hP
    exact ⟨Q, hz, hQ⟩⟩

theorem iotaMap_diagT (z : L) :
    ((iotaMap K L (diagT (k := k) (K := K) z) : Rep k L) : Place k L → L) = diag k L z :=
  rfl

theorem trMap_diagT (z : L) :
    ((trMap K L (diagT (k := k) (K := K) z) : Rep k K) : Place k K → K) =
      diag k K (Algebra.trace K L z) := rfl

/-! ### Surjectivity of `ι` modulo `A_L(D)` -/

/-- Every place `P` of `K` admits a place of `L` not above it. -/
theorem exists_place_not_above (P : Place k K) :
    ∃ Q₀ : Place k L, Q₀.restrict (K := K) ≠ P := by
  obtain ⟨t, ht, htP⟩ := P.exists_transcendental_mem
  have htL : Transcendental k (algebraMap K L t) :=
    (transcendental_algebraMap_iff (algebraMap K L).injective).mpr ht
  obtain ⟨Q₀, hQ₀⟩ := Place.exists_ord_neg htL
  refine ⟨Q₀, fun h ↦ ?_⟩
  have : algebraMap K L t ∈ Q₀.1 := Place.mem_restrict.mp (h ▸ htP)
  have := Q₀.ord_nonneg_of_mem this
  omega

theorem exists_iotaMap_sub_mem (D : Divisor k L) (α : Rep k L) :
    ∃ x : repT k K L, ∀ Q, (α : Place k L → L) Q - (iotaMap K L x : Place k L → L) Q = 0 ∨
      -D Q ≤ Q.ord ((α : Place k L → L) Q - (iotaMap K L x : Place k L → L) Q) := by
  classical
  set bad : Set (Place k L) := {Q | (α : Place k L → L) Q ∉ Q.1} ∪ D.support
  have hbad : bad.Finite := (mem_repartitions.mp α.2).union D.support.finite_toSet
  set badK : Set (Place k K) := (fun Q : Place k L ↦ Q.restrict (K := K)) '' bad
  have happrox : ∀ P : Place k K, ∃ y : L, ∀ Q : Place k L, Q.restrict (K := K) = P →
      (α : Place k L → L) Q - y = 0 ∨ -D Q ≤ Q.ord ((α : Place k L → L) Q - y) := by
    intro P
    obtain ⟨Q₀, hQ₀⟩ := exists_place_not_above (L := L) P
    set T := (finite_setOf_restrict_eq (L := L) P).toFinset
    obtain ⟨y, hy⟩ := exists_approx D T Q₀ (by simpa [T] using hQ₀) (α : Place k L → L)
    exact ⟨y, fun Q hQ ↦ hy Q (by simpa [T] using hQ)⟩
  set x : Place k K → L := fun P ↦ if P ∈ badK then (happrox P).choose else 0
  have hx : x ∈ repT k K L := by
    refine (hbad.image (fun Q : Place k L ↦ Q.restrict (K := K))).subset fun P hP ↦ ?_
    by_contra hPb
    simp only [Set.mem_setOf_eq, x] at hP
    rw [if_neg (show P ∉ badK from hPb)] at hP
    exact hP (intClo L P).zero_mem
  refine ⟨⟨x, hx⟩, fun Q ↦ ?_⟩
  rw [iotaMap_apply]
  change _ - x _ = 0 ∨ _ ≤ Q.ord (_ - x _)
  by_cases hQ : Q.restrict (K := K) ∈ badK
  · simp only [x, if_pos hQ]
    exact (happrox _).choose_spec Q rfl
  · simp only [x, if_neg hQ, sub_zero]
    have hQb : Q ∉ bad := fun h ↦ hQ ⟨Q, h, rfl⟩
    simp only [bad, Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe,
      Finsupp.notMem_support_iff] at hQb
    by_cases h0 : (α : Place k L → L) Q = 0
    · exact Or.inl h0
    · exact Or.inr (by rw [hQb.2, neg_zero]; exact Q.ord_nonneg_of_mem hQb.1)

/-! ### The cotrace -/

/-- `ι x ∈ A_L(B)` iff `x_P ∈ Λ_P(B)` for every `P`. -/
theorem iotaMap_mem_adeleSub_iff {B : Divisor k L} {x : repT k K L} :
    (iotaMap K L x : Place k L → L) ∈ adeleSub B ↔
      ∀ P : Place k K, InLam P B ((x : Place k K → L) P) := by
  constructor
  · intro h P Q hQ
    have := h Q
    rwa [iotaMap_apply, hQ] at this
  · intro h Q
    rw [iotaMap_apply]
    exact h _ Q rfl

variable (K L) in
theorem exists_cotrace (ω : Dual k (Rep k K)) (hω : IsWeil ω) (h0 : ω ≠ 0) :
    ∃ φ : Dual k (Rep k L), (∀ x, φ (iotaMap K L x) = ω (trMap K L x)) ∧
      ∀ α : Rep k L, (α : Place k L → L) ∈ adeleSub (conormOf L (weilDiv ω) + different k K L) →
        φ α = 0 := by
  set D := conormOf L (weilDiv ω) + different k K L
  set N : Submodule k (Rep k L) := (adeleSub D).comap ((repartitions k L).restrictScalars k).subtype
  obtain ⟨φ, h1, h2⟩ := exists_extend_linearMap (iotaMap K L) N
    (fun α ↦ by
      obtain ⟨x, hx⟩ := exists_iotaMap_sub_mem (K := K) D α
      exact ⟨x, fun Q ↦ hx Q⟩)
    (ω ∘ₗ trMap K L) (fun x hx ↦ by
      have hW := mem_weilSub_weilDiv hω h0
      rw [mem_weilSub] at hW
      apply hW
      change (trMap K L x : Place k K → K) ∈ adeleSub _ ⊔ diagK k K
      refine Submodule.mem_sup_left fun P ↦ ?_
      rw [trMap_apply]
      exact trace_ord_of_inLam (weilDiv ω) (iotaMap_mem_adeleSub_iff.mp hx P))
  exact ⟨φ, h1, fun α hα ↦ h2 α hα⟩

variable (K L) in
/-- The **cotrace** `Cotr_{L/K}(ω)` of a Weil differential `ω` of `K`: the linear form on `A_L`
with `Cotr(ω)(ι x) = ω(Tr x)` vanishing on `A_L(Con (ω) + Diff)`. -/
noncomputable def cotrace (ω : Dual k (Rep k K)) : Dual k (Rep k L) :=
  open Classical in
  if h : IsWeil ω ∧ ω ≠ 0 then (exists_cotrace K L ω h.1 h.2).choose else 0

theorem cotrace_iotaMap {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) (x : repT k K L) :
    cotrace K L ω (iotaMap K L x) = ω (trMap K L x) := by
  rw [cotrace, dif_pos ⟨hω, h0⟩]
  exact (exists_cotrace K L ω hω h0).choose_spec.1 x

theorem cotrace_eq_zero {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) (α : Rep k L)
    (hα : (α : Place k L → L) ∈ adeleSub (conormOf L (weilDiv ω) + different k K L)) :
    cotrace K L ω α = 0 := by
  rw [cotrace, dif_pos ⟨hω, h0⟩]
  exact (exists_cotrace K L ω hω h0).choose_spec.2 α hα

/-- `Cotr(ω) ∈ Ω_L(Con (ω) + Diff)`. -/
theorem cotrace_mem_weilSub {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0) :
    cotrace K L ω ∈ weilSub (conormOf L (weilDiv ω) + different k K L) := by
  rw [mem_weilSub]
  intro α hα
  change (α : Place k L → L) ∈ adeleSub _ ⊔ diagK k L at hα
  obtain ⟨a, ha, _, ⟨z, rfl⟩, haz⟩ := Submodule.mem_sup.mp hα
  set d := diagT (k := k) (K := K) z
  have hsplit : α = (α - iotaMap K L d) + iotaMap K L d := by abel
  rw [hsplit, map_add, cotrace_iotaMap hω h0]
  have h1 : cotrace K L ω (α - iotaMap K L d) = 0 := by
    refine cotrace_eq_zero hω h0 _ ?_
    have : ((α - iotaMap K L d : Rep k L) : Place k L → L) = a := by
      change (α : Place k L → L) - diag k L z = a
      rw [← haz]; abel
    rw [this]; exact ha
  have h2 : ω (trMap K L d) = 0 := by
    have hW := mem_weilSub_weilDiv hω h0
    rw [mem_weilSub] at hW
    apply hW
    change (trMap K L d : Place k K → K) ∈ adeleSub _ ⊔ diagK k K
    exact Submodule.mem_sup_right ⟨_, (trMap_diagT z).symm⟩
  rw [h1, h2, add_zero]

/-- `Cotr(ω) ∉ Ω_L(Con (ω) + Diff + Q₀)` for every place `Q₀` of `L`. -/
theorem cotrace_notMem_weilSub {ω : Dual k (Rep k K)} (hω : IsWeil ω) (h0 : ω ≠ 0)
    (Q₀ : Place k L) :
    cotrace K L ω ∉ weilSub (conormOf L (weilDiv ω) + different k K L + Finsupp.single Q₀ 1) := by
  classical
  set W := weilDiv ω
  set P := Q₀.restrict (K := K)
  set D := conormOf L W + different k K L
  -- a repartition `b ∈ A_K(W + P)` with `ω b ≠ 0`
  have hnot : ω ∉ weilSub (W + Finsupp.single P 1) := by
    rw [mem_weilSub_iff hω h0]
    intro h
    have := h P
    simp only [W, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
    omega
  rw [mem_weilSub] at hnot
  push Not at hnot
  obtain ⟨a, ha, hωa⟩ := hnot
  change (a : Place k K → K) ∈ adeleSub _ ⊔ diagK k K at ha
  obtain ⟨b, hb, _, ⟨u, rfl⟩, hbu⟩ := Submodule.mem_sup.mp ha
  have hbrep : b ∈ (repartitions k K).restrictScalars k := by
    have : b = (a : Place k K → K) - diag k K u := by rw [← hbu]; abel
    rw [this]
    exact Submodule.sub_mem _ a.2 (diagK_le ⟨u, rfl⟩)
  set b' : Rep k K := ⟨b, hbrep⟩
  have hωb : ω b' ≠ 0 := by
    have hW := mem_weilSub_weilDiv hω h0
    rw [mem_weilSub] at hW
    have hd : ω ⟨diag k K u, diagK_le ⟨u, rfl⟩⟩ = 0 :=
      hW _ (Submodule.mem_sup_right (show diag k K u ∈ diagK k K from ⟨u, rfl⟩))
    have : a = b' + ⟨diag k K u, diagK_le ⟨u, rfl⟩⟩ := Subtype.ext hbu.symm
    rw [this, map_add, hd, add_zero] at hωa
    exact hωa
  -- lift `b` componentwise
  have hlift : ∀ P' : Place k K, ∃ z : L, Algebra.trace K L z = b P' ∧
      InLam P' (D + Finsupp.single Q₀ 1) z := by
    intro P'
    by_cases hP' : P' = P
    · rw [hP']
      have hbP := hb P
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at hbP
      exact exists_lift_sharp W rfl hbP
    · have hbP := hb P'
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg (Ne.symm hP'),
        add_zero] at hbP
      obtain ⟨z, hz, hzL⟩ := exists_lift (L := L) W hbP
      refine ⟨z, hz, hzL.mono ?_⟩
      exact le_add_of_nonneg_right (Finsupp.single_nonneg.mpr zero_le_one)
  set x : Place k K → L := fun P' ↦ (hlift P').choose
  have hxtr : ∀ P', Algebra.trace K L (x P') = b P' := fun P' ↦ (hlift P').choose_spec.1
  have hxL : ∀ P', InLam P' (D + Finsupp.single Q₀ 1) (x P') :=
    fun P' ↦ (hlift P').choose_spec.2
  have hxT : x ∈ repT k K L := by
    refine ((D + Finsupp.single Q₀ 1).support.finite_toSet.image
      (fun Q : Place k L ↦ Q.restrict (K := K))).subset fun P' hP' ↦ ?_
    simp only [Set.mem_setOf_eq] at hP'
    by_contra hcon
    apply hP'
    refine (hxL P').mem_intClo fun Q hQ ↦ ?_
    by_contra hpos
    exact hcon ⟨Q, Finsupp.mem_support_iff.mpr (by omega), hQ⟩
  set xT : repT k K L := ⟨x, hxT⟩
  have htr : trMap K L xT = b' := Subtype.ext (funext hxtr)
  have hmem : iotaMap K L xT ∈ repSub (D + Finsupp.single Q₀ 1) := by
    change (iotaMap K L xT : Place k L → L) ∈ adeleSub _ ⊔ diagK k L
    exact Submodule.mem_sup_left (iotaMap_mem_adeleSub_iff.mpr hxL)
  intro hmemW
  rw [mem_weilSub] at hmemW
  have := hmemW _ hmem
  rw [cotrace_iotaMap hω h0, htr] at this
  exact hωb this

end WeilCurves.FunctionField
