/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import WeilCurves.ConstantExtension.Split

/-!
# F. K. Schmidt's theorem: there is a divisor of degree one

Let `K` be a function field over a finite field `k` with `q` elements, `k` the full constant
field. Let `δ` be the smallest positive degree of a divisor (`WeilCurves.FunctionField.index`).
We show `δ = 1` (`WeilCurves.FunctionField.exists_deg_eq_one`), following the coefficient-growth
form of the classical argument (cf. van Frankenhuijsen, arXiv:0806.0044, §2.2, where it is phrased
with the pole of the zeta function at `s = 1`):

* every place of `K` has degree divisible by `δ`, so above each place `P` of `K` there are exactly
  `δ` places of the constant field extension `K_δ`, all of degree `deg P`
  (`WeilCurves.FunctionField.places_above`);
* if `δ ≥ 2`, choosing two of them above each `P` gives an injection of pairs of effective
  divisors of `K` into effective divisors of `K_δ`, preserving degree; so
  `A'(δm) ≥ ∑_j A(δj) A(δ(m - j)) ≥ (m - c) q^{δm - 2g}`;
* but Riemann–Roch on `K_δ` (a function field over `k`) gives `A'(n) ≤ C q^n`. Contradiction.
-/

namespace WeilCurves.FunctionField

open Divisor

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [IsFunctionField k K]

/-! ### Upper bound for the number of effective divisors -/

/-- `#{E ≥ 0 | E ∼ A} ≤ q ^ ℓ(A)` (no assumption on the constant field). -/
theorem card_effClass_le (A : Divisor k K) : Nat.card (effClass A) ≤ Nat.card k ^ ell A := by
  classical
  have : Finite (L A) := Module.finite_of_finite k
  have : Fintype (L A) := Fintype.ofFinite _
  have : Fintype k := Fintype.ofFinite _
  let S := {f : L A // f ≠ 0}
  have hS0 : ∀ s : S, ((s.1 : K)) ≠ 0 := fun s h ↦ s.2 (Subtype.ext h)
  let Ψ : S → effClass A := fun s ↦ ⟨A + div k (s.1 : K),
    (mem_L_of_ne_zero (hS0 s)).mp s.1.2, by
      rw [add_sub_cancel_left]; exact div_mem_principal (hS0 s)⟩
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨E, hE, hEA⟩
    obtain ⟨f, hf, hfd⟩ := mem_principal.mp hEA
    have hEq : E = A + div k f := by rw [hfd]; abel
    have hfL : f ∈ L A := (mem_L_of_ne_zero hf).mpr (hEq ▸ hE)
    exact ⟨⟨⟨f, hfL⟩, fun h ↦ hf (congrArg Subtype.val h)⟩, Subtype.ext hEq.symm⟩
  calc Nat.card (effClass A) ≤ Nat.card S := Nat.card_le_card_of_surjective Ψ hΨ
    _ ≤ Nat.card (L A) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = Nat.card k ^ ell A := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k) (V := L A),
        Nat.card_eq_fintype_card, ell]

/-- `#Cl(n) ≤ #Cl(0)`. -/
theorem card_Cl_le (n : ℤ) : Nat.card (Cl k K n) ≤ classNumber k K := by
  rcases (Cl k K n).eq_empty_or_nonempty with h | ⟨c, hc⟩
  · rw [h]; simp
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
  simp only [Cl, Set.mem_setOf_eq, Pic.deg_mk] at hc
  rw [← hc, card_Cl]

/-- **`A_n ≤ h q^{n - riemannConst}`** for `n` large (no assumption on the constant field). -/
theorem exists_effCount_le : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    effCount k K n ≤ classNumber k K * Nat.card k ^ (n - riemannConst k K).toNat := by
  obtain ⟨N, hN⟩ := riemann_equality (k := k) (K := K)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [effCount_eq_sum]
  calc ∑ c ∈ (finite_Cl (k := k) (K := K) n).toFinset,
        Nat.card (effClass (Quotient.out c : Divisor k K))
      ≤ ∑ c ∈ (finite_Cl (k := k) (K := K) n).toFinset,
          Nat.card k ^ (n - riemannConst k K).toNat := by
        refine Finset.sum_le_sum fun c hc ↦ (card_effClass_le _).trans (le_of_eq ?_)
        rw [Set.Finite.mem_toFinset] at hc
        have hdeg : (Quotient.out c : Divisor k K).deg = n := by
          rw [← Pic.deg_mk, QuotientAddGroup.out_eq']; exact hc
        have := hN _ (hdeg ▸ hn)
        congr 1
        omega
    _ = Nat.card (Cl k K n) * Nat.card k ^ (n - riemannConst k K).toNat := by
        rw [Finset.sum_const, smul_eq_mul, ← Nat.card_eq_card_finite_toFinset]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_Cl_le n)

/-! ### The index: the smallest positive degree of a divisor -/

variable (k K) in
theorem exists_pos_deg : ∃ n : ℕ, 0 < n ∧ ∃ D : Divisor k K, D.deg = n := by
  obtain P : Place k K := Classical.arbitrary _
  exact ⟨P.deg, P.deg_pos, Finsupp.single P 1, by rw [deg_single, one_mul]⟩

open Classical in
variable (k K) in
/-- The index `δ`: the smallest positive degree of a divisor. -/
noncomputable def index : ℕ := Nat.find (exists_pos_deg k K)

theorem index_pos : 0 < index k K := by
  classical exact (Nat.find_spec (exists_pos_deg k K)).1

theorem exists_deg_eq_index : ∃ D : Divisor k K, D.deg = index k K := by
  classical exact (Nat.find_spec (exists_pos_deg k K)).2

/-- Every divisor has degree divisible by the index. -/
theorem index_dvd_deg (D : Divisor k K) : (index k K : ℤ) ∣ D.deg := by
  classical
  obtain ⟨D₀, hD₀⟩ := exists_deg_eq_index (k := k) (K := K)
  have hδ : (0 : ℤ) < index k K := by exact_mod_cast index_pos
  set r := D.deg % index k K
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hδ.ne'
  have hr1 : r < index k K := Int.emod_lt_of_pos _ hδ
  have hD' : (D - (D.deg / index k K) • D₀).deg = r := by
    rw [deg_sub, deg_zsmul, hD₀]
    have := Int.emod_add_mul_ediv D.deg (index k K)
    simp only [r]; linarith
  by_contra hndvd
  have hrpos : 0 < r := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · exact absurd (Int.dvd_of_emod_eq_zero h.symm) hndvd
  have hmin := Nat.find_min' (exists_pos_deg k K) (m := r.toNat)
    ⟨by omega, _, by rw [hD']; omega⟩
  change index k K ≤ r.toNat at hmin
  omega

theorem index_dvd_place_deg (P : Place k K) : index k K ∣ P.deg := by
  have := index_dvd_deg (Finsupp.single P (1 : ℤ))
  rw [deg_single, one_mul] at this
  exact_mod_cast this

/-! ### Lower bound for the number of effective divisors -/

/-- `A_n ≥ q^{n - g}` for `n` a multiple of the index with `n > 2g - 2`, `n ≥ g`. -/
theorem effCount_ge (hk : IsFullConstantField k K) {n : ℤ} (hdvd : (index k K : ℤ) ∣ n)
    (hn : 2 * genus k K - 2 < n) (hng : genus k K ≤ n) :
    Nat.card k ^ (n - genus k K).toNat ≤ effCount k K n := by
  obtain ⟨D₀, hD₀⟩ := exists_deg_eq_index (k := k) (K := K)
  obtain ⟨c, hc⟩ := hdvd
  have hcl : 1 ≤ Nat.card (Cl k K n) := by
    have : Finite (Cl k K n) := (finite_Cl n).to_subtype
    refine Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨⟨QuotientAddGroup.mk (c • D₀), ?_⟩⟩,
      inferInstance⟩)
    simp only [Cl, Set.mem_setOf_eq, Pic.deg_mk, deg_zsmul, hD₀, hc]; ring
  have h := effCount_mul_of_deg_gt hk hn
  set a := (n - genus k K).toNat
  have he : (n + 1 - genus k K).toNat = a + 1 := by omega
  rw [he] at h
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  have hqa : 1 ≤ Nat.card k ^ a := Nat.one_le_pow _ _ (by omega)
  have hqa1 : 1 ≤ Nat.card k ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  have h' : (effCount k K n : ℤ) * (Nat.card k - 1) =
      Nat.card (Cl k K n) * ((Nat.card k : ℤ) ^ (a + 1) - 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.card k), Nat.cast_sub hqa1] at this
    exact this
  have hq' : (2 : ℤ) ≤ Nat.card k := by exact_mod_cast hq
  have hqa' : (1 : ℤ) ≤ (Nat.card k : ℤ) ^ a := by exact_mod_cast hqa
  have hcl' : (1 : ℤ) ≤ Nat.card (Cl k K n) := by exact_mod_cast hcl
  have key : ((Nat.card k : ℤ) ^ a) * (Nat.card k - 1) ≤
      (effCount k K n : ℤ) * (Nat.card k - 1) := by
    rw [h', pow_succ]
    have h1 : (0 : ℤ) ≤ (Nat.card k : ℤ) ^ a * Nat.card k - 1 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right hcl' h1
    nlinarith
  have := le_of_mul_le_mul_right key (by omega)
  exact_mod_cast this

/-! ### Transporting divisors along a section of the restriction map -/

section Transport

variable {L : Type*} [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  [FiniteDimensional K L] {c : Place k K → Place k L}

omit [Finite k] [IsFunctionField k K] in
theorem section_injective (hc : ∀ P, (c P).restrict (K := K) = P) : Function.Injective c :=
  fun P P' h ↦ by rw [← hc P, ← hc P', h]

omit [Finite k] [IsFunctionField k K] [FiniteDimensional K L] [Algebra K L]
  [IsScalarTower k K L] in
theorem deg_mapDomain (hdeg : ∀ P, (c P).deg = P.deg) (E : Divisor k K) :
    Divisor.deg (Finsupp.mapDomain c E : Divisor k L) = E.deg := by
  simp only [Divisor.deg]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  simp [hdeg]

omit [Finite k] [IsFunctionField k K] in
theorem mapDomain_nonneg (hc : ∀ P, (c P).restrict (K := K) = P) {E : Divisor k K}
    (hE : 0 ≤ E) : 0 ≤ (Finsupp.mapDomain c E : Divisor k L) := by
  intro Q
  by_cases hQ : Q ∈ Set.range c
  · obtain ⟨P, rfl⟩ := hQ
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    rw [Finsupp.mapDomain_apply (section_injective hc)]
    exact hE P
  · simp only [Finsupp.coe_zero, Pi.zero_apply]
    rw [Finsupp.mapDomain_notin_range _ _ hQ]

end Transport

/-! ### Schmidt's theorem -/

/-- **F. K. Schmidt's theorem**: the index is `1` (`k` the full constant field). -/
theorem index_eq_one (hk : IsFullConstantField k K) : index k K = 1 := by
  classical
  have : Fact (IsFullConstantField k K) := ⟨hk⟩
  by_contra hne
  have hδ2 : 2 ≤ index k K := by have := index_pos (k := k) (K := K); omega
  set δ := index k K
  have : NeZero δ := ⟨by omega⟩
  -- two distinct places of degree `deg P` above each place `P` of `K`
  have htwo : ∀ P : Place k K, ∃ Q₁ Q₂ : Place k (ConstExt k K δ),
      Q₁.restrict (K := K) = P ∧ Q₂.restrict (K := K) = P ∧ Q₁ ≠ Q₂ ∧
      Q₁.deg = P.deg ∧ Q₂.deg = P.deg := by
    intro P
    obtain ⟨hfin, hcard, hdeg⟩ := places_above δ P (index_dvd_place_deg P)
    obtain ⟨Q₁, Q₂, h₁, h₂, hne⟩ := (Set.one_lt_ncard_iff hfin).mp (by omega)
    exact ⟨Q₁, Q₂, h₁, h₂, hne, hdeg Q₁ h₁, hdeg Q₂ h₂⟩
  choose c₁ c₂ hc₁ hc₂ hne₁₂ hd₁ hd₂ using htwo
  set L := ConstExt k K δ
  have hdisj₁ : ∀ P, c₁ P ∉ Set.range c₂ := by
    rintro P ⟨P', hP'⟩
    have : P' = P := by rw [← hc₂ P', hP', hc₁ P]
    subst this; exact hne₁₂ P' hP'.symm
  have hdisj₂ : ∀ P, c₂ P ∉ Set.range c₁ := by
    rintro P ⟨P', hP'⟩
    have : P' = P := by rw [← hc₁ P', hP', hc₂ P]
    subst this; exact hne₁₂ P' hP'
  have hpair : ∀ E₁ E₂ F₁ F₂ : Divisor k K,
      (Finsupp.mapDomain c₁ E₁ + Finsupp.mapDomain c₂ E₂ : Divisor k L) =
        Finsupp.mapDomain c₁ F₁ + Finsupp.mapDomain c₂ F₂ → E₁ = F₁ ∧ E₂ = F₂ := by
    intro E₁ E₂ F₁ F₂ h
    constructor
    · ext P
      have := congrArg (· (c₁ P)) h
      simpa [Finsupp.mapDomain_apply (section_injective hc₁),
        Finsupp.mapDomain_notin_range _ _ (hdisj₁ P)] using this
    · ext P
      have := congrArg (· (c₂ P)) h
      simpa [Finsupp.mapDomain_apply (section_injective hc₂),
        Finsupp.mapDomain_notin_range _ _ (hdisj₂ P)] using this
  -- constants
  have hg := genus_nonneg hk
  obtain ⟨N, hN⟩ := exists_effCount_le (k := k) (K := L)
  set q := Nat.card k with hq_def
  have hq : 2 ≤ q := Finite.one_lt_card
  set R := (-riemannConst k L).toNat
  set B := classNumber k L * q ^ (R + 2 * (genus k K).toNat)
  set M := 2 * (genus k K).toNat + 1
  set m := 2 * M + B + N.toNat
  set J := Finset.Icc M (m - M)
  have hJcard : J.card = m - 2 * M + 1 := by
    rw [Nat.card_Icc]; omega
  have hδ0 : (0 : ℤ) < δ := by exact_mod_cast index_pos
  -- the injection
  have hfinK : ∀ n : ℤ, Finite (effDeg k K n) := fun n ↦
    (finite_setOf_effective_deg_eq n).to_subtype
  have hfinL : Finite (effDeg k L ((δ : ℤ) * m)) :=
    (finite_setOf_effective_deg_eq _).to_subtype
  let Φ : (Σ j : J, effDeg k K ((δ : ℤ) * j) × effDeg k K ((δ : ℤ) * (m - j : ℕ))) →
      effDeg k L ((δ : ℤ) * m) := fun x ↦
    ⟨Finsupp.mapDomain c₁ x.2.1.1 + Finsupp.mapDomain c₂ x.2.2.1,
      add_nonneg (mapDomain_nonneg hc₁ x.2.1.2.1) (mapDomain_nonneg hc₂ x.2.2.2.1), by
        rw [deg_add, deg_mapDomain hd₁, deg_mapDomain hd₂, x.2.1.2.2, x.2.2.2.2]
        have hj := (Finset.mem_Icc.mp x.1.2).2
        have : ((m - x.1.1 : ℕ) : ℤ) = m - x.1.1 := by
          rw [Nat.cast_sub (by omega)]
        rw [this]; ring⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨j, E₁, E₂⟩ ⟨j', F₁, F₂⟩ h
    obtain ⟨h₁, h₂⟩ := hpair _ _ _ _ (congrArg Subtype.val h)
    have hjj : j = j' := by
      have := congrArg Divisor.deg h₁
      rw [E₁.2.2, F₁.2.2] at this
      exact Subtype.ext (by exact_mod_cast (mul_left_cancel₀ hδ0.ne' this))
    subst hjj
    have hE : E₁ = F₁ := Subtype.ext h₁
    have hF : E₂ = F₂ := Subtype.ext h₂
    subst hE; subst hF; rfl
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_sigma] at hcard
  simp only [Nat.card_prod] at hcard
  set E := ((δ : ℤ) * m - 2 * genus k K).toNat
  have hlow : ∀ j : J, q ^ E ≤ Nat.card (effDeg k K ((δ : ℤ) * j)) *
      Nat.card (effDeg k K ((δ : ℤ) * (m - j : ℕ))) := by
    intro j
    have hj := Finset.mem_Icc.mp j.2
    have hδ1 : (1 : ℤ) ≤ δ := by omega
    have hjM : ((M : ℕ) : ℤ) ≤ j := by exact_mod_cast hj.1
    have hmj : ((M : ℕ) : ℤ) ≤ ((m - j.1 : ℕ) : ℤ) := by
      have h2 := hj.2
      exact_mod_cast (by omega : M ≤ m - j.1)
    have hMg : 2 * genus k K < (M : ℤ) := by simp only [M]; push_cast; omega
    have e₁ := effCount_ge hk (n := (δ : ℤ) * j) (Dvd.intro _ rfl) (by nlinarith) (by nlinarith)
    have e₂ := effCount_ge hk (n := (δ : ℤ) * (m - j : ℕ)) (Dvd.intro _ rfl) (by nlinarith)
      (by nlinarith)
    have hsum : ((δ : ℤ) * j - genus k K).toNat +
        ((δ : ℤ) * (m - j : ℕ) - genus k K).toNat = E := by
      have : ((m - j.1 : ℕ) : ℤ) = m - j.1 := by rw [Nat.cast_sub (by omega)]
      simp only [E]; rw [this]
      have h1 : 0 ≤ (δ : ℤ) * j - genus k K := by nlinarith
      have h2 : 0 ≤ (δ : ℤ) * (m - j.1) - genus k K := by
        have : ((M : ℕ) : ℤ) ≤ (m : ℤ) - j.1 := by rw [← this]; exact hmj
        nlinarith
      have hdist : (δ : ℤ) * (m - j.1) = δ * m - δ * j.1 := by ring
      omega
    rw [← hsum, pow_add]
    exact Nat.mul_le_mul e₁ e₂
  have hsumlow : J.card * q ^ E ≤ Nat.card (effDeg k L ((δ : ℤ) * m)) := by
    refine le_trans ?_ hcard
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset J) _ (q ^ E) (fun j _ ↦ hlow j)
    rwa [Finset.card_univ, Fintype.card_coe, smul_eq_mul] at this
  have hup := hN ((δ : ℤ) * m) (by
    have : (N.toNat : ℤ) ≤ m := by simp only [m]; push_cast; omega
    have hm0 : (0 : ℤ) ≤ m := by positivity
    nlinarith [Int.self_le_toNat N])
  have hexp : ((δ : ℤ) * m - riemannConst k L).toNat ≤ E + (R + 2 * (genus k K).toNat) := by
    simp only [E, R]
    have : 2 * genus k K ≤ (δ : ℤ) * m := by
      have : (M : ℤ) ≤ m := by simp only [m]; push_cast; omega
      have hMg : 2 * genus k K < (M : ℤ) := by simp only [M]; push_cast; omega
      nlinarith
    omega
  have hqpos : 0 < q ^ E := pow_pos (by omega) _
  have h3 : J.card * q ^ E ≤ B * q ^ E := by
    calc J.card * q ^ E ≤ effCount k L ((δ : ℤ) * m) := hsumlow
      _ ≤ classNumber k L * q ^ ((δ : ℤ) * m - riemannConst k L).toNat := hup
      _ ≤ classNumber k L * q ^ (E + (R + 2 * (genus k K).toNat)) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hexp)
      _ = B * q ^ E := by simp only [B]; rw [pow_add]; ring
  have h4 := Nat.le_of_mul_le_mul_right h3 hqpos
  rw [hJcard] at h4
  omega

/-- **F. K. Schmidt's theorem**: a function field over a finite field `k`, with full constant
field `k`, has a divisor of degree `1`. -/
theorem exists_deg_eq_one (hk : IsFullConstantField k K) : ∃ D : Divisor k K, D.deg = 1 := by
  obtain ⟨D, hD⟩ := exists_deg_eq_index (k := k) (K := K)
  exact ⟨D, by rw [hD, index_eq_one hk]; rfl⟩

open PowerSeries in
/-- **Rationality of the zeta function** (unconditional): `(1 - t)(1 - q t) Z(t) = L(t)` with
`L ∈ ℤ[t]` of degree `2g`, `L(0) = 1` and leading coefficient `q^g`. -/
theorem exists_LPolynomial_of_full (hk : IsFullConstantField k K) :
    ∃ L : Polynomial ℤ, L.natDegree = 2 * (genus k K).toNat ∧ L.coeff 0 = 1 ∧
      L.coeff (2 * (genus k K).toNat) = (Nat.card k : ℤ) ^ (genus k K).toNat ∧
      (L : PowerSeries ℤ) = (1 - X) * ((1 - C (Nat.card k : ℤ) * X) * zeta k K) :=
  exists_LPolynomial' hk (exists_deg_eq_one hk)

end WeilCurves.FunctionField
