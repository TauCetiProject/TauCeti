/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import TauCeti.Analysis.Normed.Ring.UnitBall
public import TauCeti.Topology.Algebra.Valued.Integer

/-!
# Discrete valuation rings and finite residue fields of nonarchimedean fields

Let `K` be a normed field with an ultrametric norm, with valuation ring `𝒪[K]` (the closed unit
ball) and residue field `𝓀[K]`. This file collects criteria, phrased with the norm, for `𝒪[K]` to
be a discrete valuation ring and for `𝓀[K]` to be finite, and the resulting finite-dimensionality
of `K` over a complete field of scalars.

* If `𝒪[K]` is a discrete valuation ring, the norm of every nonzero element is an integer power of
  the norm of a uniformiser.
* Conversely, `𝒪[K]` is a discrete valuation ring as soon as the nonzero norms are the integer
  powers of some `‖π‖ ∈ (0, 1)`. Consequently a nontrivially normed field embedded isometrically
  into a field with discrete valuation ring has a discrete valuation ring as well: a nontrivially
  valued subfield of a discretely valued field is discretely valued.
* If every element `a` of norm at most `1` satisfies `‖a ^ q - a‖ < 1` for some `q > 1`, every
  residue is a root of `X ^ q - X`, so `𝓀[K]` is finite with at most `q` elements.
* By Riesz's theorem, a field whose valuation ring is a discrete valuation ring with finite
  residue field is finite-dimensional over every complete nontrivially normed field acting
  continuously on it: its valuation ring is a totally bounded neighbourhood of `0`.

These are the inputs for recognising a subfield of a discretely valued `p`-adic field, such as the
field fixed by a Frobenius lift, as a finite extension of `ℚ_[p]`.

## Main results

* `Valued.integer.exists_norm_eq_zpow_of_irreducible`: norms of nonzero elements are integer
  powers of the norm of a uniformiser.
* `Valued.integer.isDiscreteValuationRing_of_norm_eq_zpow`: the valuation ring is a discrete
  valuation ring when the nonzero norms are the integer powers of some `‖π‖ ∈ (0, 1)`.
* `RingHom.isDiscreteValuationRing_integer_of_norm_map_eq`: a nontrivially normed field embedded
  isometrically into a discretely valued field is discretely valued.
* `Valued.integer.pow_eq_self_of_norm_pow_sub_lt_one`,
  `Valued.integer.finite_residueField_of_norm_pow_sub_lt_one` and
  `Valued.integer.natCard_residueField_le_of_norm_pow_sub_lt_one`: the residue field consists of
  roots of `X ^ q - X`, hence is finite with at most `q` elements.
* `Valued.integer.finiteDimensional_of_finite_residueField`: a field with discrete valuation ring
  and finite residue field is finite-dimensional over a complete nontrivially normed field of
  scalars.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §1, and Chapter II, §1.
-/

public section

open IsLocalRing Polynomial
open scoped NormedField Valued

namespace Valued.integer

section Discrete

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- If every nonzero norm of a nonarchimedean field `K` is an integer power of `‖π‖` for some
`0 < ‖π‖ < 1`, the valuation ring `𝒪[K]` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_norm_eq_zpow {π : K} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hdisc : ∀ x : K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) : IsDiscreteValuationRing 𝒪[K] := by
  have heq : Subring.unitClosedBall K = 𝒪[K] := Subring.ext fun x ↦ by
    rw [Subring.mem_unitClosedBall, mem_iff]
  have : IsPrincipalIdealRing 𝒪[K] :=
    heq ▸ TauCeti.isPrincipalIdealRing_unitClosedBall_of_norm_eq_zpow hπ0 hπ1 hdisc
  refine { not_a_field' := fun h ↦ ?_ }
  have hmem : (⟨π, mem_iff.2 hπ1.le⟩ : 𝒪[K]) ∈ IsLocalRing.maximalIdeal 𝒪[K] :=
    mem_maximalIdeal_iff.2 hπ1
  rw [h, Ideal.mem_bot, Subtype.ext_iff] at hmem
  exact (norm_pos_iff.1 hπ0) hmem

omit [IsUltrametricDist K] in
/-- If `ϖ` has the largest norm among the elements of norm less than `1`, every element whose norm
lies in `(‖ϖ‖ ^ m, 1]` has norm a power of `‖ϖ‖`. -/
private theorem exists_norm_eq_pow_of_forall_norm_lt_one {ϖ : K} (hϖ0 : ϖ ≠ 0)
    (hϖ : ∀ y : K, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) :
    ∀ m : ℕ, ∀ x : K, ‖ϖ‖ ^ m < ‖x‖ → ‖x‖ ≤ 1 → ∃ n : ℕ, ‖x‖ = ‖ϖ‖ ^ n := by
  have hϖpos : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  intro m
  induction m with
  | zero =>
    intro x hx hx1
    rw [pow_zero] at hx
    exact absurd hx1 hx.not_ge
  | succ m ih =>
    intro x hx hx1
    rcases hx1.lt_or_eq with hlt | heq
    · obtain ⟨n, hn⟩ := ih (x / ϖ) (by
        rw [norm_div, lt_div_iff₀ hϖpos, ← pow_succ]
        exact hx) (by
        rw [norm_div, div_le_one hϖpos]
        exact hϖ x hlt)
      refine ⟨n + 1, ?_⟩
      rw [norm_div, div_eq_iff hϖpos.ne'] at hn
      rw [hn, pow_succ]
    · exact ⟨0, by simp [heq]⟩

omit [IsUltrametricDist K] in
/-- If `ϖ` has the largest norm among the elements of norm less than `1`, every nonzero norm is an
integer power of `‖ϖ‖`. -/
private theorem exists_norm_eq_zpow_of_forall_norm_lt_one {ϖ : K} (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1)
    (hϖ : ∀ y : K, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) {x : K} (hx : x ≠ 0) : ∃ k : ℤ, ‖x‖ = ‖ϖ‖ ^ k := by
  have key {y : K} (hy0 : y ≠ 0) (hy1 : ‖y‖ ≤ 1) : ∃ n : ℕ, ‖y‖ = ‖ϖ‖ ^ n := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hy0) hϖ1
    exact exists_norm_eq_pow_of_forall_norm_lt_one hϖ0 hϖ m y hm hy1
  rcases le_total ‖x‖ 1 with h | h
  · obtain ⟨n, hn⟩ := key hx h
    exact ⟨n, by simpa using hn⟩
  · obtain ⟨n, hn⟩ := key (inv_ne_zero hx) (by simpa using inv_le_one_of_one_le₀ h)
    refine ⟨-n, ?_⟩
    rw [norm_inv] at hn
    rw [zpow_neg, zpow_natCast, ← hn, inv_inv]

/-- If the valuation ring `𝒪[K]` of a nonarchimedean field is a discrete valuation ring with
uniformiser `ϖ`, the norm of every nonzero element of `K` is an integer power of `‖ϖ‖`. -/
theorem exists_norm_eq_zpow_of_irreducible [IsDiscreteValuationRing 𝒪[K]] {ϖ : 𝒪[K]}
    (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖(ϖ : K)‖ ^ n := by
  refine exists_norm_eq_zpow_of_forall_norm_lt_one (fun h ↦ hϖ.ne_zero (Subtype.ext h))
    (norm_irreducible_lt_one hϖ) (fun y hy ↦ ?_) hx
  -- An element of norm less than `1` lies in the maximal ideal `(ϖ)`.
  have hmem : (⟨y, mem_iff.2 hy.le⟩ : 𝒪[K]) ∈ Ideal.span {ϖ} := by
    rw [← hϖ.maximalIdeal_eq, mem_maximalIdeal_iff]
    exact hy
  exact dvd_iff_norm_le.1 (Ideal.mem_span_singleton.1 hmem)

/-- A nontrivially normed field `L` admitting a norm-preserving ring homomorphism into a
nonarchimedean field `K` whose valuation ring is a discrete valuation ring has a discrete
valuation ring as well: a nontrivially valued subfield of a discretely valued field is discretely
valued. -/
theorem _root_.RingHom.isDiscreteValuationRing_integer_of_norm_map_eq {L : Type*}
    [NontriviallyNormedField L] [IsUltrametricDist L] [IsDiscreteValuationRing 𝒪[K]]
    (φ : L →+* K) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : IsDiscreteValuationRing 𝒪[L] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set r := ‖(ϖ : K)‖
  have hr0 : 0 < r := norm_irreducible_pos hϖ
  have hr1 : r < 1 := norm_irreducible_lt_one hϖ
  -- The norm of every nonzero element of `L` is an integer power of `r`.
  have hpow {y : L} (hy : y ≠ 0) : ∃ n : ℤ, ‖y‖ = r ^ n := by
    simpa [hφ] using exists_norm_eq_zpow_of_irreducible hϖ ((map_ne_zero φ).2 hy)
  -- An element of norm less than `1` has norm `r ^ n` for a positive natural number `n`.
  have hpos {y : L} (hy0 : y ≠ 0) (hy1 : ‖y‖ < 1) : ∃ n : ℕ, 0 < n ∧ ‖y‖ = r ^ n := by
    obtain ⟨n, hn⟩ := hpow hy0
    have hn0 : 0 < n := by
      rw [hn] at hy1
      exact (zpow_lt_one_iff_right_of_lt_one₀ hr0 hr1).1 hy1
    exact ⟨n.toNat, by omega, by rw [hn, ← zpow_natCast, Int.toNat_of_nonneg hn0.le]⟩
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ y : L, ‖y‖ = r ^ n := by
    obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one L
    obtain ⟨n, hn, hy⟩ := hpos (norm_pos_iff.1 hy0) hy1
    exact ⟨n, hn, y, hy⟩
  classical
  obtain ⟨hN, ϖL, hϖL⟩ := Nat.find_spec hex
  have hϖL0 : ϖL ≠ 0 := by
    rw [← norm_pos_iff, hϖL]
    positivity
  have hϖL1 : ‖ϖL‖ < 1 := by rw [hϖL]; exact pow_lt_one₀ hr0.le hr1 hN.ne'
  -- `ϖL` has the largest norm among the elements of norm less than `1`.
  have hmax (y : L) (hy1 : ‖y‖ < 1) : ‖y‖ ≤ ‖ϖL‖ := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    obtain ⟨n, hn, hy⟩ := hpos hy0 hy1
    rw [hy, hϖL]
    exact pow_le_pow_of_le_one hr0.le hr1.le (Nat.find_min' hex ⟨hn, y, hy⟩)
  exact isDiscreteValuationRing_of_norm_eq_zpow (norm_pos_iff.2 hϖL0) hϖL1
    fun _ hx ↦ exists_norm_eq_zpow_of_forall_norm_lt_one hϖL0 hϖL1 hmax hx

end Discrete

section Residue

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- If every element `a` of norm at most `1` of a nonarchimedean field satisfies
`‖a ^ q - a‖ < 1`, then every element of the residue field `𝓀[K]` is a root of `X ^ q - X`. -/
theorem pow_eq_self_of_norm_pow_sub_lt_one {q : ℕ} (h : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ q - a‖ < 1)
    (x : 𝓀[K]) : x ^ q = x := by
  obtain ⟨a, rfl⟩ := residue_surjective x
  -- The valuation of the valued structure `NormedField.toValued` is `‖·‖₊` by definition.
  have hv (y : K) : Valued.v y = ‖y‖₊ := rfl
  have ha1 : ‖(a : K)‖ ≤ 1 := by
    have h1 := (Valuation.mem_integer_iff _ _).1 a.2
    rw [hv] at h1
    exact_mod_cast h1
  have ha : ‖(a : K) ^ q - a‖₊ ≠ 1 := ne_of_lt (by exact_mod_cast h a ha1)
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff, (Valuation.integer.integers _).isUnit_iff_valuation_eq_one, hv,
    Algebra.algebraMap_ofSubsemiring_apply]
  simpa using ha

/-- If, for some `q > 1`, every element `a` of norm at most `1` of a nonarchimedean field satisfies
`‖a ^ q - a‖ < 1`, the residue field `𝓀[K]` is finite. -/
theorem finite_residueField_of_norm_pow_sub_lt_one {q : ℕ} (hq : 1 < q)
    (h : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ q - a‖ < 1) : Finite 𝓀[K] :=
  Set.finite_univ_iff.1 <| (finite_setOfPred_isRoot (X_pow_sub_X_ne_zero hq)).subset fun x _ ↦ by
    simp [pow_eq_self_of_norm_pow_sub_lt_one h x]

/-- If, for some `q > 1`, every element `a` of norm at most `1` of a nonarchimedean field satisfies
`‖a ^ q - a‖ < 1`, the residue field `𝓀[K]` has at most `q` elements. -/
theorem natCard_residueField_le_of_norm_pow_sub_lt_one {q : ℕ} (hq : 1 < q)
    (h : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ q - a‖ < 1) : Nat.card 𝓀[K] ≤ q := by
  have := finite_residueField_of_norm_pow_sub_lt_one hq h
  have := Fintype.ofFinite 𝓀[K]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← natDegree_X_pow_sub_X (R := 𝓀[K]) hq]
  refine card_le_degree_of_subset_roots fun x _ ↦ ?_
  simp [X_pow_sub_X_ne_zero hq, pow_eq_self_of_norm_pow_sub_lt_one h x]

end Residue

section FiniteDimensional

variable (𝕜 : Type*) {K : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NontriviallyNormedField K] [IsUltrametricDist K] [Module 𝕜 K] [ContinuousSMul 𝕜 K]

/-- **Riesz's theorem** for nonarchimedean fields: a field whose valuation ring is a discrete
valuation ring with finite residue field is finite-dimensional over every complete nontrivially
normed field `𝕜` acting continuously on it; its valuation ring is a totally bounded neighbourhood
of `0`. For `𝕜 = ℚ_[p]` this recognises such a field as a finite extension of `ℚ_[p]`. -/
theorem finiteDimensional_of_finite_residueField [IsDiscreteValuationRing 𝒪[K]]
    [Finite 𝓀[K]] : FiniteDimensional 𝕜 K := by
  -- The valuation of `NormedField.toValued` is `NormedField.valuation`, which has rank one.
  have : (Valued.v : Valuation K NNReal).RankOne :=
    inferInstanceAs (NormedField.valuation (K := K)).RankOne
  have htb : TotallyBounded (𝒪[K] : Set K) := by
    simpa using (totallyBounded_iff_finite_residueField.2 ‹_›).image uniformContinuous_subtype_val
  have hball : (𝒪[K] : Set K) = Metric.closedBall 0 1 := by
    ext x
    simp [mem_iff]
  refine FiniteDimensional.of_totallyBounded_nhds 𝕜 (x := 0) ?_ htb
  rw [hball]
  exact Metric.closedBall_mem_nhds 0 one_pos

end FiniteDimensional

end Valued.integer
