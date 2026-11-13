/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.RingTheory.MvPowerSeries.InitialDiagram
import Mathlib.LinearAlgebra.Projection

/-!
# Hironaka's formal division theorem for multivariate power series

Given a monomial order `ord : MonomialOrder σ` and a finite linearly ordered family
`F : ι → MvPowerSeries σ R` of formal power series whose `ord`-initial exponents `α i` carry unit
coefficients, exponents in `σ →₀ ℕ` partition into the disjoint translated cones
`Δᵢ = {γ | α i ≤ γ ∧ ∀ j < i, ¬ α j ≤ γ}` and the complementary remainder region
`Δ = {γ | ∀ i, ¬ α i ≤ γ}`. Hironaka's formal division theorem states that every
`G : MvPowerSeries σ R` admits a unique decomposition `G = (∑ i, Q i * F i) + R'` with
`α i + β ∈ Δᵢ` for `β ∈ (Q i).support` and `β ∈ Δ` for `β ∈ R'.support`
(`MonomialOrder.existsUnique_formalDivision`).

Because `ord` is compatible with addition and cancellative, in `coeff γ ((∑ i, Q i * F i) + R')`
every contribution from non-initial exponents `δ ≠ α i` of `F i` involves quotient exponents `β`
with `α i + β ≺[ord] γ`. Existence (via `WellFounded.fix` on `ord.syn`) and uniqueness (via
`MonomialOrder.coeff_eq_zero_and_coeff_eq_zero_of_isLowerSet`) therefore hold over an arbitrary
ring `R` and variable type `σ`, specializing to `TauCeti.formalDivision` for `MonomialOrder.degLex`.

When `σ` is finite and the coefficients form a field `K`, choosing generators of
`I : Ideal (MvPowerSeries σ K)` at `ord.initialDiagramVertices I` yields:

* unique normal-form remainders (`MonomialOrder.existsUnique_sub_mem_and_mem_complementSubmodule`)
  and `IsCompl (I.restrictScalars K) (ord.complementSubmodule I)`
  (`MonomialOrder.isCompl_restrictScalars_complementSubmodule`);
* the `K`-linear projection `ord.normalRemainder I` (via `Submodule.projection`) and quotient
  equivalence `ord.quotientEquivComplementSubmodule I` (via `Submodule.quotientEquivOfIsCompl`);
* for each `v ∈ ord.initialDiagram I`, the normalized generator `ord.standardGenerator I v ∈ I`
  with initial exponent `v` and initial coefficient `1`, generating `I` over
  `ord.initialDiagramVertices I`
  (`MonomialOrder.span_image_standardGenerator_initialDiagramVertices`).

## Main definitions

* `MonomialOrder.complementSubmodule`: the `R`-submodule of series supported outside
  `ord.initialDiagram I`.
* `MonomialOrder.normalRemainder`: the canonical `K`-linear normal-remainder projection
  `MvPowerSeries σ K →ₗ[K] MvPowerSeries σ K` modulo `I` onto `ord.complementSubmodule I`.
* `MonomialOrder.quotientEquivComplementSubmodule`: the canonical `K`-linear isomorphism
  `(MvPowerSeries σ K ⧸ I) ≃ₗ[K] ord.complementSubmodule I`.
* `MonomialOrder.standardGenerator`: the unique normalized element of `I` congruent to
  `monomial v 1` modulo `ord.complementSubmodule I`.

## Main results

* `MonomialOrder.existsUnique_formalDivision`,
  `MonomialOrder.existsUnique_formalDivision_of_divisionRing`, `TauCeti.formalDivision`: Hironaka's
  formal division over a ring, a division ring, and `MvPowerSeries (Fin n) K` with `degLex`.
* `MonomialOrder.snd_eq_zero_iff_mem_of_eq_sum_mul_add`,
  `MonomialOrder.span_range_eq_of_forall_mem_initialDiagram_exists_le`: formal division by
  initial-diagram generators detects ideal membership and spans `I`.
* `MonomialOrder.isCompl_restrictScalars_complementSubmodule`,
  `MonomialOrder.snd_eq_normalRemainder_of_eq_sum_mul_add`: complement decomposition and agreement
  of formal-division remainders with `ord.normalRemainder I`.
* `MonomialOrder.eq_standardGenerator_iff`, `MonomialOrder.initialExp_standardGenerator`,
  `MonomialOrder.span_image_standardGenerator_initialDiagramVertices`: uniqueness, initial data,
  and ideal generation for Hironaka's normalized vertex generators.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Theorem 3.17, Remark 3.18 and Corollary 3.19, p. 238.
* Heisuke Hironaka, *Resolution of singularities of an algebraic variety over a field of
  characteristic zero. I*, Ann. of Math. (2) 79 (1964), 109–203.
-/

public section

open scoped MonomialOrder

namespace MonomialOrder

section Partition

variable {σ ι : Type*} (α : ι → (σ →₀ ℕ))

/-- `inCell α i γ` holds when `γ` lies in `α i + (σ →₀ ℕ)` and avoids every earlier cone
`α j + (σ →₀ ℕ)` (`j < i`). -/
private def inCell [LinearOrder ι] (i : ι) (γ : σ →₀ ℕ) : Prop :=
  α i ≤ γ ∧ ∀ j, j < i → ¬ α j ≤ γ

/-- `inRem α γ` holds when `γ` avoids all cones `α i + (σ →₀ ℕ)`. -/
private def inRem (γ : σ →₀ ℕ) : Prop := ∀ i, ¬ α i ≤ γ

private theorem inCell_unique [LinearOrder ι] {i₁ i₂ : ι} {γ : σ →₀ ℕ}
    (h₁ : inCell α i₁ γ) (h₂ : inCell α i₂ γ) : i₁ = i₂ := by
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hlt
  · exact absurd h₁.1 (h₂.2 i₁ hlt)
  · rfl
  · exact absurd h₂.1 (h₁.2 i₂ hlt)

private theorem not_inCell_of_inRem [LinearOrder ι] {i : ι} {γ : σ →₀ ℕ} (hr : inRem α γ) :
    ¬ inCell α i γ := fun hc ↦ hr i hc.1

private theorem exists_inCell_of_not_inRem [Finite ι] [LinearOrder ι] {γ : σ →₀ ℕ}
    (h : ¬ inRem α γ) : ∃ i, inCell α i γ := by
  classical
  cases nonempty_fintype ι
  simp only [inRem, not_forall, not_not] at h
  let s : Finset ι := Finset.univ.filter fun i ↦ α i ≤ γ
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, fun j hj hle ↦ ?_⟩
  exact hj.not_ge (s.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩))

private theorem inRem_iff_not_exists_inCell [Finite ι] [LinearOrder ι] {γ : σ →₀ ℕ} :
    inRem α γ ↔ ¬ ∃ i, inCell α i γ :=
  ⟨fun hr ⟨_, hi⟩ ↦ not_inCell_of_inRem α hr hi,
    fun h ↦ by_contra fun hr ↦ h (exists_inCell_of_not_inRem α hr)⟩

private theorem inCell_add_iff [LinearOrder ι] {i : ι} {β : σ →₀ ℕ} :
    inCell α i (α i + β) ↔ ∀ j, j < i → ¬ α j ≤ α i + β :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨le_self_add, h⟩⟩

end Partition

section GeneralDivision

variable {σ R : Type*} [Ring R] (ord : MonomialOrder σ)

open scoped Classical in
/-- Sum of all lower-order contributions `(p.2 ≠ α i)` to `coeff γ (∑ i, Q i * F i)`. -/
private noncomputable def lowerSum {ι : Type*} [Fintype ι] (F : ι → MvPowerSeries σ R)
    (α : ι → (σ →₀ ℕ)) (Q : ι → MvPowerSeries σ R) (γ : σ →₀ ℕ) : R :=
  ∑ i : ι, ∑ p ∈ (Finset.antidiagonal γ).filter (fun p ↦ p.2 ≠ α i),
    MvPowerSeries.coeff p.1 (Q i) * MvPowerSeries.coeff p.2 (F i)

open scoped Classical in
private theorem coeff_mul_eq_ite_inCell {ι : Type*} [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)} {Q : ι → MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (i : ι) (γ : σ →₀ ℕ) :
    MvPowerSeries.coeff γ (Q i * F i) =
      (if inCell α i γ then
        MvPowerSeries.coeff (γ - α i) (Q i) * MvPowerSeries.coeff (α i) (F i)
      else 0) +
      ∑ p ∈ (Finset.antidiagonal γ).filter (fun p ↦ p.2 ≠ α i),
        MvPowerSeries.coeff p.1 (Q i) * MvPowerSeries.coeff p.2 (F i) := by
  rw [MvPowerSeries.coeff_mul,
    ← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal γ) (fun p ↦ p.2 = α i)]
  congr 1
  rw [Finset.HasAntidiagonal.filter_snd_eq_antidiagonal γ (α i)]
  by_cases hcell : inCell α i γ
  · rw [ite_eq_left hcell, ite_eq_left hcell.1, Finset.sum_singleton]
  · rw [ite_eq_right hcell]
    split_ifs with hle
    · rw [Finset.sum_singleton]
      have hnot : ¬ inCell α i (α i + (γ - α i)) := by rwa [add_tsub_cancel_of_le hle]
      have hzero : MvPowerSeries.coeff (γ - α i) (Q i) = 0 := by
        by_contra hne
        exact hnot ((inCell_add_iff α).mpr (hQ i (γ - α i) (MvPowerSeries.mem_support.mpr hne)))
      rw [hzero, zero_mul]
    · exact Finset.sum_empty

private theorem coeff_sum_add_of_inCell {ι : Type*} [Fintype ι] [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    {Q : ι → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β)
    {i₀ : ι} {γ : σ →₀ ℕ} (hi₀ : inCell α i₀ γ) :
    MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) =
      MvPowerSeries.coeff (γ - α i₀) (Q i₀) * MvPowerSeries.coeff (α i₀) (F i₀) +
        lowerSum F α Q γ := by
  classical
  have hrem0 : MvPowerSeries.coeff γ rem = 0 := by
    by_contra hne
    exact hR γ (MvPowerSeries.mem_support.mpr hne) i₀ hi₀.1
  rw [map_add, hrem0, add_zero, map_sum]
  simp_rw [coeff_mul_eq_ite_inCell hQ, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i₀
    (fun i _ hne ↦ ite_eq_right fun hi ↦ hne (inCell_unique α hi hi₀))
    (fun hmem ↦ absurd (Finset.mem_univ i₀) hmem), ite_eq_left hi₀]

private theorem coeff_sum_add_of_inRem {ι : Type*} [Fintype ι] [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    {Q : ι → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    {γ : σ →₀ ℕ} (hr : inRem α γ) :
    MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) =
      MvPowerSeries.coeff γ rem + lowerSum F α Q γ := by
  classical
  rw [map_add, add_comm _ (MvPowerSeries.coeff γ rem), map_sum]
  simp_rw [coeff_mul_eq_ite_inCell hQ, Finset.sum_add_distrib]
  rw [Finset.sum_eq_zero fun i _ ↦ ite_eq_right (not_inCell_of_inRem α hr), zero_add]
  rfl

private theorem toSyn_add_lt_of_mem_antidiagonal {ι : Type*}
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    {i : ι} {γ : σ →₀ ℕ} {p : (σ →₀ ℕ) × (σ →₀ ℕ)} [DecidableEq σ]
    (hp : p ∈ Finset.antidiagonal γ) (hne : p.2 ≠ α i)
    (hc : MvPowerSeries.coeff p.2 (F i) ≠ 0) :
    ord.toSyn (α i + p.1) < ord.toSyn γ := by
  rw [Finset.mem_antidiagonal] at hp
  have hmem : p.2 ∈ (F i).support := MvPowerSeries.mem_support.mpr hc
  have hle : ord.toSyn (α i) ≤ ord.toSyn p.2 := (hα i).2 (Set.mem_image_of_mem _ hmem)
  have hlt : ord.toSyn (α i) < ord.toSyn p.2 :=
    hle.lt_of_ne (ord.toSyn.injective.ne hne.symm)
  calc
    ord.toSyn (α i + p.1) = ord.toSyn p.1 + ord.toSyn (α i) := by rw [map_add, add_comm]
    _ < ord.toSyn p.1 + ord.toSyn p.2 := (add_lt_add_iff_left _).mpr hlt
    _ = ord.toSyn γ := by rw [← map_add, hp]

/-- Lower-set vanishing for formal division: if `(Q, rem)` satisfies the formal-division support
conditions and `(∑ i, Q i * F i) + rem` has zero coefficients on `ord.toSyn ⁻¹' S` for a lower set
`S : Set ord.syn`, then every `Q i` vanishes at `β` whenever `ord.toSyn (α i + β) ∈ S` and `rem`
vanishes on `ord.toSyn ⁻¹' S`. -/
theorem coeff_eq_zero_and_coeff_eq_zero_of_isLowerSet {ι : Type*} [Fintype ι] [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    {Q : ι → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β)
    {S : Set ord.syn} (hS : IsLowerSet S)
    (hG : ∀ γ, ord.toSyn γ ∈ S → MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) = 0) :
    (∀ i β, ord.toSyn (α i + β) ∈ S → MvPowerSeries.coeff β (Q i) = 0) ∧
      (∀ γ, ord.toSyn γ ∈ S → MvPowerSeries.coeff γ rem = 0) := by
  classical
  let P : ord.syn → Prop := fun s ↦ s ∈ S →
    (∀ i β, ord.toSyn (α i + β) = s → MvPowerSeries.coeff β (Q i) = 0) ∧
      MvPowerSeries.coeff (ord.toSyn.symm s) rem = 0
  have key : ∀ s, P s := fun s ↦ WellFoundedLT.induction s fun s ih hs ↦ by
    set γ := ord.toSyn.symm s
    have hγs : ord.toSyn γ = s := ord.toSyn.apply_symm_apply s
    have hlow : lowerSum F α Q γ = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun p hp ↦ ?_
      rw [Finset.mem_filter] at hp
      by_cases hc : MvPowerSeries.coeff p.2 (F i) = 0
      · rw [hc, mul_zero]
      · have hlt : ord.toSyn (α i + p.1) < s :=
          hγs ▸ ord.toSyn_add_lt_of_mem_antidiagonal hα hp.1 hp.2 hc
        rw [(ih _ hlt (hS hlt.le hs)).1 i p.1 rfl, zero_mul]
    have hQ_zero : ∀ i β, ord.toSyn (α i + β) = s → MvPowerSeries.coeff β (Q i) = 0 := by
      intro i β hβs
      have hsum : α i + β = γ := ord.toSyn.injective (hβs.trans hγs.symm)
      by_cases hcell : inCell α i γ
      · have hβ : β = γ - α i := by rw [← hsum, add_tsub_cancel_left]
        have htot := coeff_sum_add_of_inCell (F := F) hQ hR hcell
        rw [hG γ (hγs ▸ hs), hlow, add_zero] at htot
        rw [hβ]
        exact (hu i).mul_left_eq_zero.mp htot.symm
      · by_contra hne
        exact hcell (hsum ▸ (inCell_add_iff α).mpr (hQ i β (MvPowerSeries.mem_support.mpr hne)))
    have hR_zero : MvPowerSeries.coeff γ rem = 0 := by
      by_cases hr : inRem α γ
      · have htot := coeff_sum_add_of_inRem (F := F) hQ (rem := rem) hr
        rw [hG γ (hγs ▸ hs), hlow, add_zero] at htot
        exact htot.symm
      · obtain ⟨i, hi⟩ := exists_inCell_of_not_inRem α hr
        by_contra hne
        exact hR γ (MvPowerSeries.mem_support.mpr hne) i hi.1
    exact ⟨hQ_zero, hR_zero⟩
  refine ⟨fun i β hβ ↦ (key _ hβ).1 i β rfl, fun γ hγ ↦ ?_⟩
  simpa only [AddEquiv.symm_apply_apply] using (key (ord.toSyn γ) hγ).2

/-- Strict initial-segment vanishing for formal division: if `(∑ i, Q i * F i) + rem` vanishes at
all exponents strictly `ord`-smaller than `t`, so do `rem` and the shifted quotients `Q i`. -/
theorem coeff_eq_zero_and_coeff_eq_zero_of_forall_lt {ι : Type*} [Fintype ι] [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    {Q : ι → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β) {t : ord.syn}
    (hG : ∀ γ, ord.toSyn γ < t → MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) = 0) :
    (∀ i β, ord.toSyn (α i + β) < t → MvPowerSeries.coeff β (Q i) = 0) ∧
      (∀ γ, ord.toSyn γ < t → MvPowerSeries.coeff γ rem = 0) :=
  ord.coeff_eq_zero_and_coeff_eq_zero_of_isLowerSet hα hu hQ hR (IsLowerSet.Iio t) hG

/-- Closed initial-segment vanishing for formal division: if `(∑ i, Q i * F i) + rem` vanishes at
all exponents `ord`-at-most `t`, so do `rem` and the shifted quotients `Q i`. -/
theorem coeff_eq_zero_and_coeff_eq_zero_of_forall_le {ι : Type*} [Fintype ι] [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    {Q : ι → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β) {t : ord.syn}
    (hG : ∀ γ, ord.toSyn γ ≤ t → MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) = 0) :
    (∀ i β, ord.toSyn (α i + β) ≤ t → MvPowerSeries.coeff β (Q i) = 0) ∧
      (∀ γ, ord.toSyn γ ≤ t → MvPowerSeries.coeff γ rem = 0) :=
  ord.coeff_eq_zero_and_coeff_eq_zero_of_isLowerSet hα hu hQ hR (IsLowerSet.Iic t) hG

private theorem formalDivision_unique {ι : Type*} [Fintype ι] [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    {G : MvPowerSeries σ R}
    {qr₁ qr₂ : (ι → MvPowerSeries σ R) × MvPowerSeries σ R}
    (h₁ : G = (∑ i, qr₁.1 i * F i) + qr₁.2 ∧
      (∀ i β, β ∈ (qr₁.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr₁.2.support, ∀ i, ¬ α i ≤ β))
    (h₂ : G = (∑ i, qr₂.1 i * F i) + qr₂.2 ∧
      (∀ i β, β ∈ (qr₂.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr₂.2.support, ∀ i, ¬ α i ≤ β)) :
    qr₁ = qr₂ := by
  have hQ : ∀ i β, β ∈ (qr₁.1 i - qr₂.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β := fun i β hβ ↦
    (MvPowerSeries.support_sub _ _ hβ).elim (h₁.2.1 i β) (h₂.2.1 i β)
  have hR : ∀ β ∈ (qr₁.2 - qr₂.2).support, ∀ i, ¬ α i ≤ β := fun β hβ ↦
    (MvPowerSeries.support_sub _ _ hβ).elim (h₁.2.2 β) (h₂.2.2 β)
  have hsum : (∑ i, (qr₁.1 i - qr₂.1 i) * F i) + (qr₁.2 - qr₂.2) = 0 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← add_sub_add_comm]
    exact sub_eq_zero.mpr (h₁.1.symm.trans h₂.1)
  obtain ⟨hQ0, hR0⟩ := ord.coeff_eq_zero_and_coeff_eq_zero_of_isLowerSet hα hu hQ hR isLowerSet_univ
    fun γ _ ↦ by rw [hsum, map_zero]
  refine Prod.ext (funext fun i ↦ MvPowerSeries.ext fun β ↦ ?_) (MvPowerSeries.ext fun γ ↦ ?_)
  · exact sub_eq_zero.mp (by simpa only [map_sub] using hQ0 i β trivial)
  · exact sub_eq_zero.mp (by simpa only [map_sub] using hR0 γ trivial)

open scoped Classical in
/-- Recursive step computing the unique normalized value at `s : ord.syn` from strictly smaller
values in `ord.syn`. -/
private noncomputable def divStep {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι → MvPowerSeries σ R) (α : ι → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R)
    (s : ord.syn) (rec : ∀ t, t < s → R) : R :=
  let γ := ord.toSyn.symm s
  let L : R := ∑ i : ι, ∑ p ∈ (Finset.antidiagonal γ).filter (fun p ↦ p.2 ≠ α i),
    if h : ord.toSyn (α i + p.1) < s ∧ inCell α i (α i + p.1) then
      rec (ord.toSyn (α i + p.1)) h.1 * MvPowerSeries.coeff p.2 (F i)
    else 0
  if hex : ∃ i, inCell α i γ then
    (MvPowerSeries.coeff γ G - L) * ↑(hu hex.choose).unit⁻¹
  else
    MvPowerSeries.coeff γ G - L

open scoped Classical in
private noncomputable def divVal {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι → MvPowerSeries σ R) (α : ι → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R) :
    ord.syn → R :=
  WellFounded.fix (wellFounded_lt (α := ord.syn)) (ord.divStep F α hu G)

open scoped Classical in
private noncomputable def divQuot {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι → MvPowerSeries σ R) (α : ι → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R) :
    ι → MvPowerSeries σ R :=
  fun i β ↦ if inCell α i (α i + β) then ord.divVal F α hu G (ord.toSyn (α i + β)) else 0

open scoped Classical in
private noncomputable def divRem {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι → MvPowerSeries σ R) (α : ι → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  fun γ ↦ if inRem α γ then ord.divVal F α hu G (ord.toSyn γ) else 0

open scoped Classical in
private theorem coeff_divQuot {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι → MvPowerSeries σ R) (α : ι → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R)
    (i : ι) (β : σ →₀ ℕ) :
    MvPowerSeries.coeff β (ord.divQuot F α hu G i) =
      if inCell α i (α i + β) then ord.divVal F α hu G (ord.toSyn (α i + β)) else 0 := by
  rw [MvPowerSeries.coeff_apply, divQuot]

open scoped Classical in
private theorem coeff_divRem {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι → MvPowerSeries σ R) (α : ι → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R)
    (γ : σ →₀ ℕ) :
    MvPowerSeries.coeff γ (ord.divRem F α hu G) =
      if inRem α γ then ord.divVal F α hu G (ord.toSyn γ) else 0 := by
  rw [MvPowerSeries.coeff_apply, divRem]

open scoped Classical in
private theorem divVal_eq {ι : Type*} [Fintype ι] [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    (G : MvPowerSeries σ R) (γ : σ →₀ ℕ) :
    ord.divVal F α hu G (ord.toSyn γ) =
      if hex : ∃ i, inCell α i γ then
        (MvPowerSeries.coeff γ G - lowerSum F α (ord.divQuot F α hu G) γ) *
          ↑(hu hex.choose).unit⁻¹
      else
        MvPowerSeries.coeff γ G - lowerSum F α (ord.divQuot F α hu G) γ := by
  have hL : (∑ i : ι,
      ∑ p ∈ (Finset.antidiagonal γ).filter (fun p ↦ p.2 ≠ α i),
        if _ : ord.toSyn (α i + p.1) < ord.toSyn γ ∧ inCell α i (α i + p.1) then
          ord.divVal F α hu G (ord.toSyn (α i + p.1)) * MvPowerSeries.coeff p.2 (F i)
        else 0) = lowerSum F α (ord.divQuot F α hu G) γ := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.mem_filter] at hp
    by_cases hc : MvPowerSeries.coeff p.2 (F i) = 0
    · simp [hc]
    · have hlt : ord.toSyn (α i + p.1) < ord.toSyn γ :=
        ord.toSyn_add_lt_of_mem_antidiagonal hα hp.1 hp.2 hc
      by_cases hcell : inCell α i (α i + p.1)
      · have hcond : ord.toSyn (α i + p.1) < ord.toSyn γ ∧ inCell α i (α i + p.1) := ⟨hlt, hcell⟩
        rw [dite_eq_left hcond, ord.coeff_divQuot, ite_eq_left hcell]
      · have hcond : ¬ (ord.toSyn (α i + p.1) < ord.toSyn γ ∧ inCell α i (α i + p.1)) :=
          fun h ↦ hcell h.2
        rw [dite_eq_right hcond, ord.coeff_divQuot, ite_eq_right hcell, zero_mul]
  have hfix : ord.divVal F α hu G (ord.toSyn γ) =
      ord.divStep F α hu G (ord.toSyn γ) (fun t _ ↦ ord.divVal F α hu G t) :=
    WellFounded.fix_eq _ _ (ord.toSyn γ)
  rw [hfix]
  dsimp only [divStep]
  simp only [AddEquiv.symm_apply_apply, hL]

private theorem divQuot_rem_spec {ι : Type*} [Fintype ι] [LinearOrder ι]
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    (G : MvPowerSeries σ R) :
    G = (∑ i, ord.divQuot F α hu G i * F i) + ord.divRem F α hu G ∧
      (∀ i β, β ∈ (ord.divQuot F α hu G i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ (ord.divRem F α hu G).support, ∀ i, ¬ α i ≤ β) := by
  classical
  set Q := ord.divQuot F α hu G
  set rem := ord.divRem F α hu G
  have hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β := by
    intro i β hβ
    rw [MvPowerSeries.mem_support, ord.coeff_divQuot] at hβ
    by_cases hcell : inCell α i (α i + β)
    · exact hcell.2
    · exact absurd (ite_eq_right hcell) hβ
  have hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β := by
    intro γ hγ
    rw [MvPowerSeries.mem_support, ord.coeff_divRem] at hγ
    by_cases hr : inRem α γ
    · exact hr
    · exact absurd (ite_eq_right hr) hγ
  refine ⟨MvPowerSeries.ext fun γ ↦ ?_, hQ, hR⟩
  by_cases hex : ∃ i, inCell α i γ
  · have hi₀ : inCell α hex.choose γ := hex.choose_spec
    rw [coeff_sum_add_of_inCell hQ hR hi₀]
    have hQcoeff : MvPowerSeries.coeff (γ - α hex.choose) (Q hex.choose) =
        ord.divVal F α hu G (ord.toSyn γ) := by
      have hadd : α hex.choose + (γ - α hex.choose) = γ := add_tsub_cancel_of_le hi₀.1
      rw [ord.coeff_divQuot, hadd, ite_eq_left hi₀]
    rw [hQcoeff, ord.divVal_eq hα hu G γ, dite_eq_left hex]
    have hunit : (↑(hu hex.choose).unit⁻¹ : R) *
        MvPowerSeries.coeff (α hex.choose) (F hex.choose) = 1 := by
      simpa only [IsUnit.unit_spec] using Units.inv_mul (hu hex.choose).unit
    rw [mul_assoc, hunit, mul_one, sub_add_cancel]
  · have hr : inRem α γ := (inRem_iff_not_exists_inCell α).mpr hex
    rw [coeff_sum_add_of_inRem hQ (rem := rem) hr, ord.coeff_divRem, ite_eq_left hr,
      ord.divVal_eq hα hu G γ, dite_eq_right hex, sub_add_cancel]

/-- **Hironaka's formal division theorem** for an arbitrary monomial order `ord` over a ring `R`:
if each `F i` has `ord`-initial exponent `α i` with a unit coefficient, then every formal power
series `G` admits a unique decomposition `G = (∑ i, Q i * F i) + R'` whose quotient supports
satisfy `α i + supp(Q i) ⊆ Δᵢ` and whose remainder support avoids every cone `α i + (σ →₀ ℕ)`. -/
theorem existsUnique_formalDivision {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι → MvPowerSeries σ R) (α : ι → (σ →₀ ℕ))
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    (G : MvPowerSeries σ R) :
    ∃! qr : (ι → MvPowerSeries σ R) × MvPowerSeries σ R,
      G = (∑ i, qr.1 i * F i) + qr.2 ∧
      (∀ i β, β ∈ (qr.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) :=
  ⟨(ord.divQuot F α hu G, ord.divRem F α hu G), ord.divQuot_rem_spec hα hu G,
    fun _ h ↦ ord.formalDivision_unique hα hu h (ord.divQuot_rem_spec hα hu G)⟩

/-- Over a division ring `K`, every `ord`-initial coefficient is automatically a unit, so formal
division requires only that `α i` is the `ord`-initial exponent of `F i`. -/
theorem existsUnique_formalDivision_of_divisionRing {K ι : Type*} [DivisionRing K]
    [Fintype ι] [LinearOrder ι]
    (F : ι → MvPowerSeries σ K) (α : ι → (σ →₀ ℕ))
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (G : MvPowerSeries σ K) :
    ∃! qr : (ι → MvPowerSeries σ K) × MvPowerSeries σ K,
      G = (∑ i, qr.1 i * F i) + qr.2 ∧
      (∀ i β, β ∈ (qr.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) := by
  refine ord.existsUnique_formalDivision F α hα (fun i ↦ ?_) G
  obtain ⟨hf0, hexp⟩ := ord.isLeast_toSyn_support_iff_ne_zero_and_initialExp_eq.mp (hα i)
  exact hexp ▸ (ord.coeff_initialExp_ne_zero hf0).isUnit

end GeneralDivision

section StandardGenerators

variable {σ : Type*} (ord : MonomialOrder σ)

/-- The `R`-submodule of `MvPowerSeries σ R` consisting of power series whose support is disjoint
from `ord.initialDiagram I`. -/
def complementSubmodule {R : Type*} [Semiring R] (I : Ideal (MvPowerSeries σ R)) :
    Submodule R (MvPowerSeries σ R) where
  carrier := {f | ∀ β ∈ f.support, β ∉ ord.initialDiagram I}
  zero_mem' β hβ := by simp at hβ
  add_mem' {f g} hf hg β hβ := (MvPowerSeries.support_add f g hβ).elim (hf β) (hg β)
  smul_mem' c {f} hf β hβ := hf β (MvPowerSeries.support_smul_subset c f hβ)

theorem mem_complementSubmodule_iff {R : Type*} [Semiring R]
    {I : Ideal (MvPowerSeries σ R)} {f : MvPowerSeries σ R} :
    f ∈ ord.complementSubmodule I ↔ ∀ β ∈ f.support, β ∉ ord.initialDiagram I := (Iff.rfl)

@[simp]
theorem monomial_mem_complementSubmodule_iff {R : Type*} [Semiring R]
    {I : Ideal (MvPowerSeries σ R)} {α : σ →₀ ℕ} {c : R} :
    MvPowerSeries.monomial α c ∈ ord.complementSubmodule I ↔
      c = 0 ∨ α ∉ ord.initialDiagram I := by
  rw [mem_complementSubmodule_iff]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · simp only [hc, false_or]
    refine ⟨fun h ↦ h α ?_, fun hα β hβ ↦ ?_⟩
    · rw [MvPowerSeries.mem_support, MvPowerSeries.coeff_monomial_same]
      exact hc
    · rw [MvPowerSeries.mem_support] at hβ
      rwa [MvPowerSeries.eq_of_coeff_monomial_ne_zero hβ]

@[simp]
theorem complementSubmodule_bot {R : Type*} [Semiring R] :
    ord.complementSubmodule (⊥ : Ideal (MvPowerSeries σ R)) = ⊤ := by
  ext f
  simp [mem_complementSubmodule_iff]

@[simp]
theorem complementSubmodule_top {R : Type*} [Semiring R] :
    ord.complementSubmodule (⊤ : Ideal (MvPowerSeries σ R)) = ⊥ := by
  ext f
  rw [mem_complementSubmodule_iff, Submodule.mem_bot]
  exact ⟨ord.eq_zero_of_mem_of_forall_mem_support_notMem_initialDiagram trivial,
    fun h ↦ by simp [h]⟩

/-- Any left ideal `I` of `MvPowerSeries σ R` (restricted to `R`-scalars) is disjoint from
`ord.complementSubmodule I`. -/
theorem disjoint_restrictScalars_complementSubmodule {R : Type*} [Semiring R]
    (I : Ideal (MvPowerSeries σ R)) :
    Disjoint (I.restrictScalars R) (ord.complementSubmodule I) := by
  rw [Submodule.disjoint_def]
  intro f hfI hfc
  exact ord.eq_zero_of_mem_of_forall_mem_support_notMem_initialDiagram
    ((Submodule.restrictScalars_mem R I f).mp hfI)
    (ord.mem_complementSubmodule_iff.mp hfc)

private theorem sub_mem_and_mem_complementSubmodule {R ι : Type*} [Ring R] [Fintype ι]
    {I : Ideal (MvPowerSeries σ R)}
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hFI : ∀ i, F i ∈ I)
    (hD : ∀ γ ∈ ord.initialDiagram I, ∃ i, α i ≤ γ)
    {G : MvPowerSeries σ R}
    {qr : (ι → MvPowerSeries σ R) × MvPowerSeries σ R}
    (hdiv : G = (∑ i, qr.1 i * F i) + qr.2)
    (hrem : ∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) :
    G - qr.2 ∈ I ∧ qr.2 ∈ ord.complementSubmodule I := by
  refine ⟨?_, ord.mem_complementSubmodule_iff.mpr fun β hβ hβD ↦ ?_⟩
  · rw [sub_eq_of_eq_add hdiv]
    exact sum_mem fun i _ ↦ I.mul_mem_left (qr.1 i) (hFI i)
  · obtain ⟨i, hi⟩ := hD β hβD
    exact hrem β hβ i hi

/-- If `F i ∈ I` have exponents `α i` whose cones cover `ord.initialDiagram I`, then in any
decomposition `G = (∑ i, Q i * F i) + R'` whose remainder avoids every cone `α i + (σ →₀ ℕ)`, the
remainder `R'` vanishes if and only if `G ∈ I`. -/
theorem snd_eq_zero_iff_mem_of_eq_sum_mul_add {R ι : Type*} [Ring R] [Fintype ι]
    {I : Ideal (MvPowerSeries σ R)}
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hFI : ∀ i, F i ∈ I)
    (hD : ∀ γ ∈ ord.initialDiagram I, ∃ i, α i ≤ γ)
    {G : MvPowerSeries σ R}
    {qr : (ι → MvPowerSeries σ R) × MvPowerSeries σ R}
    (hdiv : G = (∑ i, qr.1 i * F i) + qr.2)
    (hrem : ∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) :
    qr.2 = 0 ↔ G ∈ I := by
  obtain ⟨hsubI, hcomp⟩ := ord.sub_mem_and_mem_complementSubmodule hFI hD hdiv hrem
  refine ⟨fun h0 ↦ by simpa [h0] using hsubI, fun hGI ↦ ?_⟩
  have hremI : qr.2 ∈ I := by
    simpa only [sub_sub_cancel] using I.sub_mem hGI hsubI
  exact ord.eq_zero_of_mem_of_forall_mem_support_notMem_initialDiagram hremI
    (ord.mem_complementSubmodule_iff.mp hcomp)

/-- Over a ring `R`, any finite family `F i ∈ I` with unit initial coefficients whose `ord`-initial
exponents `α i` generate `ord.initialDiagram I` as an upper set generates `I` as a left ideal of
`MvPowerSeries σ R`. -/
theorem span_range_eq_of_forall_mem_initialDiagram_exists_le
    {R ι : Type*} [Ring R] [Finite ι]
    {I : Ideal (MvPowerSeries σ R)}
    {F : ι → MvPowerSeries σ R} {α : ι → (σ →₀ ℕ)}
    (hFI : ∀ i, F i ∈ I)
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    (hD : ∀ γ ∈ ord.initialDiagram I, ∃ i, α i ≤ γ) :
    Ideal.span (Set.range F) = I := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine le_antisymm (Ideal.span_le.mpr (Set.range_subset_iff.mpr hFI)) fun G hGI ↦ ?_
  obtain ⟨qr, ⟨hdiv, _, hrem⟩, _⟩ := ord.existsUnique_formalDivision
    (F ∘ e.symm) (α ∘ e.symm) (fun j ↦ hα (e.symm j)) (fun j ↦ hu (e.symm j)) G
  have hD' : ∀ γ ∈ ord.initialDiagram I, ∃ j : Fin m, α (e.symm j) ≤ γ := fun γ hγ ↦ by
    obtain ⟨i, hi⟩ := hD γ hγ
    exact ⟨e i, by simpa using hi⟩
  have hr0 : qr.2 = 0 :=
    (ord.snd_eq_zero_iff_mem_of_eq_sum_mul_add (fun j ↦ hFI (e.symm j)) hD' hdiv hrem).mpr hGI
  rw [hdiv, hr0, add_zero]
  exact sum_mem fun j _ ↦ Ideal.mul_mem_left _ (qr.1 j) (Ideal.subset_span ⟨e.symm j, rfl⟩)

/-- Over a division ring `K`, any finite family `F i ∈ I` whose `ord`-initial exponents `α i`
generate `ord.initialDiagram I` as an upper set generates `I` as a left ideal of
`MvPowerSeries σ K`. -/
theorem span_range_eq_of_forall_mem_initialDiagram_exists_le_of_divisionRing
    {K ι : Type*} [DivisionRing K] [Finite ι]
    {I : Ideal (MvPowerSeries σ K)}
    {F : ι → MvPowerSeries σ K} {α : ι → (σ →₀ ℕ)}
    (hFI : ∀ i, F i ∈ I)
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hD : ∀ γ ∈ ord.initialDiagram I, ∃ i, α i ≤ γ) :
    Ideal.span (Set.range F) = I := by
  refine ord.span_range_eq_of_forall_mem_initialDiagram_exists_le hFI hα (fun i ↦ ?_) hD
  obtain ⟨hf0, hexp⟩ :=
    ord.isLeast_toSyn_support_iff_ne_zero_and_initialExp_eq.mp (hα i)
  rw [← hexp]
  exact (ord.coeff_initialExp_ne_zero hf0).isUnit

section Field

variable {K : Type*} [Field K] [Finite σ]

/-- Choose a finite family of elements in `I` realizing the minimal vertices of
`ord.initialDiagram I` as initial exponents. -/
private theorem exists_vertex_family (I : Ideal (MvPowerSeries σ K)) :
    ∃ (m : ℕ) (F : Fin m → MvPowerSeries σ K) (α : Fin m → (σ →₀ ℕ)),
      (∀ i, F i ∈ I) ∧
      (∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i))) ∧
      (∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) ∧
      (∀ γ ∈ ord.initialDiagram I, ∃ i, α i ≤ γ) := by
  let V := ord.initialDiagramVertices I
  let e : Fin V.card ≃ {v // v ∈ V} := (Finset.equivFin V).symm
  have hmem : ∀ i : Fin V.card, ∃ f ∈ I, f ≠ 0 ∧ ord.initialExp f = (e i : σ →₀ ℕ) :=
    fun i ↦ ord.mem_initialDiagram_iff.mp (ord.initialDiagramVertices_subset I (e i).2)
  choose F hFI hF0 hFexp using hmem
  refine ⟨V.card, F, fun i ↦ (e i : σ →₀ ℕ), hFI,
    fun i ↦ ord.isLeast_toSyn_support_iff_ne_zero_and_initialExp_eq.mpr ⟨hF0 i, hFexp i⟩,
    fun i ↦ ?_, fun γ hγ ↦ ?_⟩
  · dsimp only
    rw [← hFexp i]
    exact (ord.coeff_initialExp_ne_zero (hF0 i)).isUnit
  · obtain ⟨v, hvV, hle⟩ :=
      (ord.mem_initialDiagram_iff_exists_mem_initialDiagramVertices_le).mp hγ
    exact ⟨e.symm ⟨v, hvV⟩, by simpa using hle⟩

/-- Every power series `G : MvPowerSeries σ K` is congruent modulo `I` to a unique series `R'`
in `ord.complementSubmodule I`. -/
theorem existsUnique_sub_mem_and_mem_complementSubmodule
    (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    ∃! R' : MvPowerSeries σ K, G - R' ∈ I ∧ R' ∈ ord.complementSubmodule I := by
  obtain ⟨m, F, α, hFI, hα, hu, hD⟩ := ord.exists_vertex_family I
  obtain ⟨qr, ⟨hdiv, _, hrem⟩, _⟩ := ord.existsUnique_formalDivision F α hα hu G
  obtain ⟨hqr_mem, hqr_comp⟩ := ord.sub_mem_and_mem_complementSubmodule hFI hD hdiv hrem
  refine ⟨qr.2, ⟨hqr_mem, hqr_comp⟩, fun R₁ ⟨hR₁I, hR₁comp⟩ ↦ ?_⟩
  have hdiffI : R₁ - qr.2 ∈ I := by
    have hsub : R₁ - qr.2 = (G - qr.2) - (G - R₁) := by abel
    exact hsub ▸ I.sub_mem hqr_mem hR₁I
  exact sub_eq_zero.mp (ord.eq_zero_of_mem_of_forall_mem_support_notMem_initialDiagram hdiffI
    (ord.mem_complementSubmodule_iff.mp ((ord.complementSubmodule I).sub_mem hR₁comp hqr_comp)))

/-- `I` (restricted to `K`-scalars) and `ord.complementSubmodule I` are complementary
`K`-submodules of `MvPowerSeries σ K`. -/
theorem isCompl_restrictScalars_complementSubmodule (I : Ideal (MvPowerSeries σ K)) :
    IsCompl (I.restrictScalars K) (ord.complementSubmodule I) := by
  refine ⟨ord.disjoint_restrictScalars_complementSubmodule I, codisjoint_iff_le_sup.mpr ?_⟩
  intro G _
  obtain ⟨R', ⟨hGR, hRcomp⟩, _⟩ :=
    ord.existsUnique_sub_mem_and_mem_complementSubmodule I G
  have hsum : (G - R') + R' = G := sub_add_cancel G R'
  exact hsum ▸ Submodule.add_mem_sup ((Submodule.restrictScalars_mem K I (G - R')).mpr hGR) hRcomp

/-- The canonical `K`-linear normal-form remainder map modulo `I`, given by the linear projection
onto `ord.complementSubmodule I` along `I` (`Submodule.projection`). -/
noncomputable def normalRemainder (I : Ideal (MvPowerSeries σ K)) :
    MvPowerSeries σ K →ₗ[K] MvPowerSeries σ K :=
  (ord.complementSubmodule I).projection (I.restrictScalars K)
    (ord.isCompl_restrictScalars_complementSubmodule I).symm

@[simp]
theorem sub_normalRemainder_mem (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    G - ord.normalRemainder I G ∈ I :=
  (Submodule.restrictScalars_mem K I _).mp (Submodule.sub_projection_mem _ G)

@[simp]
theorem normalRemainder_mem_complementSubmodule
    (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    ord.normalRemainder I G ∈ ord.complementSubmodule I :=
  Submodule.projection_apply_mem _ G

theorem notMem_initialDiagram_of_mem_support_normalRemainder
    (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K)
    {β : σ →₀ ℕ} (hβ : β ∈ (ord.normalRemainder I G).support) :
    β ∉ ord.initialDiagram I :=
  ord.mem_complementSubmodule_iff.mp (ord.normalRemainder_mem_complementSubmodule I G) β hβ

theorem eq_normalRemainder_iff {I : Ideal (MvPowerSeries σ K)}
    {G R' : MvPowerSeries σ K} :
    R' = ord.normalRemainder I G ↔
      G - R' ∈ I ∧ R' ∈ ord.complementSubmodule I :=
  ⟨fun h ↦ h ▸ ⟨ord.sub_normalRemainder_mem I G,
    ord.normalRemainder_mem_complementSubmodule I G⟩,
    fun h ↦ (ord.existsUnique_sub_mem_and_mem_complementSubmodule I G).unique h
      ⟨ord.sub_normalRemainder_mem I G, ord.normalRemainder_mem_complementSubmodule I G⟩⟩

/-- In any decomposition `G = (∑ i, qr.1 i * F i) + qr.2` by elements `F i ∈ I` whose exponents
`α i` generate `ord.initialDiagram I` as an upper set, if `qr.2` avoids every cone
`Set.Ici (α i)`, then `qr.2` equals `ord.normalRemainder I G`. -/
theorem snd_eq_normalRemainder_of_eq_sum_mul_add {ι : Type*} [Fintype ι]
    {I : Ideal (MvPowerSeries σ K)}
    {F : ι → MvPowerSeries σ K} {α : ι → (σ →₀ ℕ)}
    (hFI : ∀ i, F i ∈ I)
    (hD : ∀ γ ∈ ord.initialDiagram I, ∃ i, α i ≤ γ)
    {G : MvPowerSeries σ K}
    {qr : (ι → MvPowerSeries σ K) × MvPowerSeries σ K}
    (hdiv : G = (∑ i, qr.1 i * F i) + qr.2)
    (hrem : ∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) :
    qr.2 = ord.normalRemainder I G :=
  ord.eq_normalRemainder_iff.mpr (ord.sub_mem_and_mem_complementSubmodule hFI hD hdiv hrem)

@[simp]
theorem normalRemainder_eq_zero_iff {I : Ideal (MvPowerSeries σ K)} {G : MvPowerSeries σ K} :
    ord.normalRemainder I G = 0 ↔ G ∈ I :=
  (Submodule.projection_apply_eq_zero_iff _).trans (Submodule.restrictScalars_mem K I G)

@[simp]
theorem normalRemainder_eq_self_of_mem_complementSubmodule
    {I : Ideal (MvPowerSeries σ K)} {G : MvPowerSeries σ K}
    (hG : G ∈ ord.complementSubmodule I) :
    ord.normalRemainder I G = G :=
  Submodule.projection_apply_of_mem_left _ hG

theorem normalRemainder_idem (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    ord.normalRemainder I (ord.normalRemainder I G) = ord.normalRemainder I G :=
  ord.normalRemainder_eq_self_of_mem_complementSubmodule
    (ord.normalRemainder_mem_complementSubmodule I G)

theorem normalRemainder_eq_iff_sub_mem {I : Ideal (MvPowerSeries σ K)}
    {f g : MvPowerSeries σ K} :
    ord.normalRemainder I f = ord.normalRemainder I g ↔ f - g ∈ I := by
  rw [← sub_eq_zero, ← map_sub, ord.normalRemainder_eq_zero_iff]

@[simp]
theorem ker_normalRemainder (I : Ideal (MvPowerSeries σ K)) :
    LinearMap.ker (ord.normalRemainder I) = I.restrictScalars K :=
  Submodule.ker_projection _

@[simp]
theorem range_normalRemainder (I : Ideal (MvPowerSeries σ K)) :
    LinearMap.range (ord.normalRemainder I) = ord.complementSubmodule I :=
  Submodule.range_projection _

@[simp]
theorem normalRemainder_bot :
    ord.normalRemainder (⊥ : Ideal (MvPowerSeries σ K)) = LinearMap.id :=
  LinearMap.ext fun _ ↦ ord.normalRemainder_eq_self_of_mem_complementSubmodule <| by
    rw [complementSubmodule_bot]
    trivial

@[simp]
theorem normalRemainder_top :
    ord.normalRemainder (⊤ : Ideal (MvPowerSeries σ K)) = 0 :=
  LinearMap.ext fun _ ↦ ord.normalRemainder_eq_zero_iff.mpr trivial

@[simp]
theorem mk_normalRemainder (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    Ideal.Quotient.mk I (ord.normalRemainder I G) = Ideal.Quotient.mk I G := by
  symm
  rw [Ideal.Quotient.eq]
  exact ord.sub_normalRemainder_mem I G

/-- The canonical `K`-linear isomorphism between `MvPowerSeries σ K ⧸ I` and the complementary
monomial-support subspace `ord.complementSubmodule I` (`Submodule.quotientEquivOfIsCompl`). -/
noncomputable def quotientEquivComplementSubmodule (I : Ideal (MvPowerSeries σ K)) :
    (MvPowerSeries σ K ⧸ I) ≃ₗ[K] ord.complementSubmodule I :=
  (Submodule.Quotient.restrictScalarsEquiv K I).symm.trans
    ((I.restrictScalars K).quotientEquivOfIsCompl (ord.complementSubmodule I)
      (ord.isCompl_restrictScalars_complementSubmodule I))

@[simp]
theorem coe_quotientEquivComplementSubmodule_mk (I : Ideal (MvPowerSeries σ K))
    (G : MvPowerSeries σ K) :
    (ord.quotientEquivComplementSubmodule I (Ideal.Quotient.mk I G) : MvPowerSeries σ K) =
      ord.normalRemainder I G := by
  simp [quotientEquivComplementSubmodule, normalRemainder, ← Ideal.Quotient.mk_eq_mk]

@[simp]
theorem quotientEquivComplementSubmodule_symm_apply (I : Ideal (MvPowerSeries σ K))
    (f : ord.complementSubmodule I) :
    (ord.quotientEquivComplementSubmodule I).symm f =
      Ideal.Quotient.mk I (f : MvPowerSeries σ K) := by
  simp [quotientEquivComplementSubmodule, ← Ideal.Quotient.mk_eq_mk]

/-- Hironaka's normalized generator of `I` at an exponent `v : σ →₀ ℕ`:
`monomial v 1 - ord.normalRemainder I (monomial v 1)`. For `v ∈ ord.initialDiagram I`, this is the
unique element of `I` whose difference from `monomial v 1` is supported outside
`ord.initialDiagram I` (Bierstone–Milman 1997, Corollary 3.19); for `v ∉ ord.initialDiagram I` it
is `0`. -/
noncomputable def standardGenerator (I : Ideal (MvPowerSeries σ K)) (v : σ →₀ ℕ) :
    MvPowerSeries σ K :=
  MvPowerSeries.monomial v 1 - ord.normalRemainder I (MvPowerSeries.monomial v 1)

theorem standardGenerator_def (I : Ideal (MvPowerSeries σ K)) (v : σ →₀ ℕ) :
    ord.standardGenerator I v =
      MvPowerSeries.monomial v 1 - ord.normalRemainder I (MvPowerSeries.monomial v 1) := (rfl)

@[simp]
theorem standardGenerator_mem (I : Ideal (MvPowerSeries σ K)) (v : σ →₀ ℕ) :
    ord.standardGenerator I v ∈ I :=
  ord.sub_normalRemainder_mem I (MvPowerSeries.monomial v 1)

@[simp]
theorem standardGenerator_sub_monomial_mem_complementSubmodule
    (I : Ideal (MvPowerSeries σ K)) (v : σ →₀ ℕ) :
    ord.standardGenerator I v - MvPowerSeries.monomial v 1 ∈ ord.complementSubmodule I := by
  rw [standardGenerator_def, sub_sub_cancel_left]
  exact (ord.complementSubmodule I).neg_mem (ord.normalRemainder_mem_complementSubmodule I _)

theorem notMem_initialDiagram_of_mem_support_standardGenerator_sub_monomial
    (I : Ideal (MvPowerSeries σ K)) (v : σ →₀ ℕ)
    {β : σ →₀ ℕ} (hβ : β ∈ (ord.standardGenerator I v - MvPowerSeries.monomial v 1).support) :
    β ∉ ord.initialDiagram I :=
  ord.mem_complementSubmodule_iff.mp
    (ord.standardGenerator_sub_monomial_mem_complementSubmodule I v) β hβ

theorem standardGenerator_eq_zero_of_notMem {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∉ ord.initialDiagram I) :
    ord.standardGenerator I v = 0 := by
  simp [standardGenerator_def, hv]

/-- Uniqueness characterization of `ord.standardGenerator I v`: `f` equals
`ord.standardGenerator I v` if and only if `f ∈ I` and `f - monomial v 1` is supported outside
`ord.initialDiagram I`. -/
theorem eq_standardGenerator_iff {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    {f : MvPowerSeries σ K} :
    f = ord.standardGenerator I v ↔
      f ∈ I ∧ ∀ β ∈ (f - MvPowerSeries.monomial v 1).support, β ∉ ord.initialDiagram I := by
  refine ⟨?_, fun ⟨hfI, hsupp⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨ord.standardGenerator_mem I v,
      fun _ hβ ↦ ord.notMem_initialDiagram_of_mem_support_standardGenerator_sub_monomial I v hβ⟩
  · have hrem : MvPowerSeries.monomial v 1 - f =
        ord.normalRemainder I (MvPowerSeries.monomial v 1) := by
      refine ord.eq_normalRemainder_iff.mpr ⟨by simpa only [sub_sub_cancel] using hfI, ?_⟩
      rw [← neg_sub]
      exact (ord.complementSubmodule I).neg_mem (ord.mem_complementSubmodule_iff.mpr hsupp)
    calc
      f = MvPowerSeries.monomial v 1 - (MvPowerSeries.monomial v 1 - f) :=
        (sub_sub_cancel _ _).symm
      _ = ord.standardGenerator I v := by rw [hrem, standardGenerator_def]

/-- If `G` has zero coefficients on `ord.toSyn ⁻¹' S` for a lower set `S : Set ord.syn`, then so
does `ord.normalRemainder I G`. -/
theorem coeff_normalRemainder_eq_zero_of_isLowerSet {I : Ideal (MvPowerSeries σ K)}
    {G : MvPowerSeries σ K} {S : Set ord.syn} (hS : IsLowerSet S)
    (hG : ∀ γ, ord.toSyn γ ∈ S → MvPowerSeries.coeff γ G = 0) :
    ∀ γ, ord.toSyn γ ∈ S → MvPowerSeries.coeff γ (ord.normalRemainder I G) = 0 := by
  obtain ⟨m, F, α, hFI, hα, hu, hD⟩ := ord.exists_vertex_family I
  obtain ⟨qr, ⟨hdiv, hQ, hR⟩, _⟩ := ord.existsUnique_formalDivision F α hα hu G
  rw [← ord.snd_eq_normalRemainder_of_eq_sum_mul_add hFI hD hdiv hR]
  exact (ord.coeff_eq_zero_and_coeff_eq_zero_of_isLowerSet hα hu hQ hR hS
    fun γ hγ ↦ hdiv ▸ hG γ hγ).2

/-- For `v ∈ ord.initialDiagram I`, `ord.standardGenerator I v` has `ord`-initial exponent `v`. -/
@[simp]
theorem initialExp_standardGenerator {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    ord.initialExp (ord.standardGenerator I v) = v := by
  obtain ⟨g, hgI, hg0, hgexp⟩ := ord.mem_initialDiagram_iff.mp hv
  let g' : MvPowerSeries σ K := (ord.initialCoeff g)⁻¹ • g
  have hg'I : g' ∈ I := (I.restrictScalars K).smul_mem _ hgI
  have hg'v : MvPowerSeries.coeff v g' = 1 := by
    rw [MvPowerSeries.coeff_smul, ← hgexp, ← initialCoeff_def,
      inv_mul_cancel₀ (ord.initialCoeff_ne_zero_iff.mpr hg0)]
  have hg'lt : ∀ γ, γ ≺[ord] v → MvPowerSeries.coeff γ g' = 0 := by
    intro γ hγ
    rw [MvPowerSeries.coeff_smul, ord.coeff_eq_zero_of_lt_initialExp (hgexp.symm ▸ hγ), mul_zero]
  let h : MvPowerSeries σ K := g' - MvPowerSeries.monomial v 1
  have hhle : ∀ γ, γ ≼[ord] v → MvPowerSeries.coeff γ h = 0 := by
    intro γ hγ
    rcases hγ.eq_or_lt with heq | hlt
    · rw [ord.toSyn.injective heq, map_sub, hg'v, MvPowerSeries.coeff_monomial_same, sub_self]
    · rw [map_sub, hg'lt γ hlt,
        MvPowerSeries.coeff_monomial_ne (fun heq ↦ hlt.ne (congrArg ord.toSyn heq)), sub_zero]
  have hrem_eq : ord.normalRemainder I h =
      -ord.normalRemainder I (MvPowerSeries.monomial v 1) := by
    simp only [h, map_sub, ord.normalRemainder_eq_zero_iff.mpr hg'I, zero_sub]
  have hgen_eq : ord.standardGenerator I v =
      MvPowerSeries.monomial v 1 + ord.normalRemainder I h := by
    rw [hrem_eq, standardGenerator_def, sub_eq_add_neg]
  have hRle : ∀ γ, γ ≼[ord] v → MvPowerSeries.coeff γ (ord.normalRemainder I h) = 0 :=
    ord.coeff_normalRemainder_eq_zero_of_isLowerSet (IsLowerSet.Iic (ord.toSyn v)) hhle
  rw [hgen_eq]
  refine ord.initialExp_eq_of_coeff_ne_zero_of_forall_lt ?_ fun γ hγ ↦ ?_
  · rw [map_add, MvPowerSeries.coeff_monomial_same, hRle v le_rfl, add_zero]
    exact one_ne_zero
  · rw [map_add, MvPowerSeries.coeff_monomial_ne (fun heq ↦ hγ.ne (congrArg ord.toSyn heq)),
      hRle γ hγ.le, add_zero]

@[simp]
theorem coeff_self_standardGenerator {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    MvPowerSeries.coeff v (ord.standardGenerator I v) = 1 := by
  have hnot : v ∉ (ord.standardGenerator I v - MvPowerSeries.monomial v 1).support :=
    fun h ↦ ord.notMem_initialDiagram_of_mem_support_standardGenerator_sub_monomial I v h hv
  have hc : MvPowerSeries.coeff v (ord.standardGenerator I v - MvPowerSeries.monomial v 1) = 0 :=
    not_not.mp (MvPowerSeries.mem_support.not.mp hnot)
  rw [map_sub, MvPowerSeries.coeff_monomial_same, sub_eq_zero] at hc
  exact hc

@[simp]
theorem initialCoeff_standardGenerator {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    ord.initialCoeff (ord.standardGenerator I v) = 1 := by
  rw [initialCoeff_def, ord.initialExp_standardGenerator hv, ord.coeff_self_standardGenerator hv]

@[simp]
theorem initialTerm_standardGenerator {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    ord.initialTerm (ord.standardGenerator I v) = MvPowerSeries.monomial v 1 := by
  rw [initialTerm_def, ord.initialExp_standardGenerator hv, ord.initialCoeff_standardGenerator hv]

theorem standardGenerator_ne_zero {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    ord.standardGenerator I v ≠ 0 := by
  rw [← ord.initialCoeff_ne_zero_iff, ord.initialCoeff_standardGenerator hv]
  exact one_ne_zero

@[simp]
theorem standardGenerator_eq_zero_iff {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ} :
    ord.standardGenerator I v = 0 ↔ v ∉ ord.initialDiagram I :=
  ⟨fun h hv ↦ ord.standardGenerator_ne_zero hv h, ord.standardGenerator_eq_zero_of_notMem⟩

theorem isLeast_toSyn_standardGenerator {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    IsLeast (ord.toSyn '' (ord.standardGenerator I v).support) (ord.toSyn v) :=
  ord.isLeast_toSyn_support_iff_ne_zero_and_initialExp_eq.mpr
    ⟨ord.standardGenerator_ne_zero hv, ord.initialExp_standardGenerator hv⟩

/-- **Bierstone–Milman Corollary 3.19**: the finite set of normalized vertex generators
`ord.standardGenerator I v` for `v ∈ ord.initialDiagramVertices I` generates `I`. -/
theorem span_image_standardGenerator_initialDiagramVertices (I : Ideal (MvPowerSeries σ K)) :
    Ideal.span (ord.standardGenerator I '' (ord.initialDiagramVertices I : Set (σ →₀ ℕ))) = I := by
  rw [← Set.range_domRestrict]
  refine ord.span_range_eq_of_forall_mem_initialDiagram_exists_le_of_divisionRing
    (α := fun v : ord.initialDiagramVertices I ↦ (v : σ →₀ ℕ))
    (fun v ↦ ord.standardGenerator_mem I v)
    (fun v ↦ ord.isLeast_toSyn_standardGenerator (ord.initialDiagramVertices_subset I v.2))
    fun γ hγ ↦ ?_
  obtain ⟨v, hvV, hle⟩ := (ord.mem_initialDiagram_iff_exists_mem_initialDiagramVertices_le).mp hγ
  exact ⟨⟨v, hvV⟩, hle⟩

end Field

end StandardGenerators

end MonomialOrder

namespace TauCeti

/-- **Hironaka's formal division theorem** in `MvPowerSeries (Fin n) K` with respect to graded
lexicographic initial exponents (Bierstone–Milman 1997, Theorem 3.17). -/
theorem formalDivision {K : Type*} [Field K] (n m : ℕ)
    (F : Fin m → MvPowerSeries (Fin n) K) (α : Fin m → (Fin n →₀ ℕ))
    (hα : ∀ i, IsLeast (toDegLex '' (F i).support) (toDegLex (α i)))
    (G : MvPowerSeries (Fin n) K) :
    ∃! qr : (Fin m → MvPowerSeries (Fin n) K) × MvPowerSeries (Fin n) K,
      G = (∑ i, qr.1 i * F i) + qr.2 ∧
      (∀ i β, β ∈ (qr.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) :=
  MonomialOrder.degLex.existsUnique_formalDivision_of_divisionRing F α hα G

end TauCeti
