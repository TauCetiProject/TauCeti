/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.RingTheory.MvPowerSeries.InitialDiagram
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Hironaka's formal division theorem for multivariate power series

Given a monomial order `ord : MonomialOrder σ` and a finite family `F : Fin m → MvPowerSeries σ R`
of formal power series whose `ord`-initial exponents `α i` carry unit coefficients, exponents in
`σ →₀ ℕ` partition into the disjoint translated cones
`Δᵢ = {γ | α i ≤ γ ∧ ∀ j < i, ¬ α j ≤ γ}` and the complementary remainder region
`Δ = {γ | ∀ i, ¬ α i ≤ γ}`. Hironaka's formal division theorem asserts that every formal power
series `G : MvPowerSeries σ R` admits a unique decomposition
`G = (∑ i, Q i * F i) + R'` such that `α i + β ∈ Δᵢ` for every `β ∈ (Q i).support` and
`β ∈ Δ` for every `β ∈ R'.support` (`MonomialOrder.existsUnique_formalDivision`).

Because the monomial order is compatible with addition and cancellative, in each coefficient
`coeff γ ((∑ i, Q i * F i) + R')` every contribution from non-initial exponents `δ ≠ α i` of `F i`
involves quotient exponents `β` satisfying `α i + β ≺[ord] γ`. Both existence (by well-founded
recursion `WellFounded.fix` on `ord.syn`) and uniqueness (as a special case of lower-set
vanishing `MonomialOrder.formalDivision_coeff_eq_zero_of_isLowerSet`) therefore hold over an
arbitrary ring `R` and arbitrary variable type `σ`, without topological completeness or finiteness
hypotheses. Specializing to `MonomialOrder.degLex` over a field gives the graded-lexicographic
division theorem `TauCeti.formalDivision`.

When `σ` is finite and the coefficients form a field `K`, choosing generators of an ideal
`I : Ideal (MvPowerSeries σ K)` at the minimal vertices `ord.initialDiagramVertices I` yields:

* a unique normal-form remainder `ord.normalRemainder I G` supported outside `ord.initialDiagram I`
  (`MonomialOrder.existsUnique_sub_mem_and_support_disjoint_initialDiagram`), linear in `G`
  (`MonomialOrder.normalRemainderLinearMap`) and vanishing precisely on `I`
  (`MonomialOrder.normalRemainder_eq_zero_iff`);
* the direct-sum complement decomposition
  `IsCompl (I.restrictScalars K) (ord.complementSubmodule I)`
  (`MonomialOrder.isCompl_restrictScalars_complementSubmodule`) and the induced `K`-linear
  isomorphism `MonomialOrder.quotientEquivComplementSubmodule` from `MvPowerSeries σ K ⧸ I` onto
  `ord.complementSubmodule I`;
* for each `v ∈ ord.initialDiagram I`, the unique normalized generator `ord.standardGenerator I v`
  in `I` whose difference from `monomial v 1` is supported outside `ord.initialDiagram I`, having
  initial exponent `v` and initial coefficient `1`, and generating `I` as `v` ranges over
  `ord.initialDiagramVertices I`
  (`MonomialOrder.span_image_standardGenerator_initialDiagramVertices`).

## Main definitions

* `MonomialOrder.complementSubmodule`: the `R`-submodule of series supported outside
  `ord.initialDiagram I`.
* `MonomialOrder.normalRemainder`, `MonomialOrder.normalRemainderLinearMap`: the canonical
  remainder modulo `I` supported outside `ord.initialDiagram I`, for `[Finite σ] [Field K]`.
* `MonomialOrder.quotientEquivComplementSubmodule`: the canonical `K`-linear isomorphism
  `(MvPowerSeries σ K ⧸ I) ≃ₗ[K] ord.complementSubmodule I`.
* `MonomialOrder.standardGenerator`: the unique normalized element of `I` congruent to
  `monomial v 1` modulo `ord.complementSubmodule I`.

## Main results

* `MonomialOrder.existsUnique_formalDivision`: Hironaka's formal division for an arbitrary
  `MonomialOrder σ` over a ring `R` when the initial coefficients are units.
* `MonomialOrder.existsUnique_formalDivision_of_divisionRing`: specialization over a division ring.
* `TauCeti.formalDivision`: graded-lexicographic formal division in `MvPowerSeries (Fin n) K`.
* `MonomialOrder.formalDivision_snd_eq_zero_iff_mem`,
  `MonomialOrder.span_range_eq_of_initialDiagram_subset`: division by initial-diagram generators
  detects membership in `I` and generates `I`.
* `MonomialOrder.isCompl_restrictScalars_complementSubmodule`: `I` and `ord.complementSubmodule I`
  are complementary `K`-submodules of `MvPowerSeries σ K`.
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

variable {σ : Type*} {m : ℕ} (α : Fin m → (σ →₀ ℕ))

/-- `inCell α i γ` holds when `γ` lies in `α i + (σ →₀ ℕ)` and avoids every earlier cone
`α j + (σ →₀ ℕ)` (`j < i`). -/
private def inCell (i : Fin m) (γ : σ →₀ ℕ) : Prop :=
  α i ≤ γ ∧ ∀ j, j < i → ¬ α j ≤ γ

/-- `inRem α γ` holds when `γ` avoids all cones `α i + (σ →₀ ℕ)`. -/
private def inRem (γ : σ →₀ ℕ) : Prop :=
  ∀ i, ¬ α i ≤ γ

private theorem inCell_unique {i₁ i₂ : Fin m} {γ : σ →₀ ℕ}
    (h₁ : inCell α i₁ γ) (h₂ : inCell α i₂ γ) : i₁ = i₂ := by
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hlt
  · exact absurd h₁.1 (h₂.2 i₁ hlt)
  · rfl
  · exact absurd h₂.1 (h₁.2 i₂ hlt)

private theorem not_inCell_of_inRem {i : Fin m} {γ : σ →₀ ℕ} (hr : inRem α γ) :
    ¬ inCell α i γ :=
  fun hc ↦ hr i hc.1

private theorem exists_inCell_of_not_inRem {γ : σ →₀ ℕ} (h : ¬ inRem α γ) :
    ∃ i, inCell α i γ := by
  classical
  simp only [inRem, not_forall, not_not] at h
  let s : Finset (Fin m) := Finset.univ.filter fun i ↦ α i ≤ γ
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, fun j hj hle ↦ ?_⟩
  exact hj.not_ge (s.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩))

private theorem inRem_iff_not_exists_inCell {γ : σ →₀ ℕ} :
    inRem α γ ↔ ¬ ∃ i, inCell α i γ :=
  ⟨fun hr ⟨_, hi⟩ ↦ not_inCell_of_inRem α hr hi,
    fun h ↦ by_contra fun hr ↦ h (exists_inCell_of_not_inRem α hr)⟩

private theorem inCell_add_iff {i : Fin m} {β : σ →₀ ℕ} :
    inCell α i (α i + β) ↔ ∀ j, j < i → ¬ α j ≤ α i + β :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨le_self_add, h⟩⟩

end Partition

section GeneralDivision

variable {σ R : Type*} [Ring R] (ord : MonomialOrder σ) {m : ℕ}

open scoped Classical in
/-- Sum of all lower-order contributions `(p.2 ≠ α i)` to `coeff γ (∑ i, Q i * F i)`. -/
private noncomputable def lowerSum (F : Fin m → MvPowerSeries σ R) (α : Fin m → (σ →₀ ℕ))
    (Q : Fin m → MvPowerSeries σ R) (γ : σ →₀ ℕ) : R :=
  ∑ i : Fin m, ∑ p ∈ (Finset.antidiagonal γ).filter (fun p ↦ p.2 ≠ α i),
    MvPowerSeries.coeff p.1 (Q i) * MvPowerSeries.coeff p.2 (F i)

open scoped Classical in
private theorem coeff_mul_eq_ite_inCell {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    {Q : Fin m → MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (i : Fin m) (γ : σ →₀ ℕ) :
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
      have hnot : ¬ inCell α i (α i + (γ - α i)) := by
        rwa [add_tsub_cancel_of_le hle]
      have hzero : MvPowerSeries.coeff (γ - α i) (Q i) = 0 := by
        by_contra hne
        exact hnot ((inCell_add_iff α).mpr (hQ i (γ - α i) hne))
      rw [hzero, zero_mul]
    · exact Finset.sum_empty

private theorem coeff_sum_add_of_inCell {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    {Q : Fin m → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β)
    {i₀ : Fin m} {γ : σ →₀ ℕ} (hi₀ : inCell α i₀ γ) :
    MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) =
      MvPowerSeries.coeff (γ - α i₀) (Q i₀) * MvPowerSeries.coeff (α i₀) (F i₀) +
        lowerSum F α Q γ := by
  classical
  have hrem0 : MvPowerSeries.coeff γ rem = 0 := by
    by_contra hne
    exact hR γ hne i₀ hi₀.1
  rw [map_add, hrem0, add_zero, map_sum]
  simp_rw [coeff_mul_eq_ite_inCell hQ, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i₀]
  · exact ite_eq_left hi₀
  · intro i _ hne
    exact ite_eq_right fun hi ↦ hne (inCell_unique α hi hi₀)
  · intro hmem
    exact absurd (Finset.mem_univ i₀) hmem

private theorem coeff_sum_add_of_inRem {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    {Q : Fin m → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    {γ : σ →₀ ℕ} (hr : inRem α γ) :
    MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) =
      MvPowerSeries.coeff γ rem + lowerSum F α Q γ := by
  classical
  rw [map_add, add_comm _ (MvPowerSeries.coeff γ rem), map_sum]
  simp_rw [coeff_mul_eq_ite_inCell hQ, Finset.sum_add_distrib]
  have hzero : (∑ x : Fin m, if inCell α x γ then
      MvPowerSeries.coeff (γ - α x) (Q x) * MvPowerSeries.coeff (α x) (F x) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ ite_eq_right (not_inCell_of_inRem α hr)
  rw [hzero, zero_add]
  rfl

private theorem toSyn_add_lt_of_mem_antidiagonal {F : Fin m → MvPowerSeries σ R}
    {α : Fin m → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    {i : Fin m} {γ : σ →₀ ℕ} {p : (σ →₀ ℕ) × (σ →₀ ℕ)} [DecidableEq σ]
    (hp : p ∈ Finset.antidiagonal γ) (hne : p.2 ≠ α i)
    (hc : MvPowerSeries.coeff p.2 (F i) ≠ 0) :
    ord.toSyn (α i + p.1) < ord.toSyn γ := by
  rw [Finset.mem_antidiagonal] at hp
  have hmem : p.2 ∈ (F i).support := hc
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
theorem formalDivision_coeff_eq_zero_of_isLowerSet
    {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    {Q : Fin m → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
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
        exact hcell (hsum ▸ (inCell_add_iff α).mpr (hQ i β hne))
    have hR_zero : MvPowerSeries.coeff γ rem = 0 := by
      by_cases hr : inRem α γ
      · have htot := coeff_sum_add_of_inRem (F := F) hQ (rem := rem) hr
        rw [hG γ (hγs ▸ hs), hlow, add_zero] at htot
        exact htot.symm
      · obtain ⟨i, hi⟩ := exists_inCell_of_not_inRem α hr
        by_contra hne
        exact hR γ hne i hi.1
    exact ⟨hQ_zero, hR_zero⟩
  refine ⟨fun i β hβ ↦ (key _ hβ).1 i β rfl, fun γ hγ ↦ ?_⟩
  simpa only [AddEquiv.symm_apply_apply] using (key (ord.toSyn γ) hγ).2

/-- Strict initial-segment vanishing for formal division: if `(∑ i, Q i * F i) + rem` vanishes at
all exponents strictly `ord`-smaller than `t`, so do `rem` and the shifted quotients `Q i`. -/
theorem formalDivision_coeff_eq_zero_of_forall_lt
    {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    {Q : Fin m → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β) {t : ord.syn}
    (hG : ∀ γ, ord.toSyn γ < t → MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) = 0) :
    (∀ i β, ord.toSyn (α i + β) < t → MvPowerSeries.coeff β (Q i) = 0) ∧
      (∀ γ, ord.toSyn γ < t → MvPowerSeries.coeff γ rem = 0) :=
  ord.formalDivision_coeff_eq_zero_of_isLowerSet hα hu hQ hR (IsLowerSet.Iio t) hG

/-- Closed initial-segment vanishing for formal division: if `(∑ i, Q i * F i) + rem` vanishes at
all exponents `ord`-at-most `t`, so do `rem` and the shifted quotients `Q i`. -/
theorem formalDivision_coeff_eq_zero_of_forall_le
    {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    {Q : Fin m → MvPowerSeries σ R} {rem : MvPowerSeries σ R}
    (hQ : ∀ i β, β ∈ (Q i).support → ∀ j, j < i → ¬ α j ≤ α i + β)
    (hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β) {t : ord.syn}
    (hG : ∀ γ, ord.toSyn γ ≤ t → MvPowerSeries.coeff γ ((∑ i, Q i * F i) + rem) = 0) :
    (∀ i β, ord.toSyn (α i + β) ≤ t → MvPowerSeries.coeff β (Q i) = 0) ∧
      (∀ γ, ord.toSyn γ ≤ t → MvPowerSeries.coeff γ rem = 0) :=
  ord.formalDivision_coeff_eq_zero_of_isLowerSet hα hu hQ hR (IsLowerSet.Iic t) hG

private theorem formalDivision_unique
    {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    {G : MvPowerSeries σ R}
    {qr₁ qr₂ : (Fin m → MvPowerSeries σ R) × MvPowerSeries σ R}
    (h₁ : G = (∑ i, qr₁.1 i * F i) + qr₁.2 ∧
      (∀ i β, β ∈ (qr₁.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr₁.2.support, ∀ i, ¬ α i ≤ β))
    (h₂ : G = (∑ i, qr₂.1 i * F i) + qr₂.2 ∧
      (∀ i β, β ∈ (qr₂.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr₂.2.support, ∀ i, ¬ α i ≤ β)) :
    qr₁ = qr₂ := by
  have hQ : ∀ i β, β ∈ (qr₁.1 i - qr₂.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β := by
    intro i β hβ
    have hc : MvPowerSeries.coeff β (qr₁.1 i - qr₂.1 i) ≠ 0 := hβ
    rw [map_sub, sub_ne_zero] at hc
    by_cases hc₁ : MvPowerSeries.coeff β (qr₁.1 i) = 0
    · have hc₂ : MvPowerSeries.coeff β (qr₂.1 i) ≠ 0 := fun h ↦ hc (hc₁.trans h.symm)
      exact h₂.2.1 i β hc₂
    · exact h₁.2.1 i β hc₁
  have hR : ∀ β ∈ (qr₁.2 - qr₂.2).support, ∀ i, ¬ α i ≤ β := by
    intro β hβ
    have hc : MvPowerSeries.coeff β (qr₁.2 - qr₂.2) ≠ 0 := hβ
    rw [map_sub, sub_ne_zero] at hc
    by_cases hc₁ : MvPowerSeries.coeff β qr₁.2 = 0
    · have hc₂ : MvPowerSeries.coeff β qr₂.2 ≠ 0 := fun h ↦ hc (hc₁.trans h.symm)
      exact h₂.2.2 β hc₂
    · exact h₁.2.2 β hc₁
  have hsum : (∑ i, (qr₁.1 i - qr₂.1 i) * F i) + (qr₁.2 - qr₂.2) = 0 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    have heq : (∑ i, qr₁.1 i * F i) + qr₁.2 = (∑ i, qr₂.1 i * F i) + qr₂.2 :=
      h₁.1.symm.trans h₂.1
    calc
      (∑ i, qr₁.1 i * F i - ∑ i, qr₂.1 i * F i) + (qr₁.2 - qr₂.2) =
          ((∑ i, qr₁.1 i * F i) + qr₁.2) - ((∑ i, qr₂.1 i * F i) + qr₂.2) :=
        (add_sub_add_comm _ _ _ _).symm
      _ = 0 := sub_eq_zero.mpr heq
  obtain ⟨hQ0, hR0⟩ := ord.formalDivision_coeff_eq_zero_of_isLowerSet hα hu hQ hR isLowerSet_univ
    fun γ _ ↦ by rw [hsum, map_zero]
  refine Prod.ext (funext fun i ↦ MvPowerSeries.ext fun β ↦ ?_) (MvPowerSeries.ext fun γ ↦ ?_)
  · exact sub_eq_zero.mp (by simpa only [map_sub] using hQ0 i β trivial)
  · exact sub_eq_zero.mp (by simpa only [map_sub] using hR0 γ trivial)

open scoped Classical in
/-- Recursive step computing the unique normalized value at `s : ord.syn` from strictly smaller
values in `ord.syn`. -/
private noncomputable def divStep (F : Fin m → MvPowerSeries σ R) (α : Fin m → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R)
    (s : ord.syn) (rec : ∀ t, t < s → R) : R :=
  let γ := ord.toSyn.symm s
  let L : R := ∑ i : Fin m, ∑ p ∈ (Finset.antidiagonal γ).filter (fun p ↦ p.2 ≠ α i),
    if h : ord.toSyn (α i + p.1) < s ∧ inCell α i (α i + p.1) then
      rec (ord.toSyn (α i + p.1)) h.1 * MvPowerSeries.coeff p.2 (F i)
    else 0
  if hex : ∃ i, inCell α i γ then
    (MvPowerSeries.coeff γ G - L) * ↑(hu hex.choose).unit⁻¹
  else
    MvPowerSeries.coeff γ G - L

open scoped Classical in
private noncomputable def divVal (F : Fin m → MvPowerSeries σ R) (α : Fin m → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R) :
    ord.syn → R :=
  WellFounded.fix (wellFounded_lt (α := ord.syn)) (ord.divStep F α hu G)

open scoped Classical in
private noncomputable def divQuot (F : Fin m → MvPowerSeries σ R) (α : Fin m → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R) :
    Fin m → MvPowerSeries σ R :=
  fun i β ↦ if inCell α i (α i + β) then ord.divVal F α hu G (ord.toSyn (α i + β)) else 0

open scoped Classical in
private noncomputable def divRem (F : Fin m → MvPowerSeries σ R) (α : Fin m → (σ →₀ ℕ))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i))) (G : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  fun γ ↦ if inRem α γ then ord.divVal F α hu G (ord.toSyn γ) else 0

open scoped Classical in
private theorem divVal_eq
    {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    (G : MvPowerSeries σ R) (γ : σ →₀ ℕ) :
    ord.divVal F α hu G (ord.toSyn γ) =
      if hex : ∃ i, inCell α i γ then
        (MvPowerSeries.coeff γ G - lowerSum F α (ord.divQuot F α hu G) γ) *
          ↑(hu hex.choose).unit⁻¹
      else
        MvPowerSeries.coeff γ G - lowerSum F α (ord.divQuot F α hu G) γ := by
  have hL : (∑ i : Fin m,
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
        rw [dite_eq_left hcond]
        simp [divQuot, MvPowerSeries.coeff_apply, hcell]
      · have hcond : ¬ (ord.toSyn (α i + p.1) < ord.toSyn γ ∧ inCell α i (α i + p.1)) :=
          fun h ↦ hcell h.2
        rw [dite_eq_right hcond]
        simp [divQuot, MvPowerSeries.coeff_apply, hcell]
  have hfix : ord.divVal F α hu G (ord.toSyn γ) =
      ord.divStep F α hu G (ord.toSyn γ) (fun t _ ↦ ord.divVal F α hu G t) :=
    WellFounded.fix_eq _ _ (ord.toSyn γ)
  rw [hfix]
  dsimp only [divStep]
  simp only [AddEquiv.symm_apply_apply, hL]

private theorem divQuot_rem_spec
    {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
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
    have hc : (if inCell α i (α i + β) then ord.divVal F α hu G (ord.toSyn (α i + β)) else 0) ≠
        0 := hβ
    by_cases hcell : inCell α i (α i + β)
    · exact hcell.2
    · exact absurd (ite_eq_right hcell) hc
  have hR : ∀ β ∈ rem.support, ∀ i, ¬ α i ≤ β := by
    intro γ hγ
    have hc : (if inRem α γ then ord.divVal F α hu G (ord.toSyn γ) else 0) ≠ 0 := hγ
    by_cases hr : inRem α γ
    · exact hr
    · exact absurd (ite_eq_right hr) hc
  refine ⟨MvPowerSeries.ext fun γ ↦ ?_, hQ, hR⟩
  by_cases hex : ∃ i, inCell α i γ
  · have hi₀ : inCell α hex.choose γ := hex.choose_spec
    rw [coeff_sum_add_of_inCell hQ hR hi₀]
    have hQcoeff : MvPowerSeries.coeff (γ - α hex.choose) (Q hex.choose) =
        ord.divVal F α hu G (ord.toSyn γ) := by
      have hadd : α hex.choose + (γ - α hex.choose) = γ := add_tsub_cancel_of_le hi₀.1
      simp only [Q, divQuot, MvPowerSeries.coeff_apply, hadd, ite_eq_left hi₀]
    rw [hQcoeff, ord.divVal_eq hα hu G γ, dite_eq_left hex]
    have hunit : (↑(hu hex.choose).unit⁻¹ : R) * MvPowerSeries.coeff (α hex.choose) (F hex.choose) =
        1 := by
      simpa only [IsUnit.unit_spec] using Units.inv_mul (hu hex.choose).unit
    rw [mul_assoc, hunit, mul_one, sub_add_cancel]
  · have hr : inRem α γ := (inRem_iff_not_exists_inCell α).mpr hex
    rw [coeff_sum_add_of_inRem hQ (rem := rem) hr]
    have hRcoeff : MvPowerSeries.coeff γ rem = ord.divVal F α hu G (ord.toSyn γ) := by
      simp only [rem, divRem, MvPowerSeries.coeff_apply, ite_eq_left hr]
    rw [hRcoeff, ord.divVal_eq hα hu G γ, dite_eq_right hex, sub_add_cancel]

/-- **Hironaka's formal division theorem** for an arbitrary monomial order `ord` over a ring `R`:
if each `F i` has `ord`-initial exponent `α i` with a unit coefficient, then every formal power
series `G` admits a unique decomposition `G = (∑ i, Q i * F i) + R'` whose quotient supports
satisfy `α i + supp(Q i) ⊆ Δᵢ` and whose remainder support avoids every cone `α i + (σ →₀ ℕ)`. -/
theorem existsUnique_formalDivision
    (F : Fin m → MvPowerSeries σ R) (α : Fin m → (σ →₀ ℕ))
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hu : ∀ i, IsUnit (MvPowerSeries.coeff (α i) (F i)))
    (G : MvPowerSeries σ R) :
    ∃! qr : (Fin m → MvPowerSeries σ R) × MvPowerSeries σ R,
      G = (∑ i, qr.1 i * F i) + qr.2 ∧
      (∀ i β, β ∈ (qr.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) :=
  ⟨(ord.divQuot F α hu G, ord.divRem F α hu G),
    ord.divQuot_rem_spec hα hu G,
    fun _ h ↦ ord.formalDivision_unique hα hu h (ord.divQuot_rem_spec hα hu G)⟩

/-- Over a division ring `K`, every `ord`-initial coefficient is automatically a unit, so formal
division requires only that `α i` is the `ord`-initial exponent of `F i`. -/
theorem existsUnique_formalDivision_of_divisionRing {K : Type*} [DivisionRing K]
    (F : Fin m → MvPowerSeries σ K) (α : Fin m → (σ →₀ ℕ))
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (G : MvPowerSeries σ K) :
    ∃! qr : (Fin m → MvPowerSeries σ K) × MvPowerSeries σ K,
      G = (∑ i, qr.1 i * F i) + qr.2 ∧
      (∀ i β, β ∈ (qr.1 i).support → ∀ j, j < i → ¬ α j ≤ α i + β) ∧
      (∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) := by
  refine ord.existsUnique_formalDivision F α hα (fun i ↦ ?_) G
  obtain ⟨hf0, hexp⟩ := ord.isLeast_toSyn_iff.mp (hα i)
  rw [← hexp]
  exact (ord.coeff_initialExp_ne_zero hf0).isUnit

end GeneralDivision

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

namespace MonomialOrder

section StandardGenerators

variable {σ : Type*} (ord : MonomialOrder σ)

/-- The `R`-submodule of `MvPowerSeries σ R` consisting of power series whose support is disjoint
from `ord.initialDiagram I`. -/
def complementSubmodule {R : Type*} [Semiring R] (I : Ideal (MvPowerSeries σ R)) :
    Submodule R (MvPowerSeries σ R) where
  carrier := {f | ∀ β ∈ f.support, β ∉ ord.initialDiagram I}
  zero_mem' β hβ := absurd (MvPowerSeries.coeff_zero β) hβ
  add_mem' {f g} hf hg β hβ := by
    have hc : MvPowerSeries.coeff β (f + g) ≠ 0 := hβ
    rw [map_add] at hc
    by_cases hcf : MvPowerSeries.coeff β f = 0
    · rw [hcf, zero_add] at hc
      exact hg β hc
    · exact hf β hcf
  smul_mem' c {f} hf β hβ := by
    have hc : MvPowerSeries.coeff β (c • f) ≠ 0 := hβ
    rw [MvPowerSeries.coeff_smul] at hc
    exact hf β (right_ne_zero_of_mul hc)

@[simp]
theorem mem_complementSubmodule_iff {R : Type*} [Semiring R]
    {I : Ideal (MvPowerSeries σ R)} {f : MvPowerSeries σ R} :
    f ∈ ord.complementSubmodule I ↔ ∀ β ∈ f.support, β ∉ ord.initialDiagram I := (Iff.rfl)

theorem disjoint_restrictScalars_complementSubmodule {R : Type*} [CommSemiring R]
    (I : Ideal (MvPowerSeries σ R)) :
    Disjoint (I.restrictScalars R) (ord.complementSubmodule I) := by
  rw [Submodule.disjoint_def]
  intro f hfI hfc
  exact ord.eq_zero_of_mem_of_disjoint_support hfI hfc

/-- If `F i ∈ I` have exponents `α i` whose cones cover `ord.initialDiagram I`, then in any
decomposition `G = (∑ i, Q i * F i) + R'` whose remainder avoids every cone `α i + (σ →₀ ℕ)`, the
remainder `R'` vanishes if and only if `G ∈ I`. -/
theorem formalDivision_snd_eq_zero_iff_mem {R : Type*} [Ring R]
    {m : ℕ} {I : Ideal (MvPowerSeries σ R)}
    {F : Fin m → MvPowerSeries σ R} {α : Fin m → (σ →₀ ℕ)}
    (hFI : ∀ i, F i ∈ I)
    (hD : ∀ γ ∈ ord.initialDiagram I, ∃ i, α i ≤ γ)
    {G : MvPowerSeries σ R}
    {qr : (Fin m → MvPowerSeries σ R) × MvPowerSeries σ R}
    (hdiv : G = (∑ i, qr.1 i * F i) + qr.2)
    (hrem : ∀ β ∈ qr.2.support, ∀ i, ¬ α i ≤ β) :
    qr.2 = 0 ↔ G ∈ I := by
  refine ⟨fun h0 ↦ ?_, fun hGI ↦ ?_⟩
  · rw [hdiv, h0, add_zero]
    exact sum_mem fun i _ ↦ I.mul_mem_left (qr.1 i) (hFI i)
  · have hremI : qr.2 ∈ I := by
      have hsub : qr.2 = G - ∑ i, qr.1 i * F i := eq_sub_of_add_eq' hdiv.symm
      rw [hsub]
      exact I.sub_mem hGI (sum_mem fun i _ ↦ I.mul_mem_left (qr.1 i) (hFI i))
    exact ord.eq_zero_of_mem_of_disjoint_support hremI fun β hβ hβD ↦ by
      obtain ⟨i, hi⟩ := hD β hβD
      exact hrem β hβ i hi

/-- Over a division ring `K`, any finite family `F i ∈ I` whose `ord`-initial exponents `α i`
generate `ord.initialDiagram I` as an upper set generates `I` as a left ideal of
`MvPowerSeries σ K`. -/
theorem span_range_eq_of_initialDiagram_subset {K : Type*} [DivisionRing K]
    {m : ℕ} {I : Ideal (MvPowerSeries σ K)}
    {F : Fin m → MvPowerSeries σ K} {α : Fin m → (σ →₀ ℕ)}
    (hFI : ∀ i, F i ∈ I)
    (hα : ∀ i, IsLeast (ord.toSyn '' (F i).support) (ord.toSyn (α i)))
    (hD : ∀ γ ∈ ord.initialDiagram I, ∃ i, α i ≤ γ) :
    Ideal.span (Set.range F) = I := by
  refine le_antisymm (Ideal.span_le.mpr (Set.range_subset_iff.mpr hFI)) fun G hGI ↦ ?_
  obtain ⟨qr, ⟨hdiv, _, hrem⟩, _⟩ := ord.existsUnique_formalDivision_of_divisionRing F α hα G
  have hr0 : qr.2 = 0 := (ord.formalDivision_snd_eq_zero_iff_mem hFI hD hdiv hrem).mpr hGI
  rw [hdiv, hr0, add_zero]
  exact sum_mem fun i _ ↦ Ideal.mul_mem_left _ (qr.1 i) (Ideal.subset_span ⟨i, rfl⟩)

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
    fun i ↦ ord.isLeast_toSyn_iff.mpr ⟨hF0 i, hFexp i⟩, fun i ↦ ?_, fun γ hγ ↦ ?_⟩
  · dsimp only
    rw [← hFexp i]
    exact (ord.coeff_initialExp_ne_zero (hF0 i)).isUnit
  · obtain ⟨v, hvV, hle⟩ :=
      (ord.mem_initialDiagram_iff_exists_mem_initialDiagramVertices_le).mp hγ
    exact ⟨e.symm ⟨v, hvV⟩, by simpa using hle⟩

/-- Every power series `G : MvPowerSeries σ K` is congruent modulo `I` to a unique series `R'`
whose support avoids `ord.initialDiagram I`. -/
theorem existsUnique_sub_mem_and_support_disjoint_initialDiagram
    (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    ∃! R' : MvPowerSeries σ K, G - R' ∈ I ∧ ∀ β ∈ R'.support, β ∉ ord.initialDiagram I := by
  obtain ⟨m, F, α, hFI, hα, hu, hD⟩ := ord.exists_vertex_family I
  obtain ⟨qr, ⟨hdiv, _, hrem⟩, _⟩ := ord.existsUnique_formalDivision F α hα hu G
  have hqr_mem : G - qr.2 ∈ I := by
    rw [sub_eq_of_eq_add hdiv]
    exact sum_mem fun i _ ↦ I.mul_mem_left (qr.1 i) (hFI i)
  have hqr_supp : ∀ β ∈ qr.2.support, β ∉ ord.initialDiagram I := fun β hβ hβD ↦ by
    obtain ⟨i, hi⟩ := hD β hβD
    exact hrem β hβ i hi
  refine ⟨qr.2, ⟨hqr_mem, hqr_supp⟩, fun R₁ ⟨hR₁I, hR₁supp⟩ ↦ ?_⟩
  have hdiffI : R₁ - qr.2 ∈ I := by
    have hsub : R₁ - qr.2 = (G - qr.2) - (G - R₁) := by abel
    exact hsub ▸ I.sub_mem hqr_mem hR₁I
  have hdiff_supp : ∀ β ∈ (R₁ - qr.2).support, β ∉ ord.initialDiagram I :=
    (ord.complementSubmodule I).sub_mem hR₁supp hqr_supp
  exact sub_eq_zero.mp (ord.eq_zero_of_mem_of_disjoint_support hdiffI hdiff_supp)

/-- `I` (restricted to `K`-scalars) and `ord.complementSubmodule I` are complementary
`K`-submodules of `MvPowerSeries σ K`. -/
theorem isCompl_restrictScalars_complementSubmodule (I : Ideal (MvPowerSeries σ K)) :
    IsCompl (I.restrictScalars K) (ord.complementSubmodule I) := by
  refine ⟨ord.disjoint_restrictScalars_complementSubmodule I, codisjoint_iff_le_sup.mpr ?_⟩
  intro G _
  obtain ⟨R', ⟨hGR, hRsupp⟩, _⟩ :=
    ord.existsUnique_sub_mem_and_support_disjoint_initialDiagram I G
  have hsum : (G - R') + R' = G := sub_add_cancel G R'
  exact hsum ▸ Submodule.add_mem_sup hGR hRsupp

/-- The canonical normal-form remainder of `G : MvPowerSeries σ K` modulo `I`, uniquely
characterized by `G - ord.normalRemainder I G ∈ I` and support disjoint from
`ord.initialDiagram I`. -/
noncomputable def normalRemainder (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    MvPowerSeries σ K :=
  (ord.existsUnique_sub_mem_and_support_disjoint_initialDiagram I G).choose

theorem sub_normalRemainder_mem (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    G - ord.normalRemainder I G ∈ I :=
  (ord.existsUnique_sub_mem_and_support_disjoint_initialDiagram I G).choose_spec.1.1

theorem notMem_initialDiagram_of_mem_support_normalRemainder
    (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K)
    {β : σ →₀ ℕ} (hβ : β ∈ (ord.normalRemainder I G).support) :
    β ∉ ord.initialDiagram I :=
  (ord.existsUnique_sub_mem_and_support_disjoint_initialDiagram I G).choose_spec.1.2 β hβ

theorem normalRemainder_mem_complementSubmodule
    (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    ord.normalRemainder I G ∈ ord.complementSubmodule I :=
  fun _ hβ ↦ ord.notMem_initialDiagram_of_mem_support_normalRemainder I G hβ

theorem eq_normalRemainder_iff {I : Ideal (MvPowerSeries σ K)}
    {G R' : MvPowerSeries σ K} :
    R' = ord.normalRemainder I G ↔
      G - R' ∈ I ∧ ∀ β ∈ R'.support, β ∉ ord.initialDiagram I :=
  ⟨fun h ↦ h ▸ ⟨ord.sub_normalRemainder_mem I G,
    fun _ hβ ↦ ord.notMem_initialDiagram_of_mem_support_normalRemainder I G hβ⟩,
    (ord.existsUnique_sub_mem_and_support_disjoint_initialDiagram I G).choose_spec.2 R'⟩

@[simp]
theorem normalRemainder_eq_zero_iff {I : Ideal (MvPowerSeries σ K)} {G : MvPowerSeries σ K} :
    ord.normalRemainder I G = 0 ↔ G ∈ I := by
  rw [eq_comm, ord.eq_normalRemainder_iff]
  refine ⟨fun h ↦ by simpa using h.1, fun hG ↦ ⟨by simpa using hG, fun β hβ ↦ ?_⟩⟩
  exact absurd (MvPowerSeries.coeff_zero β) hβ

@[simp]
theorem normalRemainder_zero (I : Ideal (MvPowerSeries σ K)) :
    ord.normalRemainder I 0 = 0 :=
  ord.normalRemainder_eq_zero_iff.mpr I.zero_mem

theorem normalRemainder_eq_self_of_mem_complementSubmodule
    {I : Ideal (MvPowerSeries σ K)} {G : MvPowerSeries σ K}
    (hG : G ∈ ord.complementSubmodule I) :
    ord.normalRemainder I G = G :=
  (ord.eq_normalRemainder_iff.mpr ⟨by simp, hG⟩).symm

@[simp]
theorem normalRemainder_idem (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    ord.normalRemainder I (ord.normalRemainder I G) = ord.normalRemainder I G :=
  ord.normalRemainder_eq_self_of_mem_complementSubmodule
    (ord.normalRemainder_mem_complementSubmodule I G)

/-- `ord.normalRemainder I` bundled as a `K`-linear endomorphism of `MvPowerSeries σ K`. -/
noncomputable def normalRemainderLinearMap (I : Ideal (MvPowerSeries σ K)) :
    MvPowerSeries σ K →ₗ[K] MvPowerSeries σ K where
  toFun := ord.normalRemainder I
  map_add' f g := by
    symm
    refine ord.eq_normalRemainder_iff.mpr ⟨?_, ?_⟩
    · have hsub : (f + g) - (ord.normalRemainder I f + ord.normalRemainder I g) =
          (f - ord.normalRemainder I f) + (g - ord.normalRemainder I g) := by abel
      rw [hsub]
      exact I.add_mem (ord.sub_normalRemainder_mem I f) (ord.sub_normalRemainder_mem I g)
    · exact (ord.complementSubmodule I).add_mem
        (ord.normalRemainder_mem_complementSubmodule I f)
        (ord.normalRemainder_mem_complementSubmodule I g)
  map_smul' c f := by
    symm
    refine ord.eq_normalRemainder_iff.mpr ⟨?_, ?_⟩
    · have hsub : c • f - c • ord.normalRemainder I f = c • (f - ord.normalRemainder I f) :=
        (smul_sub c f (ord.normalRemainder I f)).symm
      rw [RingHom.id_apply, hsub]
      exact (I.restrictScalars K).smul_mem c (ord.sub_normalRemainder_mem I f)
    · rw [RingHom.id_apply]
      exact (ord.complementSubmodule I).smul_mem c
        (ord.normalRemainder_mem_complementSubmodule I f)

@[simp]
theorem normalRemainderLinearMap_apply (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K) :
    ord.normalRemainderLinearMap I G = ord.normalRemainder I G := (rfl)

theorem normalRemainder_eq_iff_sub_mem {I : Ideal (MvPowerSeries σ K)}
    {f g : MvPowerSeries σ K} :
    ord.normalRemainder I f = ord.normalRemainder I g ↔ f - g ∈ I := by
  rw [← sub_eq_zero, ← ord.normalRemainderLinearMap_apply, ← ord.normalRemainderLinearMap_apply,
    ← map_sub, ord.normalRemainderLinearMap_apply, ord.normalRemainder_eq_zero_iff]

@[simp]
theorem ker_normalRemainderLinearMap (I : Ideal (MvPowerSeries σ K)) :
    LinearMap.ker (ord.normalRemainderLinearMap I) = I.restrictScalars K := by
  ext G
  simp [LinearMap.mem_ker]

@[simp]
theorem range_normalRemainderLinearMap (I : Ideal (MvPowerSeries σ K)) :
    LinearMap.range (ord.normalRemainderLinearMap I) = ord.complementSubmodule I := by
  ext G
  simp only [LinearMap.mem_range, normalRemainderLinearMap_apply]
  exact ⟨fun ⟨H, hH⟩ ↦ hH ▸ ord.normalRemainder_mem_complementSubmodule I H,
    fun hG ↦ ⟨G, ord.normalRemainder_eq_self_of_mem_complementSubmodule hG⟩⟩

/-- The canonical `K`-linear isomorphism between `MvPowerSeries σ K ⧸ I` and the complementary
monomial-support subspace `ord.complementSubmodule I` induced by `ord.normalRemainder I`. -/
noncomputable def quotientEquivComplementSubmodule (I : Ideal (MvPowerSeries σ K)) :
    (MvPowerSeries σ K ⧸ I) ≃ₗ[K] ord.complementSubmodule I :=
  (Submodule.Quotient.restrictScalarsEquiv K I).symm.trans <|
    (Submodule.quotEquivOfEq (I.restrictScalars K) (LinearMap.ker (ord.normalRemainderLinearMap I))
      (ord.ker_normalRemainderLinearMap I).symm).trans <|
      (ord.normalRemainderLinearMap I).quotKerEquivRange.trans <|
        LinearEquiv.ofEq _ _ (ord.range_normalRemainderLinearMap I)

@[simp]
theorem coe_quotientEquivComplementSubmodule_mk (I : Ideal (MvPowerSeries σ K))
    (G : MvPowerSeries σ K) :
    (ord.quotientEquivComplementSubmodule I (Ideal.Quotient.mk I G) : MvPowerSeries σ K) =
      ord.normalRemainder I G := (rfl)

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

theorem standardGenerator_mem (I : Ideal (MvPowerSeries σ K)) (v : σ →₀ ℕ) :
    ord.standardGenerator I v ∈ I :=
  ord.sub_normalRemainder_mem I (MvPowerSeries.monomial v 1)

theorem notMem_initialDiagram_of_mem_support_standardGenerator_sub_monomial
    (I : Ideal (MvPowerSeries σ K)) (v : σ →₀ ℕ)
    {β : σ →₀ ℕ} (hβ : β ∈ (ord.standardGenerator I v - MvPowerSeries.monomial v 1).support) :
    β ∉ ord.initialDiagram I := by
  have hsub : ord.standardGenerator I v - MvPowerSeries.monomial v 1 =
      -ord.normalRemainder I (MvPowerSeries.monomial v 1) := by
    rw [standardGenerator_def, sub_sub_cancel_left]
  have hc : MvPowerSeries.coeff β (ord.normalRemainder I (MvPowerSeries.monomial v 1)) ≠ 0 := by
    have hc' : MvPowerSeries.coeff β (ord.standardGenerator I v - MvPowerSeries.monomial v 1) ≠
        0 := hβ
    rwa [hsub, map_neg, neg_ne_zero] at hc'
  exact ord.notMem_initialDiagram_of_mem_support_normalRemainder I _ hc

theorem standardGenerator_eq_zero_of_notMem {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∉ ord.initialDiagram I) :
    ord.standardGenerator I v = 0 := by
  have hcomp : MvPowerSeries.monomial v (1 : K) ∈ ord.complementSubmodule I := by
    intro β hβ
    have heq : β = v := MvPowerSeries.eq_of_coeff_monomial_ne_zero hβ
    rwa [heq]
  rw [standardGenerator_def, ord.normalRemainder_eq_self_of_mem_complementSubmodule hcomp,
    sub_self]

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
      refine ord.eq_normalRemainder_iff.mpr ⟨?_, ?_⟩
      · simpa only [sub_sub_cancel] using hfI
      · intro β hβ
        have hc : MvPowerSeries.coeff β (f - MvPowerSeries.monomial v 1) ≠ 0 := by
          have hc' : MvPowerSeries.coeff β (MvPowerSeries.monomial v 1 - f) ≠ 0 := hβ
          rwa [← neg_sub, map_neg, neg_ne_zero] at hc'
        exact hsupp β hc
    calc
      f = MvPowerSeries.monomial v 1 - (MvPowerSeries.monomial v 1 - f) := (sub_sub_cancel _ _).symm
      _ = ord.standardGenerator I v := by rw [hrem, standardGenerator_def]

/-- If `G` has zero coefficients on `ord.toSyn ⁻¹' S` for a lower set `S : Set ord.syn`, then so
does `ord.normalRemainder I G`. -/
theorem coeff_normalRemainder_eq_zero_of_isLowerSet {I : Ideal (MvPowerSeries σ K)}
    {G : MvPowerSeries σ K} {S : Set ord.syn} (hS : IsLowerSet S)
    (hG : ∀ γ, ord.toSyn γ ∈ S → MvPowerSeries.coeff γ G = 0) :
    ∀ γ, ord.toSyn γ ∈ S → MvPowerSeries.coeff γ (ord.normalRemainder I G) = 0 := by
  obtain ⟨m, F, α, hFI, hα, hu, hD⟩ := ord.exists_vertex_family I
  obtain ⟨qr, ⟨hdiv, hQ, hR⟩, _⟩ := ord.existsUnique_formalDivision F α hα hu G
  have hqr_eq : qr.2 = ord.normalRemainder I G := by
    refine ord.eq_normalRemainder_iff.mpr ⟨?_, fun β hβ hβD ↦ ?_⟩
    · rw [sub_eq_of_eq_add hdiv]
      exact sum_mem fun i _ ↦ I.mul_mem_left (qr.1 i) (hFI i)
    · obtain ⟨i, hi⟩ := hD β hβD
      exact hR β hβ i hi
  rw [← hqr_eq]
  exact (ord.formalDivision_coeff_eq_zero_of_isLowerSet hα hu hQ hR hS
    fun γ hγ ↦ hdiv ▸ hG γ hγ).2

/-- For `v ∈ ord.initialDiagram I`, `ord.standardGenerator I v` has `ord`-initial exponent `v`. -/
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
    have hlin := map_sub (ord.normalRemainderLinearMap I) g' (MvPowerSeries.monomial v 1)
    simpa only [h, normalRemainderLinearMap_apply, ord.normalRemainder_eq_zero_iff.mpr hg'I,
      zero_sub] using hlin
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
    by_contra fun h ↦ hnot h
  rw [map_sub, MvPowerSeries.coeff_monomial_same, sub_eq_zero] at hc
  exact hc

@[simp]
theorem initialCoeff_standardGenerator {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    ord.initialCoeff (ord.standardGenerator I v) = 1 := by
  rw [initialCoeff_def, ord.initialExp_standardGenerator hv, ord.coeff_self_standardGenerator hv]

theorem standardGenerator_ne_zero {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    ord.standardGenerator I v ≠ 0 := by
  rw [← ord.initialCoeff_ne_zero_iff, ord.initialCoeff_standardGenerator hv]
  exact one_ne_zero

theorem isLeast_toSyn_standardGenerator {I : Ideal (MvPowerSeries σ K)} {v : σ →₀ ℕ}
    (hv : v ∈ ord.initialDiagram I) :
    IsLeast (ord.toSyn '' (ord.standardGenerator I v).support) (ord.toSyn v) :=
  ord.isLeast_toSyn_iff.mpr ⟨ord.standardGenerator_ne_zero hv, ord.initialExp_standardGenerator hv⟩

/-- **Bierstone–Milman Corollary 3.19**: the finite set of normalized vertex generators
`ord.standardGenerator I v` for `v ∈ ord.initialDiagramVertices I` generates `I`. -/
theorem span_image_standardGenerator_initialDiagramVertices (I : Ideal (MvPowerSeries σ K)) :
    Ideal.span (ord.standardGenerator I '' (ord.initialDiagramVertices I : Set (σ →₀ ℕ))) = I := by
  let V := ord.initialDiagramVertices I
  let e : Fin V.card ≃ {v // v ∈ V} := (Finset.equivFin V).symm
  have hrange : Set.range (fun i : Fin V.card ↦ ord.standardGenerator I (e i)) =
      ord.standardGenerator I '' (V : Set (σ →₀ ℕ)) := by
    ext f
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨e i, (e i).2, hi⟩, fun ⟨v, hv, hf⟩ ↦ ⟨e.symm ⟨v, hv⟩, by simpa using hf⟩⟩
  rw [← hrange]
  refine ord.span_range_eq_of_initialDiagram_subset (α := fun i ↦ (e i : σ →₀ ℕ))
    (fun i ↦ ord.standardGenerator_mem I (e i))
    (fun i ↦ ord.isLeast_toSyn_standardGenerator (ord.initialDiagramVertices_subset I (e i).2))
    fun γ hγ ↦ ?_
  obtain ⟨v, hvV, hle⟩ := (ord.mem_initialDiagram_iff_exists_mem_initialDiagramVertices_le).mp hγ
  exact ⟨e.symm ⟨v, hvV⟩, by simpa using hle⟩

end Field

end StandardGenerators

end MonomialOrder
