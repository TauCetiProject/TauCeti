/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Sequences
import TauCeti.RingTheory.MvPowerSeries.MaximalIdeal

/-!
# The Hilbert–Samuel function of multivariate power series and lexicographic stabilization

Over a field `K` in finitely many variables `σ`, Hironaka's formal division theorem
(`MonomialOrder.quotientEquivComplementSubmodule`) identifies every quotient
`MvPowerSeries σ K ⧸ (I ⊔ 𝔪 ^ (ℓ + 1))` as a `K`-vector space with the formal power series
supported outside the `degLex`-initial diagram of `I ⊔ 𝔪 ^ (ℓ + 1)`. Because `degLex` compares
total degree first, adjoining `𝔪 ^ (ℓ + 1)` simply adjoins all exponents of degree strictly
greater than `ℓ` (`MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow`). Consequently, the
Hilbert–Samuel function `TauCeti.localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ` counts the
exponents `α ∉ degLex.initialDiagram I` of total degree at most `ℓ`
(`TauCeti.localQuotientHilbertSamuel_mvPowerSeries_eq_degreeLeComplCard`).

For upward-closed subsets `D j ⊆ σ →₀ ℕ` in finitely many variables (`[Finite σ]`), the
bounded-degree complement counts `TauCeti.degreeLeComplCard (D j)` satisfy the descending chain
condition in the lexicographic order on `ℕ → ℕ`: no sequence of upper sets strictly decreases at
every step (`TauCeti.not_forall_toLex_degreeLeComplCard_lt`), and every lexicographically
nonincreasing sequence is eventually constant
(`TauCeti.exists_degreeLeComplCard_stabilizes_of_toLex_le`).
Specializing to `degLex`-initial diagrams yields lexicographic and pointwise stabilization for
Hilbert–Samuel functions realized by ideals in `MvPowerSeries σ K`
(`TauCeti.exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_toLex_le`,
`TauCeti.exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_pointwise`,
`TauCeti.hsLexStabilization`), enabling local finiteness and upper-semicontinuity arguments along
filtrations or blowup sequences of formal ideals.

## Main definitions

* `TauCeti.degreeLeComplFinset`: for `[Finite σ]`, the `Finset` of exponents `α : σ →₀ ℕ` with
  `α.degree ≤ ℓ` and `α ∉ S`.
* `TauCeti.degreeLeComplCard`: the cardinality `(degreeLeComplFinset S ℓ).card`.

## Main results

* `TauCeti.not_forall_toLex_degreeLeComplCard_lt`,
  `TauCeti.exists_degreeLeComplCard_stabilizes_of_toLex_le`: lexicographic descending chain
  condition and stabilization for bounded-degree complement counts of upper sets in `σ →₀ ℕ`.
* `MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow`:
  `degLex.initialDiagram (I ⊔ 𝔪 ^ (ℓ + 1)) = degLex.initialDiagram I ∪ {α | ℓ < α.degree}`.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_eq_degreeLeComplCard`:
  `localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ =`
  `degreeLeComplCard (degLex.initialDiagram I) ℓ`.
* `TauCeti.localHilbertSamuel_mvPowerSeries`,
  `TauCeti.localQuotientHilbertSamuel_powerSeries_span_X_pow`: explicit evaluations for
  `MvPowerSeries σ K` (`(ℓ + card σ).choose (card σ)`) and `K⟦X⟧ ⧸ (X ^ k)` (`min (ℓ + 1) k`).
* `TauCeti.exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_toLex_le`,
  `TauCeti.exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_pointwise`,
  `TauCeti.hsLexStabilization`: lexicographic and pointwise stabilization of realized
  Hilbert–Samuel functions in `MvPowerSeries`.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20, p. 239.
* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), 801–836, Theorem 5.2.1, pp. 820–821.
* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *ℚ-universal desingularization*,
  Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

open scoped MonomialOrder

namespace TauCeti

section DegreeLeCompl

open Filter Topology

open scoped Classical in
/-- For a finite variable type `σ`, the `Finset` of exponents `α : σ →₀ ℕ` of total degree at most
`ℓ` lying outside `S`. -/
noncomputable def degreeLeComplFinset {σ : Type*} [Finite σ] (S : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ := σ) ℓ).toFinset.filter (· ∉ S)

@[simp]
theorem mem_degreeLeComplFinset_iff {σ : Type*} [Finite σ] {S : Set (σ →₀ ℕ)} {ℓ : ℕ}
    {α : σ →₀ ℕ} :
    α ∈ degreeLeComplFinset S ℓ ↔ α.degree ≤ ℓ ∧ α ∉ S := by
  simp [degreeLeComplFinset]

/-- The number of exponents `α : σ →₀ ℕ` of total degree at most `ℓ` lying outside `S`. -/
noncomputable def degreeLeComplCard {σ : Type*} [Finite σ] (S : Set (σ →₀ ℕ)) (ℓ : ℕ) : ℕ :=
  (degreeLeComplFinset S ℓ).card

theorem degreeLeComplCard_def {σ : Type*} [Finite σ] (S : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    degreeLeComplCard S ℓ = (degreeLeComplFinset S ℓ).card :=
  (rfl)

@[simp]
theorem degreeLeComplFinset_univ {σ : Type*} [Finite σ] (ℓ : ℕ) :
    degreeLeComplFinset (Set.univ : Set (σ →₀ ℕ)) ℓ = ∅ := by
  ext α
  simp

@[simp]
theorem degreeLeComplCard_univ {σ : Type*} [Finite σ] (ℓ : ℕ) :
    degreeLeComplCard (Set.univ : Set (σ →₀ ℕ)) ℓ = 0 := by
  rw [degreeLeComplCard_def, degreeLeComplFinset_univ, Finset.card_empty]

/-- In `d = Fintype.card σ` variables, the number of all exponents of total degree at most `ℓ` is
`(ℓ + d).choose d`. -/
@[simp]
theorem degreeLeComplCard_empty {σ : Type*} [Fintype σ] (ℓ : ℕ) :
    degreeLeComplCard (∅ : Set (σ →₀ ℕ)) ℓ =
      (ℓ + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hfin : degreeLeComplFinset (∅ : Set (σ →₀ ℕ)) ℓ =
      (Finset.range (ℓ + 1)).biUnion ((Finset.univ : Finset σ).finsuppAntidiag ·) := by
    ext α
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [degreeLeComplCard_def, hfin, Finset.card_biUnion]
  · simp [Finset.card_finsuppAntidiag_nat_eq_multichoose, Nat.sum_range_multichoose]
  · intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun α hαa hαb ↦ hab ?_
    rw [Finset.mem_finsuppAntidiag] at hαa hαb
    exact hαa.1.symm.trans hαb.1

theorem degreeLeComplCard_anti {σ : Type*} [Finite σ] {S T : Set (σ →₀ ℕ)} (h : S ⊆ T) (ℓ : ℕ) :
    degreeLeComplCard T ℓ ≤ degreeLeComplCard S ℓ := by
  refine Finset.card_le_card fun α hα ↦ ?_
  rw [mem_degreeLeComplFinset_iff] at hα ⊢
  exact ⟨hα.1, fun hαS ↦ hα.2 (h hαS)⟩

theorem degreeLeComplCard_mono {σ : Type*} [Finite σ] (S : Set (σ →₀ ℕ)) :
    Monotone (degreeLeComplCard S) := by
  intro m n hmn
  refine Finset.card_le_card fun α hα ↦ ?_
  rw [mem_degreeLeComplFinset_iff] at hα ⊢
  exact ⟨hα.1.trans hmn, hα.2⟩

/-- Pointwise convergence of `D (φ m)` to `D_lim` implies eventual equality of
`degreeLeComplCard` uniformly up to any finite degree bound `B`. -/
private theorem eventually_degreeLeComplCard_eq {σ : Type*} [Finite σ]
    {D : ℕ → Set (σ →₀ ℕ)} {D_lim : Set (σ →₀ ℕ)} {φ : ℕ → ℕ}
    (hev : ∀ α, ∀ᶠ m in atTop, α ∈ D (φ m) ↔ α ∈ D_lim) (B : ℕ) :
    ∀ᶠ m in atTop, ∀ ℓ ≤ B, degreeLeComplCard (D (φ m)) ℓ = degreeLeComplCard D_lim ℓ := by
  let F : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) B).toFinset
  filter_upwards [(eventually_all_finset F).mpr fun α _ ↦ hev α] with m hm ℓ hℓ
  refine congrArg Finset.card (Finset.ext fun α ↦ ?_)
  rw [mem_degreeLeComplFinset_iff, mem_degreeLeComplFinset_iff]
  refine and_congr_right fun hdeg ↦ not_congr (hm α ?_)
  exact (Set.Finite.mem_toFinset _).mpr (hdeg.trans hℓ)

/-- **Lexicographic descending chain condition for upper-set complement counts**
(Bierstone–Milman 1989, Theorem 5.2.1): for finitely many variables `σ`, there is no infinite
sequence of upper sets `D j ⊆ σ →₀ ℕ` whose bounded-degree complement counts strictly decrease at
every step in the lexicographic order on `ℕ → ℕ`. -/
theorem not_forall_toLex_degreeLeComplCard_lt {σ : Type*} [Finite σ]
    {D : ℕ → Set (σ →₀ ℕ)} (hD : ∀ j, IsUpperSet (D j)) :
    ¬ ∀ j, toLex (degreeLeComplCard (D (j + 1))) < toLex (degreeLeComplCard (D j)) := by
  classical
  intro hlt
  have hanti : StrictAnti (fun j ↦ toLex (degreeLeComplCard (D j))) :=
    strictAnti_nat_of_succ_lt hlt
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq fun j α ↦ decide (α ∈ D j)
  let D_lim : Set (σ →₀ ℕ) := {α | a α = true}
  have hev (α : σ →₀ ℕ) : ∀ᶠ m in atTop, α ∈ D (φ m) ↔ α ∈ D_lim := by
    have hα := tendsto_pi_nhds.mp hlim α
    rw [nhds_discrete, tendsto_pure] at hα
    filter_upwards [hα] with m hm
    simpa [D_lim] using congrArg (· = true) hm
  let V : Finset (σ →₀ ℕ) :=
    (WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (· ∈ D_lim))).toFinset
  have hsub : ∀ᶠ m in atTop, D_lim ⊆ D (φ m) := by
    filter_upwards [(eventually_all_finset V).mpr fun v _ ↦ hev v] with m hm γ hγ
    obtain ⟨v, hvle, hvmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D_lim) γ hγ
    exact hD (φ m) hvle ((hm v ((Set.Finite.mem_toFinset _).mpr hvmin)).mpr hvmin.prop)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hsub
  have hle_lim : toLex (degreeLeComplCard (D (φ M₀))) ≤ toLex (degreeLeComplCard D_lim) :=
    Pi.toLex_monotone (degreeLeComplCard_anti (hM₀ M₀ le_rfl))
  have hlt_lim : toLex (degreeLeComplCard (D (φ (M₀ + 1)))) < toLex (degreeLeComplCard D_lim) :=
    (hanti (hφ (Nat.lt_succ_self M₀))).trans_le hle_lim
  obtain ⟨ℓ₀, hpre, hlt₀⟩ := hlt_lim
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp (eventually_degreeLeComplCard_eq hev ℓ₀)
  let m := max (M₀ + 1) M₁
  have heq : ∀ ℓ ≤ ℓ₀, degreeLeComplCard (D (φ m)) ℓ = degreeLeComplCard D_lim ℓ :=
    hM₁ m (le_max_right _ _)
  have hgt : toLex (degreeLeComplCard (D (φ (M₀ + 1)))) <
      toLex (degreeLeComplCard (D (φ m))) :=
    ⟨ℓ₀, fun ℓ hℓ ↦ (hpre ℓ hℓ).trans (heq ℓ hℓ.le).symm, hlt₀.trans_eq (heq ℓ₀ le_rfl).symm⟩
  exact hgt.not_ge (hanti.antitone (hφ.monotone (le_max_left _ _)))

/-- Every lexicographically nonincreasing sequence of bounded-degree complement counts of upper
sets in `σ →₀ ℕ` (`Finite σ`) is eventually constant. -/
theorem exists_degreeLeComplCard_stabilizes_of_toLex_le {σ : Type*} [Finite σ]
    {D : ℕ → Set (σ →₀ ℕ)} (hD : ∀ j, IsUpperSet (D j))
    (hlex : ∀ j, toLex (degreeLeComplCard (D (j + 1))) ≤ toLex (degreeLeComplCard (D j))) :
    ∃ j₀, ∀ j, j₀ ≤ j → degreeLeComplCard (D j) = degreeLeComplCard (D j₀) := by
  have hanti : Antitone (fun j ↦ toLex (degreeLeComplCard (D j))) :=
    antitone_nat_of_succ_le hlex
  by_contra! hnostab
  choose next hge hne using hnostab
  let ψ : ℕ → ℕ := fun k ↦ Nat.rec 0 (fun _ m ↦ next m) k
  refine not_forall_toLex_degreeLeComplCard_lt (D := fun k ↦ D (ψ k)) (fun k ↦ hD (ψ k)) fun k ↦ ?_
  exact lt_of_le_of_ne (hanti (hge (ψ k))) (toLex.injective.ne (hne (ψ k)))

end DegreeLeCompl

end TauCeti

namespace MonomialOrder

/-- Over a field `K` (with arbitrary ordered variable type `σ`), the `degLex`-initial diagram of
`I ⊔ 𝔪 ^ (ℓ + 1)` is obtained from `degLex.initialDiagram I` by adjoining all exponents of total
degree strictly greater than `ℓ`. -/
theorem initialDiagram_degLex_sup_maximalIdeal_pow {σ K : Type*} [Field K] [LinearOrder σ]
    [WellFoundedGT σ] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    degLex.initialDiagram (I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ (ℓ + 1)) =
      degLex.initialDiagram I ∪ {α : σ →₀ ℕ | ℓ < α.degree} := by
  ext α
  refine ⟨fun hα ↦ ?_, fun hα ↦ ?_⟩
  · obtain ⟨f, hf, hf0, rfl⟩ := degLex.mem_initialDiagram_iff.mp hα
    by_cases hdeg : ℓ < (degLex.initialExp f).degree
    · exact Or.inr hdeg
    obtain ⟨g, hgI, h, hh𝔪, rfl⟩ := Submodule.mem_sup.mp hf
    have hh0 {β : σ →₀ ℕ} (hβ : β ≼[degLex] degLex.initialExp (g + h)) :
        MvPowerSeries.coeff β h = 0 := by
      have hβdeg : β.degree ≤ (degLex.initialExp (g + h)).degree := by
        by_contra! hgt
        exact hβ.not_gt (by rw [degLex_lt_iff, Finsupp.DegLex.lt_iff]; exact Or.inl hgt)
      refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_
        (MvPowerSeries.le_order_of_mem_maximalIdeal_pow (ℓ + 1) hh𝔪))
      exact_mod_cast (by omega : β.degree < ℓ + 1)
    have hg_coeff : MvPowerSeries.coeff (degLex.initialExp (g + h)) g ≠ 0 := by
      have hc := degLex.coeff_initialExp_ne_zero hf0
      rwa [map_add, hh0 le_rfl, add_zero] at hc
    have hg0 : g ≠ 0 := fun h0 ↦ hg_coeff (by simp [h0])
    refine Or.inl (degLex.mem_initialDiagram_iff.mpr
      ⟨g, hgI, hg0, degLex.initialExp_eq_of_coeff_ne_zero_of_forall_lt hg_coeff ?_⟩)
    intro β hβ
    have hsum0 := degLex.coeff_eq_zero_of_lt_initialExp hβ
    rwa [map_add, hh0 hβ.le, add_zero] at hsum0
  · rcases hα with hαI | hdeg
    · exact degLex.initialDiagram_mono le_sup_left hαI
    · refine degLex.mem_initialDiagram_iff.mpr ⟨MvPowerSeries.monomial α 1,
        Ideal.mem_sup_right (MvPowerSeries.monomial_mem_maximalIdeal_pow_of_le_degree hdeg 1), ?_,
        degLex.initialExp_monomial_of_ne_zero α one_ne_zero⟩
      intro h0
      simpa using congrArg (MvPowerSeries.coeff α) h0

end MonomialOrder

namespace TauCeti

section MvPowerSeriesHilbertSamuel

private theorem mem_complementSubmodule_degLex_sup_iff {σ K : Type*} [Field K] [Finite σ]
    [LinearOrder σ] {I : Ideal (MvPowerSeries σ K)} {ℓ : ℕ} {f : MvPowerSeries σ K} :
    f ∈ MonomialOrder.degLex.complementSubmodule
        (I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ (ℓ + 1)) ↔
      ∀ β ∈ f.support, β ∈ degreeLeComplFinset (MonomialOrder.degLex.initialDiagram I) ℓ := by
  refine MonomialOrder.degLex.mem_complementSubmodule_iff.trans (forall₂_congr fun β _ ↦ ?_)
  simp [MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow, and_comm]

/-- Evaluating coefficients on `degreeLeComplFinset (degLex.initialDiagram I) ℓ` identifies the
formal-division complement submodule of `I ⊔ 𝔪 ^ (ℓ + 1)` with the finite-dimensional `K`-vector
space `degreeLeComplFinset (degLex.initialDiagram I) ℓ → K`. -/
private noncomputable def complementSubmoduleDegLexSupEquiv {σ K : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    MonomialOrder.degLex.complementSubmodule
      (I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ (ℓ + 1)) ≃ₗ[K]
      (degreeLeComplFinset (MonomialOrder.degLex.initialDiagram I) ℓ → K) where
  toFun f α := MvPowerSeries.coeff α.1 f.1
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ map_smul _ _ _
  invFun c := ⟨∑ α : degreeLeComplFinset (MonomialOrder.degLex.initialDiagram I) ℓ,
      MvPowerSeries.monomial α.1 (c α),
    sum_mem fun α _ ↦ MonomialOrder.degLex.monomial_mem_complementSubmodule_iff.mpr <| Or.inr <| by
      have hα := mem_degreeLeComplFinset_iff.mp α.2
      simp [MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow, hα.1, hα.2]⟩
  left_inv f := Subtype.ext <| MvPowerSeries.ext fun β ↦ by
    rw [map_sum]
    by_cases hβ : β ∈ degreeLeComplFinset (MonomialOrder.degLex.initialDiagram I) ℓ
    · rw [Finset.sum_eq_single ⟨β, hβ⟩, MvPowerSeries.coeff_monomial_same]
      · rintro α _ hne
        exact MvPowerSeries.coeff_monomial_ne (Subtype.ext_iff.not.mp hne.symm) _
      · intro hm
        exact absurd (Finset.mem_univ _) hm
    · rw [Finset.sum_eq_zero]
      · symm
        by_contra hne
        exact hβ (mem_complementSubmodule_degLex_sup_iff.mp f.2 β
          (MvPowerSeries.mem_support.mpr hne))
      · rintro α _
        refine MvPowerSeries.coeff_monomial_ne (fun h ↦ hβ ?_) _
        rw [h]
        exact α.2
  right_inv c := funext fun α ↦ by
    dsimp only
    rw [map_sum, Finset.sum_eq_single α, MvPowerSeries.coeff_monomial_same]
    · rintro β _ hne
      exact MvPowerSeries.coeff_monomial_ne (Subtype.ext_iff.not.mp hne.symm) _
    · intro hm
      exact absurd (Finset.mem_univ _) hm

/-- **Bierstone–Milman Corollary 3.20**: over a field `K` in finitely many variables `σ`, the
Hilbert–Samuel function `localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ` equals the number of
exponents `α ∉ degLex.initialDiagram I` of total degree at most `ℓ`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_eq_degreeLeComplCard {σ K : Type*} [Field K]
    [Finite σ] [LinearOrder σ] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ =
      (degreeLeComplCard (MonomialOrder.degLex.initialDiagram I) ℓ : ℕ∞) := by
  rw [localQuotientHilbertSamuel_def, MvPowerSeries.length_eq_length (R := K),
    (MonomialOrder.degLex.quotientEquivComplementSubmodule _).length_eq,
    (complementSubmoduleDegLexSupEquiv I ℓ).length_eq, Module.length_pi_of_fintype]
  simp [degreeLeComplCard_def]

/-- Over a field `K` in `d = Fintype.card σ` variables, the Hilbert–Samuel function of
`MvPowerSeries σ K` at order `ℓ` is `(ℓ + d).choose d`. -/
@[simp]
theorem localHilbertSamuel_mvPowerSeries (σ K : Type*) [Field K] [Fintype σ] (ℓ : ℕ) :
    localHilbertSamuel (MvPowerSeries σ K) ℓ =
      ((ℓ + Fintype.card σ).choose (Fintype.card σ) : ℕ∞) := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  rw [localHilbertSamuel_def, localQuotientHilbertSamuel_mvPowerSeries_eq_degreeLeComplCard,
    MonomialOrder.initialDiagram_bot, degreeLeComplCard_empty]

/-- Over a field `K`, the Hilbert–Samuel function of `K⟦X⟧ ⧸ (X ^ k)` at order `ℓ` is
`min (ℓ + 1) k` (in particular, for `k = 2`, `1` at `ℓ = 0` and `2` for `ℓ ≥ 1`). -/
theorem localQuotientHilbertSamuel_powerSeries_span_X_pow (K : Type*) [Field K] (k ℓ : ℕ) :
    localQuotientHilbertSamuel (PowerSeries K) (Ideal.span {PowerSeries.X ^ k}) ℓ =
      (min (ℓ + 1) k : ℕ∞) := by
  have hspan : (Ideal.span {PowerSeries.X ^ k} : Ideal (MvPowerSeries Unit K)) =
      Ideal.span ((fun α ↦ MvPowerSeries.monomial α (1 : K)) '' {Finsupp.single () k}) := by
    rw [Set.image_singleton, ← MvPowerSeries.X_pow_eq, PowerSeries.X_apply]
  rw [show localQuotientHilbertSamuel (PowerSeries K) (Ideal.span {PowerSeries.X ^ k}) ℓ =
    localQuotientHilbertSamuel (MvPowerSeries Unit K) (Ideal.span {PowerSeries.X ^ k}) ℓ from rfl,
    localQuotientHilbertSamuel_mvPowerSeries_eq_degreeLeComplCard, hspan,
    MonomialOrder.initialDiagram_span_monomial, Set.biUnion_singleton, degreeLeComplCard_def]
  have hcard : (degreeLeComplFinset (Set.Ici (Finsupp.single () k)) ℓ).card =
      (Finset.range (min (ℓ + 1) k)).card := by
    refine Finset.card_bij (fun α _ ↦ α ()) (fun α hα ↦ ?_)
      (fun α₁ _ α₂ _ h ↦ Finsupp.ext fun ⟨⟩ ↦ h)
      fun m hm ↦ ⟨Finsupp.single () m, ?_, by simp⟩
    · rw [mem_degreeLeComplFinset_iff, Set.mem_Ici, Finsupp.single_le_iff, Finsupp.degree_eq_sum,
        Finset.univ_unique, Finset.sum_singleton] at hα
      change α () ≤ ℓ ∧ ¬ k ≤ α () at hα
      rw [Finset.mem_range, lt_min_iff]
      omega
    · rw [Finset.mem_range, lt_min_iff] at hm
      rw [mem_degreeLeComplFinset_iff, Set.mem_Ici, Finsupp.single_le_iff, Finsupp.degree_single,
        Finsupp.single_eq_same]
      omega
  rw [hcard, Finset.card_range]
  rcases le_total (ℓ + 1) k with hle | hle
  · rw [min_eq_left hle, Nat.cast_add, Nat.cast_one, min_eq_left (by exact_mod_cast hle)]
  · rw [min_eq_right hle, min_eq_right (by exact_mod_cast hle)]

/-- **Lexicographic stabilization of realized Hilbert–Samuel functions**
(Bierstone–Milman 1989, Theorem 5.2.1; Bierstone–Milman–Temkin 2011, §6.1): for a field `K` and a
finite variable type `σ`, every lexicographically nonincreasing sequence of Hilbert–Samuel
functions realized by ideals `I j` of `MvPowerSeries σ K` is eventually constant. -/
theorem exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_toLex_le {σ K : Type*}
    [Field K] [Finite σ] (I : ℕ → Ideal (MvPowerSeries σ K))
    (hlex : ∀ j,
      toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1))) ≤
        toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) := by
  cases nonempty_fintype σ
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let D : ℕ → Set (σ →₀ ℕ) := fun j ↦ MonomialOrder.degLex.initialDiagram (I j)
  have hH (j ℓ : ℕ) : localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) ℓ =
      (degreeLeComplCard (D j) ℓ : ℕ∞) :=
    localQuotientHilbertSamuel_mvPowerSeries_eq_degreeLeComplCard (I j) ℓ
  have hlexD (j : ℕ) : toLex (degreeLeComplCard (D (j + 1))) ≤
      toLex (degreeLeComplCard (D j)) := by
    by_contra! hgt
    obtain ⟨ℓ₀, hpre, hlt₀⟩ := hgt
    have hgtH : toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j)) <
        toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1))) := by
      refine ⟨ℓ₀, fun ℓ hℓ ↦ ?_, ?_⟩
      · change localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) ℓ =
          localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1)) ℓ
        rw [hH, hH]
        exact congrArg Nat.cast (hpre ℓ hℓ)
      · change localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) ℓ₀ <
          localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1)) ℓ₀
        rw [hH, hH, Nat.cast_lt]
        exact hlt₀
    exact hgtH.not_ge (hlex j)
  obtain ⟨j₀, hj₀⟩ := exists_degreeLeComplCard_stabilizes_of_toLex_le
    (fun j ↦ MonomialOrder.degLex.isUpperSet_initialDiagram (I j)) hlexD
  refine ⟨j₀, fun j hj ↦ funext fun ℓ ↦ ?_⟩
  rw [hH, hH, hj₀ j hj]

/-- No sequence of ideals in `MvPowerSeries σ K` (`Field K`, `Finite σ`) has strictly
lexicographically decreasing Hilbert–Samuel functions at every step. -/
theorem not_forall_toLex_localQuotientHilbertSamuel_mvPowerSeries_lt {σ K : Type*} [Field K]
    [Finite σ] (I : ℕ → Ideal (MvPowerSeries σ K)) :
    ¬ ∀ j,
      toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1))) <
        toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j)) := by
  intro hlt
  obtain ⟨j₀, hj₀⟩ := exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_toLex_le I
    fun j ↦ (hlt j).le
  exact (hlt j₀).ne (congrArg toLex (hj₀ (j₀ + 1) (Nat.le_succ j₀)))

/-- **Pointwise Hilbert–Samuel stabilization** (Bierstone–Milman 1989, Theorem 5.2.1): if
`localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1)) ℓ ≤
localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) ℓ` for every `j` and `ℓ`, then the sequence of
Hilbert–Samuel functions is eventually constant. -/
theorem exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_pointwise {σ K : Type*}
    [Field K] [Finite σ] (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : ∀ j ℓ,
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1)) ℓ ≤
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) ℓ) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) :=
  exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_toLex_le I
    fun j ↦ Pi.toLex_monotone (h j)

/-- **Lexicographic stabilization of realized Hilbert–Samuel functions** in
`MvPowerSeries (Fin n) K` (Bierstone–Milman 1989, Theorem 5.2.1;
Bierstone–Milman–Temkin 2011, §6.1). -/
theorem hsLexStabilization (K : Type*) [Field K] (n : ℕ)
    (I : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) := by
  refine exists_localQuotientHilbertSamuel_mvPowerSeries_stabilizes_of_toLex_le I fun j ↦ ?_
  rcases h j with heq | hlt
  · exact (congrArg toLex heq).le
  · exact le_of_lt hlt

end MvPowerSeriesHilbertSamuel

end TauCeti
