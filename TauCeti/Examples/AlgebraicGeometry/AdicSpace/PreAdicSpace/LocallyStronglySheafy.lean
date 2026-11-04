/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Adic
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyStronglySheafy
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.PadicInt
import TauCeti.RingTheory.Huber.Padic.TateAlgebra
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Tests for analytic, locally noetherian analytic, and locally strongly sheafy adic spaces

Concrete checks for `TauCeti.AdicSpace.IsAnalytic`, `TauCeti.AdicSpace.IsLocallyNoetherianAnalytic`
and `TauCeti.AdicSpace.IsLocallyStronglySheafy`:

* `Spa(ℚ_[p], S.plus)` and `Spa(ℚ_p⟨X₁, …, Xₘ⟩, S.plus)` are nonempty, locally noetherian analytic,
  locally strongly sheafy, and analytic, and every morphism into `Spa(ℚ_[p], S.plus)` is adic;
* `(ℚ_[p], ℚ_[p])` is not a Huber pair (`¬ IsRingOfIntegralElements ⊤`) and has empty adic spectrum,
  even though `ℚ_[p]` is strongly sheafy;
* open immersions preserve `IsLocallyNoetherianAnalytic` on both sides of the bridge;
* the empty adic space (constructed unconditionally as `Spa(0, 0)`) satisfies all four space-level
  predicates;
* `Spa(ℤ_[p], ℤ_[p])` is locally noetherian but not analytic, hence not locally noetherian analytic,
  whereas its analytic locus is locally noetherian analytic and locally strongly sheafy.
-/

open CategoryTheory TopologicalSpace IsLocalRing

namespace TauCeti.ValuationSpectrum

open Huber PreAdicSpace AdicSpace

section PadicField

variable (p : ℕ) [Fact p.Prime]

/-- *Huber.test_field_plus_unbounded_positive*: `ℚ_[p]` and `ℚ_p⟨X⟩` are strongly sheafy, and for
every Huber pair `S` on `ℚ_[p]` the adic spectrum `spa S.plus` is nonempty. -/
example (S : Pair ℚ_[p]) :
    IsStronglySheafy ℚ_[p] ∧
      IsStronglySheafy (restrictedMvPowerSeriesCompletion 1 ℚ_[p]) ∧
      (spa S.plus).Nonempty := by
  refine ⟨.of_isStronglyNoetherian,
    (IsStronglySheafy.of_isStronglyNoetherian (A := ℚ_[p])).restrictedMvPowerSeriesCompletion 1,
    Set.nonempty_iff_ne_empty.mpr ?_⟩
  rw [Ne, spa_eq_empty_iff_subsingleton S.plus S.isRingOfIntegralElements]
  exact not_subsingleton ℚ_[p]

/-- *Huber.test_field_plus_unbounded_negative*: `ℚ_[p]` is strongly sheafy, yet `⊤ : Subring ℚ_[p]`
is not a ring of integral elements (`p⁻¹` is not power-bounded) and `spa (⊤ : Subring ℚ_[p]) = ∅`.
-/
example : IsStronglySheafy ℚ_[p] ∧ ¬ IsRingOfIntegralElements (⊤ : Subring ℚ_[p]) ∧
    spa (⊤ : Subring ℚ_[p]) = ∅ := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  have hpinv : ¬ IsPowerBounded ((p : ℚ_[p])⁻¹) := by
    rw [isPowerBounded_iff_norm_le_one, norm_inv, not_le]
    exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hp0, _root_.Padic.norm_p_lt_one⟩
  refine ⟨.of_isStronglyNoetherian, fun h ↦ hpinv (h.isPowerBounded_of_mem trivial), ?_⟩
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  have h2 := valuation_le_one_of_mem_spa hv (a := (p : ℚ_[p])⁻¹) trivial
  have hlt :=
    ((isContinuous_def v).mp ((mem_spa_iff _ v).mp hv).1).lt_one_of_isTopologicallyNilpotent
      (Padic.isPseudoUniformizer_p (p := p)).isTopologicallyNilpotent
  have hle := mul_le_mul_of_nonneg_left h2 (zero_le : 0 ≤ v.valuation (p : ℚ_[p]))
  rw [← map_mul, mul_inv_cancel₀ hp0, map_one, mul_one] at hle
  exact hlt.not_ge hle

/-- *locallyNoetherianAnalytic_padic*: `Spa(ℚ_[p], ℚ_[p]°)` is nonempty, locally noetherian
analytic, locally strongly sheafy, and analytic, with `IsLocallyNoetherian` and `IsAnalytic`
recovered via `isLocallyNoetherianAnalytic_iff` and `analyticLocus.ι` an isomorphism, and every
morphism into `Spa(ℚ_[p], ℚ_[p]°)` is adic (`IsAdic.of_isAnalytic`). -/
example (Y : AdicSpace.{0}) :
    let hP : (Padic.pairOfDefinition (p := p)).ringOfDefinition ≤ (Pair.powerBounded ℚ_[p]).plus :=
      by rw [Pair.powerBounded_plus]; exact (Padic.pairOfDefinition (p := p)).le_powerBoundedSubring
    let X : AdicSpace.{0} :=
      ⟨presentationLimitPreAdicSpace (Padic.pairOfDefinition (p := p))
          (Pair.powerBounded ℚ_[p]).plus
          (Pair.powerBounded ℚ_[p]).isRingOfIntegralElements.isPowerBounded_of_mem hP,
        isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian
          (Padic.pairOfDefinition (p := p)) hP
          (Pair.powerBounded ℚ_[p]).isRingOfIntegralElements.isPowerBounded_of_mem⟩
    Nonempty X.obj ∧ X.IsLocallyNoetherianAnalytic ∧ X.IsLocallyNoetherian ∧ X.IsAnalytic ∧
      X.IsLocallyStronglySheafy ∧ IsIso (AdicSpace.analyticLocus.ι X) ∧
      ∀ f : Y ⟶ X, AdicSpace.IsAdic f := by
  intro hP X
  have hLNA : X.IsLocallyNoetherianAnalytic :=
    IsLocallyNoetherianAnalytic.spa (Padic.pairOfDefinition (p := p))
      (Pair.powerBounded ℚ_[p]).plus
      (Pair.powerBounded ℚ_[p]).isRingOfIntegralElements.isPowerBounded_of_mem hP
  have hne : (spa (Pair.powerBounded ℚ_[p]).plus).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, Ne,
      spa_eq_empty_iff_subsingleton _ (Pair.powerBounded ℚ_[p]).isRingOfIntegralElements]
    exact not_subsingleton ℚ_[p]
  exact ⟨hne.to_subtype, hLNA, (isLocallyNoetherianAnalytic_iff.mp hLNA).1,
    (isLocallyNoetherianAnalytic_iff.mp hLNA).2, hLNA.isLocallyStronglySheafy,
    (AdicSpace.isIso_analyticLocus_ι_iff _).mpr hLNA.isAnalytic,
    fun f ↦ AdicSpace.IsAdic.of_isAnalytic f hLNA.isAnalytic⟩

/-- *test_field*: for every Huber pair `S` on `ℚ_[p]` and compatible pair of definition `P`,
`Spa(ℚ_[p], S.plus)` is locally strongly sheafy. -/
example (S : Pair ℚ_[p]) (P : PairOfDefinition ℚ_[p]) (hP : P.ringOfDefinition ≤ S.plus) :
    IsLocallyStronglySheafy ⟨presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP,
      isAdic_presentationLimitPreAdicSpace_of_isSheafyRing P S.isRingOfIntegralElements hP
        IsStronglySheafy.of_isStronglyNoetherian.isSheafyRing⟩ :=
  IsLocallyStronglySheafy.spa .of_isStronglyNoetherian S P hP

/-- *test_tateAlgebra*: for every `m : ℕ` and Huber pair `S` on `ℚ_p⟨X₁, …, Xₘ⟩` with compatible
pair of definition `P`, `Spa(ℚ_p⟨X₁, …, Xₘ⟩, S.plus)` is locally noetherian analytic and locally
strongly sheafy. -/
example (m : ℕ) (S : Pair (restrictedMvPowerSeriesCompletion m ℚ_[p]))
    (P : PairOfDefinition (restrictedMvPowerSeriesCompletion m ℚ_[p]))
    (hP : P.ringOfDefinition ≤ S.plus) :
    let X : AdicSpace.{0} := ⟨presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP,
      isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian P hP
        S.isRingOfIntegralElements.isPowerBounded_of_mem⟩
    X.IsLocallyNoetherianAnalytic ∧ X.IsLocallyStronglySheafy := by
  intro X
  have hX : X.IsLocallyNoetherianAnalytic :=
    IsLocallyNoetherianAnalytic.spa P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP
  exact ⟨hX, hX.isLocallyStronglySheafy⟩

end PadicField

/-! ### Open subspaces and the empty adic space -/

section RestrictAndEmpty

/-- *locallyNoetherianAnalytic_restrict*: an open subspace of a locally noetherian analytic adic
space is locally noetherian analytic, on both sides of `isLocallyNoetherianAnalytic_iff`. -/
example {X Y : AdicSpace.{0}} (f : Y ⟶ X) [PreAdicSpace.IsOpenImmersion f.hom]
    (hX : X.IsLocallyNoetherianAnalytic) :
    Y.IsLocallyNoetherianAnalytic ∧ (Y.IsLocallyNoetherian ∧ Y.IsAnalytic) := by
  have hY := hX.of_isOpenImmersion f
  exact ⟨hY, isLocallyNoetherianAnalytic_iff.mp hY⟩

/-- *locallyNoetherianAnalytic_empty*: the adic spectrum of the zero ring `PUnit` is an
unconditional empty adic space satisfying `IsLocallyNoetherianAnalytic`, `IsLocallyNoetherian`,
`IsAnalytic`, and `IsLocallyStronglySheafy`. -/
example : ∃ X : AdicSpace.{0}, IsEmpty X.obj ∧ X.IsLocallyNoetherianAnalytic ∧
    X.IsLocallyNoetherian ∧ X.IsAnalytic ∧ X.IsLocallyStronglySheafy := by
  have hpu : IsPseudoUniformizer (0 : PUnit) :=
    isPseudoUniformizer_iff.mpr ⟨Subsingleton.elim (0 : PUnit) 1 ▸ isUnit_one, .zero⟩
  let _ : IsTateRing PUnit :=
    have _ : IsHuberRing PUnit := inferInstance
    ⟨⟨0, hpu⟩⟩
  have _ : IsStronglyNoetherian PUnit := IsNoetherianType.isStronglyNoetherian
  let P : PairOfDefinition PUnit :=
    { ringOfDefinition := ⊤
      isOpen_ringOfDefinition := isOpen_discrete _
      idealOfDefinition := ⊥
      fg_idealOfDefinition := Submodule.fg_bot
      isAdic_idealOfDefinition := is_bot_adic_iff.mpr inferInstance }
  have hP : P.ringOfDefinition ≤ (Pair.discrete PUnit).plus := by simp
  let X : AdicSpace.{0} :=
    ⟨presentationLimitPreAdicSpace P (Pair.discrete PUnit).plus
        (Pair.discrete PUnit).isRingOfIntegralElements.isPowerBounded_of_mem hP,
      isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian P hP
        (Pair.discrete PUnit).isRingOfIntegralElements.isPowerBounded_of_mem⟩
  have hempty : IsEmpty X.obj := by
    have hspa : spa (Pair.discrete PUnit).plus = ∅ :=
      (spa_eq_empty_iff_subsingleton _ (Pair.discrete PUnit).isRingOfIntegralElements).mpr
        inferInstance
    exact Set.isEmpty_coe_sort.mpr hspa
  exact ⟨X, hempty, isLocallyNoetherianAnalytic_of_isEmpty X,
    (isLocallyNoetherianAnalytic_of_isEmpty X).isLocallyNoetherian,
    isAnalytic_of_isEmpty X, isLocallyStronglySheafy_of_isEmpty X⟩

end RestrictAndEmpty

/-! ### Non-analytic locally noetherian control: `Spa(ℤ_p, ℤ_p)` -/

section PadicIntControl

variable (p : ℕ) [Fact p.Prime]

/-- *locallyNoetherianAnalytic_padicInt*: `Spa(ℤ_[p], ℤ_[p])` is locally noetherian (`ℤ_[p]` is its
own noetherian ring of definition), but its closed point `trivialSection ⊤` is not analytic, so
`Spa(ℤ_[p], ℤ_[p])` is neither analytic nor locally noetherian analytic, whereas its analytic locus
is both locally noetherian analytic and locally strongly sheafy. -/
example
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (⊤ : Subring ℤ_[p])))
      (presentationLimitPresheaf
        (PairOfDefinition.adic (maximalIdeal ℤ_[p]) PadicInt.isAdic_maximalIdeal
          (by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _))
        (⊤ : Subring ℤ_[p]))) :
    let P := PairOfDefinition.adic (maximalIdeal ℤ_[p]) PadicInt.isAdic_maximalIdeal
      (by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _)
    let hpb : ∀ ⦃a : ℤ_[p]⦄, a ∈ (⊤ : Subring ℤ_[p]) → IsPowerBounded a :=
      fun a _ ↦ IsPowerBounded.of_norm_le_one (_root_.PadicInt.norm_le_one a)
    let X : AdicSpace.{0} :=
      ⟨presentationLimitPreAdicSpace P ⊤ hpb le_top,
        isAdic_presentationLimitPreAdicSpace P ⊤ hpb le_top hs⟩
    X.IsLocallyNoetherian ∧ ¬ X.IsAnalytic ∧ ¬ X.IsLocallyNoetherianAnalytic ∧
      X.analyticLocus.IsLocallyNoetherianAnalytic ∧ X.analyticLocus.IsLocallyStronglySheafy := by
  intro P hpb X
  have _ : IsNoetherianType ℤ_[p] := .of_pairOfDefinition P (by
    rw [PairOfDefinition.adic_ringOfDefinition]
    exact isNoetherianRing_of_ringEquiv ℤ_[p] Subring.topEquiv.symm)
  have hLN : X.IsLocallyNoetherian := IsLocallyNoetherian.spa P ⊤ hpb le_top hs
  have hnotAn : ¬ X.IsAnalytic := by
    rw [isAnalytic_spa_iff P ⊤ hpb le_top hs]
    intro heq
    have hmem : trivialSection (⊤ : PrimeSpectrum ℤ_[p]) ∈ spa (⊤ : Subring ℤ_[p]) := by
      rw [spa_padicInt]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [← heq, spaAnalytic_padicInt, Set.mem_singleton_iff] at hmem
    exact TauCeti.IsDiscreteValuationRing.ofValuation_intValuation_ne_trivialSection_top hmem.symm
  exact ⟨hLN, hnotAn, fun h ↦ hnotAn h.isAnalytic,
    hLN.isLocallyNoetherianAnalytic_analyticLocus,
    hLN.isLocallyNoetherianAnalytic_analyticLocus.isLocallyStronglySheafy⟩

end PadicIntControl

end TauCeti.ValuationSpectrum
