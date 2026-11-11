/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup

/-!
# Negative simple roots in the represented Lie-type groups

`ValidLieTypeIndex.negativeSimpleRootSubgroup` supplies the negative counterpart of
`ValidLieTypeIndex.simpleRootSubgroup` on every represented ambient group. Both use the same
Bourbaki node numbering and additive parameter field. In particular, the Suzuki branch uses
exactly the same B₂-to-C₂ node adapter as its positive counterpart. The branch equations identify
the maps with the lowering root maps of the existing spin, symplectic, minuscule, tripled,
short-root, and Geck carriers.

The uniform Frobenius equation holds on these negative root maps as well as on the positive
ones. These maps provide the other half of the pinning needed to compare represented models;
no identification with a canonical group, or generation of the ambient point group, is asserted.

The dispatch follows `ValidLieTypeIndex.AmbientGroup` and the positive-root assembly in
`Assembly.AmbientGroup`. The root maps and their Frobenius equations are those of the native
carriers, without a new root enumeration or a new validity predicate.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.ValidLieTypeIndex

noncomputable section

/-- The negative simple root map at a Bourbaki-numbered node of a valid Lie-type index.
Its parameter is additive, just as for `simpleRootSubgroup`; negating that parameter in the
positive root map would instead remain in the positive root subgroup. -/
def negativeSimpleRootSubgroup :
    (d : ValidLieTypeIndex) → Fin d.rank → Multiplicative d.Closure →* d.AmbientGroup
  | ⟨.A _ _, _⟩, i | ⟨.twistedA _ _, _⟩, i =>
      SlStd.rootSubgroupPoints _ (.inr i) _
  | ⟨.B _ _, hv⟩, i =>
      let d : TypeBLieIndex := ⟨⟨_, hv⟩, trivial⟩
      TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inr (d.carrierNode i)) _
  | ⟨.C _ _, hv⟩, i =>
      let d : TypeCLieIndex := ⟨⟨_, hv⟩, trivial⟩
      SpStd.rootSubgroupPoints d.carrierRank (.inr (d.carrierNode i)) _
  | ⟨.D _ _, hv⟩, i | ⟨.twistedD _ _, hv⟩, i =>
      let d : TypeDDiagramLieIndex := ⟨⟨_, hv⟩, by simp⟩
      TypeDSpinCarrier.rootSubgroupPoints _ d.four_le_rank (.inr i) _
  | ⟨.E6 _, hv⟩, i =>
      let d : TypeE6LieIndex := ⟨⟨_, hv⟩, by simp⟩
      E6Minuscule.rootSubgroupPoints (.inr (finCongr d.rank_eq_six i)) _
  | ⟨.E7 _, hv⟩, i =>
      let d : TypeE7LieIndex := ⟨⟨_, hv⟩, by simp⟩
      E7Minuscule.rootSubgroupPoints (.inr (finCongr d.rank_eq_seven i)) _
  | ⟨.E8 _, hv⟩, i | ⟨.F4 _, hv⟩, i | ⟨.G2 _, hv⟩, i =>
      DynkinType.geckRootSubgroupPoints _ (ValidLieTypeIndex.dynkinType_valid ⟨_, hv⟩) (.inr i) _
  | ⟨.twistedE6 _, hv⟩, i =>
      let d : TypeTwistedE6LieIndex := ⟨⟨_, hv⟩, by simp⟩
      E6DoubledMinuscule.rootSubgroupPoints (.inr (finCongr d.rank_eq_six i)) _
  | ⟨.trialityD4 _, hv⟩, i =>
      let d : TypeTrialityD4LieIndex := ⟨⟨_, hv⟩, by simp⟩
      D4Tripled.rootSubgroupPoints (.inr (finCongr d.rank_eq_four i)) _
  | ⟨.suzuki m, hv⟩, i =>
      SpStd.rootSubgroupPoints 1 (.inr ((RankTwoBLieIndex.ofSuzuki m hv).carrierNode i)) _
  | ⟨.reeG2 m, hv⟩, i =>
      letI := ReeG2LieIndex.algebraZModThree (ReeG2LieIndex.of m hv)
      G2ShortRoot.PrimeField.rootSubgroupPoints
        (.inr (finCongr (ReeG2LieIndex.of m hv).rank_eq_two i)) (ReeG2LieIndex.of m hv).1.Closure
  | ⟨.reeF4 m, hv⟩, i =>
      letI := ReeF4LieIndex.algebraZModTwo (ReeF4LieIndex.of m hv)
      F4ShortRoot.PrimeField.rootSubgroupPoints
        (.inr (finCongr (ReeF4LieIndex.of m hv).rank_eq_four i)) (ReeF4LieIndex.of m hv).1.Closure
  | ⟨.tits, _⟩, i =>
      letI := TitsLieIndex.algebraZModTwo TitsLieIndex.of
      F4ShortRoot.PrimeField.rootSubgroupPoints
        (.inr (finCongr TitsLieIndex.of.rank_eq_four i)) TitsLieIndex.of.1.Closure

section Branches

variable {n m : ℕ} {q : PrimePower}

/-- On type A, negative simple roots are the standard lowering root maps. -/
theorem negativeSimpleRootSubgroup_A (hv : (LieTypeIndex.A n q).Valid)
    (i : Fin (rank ⟨.A n q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = SlStd.rootSubgroupPoints n (.inr i) _ :=
  (rfl)

/-- The graph-twisted type A family has the same negative root maps as type A. -/
theorem negativeSimpleRootSubgroup_twistedA (hv : (LieTypeIndex.twistedA n q).Valid)
    (i : Fin (rank ⟨.twistedA n q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = SlStd.rootSubgroupPoints n (.inr i) _ :=
  (rfl)

/-- On type B, negative simple roots are those of the full-weight spin carrier. -/
theorem negativeSimpleRootSubgroup_B (hv : (LieTypeIndex.B n q).Valid)
    (i : Fin (rank ⟨.B n q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i =
      TypeBSpinCarrier.rootSubgroupPoints (TypeBLieIndex.carrierRank ⟨⟨_, hv⟩, trivial⟩)
        (.inr (TypeBLieIndex.carrierNode ⟨⟨_, hv⟩, trivial⟩ i)) _ :=
  (rfl)

/-- On type C, negative simple roots are those of the standard symplectic carrier. -/
theorem negativeSimpleRootSubgroup_C (hv : (LieTypeIndex.C n q).Valid)
    (i : Fin (rank ⟨.C n q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i =
      SpStd.rootSubgroupPoints (TypeCLieIndex.carrierRank ⟨⟨_, hv⟩, trivial⟩)
        (.inr (TypeCLieIndex.carrierNode ⟨⟨_, hv⟩, trivial⟩ i)) _ :=
  (rfl)

/-- On type D, negative simple roots are those of the full-weight spin carrier. -/
theorem negativeSimpleRootSubgroup_D (hv : (LieTypeIndex.D n q).Valid)
    (i : Fin (rank ⟨.D n q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = TypeDSpinCarrier.rootSubgroupPoints n
      (TypeDDiagramLieIndex.four_le_rank ⟨⟨_, hv⟩, by simp⟩) (.inr i) _ :=
  (rfl)

/-- The graph-twisted type D family retains the spin carrier's negative root maps. -/
theorem negativeSimpleRootSubgroup_twistedD (hv : (LieTypeIndex.twistedD n q).Valid)
    (i : Fin (rank ⟨.twistedD n q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = TypeDSpinCarrier.rootSubgroupPoints n
      (TypeDDiagramLieIndex.four_le_rank ⟨⟨_, hv⟩, by simp⟩) (.inr i) _ :=
  (rfl)

/-- On E₆, negative simple roots are those of the minuscule carrier. -/
theorem negativeSimpleRootSubgroup_E6 (hv : (LieTypeIndex.E6 q).Valid)
    (i : Fin (rank ⟨.E6 q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = E6Minuscule.rootSubgroupPoints
      (.inr (finCongr (TypeE6LieIndex.rank_eq_six ⟨⟨_, hv⟩, by simp⟩) i)) _ :=
  (rfl)

/-- On E₇, negative simple roots are those of the minuscule carrier. -/
theorem negativeSimpleRootSubgroup_E7 (hv : (LieTypeIndex.E7 q).Valid)
    (i : Fin (rank ⟨.E7 q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = E7Minuscule.rootSubgroupPoints
      (.inr (finCongr (TypeE7LieIndex.rank_eq_seven ⟨⟨_, hv⟩, by simp⟩) i)) _ :=
  (rfl)

/-- On E₈, negative simple roots are those of the Geck carrier. -/
theorem negativeSimpleRootSubgroup_E8 (hv : (LieTypeIndex.E8 q).Valid)
    (i : Fin (rank ⟨.E8 q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = DynkinType.geckRootSubgroupPoints _
      (dynkinType_valid ⟨.E8 q, hv⟩) (.inr i) _ :=
  (rfl)

/-- On F₄, negative simple roots are those of the Geck carrier. -/
theorem negativeSimpleRootSubgroup_F4 (hv : (LieTypeIndex.F4 q).Valid)
    (i : Fin (rank ⟨.F4 q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = DynkinType.geckRootSubgroupPoints _
      (dynkinType_valid ⟨.F4 q, hv⟩) (.inr i) _ :=
  (rfl)

/-- On G₂, negative simple roots are those of the Geck carrier. -/
theorem negativeSimpleRootSubgroup_G2 (hv : (LieTypeIndex.G2 q).Valid)
    (i : Fin (rank ⟨.G2 q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = DynkinType.geckRootSubgroupPoints _
      (dynkinType_valid ⟨.G2 q, hv⟩) (.inr i) _ :=
  (rfl)

/-- The twisted E₆ family uses the doubled minuscule carrier's negative root maps. -/
theorem negativeSimpleRootSubgroup_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid)
    (i : Fin (rank ⟨.twistedE6 q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = E6DoubledMinuscule.rootSubgroupPoints
      (.inr (finCongr (TypeTwistedE6LieIndex.rank_eq_six ⟨⟨_, hv⟩, by simp⟩) i)) _ :=
  (rfl)

/-- Triality uses the tripled D₄ carrier's negative root maps. -/
theorem negativeSimpleRootSubgroup_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid)
    (i : Fin (rank ⟨.trialityD4 q, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = D4Tripled.rootSubgroupPoints
      (.inr (finCongr (TypeTrialityD4LieIndex.rank_eq_four ⟨⟨_, hv⟩, by simp⟩) i)) _ :=
  (rfl)

/-- Suzuki negative roots use the same length-preserving B₂-to-C₂ adapter as positive roots. -/
theorem negativeSimpleRootSubgroup_suzuki (hv : (LieTypeIndex.suzuki m).Valid)
    (i : Fin (rank ⟨.suzuki m, hv⟩)) :
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = SpStd.rootSubgroupPoints 1
      (.inr ((RankTwoBLieIndex.ofSuzuki m hv).carrierNode i)) _ :=
  (rfl)

/-- Ree G₂ uses the short-root carrier's negative root maps in characteristic three. -/
theorem negativeSimpleRootSubgroup_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid)
    (i : Fin (rank ⟨.reeG2 m, hv⟩)) :
    letI := ReeG2LieIndex.algebraZModThree (ReeG2LieIndex.of m hv)
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = G2ShortRoot.PrimeField.rootSubgroupPoints
      (.inr (finCongr (ReeG2LieIndex.of m hv).rank_eq_two i))
      (ReeG2LieIndex.of m hv).1.Closure :=
  (rfl)

/-- Ree F₄ uses the short-root carrier's negative root maps in characteristic two. -/
theorem negativeSimpleRootSubgroup_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid)
    (i : Fin (rank ⟨.reeF4 m, hv⟩)) :
    letI := ReeF4LieIndex.algebraZModTwo (ReeF4LieIndex.of m hv)
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = F4ShortRoot.PrimeField.rootSubgroupPoints
      (.inr (finCongr (ReeF4LieIndex.of m hv).rank_eq_four i))
      (ReeF4LieIndex.of m hv).1.Closure :=
  (rfl)

/-- The Tits index retains the short-root F₄ carrier's negative root maps. -/
theorem negativeSimpleRootSubgroup_tits (hv : LieTypeIndex.tits.Valid)
    (i : Fin (rank ⟨.tits, hv⟩)) :
    letI := TitsLieIndex.algebraZModTwo TitsLieIndex.of
    negativeSimpleRootSubgroup ⟨_, hv⟩ i = F4ShortRoot.PrimeField.rootSubgroupPoints
      (.inr (finCongr TitsLieIndex.of.rank_eq_four i)) TitsLieIndex.of.1.Closure :=
  (rfl)

end Branches

/-- Field Frobenius raises every negative simple root parameter to the indexed field order. -/
@[simp]
theorem frobenius_negativeSimpleRootSubgroup (d : ValidLieTypeIndex) (i : Fin d.rank)
    (u : Multiplicative d.Closure) :
    d.frobenius (d.negativeSimpleRootSubgroup i u) =
      d.negativeSimpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.fieldOrder)) := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals dsimp only [negativeSimpleRootSubgroup]
  -- Each branch is the carrier's signed-root Frobenius equation. The application retains
  -- the dispatched group instance when the branch equations rewrite its maps: erw reduces
  -- that instance to the carrier's instance, and rfl removes the index-subtype wrappers.
  · erw [frobenius_A, GraphTwistedIndex.frobenius_A,
      TypeALieIndex.frobenius_def, SlStd.frobenius_rootSubgroupPoints,
      ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_twistedA, GraphTwistedIndex.frobenius_twistedA,
      TypeALieIndex.frobenius_def,
      SlStd.frobenius_rootSubgroupPoints, ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_B, GraphTwistedIndex.frobenius_B,
      TypeBLieIndex.frobenius_def, TypeBSpinCarrier.frobenius_rootSubgroupPoints,
      ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_C, GraphTwistedIndex.frobenius_C,
      TypeCLieIndex.frobenius_def, SpStd.frobenius_rootSubgroupPoints,
      ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_D, GraphTwistedIndex.frobenius_D,
      TypeDDiagramLieIndex.frobenius_def, TypeDSpinCarrier.frobenius_rootSubgroupPoints,
      ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_twistedD, GraphTwistedIndex.frobenius_twistedD,
      TypeDDiagramLieIndex.frobenius_def,
      TypeDSpinCarrier.frobenius_rootSubgroupPoints, ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_E6, GraphTwistedIndex.frobenius_E6,
      TypeE6LieIndex.steinberg_def, E6Minuscule.frobenius_rootSubgroupPoints,
      ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_E7, GraphTwistedIndex.frobenius_E7,
      TypeE7LieIndex.steinberg_def, E7Minuscule.frobenius_rootSubgroupPoints,
      ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_E8, GraphTwistedIndex.frobenius_E8,
      UnimodularExceptionalIndex.steinberg_eq_geckFrobenius, geckFrobenius_def,
      DynkinType.geckFrobenius_geckRootSubgroupPoints, ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_F4, GraphTwistedIndex.frobenius_F4,
      UnimodularExceptionalIndex.steinberg_eq_geckFrobenius, geckFrobenius_def,
      DynkinType.geckFrobenius_geckRootSubgroupPoints, ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_G2, GraphTwistedIndex.frobenius_G2,
      UnimodularExceptionalIndex.steinberg_eq_geckFrobenius, geckFrobenius_def,
      DynkinType.geckFrobenius_geckRootSubgroupPoints, ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_twistedE6, GraphTwistedIndex.frobenius_twistedE6,
      TypeTwistedE6LieIndex.frobenius_def,
      E6DoubledMinuscule.frobenius_rootSubgroupPoints, ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_trialityD4, GraphTwistedIndex.frobenius_trialityD4,
      TypeTrialityD4LieIndex.frobenius_def,
      D4Tripled.frobenius_rootSubgroupPoints, ← fieldOrder_eq_characteristic_pow]
    rfl
  · erw [frobenius_suzuki,
      RankTwoBLieIndex.frobenius_def, SpStd.frobenius_rootSubgroupPoints,
      ← fieldOrder_eq_characteristic_pow]
    rfl
  case reeG2 m =>
    erw [frobenius_reeG2, ReeG2LieIndex.frobenius_def,
      G2ShortRoot.PrimeField.frobenius_rootSubgroupPoints,
      ← ReeG2LieIndex.fieldOrder_eq_three_pow (ReeG2LieIndex.of m hv)]
    rfl
  case reeF4 m =>
    erw [frobenius_reeF4, ReeF4LieIndex.frobenius_def,
      F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints,
      ← ReeF4LieIndex.fieldOrder_eq_two_pow (ReeF4LieIndex.of m hv)]
    rfl
  case tits =>
    erw [frobenius_tits, TitsLieIndex.frobenius_def,
      F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints, pow_one,
      ← TitsLieIndex.fieldOrder_eq_two TitsLieIndex.of]
    rfl

end

end TauCeti.ValidLieTypeIndex
