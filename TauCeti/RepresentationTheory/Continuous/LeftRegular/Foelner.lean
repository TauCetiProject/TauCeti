/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Koopman.Foelner

/-!
# Følner vectors in the discrete regular representation

Specializing the action-level Følner-indicator construction of
`TauCeti.RepresentationTheory.Continuous.Koopman.Foelner` to left multiplication of a group `G` on
itself gives the exact translation displacement of finite-set constant indicators in `ℓ²(G, E)`
(`Finset.norm_count_leftRegular_sub_indicatorConstLp`) and produces almost invariant unit vectors in
`ℓ²(G, E)` whenever `G` has Følner sets and `E` is nontrivial
(`MeasureTheory.Measure.hasAlmostInvariantVectors_count_leftRegular`). Together with the vanishing
of invariants proved in `LeftRegular.Basic`, this gives the regular-representation obstruction to
property (T) for infinite amenable groups.
The argument follows Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory Finset
open scoped ENNReal Pointwise symmDiff

namespace MeasureTheory.Measure

variable {G 𝕜 E : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- In counting-measure `L²(G, E)`, the left-translation displacement of a constant indicator
supported on a finite set `F` is `√|g • F ∆ F| * ‖c‖`. -/
theorem _root_.Finset.norm_count_leftRegular_sub_indicatorConstLp [DecidableEq G] [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (F : Finset G) (g : G) (c : E) :
    ‖(count : Measure G).leftRegular 𝕜 E 2 g
        (indicatorConstLp 2 F.measurableSet (by simp) c) -
      indicatorConstLp 2 F.measurableSet (by simp) c‖ =
        Real.sqrt (#((g • F) ∆ F) : ℝ) * ‖c‖ := by
  rw [← koopman_eq_leftRegular]
  exact F.norm_count_koopman_sub_indicatorConstLp (G := G) (𝕜 := 𝕜) g c

/-- Følner sets produce almost invariant unit vectors in the vector-valued counting-measure regular
representation `ℓ²(G, E)` whenever `E` is nontrivial. No countability of the group is required. -/
theorem hasAlmostInvariantVectors_count_leftRegular [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] (hG : TauCeti.HasFoelnerSets G) :
    ((count : Measure G).leftRegular 𝕜 E 2).HasAlmostInvariantVectors := by
  classical
  rw [← koopman_eq_leftRegular]
  exact hasAlmostInvariantVectors_count_koopman_of_forall_exists_finset
    (TauCeti.hasFoelnerSets_iff.mp hG)

end MeasureTheory.Measure
