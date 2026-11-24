/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Koopman.Basic
public import TauCeti.GroupTheory.Amenable.Foelner
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Følner vectors in counting-measure Koopman and regular representations

For any group `G` acting measurably on a space `X` with measurable singletons, a counting-measure
Følner family along a nontrivial filter yields almost invariant unit vectors in the vector-valued
Koopman representation `ℓ²(X, E)` whenever `E` is nontrivial
(`IsFoelner.hasAlmostInvariantVectors_count_koopman`). Specializing to the left regular action of
`G` on itself gives vector-valued Følner almost invariant vectors in `ℓ²(G, E)`
(`MeasureTheory.Measure.hasAlmostInvariantVectors_count_leftRegular`). Together with the vanishing
of invariants proved in `LeftRegular.Basic`, this gives the regular-representation obstruction to
property (T) for infinite amenable groups.
The argument follows Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory Filter Finset
open scoped ENNReal Pointwise symmDiff

/-- A counting-measure Følner family along a nontrivial filter produces almost invariant unit
vectors in the vector-valued Koopman representation `ℓ²(X, E)` whenever `E` is nontrivial. -/
theorem IsFoelner.hasAlmostInvariantVectors_count_koopman {G X 𝕜 E ι : Type*} [Group G]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MulAction G X] [MeasurableConstSMul G X]
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E]
    {l : Filter ι} [l.NeBot] {F : ι → Set X}
    (hF : IsFoelner G (Measure.count : Measure X) l F) :
    ((Measure.count : Measure X).koopman G 𝕜 E 2).HasAlmostInvariantVectors := by
  classical
  exact Measure.hasAlmostInvariantVectors_count_koopman_of_forall_exists_finset
    fun K _ hε ↦ hF.exists_finset_card_smul_symmDiff_lt K hε

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
