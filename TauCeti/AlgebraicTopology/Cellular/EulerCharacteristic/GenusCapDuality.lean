/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.CapDuality

/-!
# The Euler–genus identity from middle-degree cap duality

For a closed homologically oriented surface, injectivity of capping with a degree-two
rational homology class makes the first Betti number even. The Euler characteristic
is therefore twice one minus the topological genus.
-/

public noncomputable section

open AlgebraicTopology CategoryTheory Module MonoidalCategory

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [FiniteCWType M] (o : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2)

include o hn

/-- Injective middle-degree cap duality implies the Euler–genus identity for a closed
oriented surface. -/
theorem eulerChar_eq_two_sub_two_mul_genus_of_injective_cap
    (μ : ((singularHomologyFunctor (ModuleCat ℚ) 2).obj (𝟙_ (ModuleCat ℚ))).obj
      (TopCat.of M))
    (hinj : Function.Injective
      ((TopCat.of M).singularCapLinearMap ℚ (by decide : 1 + 1 = 2) μ)) :
    eulerChar M = 2 - 2 * RiemannSurface.genus M := by
  apply (TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank
    o hn).2
  exact (TopCat.of M).even_finrank_singularHomology_of_injective_singularCapLinearMap
    ℚ (by norm_num) (by decide : Odd 1) (by decide : 1 + 1 = 2) μ hinj

end TauCeti.HomologicalOrientation
