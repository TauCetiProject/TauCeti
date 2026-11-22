/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular

/-!
# Bochner `L¹` integrated form of regular covariant representations

This file extends `TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular` and
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1`, identifying the Bochner `L¹` integrated form
of the regular covariant representation for the trivial action on `ℂ` with ordinary group
convolution `MeasureTheory.Lp.convolutionL` on `L²(G, H)`.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For the trivial action of `G` on `ℂ` acting by scalars on any complex Hilbert space `H`,
`integratedOperatorBochnerL1` of the regular representation on `L²(G, H)` is
`MeasureTheory.Lp.convolutionL`. -/
theorem integratedOperatorBochnerL1_regular_trivial (μ : Measure G)
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant] :
    (regular (CStarAction.trivial (G := G) (A := ℂ))
        (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom μ).integratedOperatorBochnerL1 μ =
      Lp.convolutionL μ 2 ENNReal.ofNat_ne_top := by
  let ρ : ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H) := (StarAlgHom.ofId ℂ (H →L[ℂ] H)).toNonUnitalStarAlgHom
  ext f ξ : 2
  rw [integratedOperatorBochnerL1_apply, Lp.convolutionL_apply]
  refine integral_congr_ae (.of_forall fun g => ?_)
  dsimp only
  refine Lp.ext ?_
  filter_upwards [coeFn_regular_coefficient (CStarAction.trivial (G := G) (A := ℂ)) ρ μ (f g)
      ((regular (CStarAction.trivial (G := G) (A := ℂ)) ρ μ).group g ξ),
    μ.coeFn_leftRegular (𝕜 := ℂ) 2 g ξ,
    Lp.coeFn_smul (f g) (Lp.leftTranslation μ 2 ℂ g ξ),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) g ξ] with r h₁ h₂ h₃ h₄
  rw [h₁, regular_group, h₂, h₃, Pi.smul_apply, h₄]
  simp [ρ, Algebra.algebraMap_eq_smul_one]

end TauCeti.CStarAction.CovariantRepresentation
