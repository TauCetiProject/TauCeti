/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# The jointly analytic Möbius action of `PSL(2, 𝕜)` on the projective line

Give `PSL(2, 𝕜) = SL(2, 𝕜) ⧸ Z(SL(2, 𝕜))`, for `𝕜 = ℝ` or `ℂ`, its analytic Lie group structure
as the quotient of `SL(2, 𝕜)` by its finite center (`Subgroup.instLieGroupDiscreteQuotient`). This
file proves that the Möbius action of `PSL(2, 𝕜)` on the projective line `OnePoint 𝕜` is jointly
analytic (`OnePoint.instContMDiffSMulPSL`): the map `(g, x) ↦ g • x` is analytic on
`PSL(2, 𝕜) × OnePoint 𝕜`, including at `∞`. For `𝕜 = ℂ` this is the holomorphic action of the
automorphism group of the Riemann sphere. The proof lifts the action along the projection
`SL(2, 𝕜) → PSL(2, 𝕜)`, a local diffeomorphism, where it is the action of the general linear
group (`OnePoint.instContMDiffSMul`) restricted along the analytic inclusion
`SL(2, 𝕜) → GL(2, 𝕜)`.

## Main declarations

* `OnePoint.instContMDiffSMulPSL`: the Möbius action of `PSL(2, 𝕜)` on `OnePoint 𝕜` is jointly
  analytic.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2 (the Möbius transformations of the Riemann sphere).
-/

public section

open Matrix
open scoped ContDiff Manifold MatrixGroups Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace OnePoint

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜]

/-- **The Möbius action of `PSL(2, 𝕜)` on the projective line is jointly analytic**, for the
analytic Lie group structure of `PSL(2, 𝕜)` as the quotient of `SL(2, 𝕜)` by its finite center.
For `𝕜 = ℂ` this is the holomorphic action of the automorphism group of the Riemann sphere. -/
instance instContMDiffSMulPSL :
    ContMDiffSMul 𝓘(𝕜, SpecialLinearGroup.Model (Fin 2) 𝕜) 𝓘(𝕜) ω PSL(2, 𝕜) (OnePoint 𝕜) where
  contMDiff_smul := by
    -- Lift the action along the projection `SL(2, 𝕜) → PSL(2, 𝕜)` in the group factor, which
    -- is put second so that `IsLocalDiffeomorph.contMDiff_comp_prodMap_iff` applies.
    have hSL : ContMDiff (𝓘(𝕜).prod 𝓘(𝕜, SpecialLinearGroup.Model (Fin 2) 𝕜)) 𝓘(𝕜) ω
        fun p : OnePoint 𝕜 × SL(2, 𝕜) ↦ SpecialLinearGroup.toGL p.2 • p.1 :=
      ((SpecialLinearGroup.contMDiff_toGL (n := Fin 2) (𝕜 := 𝕜)).comp contMDiff_snd).smul
        contMDiff_fst
    have hPSL : ContMDiff (𝓘(𝕜).prod 𝓘(𝕜, SpecialLinearGroup.Model (Fin 2) 𝕜)) 𝓘(𝕜) ω
        fun p : OnePoint 𝕜 × PSL(2, 𝕜) ↦ p.2 • p.1 :=
      ((Subgroup.isLocalDiffeomorph_quotientMk (I := 𝓘(𝕜, SpecialLinearGroup.Model (Fin 2) 𝕜))
        (n := ω) (Subgroup.center SL(2, 𝕜))).contMDiff_comp_prodMap_iff
          (g := fun p : OnePoint 𝕜 × PSL(2, 𝕜) ↦ p.2 • p.1) QuotientGroup.mk_surjective le_rfl).1
        (hSL.congr fun p ↦ pslMk_smul p.2 p.1)
    exact hPSL.comp (contMDiff_snd.prodMk contMDiff_fst)

end OnePoint
