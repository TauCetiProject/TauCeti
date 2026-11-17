/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.RepresentationTheory.Continuous.Basic

import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Geometry.Lie.AutomaticSmoothness
import TauCeti.RepresentationTheory.Continuous.Hom

/-!
# Automatic smoothness of continuous representations of Lie groups

Every continuous finite-dimensional representation `π : ContRepresentation 𝕜 G V` of a
finite-dimensional real Lie group `G` over a finite-dimensional normed field extension `𝕜` of `ℝ` is
smooth: viewing `π` as a continuous group homomorphism into the general linear Lie group
`(V →L[𝕜] V)ˣ` via `ContRepresentation.toUnitsContinuousMonoidHom`, automatic smoothness for
Lie-group homomorphisms (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`) yields smoothness of
`π : G → (V →L[𝕜] V)` and hence joint smoothness of the action `(g, v) ↦ π g v` on `G × V`.

## Main results

* `ContRepresentation.contMDiff`: every continuous finite-dimensional representation of a
  finite-dimensional real Lie group is smooth as an operator-valued map.
* `ContRepresentation.contMDiff_apply`: the joint action `(g, v) ↦ π g v` of a continuous
  finite-dimensional representation of a finite-dimensional real Lie group is smooth.
-/

public section

noncomputable section

open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace ContRepresentation

attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [FiniteDimensional ℝ 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass 𝕜 ℝ V]
  [IsScalarTower ℝ 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Every continuous finite-dimensional representation of a finite-dimensional real Lie group is
smooth.** -/
theorem contMDiff (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ContMDiff I 𝓘(ℝ, V →L[𝕜] V) ∞ π := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : FiniteDimensional ℝ V := Module.Finite.trans 𝕜 V
  let _ : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let _ : FiniteDimensional ℝ (V →L[𝕜] V) := Module.Finite.trans 𝕜 (V →L[𝕜] V)
  let _ : NormedAlgebra ℝ (V →L[𝕜] V) :=
    { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }
  have hhom : ContMDiff I 𝓘(ℝ, V →L[𝕜] V) ∞ (π.toUnitsContinuousMonoidHom hπ) :=
    TauCeti.Lie.contMDiff_of_continuous_monoidHom (π.toUnitsContinuousMonoidHom hπ)
      (π.toUnitsContinuousMonoidHom hπ).continuous
  simpa [Function.comp_def, toMonoidHom_apply] using
    (Units.contMDiff_val (𝕜 := ℝ) (R := V →L[𝕜] V) (n := ∞)).comp hhom

/-- The joint action `(g, v) ↦ π g v` of a continuous finite-dimensional representation of a
finite-dimensional real Lie group is smooth. -/
theorem contMDiff_apply (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ContMDiff (I.prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ (fun p : G × V ↦ π p.1 p.2) := by
  let R : (V →L[𝕜] V) →L[ℝ] (V →L[ℝ] V) := ContinuousLinearMap.restrictScalarsL 𝕜 V V ℝ ℝ
  have hR : ContMDiff I 𝓘(ℝ, V →L[ℝ] V) ∞ (fun g : G ↦ R (π g)) :=
    R.contDiff.contMDiff.comp (π.contMDiff hπ)
  exact (hR.comp contMDiff_fst).clm_apply contMDiff_snd

end ContRepresentation
