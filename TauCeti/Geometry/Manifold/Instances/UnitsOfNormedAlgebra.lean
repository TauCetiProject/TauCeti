/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# The units of a normed algebra: derivative of the inclusion and smooth star

The inclusion of the units of a complete normed algebra has identity derivative in their native
open-submanifold charts, at every unit. Since that inclusion is the chart of the units at `1`,
composing an immersion into the units with it gives an immersion into the algebra.

For a complete normed star algebra over a field with trivial star, the star operation on the
group of units is smooth at every regularity order. This applies in particular to conjugate
transpose on invertible real or complex matrices, viewed as a real smooth map.

## Main results

* `Units.mvfderiv_val`: the vector-valued derivative of the units inclusion is the identity.
* `Units.hasMFDerivAt_val`: the units inclusion has the identity as derivative.
* `Units.isInvertible_mfderiv_val`: the derivative of the units inclusion is invertible.
* `Units.isImmersion_val_comp`: an immersion into the units stays an immersion into the algebra.
* `Units.contMDiff_star`: star is smooth on the group of units.

## References

* `Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra`, for the open-submanifold charts.
* `Mathlib.Geometry.Manifold.MFDeriv.Atlas`, for `mfderiv_extChartAt_self`.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 7 (Lie Groups), Basic Definitions, for smooth group operations.
-/

public section

open scoped ContDiff Manifold

namespace Units

section Deriv

variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

/-- The derivative of the units inclusion is the identity in the ambient algebra coordinates. -/
@[simp]
theorem mvfderiv_val (u : Rˣ) :
    mvfderiv 𝓘(𝕜, R) (val : Rˣ → R) u = ContinuousLinearMap.id 𝕜 R := by
  have hc : (extChartAt 𝓘(𝕜, R) u) = (val : Rˣ → R) := by
    funext g
    simp only [extChartAt_coe, Function.comp_apply, Units.chartAt_apply,
      modelWithCornersSelf_coe, id_eq]
  ext v
  rw [mvfderiv_apply_eq_mfderiv_apply, ← hc, mfderiv_extChartAt_self]
  exact ContinuousLinearMap.id_apply v

/-- The units inclusion has the identity as derivative at every unit. -/
theorem hasMFDerivAt_val (u : Rˣ) :
    HasMFDerivAt 𝓘(𝕜, R) 𝓘(𝕜, R) (val : Rˣ → R) u (ContinuousLinearMap.id 𝕜 R) := by
  refine ((contMDiff_val (n := 1)).mdifferentiableAt one_ne_zero (x := u)).hasMFDerivAt
    |>.congr_mfderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  -- The tangent space `TangentSpace 𝓘(𝕜, R) u` is `R`, so both sides are `v`.
  rw [← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_val]
  rfl

/-- The derivative of the units inclusion is invertible at every unit. -/
theorem isInvertible_mfderiv_val (u : Rˣ) :
    (mfderiv 𝓘(𝕜, R) 𝓘(𝕜, R) (val : Rˣ → R) u).IsInvertible := by
  have hc : (extChartAt 𝓘(𝕜, R) u : Rˣ → R) = val := funext fun _ ↦ by simp
  rw [← hc]
  exact isInvertible_mfderiv_extChartAt (mem_extChartAt_source u)

end Deriv

section Immersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- Composing an immersion into the units of a complete normed algebra with the inclusion into the
algebra gives an immersion, since that inclusion is the chart of the units at `1`. -/
theorem isImmersion_val_comp {f : M → Rˣ} (hf : Manifold.IsImmersion I 𝓘(𝕜, R) n f) :
    Manifold.IsImmersion I 𝓘(𝕜, R) n (val ∘ f) :=
  -- `chartAt R (1 : Rˣ)` is defined to be `Units.val` on `Set.univ`.
  TauCeti.isImmersion_isLocalDiffeomorphAt_comp (k := chartAt R (1 : Rˣ))
    (fun _ ↦ (chartAt R (1 : Rˣ)).isLocalDiffeomorphAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (1 : Rˣ)) (by simp)) hf

end Immersion

section Star

variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
  [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R] [StarRing R] [ContinuousStar R]
  [StarModule 𝕜 R] {k : ℕ∞ω}

/-- Star on the units of a complete normed star algebra is smooth over a field with trivial star. -/
theorem contMDiff_star : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) k (star : Rˣ → Rˣ) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact (starL' 𝕜 : R ≃L[𝕜] R).contDiff.contMDiff.comp contMDiff_val

end Star

end Units
