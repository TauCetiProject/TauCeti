/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Smooth Kato intertwiners

The intertwiner of two nearby projections is polynomial in the varying projection. Its inverse
is smooth on the open set of invertible intertwiners, by native smooth inversion in a Banach
algebra. The ground field may differ from the operator field: in particular a real parameter
may act on complex-linear operators. No idempotence is needed for these regularity facts.

These are the operator prerequisites for smooth range bundles; see Kato, *Perturbation Theory
for Linear Operators*, Chapter I, §4.6.
-/

public section

open Set
open scoped Manifold ContDiff Ring

namespace TauCeti
variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] [CompleteSpace F]
  {n : ℕ∞ω} {p : B → F →L[𝕜'] F}

omit [CompleteSpace F] in
/-- The Kato intertwiner of a smooth operator family and a fixed member is smooth. -/
theorem contMDiff_intertwiner (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (x₀ : B) :
    ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n
      (fun x ↦ p x * p x₀ + (1 - p x) * (1 - p x₀)) := by
  let : NormedAlgebra 𝕜 (F →L[𝕜'] F) :=
    { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }
  have hsub : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n (fun x ↦ 1 - p x) :=
    (contDiff_fst.sub contDiff_snd).comp_contMDiff
      ((contMDiff_const (c := (1 : F →L[𝕜'] F))).prodMk_space hp)
  exact (contDiff_mul.comp_contMDiff (hp.prodMk_space contMDiff_const)).add
    (contDiff_mul.comp_contMDiff (hsub.prodMk_space contMDiff_const))

/-- The inverse Kato intertwiner is smooth on its native invertibility domain. -/
theorem contMDiffOn_inverse_intertwiner (hp : ContMDiff I 𝓘(𝕜, F →L[𝕜'] F) n p) (x₀ : B) :
    ContMDiffOn I 𝓘(𝕜, F →L[𝕜'] F) n
      (fun x ↦ (p x * p x₀ + (1 - p x) * (1 - p x₀))⁻¹ʳ)
      {x | IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀))} := by
  let : NormedAlgebra 𝕜 (F →L[𝕜'] F) :=
    { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }
  intro x hx
  have hi := contDiffAt_ringInverse 𝕜 hx.unit (n := n)
  rw [hx.unit_spec] at hi
  exact (hi.comp_contMDiffAt
    (f := fun x ↦ p x * p x₀ + (1 - p x) * (1 - p x₀))
    (contMDiff_intertwiner hp x₀ x)).contMDiffWithinAt

end TauCeti
