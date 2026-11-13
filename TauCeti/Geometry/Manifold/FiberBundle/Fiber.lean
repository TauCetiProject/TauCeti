/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel

/-!
# Regular fibres of smooth bundle projections

The fibre of a smooth bundle projection, as a subtype of its total space, carries the
regular-fibre atlas. This is the embedded-submanifold structure constructed from the
projection, not an atlas transported from a bundle trivialization. The total space is charted
through the manifold fibre by `TauCeti.ManifoldTotalSpace`.

These named atlases allow comparisons with parametrizations of individual fibres, such as
the orbit maps of principal bundles. No separation or countability hypothesis is needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer (2013),
  Corollary 5.14 and Proposition 5.38 (regular fibres).
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.ManifoldTotalSpace

variable {n : ℕ∞ω} {B F : Type*} {P : B → Type*}
  {EB HB EF HF : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IB : ModelWithCorners ℝ EB HB} {IF : ModelWithCorners ℝ EF HF}
  [TopologicalSpace B] [ChartedSpace HB B] [TopologicalSpace F] [ChartedSpace HF F]
  [TopologicalSpace (TotalSpace F P)] [∀ b, TopologicalSpace (P b)] [FiberBundle F P]
  [IsManifold IB n B]

local notation "T" => ManifoldTotalSpace F P
local notation "π₀" => fun x : T ↦ Bundle.TotalSpace.proj
  (Homeomorph.symm (ManifoldTotalSpace.homeomorph F P) x)

variable [IB.Boundaryless] [IF.Boundaryless]
  [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EF]

variable (F P IB IF) in
/-- The regular-fibre atlas on the actual fibre subtype of a bundle projection. It retains
the subspace topology and is not installed as a global instance. -/
@[instance_reducible]
noncomputable def fiberChartedSpace (hn : 1 ≤ n) (b : B) :
    ChartedSpace (Fin (Module.finrank ℝ (EB × EF) - Module.finrank ℝ EB) → ℝ)
      {x : T // π₀ x = b} :=
  regularFiberChartedSpace hn (contMDiff_proj n F P IB IF)
    BoundarylessManifold.isInteriorPoint (isRegularValue_proj b)

/-- The bundle-fibre atlas is the regular-fibre atlas of the projection. This equation
allows reuse of the regular-fibre API without unfolding the bundle-fibre atlas. -/
theorem fiberChartedSpace_eq_regularFiberChartedSpace (hn : 1 ≤ n) (b : B) :
    fiberChartedSpace F P IB IF hn b =
      regularFiberChartedSpace hn (contMDiff_proj n F P IB IF)
        BoundarylessManifold.isInteriorPoint (isRegularValue_proj b) :=
  (rfl)

variable [IsManifold IF n F] [ContMDiffFiberBundle n F P IB IF]

local notation "K" => 𝓘(ℝ, Fin (Module.finrank ℝ (EB × EF) - Module.finrank ℝ EB) → ℝ)

variable (F P IB IF) in
/-- A fibre with the regular-fibre atlas of the bundle projection is a `C^n` manifold. -/
theorem isManifold_fiber (hn : 1 ≤ n) (b : B) :
    letI := fiberChartedSpace F P IB IF hn b
    IsManifold K n {x : T // π₀ x = b} :=
  isManifold_regularFiber hn (contMDiff_proj n F P IB IF)
    BoundarylessManifold.isInteriorPoint (isRegularValue_proj b)

variable (F P IB IF) in
/-- The inclusion of a bundle fibre with its regular-fibre atlas is a smooth embedding. -/
theorem isSmoothEmbedding_coe_fiber (hn : 1 ≤ n) (b : B) :
    letI := fiberChartedSpace F P IB IF hn b
    Manifold.IsSmoothEmbedding K (IB.prod IF) n
      (Subtype.val : {x : T // π₀ x = b} → T) :=
  isSmoothEmbedding_coe_regularFiber hn (contMDiff_proj n F P IB IF)
    BoundarylessManifold.isInteriorPoint (isRegularValue_proj b)

variable (F P IB IF) in
/-- The tangent image of a bundle-fibre inclusion is the kernel of the projection differential. -/
theorem range_mfderiv_coe_fiber (hn : 1 ≤ n) (b : B) :
    letI := fiberChartedSpace F P IB IF hn b
    ∀ z : {x : T // π₀ x = b},
      (mfderiv K (IB.prod IF) Subtype.val z).range =
        (mfderiv (IB.prod IF) IB π₀ z.1).ker :=
  range_mfderiv_coe_regularFiber hn (contMDiff_proj n F P IB IF)
    BoundarylessManifold.isInteriorPoint (isRegularValue_proj b)

end TauCeti.ManifoldTotalSpace
