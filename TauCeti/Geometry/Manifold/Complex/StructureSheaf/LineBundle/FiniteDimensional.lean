/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Cech
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.FiniteDimensional

/-!
# Finite-dimensional global holomorphic sections and degree-zero Čech cohomology

For a finite-rank holomorphic vector bundle on a compact Hausdorff complex curve, its existing
sheaf of holomorphic sections has finite-dimensional global sections. The native degree-zero
Čech comparison gives finite-dimensionality of its cover-colimit Čech cohomology in degree zero.
The base uses the ordinary complex chart model, without boundary; it may be empty or disconnected.

The section comparison removes only the open-top subtype. Both the original fibres and the
analytic section predicate are preserved. No assertion about positive-degree cohomology is made.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §§14–16, 29.
-/

public noncomputable section

open Bundle Opposite TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [T2Space X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] {V : X → Type} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] [ContMDiffVectorBundle ω F V 𝓘(ℂ)]

/-- Global sections of the existing holomorphic-section sheaf on a compact complex curve are
finite-dimensional, without a connectedness or positive-rank assumption. -/
instance holomorphicBundleSections.instFiniteDimensionalTop :
    FiniteDimensional ℂ (holomorphicBundleSections 𝓘(ℂ) F V ⊤) :=
  Module.Finite.equiv (holomorphicBundleSections.topEquivContMDiffSection 𝓘(ℂ) F V).symm

/-- The global object of the native holomorphic-section sheaf is finite-dimensional. -/
instance holomorphicSectionSheaf.instFiniteDimensionalGlobal :
    FiniteDimensional ℂ ((holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op ⊤)) := by
  rw [holomorphicSectionSheaf.obj_eq]
  infer_instance

/-- The native cover-colimit Čech group in degree zero is finite-dimensional for a finite-rank
holomorphic bundle on a compact complex curve. -/
instance holomorphicSectionCechCohomology.instFiniteDimensionalZero :
    FiniteDimensional ℂ (holomorphicSectionCechCohomology 𝓘(ℂ) F V 0) := by
  let e := (Topology.cechCohomologyZeroIso (holomorphicSectionSheaf 𝓘(ℂ) F V)).toLinearEquiv
  exact Module.Finite.equiv e

end TauCeti
