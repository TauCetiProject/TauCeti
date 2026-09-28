/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Finite-dimensional module topology in coordinates

For a finite-dimensional vector space over a topological field, the module topology is the
coordinate topology through any basis. This identifies the canonical topology used on quadratic
spaces and their endomorphisms with a finite product of copies of the field. In particular, over
a Hausdorff locally compact field it is Hausdorff and locally compact. No norm or completeness
hypothesis on the field is needed.
-/

public section

namespace Module.Basis

variable {K V ι : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]
  [Finite ι]

/-- Coordinates through a finite basis give a homeomorphism for the module topology. -/
noncomputable def equivFunHomeomorph (b : Basis ι K V) : V ≃ₜ (ι → K) :=
  let _ : ContinuousAdd V := IsModuleTopology.toContinuousAdd K V
  { b.equivFun with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }

@[simp]
theorem equivFunHomeomorph_apply (b : Basis ι K V) (v : V) :
    b.equivFunHomeomorph v = b.equivFun v := by
  simp [equivFunHomeomorph]

@[simp]
theorem equivFunHomeomorph_symm_apply (b : Basis ι K V) (c : ι → K) :
    b.equivFunHomeomorph.symm c = b.equivFun.symm c := by
  simp [equivFunHomeomorph]

end Module.Basis

namespace TauCeti

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The module topology of a finite-dimensional space over a Hausdorff topological field is
Hausdorff. -/
theorem t2Space_moduleTopology [T2Space K] :
    @T2Space V (moduleTopology K V) := by
  let _ : TopologicalSpace V := moduleTopology K V
  let b := Module.finBasis K V
  exact b.equivFunHomeomorph.symm.t2Space

/-- The module topology of a finite-dimensional space over a locally compact topological field
is locally compact. -/
theorem locallyCompactSpace_moduleTopology [LocallyCompactSpace K] :
    @LocallyCompactSpace V (moduleTopology K V) := by
  let _ : TopologicalSpace V := moduleTopology K V
  let b := Module.finBasis K V
  exact b.equivFunHomeomorph.isOpenEmbedding.locallyCompactSpace

end TauCeti
