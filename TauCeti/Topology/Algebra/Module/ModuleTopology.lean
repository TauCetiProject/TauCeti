/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Finite-dimensional module topology in coordinates

For a module over a topological semiring with a finite basis, the module topology is the
coordinate topology through that basis. This identifies the canonical topology used on quadratic
spaces and their endomorphisms with a finite product of copies of the scalars. In particular, over
a Hausdorff locally compact division ring equipped with a topological semiring structure, the
module topology of a finite-dimensional space is Hausdorff and locally compact, and every subspace
of a finite-dimensional space is closed; over σ-compact scalars it is σ-compact. No norm or
completeness hypothesis on the scalars is needed.

The basis-dependent API is grouped in `TauCeti.ModuleTopology`, alongside Mathlib's
organizational `ModuleTopology` namespace.
-/

public section

namespace TauCeti

namespace ModuleTopology

variable {K V ι : Type*} [Semiring K] [TopologicalSpace K] [IsTopologicalSemiring K]
  [AddCommMonoid V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]
  [Finite ι]

/-- Coordinates through a finite basis give a homeomorphism for the module topology. -/
noncomputable def equivFunHomeomorph (b : _root_.Module.Basis ι K V) : V ≃ₜ (ι → K) :=
  let _ : ContinuousAdd V := IsModuleTopology.toContinuousAdd K V
  { b.equivFun with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }

@[simp]
theorem equivFunHomeomorph_apply (b : _root_.Module.Basis ι K V) (v : V) :
    equivFunHomeomorph b v = b.equivFun v := by
  simp [equivFunHomeomorph]

@[simp]
theorem equivFunHomeomorph_symm_apply (b : _root_.Module.Basis ι K V) (c : ι → K) :
    (equivFunHomeomorph b).symm c = b.equivFun.symm c := by
  simp [equivFunHomeomorph]


/-- The module topology is Hausdorff when the scalars are Hausdorff and the module has a finite
basis. -/
theorem t2Space (b : _root_.Module.Basis ι K V) [T2Space K] : T2Space V :=
  (equivFunHomeomorph b).symm.t2Space

/-- The module topology is locally compact when the scalars are locally compact and the module
has a finite basis. -/
theorem locallyCompactSpace (b : _root_.Module.Basis ι K V) [LocallyCompactSpace K] :
    LocallyCompactSpace V :=
  (equivFunHomeomorph b).isOpenEmbedding.locallyCompactSpace

/-- The module topology is σ-compact when the scalars are σ-compact and the module has a finite
basis. -/
theorem sigmaCompactSpace (b : _root_.Module.Basis ι K V) [SigmaCompactSpace K] :
    SigmaCompactSpace V :=
  (equivFunHomeomorph b).isClosedEmbedding.sigmaCompactSpace

end ModuleTopology

variable {K V : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalSemiring K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The module topology of a finite-dimensional space over a Hausdorff division ring equipped
with a topological semiring structure is Hausdorff. -/
theorem t2Space_moduleTopology [T2Space K] :
    @T2Space V (moduleTopology K V) := by
  let _ : TopologicalSpace V := moduleTopology K V
  let b := Module.finBasis K V
  exact ModuleTopology.t2Space b

/-- The module topology of a finite-dimensional space over a locally compact division ring
equipped with a topological semiring structure is locally compact. -/
theorem locallyCompactSpace_moduleTopology [LocallyCompactSpace K] :
    @LocallyCompactSpace V (moduleTopology K V) := by
  let _ : TopologicalSpace V := moduleTopology K V
  let b := Module.finBasis K V
  exact ModuleTopology.locallyCompactSpace b

/-- The module topology of a finite-dimensional space over a σ-compact division ring equipped
with a topological semiring structure is σ-compact. -/
theorem sigmaCompactSpace_moduleTopology [SigmaCompactSpace K] :
    @SigmaCompactSpace V (moduleTopology K V) := by
  let _ : TopologicalSpace V := moduleTopology K V
  let b := Module.finBasis K V
  exact ModuleTopology.sigmaCompactSpace b

/-- Every subspace of a finite-dimensional space over a Hausdorff division ring equipped with a
topological semiring structure is closed for the module topology. -/
theorem _root_.Submodule.isClosed_of_isModuleTopology [T2Space K] [TopologicalSpace V]
    [IsModuleTopology K V] (W : Submodule K V) : IsClosed (W : Set V) := by
  have : T2Space (V ⧸ W) := ModuleTopology.t2Space (Module.finBasis K (V ⧸ W))
  have : ContinuousAdd (V ⧸ W) := IsModuleTopology.toContinuousAdd K (V ⧸ W)
  have hW : (W : Set V) = W.mkQ ⁻¹' {0} := by
    ext x
    simp [Submodule.Quotient.mk_eq_zero]
  rw [hW]
  exact isClosed_singleton.preimage (IsModuleTopology.continuous_of_linearMap W.mkQ)

end TauCeti
