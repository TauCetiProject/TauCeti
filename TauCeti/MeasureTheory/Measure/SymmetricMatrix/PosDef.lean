/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Matrix.PosDef
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Topology of the positive-definite cone of real symmetric matrices

On the symmetric subspace, positive definiteness cuts out an open subset by
`Matrix.isOpen_setOfPred_posDef_selfAdjoint`.

The Wishart densities are supported on this cone, so its measurability is part of the
carrier API.

The cone is also packaged as a subtype, `TauCeti.PosDefMatrix`, which is the carrier the
Wishart and Cholesky APIs are stated on.

Its closure is the positive-semidefinite cone, including singular matrices. This distinction
identifies the topological support of laws whose densities are positive exactly on the
positive-definite cone.

## Main declarations

* `TauCeti.PosDefMatrix` — the positive-definite cone in the space of real symmetric matrices.
* `TauCeti.isOpen_posDefMatrix` — the positive-definite cone is open in the symmetric subspace.
* `TauCeti.measurableSet_posDefMatrix` — the positive-definite cone is measurable.
* `TauCeti.closure_posDefMatrix` — its closure is the positive-semidefinite cone.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

/-- The cone of positive-definite real symmetric matrices of size `p`. -/
abbrev PosDefMatrix (p : ℕ) :=
  {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) //
    (A : Matrix (Fin p) (Fin p) ℝ).PosDef}

/-- The positive-definite cone is open in the real submodule of symmetric matrices. -/
theorem isOpen_posDefMatrix (p : ℕ) :
    IsOpen {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  -- The selfAdjoint subgroup and its real submodule have definitionally equal carriers
  -- and induced topologies, so the openness theorem applies to this subtype.
  exact Matrix.isOpen_setOfPred_posDef_selfAdjoint

/-- The positive-definite cone is measurable in the symmetric subspace. -/
theorem measurableSet_posDefMatrix (p : ℕ) :
    MeasurableSet {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} :=
  (isOpen_posDefMatrix p).measurableSet

open Filter Set
open scoped Topology in
/-- The closure of the positive-definite cone in the symmetric subspace is the
positive-semidefinite cone, also in dimension zero. -/
theorem closure_posDefMatrix (p : ℕ) :
    closure {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} =
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef} := by
  refine Subset.antisymm
    (closure_minimal (fun _ hA ↦ hA.posSemidef)
      (isClosed_setOfPred_posSemidef.preimage continuous_subtype_val)) ?_
  intro A hA
  -- Add a positive multiple of the identity while staying in the symmetric subspace.
  let I : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
    ⟨1, IsSelfAdjoint.one _⟩
  have hmem : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t • I + A ∈ {B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (B : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (Matrix.PosDef.one.smul ht).add_posSemidef hA
  have hcont : Continuous (fun t : ℝ ↦ t • I + A) := by fun_prop
  exact mem_closure_of_tendsto
    ((hcont.tendsto' 0 A (by simp)).mono_left nhdsWithin_le_nhds) hmem

end TauCeti
