/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Second countability of spaces of continuous multilinear maps

If finitely many spaces `E i` are finite-dimensional over a complete field and `F` is second
countable, then the space of continuous multilinear maps from `∀ i, E i` to `F` is second
countable. For continuous linear maps this is the Mathlib instance in
`Mathlib.Analysis.Normed.Module.FiniteDimension`; the multilinear case on copies of one space
follows by currying one variable at a time, since `E [×(m + 1)]→L[𝕜] F` is isometric to
`E →L[𝕜] (E [×m]→L[𝕜] F)`. A general family reduces to copies of the product `∀ j, E j`, of which
it is a retract by precomposition with the projections and the inclusions of the factors.

These are the spaces in which the iterated derivatives of a map `E → F` take their values, so
this is what makes spaces of continuous derivative fields on second countable locally compact
sets second countable.

## Main results

* `ContinuousMultilinearMap.secondCountableTopology`: the instance for finitely many
  finite-dimensional spaces over a complete field.
-/

public section

open Topology

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SecondCountableTopology F]

section Const

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The continuous multilinear maps in `m` variables from a finite-dimensional space to a second
countable space form a second countable space. -/
private theorem secondCountableTopology_fin (m : ℕ) : SecondCountableTopology (E [×m]→L[𝕜] F) := by
  induction m with
  | zero => exact (continuousMultilinearCurryFin0 𝕜 E F).toHomeomorph.secondCountableTopology
  | succ m ih =>
    exact (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) ↦ E)
      F).toHomeomorph.secondCountableTopology

/-- The continuous multilinear maps on finitely many copies of a finite-dimensional space, with
values in a second countable space, form a second countable space. -/
private theorem secondCountableTopology_const {ι : Type*} [Finite ι] :
    SecondCountableTopology (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) := by
  have := Fintype.ofFinite ι
  have := secondCountableTopology_fin (𝕜 := 𝕜) (E := E) (F := F) (Fintype.card ι)
  exact (domDomCongrₗᵢ 𝕜 E F (Fintype.equivFin ι)).toHomeomorph.secondCountableTopology

end Const

/-- The continuous multilinear maps on finitely many finite-dimensional spaces over a complete
field, with values in a second countable space, form a second countable space. They are a retract
of those on copies of the product `∀ j, E j`, by precomposition with the projections and the
inclusions of the factors. -/
instance secondCountableTopology {ι : Type*} [Finite ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [∀ i, FiniteDimensional 𝕜 (E i)] :
    SecondCountableTopology (ContinuousMultilinearMap 𝕜 E F) := by
  classical
  have := Fintype.ofFinite ι
  have := secondCountableTopology_const (𝕜 := 𝕜) (E := ∀ j, E j) (F := F) (ι := ι)
  let p := compContinuousLinearMapL (F := F) fun i ↦ ContinuousLinearMap.proj (R := 𝕜) (φ := E) i
  let s := compContinuousLinearMapL (F := F) fun i ↦ ContinuousLinearMap.single 𝕜 E i
  have hsp : Function.LeftInverse s p := fun f ↦ by
    ext v
    simp [p, s]
  exact (IsEmbedding.of_leftInverse hsp s.continuous p.continuous).secondCountableTopology

end ContinuousMultilinearMap
