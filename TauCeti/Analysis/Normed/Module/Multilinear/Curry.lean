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

Over a complete nontrivially normed field `𝕜`, continuous multilinear maps in finitely many
variables from finite-dimensional normed spaces to a second countable normed space form a second
countable space. Mathlib records the one-variable case: `E →L[𝕜] F` is second countable when `E`
is finite-dimensional and `F` is second countable.

For `n` variables in a single space `G`, currying the first variable identifies `G [×(n+1)]→L[𝕜] F`
with `G →L[𝕜] (G [×n]→L[𝕜] F)`, so the one-variable case gives the claim by induction on `n`.
Reindexing along `ι ≃ Fin n` gives any finite index type. A family `E i` of spaces reduces to a
single space `Π i, E i`: precomposing with the projections embeds the multilinear maps on `E`
into those on `Π i, E i`, with continuous left inverse the precomposition with the inclusions.

## Main results

* `ContinuousMultilinearMap.secondCountableTopology'`: the space of continuous multilinear maps
  in variables indexed by a finite type, from a single finite-dimensional space, is second
  countable. This covers `G [×n]→L[𝕜] F`.
* `ContinuousMultilinearMap.secondCountableTopology`: the space of continuous multilinear maps
  from a finite family of finite-dimensional spaces is second countable.
-/

public section

open TopologicalSpace

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ι : Type*} [Finite ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SecondCountableTopology F]

/-- Continuous multilinear maps in finitely many variables from a finite-dimensional space to a
second countable space form a second countable space. -/
instance secondCountableTopology' {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] :
    SecondCountableTopology (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ G) F) := by
  have := Fintype.ofFinite ι
  -- Currying one variable at a time, `G [×n]→L[𝕜] F` is second countable.
  have (n : ℕ) : SecondCountableTopology (G [×n]→L[𝕜] F) := by
    induction n with
    | zero => exact (continuousMultilinearCurryFin0 𝕜 G F).toHomeomorph.secondCountableTopology
    | succ n ih =>
      exact (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ G)
        F).toHomeomorph.secondCountableTopology
  exact (domDomCongrₗᵢ 𝕜 G F (Fintype.equivFin ι)).toHomeomorph.secondCountableTopology

/-- Continuous multilinear maps from a finite family of finite-dimensional spaces to a second
countable space form a second countable space. -/
instance secondCountableTopology {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, FiniteDimensional 𝕜 (E i)] :
    SecondCountableTopology (ContinuousMultilinearMap 𝕜 E F) := by
  classical
  have := Fintype.ofFinite ι
  -- Precomposing with the projections of `Π i, E i` is an embedding, with continuous left inverse
  -- the precomposition with the inclusions of the factors.
  refine (Function.LeftInverse.isEmbedding
    (f := fun g ↦ g.compContinuousLinearMap (ContinuousLinearMap.single 𝕜 E))
    (g := fun f : ContinuousMultilinearMap 𝕜 E F ↦
      f.compContinuousLinearMap (ContinuousLinearMap.proj (R := 𝕜) (φ := E)))
    (fun f ↦ ?_) (continuous_precomp _) (continuous_precomp _)).secondCountableTopology
  ext m
  simp

end ContinuousMultilinearMap
