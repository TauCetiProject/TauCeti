/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth maps into `L^p` products and Euclidean space

A map from a manifold into a finite `L^p` product `PiLp p E`, in particular into
`EuclideanSpace 𝕜 ι = PiLp 2 (fun _ ↦ 𝕜)`, is `C^n` exactly when each of its coordinates is. This
is the manifold analogue of Mathlib's `contDiff_piLp`, and the analogue for `PiLp p E` of
Mathlib's `contMDiff_pi_module_iff` for `∀ i, E i`, transported along the continuous linear
equivalence `PiLp.continuousLinearEquiv`.

## Main results

* `TauCeti.contMDiff_piLp_iff`: a map into `PiLp p E` is `C^n` if and only if each of its
  coordinates is.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {p : ENNReal} [Fact (1 ≤ p)] {F : ι → Type*} [∀ j, NormedAddCommGroup (F j)]
  [∀ j, NormedSpace 𝕜 (F j)]

/-- A map into `PiLp p F`, such as a map into `EuclideanSpace 𝕜 ι`, is `C^n` if and only if each
of its coordinates is. -/
theorem contMDiff_piLp_iff {g : M → PiLp p F} :
    ContMDiff I 𝓘(𝕜, PiLp p F) n g ↔ ∀ j, ContMDiff I 𝓘(𝕜, F j) n fun x ↦ g x j :=
  ⟨fun h j ↦ (PiLp.proj p (𝕜 := 𝕜) F j).contMDiff.comp h,
    fun h ↦ ((PiLp.continuousLinearEquiv p 𝕜 F).symm : (∀ j, F j) →L[𝕜] PiLp p F).contMDiff.comp
      (contMDiff_pi_module_iff.2 h)⟩

end TauCeti
