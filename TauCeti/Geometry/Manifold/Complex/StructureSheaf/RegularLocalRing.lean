/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Regular
public import TauCeti.RingTheory.Regular.RegularSequence

import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Coordinate parameters of regular holomorphic local rings

Centered coordinates in any holomorphic chart form a regular sequence in the holomorphic local
ring (`OpenPartialHomeomorph.isRegular_ofFn_holomorphicLinearCoordinateGerm`). Thus successive
coordinate equations are non-zero-divisors on the successive quotients. This is the local algebra
underlying smooth holomorphic zero sets.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II.
-/

public noncomputable section

open IsLocalRing
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]

/-- Centered coordinates of a holomorphic chart, in any ordered basis, form a regular sequence
in the holomorphic local ring. In particular each coordinate is a non-zero-divisor after
quotienting by the preceding coordinates. -/
theorem isRegular_ofFn_holomorphicLinearCoordinateGerm (e : OpenPartialHomeomorph X E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω X) (x : X) (hx : x ∈ e.source)
    {n : ℕ} (b : Module.Basis (Fin n) ℂ E) :
    RingTheory.Sequence.IsRegular ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)
      (List.ofFn fun i ↦ e.holomorphicLinearCoordinateGerm he x
        (LinearMap.toContinuousLinearMap (b.coord i)) hx) := by
  have := e.isRegularLocalRing_holomorphicStalk he hx
  have hspan :
      (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x)).spanFinrank = n := by
    rw [e.spanFinrank_maximalIdeal_holomorphicStalk he hx, Module.finrank_eq_card_basis b,
      Fintype.card_fin]
  apply TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal
  · rw [Ideal.ofList_ofFn, maximalIdeal_stalk]
    exact (e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hx).symm
  · simp only [List.length_ofFn, hspan, le_refl]

end OpenPartialHomeomorph
