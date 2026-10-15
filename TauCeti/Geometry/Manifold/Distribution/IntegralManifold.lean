/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Integral manifolds of a distribution

An integral manifold of a tangent distribution `D` is a `C^n` immersion of a nonempty charted space
whose differential has image exactly `D` at every point.  The source has its own topology and
charted-space structure: it is not given the subspace topology from the ambient manifold, and the
immersion need not be injective.  This is the notion needed by the Frobenius theorem and by the
construction of immersed Lie subgroups.

This file provides both the unbundled predicate `TauCeti.IsIntegralManifold` for a specified
immersion and `TauCeti.IntegralManifold`, which packages a `k`-dimensional source manifold and its
parametrization.  The rank theorem shows that, for regularity `n ≠ 0`, the dimension of any
finite-dimensional source equals the rank of the distribution at any image point; it is not extra
data hidden in the definition.

## Main definitions

* `TauCeti.IsIntegralManifold`: an immersion of a nonempty charted space whose tangent image equals
  the given distribution.
* `TauCeti.IntegralManifold`: a packaged integral manifold with Euclidean model of dimension `k`.

## Main results

* `TauCeti.IsIntegralManifold.finrank_model_eq`: for regularity `n ≠ 0`, the source model
  dimension equals the rank of the distribution at any image point.
* `TauCeti.isIntegralManifold_id`: the identity is an integral manifold of the full tangent
  distribution.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

universe u v

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {k : ℕ}

section Unbundled

/-- A map is an **integral manifold** of `D` when its source is a nonempty charted space, it is a
`C^n` immersion, and the image of its differential at every point is exactly the prescribed tangent
subspace.

Nonemptiness rules out the empty map, which would otherwise satisfy the remaining conditions
vacuously for every distribution.

The source topology and charted-space structure are independent of the ambient topology.  In
particular, this predicate neither requires the map to be injective nor equips its range with the
subspace topology. -/
def IsIntegralManifold {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    (n : ℕ∞ω) {N : Type v} [TopologicalSpace N] [ChartedSpace H' N]
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) (f : N → M) : Prop :=
  Nonempty N ∧ Manifold.IsImmersion J I n f ∧
    ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap = D (f y)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type v} [TopologicalSpace N] [ChartedSpace H' N]
  {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {f : N → M}

/-- Characterization of an integral manifold as an immersion of a nonempty charted space with the
prescribed differential range. -/
theorem isIntegralManifold_iff : IsIntegralManifold J n D f ↔
    Nonempty N ∧ Manifold.IsImmersion J I n f ∧
      ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap = D (f y) :=
  Iff.rfl

/-- The source of an integral manifold is nonempty. -/
theorem IsIntegralManifold.nonempty (hf : IsIntegralManifold J n D f) : Nonempty N :=
  hf.1

/-- The parametrization of an integral manifold is an immersion. -/
theorem IsIntegralManifold.isImmersion (hf : IsIntegralManifold J n D f) :
    Manifold.IsImmersion J I n f :=
  hf.2.1

/-- The tangent image of an integral manifold is the prescribed distribution fiber. -/
theorem IsIntegralManifold.range_mfderiv (hf : IsIntegralManifold J n D f) (y : N) :
    LinearMap.range (mfderiv J I f y).toLinearMap = D (f y) :=
  hf.2.2 y

/-- The parametrization of an integral manifold is of class `C^n`. -/
theorem IsIntegralManifold.contMDiff (hf : IsIntegralManifold J n D f) :
    ContMDiff J I n f :=
  hf.isImmersion.contMDiff

/-- For regularity `n ≠ 0`, the model dimension of an integral manifold `f` equals the rank of
the distribution at the image point `f y` of any source point `y`. -/
theorem IsIntegralManifold.finrank_model_eq
    (hf : IsIntegralManifold J n D f) (hn : n ≠ 0) (y : N)
    (hD : Module.finrank ℝ (D (f y)) = k) : Module.finrank ℝ E' = k := by
  -- Integrality identifies the fiber of `D` with the range of the injective differential.
  rw [← hD, ← hf.range_mfderiv y,
    LinearMap.finrank_range_of_inj (hf.isImmersion.mfderiv_injective hn y)]
  exact finrank_tangentSpace (I := J) y

/-- The identity map of a nonempty manifold is an integral manifold of the full tangent
distribution. -/
theorem isIntegralManifold_id [IsManifold I n M] [Nonempty M] :
    IsIntegralManifold I n (fun x : M ↦ (⊤ : Submodule ℝ (TangentSpace I x))) id := by
  refine ⟨inferInstance, Manifold.IsImmersion.id, fun x ↦ ?_⟩
  rw [mfderiv_id]
  exact LinearMap.range_id

end Unbundled

section Bundled

/-- A packaged `k`-dimensional integral manifold of `D`.

Its carrier is nonempty and has an independent `C^n` manifold structure modelled on `ℝ^k`; the
map into the ambient manifold is only required to be an immersion.  Injectivity,
embeddedness, connectedness, and maximality are deliberately separate properties. -/
structure IntegralManifold (n : ℕ∞ω)
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) (k : ℕ) where
  /-- The carrier of the integral manifold. -/
  carrier : Type v
  /-- The topology of the carrier, which need not be the subspace topology from `M`. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The carrier is charted by the `k`-dimensional Euclidean model. -/
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin k)) carrier]
  /-- The carrier is a manifold of regularity `n`. -/
  [isManifold : IsManifold (𝓡 k) n carrier]
  /-- The carrier is nonempty, so a packaged integral manifold is never vacuous. -/
  [nonempty : Nonempty carrier]
  /-- The parametrizing immersion into the ambient manifold. -/
  map : carrier → M
  /-- The parametrization is a `C^n` immersion. -/
  isImmersion : Manifold.IsImmersion (𝓡 k) I n map
  /-- The image of the differential is exactly the distribution fiber. -/
  range_mfderiv : ∀ y,
    LinearMap.range (mfderiv (𝓡 k) I map y).toLinearMap = D (map y)

attribute [instance] IntegralManifold.topologicalSpace IntegralManifold.chartedSpace
  IntegralManifold.isManifold IntegralManifold.nonempty
attribute [simp] IntegralManifold.range_mfderiv

namespace IntegralManifold

variable {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}

/-- The map of a packaged integral manifold satisfies the unbundled integral-manifold
predicate. -/
theorem isIntegralManifold (N : IntegralManifold (I := I) n D k) :
    IsIntegralManifold (𝓡 k) n D N.map :=
  ⟨N.nonempty, N.isImmersion, N.range_mfderiv⟩

/-- The map of a packaged integral manifold is of class `C^n`. -/
theorem contMDiff_map (N : IntegralManifold (I := I) n D k) :
    ContMDiff (𝓡 k) I n N.map :=
  N.isImmersion.contMDiff

end IntegralManifold

end Bundled

end TauCeti
