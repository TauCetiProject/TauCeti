/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Componentwise volume-preserving maps of `L²` products

The volume of the `L²` product `WithLp 2 (U × V)` of two finite-dimensional real inner product
spaces is the product of the volumes of the factors (Mathlib's `WithLp.volume_preserving_ofLp`).
So the componentwise map `(x, y) ↦ (f x, g y)` of two volume-preserving maps preserves volume
(`MeasureTheory.MeasurePreserving.withLpProdMap`), the measure-theoretic counterpart of Mathlib's
`Isometry.withLpProdMap`. A typical instance is a map of `WithLp 2 (ℝ × E)` that keeps the first
coordinate and moves the second by a volume-preserving map of `E`.
-/

public section

namespace MeasureTheory.MeasurePreserving

variable {U V U' V' : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup U']
  [InnerProductSpace ℝ U'] [FiniteDimensional ℝ U'] [MeasurableSpace U'] [BorelSpace U']
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V'] [MeasurableSpace V']
  [BorelSpace V']

/-- On `L²` products of finite-dimensional real inner product spaces, the componentwise map
`(x, y) ↦ (f x, g y)` of two volume-preserving maps preserves volume. -/
theorem withLpProdMap {f : U → U'} {g : V → V'} (hf : MeasurePreserving f)
    (hg : MeasurePreserving g) : MeasurePreserving (WithLp.map 2 (Prod.map f g)) :=
  (WithLp.volume_preserving_toLp U' V').comp
    ((hf.prod hg).comp (WithLp.volume_preserving_ofLp U V))

end MeasureTheory.MeasurePreserving
