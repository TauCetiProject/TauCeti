/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Jacobson.Radical
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.RingTheory.Ideal.Extended
import TauCeti.RingTheory.Jacobson.Finite

/-!
# The Jacobson radical of a monoid algebra and coefficient maps

For a finite monoid `G`, the monoid algebra `O[G]` is a finite `O`-module, so the extension of an
ideal in the Jacobson radical of `O` lies in the Jacobson radical of `O[G]`
(`TauCeti.Ring.map_algebraMap_le_jacobson`).

## Main results

* `TauCeti.MonoidAlgebra.ker_mapRingHom_le_jacobson`: the kernel of a coefficient map
  `O[G] → k[G]` lies in the Jacobson radical when the kernel of `O → k` does, for a finite monoid
  `G`; for instance when `O` is a local ring and `k` its residue field.
-/

public section

namespace TauCeti.MonoidAlgebra

variable {O k G : Type*} [CommRing O] [Semiring k] [Monoid G] [Finite G]

/-- The kernel of the coefficient map `O[G] → k[G]` along `φ : O →+* k` lies in the Jacobson
radical of `O[G]` whenever `ker φ` lies in the Jacobson radical of `O`, for a finite monoid `G`:
that kernel is the extension of `ker φ` to `O[G]`, which is a finite `O`-module. -/
theorem ker_mapRingHom_le_jacobson {φ : O →+* k} (hφ : RingHom.ker φ ≤ Ring.jacobson O) :
    RingHom.ker (MonoidAlgebra.mapRingHom G φ) ≤ Ring.jacobson (MonoidAlgebra O G) := by
  intro x hx
  rw [RingHom.mem_ker, mapRingHom_eq_zero_iff, ← Ideal.mem_map_algebraMap_iff] at hx
  exact Ring.map_algebraMap_le_jacobson hφ hx

end TauCeti.MonoidAlgebra
