/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.Group
public import TauCeti.Algebra.Quaternion.CentralSimple

/-!
# Brauer classes of quaternion symbols

For a field `K` with `2` invertible, this file bundles the quaternion symbol with unit parameters
`a b : Kˣ` as a central simple algebra and defines its Brauer class. The general centrality and
simplicity results used here are in `TauCeti.Algebra.Quaternion.CentralSimple`.

## Main results

* `TauCeti.BrauerGroup.quaternionCSA`: the bundled central simple algebra of a quaternion symbol
  with unit parameters.
* `TauCeti.BrauerGroup.quaternionClass`: the Brauer class of that symbol.

## References

The classical central-simple background is in T. Y. Lam, *Introduction to Quadratic Forms over
Fields* (2005), Chapter III, §2, and P. Gille and T. Szamuely, *Central Simple Algebras and Galois
Cohomology* (2006), §1.1.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace BrauerGroup

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- The bundled central simple algebra underlying the quaternion symbol `(a,b)`. -/
noncomputable def quaternionCSA (a b : Kˣ) : CSA K :=
  CSA.of K ℍ[K,(a : K),(b : K)]

/-- The bundled algebra underlying `quaternionCSA` is the corresponding quaternion symbol. -/
@[simp] theorem quaternionCSA_def (a b : Kˣ) :
    quaternionCSA a b = CSA.of K ℍ[K,(a : K),(b : K)] := (rfl)

/-- The Brauer class of the quaternion symbol `(a,b)` for unit parameters `a b : Kˣ`. -/
noncomputable def quaternionClass (a b : Kˣ) : BrauerGroup K :=
  BrauerGroup.mk (quaternionCSA a b)

/-- The defining equation for `quaternionClass`. -/
@[simp] theorem quaternionClass_def (a b : Kˣ) :
    quaternionClass a b = BrauerGroup.mk (CSA.of K ℍ[K,(a : K),(b : K)]) := (rfl)

end BrauerGroup

end TauCeti
