/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Basic

import TauCeti.Topology.Algebra.Group.Generation

/-!
# Finite-order Hecke characters

A finite-order Hecke character is locally constant: its kernel is an open subgroup of the idele
class group.  Together with the ray-subgroup criterion
`HeckeCharacter.mem_range_ofRayClassCharacter_iff`, this is part of the equivalence between finite
order, open kernel, and factorization through a ray class group.

## Main results

* `HeckeCharacter.isOpen_ker_of_isFiniteOrder`: a finite-order Hecke character has open kernel.
* `HeckeCharacter.isOpen_ker_ofRayClassCharacter`: in particular, a character pulled back from a
  ray class group has open kernel.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField Set
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

/-- A finite-order Hecke character has open kernel, and is therefore locally constant. -/
theorem isOpen_ker_of_isFiniteOrder {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    IsOpen ((χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).ker : Set (IdeleClassGroup (𝓞 K) K)) :=
  ContinuousMonoidHom.isOpen_ker_of_isOfFinOrder hχ

/-- **A Hecke character pulled back from a ray class character has open kernel.** -/
theorem isOpen_ker_ofRayClassCharacter {𝔪 : Modulus K} (η : RayClassCharacter 𝔪) :
    IsOpen (((ofRayClassCharacter 𝔪 η : HeckeCharacter K) :
      IdeleClassGroup (𝓞 K) K →* ℂˣ).ker : Set (IdeleClassGroup (𝓞 K) K)) :=
  isOpen_ker_of_isFiniteOrder (isFiniteOrder_ofRayClassCharacter η)

end HeckeCharacter

end TauCeti.GlobalNumberFields
