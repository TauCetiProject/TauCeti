/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# The coefficient pairing of trivial `𝔽₂` coefficients

Multiplication in `𝔽₂` is a `G`-equivariant biadditive map of the lifted carrier of the trivial
`𝔽₂` coefficient object (`TauCeti.trivialF2Pairing`). This file reads it as a coefficient pairing
`TauCeti.TopPairing` of `TauCeti.trivialF2` itself, which is what the `𝔽₂`-valued cup products of
continuous cohomology are formed from. It is the `ℤ`-coefficient counterpart of
`TauCeti.fpPairing`, whose coefficient object `TauCeti.trivialFp` is a `ZMod p`-module.

## Main definitions

* `TauCeti.trivialF2TopPairing`: multiplication on the trivial integral `𝔽₂` coefficient object.

## Main results

* `TauCeti.trivialF2TopPairing_bil_apply`: the pairing multiplies the underlying values in
  `ZMod 2`.
* `TauCeti.trivialF2TopPairing_flip`: the opposite of the multiplication pairing is itself.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable (G : Type u) [Monoid G]

attribute [local instance] TopRep.distribMulAction

/-- Multiplication on the trivial `𝔽₂` coefficient object, as a continuous equivariant pairing
over `ℤ`. It is the generic discrete-module pairing `TauCeti.ofDiscreteModulePairing` of
`TauCeti.trivialF2Pairing`, read on the coefficient object itself along
`TauCeti.ofDiscreteModule_trivialF2`. This is the coefficient pairing used by the mod-two Kummer
cup. -/
noncomputable def trivialF2TopPairing :
    TopPairing (trivialF2 G) (trivialF2 G) (trivialF2 G) :=
  cast (congrArg (fun X ↦ TopPairing X X X) (ofDiscreteModule_trivialF2 G))
    (ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G))

/-- The coefficient pairing multiplies the underlying values in `ZMod 2`. -/
@[simp]
theorem trivialF2TopPairing_bil_apply (x y : (trivialF2 G).V) :
    (trivialF2TopPairing G).bil x y =
      (trivialF2Equiv G).symm (trivialF2Equiv G x * trivialF2Equiv G y) := by
  rw [trivialF2TopPairing, TopPairing.bil_transport _ (ofDiscreteModule_trivialF2 G)
      (ofDiscreteModule_trivialF2 G) (ofDiscreteModule_trivialF2 G),
    eqToHom_ofDiscreteModule_trivialF2_symm_apply,
    eqToHom_ofDiscreteModule_trivialF2_symm_apply, ofDiscreteModulePairing_bil_apply,
    eqToHom_ofDiscreteModule_trivialF2_apply, trivialF2Pairing_apply]

/-- Multiplication on the trivial `𝔽₂` coefficient object is symmetric. -/
theorem trivialF2TopPairing_bil_comm (x y : (trivialF2 G).V) :
    (trivialF2TopPairing G).bil x y = (trivialF2TopPairing G).bil y x := by
  simp only [trivialF2TopPairing_bil_apply, mul_comm]

/-- The opposite of the multiplication pairing is itself, because multiplication in `ZMod 2` is
commutative. -/
@[simp]
theorem trivialF2TopPairing_flip : (trivialF2TopPairing G).flip = trivialF2TopPairing G :=
  -- `DFunLike.ext` rather than `LinearMap.ext₂`: the latter would synthesize the `ℤ`-module
  -- structure on the carrier as `AddCommGroup.toIntModule`, not the coefficient object's own.
  TopPairing.ext (DFunLike.ext _ _ fun x ↦ DFunLike.ext _ _ fun y ↦ by
    rw [TopPairing.flip_bil, trivialF2TopPairing_bil_comm])

end TauCeti
