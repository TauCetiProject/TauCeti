/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A normed model for a finite-dimensional real Lie algebra

`TauCeti.Lie.NormedModel` equips a copy of a real Lie algebra with the supremum norm in a chosen
finite basis. The Lie algebra structure is carried over from the original algebra.
-/

public section

noncomputable section

namespace TauCeti.Lie

/-- A copy of a finite-dimensional real Lie algebra on which to place a norm.
Its norm is the supremum norm on coordinates in a chosen finite basis of `L`, independently
of any norm on `L`. -/
def NormedModel (L : Type*) := L

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

instance : LieRing (NormedModel L) := inferInstanceAs (LieRing L)

instance : LieAlgebra ℝ (NormedModel L) := inferInstanceAs (LieAlgebra ℝ L)

namespace NormedModel

/-- The normed model has the original Lie algebra structure. -/
def lieEquiv : NormedModel L ≃ₗ⁅ℝ⁆ L := LieEquiv.refl

variable [FiniteDimensional ℝ L]

instance : FiniteDimensional ℝ (NormedModel L) := inferInstanceAs (FiniteDimensional ℝ L)

/-- The additive group is normed by the supremum norm of the chosen coordinates. -/
instance : NormedAddCommGroup (NormedModel L) :=
  let coordinates := lieEquiv.toLinearEquiv.trans (Module.finBasis ℝ L).equivFun
  NormedAddCommGroup.induced (NormedModel L) _ coordinates coordinates.injective

/-- Scalar multiplication uses the supremum norm in the chosen coordinates. -/
instance : NormedSpace ℝ (NormedModel L) :=
  let coordinates := lieEquiv.toLinearEquiv.trans (Module.finBasis ℝ L).equivFun
  NormedSpace.induced ℝ (NormedModel L) _ coordinates

end NormedModel

variable [FiniteDimensional ℝ L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The adjoint Lie homomorphism with values in the continuous endomorphisms of the normed
model. -/
def continuousAd : NormedModel L →ₗ⁅ℝ⁆ (NormedModel L →L[ℝ] NormedModel L) :=
  (Module.End.toContinuousLinearMap (NormedModel L)).toLieEquiv.toLieHom.comp
    (LieAlgebra.ad ℝ (NormedModel L))

/-- The continuous adjoint acts by the Lie bracket. -/
@[simp]
theorem continuousAd_apply (x y : NormedModel L) : continuousAd x y = ⁅x, y⁆ :=
  (rfl)

end TauCeti.Lie
