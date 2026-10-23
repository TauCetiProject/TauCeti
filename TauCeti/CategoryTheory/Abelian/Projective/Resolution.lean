/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Chain maps between projective resolutions over the identity

Mathlib compares two projective resolutions `P` and `Q` of the same object `X` by the lift of the
identity of `X` (`CategoryTheory.ProjectiveResolution.homotopyEquiv`), which it constructs
abstractly from the projectivity of the terms. Often one has an explicit chain map
`f : P.complex ⟶ Q.complex` instead, compatible with the augmentations. Such an `f` is itself a
lift of the identity of `X`, so it is homotopic to Mathlib's comparison
(`CategoryTheory.ProjectiveResolution.homotopyOfComm`) and is a homotopy equivalence
(`CategoryTheory.ProjectiveResolution.homotopyEquivOfComm`).
-/

public section

noncomputable section

namespace CategoryTheory.ProjectiveResolution

variable {C : Type*} [Category* C] [Abelian C] {X : C} (P Q : ProjectiveResolution X)
  (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π)

/-- A chain map between projective resolutions of `X` compatible with the augmentations is
homotopic to the comparison `(homotopyEquiv P Q).hom`, the lift of the identity of `X`. -/
def homotopyOfComm : Homotopy f (homotopyEquiv P Q).hom :=
  liftHomotopy (𝟙 X) _ _ (by simp [hf]) (by simp)

/-- A chain map between projective resolutions of `X` compatible with the augmentations is a
homotopy equivalence; its homotopy inverse is the lift of the identity of `X`. -/
def homotopyEquivOfComm : HomotopyEquiv P.complex Q.complex :=
  (homotopyEquiv P Q).copy (homotopyOfComm P Q f hf).symm

/-- The forward map of the homotopy equivalence is the given chain map. -/
@[simp]
theorem homotopyEquivOfComm_hom : (homotopyEquivOfComm P Q f hf).hom = f :=
  (rfl)

/-- The homotopy inverse is the lift of the identity from `Q` to `P`. -/
@[simp]
theorem homotopyEquivOfComm_inv : (homotopyEquivOfComm P Q f hf).inv = lift (𝟙 X) Q P :=
  (rfl)

end CategoryTheory.ProjectiveResolution
