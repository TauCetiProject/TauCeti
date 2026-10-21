/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
public import TauCeti.AlgebraicGeometry.Modules.ClosedImmersion
import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic

/-!
# Higher direct images along closed immersions

All positive higher direct images of a module sheaf along a closed immersion vanish.
Consequently, over a locally Noetherian target, all higher direct images of a coherent
coefficient are coherent. The coefficient and the immersion need not be flat over any base.

The proof uses exactness of closed-embedding pushforward of abelian sheaves, reflected
through the exact faithful functor forgetting module structures. Mathlib's injective
resolution comparison then computes the higher direct images.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Lemma 2.10 and Proposition 8.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- Positive higher direct images along a closed immersion vanish, for arbitrary
module sheaves. -/
theorem isZero_higherDirectImage_succ_of_isClosedImmersion (M : X.Modules) (q : ℕ) :
    IsZero ((f.higherDirectImage (q + 1)).obj M) := by
  have := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  exact (Scheme.Modules.pushforward f).isZero_rightDerived_succ M q

/-- Over a locally Noetherian target, every higher direct image along a closed immersion
of a quasicoherent module of finite type is finitely presented. In positive degree the
image is zero; in degree zero this is coherent finite pushforward. -/
theorem isFinitePresentation_higherDirectImage_of_isClosedImmersion
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    ((f.higherDirectImage q).obj M).IsFinitePresentation := by
  cases q with
  | zero =>
    exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
      ((f.higherDirectImageZeroIso).app M).symm inferInstance
  | succ q =>
    have hN := f.isZero_higherDirectImage_succ_of_isClosedImmersion M q
    have hZ := TauCeti.SheafOfModules.isZero_free (S := Y.ringCatSheaf) PEmpty.{u + 1}
    exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
      (hZ.iso hN) inferInstance

end AlgebraicGeometry.Scheme.Hom
