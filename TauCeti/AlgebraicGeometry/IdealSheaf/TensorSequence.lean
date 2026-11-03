/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Tensoring the exact sequence of a closed subscheme

For an ideal sheaf `I` and a finite locally free module sheaf `E`, tensoring the ideal sequence
with `E` gives the short exact sequence

`0 → E ⊗ I → E ⊗ 𝒪_X → E ⊗ i_*𝒪_{V(I)} → 0`.

The target retains the scheme structure of the closed subscheme, including nilpotents. This
sequence is used to prescribe restrictions of global sections, and in particular jets along
nonreduced effective divisors. No finiteness or regularity of the closed subscheme is needed.

The exactness follows from dualizability: tensoring with a finite locally free sheaf is both
a left and a right adjoint.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Section 5, and IV, Section 3.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Tensoring the ideal sequence of a closed subscheme with a finite locally free sheaf
preserves short exactness. -/
theorem shortExact_tensor_toPushforwardSubscheme (E : X.Modules)
    [E.IsLocallyFree] [E.IsFiniteType] :
    ((ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).map (tensorLeft E)).ShortExact := by
  let : ExactPairing ((ihom E).obj (𝟙_ X.Modules)) E :=
    TauCeti.exactPairingOfIsIsoDualTensorIhom (Y := E)
  let : ExactPairing E ((ihom E).obj (𝟙_ X.Modules)) :=
    BraidedCategory.exactPairing_swap _ _
  have : Limits.PreservesLimits (tensorLeft E) :=
    (tensorLeftAdjunction E ((ihom E).obj (𝟙_ X.Modules))).rightAdjoint_preservesLimits
  exact I.shortExact_toPushforwardSubscheme.map_of_exact (tensorLeft E)

/-- Sections of a finite locally free sheaf restrict surjectively to a closed subscheme
if first cohomology of its tensor product with the ideal sheaf vanishes. -/
theorem surjective_tensorRestriction_of_subsingleton_cohomology_one (E : X.Modules)
    [E.IsLocallyFree] [E.IsFiniteType]
    (hvan : Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (E ⊗ I.sheaf) 1)) :
    Function.Surjective (Scheme.Modules.Hom.app
      ((ρ_ E).inv ≫ E ◁
        SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) ⊤) := by
  have hsurj := TauCeti.AlgebraicGeometry.Scheme.Modules.sections_surjective
    (I.shortExact_tensor_toPushforwardSubscheme E) hvan
  have hunitor : Function.Surjective (Scheme.Modules.Hom.app (ρ_ E).inv ⊤) :=
    (ConcreteCategory.bijective_of_isIso ((ρ_ E).inv.app ⊤)).2
  exact hsurj.comp hunitor

end AlgebraicGeometry.Scheme.IdealSheafData
