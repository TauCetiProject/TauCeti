/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DualPresentation
public import TauCeti.Algebra.Module.AuslanderReiten.Indecomposable

/-!
# Indecomposability and projectivity of right transposes

The inverse translate `Tr D` is the `A`-valued right transpose of a finite minimal projective
presentation of a right module, the Matlis dual `D N`. This gives an actual left `A`-module, with
no change of its scalars to the double opposite.

The right-transpose results here hold over any ring: a minimal right transpose is projective
exactly when its source is projective, and for a finite-length indecomposable source it is
indecomposable exactly when the source is not projective. Applied to `D N`, they place the inverse
translate of a non-injective indecomposable among the non-projective indecomposables
(`ModuleCat.indecomposable_arInverseTranslate_iff`, `ModuleCat.projective_arInverseTranslate_iff`).

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

universe u v w

section RightTranspose

variable {A : Type u} [Ring A] {N : ModuleCat.{v} Aᵐᵒᵖ}

/-- Minimal right presentations of isomorphic modules compute isomorphic left transposes. -/
theorem nonempty_linearEquiv_rightTranspose (Q : FiniteProjectivePresentation N)
    {N' : ModuleCat.{w} Aᵐᵒᵖ} (P : FiniteProjectivePresentation N')
    (f : N ≃ₗ[Aᵐᵒᵖ] N')
    (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    (hP : IsMinimalProjectivePresentation P.p P.π) :
    Nonempty (Q.rightTranspose ≃ₗ[A] P.rightTranspose) := by
  obtain ⟨e⟩ := (hQ.comp_linearEquiv f).nonempty_linearEquiv_auslanderReitenTranspose hP
  exact ⟨(Q.rightTransposeEquiv.trans e).trans P.rightTransposeEquiv.symm⟩

/-- A minimal right transpose vanishes exactly on projective right modules. -/
theorem subsingleton_rightTranspose_iff_projective (Q : FiniteProjectivePresentation N)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π) :
    Subsingleton Q.rightTranspose ↔ Module.Projective Aᵐᵒᵖ N :=
  Q.rightTransposeEquiv.toEquiv.subsingleton_congr.trans
    hQ.subsingleton_auslanderReitenTranspose_iff_projective

/-- A finite minimal right transpose is projective exactly when its source is projective.
Neither finite length nor indecomposability of the source is required. -/
@[simp]
theorem projective_rightTranspose_iff (Q : FiniteProjectivePresentation N)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π) :
    Module.Projective A Q.rightTranspose ↔ Module.Projective Aᵐᵒᵖ N := by
  have he : Module.Projective A Q.rightTranspose ↔
      Module.Projective Aᵐᵒᵖᵐᵒᵖ (AuslanderReitenTranspose Q.p) := by
    constructor <;> intro h <;> let := h
    · exact Module.Projective.of_equiv Q.rightTransposeEquiv
    · exact Module.Projective.of_equiv Q.rightTransposeEquiv.symm
  exact he.trans (hQ.isSuperfluous_ker.projective_auslanderReitenTranspose_iff_subsingleton.trans
    hQ.subsingleton_auslanderReitenTranspose_iff_projective)

/-- The finite minimal right transpose of a finite-length indecomposable module is
indecomposable exactly when the source is not projective. -/
@[simp]
theorem isIndecomposableModule_rightTranspose_iff (Q : FiniteProjectivePresentation N)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    [Small.{v} Aᵐᵒᵖ] (hN : IsFiniteLength Aᵐᵒᵖ N)
    (hiN : IsIndecomposableModule Aᵐᵒᵖ N) :
    IsIndecomposableModule A Q.rightTranspose ↔ ¬ Module.Projective Aᵐᵒᵖ N := by
  have he : IsIndecomposableModule A Q.rightTranspose ↔
      IsIndecomposableModule Aᵐᵒᵖᵐᵒᵖ (AuslanderReitenTranspose Q.p) :=
    ⟨fun h ↦ h.of_linearEquiv Q.rightTransposeEquiv,
      fun h ↦ h.of_linearEquiv Q.rightTransposeEquiv.symm⟩
  exact he.trans (Q.isIndecomposableModule_auslanderReitenTranspose_iff hQ hN hiN)

end RightTranspose

end TauCeti.FiniteProjectivePresentation
