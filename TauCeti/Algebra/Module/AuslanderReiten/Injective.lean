/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Translate
public import TauCeti.Algebra.Module.AuslanderReiten.ProjectiveSummand
public import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation
public import TauCeti.Algebra.Module.Dual.ProjectiveInjective

/-!
# Injectivity of the Auslander–Reiten translate

Over a finite-dimensional algebra, the translate of a finite minimal projective presentation
is injective exactly when the presented module is projective. In that case the translate is
zero. Thus `D Tr` takes non-projective modules to non-injective modules, as required for the
Auslander–Reiten correspondence.

Linear duality exchanges injectivity and projectivity. The transpose of a minimal presentation
has no nonzero projective summands, so an injective translate must vanish. These results do not
require indecomposability or algebraic closedness of the ground field.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.IsMinimalProjectivePresentation

variable {k A P₀ P₁ M : Type*} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]
  [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁]
  [AddCommGroup M] [Module A M]
  {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- The translate of a finite minimal projective presentation is injective exactly when
the presented module is projective. In particular a non-projective module has non-injective
translate, even without an indecomposability hypothesis. -/
theorem moduleInjective_auslanderReitenTranslate_iff_projective
    (h : IsMinimalProjectivePresentation p₁ p₀) :
    Module.Injective A (AuslanderReitenTranslate k p₁) ↔ Module.Projective A M := by
  let := h.projective
  let := h.isProjectiveCover.projective
  have : FiniteDimensional k (AuslanderReitenTranspose p₁) :=
    Module.Finite.trans Aᵐᵒᵖ (AuslanderReitenTranspose p₁)
  exact ((LinearEquiv.refl k (AuslanderReitenTranslate k p₁)).moduleInjective_iff_projective_of_dual
    (fun a φ x ↦ AuslanderReitenTranslate.smul_apply a φ x)).trans
      (h.isSuperfluous_ker.projective_auslanderReitenTranspose_iff_subsingleton.trans
        h.subsingleton_auslanderReitenTranspose_iff_projective)

end TauCeti.IsMinimalProjectivePresentation
