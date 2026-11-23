/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Translate
public import TauCeti.Algebra.Module.AuslanderReiten.ProjectiveSummand
public import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation
public import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

/-!
# Injectivity of the Auslander–Reiten translate

Over an Artin algebra, the translate of a finite minimal projective presentation is injective
exactly when the presented module is projective. In that case the translate is zero. Thus `D Tr`
takes non-projective modules to non-injective modules, as required for the Auslander–Reiten
correspondence.

Matlis duality exchanges injectivity and projectivity of finitely generated modules. The transpose
of a minimal presentation has no nonzero projective summands, so an injective translate must
vanish. These results do not require indecomposability.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.IsMinimalProjectivePresentation

universe v

variable {R A P₀ P₁ M : Type*} {E : Type v} [CommRing R] [IsArtinianRing R] [Ring A]
  [Algebra R A] [Module.Finite R A] [AddCommGroup E] [Module R E] [Module.Injective R E]
  [Small.{v} R]
  [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁]
  [AddCommGroup M] [Module A M]
  {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- The translate of a finite minimal projective presentation over an Artin algebra is injective
exactly when the presented module is projective. In particular a non-projective module has
non-injective translate, even without an indecomposability hypothesis. -/
theorem moduleInjective_auslanderReitenTranslate_iff_projective
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (h : IsMinimalProjectivePresentation p₁ p₀) :
    Module.Injective A (AuslanderReitenTranslate R E p₁) ↔ Module.Projective A M := by
  let := h.projective
  let := h.isProjectiveCover.projective
  exact (moduleInjective_matlisDual_iff_projective_op hE).trans
    (h.isSuperfluous_ker.projective_auslanderReitenTranspose_iff_subsingleton.trans
      h.subsingleton_auslanderReitenTranspose_iff_projective)

end TauCeti.IsMinimalProjectivePresentation
