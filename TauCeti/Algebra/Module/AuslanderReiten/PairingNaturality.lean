/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.CocyclePairing
public import TauCeti.Algebra.Module.AuslanderReiten.PresentationNaturality
public import TauCeti.Algebra.Module.HomCocycle.Presentation

/-!
# Naturality of the Auslander–Reiten pairing in presentations

For a commutative square from `p` to `q`, precomposition on Hom cocycle
classes is dual to postcomposition with the induced map `D Tr(p) → D Tr(q)`.
Together with coefficient naturality, this makes the cocycle pairing natural
in both variables. No minimality or finite-dimensionality of the algebra or
coefficient module is required.

The comparison follows the naturality of Nakayama Hom duality and the
canonical embedding of the translate into the source Nakayama module.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace LinearMap

open TauCeti

variable {k A P₀ P₁ Q₀ Q₁ N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [Module.Finite A Q₀] [Module.Projective A Q₀]
  [AddCommGroup Q₁] [Module A Q₁] [Module.Finite A Q₁] [Module.Projective A Q₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- Postcomposition with the translate of a presentation square is dual to
precomposition on Hom cocycle classes. -/
theorem auslanderReitenCocyclePairing_presentation_naturality
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁)
    (g : N →ₗ[A] AuslanderReitenTranslate k p) :
    auslanderReitenCocyclePairing q ((auslanderReitenTranslateMap f₀ f₁ hf).comp g) =
      (homCocycleQuotientPrecomp f₀ f₁ hf).dualMap (auslanderReitenCocyclePairing p g) := by
  have hnat :
      (nakayamaHomEquiv k A Q₁ N).symm
          ((auslanderReitenTranslateToNakayama q).comp
            ((auslanderReitenTranslateMap f₀ f₁ hf).comp g)) =
        (f₁.lcomp k N).dualMap
          ((nakayamaHomEquiv k A P₁ N).symm
            ((auslanderReitenTranslateToNakayama p).comp g)) := by
    apply (nakayamaHomEquiv k A Q₁ N).injective
    simp only [LinearEquiv.apply_symm_apply, nakayamaHomEquiv_dualMap_lcomp]
    rw [← comp_assoc, auslanderReitenTranslateToNakayama_comp_auslanderReitenTranslateMap,
      comp_assoc]
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ h => simp [hnat, lcomp_apply']

end LinearMap
