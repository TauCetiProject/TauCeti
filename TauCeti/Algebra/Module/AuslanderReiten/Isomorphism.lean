/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Translate
public import TauCeti.Algebra.Module.AuslanderReiten.Full
public import TauCeti.Algebra.Module.AuslanderReiten.Faithful
public import TauCeti.Algebra.Category.ModuleCat.Projective.Stable

/-!
# Transposes and translates detect indecomposable isomorphism classes

For non-projective finite-length indecomposable modules, an isomorphism between transposes
of finite projective presentations implies an isomorphism of the original modules. When
the transposes have finite length over a commutative base ring `R`, the same holds for their
Matlis duals, the Auslander--Reiten translates. For minimal presentations this becomes an iff: the
translate detects isomorphism classes on the non-projective indecomposables. Over an Artin algebra
every finite presentation has a transpose of finite length over `R`.

Minimality is needed only for the forward implication. Arbitrary finite projective
presentations suffice for reflection.

The proofs use the full and faithful stable transpose, the projective stable quotient's
detection of non-projective indecomposable isomorphism classes, and Matlis biduality.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

open CategoryTheory

universe u v w

variable {A : Type u} [Ring A] [Small.{v} A] {M N : ModuleCat.{v} A}

local notation "S" => ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))
local notation "T" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))

/-- Isomorphic transposes of finite projective presentations detect isomorphism of
finite-length indecomposable modules, provided the source module is not projective.
The presentations need not be minimal. -/
theorem nonempty_linearEquiv_of_auslanderReitenTranspose (P : FiniteProjectivePresentation M)
    (Q : FiniteProjectivePresentation N) (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hiM : IsIndecomposableModule A M) (hiN : IsIndecomposableModule A N)
    (hpM : ¬ Module.Projective A M)
    (e : AuslanderReitenTranspose P.p ≃ₗ[Aᵐᵒᵖ] AuslanderReitenTranspose Q.p) :
    Nonempty (M ≃ₗ[A] N) := by
  let i := (T).mapIso e.toModuleIso
  obtain ⟨f, hf⟩ := AuslanderReitenTranspose.stableMap_surjective
    P.exact P.surjective Q.exact Q.surjective i.inv
  obtain ⟨g, hg⟩ := AuslanderReitenTranspose.stableMap_surjective
    Q.exact Q.surjective P.exact P.surjective i.hom
  have hfg : f ≫ g = 𝟙 ((S).obj M) := by
    apply AuslanderReitenTranspose.stableMap_injective P.exact P.surjective P.exact P.surjective
    rw [AuslanderReitenTranspose.stableMap_comp P.exact.linearMap_comp_eq_zero
      Q.exact Q.surjective P.exact P.surjective, hf, hg,
      AuslanderReitenTranspose.stableMap_id, i.hom_inv_id]
  have hgf : g ≫ f = 𝟙 ((S).obj N) := by
    apply AuslanderReitenTranspose.stableMap_injective Q.exact Q.surjective Q.exact Q.surjective
    rw [AuslanderReitenTranspose.stableMap_comp Q.exact.linearMap_comp_eq_zero
      P.exact P.surjective Q.exact Q.surjective, hf, hg,
      AuslanderReitenTranspose.stableMap_id, i.inv_hom_id]
  have hp : ¬ Projective M := fun h ↦ hpM (by let := h; infer_instance)
  obtain ⟨j⟩ := (ModuleCat.nonempty_iso_projectiveStableFunctor_obj_iff M N hM hN
    ((indecomposable_iff_isIndecomposableModule M).mpr hiM)
    ((indecomposable_iff_isIndecomposableModule N).mpr hiN) hp).mp ⟨⟨f, g, hfg, hgf⟩⟩
  exact ⟨j.toLinearEquiv⟩

variable {R : Type*} [CommRing R] [Algebra R A] {E : Type w} [AddCommGroup E] [Module R E]
  [Module.Injective R E] [Small.{w} R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
include hE

/-- Isomorphic Auslander--Reiten translates detect isomorphism of non-projective,
finite-length indecomposable modules when both transposes have finite length over `R`.
No minimality of either finite projective presentation is needed. -/
theorem nonempty_linearEquiv_of_auslanderReitenTranslate (P : FiniteProjectivePresentation M)
    (Q : FiniteProjectivePresentation N) (hTrP : IsFiniteLength R (AuslanderReitenTranspose P.p))
    (hTrQ : IsFiniteLength R (AuslanderReitenTranspose Q.p))
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hiM : IsIndecomposableModule A M) (hiN : IsIndecomposableModule A N)
    (hpM : ¬ Module.Projective A M)
    (e : AuslanderReitenTranslate R E P.p ≃ₗ[A] AuslanderReitenTranslate R E Q.p) :
    Nonempty (M ≃ₗ[A] N) :=
  P.nonempty_linearEquiv_of_auslanderReitenTranspose Q hM hN hiM hiN hpM
    ((MatlisDual.evalEquivOp hE hTrP).trans
      ((MatlisDual.congr e.symm).trans (MatlisDual.evalEquivOp hE hTrQ).symm))

/-- On non-projective finite-length indecomposables, the Auslander--Reiten translate
computed from finite minimal projective presentations detects exactly the module
isomorphism classes, when the transposes have finite length over `R`. Only the source needs an
explicit non-projectivity hypothesis. -/
theorem nonempty_linearEquiv_auslanderReitenTranslate_iff (P : FiniteProjectivePresentation M)
    (Q : FiniteProjectivePresentation N)
    (hTrP : IsFiniteLength R (AuslanderReitenTranspose P.p))
    (hTrQ : IsFiniteLength R (AuslanderReitenTranspose Q.p))
    (hP : IsMinimalProjectivePresentation P.p P.π)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hiM : IsIndecomposableModule A M) (hiN : IsIndecomposableModule A N)
    (hpM : ¬ Module.Projective A M) :
    Nonempty (AuslanderReitenTranslate R E P.p ≃ₗ[A] AuslanderReitenTranslate R E Q.p) ↔
      Nonempty (M ≃ₗ[A] N) :=
  ⟨fun ⟨e⟩ ↦ P.nonempty_linearEquiv_of_auslanderReitenTranslate hE Q hTrP hTrQ hM hN hiM hiN hpM e,
    fun ⟨e⟩ ↦ (hP.comp_linearEquiv e).nonempty_linearEquiv_auslanderReitenTranslate hQ⟩

end TauCeti.FiniteProjectivePresentation
