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
import TauCeti.LinearAlgebra.Dual.Equivalence

/-!
# Transposes and translates detect indecomposable isomorphism classes

For non-projective finite-length indecomposable modules, an isomorphism between transposes
of finite projective presentations implies an isomorphism of the original modules. When
the transposes are reflexive over the scalar ring, the same holds for their scalar duals,
the Auslander--Reiten translates. For minimal presentations this becomes an iff: the
translate detects isomorphism classes on the non-projective indecomposables.

Minimality is needed only for the forward implication. Arbitrary finite projective
presentations suffice for reflection. The scalar base need not be a field; reflexivity is
automatic for finite-dimensional transposes over a field.

The proofs use the full and faithful stable transpose, the projective stable quotient's
detection of non-projective indecomposable isomorphism classes, and scalar double duality.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.1.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

open CategoryTheory

universe u v

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

variable {k : Type*} [CommSemiring k] [Algebra k A]

/-- Isomorphic Auslander--Reiten translates detect isomorphism of non-projective,
finite-length indecomposable modules when both transposes are scalar-reflexive.
No minimality of either finite projective presentation is needed. -/
theorem nonempty_linearEquiv_of_auslanderReitenTranslate (P : FiniteProjectivePresentation M)
    (Q : FiniteProjectivePresentation N)
    [Module.IsReflexive k (AuslanderReitenTranspose P.p)]
    [Module.IsReflexive k (AuslanderReitenTranspose Q.p)]
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hiM : IsIndecomposableModule A M) (hiN : IsIndecomposableModule A N)
    (hpM : ¬ Module.Projective A M)
    (e : AuslanderReitenTranslate k P.p ≃ₗ[A] AuslanderReitenTranslate k Q.p) :
    Nonempty (M ≃ₗ[A] N) := by
  let d := (LinearEquiv.refl k (AuslanderReitenTranslate k P.p)).ofEquivariantDual
    (LinearEquiv.refl k (AuslanderReitenTranslate k Q.p))
    (fun a φ x ↦ AuslanderReitenTranslate.smul_apply a φ x)
    (fun a φ x ↦ AuslanderReitenTranslate.smul_apply a φ x) e
  exact P.nonempty_linearEquiv_of_auslanderReitenTranspose Q hM hN hiM hiN hpM d.symm

/-- On non-projective finite-length indecomposables, the Auslander--Reiten translate
computed from finite minimal projective presentations detects exactly the module
isomorphism classes, when the transposes are scalar-reflexive. Only the source needs an
explicit non-projectivity hypothesis. -/
theorem nonempty_linearEquiv_auslanderReitenTranslate_iff (P : FiniteProjectivePresentation M)
    (Q : FiniteProjectivePresentation N)
    [Module.IsReflexive k (AuslanderReitenTranspose P.p)]
    [Module.IsReflexive k (AuslanderReitenTranspose Q.p)]
    (hP : IsMinimalProjectivePresentation P.p P.π)
    (hQ : IsMinimalProjectivePresentation Q.p Q.π)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength A N)
    (hiM : IsIndecomposableModule A M) (hiN : IsIndecomposableModule A N)
    (hpM : ¬ Module.Projective A M) :
    Nonempty (AuslanderReitenTranslate k P.p ≃ₗ[A] AuslanderReitenTranslate k Q.p) ↔
      Nonempty (M ≃ₗ[A] N) := by
  constructor
  · rintro ⟨e⟩
    exact P.nonempty_linearEquiv_of_auslanderReitenTranslate Q hM hN hiM hiN hpM e
  · rintro ⟨e⟩
    exact (hP.comp_linearEquiv e).nonempty_linearEquiv_auslanderReitenTranslate hQ

end TauCeti.FiniteProjectivePresentation
