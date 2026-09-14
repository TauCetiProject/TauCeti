/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic

/-!
# Isomorphisms of models

This file identifies the categorical isomorphisms between models with the isomorphisms of their
total spaces.  The generic-fibre condition in `Model.Hom` is preserved by the inverse because
base change is functorial; consequently model isomorphisms are exactly the morphisms whose total
maps are isomorphisms.  This is the categorical form needed when comparing models with a fixed
generic-fibre identification.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable {M N : Model R K C toK}

attribute [instance] Model.flat Model.locallyOfFinitePresentation Model.quasiCompact
  Model.quasiSeparated

/-- The inverse of an isomorphism of total spaces is a morphism over the DVR. -/
private lemma inv_overBase (f : Hom M N) [IsIso f.hom] :
    inv f.hom ≫ M.toBase = N.toBase := by
  rw [← f.overBase]
  exact IsIso.inv_hom_id_assoc f.hom N.toBase

/-- Base change preserves the composition law also for unbundled maps over the base. -/
private lemma baseChangeHom_inv_comp (f : Hom M N) [IsIso f.hom] :
    N.baseChangeHom (inv f.hom) (inv_overBase f) ≫
        M.baseChangeHom f.hom f.overBase = 𝟙 _ := by
  calc
    N.baseChangeHom (inv f.hom) (inv_overBase f) ≫
        M.baseChangeHom f.hom f.overBase =
      N.baseChangeHom (inv f.hom ≫ f.hom) _ := by
        rw [baseChangeHom_comp_raw]
    _ = N.baseChangeHom (𝟙 N.total) _ := by simp only [IsIso.inv_hom_id]
    _ = 𝟙 _ := baseChangeHom_id N

/-- The inverse of a total-space isomorphism respects the chosen generic fibres. -/
private lemma inv_genericFiber (f : Hom M N) [IsIso f.hom] :
    N.baseChangeHom (inv f.hom) (inv_overBase f) ≫ M.genericFiberIso.hom.left =
      N.genericFiberIso.hom.left := by
  calc
    N.baseChangeHom (inv f.hom) (inv_overBase f) ≫ M.genericFiberIso.hom.left =
        N.baseChangeHom (inv f.hom) (inv_overBase f) ≫
          (M.baseChangeHom f.hom f.overBase ≫ N.genericFiberIso.hom.left) := by
            rw [f.genericFiber]
    _ = (N.baseChangeHom (inv f.hom) (inv_overBase f) ≫
          M.baseChangeHom f.hom f.overBase) ≫ N.genericFiberIso.hom.left := by
            simp only [Category.assoc]
    _ = N.genericFiberIso.hom.left := by
      rw [baseChangeHom_inv_comp f, Category.id_comp]

/-- A total-space isomorphism gives a categorical isomorphism of models. -/
private noncomputable def homOfIsIso (f : Hom M N) [IsIso f.hom] : N ⟶ M where
  hom := inv f.hom
  overBase := inv_overBase f
  genericFiber := inv_genericFiber f

/-- A morphism of models is an isomorphism exactly when its total-space map is one. -/
theorem isIso_iff_isIso_hom (f : M ⟶ N) : IsIso f ↔ IsIso f.hom := by
  constructor
  · intro hf
    let _ : IsIso f := hf
    refine ⟨⟨(inv f).hom, ?_, ?_⟩⟩
    · exact congrArg Hom.hom (IsIso.hom_inv_id f)
    · exact congrArg Hom.hom (IsIso.inv_hom_id f)
  · intro hf
    let _ : IsIso f.hom := hf
    refine ⟨⟨homOfIsIso f, ?_, ?_⟩⟩
    · apply Hom.ext
      change f.hom ≫ inv f.hom = 𝟙 _
      exact IsIso.hom_inv_id f.hom
    · apply Hom.ext
      change inv f.hom ≫ f.hom = 𝟙 _
      exact IsIso.inv_hom_id f.hom

/-- A model morphism is an isomorphism whenever its map on total spaces is one. -/
instance isIso_of_isIso_hom (f : M ⟶ N) [IsIso f.hom] : IsIso f :=
  (isIso_iff_isIso_hom f).2 inferInstance

end Model

end TauCeti
