/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
public import TauCeti.AlgebraicGeometry.RelativeSpec.UniversalProperty

/-!
# Relative Spec as a right adjoint

Let `X` be a scheme and let `QcqsOver X` be the category of schemes `q : T ⟶ X` with `q`
quasi-compact and quasi-separated, with all morphisms over `X`. For such `q` the algebra
`q_* 𝒪_T` is quasi-coherent (`Scheme.Modules.isQuasicoherent_pushforward`), so the
function-algebra functor `overFunctions X` restricts to
`TauCeti.AlgebraicGeometry.qcqsFunctions X : (QcqsOver X)ᵒᵖ ⥤ QuasicoherentAlgebra X`. Affine
morphisms are quasi-compact and quasi-separated, so relative Spec lands in `QcqsOver X`
(`TauCeti.AlgebraicGeometry.relativeSpecQcqs X`).

The universal property of relative Spec, `relativeSpecHomIso`, says exactly that these two functors
are adjoint: `relativeSpecQcqs X` is right adjoint to `(qcqsFunctions X).rightOp`
(`TauCeti.AlgebraicGeometry.relativeSpecQcqsAdjunction`). Relative Spec is fully faithful, being
an equivalence onto affine schemes over `X` (`relativeSpecEquiv`), so affine schemes over `X` form
a reflective subcategory of `QcqsOver X` with reflector `T ↦ Spec_X(q_* 𝒪_T)`, and the unit at `T`
is an isomorphism exactly when `q` is affine
(`TauCeti.AlgebraicGeometry.isIso_unit_app_iff_isAffineHom`).

The restriction to quasi-compact quasi-separated `q` is needed for `qcqsFunctions` to land in
quasi-coherent algebras: for `T` a disjoint union of countably many copies of `Spec ℤ` over
`Spec ℤ`, the sections of `q_* 𝒪_T` over `D(p)` are `∏ ℤ[1/p]`, which is larger than
`(∏ ℤ)[1/p]`.

## Main definitions

* `TauCeti.AlgebraicGeometry.QcqsOver X`: quasi-compact quasi-separated schemes over `X`.
* `TauCeti.AlgebraicGeometry.qcqsFunctions X`: the function-algebra functor on them.
* `TauCeti.AlgebraicGeometry.relativeSpecQcqs X`: relative Spec, read in `QcqsOver X`.
* `TauCeti.AlgebraicGeometry.relativeSpecQcqsAdjunction X`: the adjunction
  `(qcqsFunctions X).rightOp ⊣ relativeSpecQcqs X`.

## Main results

* `TauCeti.AlgebraicGeometry.nonempty_adjunction_relativeSpecQcqs`: relative Spec is a right
  adjoint on quasi-compact quasi-separated schemes over `X`.
* `TauCeti.AlgebraicGeometry.relativeSpecQcqsAdjunction_homEquiv_apply_left`,
  `TauCeti.AlgebraicGeometry.relativeSpecQcqsAdjunction_homEquiv_symm_apply_unop_hom`,
  `TauCeti.AlgebraicGeometry.relativeSpecQcqsAdjunction_unit_app_left` and
  `TauCeti.AlgebraicGeometry.relativeSpecQcqsAdjunction_counit_app_unop_hom`: the hom-set
  bijection, unit and counit in terms of `relativeSpecHomIso`.
* `TauCeti.AlgebraicGeometry.isIso_unit_app_iff_isAffineHom`: the unit of any such adjunction at
  `T` is an isomorphism exactly when `T ⟶ X` is affine.

## References

* The Stacks Project, Tags 01LC, 01LW, 01LX, 01LY, 01S7 and 01S8.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- Schemes over `X` whose structure morphism is quasi-compact and quasi-separated, with all
morphisms over `X`. -/
abbrev QcqsOver (X : Scheme.{u}) :=
  MorphismProperty.Over (@QuasiCompact ⊓ @QuasiSeparated : MorphismProperty Scheme.{u}) ⊤ X

variable {X : Scheme.{u}}

instance (T : QcqsOver X) : QuasiCompact T.hom := T.prop.1

instance (T : QcqsOver X) : QuasiSeparated T.hom := T.prop.2

variable (X) in
/-- The function-algebra functor `q ↦ q_* 𝒪_T` on quasi-compact quasi-separated schemes over `X`,
landing in quasi-coherent algebras by `Scheme.Modules.isQuasicoherent_pushforward`: the
corestriction of `overFunctions X`. -/
@[expose]
def qcqsFunctions : (QcqsOver X)ᵒᵖ ⥤ QuasicoherentAlgebra X :=
  ObjectProperty.lift _ ((MorphismProperty.Over.forget _ _ X).op ⋙ overFunctions X)
    (fun T ↦ inferInstanceAs T.unop.hom.pushforwardStructureAlgebra.X.IsQuasicoherent)

@[simp]
lemma qcqsFunctions_obj_obj (T : (QcqsOver X)ᵒᵖ) :
    ((qcqsFunctions X).obj T).obj = T.unop.hom.pushforwardStructureAlgebra :=
  (rfl)

variable (X) in
/-- Relative Spec, read in `QcqsOver X`: an affine morphism is quasi-compact and separated, hence
quasi-separated. -/
@[expose]
def relativeSpecQcqs : (QuasicoherentAlgebra X)ᵒᵖ ⥤ QcqsOver X :=
  relativeSpec X ⋙ MorphismProperty.Comma.changeProp _ _
    (fun _ _ _ (_ : IsAffineHom _) ↦ ⟨inferInstance, inferInstance⟩) le_rfl le_rfl

@[simp]
lemma qcqsFunctions_map_hom {T T' : (QcqsOver X)ᵒᵖ} (g : T ⟶ T') :
    ((qcqsFunctions X).map g).hom =
      Scheme.Hom.pushforwardStructureAlgebraMap g.unop.left (MorphismProperty.Over.w g.unop) :=
  (rfl)

@[simp]
lemma relativeSpecQcqs_obj_left (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpecQcqs X).obj A).left = A.unop.obj.relativeSpec :=
  (rfl)

@[simp]
lemma relativeSpecQcqs_map_left {A B : (QuasicoherentAlgebra X)ᵒᵖ} (f : A ⟶ B) :
    ((relativeSpecQcqs X).map f).left = CommMon.relativeSpecMap f.unop.hom :=
  (rfl)

@[simp]
lemma relativeSpecQcqs_obj_hom (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpecQcqs X).obj A).hom = A.unop.obj.relativeSpecToBase :=
  (rfl)

variable (X) in
/-- Relative Spec is fully faithful on `QcqsOver X`: it is an equivalence onto affine schemes
over `X`, and these form a full subcategory of `QcqsOver X`. -/
def relativeSpecQcqsFullyFaithful : (relativeSpecQcqs X).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful (relativeSpec X)).comp
    (MorphismProperty.Comma.fullyFaithfulChangeProp _ _ _)

instance : (relativeSpecQcqs X).Full := (relativeSpecQcqsFullyFaithful X).full

instance : (relativeSpecQcqs X).Faithful := (relativeSpecQcqsFullyFaithful X).faithful

/-- The morphism `T ⟶ Spec_X A` over `X` of an algebra map `A ⟶ q_* 𝒪_T`, given by the inverse
components of `relativeSpecHomIso`. The ascription identifies the target of that component,
`Spec_X A` read in `Over X` through affine schemes, with `Spec_X A` read through `QcqsOver X`;
the two objects agree definitionally. -/
private def relativeSpecQcqsLift (T : QcqsOver X) (A : (QuasicoherentAlgebra X)ᵒᵖ)
    (φ : (qcqsFunctions X).rightOp.obj T ⟶ A) : T ⟶ (relativeSpecQcqs X).obj A :=
  (MorphismProperty.Over.forget _ ⊤ X).preimage
    (show (MorphismProperty.Over.forget _ ⊤ X).obj T ⟶
        (MorphismProperty.Over.forget _ ⊤ X).obj ((relativeSpecQcqs X).obj A) from
      ((relativeSpecHomIso X).inv.app A).app (op ((MorphismProperty.Over.forget _ _ X).obj T))
        φ.unop.hom)

/-- The morphism of `relativeSpecQcqsLift`, read in `Over X`, is the inverse component of
`relativeSpecHomIso`. This is the one place where `Functor.map_preimage` meets the ascription in
`relativeSpecQcqsLift`, hence the `erw`. -/
private lemma forget_map_relativeSpecQcqsLift (T : QcqsOver X) (A : (QuasicoherentAlgebra X)ᵒᵖ)
    (φ : (qcqsFunctions X).rightOp.obj T ⟶ A) :
    (MorphismProperty.Over.forget _ ⊤ X).map (relativeSpecQcqsLift T A φ) =
      ((relativeSpecHomIso X).inv.app A).app (op ((MorphismProperty.Over.forget _ _ X).obj T))
        φ.unop.hom := by
  unfold relativeSpecQcqsLift
  erw [Functor.map_preimage]

/-- The bijection of the adjunction `(qcqsFunctions X).rightOp ⊣ relativeSpecQcqs X`: the
components of `relativeSpecHomIso`, read in `QcqsOver X`. -/
private def relativeSpecQcqsHomEquiv (T : QcqsOver X) (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((qcqsFunctions X).rightOp.obj T ⟶ A) ≃ (T ⟶ (relativeSpecQcqs X).obj A) where
  toFun := relativeSpecQcqsLift T A
  invFun t := Quiver.Hom.op ⟨((relativeSpecHomIso X).hom.app A).app
    (op ((MorphismProperty.Over.forget _ _ X).obj T)) ((MorphismProperty.Over.forget _ ⊤ X).map t)⟩
  left_inv φ := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    simp only [Quiver.Hom.unop_op, forget_map_relativeSpecQcqsLift]
    exact types_congr_hom (NatTrans.congr_app (NatTrans.congr_app
      (relativeSpecHomIso X).inv_hom_id A) _) φ.unop.hom
  right_inv t := by
    apply (MorphismProperty.Over.forget _ ⊤ X).map_injective
    rw [forget_map_relativeSpecQcqsLift]
    exact types_congr_hom (NatTrans.congr_app (NatTrans.congr_app
      (relativeSpecHomIso X).hom_inv_id A) _)
      ((MorphismProperty.Over.forget (@QuasiCompact ⊓ @QuasiSeparated) ⊤ X).map t)

variable (X) in
/-- **Relative Spec is a right adjoint** on quasi-compact quasi-separated schemes over `X`, with
hom-set bijection the components of `relativeSpecHomIso`. -/
def relativeSpecQcqsAdjunction : (qcqsFunctions X).rightOp ⊣ relativeSpecQcqs X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := relativeSpecQcqsHomEquiv
      homEquiv_naturality_left_symm := by
        intro T' T A g t
        apply Quiver.Hom.unop_inj
        apply InducedCategory.hom_ext
        exact types_congr_hom (((relativeSpecHomIso X).hom.app A).naturality
          ((MorphismProperty.Over.forget _ ⊤ X).map g).op)
          ((MorphismProperty.Over.forget _ ⊤ X).map t)
      homEquiv_naturality_right := by
        intro T A A' φ a
        apply (MorphismProperty.Over.forget _ ⊤ X).map_injective
        simp only [relativeSpecQcqsHomEquiv, Equiv.coe_fn_mk, Functor.map_comp,
          forget_map_relativeSpecQcqsLift]
        exact types_congr_hom (NatTrans.congr_app ((relativeSpecHomIso X).inv.naturality a)
          (op ((MorphismProperty.Over.forget _ ⊤ X).obj T))) φ.unop.hom }

/-- The hom-set bijection of `relativeSpecQcqsAdjunction X` sends an algebra map
`φ : A ⟶ q_* 𝒪_T` to the lift `T ⟶ Spec_X A` (Stacks Project, Tag 01LW). Not a `simp` lemma: the
type of `homEquiv T A` contains `(qcqsFunctions X).rightOp.obj T`, which `simp` rewrites by
`Functor.rightOp_obj`, so no left-hand side is in simp normal form. -/
lemma relativeSpecQcqsAdjunction_homEquiv_apply_left (T : QcqsOver X)
    (A : (QuasicoherentAlgebra X)ᵒᵖ) (φ : (qcqsFunctions X).rightOp.obj T ⟶ A) :
    ((relativeSpecQcqsAdjunction X).homEquiv T A φ).left = CommMon.relativeSpecLift φ.unop.hom := by
  rw [relativeSpecQcqsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact (congrArg CommaMorphism.left (forget_map_relativeSpecQcqsLift T A φ)).trans
    (congrArg CommaMorphism.left (relativeSpecHomIso_inv_app_app A _ φ.unop.hom))

/-- The inverse of the hom-set bijection sends a morphism `t : T ⟶ Spec_X A` over `X` to its
pullback of regular functions `A ⟶ q_* 𝒪_T`, the component of `relativeSpecHomIso`. Not a `simp`
lemma, for the reason given at `relativeSpecQcqsAdjunction_homEquiv_apply_left`. -/
lemma relativeSpecQcqsAdjunction_homEquiv_symm_apply_unop_hom (T : QcqsOver X)
    (A : (QuasicoherentAlgebra X)ᵒᵖ) (t : T ⟶ (relativeSpecQcqs X).obj A) :
    (((relativeSpecQcqsAdjunction X).homEquiv T A).symm t).unop.hom =
      A.unop.obj.relativeSpecHomEquiv T.hom ⟨t.left, MorphismProperty.Over.w t⟩ := by
  rw [relativeSpecQcqsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact relativeSpecHomIso_hom_app_app A _
    ((MorphismProperty.Over.forget (@QuasiCompact ⊓ @QuasiSeparated) ⊤ X).map t)

/-- The counit of `relativeSpecQcqsAdjunction X` at `A` is the pullback of regular functions along
the identity of `Spec_X A`, the canonical map from `A` to the function algebra of `Spec_X A`
(Stacks Project, Tag 01LX). -/
lemma relativeSpecQcqsAdjunction_counit_app_unop_hom (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpecQcqsAdjunction X).counit.app A).unop.hom =
      A.unop.obj.relativeSpecHomEquiv A.unop.obj.relativeSpecToBase ⟨𝟙 _, Category.id_comp _⟩ := by
  rw [← Adjunction.homEquiv_symm_id]
  exact relativeSpecQcqsAdjunction_homEquiv_symm_apply_unop_hom _ A (𝟙 _)

/-- The unit of `relativeSpecQcqsAdjunction X` at `q : T ⟶ X` is the canonical morphism
`T ⟶ Spec_X(q_* 𝒪_T)`, the lift of the identity of `q_* 𝒪_T` (Stacks Project, Tag 01LY). -/
@[simp]
lemma relativeSpecQcqsAdjunction_unit_app_left (T : QcqsOver X) :
    ((relativeSpecQcqsAdjunction X).unit.app T).left =
      CommMon.relativeSpecLift (𝟙 T.hom.pushforwardStructureAlgebra) := by
  rw [← Adjunction.homEquiv_id]
  -- `(qcqsFunctions X).rightOp.obj T` is `op ((qcqsFunctions X).obj (op T))`, whose object is
  -- `q_* 𝒪_T` by the `(rfl)` lemmas `Functor.rightOp_obj` and `qcqsFunctions_obj_obj`; the
  -- identity sits in a dependent position, where those lemmas cannot be rewritten with.
  exact relativeSpecQcqsAdjunction_homEquiv_apply_left T _ (𝟙 _)

variable (X) in
/-- **Relative Spec is a right adjoint** on quasi-compact quasi-separated schemes over `X`
(Stacks Project, Tags 01LW and 01LY). -/
theorem nonempty_adjunction_relativeSpecQcqs :
    Nonempty ((qcqsFunctions X).rightOp ⊣ relativeSpecQcqs X) :=
  ⟨relativeSpecQcqsAdjunction X⟩

/-- A quasi-compact quasi-separated scheme over `X` is in the essential image of relative Spec
exactly when its structure morphism is affine. -/
lemma relativeSpecQcqs_essImage_iff (T : QcqsOver X) :
    (relativeSpecQcqs X).essImage T ↔ IsAffineHom T.hom := by
  constructor
  · rintro ⟨A, ⟨e⟩⟩
    have : IsAffineHom ((relativeSpecQcqs X).obj A).hom := ((relativeSpec X).obj A).prop
    rw [← MorphismProperty.Over.w e.inv]
    infer_instance
  · intro hT
    obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := relativeSpec X)
      (MorphismProperty.Over.mk ⊤ T.hom hT)
    exact ⟨A, ⟨(MorphismProperty.Comma.changeProp _ _
      (fun _ _ _ (_ : IsAffineHom _) ↦ ⟨inferInstance, inferInstance⟩) le_rfl le_rfl).mapIso e⟩⟩

/-- **The unit detects affineness**: for any adjunction `(qcqsFunctions X).rightOp ⊣
relativeSpecQcqs X`, the unit `T → Spec_X(q_* 𝒪_T)` is an isomorphism exactly when `q` is affine,
so affine schemes over `X` are reflective in `QcqsOver X` (Stacks Project, Tags 01LX and 01S8).
On `ℙ¹_k → Spec k` the unit is `ℙ¹_k → Spec k`, not an isomorphism. -/
theorem isIso_unit_app_iff_isAffineHom
    (adj : (qcqsFunctions X).rightOp ⊣ relativeSpecQcqs X) (T : QcqsOver X) :
    IsIso (adj.unit.app T) ↔ IsAffineHom T.hom :=
  adj.isIso_unit_app_iff_mem_essImage.trans (relativeSpecQcqs_essImage_iff T)

end

end TauCeti.AlgebraicGeometry
