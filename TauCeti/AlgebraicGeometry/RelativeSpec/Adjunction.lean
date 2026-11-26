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

/-- The function algebra of a quasi-compact quasi-separated scheme over `X` is quasi-coherent. -/
instance (T : QcqsOver X) : T.hom.pushforwardStructureAlgebra.X.IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.pushforward T.hom).obj (𝟙_ _)).IsQuasicoherent

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

/-- The bijection of the adjunction `(qcqsFunctions X).rightOp ⊣ relativeSpecQcqs X`: the
components of `relativeSpecHomIso`, read in `QcqsOver X`. -/
private def relativeSpecQcqsHomEquiv (T : QcqsOver X) (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((qcqsFunctions X).rightOp.obj T ⟶ A) ≃ (T ⟶ (relativeSpecQcqs X).obj A) where
  toFun φ := (MorphismProperty.Over.forget _ ⊤ X).preimage
    (show (MorphismProperty.Over.forget _ ⊤ X).obj T ⟶
        (MorphismProperty.Over.forget _ ⊤ X).obj ((relativeSpecQcqs X).obj A) from
      ((relativeSpecHomIso X).inv.app A).app (op ((MorphismProperty.Over.forget _ _ X).obj T))
        φ.unop.hom)
  invFun t := Quiver.Hom.op ⟨((relativeSpecHomIso X).hom.app A).app
    (op ((MorphismProperty.Over.forget _ _ X).obj T)) ((MorphismProperty.Over.forget _ ⊤ X).map t)⟩
  left_inv φ := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    simp only [Quiver.Hom.unop_op]
    erw [Functor.map_preimage]
    exact types_congr_hom (NatTrans.congr_app (NatTrans.congr_app
      (relativeSpecHomIso X).inv_hom_id A) _) φ.unop.hom
  right_inv t := by
    apply (MorphismProperty.Over.forget _ ⊤ X).map_injective
    erw [Functor.map_preimage]
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
        simp only [relativeSpecQcqsHomEquiv, Equiv.coe_fn_mk, Functor.map_comp]
        erw [Functor.map_preimage, Functor.map_preimage]
        exact types_congr_hom (NatTrans.congr_app ((relativeSpecHomIso X).inv.naturality a)
          (op ((MorphismProperty.Over.forget _ ⊤ X).obj T))) φ.unop.hom }

/-- The unit of `relativeSpecQcqsAdjunction X` at `q : T ⟶ X` is the canonical morphism
`T ⟶ Spec_X(q_* 𝒪_T)`, the lift of the identity of `q_* 𝒪_T` (Stacks Project, Tag 01LY). -/
lemma relativeSpecQcqsAdjunction_unit_app_left (T : QcqsOver X) :
    ((relativeSpecQcqsAdjunction X).unit.app T).left =
      CommMon.relativeSpecLift (𝟙 T.hom.pushforwardStructureAlgebra) := by
  have := congrArg CommaMorphism.left (relativeSpecHomIso_inv_app_app
    (op ((qcqsFunctions X).obj (op T))) (op ((MorphismProperty.Over.forget _ ⊤ X).obj T))
    (𝟙 T.hom.pushforwardStructureAlgebra))
  have hunit : (relativeSpecQcqsAdjunction X).unit.app T =
      relativeSpecQcqsHomEquiv T _ (𝟙 _) := rfl
  refine Eq.trans ?_ this
  rw [hunit]
  exact congrArg CommaMorphism.left
    (Functor.map_preimage (MorphismProperty.Over.forget (@QuasiCompact ⊓ @QuasiSeparated) ⊤ X) _)

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
    have : IsIso e.inv.left := ⟨e.hom.left,
      by rw [← MorphismProperty.Comma.comp_left, e.inv_hom_id]; rfl,
      by rw [← MorphismProperty.Comma.comp_left, e.hom_inv_id]; rfl⟩
    rw [← MorphismProperty.Over.w e.inv]
    have h1 : IsAffineHom e.inv.left := inferInstance
    have h2 : IsAffineHom ((relativeSpecQcqs X).obj A).hom := ((relativeSpec X).obj A).prop
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
