/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Relative
public import TauCeti.CategoryTheory.Adjunction.Representable

/-!
# Base change of the relative Picard presheaf

Let `f : X ⟶ S` be a morphism of schemes and `g : S' ⟶ S` a morphism of bases, with base change
`f' : X' = S' ×_S X ⟶ S'` (`pullback.fst g f`). A scheme `T` over `S'` is a scheme over `S`
through `g` (`Over.map g`), and the two base changes of `X` agree:
`T ×_{S'} X' = T ×_{S'} (S' ×_S X) ≅ T ×_S X` (`pullbackRightPullbackFstIso`), compatibly with
the projections to `T`. Pullback along this isomorphism identifies `Pic(T ×_{S'} X') / Pic(T)`
with `Pic(T ×_S X) / Pic(T)`, naturally in `T`. So the relative Picard presheaf of `f'` is the
restriction of the relative Picard presheaf of `f` to schemes over `S'`
(`relativePicardPresheafBaseChangeIso`).

When `f` has a section `x₀`, its base change `x₀' : S' ⟶ X'` is a section of `f'`, and the
same holds for the rigidified Picard functors (`rigidifiedPicardFunctorBaseChangeIso`). The
restriction functor `Over.map g` is left adjoint to `Over.pullback g`, so if an `S`-scheme `P`
represents the rigidified Picard functor of `(X, x₀)`, then `P_{S'} = P ×_S S'` represents that
of `(X', x₀')` (`rigidifiedPicardFunctorBaseChangeRepresentableBy`). In particular, for a
pointed scheme over a field `k` and a field extension `K` of `k`, the base change to `K` of a
`k`-scheme representing its rigidified Picard functor represents that of its base change to `K`.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardPresheafBaseChangeIso`: the relative Picard presheaf
  of `S' ×_S X ⟶ S'` is the relative Picard presheaf of `X ⟶ S` restricted along
  `Over.map g`;
* `TauCeti.AlgebraicGeometry.rigidifiedPicardFunctorBaseChangeIso`: the same for the rigidified
  Picard functors, with the base-changed section; it is pullback of rigidified classes
  (`rigidifiedPicardFunctorBaseChangeIso_hom_app_apply`);
* `TauCeti.AlgebraicGeometry.rigidifiedPicardFunctorBaseChangeRepresentableBy`,
  `TauCeti.AlgebraicGeometry.isRepresentable_rigidifiedPicardFunctor_baseChange`: a representing
  scheme of the rigidified Picard functor base changes to a representing scheme.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S S' X : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/-- Pullback along `T ×_S X ≅ T ×_{S'} (S' ×_S X)` identifies the line-bundle classes pulled back
from `T` on both sides. -/
private lemma range_pullbackHom_baseChange (T : Over S') :
    (LineBundleClass.pullbackHom (pullback.fst T.hom (pullback.fst g f))).range.map
        (LineBundleClass.pullbackHom (pullbackRightPullbackFstIso g f T.hom).inv) =
      (LineBundleClass.pullbackHom (pullback.fst (T.hom ≫ g) f)).range := by
  rw [MonoidHom.map_range, LineBundleClass.pullbackHom_comp, pullbackRightPullbackFstIso_inv_fst]

/-- The component at `T` of `relativePicardPresheafBaseChangeIso`: pullback along
`T ×_S X ≅ T ×_{S'} (S' ×_S X)` on `Pic(-) / Pic(T)`. -/
private def relativePicardBaseChangeMulEquiv (T : Over S') :
    LineBundleClass (pullback T.hom (pullback.fst g f)) ⧸
        (LineBundleClass.pullbackHom (pullback.fst T.hom (pullback.fst g f))).range ≃*
      LineBundleClass (pullback (T.hom ≫ g) f) ⧸
        (LineBundleClass.pullbackHom (pullback.fst (T.hom ≫ g) f)).range :=
  QuotientGroup.congr _ _
    (MonoidHom.toMulEquiv
      (LineBundleClass.pullbackHom (pullbackRightPullbackFstIso g f T.hom).inv)
      (LineBundleClass.pullbackHom (pullbackRightPullbackFstIso g f T.hom).hom)
      (by rw [LineBundleClass.pullbackHom_comp, Iso.hom_inv_id, LineBundleClass.pullbackHom_id])
      (by rw [LineBundleClass.pullbackHom_comp, Iso.inv_hom_id, LineBundleClass.pullbackHom_id]))
    (range_pullbackHom_baseChange f g T)

private lemma relativePicardBaseChangeMulEquiv_mk (T : Over S')
    (a : LineBundleClass (pullback T.hom (pullback.fst g f))) :
    relativePicardBaseChangeMulEquiv f g T (QuotientGroup.mk a) =
      QuotientGroup.mk (LineBundleClass.pullback (pullbackRightPullbackFstIso g f T.hom).inv a) :=
  (QuotientGroup.congr_mk _ _ _ _ a).trans
    (congrArg QuotientGroup.mk (LineBundleClass.pullbackHom_apply _ a))

/-- Pullback along `T ×_S X ≅ T ×_{S'} (S' ×_S X)` commutes with the pullbacks along morphisms
`T ⟶ T'` of schemes over `S'`. -/
private lemma relativePicardBaseChangeMulEquiv_naturality {T T' : (Over S')ᵒᵖ} (φ : T ⟶ T')
    (a : LineBundleClass (pullback T.unop.hom (pullback.fst g f))) :
    relativePicardBaseChangeMulEquiv f g T'.unop
        ((relativePicardPresheaf (pullback.fst g f)).map φ (QuotientGroup.mk a)) =
      (relativePicardPresheaf f).map ((Over.map g).op.map φ)
        (relativePicardBaseChangeMulEquiv f g T.unop (QuotientGroup.mk a)) := by
  rw [relativePicardPresheaf_map_mk, relativePicardBaseChangeMulEquiv_mk,
    relativePicardBaseChangeMulEquiv_mk, relativePicardPresheaf_map_mk,
    LineBundleClass.pullback_comp, LineBundleClass.pullback_comp]
  congr 2
  exact Over.pullbackRightPullbackFstIso_inv_comp_pullback_map f g φ.unop

/-- **Base change of the relative Picard presheaf.** For `f : X ⟶ S` and `g : S' ⟶ S`, the
relative Picard presheaf `T ↦ Pic(T ×_{S'} X') / Pic(T)` of the base change
`X' = S' ×_S X ⟶ S'` is the relative Picard presheaf `T ↦ Pic(T ×_S X) / Pic(T)` of `f`,
restricted to schemes over `S'` along `Over.map g`. The isomorphism is pullback along
`T ×_S X ≅ T ×_{S'} X'` (`relativePicardPresheafBaseChangeIso_hom_app_mk`). -/
def relativePicardPresheafBaseChangeIso :
    relativePicardPresheaf (pullback.fst g f) ≅ (Over.map g).op ⋙ relativePicardPresheaf f :=
  NatIso.ofComponents (fun T ↦ (relativePicardBaseChangeMulEquiv f g T.unop).toCommGrpIso) (by
    intro T T' φ
    ext c
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
    -- The components are typed on the carriers, which the functors' objects only unfold to at
    -- default transparency, so the rewriting lemmas for `MulEquiv.toCommGrpIso` do not apply;
    -- `exact` checks the unfolding at default transparency.
    exact relativePicardBaseChangeMulEquiv_naturality f g φ a)

/-- `relativePicardPresheafBaseChangeIso` sends the class of a line bundle on `T ×_{S'} X'` to
the class of its pullback along `T ×_S X ≅ T ×_{S'} X'`. -/
-- Not `@[simp]`: `simp` rewrites the codomain `((Over.map g).op ⋙ _).obj T` inside the type of the
-- coercion by `Functor.comp_obj`, after which this left-hand side no longer matches.
lemma relativePicardPresheafBaseChangeIso_hom_app_mk (T : (Over S')ᵒᵖ)
    (a : LineBundleClass (pullback T.unop.hom (pullback.fst g f))) :
    (relativePicardPresheafBaseChangeIso f g).hom.app T (QuotientGroup.mk a) =
      (QuotientGroup.mk
          (LineBundleClass.pullback (pullbackRightPullbackFstIso g f T.unop.hom).inv a) :
        (relativePicardPresheaf f).obj (Opposite.op ((Over.map g).obj T.unop))) :=
  -- As in `relativePicardPresheafBaseChangeIso`, the component is
  -- `relativePicardBaseChangeMulEquiv` only after unfolding at default transparency.
  relativePicardBaseChangeMulEquiv_mk f g T.unop a

variable (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)

/-- **Base change of the rigidified Picard functor.** For a section `x₀` of `f : X ⟶ S` and
`g : S' ⟶ S`, the rigidified Picard functor of the base change `X' = S' ×_S X ⟶ S'` with the
base-changed section `x₀' : S' ⟶ X'` is the rigidified Picard functor of `(X, x₀)` restricted to
schemes over `S'` along `Over.map g`. -/
def rigidifiedPicardFunctorBaseChangeIso :
    rigidifiedPicardFunctor (pullback.fst g f) (baseChangeSection f x₀ hx₀ (Over.mk g))
        (baseChangeSection_fst f x₀ hx₀ (Over.mk g)) ≅
      (Over.map g).op ⋙ rigidifiedPicardFunctor f x₀ hx₀ :=
  rigidifiedPicardFunctorIso _ _ _ ≪≫ relativePicardPresheafBaseChangeIso f g ≪≫
    Functor.isoWhiskerLeft (Over.map g).op (rigidifiedPicardFunctorIso f x₀ hx₀).symm

/-- Under the comparison with the relative Picard presheaf, the base change isomorphism of the
rigidified Picard functors is pullback of underlying line bundles. -/
private lemma rigidifiedPicardFunctorIso_hom_app_baseChangeIso_hom_app (T : (Over S')ᵒᵖ)
    (a : RigidifiedLineBundleClass (baseChangeSection (pullback.fst g f)
      (baseChangeSection f x₀ hx₀ (Over.mk g)) (baseChangeSection_fst f x₀ hx₀ (Over.mk g))
        T.unop)) :
    (rigidifiedPicardFunctorIso f x₀ hx₀).hom.app (Opposite.op ((Over.map g).obj T.unop))
        ((rigidifiedPicardFunctorBaseChangeIso f g x₀ hx₀).hom.app T a) =
      (QuotientGroup.mk (LineBundleClass.pullback (pullbackRightPullbackFstIso g f T.unop.hom).inv
          (RigidifiedLineBundleClass.toLineBundleClass a)) :
        (relativePicardPresheaf f).obj (Opposite.op ((Over.map g).obj T.unop))) := by
  have h : (rigidifiedPicardFunctorBaseChangeIso f g x₀ hx₀).hom ≫
      Functor.whiskerLeft (Over.map g).op (rigidifiedPicardFunctorIso f x₀ hx₀).hom =
        (rigidifiedPicardFunctorIso _ _ _).hom ≫ (relativePicardPresheafBaseChangeIso f g).hom := by
    simp [rigidifiedPicardFunctorBaseChangeIso, ← Functor.whiskerLeft_comp]
  -- Both sides are elements of the carriers, which the functors' objects only unfold to at
  -- default transparency, so the composites are compared by `refine` and `exact`.
  refine (ConcreteCategory.congr_hom (NatTrans.congr_app h T) a).trans ?_
  exact (congrArg (ConcreteCategory.hom ((relativePicardPresheafBaseChangeIso f g).hom.app T))
    (rigidifiedPicardFunctorIso_hom_app_apply _ _ _ T a)).trans
      (relativePicardPresheafBaseChangeIso_hom_app_mk f g T _)

/-- `rigidifiedPicardFunctorBaseChangeIso` is pullback of rigidified line-bundle classes along
`T ×_S X ≅ T ×_{S'} X'`, which carries the base-changed section of `X'` to that of `X`. -/
-- Not `@[simp]`, for the reason given at `relativePicardPresheafBaseChangeIso_hom_app_mk`.
lemma rigidifiedPicardFunctorBaseChangeIso_hom_app_apply (T : (Over S')ᵒᵖ)
    (a : RigidifiedLineBundleClass (baseChangeSection (pullback.fst g f)
      (baseChangeSection f x₀ hx₀ (Over.mk g)) (baseChangeSection_fst f x₀ hx₀ (Over.mk g))
        T.unop)) :
    (rigidifiedPicardFunctorBaseChangeIso f g x₀ hx₀).hom.app T a =
      RigidifiedLineBundleClass.pullback
        (baseChangeSection_comp_pullbackRightPullbackFstIso_inv f x₀ hx₀ g T.unop) a := by
  apply (Iso.commGroupIsoToMulEquiv
    ((rigidifiedPicardFunctorIso f x₀ hx₀).app (Opposite.op ((Over.map g).obj T.unop)))).injective
  refine (rigidifiedPicardFunctorIso_hom_app_baseChangeIso_hom_app f g x₀ hx₀ T a).trans ?_
  -- As above, the carriers only unfold to rigidified classes at default transparency.
  exact (congrArg QuotientGroup.mk
    (RigidifiedLineBundleClass.toLineBundleClass_pullback _ a)).symm.trans
      (rigidifiedPicardFunctorIso_hom_app_apply f x₀ hx₀ _ _).symm

/-- **A representing scheme of the rigidified Picard functor base changes to a representing
scheme.** If the `S`-scheme `P` represents the rigidified Picard functor of `(X, x₀)`, then
`P_{S'} = P ×_S S'` represents the rigidified Picard functor of the base change
`(S' ×_S X, x₀')` over `S'`. -/
def rigidifiedPicardFunctorBaseChangeRepresentableBy {P : Over S}
    (e : (rigidifiedPicardFunctor f x₀ hx₀ ⋙ forget CommGrpCat).RepresentableBy P) :
    (rigidifiedPicardFunctor (pullback.fst g f) (baseChangeSection f x₀ hx₀ (Over.mk g))
        (baseChangeSection_fst f x₀ hx₀ (Over.mk g)) ⋙ forget CommGrpCat).RepresentableBy
      ((Over.pullback g).obj P) :=
  ((Over.mapPullbackAdj g).representableByComp e).ofIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rigidifiedPicardFunctorBaseChangeIso f g x₀ hx₀).symm _)

/-- If the rigidified Picard functor of `(X, x₀)` is representable, so is that of its base change
along any `g : S' ⟶ S`. -/
theorem isRepresentable_rigidifiedPicardFunctor_baseChange
    [(rigidifiedPicardFunctor f x₀ hx₀ ⋙ forget CommGrpCat).IsRepresentable] :
    (rigidifiedPicardFunctor (pullback.fst g f) (baseChangeSection f x₀ hx₀ (Over.mk g))
        (baseChangeSection_fst f x₀ hx₀ (Over.mk g)) ⋙ forget CommGrpCat).IsRepresentable :=
  (rigidifiedPicardFunctorBaseChangeRepresentableBy f g x₀ hx₀
    (Functor.representableBy _)).isRepresentable

end

end AlgebraicGeometry

end TauCeti
