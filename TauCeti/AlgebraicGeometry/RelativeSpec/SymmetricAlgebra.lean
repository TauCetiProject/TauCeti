/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.DirectSum
public import TauCeti.AlgebraicGeometry.RelativeSpec.UniversalProperty

/-!
# The relative spectrum of a symmetric algebra

For a quasicoherent sheaf `F` on a scheme `X`, the relative spectrum `Spec_X (Sym F)` of its
symmetric algebra is the scheme over `X` that represents `𝒪`-linear functionals on `F`
(Stacks Project, Tag 01M1, and EGA II, §1.7). For a scheme `q : T ⟶ X`, morphisms
`T ⟶ Spec_X (Sym F)` over `X` correspond to

* morphisms of `𝒪_X`-modules `F ⟶ q_* 𝒪_T` (`relativeSpecSymmetricAlgebraHomEquiv`), naturally
  in `F` and in `T` (`relativeSpecSymmetricAlgebraHomIso`); and
* morphisms of `𝒪_T`-modules `q^* F ⟶ 𝒪_T` (`relativeSpecSymmetricAlgebraPullbackHomEquiv`),
  naturally in `F`.

The first is the universal property of relative Spec, `relativeSpecHomIso`, followed by the
universal property of the symmetric algebra as the free commutative algebra,
`symmetricAlgebraHomEquiv`; the second follows from the first by the adjunction between pullback
and pushforward of modules. This is the contravariant linear scheme `𝕍(F)` of a quasicoherent
sheaf; for a finite locally free `E`, the total space of the vector bundle `E` is the relative
spectrum of the symmetric algebra of the dual of `E`.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraHomEquiv`: morphisms
  `T ⟶ Spec_X (Sym F)` over `X` are module maps `F ⟶ q_* 𝒪_T`, with naturality in the scheme
  (`relativeSpecSymmetricAlgebraHomEquiv_comp`) and in the sheaf
  (`relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map`);
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraHomIso`: the same bijection as a natural
  isomorphism of functors of points;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraPullbackHomEquiv`: morphisms
  `T ⟶ Spec_X (Sym F)` over `X` are linear functionals `q^* F ⟶ 𝒪_T`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- **The universal property of the relative spectrum of a symmetric algebra.** For a
quasicoherent sheaf `F` on `X` and a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ Spec_X (Sym F)` over `X` correspond to morphisms of `𝒪_X`-modules `F ⟶ q_* 𝒪_T`. -/
def relativeSpecSymmetricAlgebraHomEquiv (F : QuasicoherentSheaf X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) ≃
      (F.obj ⟶ (Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)) :=
  (((relativeSpecHomIso X).app (op ((symmetricAlgebra X).obj F))).app (op T)).toEquiv.trans
    (symmetricAlgebraHomEquiv F _)

/-- The module map `F ⟶ q_* 𝒪_T` of a morphism `t : T ⟶ Spec_X (Sym F)` over `X` is the
restriction to `F` of its pullback of regular functions `Sym F ⟶ q_* 𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraHomEquiv_apply (F : QuasicoherentSheaf X) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraHomEquiv F T t =
      symmetricAlgebraι F ≫
        (((symmetricAlgebra X).obj F).obj.relativeSpecHomEquiv T.hom ⟨t.left, Over.w t⟩).hom.hom :=
  (symmetricAlgebraHomEquiv_apply _).trans
    (congrArg (fun f ↦ symmetricAlgebraι F ≫ f.hom.hom) (relativeSpecHomIso_hom_app_app _ _ t))

/-- The morphism over `X` of a module map `φ : F ⟶ q_* 𝒪_T` is the relative-spectrum lift of
the algebra map `Sym F ⟶ q_* 𝒪_T` extending `φ`. -/
lemma relativeSpecSymmetricAlgebraHomEquiv_symm_apply_left (F : QuasicoherentSheaf X)
    (T : Over X) (φ : F.obj ⟶ (Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules)) :
    ((relativeSpecSymmetricAlgebraHomEquiv F T).symm φ).left =
      CommMon.relativeSpecLift (symmetricAlgebraLift (B := T.hom.pushforwardStructureAlgebra) φ) :=
  congrArg Over.Hom.left ((congrArg (((relativeSpecHomIso X).inv.app _).app _)
    (symmetricAlgebraHomEquiv_symm_apply φ)).trans (relativeSpecHomIso_inv_app_app _ _ _))

/-- The bijection `relativeSpecSymmetricAlgebraHomEquiv` is natural in the scheme over `X`:
composing with `g : T' ⟶ T` over `X` corresponds to composing the module map `F ⟶ q_* 𝒪_T` with
pullback of regular functions along `g`. -/
lemma relativeSpecSymmetricAlgebraHomEquiv_comp (F : QuasicoherentSheaf X) {T' T : Over X}
    (g : T' ⟶ T) (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraHomEquiv F T' (g ≫ t) =
      relativeSpecSymmetricAlgebraHomEquiv F T t ≫
        (Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g)).hom.hom := by
  rw [relativeSpecSymmetricAlgebraHomEquiv_apply, relativeSpecSymmetricAlgebraHomEquiv_apply,
    CommMon.relativeSpecHomEquiv_apply, CommMon.relativeSpecHomEquiv_apply]
  have h := Scheme.Hom.pushforwardStructureAlgebraMap_comp g.left t.left (Over.w g) (Over.w t)
  -- `(g ≫ t).left` is `g.left ≫ t.left` by `Over.comp_left`, but the proof argument of
  -- `pushforwardStructureAlgebraMap` depends on it, so `h` is applied up to unfolding.
  erw [h]
  exact (congrArg (symmetricAlgebraι F ≫ ·) (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm

/-- The bijection `relativeSpecSymmetricAlgebraHomEquiv` is natural in the quasicoherent sheaf:
composing with the relative-spectrum map of `Sym a` for `a : F' ⟶ F` corresponds to
precomposing the module map with `a`. -/
lemma relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map {F' F : QuasicoherentSheaf X}
    (a : F' ⟶ F) (T : Over X) (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraHomEquiv F' T
        (t ≫ (MorphismProperty.Over.forget _ _ X).map
          ((relativeSpec X).map ((symmetricAlgebra X).map a).op)) =
      a.hom ≫ relativeSpecSymmetricAlgebraHomEquiv F T t := by
  rw [relativeSpecSymmetricAlgebraHomEquiv_apply, relativeSpecSymmetricAlgebraHomEquiv_apply]
  have h := CommMon.relativeSpecHomEquiv_comp_relativeSpecMap ((symmetricAlgebra X).map a).hom
    ⟨t.left, Over.w t⟩
  have e : (t ≫ (MorphismProperty.Over.forget _ _ X).map
      ((relativeSpec X).map ((symmetricAlgebra X).map a).op)).left =
        t.left ≫ CommMon.relativeSpecMap ((symmetricAlgebra X).map a).hom := by
    rw [Over.comp_left]
    exact congrArg (t.left ≫ ·) (relativeSpec_map_left _)
  exact (congrArg (fun s ↦ symmetricAlgebraι F' ≫
      (((symmetricAlgebra X).obj F').obj.relativeSpecHomEquiv T.hom s).hom.hom)
        (Subtype.ext e)).trans ((congrArg (fun f ↦ symmetricAlgebraι F' ≫ f.hom.hom) h).trans
          (symmetricAlgebraι_naturality_assoc a _).symm)

variable (X) in
/-- **The functor-of-points universal property of `Spec_X (Sym F)`**, natural in the
quasicoherent sheaf `F` and in the scheme `T` over `X`: morphisms `T ⟶ Spec_X (Sym F)` over `X`
correspond to morphisms of `𝒪_X`-modules `F ⟶ q_* 𝒪_T`. Its components are
`relativeSpecSymmetricAlgebraHomEquiv`. -/
def relativeSpecSymmetricAlgebraHomIso :
    (symmetricAlgebra X).op ⋙ relativeSpec X ⋙ MorphismProperty.Over.forget _ _ X ⋙ yoneda ≅
      (ObjectProperty.ι _ : QuasicoherentSheaf X ⥤ X.Modules).op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (overFunctions X ⋙ CommMon.forget X.Modules) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun T ↦
    (relativeSpecSymmetricAlgebraHomEquiv F.unop T.unop).toIso)
    (fun g ↦ by ext t; exact relativeSpecSymmetricAlgebraHomEquiv_comp _ g.unop t))
    (fun a ↦ by
      ext T t
      exact relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map a.unop _ t)

/-- The components of `relativeSpecSymmetricAlgebraHomIso` are
`relativeSpecSymmetricAlgebraHomEquiv`. -/
lemma relativeSpecSymmetricAlgebraHomIso_hom_app_app (F : (QuasicoherentSheaf X)ᵒᵖ)
    (T : (Over X)ᵒᵖ) (t : T.unop ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F.unop)))) :
    ((relativeSpecSymmetricAlgebraHomIso X).hom.app F).app T t =
      relativeSpecSymmetricAlgebraHomEquiv F.unop T.unop t :=
  (rfl)

/-- The inverse components of `relativeSpecSymmetricAlgebraHomIso` are the inverse of
`relativeSpecSymmetricAlgebraHomEquiv`. -/
lemma relativeSpecSymmetricAlgebraHomIso_inv_app_app (F : (QuasicoherentSheaf X)ᵒᵖ)
    (T : (Over X)ᵒᵖ)
    (φ : F.unop.obj ⟶ (Scheme.Modules.pushforward T.unop.hom).obj (𝟙_ T.unop.left.Modules)) :
    ((relativeSpecSymmetricAlgebraHomIso X).inv.app F).app T φ =
      (relativeSpecSymmetricAlgebraHomEquiv F.unop T.unop).symm φ :=
  (rfl)

/-- **`Spec_X (Sym F)` represents linear functionals.** For a quasicoherent sheaf `F` on `X` and a
scheme `q : T ⟶ X` over `X`, morphisms `T ⟶ Spec_X (Sym F)` over `X` correspond to morphisms of
`𝒪_T`-modules `q^* F ⟶ 𝒪_T`. It is `relativeSpecSymmetricAlgebraHomEquiv` followed by the
adjunction between pullback and pushforward of modules. -/
def relativeSpecSymmetricAlgebraPullbackHomEquiv (F : QuasicoherentSheaf X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj
        ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) ≃
      ((Scheme.Modules.pullback T.hom).obj F.obj ⟶ 𝟙_ T.left.Modules) :=
  (relativeSpecSymmetricAlgebraHomEquiv F T).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _).symm

/-- The linear functional `q^* F ⟶ 𝒪_T` of a morphism `T ⟶ Spec_X (Sym F)` over `X` is the
transpose of its module map `F ⟶ q_* 𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraPullbackHomEquiv_apply (F : QuasicoherentSheaf X) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraPullbackHomEquiv F T t =
      ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _).symm
        (relativeSpecSymmetricAlgebraHomEquiv F T t) :=
  (rfl)

/-- The morphism over `X` of a linear functional `q^* F ⟶ 𝒪_T` is the morphism of its transpose
`F ⟶ q_* 𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraPullbackHomEquiv_symm_apply (F : QuasicoherentSheaf X)
    (T : Over X) (φ : (Scheme.Modules.pullback T.hom).obj F.obj ⟶ 𝟙_ T.left.Modules) :
    (relativeSpecSymmetricAlgebraPullbackHomEquiv F T).symm φ =
      (relativeSpecSymmetricAlgebraHomEquiv F T).symm
        ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _ φ) :=
  (rfl)

/-- The linear-functional form of the universal property is natural in the quasicoherent sheaf:
composing with the relative-spectrum map of `Sym a` for `a : F' ⟶ F` corresponds to
precomposing the linear functional with `q^* a`. -/
lemma relativeSpecSymmetricAlgebraPullbackHomEquiv_comp_relativeSpec_map
    {F' F : QuasicoherentSheaf X} (a : F' ⟶ F) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((relativeSpec X).obj (op ((symmetricAlgebra X).obj F)))) :
    relativeSpecSymmetricAlgebraPullbackHomEquiv F' T
        (t ≫ (MorphismProperty.Over.forget _ _ X).map
          ((relativeSpec X).map ((symmetricAlgebra X).map a).op)) =
      (Scheme.Modules.pullback T.hom).map a.hom ≫
        relativeSpecSymmetricAlgebraPullbackHomEquiv F T t := by
  rw [relativeSpecSymmetricAlgebraPullbackHomEquiv_apply,
    relativeSpecSymmetricAlgebraPullbackHomEquiv_apply,
    relativeSpecSymmetricAlgebraHomEquiv_comp_relativeSpec_map]
  exact Adjunction.homEquiv_naturality_left_symm _ _ _

end

end TauCeti.AlgebraicGeometry
