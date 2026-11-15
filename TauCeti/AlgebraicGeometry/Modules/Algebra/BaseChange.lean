/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra
public import TauCeti.AlgebraicGeometry.Modules.Algebra.Functoriality
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Algebra.Quasicoherent

/-!
# Flat base change for algebras of regular functions

For a quasi-compact quasi-separated morphism `f : X ⟶ S`, the actual direct image
`f_* 𝒪_X` is a quasi-coherent algebra. A commutative square induces an algebra map
`g^*(f_* 𝒪_X) ⟶ f'_* 𝒪_X'`. For a cartesian square with flat `g`, this map is an
isomorphism of algebras, not just of modules.

The comparison is constructed by transposing pullback of regular functions under the
algebra pullback–pushforward adjunction. Its underlying module map is the existing
`Scheme.Modules.pushforwardBaseChange`, followed by the identification `g'^*𝒪_X ≅ 𝒪_X'`.
Thus the algebra statement uses the module flat-base-change theorem without rebuilding it.

## References

* The Stacks Project, Lemma 26.24.1 (01LC), quasi-coherence of direct images.
* The Stacks Project, Lemma 30.5.2 (02KH), flat base change in degree zero.
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X X' S S' : Scheme.{u}}

variable {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}
    [QuasiCompact f] [QuasiSeparated f]

/-- The canonical algebra comparison `g^*(f_* 𝒪_X) ⟶ f'_* 𝒪_X'` of a commutative square.
No flatness or cartesianness is needed to construct it. -/
def pushforwardStructureAlgebraBaseChange (w : CommSq g' f' f g) :
    ((QuasicoherentAlgebra.pullback g).obj f.pushforwardAlgebra).obj ⟶
      f'.pushforwardStructureAlgebra :=
  (QuasicoherentAlgebra.pullbackHomEquiv g f.pushforwardAlgebra
    f'.pushforwardStructureAlgebra).symm
      (eqToHom (pushforwardAlgebra_obj f) ≫ pushforwardStructureAlgebraMap g' w.w ≫
        (f'.pushforwardStructureAlgebraCompIso g).inv)

/-- The adjunct of algebra base change is pullback of regular functions followed by the
inverse comparison for the composite pushforward. -/
@[simp]
lemma pullbackHomEquiv_pushforwardStructureAlgebraBaseChange (w : CommSq g' f' f g) :
    QuasicoherentAlgebra.pullbackHomEquiv g f.pushforwardAlgebra
        f'.pushforwardStructureAlgebra (pushforwardStructureAlgebraBaseChange w) =
      eqToHom (pushforwardAlgebra_obj f) ≫ pushforwardStructureAlgebraMap g' w.w ≫
        (f'.pushforwardStructureAlgebraCompIso g).inv :=
  Equiv.apply_symm_apply _ _

/-- The underlying module of the pullback of a direct-image algebra is the pullback of
the direct image of the structure sheaf. -/
lemma pullback_pushforwardAlgebra_X :
    ((QuasicoherentAlgebra.pullback g).obj f.pushforwardAlgebra).obj.X =
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj (𝟙_ X.Modules)) :=
  (QuasicoherentAlgebra.pullback_obj_X g f.pushforwardAlgebra).trans
    (congrArg (Scheme.Modules.pullback g).obj
      ((congrArg CommMon.X (pushforwardAlgebra_obj f)).trans f.pushforwardStructureAlgebra_X))

/-- The underlying module map of algebra base change is module base change followed by
pushforward of the canonical identification of the pulled-back structure sheaf. -/
lemma pushforwardStructureAlgebraBaseChange_hom_hom (w : CommSq g' f' f g) :
    (pushforwardStructureAlgebraBaseChange w).hom.hom =
      eqToHom (pullback_pushforwardAlgebra_X (f := f) (g := g)) ≫
        (Scheme.Modules.pushforwardBaseChange w).app (𝟙_ X.Modules) ≫
          (Scheme.Modules.pushforward f').map (Scheme.Modules.pullbackObjUnitIso g').hom := by
  rw [pushforwardStructureAlgebraBaseChange,
    QuasicoherentAlgebra.pullbackHomEquiv_symm_apply_hom_hom]
  -- Transport across the bundled carrier using naturality of the module adjunction.
  have h : (eqToHom (pushforwardAlgebra_obj f)).hom.hom =
      eqToHom (congrArg CommMon.X (pushforwardAlgebra_obj f)) :=
    eqToHom_map (CommMon.forget S.Modules) (pushforwardAlgebra_obj f)
  erw [CommMon.comp_hom, CommMon.comp_hom, h,
    Adjunction.homEquiv_naturality_left_symm, eqToHom_map,
    eqToHom_trans_assoc]
  congr 1
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine Eq.trans ?_
    (Scheme.Modules.homEquiv_pushforwardBaseChange_comp_pullbackObjUnitIso w).symm
  -- The algebra adjunction uses the unfolded sheaf category; normalize the
  -- algebra composites before applying the module-category equations.
  erw [pushforwardStructureAlgebraMap_hom,
    pushforwardStructureAlgebraCompIso_inv_hom_hom]
  simp only [NatTrans.comp_app]
  erw [Category.assoc, Category.assoc]

/-- Flat base change for the direct-image algebra of a quasi-compact quasi-separated
morphism. The canonical comparison is an isomorphism of commutative algebras. -/
theorem isIso_pushforwardStructureAlgebraBaseChange (H : IsPullback g' f' f g) [Flat g] :
    IsIso (pushforwardStructureAlgebraBaseChange H.toCommSq) := by
  have : IsIso (pushforwardStructureAlgebraBaseChange H.toCommSq).hom.hom := by
    rw [pushforwardStructureAlgebraBaseChange_hom_hom]
    have := Scheme.Modules.isIso_pushforwardBaseChange_app H (𝟙_ X.Modules)
    -- Explicit composition reconciles the scheme and unfolded sheaf category instances.
    apply IsIso.comp_isIso'
    · apply (eqToIso _).isIso_hom
      exact pullback_pushforwardAlgebra_X
    · exact IsIso.comp_isIso' this
        ((Scheme.Modules.pushforward f').mapIso
          (Scheme.Modules.pullbackObjUnitIso g')).isIso_hom
  -- Reflect invertibility first through monoids and then through commutative monoids.
  -- The explicit map types reconcile the scheme and sheaf module-category instances.
  have : IsIso ((Mon.forget S'.Modules).map
      (pushforwardStructureAlgebraBaseChange H.toCommSq).hom) := this
  have : IsIso (pushforwardStructureAlgebraBaseChange H.toCommSq).hom :=
    isIso_of_reflects_iso _ (Mon.forget S'.Modules)
  have : IsIso ((CommMon.forget₂Mon S'.Modules).map
      (pushforwardStructureAlgebraBaseChange H.toCommSq)) := this
  exact isIso_of_reflects_iso (pushforwardStructureAlgebraBaseChange H.toCommSq)
    (CommMon.forget₂Mon S'.Modules)

/-- The flat-base-change isomorphism of function algebras, with the actual pullback and
pushforward carriers. -/
def pushforwardStructureAlgebraBaseChangeIso (H : IsPullback g' f' f g) [Flat g] :
    ((QuasicoherentAlgebra.pullback g).obj f.pushforwardAlgebra).obj ≅
      f'.pushforwardStructureAlgebra :=
  letI := isIso_pushforwardStructureAlgebraBaseChange H
  asIso (pushforwardStructureAlgebraBaseChange H.toCommSq)

/-- The forward map of the flat-base-change isomorphism is the canonical algebra comparison. -/
@[simp]
lemma pushforwardStructureAlgebraBaseChangeIso_hom (H : IsPullback g' f' f g) [Flat g] :
    (pushforwardStructureAlgebraBaseChangeIso H).hom =
      pushforwardStructureAlgebraBaseChange H.toCommSq :=
  (rfl)

/-- The inverse of flat algebra base change is the inverse of the canonical comparison. -/
@[simp]
lemma pushforwardStructureAlgebraBaseChangeIso_inv (H : IsPullback g' f' f g) [Flat g] :
    (pushforwardStructureAlgebraBaseChangeIso H).inv =
      @CategoryTheory.inv _ _ _ _ (pushforwardStructureAlgebraBaseChange H.toCommSq)
        (isIso_pushforwardStructureAlgebraBaseChange H) :=
  (rfl)

end AlgebraicGeometry.Scheme.Hom
