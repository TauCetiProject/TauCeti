/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Character.Descent
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Splitting
import TauCeti.Algebra.Bialgebra.GaloisDescent
import Mathlib.FieldTheory.IsSepClosed

/-!
# Descent of character maps between groups of multiplicative type

Over any field, an equivariant map between the geometric character groups of two
multiplicative-type coordinate algebras descends uniquely to a Hopf morphism. Both
algebras split over the separable closure, which is Galois over the ground field.
This avoids assuming that the algebraic closure is separable.

The separate perfect-field descent theorem allows an arbitrary target coordinate
algebra. Here both coordinate algebras must be of multiplicative type. The torus
character-lattice equivalence consumes this arbitrary-field form.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Equivariant geometric character maps between multiplicative-type coordinate algebras
descend uniquely over an arbitrary field. -/
theorem existsUnique_geometricCharacterMap_eq_of_multiplicativeType
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (hK : multiplicativeTypeCommHopfAlgProperty k K)
    (f : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K.obj)
    (hf : ∀ (σ : Field.absoluteGaloisGroup k) x, f (σ • x) = σ • f x) :
    ∃! g : H.obj ⟶ K.obj, CommHopfAlgCat.geometricCharacterMap g = f := by
  let L := separableClosure k (AlgebraicClosure k)
  have hHspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] H))) = ⊤ :=
    hH.span_groupLike_separableClosure_eq_top
  have hKspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] K))) = ⊤ :=
    hK.span_groupLike_separableClosure_eq_top
  let _ : Group (_root_.GroupLike L (L ⊗[k] H)) :=
    _root_.GroupLike.instGroup (R := L) (A := L ⊗[k] H)
  let _ : Group (_root_.GroupLike L (L ⊗[k] K)) :=
    _root_.GroupLike.instGroup (R := L) (A := L ⊗[k] K)
  let eH := groupLikeScalarTowerEquiv (K := AlgebraicClosure k) hHspan
  let eK := groupLikeScalarTowerEquiv (K := AlgebraicClosure k) hKspan
  let q : _root_.GroupLike L (L ⊗[k] H) →* _root_.GroupLike L (L ⊗[k] K) :=
    eK.symm.toMonoidHom.comp (f.comp eH.toMonoidHom)
  have hq (τ : L ≃ₐ[k] L) (x : _root_.GroupLike L (L ⊗[k] H)) :
      q (τ • x) = τ • q x := by
    let σ := τ.liftNormal (AlgebraicClosure k)
    have hστ (a : L) : σ (algebraMap L (AlgebraicClosure k) a) =
        algebraMap L (AlgebraicClosure k) (τ a) :=
      τ.liftNormal_commutes (AlgebraicClosure k) a
    apply eK.injective
    simp only [q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [groupLikeScalarTowerEquiv_smul hHspan σ τ hστ,
      groupLikeScalarTowerEquiv_smul hKspan σ τ hστ]
    have h := hf (show Field.absoluteGaloisGroup k from σ) (eH x)
    unfold Field.absoluteGaloisGroup at h
    simpa only [eH, eK, MulEquiv.apply_symm_apply] using h
  have hlinear := linearIndep_groupLikeVal (R := L) (A := L ⊗[k] H)
  let F := MonoidHom.liftBialgHom (R := L) (A := L ⊗[k] H) (B := L ⊗[k] K)
    q hlinear hHspan
  have hequiv (τ : L ≃ₐ[k] L) (x : L ⊗[k] H) :
      F (TensorProduct.map τ.toLinearMap LinearMap.id x) =
        TensorProduct.map τ.toLinearMap LinearMap.id (F x) := by
    apply (F.map_smul_iff_groupLike hHspan τ).2 _ x
    simpa only [F, MonoidHom.groupLikeMap_liftBialgHom] using hq τ
  let g : H.obj ⟶ K.obj := _root_.CommHopfAlgCat.ofHom (F.galoisDescend hequiv)
  have hg : CommHopfAlgCat.geometricCharacterMap g = f := by
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := eH.surjective x
    have hmap : GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) g.hom) y =
        q y := by
      simp only [g, _root_.CommHopfAlgCat.hom_ofHom, BialgHom.map_galoisDescend,
        F, MonoidHom.groupLikeMap_liftBialgHom]
    have hnatural :
        CommHopfAlgCat.geometricCharacterMap g (eH y) =
          eK (GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) g.hom) y) := by
      apply _root_.GroupLike.val_injective
      simp only [CommHopfAlgCat.val_geometricCharacterMap,
        CommHopfAlgCat.hom_baseChangeMap, eH, eK, val_groupLikeScalarTowerEquiv,
        GroupLike.val_map]
      induction y.val using TensorProduct.inductionOn with
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
          IsScalarTower.toAlgHom_apply, AlgHom.id_apply, BialgHom.id_apply]
    rw [hnatural, hmap]
    exact eK.apply_symm_apply (f (eH y))
  exact ⟨g, hg, fun g' hg' ↦ hH.geometricCharacterMap_injective (hg'.trans hg.symm)⟩

/-- Every equivariant map of geometric-character representations between groups of
multiplicative type comes from a coordinate Hopf morphism, over any field. -/
theorem geometricCharacterRepresentationMap_surjective_of_multiplicativeType
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (hK : multiplicativeTypeCommHopfAlgProperty k K) :
    Function.Surjective
      (CommHopfAlgCat.geometricCharacterRepresentationMap (H := H.obj) (K := K.obj)) := by
  intro f
  dsimp only [CommHopfAlgCat.geometricCharacterRepresentation, Rep.ofMulDistribMulAction] at f
  let q : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K.obj :=
    f.hom.toLinearMap.toAddMonoidHom.toMultiplicative
  have hq (σ : Field.absoluteGaloisGroup k) x : q (σ • x) = σ • q x := by
    have hx := Representation.IntertwiningMap.isIntertwining _ _ f.hom σ (Additive.ofMul x)
    exact congrArg (Additive.toMul (α := CommHopfAlgCat.geometricCharacterGroup K.obj)) hx
  obtain ⟨g, hg, _⟩ := hH.existsUnique_geometricCharacterMap_eq_of_multiplicativeType hK q hq
  refine ⟨g, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp only [Representation.IntertwiningMap.toLinearMap_apply]
  have hx := CommHopfAlgCat.geometricCharacterRepresentationMap_hom_apply g x
  apply (Additive.toMul (α := CommHopfAlgCat.geometricCharacterGroup K.obj)).injective
  exact (congrArg Additive.toMul hx).trans
    ((CommHopfAlgCat.toMul_additiveCharacterMap g x).trans (DFunLike.congr_fun hg x.toMul))

end TauCeti.multiplicativeTypeCommHopfAlgProperty
