/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Faithful
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Splitting
import TauCeti.Algebra.Bialgebra.GaloisDescent
import TauCeti.Algebra.Bialgebra.GroupLike.Lift
import Mathlib.FieldTheory.IsSepClosed

/-!
# Descent of character maps between groups of multiplicative type

Over any field, an equivariant map between the geometric character groups of two
multiplicative-type coordinate algebras descends uniquely to a Hopf morphism. Both
algebras split over the separable closure, which is Galois over the ground field.
This avoids assuming that the algebraic closure is separable.

The separate perfect-field descent theorem
(`TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Character.Descent`) allows an arbitrary
target coordinate algebra. Here both coordinate algebras must be of multiplicative type. The
torus character-lattice equivalence consumes this arbitrary-field form.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- An equivariant geometric character map between multiplicative-type coordinate algebras
is induced by a Galois-equivariant bialgebra map over the separable closure. -/
private theorem exists_separableClosure_bialgHom
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (hK : multiplicativeTypeCommHopfAlgProperty k K)
    (f : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K.obj)
    (hf : ∀ (σ : Field.absoluteGaloisGroup k) x, f (σ • x) = σ • f x) :
    ∃ F :
      separableClosure k (AlgebraicClosure k) ⊗[k] H →ₐc[separableClosure k (AlgebraicClosure k)]
        separableClosure k (AlgebraicClosure k) ⊗[k] K,
      (∀ (τ : separableClosure k (AlgebraicClosure k) ≃ₐ[k]
          separableClosure k (AlgebraicClosure k)) x,
        F (TensorProduct.map τ.toLinearMap LinearMap.id x) =
          TensorProduct.map τ.toLinearMap LinearMap.id (F x)) ∧
        ∀ y, groupLikeScalarTowerEquiv (K := AlgebraicClosure k)
            hK.span_groupLike_separableClosure_eq_top (F.mapGroupLike y) =
          f (groupLikeScalarTowerEquiv (K := AlgebraicClosure k)
            hH.span_groupLike_separableClosure_eq_top y) := by
  let L := separableClosure k (AlgebraicClosure k)
  have hHspan := hH.span_groupLike_separableClosure_eq_top
  have hKspan := hK.span_groupLike_separableClosure_eq_top
  let _ : Group (_root_.GroupLike L (L ⊗[k] H)) :=
    _root_.GroupLike.instGroup (R := L) (A := L ⊗[k] H)
  let _ : Group (_root_.GroupLike L (L ⊗[k] K)) :=
    _root_.GroupLike.instGroup (R := L) (A := L ⊗[k] K)
  let eH := groupLikeScalarTowerEquiv (K := AlgebraicClosure k) hHspan
  let eK := groupLikeScalarTowerEquiv (K := AlgebraicClosure k) hKspan
  -- Transport `f` to the characters over the separable closure, where both algebras split.
  let q : _root_.GroupLike L (L ⊗[k] H) →* _root_.GroupLike L (L ⊗[k] K) :=
    eK.symm.toMonoidHom.comp (f.comp eH.toMonoidHom)
  have hq (τ : L ≃ₐ[k] L) (x : _root_.GroupLike L (L ⊗[k] H)) :
      q (τ • x) = τ • q x := by
    -- Lift `τ` to the algebraic closure, where `f` is equivariant by hypothesis.
    let σ := τ.liftNormal (AlgebraicClosure k)
    have hστ (a : L) : σ (algebraMap L (AlgebraicClosure k) a) =
        algebraMap L (AlgebraicClosure k) (τ a) :=
      τ.liftNormal_commutes (AlgebraicClosure k) a
    apply eK.injective
    simp only [q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [groupLikeScalarTowerEquiv_smul hHspan σ τ hστ,
      groupLikeScalarTowerEquiv_smul hKspan σ τ hστ]
    simpa only [eH, eK, MulEquiv.apply_symm_apply,
      AlgEquiv.absoluteGaloisGroup_toAlgEquiv_symm_smul_groupLike] using
        hf (Field.absoluteGaloisGroup.toAlgEquiv.symm σ) (eH x)
  -- A split bialgebra is the group algebra of its characters, so `q` extends linearly.
  have hlinear := linearIndep_groupLikeVal (R := L) (A := L ⊗[k] H)
  let F := MonoidHom.liftBialgHom (R := L) (A := L ⊗[k] H) (B := L ⊗[k] K)
    q hlinear hHspan
  refine ⟨F, fun τ x ↦ ?_, fun y ↦ ?_⟩
  · apply (F.map_smul_iff_groupLike hHspan τ).2 _ x
    simpa only [F, MonoidHom.mapGroupLike_liftBialgHom] using hq τ
  · simp only [F, MonoidHom.mapGroupLike_liftBialgHom]
    exact eK.apply_symm_apply (f (eH y))

/-- Equivariant geometric character maps between multiplicative-type coordinate algebras
descend uniquely over an arbitrary field. -/
theorem existsUnique_geometricCharacterMap_eq_of_multiplicativeType
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (hK : multiplicativeTypeCommHopfAlgProperty k K)
    (f : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K.obj)
    (hf : ∀ (σ : Field.absoluteGaloisGroup k) x, f (σ • x) = σ • f x) :
    ∃! g : H.obj ⟶ K.obj, CommHopfAlgCat.geometricCharacterMap g = f := by
  obtain ⟨F, hequiv, hF⟩ := exists_separableClosure_bialgHom hH hK f hf
  -- The separable closure is Galois over `k`, so the equivariant map `F` descends.
  let g : H.obj ⟶ K.obj := _root_.CommHopfAlgCat.ofHom (F.galoisDescend hequiv)
  have hg : CommHopfAlgCat.geometricCharacterMap g = f := by
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := (groupLikeScalarTowerEquiv (K := AlgebraicClosure k)
      hH.span_groupLike_separableClosure_eq_top).surjective x
    -- Extending coefficients to the algebraic closure commutes with `g`, which extends to `F`.
    rw [CommHopfAlgCat.geometricCharacterMap_eq_mapGroupLike, CommHopfAlgCat.hom_baseChangeMap,
      ← groupLikeScalarTowerEquiv_mapGroupLike hH.span_groupLike_separableClosure_eq_top
        hK.span_groupLike_separableClosure_eq_top, ← hF]
    simp only [g, _root_.CommHopfAlgCat.hom_ofHom, BialgHom.map_galoisDescend]
  exact ⟨g, hg, fun g' hg' ↦ hH.geometricCharacterMap_injective (hg'.trans hg.symm)⟩

/-- Every equivariant map of geometric-character representations between groups of
multiplicative type comes from a coordinate Hopf morphism, over any field. -/
theorem geometricCharacterRepresentationMap_surjective_of_multiplicativeType
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (hK : multiplicativeTypeCommHopfAlgProperty k K) :
    Function.Surjective
      (CommHopfAlgCat.geometricCharacterRepresentationMap (H := H.obj) (K := K.obj)) :=
  CommHopfAlgCat.geometricCharacterRepresentationMap_surjective_of_exists_geometricCharacterMap_eq
    fun q hq ↦ (hH.existsUnique_geometricCharacterMap_eq_of_multiplicativeType hK q hq).exists

end TauCeti.multiplicativeTypeCommHopfAlgProperty
