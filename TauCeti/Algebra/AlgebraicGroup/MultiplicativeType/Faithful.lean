/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Functoriality

/-!
# Geometric characters determine morphisms to groups of multiplicative type

If an affine group's target is of multiplicative type, a homomorphism to that target is
determined by its pullback on geometric characters. Contravariantly, a coordinate Hopf map
whose source is of multiplicative type is determined by its map on geometric group-like
elements. These elements span after extension to an algebraic closure, and scalar extension
detects equality of the original coordinate maps.

Only the target group must be of multiplicative type; the source group need not be of finite
type. No perfectness or smoothness hypothesis is needed, so this also applies to nonreduced
groups of multiplicative type. The representation-valued formulation retains the Galois action
and supplies uniqueness in the character-group classification.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
variable {K : _root_.CommHopfAlgCat.{u} k}

/-- A coordinate morphism out of a multiplicative-type Hopf algebra is determined by its
action on geometric characters. The target coordinate algebra is arbitrary. -/
theorem geometricCharacterMap_injective (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    Function.Injective (CommHopfAlgCat.geometricCharacterMap (H := H.obj) (K := K)) := by
  intro f g hfg
  have hspan := (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top
    (R := AlgebraicClosure k)
    (C := CommHopfAlgCat.baseChange (K := AlgebraicClosure k) H.obj)).mp
      ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
        ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH))
  have hlin : (CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) f).hom.toLinearMap =
      (CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) g).hom.toLinearMap := by
    apply LinearMap.ext_on_range hspan
    intro x
    exact (CommHopfAlgCat.val_geometricCharacterMap f x).symm.trans
      ((congrArg GroupLike.val (DFunLike.congr_fun hfg x)).trans
        (CommHopfAlgCat.val_geometricCharacterMap g x))
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.ext
  intro x
  apply Algebra.TensorProduct.includeRight_injective
    (A := AlgebraicClosure k) (RingHom.injective (algebraMap k (AlgebraicClosure k)))
  have hx : (CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) f).hom (1 ⊗ₜ[k] x) =
      (CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) g).hom (1 ⊗ₜ[k] x) :=
    LinearMap.congr_fun hlin (1 ⊗ₜ[k] x)
  exact (CommHopfAlgCat.baseChangeMap_apply_tmul f 1 x).symm.trans
    (hx.trans (CommHopfAlgCat.baseChangeMap_apply_tmul g 1 x))

/-- Equality of the induced Galois-equivariant character maps detects equality of coordinate
morphisms out of a multiplicative-type Hopf algebra. -/
theorem geometricCharacterRepresentationMap_injective
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    Function.Injective
      (CommHopfAlgCat.geometricCharacterRepresentationMap (H := H.obj) (K := K)) := by
  intro f g hfg
  apply hH.geometricCharacterMap_injective
  apply MonoidHom.ext
  intro x
  have hx : CommHopfAlgCat.additiveCharacterMap f (Additive.ofMul x) =
      CommHopfAlgCat.additiveCharacterMap g (Additive.ofMul x) :=
    (CommHopfAlgCat.geometricCharacterRepresentationMap_hom_apply f _).symm.trans
      ((congrArg (fun q ↦ q.hom (Additive.ofMul x)) hfg).trans
        (CommHopfAlgCat.geometricCharacterRepresentationMap_hom_apply g _))
  exact (CommHopfAlgCat.toMul_additiveCharacterMap f (Additive.ofMul x)).symm.trans
    ((congrArg Additive.toMul hx).trans
      (CommHopfAlgCat.toMul_additiveCharacterMap g (Additive.ofMul x)))

end TauCeti.multiplicativeTypeCommHopfAlgProperty
