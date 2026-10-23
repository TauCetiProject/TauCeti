/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Character.Extension
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Faithful
import TauCeti.Algebra.Bialgebra.GaloisDescent
import Mathlib.FieldTheory.Perfect

/-!
# Descent of geometric character maps over perfect fields

Over a perfect field, every Galois-equivariant homomorphism of geometric character groups
out of a multiplicative-type coordinate algebra comes from a unique coordinate Hopf morphism.
The target coordinate algebra need not be of multiplicative type or finite type. In group-scheme
language this classifies homomorphisms from an arbitrary affine group to a group of multiplicative
type by their pullbacks on geometric characters, including non-smooth groups.

Perfectness ensures that the algebraic closure is Galois. The extension of a character map to
that closure then descends using Galois descent for bialgebra morphisms, without a finiteness
assumption on the extension. This is the morphism part of the character-lattice classification
of tori over perfect fields.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [PerfectField k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k} {K : _root_.CommHopfAlgCat.{u} k}

/-- Over a perfect field, equivariant geometric character maps out of a multiplicative-type
coordinate algebra descend uniquely to coordinate Hopf morphisms. -/
theorem existsUnique_geometricCharacterMap_eq
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (f : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K)
    (hf : ∀ (σ : Field.absoluteGaloisGroup k) x, f (σ • x) = σ • f x) :
    ∃! g : H.obj ⟶ K, CommHopfAlgCat.geometricCharacterMap g = f := by
  let : IsGalois k (AlgebraicClosure k) := ⟨⟩
  obtain ⟨F, ⟨hF, hσ⟩, _⟩ := hH.existsUnique_geometricCharacterExtension f hf
  have hequiv (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (x : AlgebraicClosure k ⊗[k] H.obj) :
      F (TensorProduct.map σ.toLinearMap LinearMap.id x) =
        TensorProduct.map σ.toLinearMap LinearMap.id (F x) := by
    -- The absolute-Galois action is the scalar-factor tensor map, behind its type wrapper.
    exact hσ (show Field.absoluteGaloisGroup k from σ) x
  let g : H.obj ⟶ K := _root_.CommHopfAlgCat.ofHom (F.galoisDescend hequiv)
  have hg : CommHopfAlgCat.geometricCharacterMap g = f := by
    apply MonoidHom.ext
    intro x
    apply _root_.GroupLike.val_injective
    rw [CommHopfAlgCat.val_geometricCharacterMap, CommHopfAlgCat.hom_baseChangeMap]
    simp only [g, _root_.CommHopfAlgCat.hom_ofHom, BialgHom.map_galoisDescend]
    exact (GroupLike.val_map F x).symm.trans (congrArg (fun q ↦ (q x).val) hF)
  exact ⟨g, hg, fun g' hg' ↦ hH.geometricCharacterMap_injective (hg'.trans hg.symm)⟩

/-- Every morphism of geometric-character representations out of a multiplicative-type
coordinate algebra over a perfect field is induced by a coordinate Hopf morphism. -/
theorem geometricCharacterRepresentationMap_surjective
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    Function.Surjective
      (CommHopfAlgCat.geometricCharacterRepresentationMap (H := H.obj) (K := K)) := by
  intro f
  -- Normalize the representation carrier to the additive character group for scalar inference.
  dsimp only [CommHopfAlgCat.geometricCharacterRepresentation, Rep.ofMulDistribMulAction] at f
  let q : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K :=
    f.hom.toLinearMap.toAddMonoidHom.toMultiplicative
  have hq (σ : Field.absoluteGaloisGroup k) x : q (σ • x) = σ • q x := by
    have hx := Representation.IntertwiningMap.isIntertwining _ _ f.hom σ
      (Additive.ofMul x)
    -- The multiplicative-action representation acts on the same additive type tag.
    exact congrArg (Additive.toMul (α := CommHopfAlgCat.geometricCharacterGroup K)) hx
  obtain ⟨g, hg, _⟩ := hH.existsUnique_geometricCharacterMap_eq q hq
  refine ⟨g, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp only [Representation.IntertwiningMap.toLinearMap_apply]
  have hx := CommHopfAlgCat.geometricCharacterRepresentationMap_hom_apply g x
  apply (Additive.toMul (α := CommHopfAlgCat.geometricCharacterGroup K)).injective
  exact (congrArg Additive.toMul hx).trans
    ((CommHopfAlgCat.toMul_additiveCharacterMap g x).trans (DFunLike.congr_fun hg x.toMul))

end TauCeti.multiplicativeTypeCommHopfAlgProperty
