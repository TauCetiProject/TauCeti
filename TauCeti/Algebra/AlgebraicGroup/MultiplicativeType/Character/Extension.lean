/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Basic
public import TauCeti.Algebra.Bialgebra.GroupLike.Lift

/-!
# Extending geometric character maps

A Galois-equivariant map on geometric characters, with multiplicative-type source
coordinate algebra, extends uniquely to a Galois-equivariant bialgebra map over the
algebraic closure. This supplies the map to which descent applies in the character
classification of groups of multiplicative type and, in particular, of tori.

The extension is over the algebraic closure; descent to the original field is a
separate assertion. The target coordinate algebra need not be of multiplicative type
or finite type, and the base field need not be perfect.

See Milne, *Algebraic Groups* (2017), §12.
-/

public section

open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  {K : _root_.CommHopfAlgCat.{u} k}

/-- A Galois-equivariant geometric character homomorphism extends uniquely over the
algebraic closure, and the extension commutes with the scalar-factor Galois action. -/
theorem existsUnique_geometricCharacterExtension
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (f : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K)
    (hf : ∀ (σ : Field.absoluteGaloisGroup k) x, f (σ • x) = σ • f x) :
    ∃! F : AlgebraicClosure k ⊗[k] H.obj →ₐc[AlgebraicClosure k]
        AlgebraicClosure k ⊗[k] K,
      GroupLike.map F = f ∧
        ∀ (σ : Field.absoluteGaloisGroup k) x, F (σ • x) = σ • F x := by
  have hspan := (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top
    (R := AlgebraicClosure k)
    (C := CommHopfAlgCat.baseChange (K := AlgebraicClosure k) H.obj)).mp
      ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
        ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH))
  have hlinear := linearIndep_groupLikeVal
    (R := AlgebraicClosure k) (A := AlgebraicClosure k ⊗[k] H.obj)
  refine ⟨f.liftBialgHom hlinear hspan, ⟨?_, ?_⟩, ?_⟩
  · exact f.groupLikeMap_liftBialgHom hlinear hspan
  · intro σ x
    -- The absolute-Galois wrapper uses the scalar action of its underlying algebra automorphism.
    apply ((f.liftBialgHom hlinear hspan).map_smul_iff_groupLike hspan
      (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ)).2 _ x
    simp only [MonoidHom.groupLikeMap_liftBialgHom]
    exact hf σ
  · intro F hF
    apply f.liftBialgHom_unique hlinear hspan F
    intro x
    exact (GroupLike.val_map F x).symm.trans
      (congrArg (fun g ↦ (g x).val) hF.1)

end TauCeti.multiplicativeTypeCommHopfAlgProperty
