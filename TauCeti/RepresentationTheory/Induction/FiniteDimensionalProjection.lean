/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.FiniteDimensional
public import TauCeti.RepresentationTheory.Induction.Projection

/-!
# The projection formula on finite-dimensional representations

For a finite-index subgroup `S ≤ G` over a field `k`, this file specializes the projection formula
`TauCeti.indProjection` of `TauCeti/RepresentationTheory/Induction/Projection.lean` to
finite-dimensional representations, as

`Ind_S^G (A ⊗ Res_S^G B) ≅ (Ind_S^G A) ⊗ B`  in  `FDRep k G`.

The forgetful functor `forget₂ (FDRep k G) (Rep k G)` is fully faithful, so the isomorphism is
obtained as the preimage of its `Rep k G` counterpart, conjugated by the comparison
`TauCeti.indFDRepForgetIso` between the small carrier chosen by `TauCeti.indFDRep` and Mathlib's.

## Main definitions

* `TauCeti.indFDRepProjection`: the projection formula in `FDRep k G` for a finite-index subgroup.

## Main statements

* `TauCeti.forget₂_map_indFDRepProjection_hom`: what `TauCeti.indFDRepProjection` is, read through
  the forgetful functor.

## Implementation notes

The subgroup has finite index because that is what keeps an induced representation
finite-dimensional. The ambient group is confined to the universe of `k` by the proof route
through the `Rep`-level `TauCeti.indProjection`, not by the statement: `FDRep k G` is monoidal for
`G` in any universe, so both sides of the isomorphism elaborate with `G` free. Lifting the
restriction would mean rebuilding the isomorphism at the universe-polymorphic
`Representation.Equiv` level, which needs a tensor-congruence for `Representation.Equiv` that the
library does not have.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G} [S.FiniteIndex]

/-- **The projection formula on finite-dimensional representations**,
`Ind_S^G (A ⊗ Res_S^G B) ≅ (Ind_S^G A) ⊗ B` in `FDRep k G`.

On isomorphism classes this becomes the statement that induction is a homomorphism of modules over
the representation ring, `TauCeti.repRingInd_mul_repRingRes`. -/
noncomputable def indFDRepProjection (A : FDRep k S) (B : FDRep k G) :
    indFDRep (A ⊗ (Action.res (FGModuleCat k) S.subtype).obj B) ≅ indFDRep A ⊗ B :=
  (forget₂ (FDRep k G) (Rep k G)).preimageIso
    ((indFDRepForgetIso _).trans
      ((indProjection S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A)
          ((forget₂ (FDRep k G) (Rep k G)).obj B)).trans
        (((indFDRepForgetIso A).symm ⊗ᵢ Iso.refl ((forget₂ (FDRep k G) (Rep k G)).obj B)).trans
          -- The closing `eqToIso` only renames the tensor product of the forgotten objects. The
          -- two are definitionally equal, but the unifier does not find that equality on its own:
          -- an `Iso.refl` in this position exhausts the heartbeat budget in `whnf`.
          (eqToIso (FDRep.forget₂_obj_tensor (indFDRep A) B).symm))))

/-- Read through the fully faithful `forget₂ (FDRep k G) (Rep k G)`, the forward direction of
`TauCeti.indFDRepProjection` is the `Rep`-level projection formula conjugated by the small-carrier
comparisons `TauCeti.indFDRepForgetIso`. -/
theorem forget₂_map_indFDRepProjection_hom (A : FDRep k S) (B : FDRep k G) :
    (forget₂ (FDRep k G) (Rep k G)).map (indFDRepProjection A B).hom =
      (indFDRepForgetIso (A ⊗ (Action.res (FGModuleCat k) S.subtype).obj B)).hom ≫
        (indProjection S.subtype ((forget₂ (FDRep k S) (Rep k S)).obj A)
            ((forget₂ (FDRep k G) (Rep k G)).obj B)).hom ≫
          (((indFDRepForgetIso A).symm ⊗ᵢ
              Iso.refl ((forget₂ (FDRep k G) (Rep k G)).obj B)).hom ≫
            eqToHom (FDRep.forget₂_obj_tensor (indFDRep A) B).symm) :=
  (forget₂ (FDRep k G) (Rep k G)).map_preimage _

end TauCeti
