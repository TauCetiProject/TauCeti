/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.OpenImmersion

/-!
# Pullback along the inclusion of an open subspace

Let `f : X ⟶ Y` be a morphism of pre-adic spaces and `V` an open subset of `Y`. The restriction
`f⁻¹(V) ⟶ V` of `f` (`TauCeti.PreAdicSpace.Hom.restrictPreimage`) makes the square

```text
f⁻¹(V) ⟶ V
   ↓       ↓
   X   ⟶   Y
```

a pullback square: the open subspace `f⁻¹(V)` is the fibre product `X ×_Y V`. No hypothesis on
`f` is needed; a morphism `T ⟶ X` whose composite with `f` lands in `V` lands in `f⁻¹(V)` and
factors through the open immersion `f⁻¹(V) ⟶ X`.

The open subspaces of an adic space are adic spaces (`TauCeti.PreAdicSpace.isAdic_restrict`), so
the same square lives in Wedhorn's category `TauCeti.AdicSpace` of adic spaces. This file defines
the open adic subspace `TauCeti.AdicSpace.restrict` with its inclusion
`TauCeti.AdicSpace.ofRestrict`, and the restriction `TauCeti.AdicSpace.restrictPreimage` of a
morphism of adic spaces over an open of its target, and proves the pullback property there. This is
the adic-space form of pullback along a rational open immersion: for an adic `f` between affinoids
and a rational subset `V = R(T/s)` the ring-level comparison with the completed tensor product is
`TauCeti.Huber.CompletedTensor.completionLocEquiv`, but the fibre product itself is the open
subspace `f⁻¹(V)` for every `f`.

## Main definitions

* `TauCeti.AdicSpace.restrict`, `TauCeti.AdicSpace.ofRestrict`: the open adic subspace of an adic
  space on an open subset, and its inclusion.
* `TauCeti.AdicSpace.restrictPreimage`: the restriction `f⁻¹(V) ⟶ V` of a morphism of adic
  spaces.

## Main results

* `TauCeti.PreAdicSpace.Hom.isPullback_restrictPreimage`: `f⁻¹(V)` is the pullback of `V ⟶ Y`
  along `f`, in pre-adic spaces.
* `TauCeti.AdicSpace.isPullback_restrictPreimage`: the same in adic spaces.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark 8.37 and §8.4 (open subspaces).
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TauCeti

universe u

namespace PreAdicSpace.Hom

variable {X Y : PreAdicSpace.{u}} (f : X ⟶ Y) (V : Opens Y)

/-- A morphism into `X` whose composite with `f` lands in `V` has image inside `f⁻¹(V)`. -/
private theorem range_subset_range_ofRestrict {T : PreAdicSpace.{u}} (a : T ⟶ X)
    (b : T ⟶ Y.restrict V.isOpenEmbedding) (h : b ≫ Y.ofRestrict V.isOpenEmbedding = a ≫ f) :
    Set.range a.base ⊆
      Set.range (X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding).base := by
  rintro _ ⟨t, rfl⟩
  have hV : f.base (a.base t) ∈ V := by
    have ht := congrArg (fun g ↦ g.base t) h
    simp only [comp_base, TopCat.comp_app, ofRestrict_base] at ht
    rw [← ht]
    exact (b.base t).2
  exact ⟨⟨a.base t, hV⟩, rfl⟩

/-- **Pullback along an open subspace.** For a morphism `f : X ⟶ Y` of pre-adic spaces and an open
`V ⊆ Y`, the open subspace `f⁻¹(V)` with the restriction `f⁻¹(V) ⟶ V` and its inclusion into `X` is
the pullback of `V ⟶ Y` along `f`. -/
theorem isPullback_restrictPreimage :
    IsPullback (f.restrictPreimage V) (X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding)
      (Y.ofRestrict V.isOpenEmbedding) f := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (f.restrictPreimage_ofRestrict V)) ?_
  refine PullbackCone.isLimitAux' _ fun s ↦ ?_
  have hs := range_subset_range_ofRestrict f V s.snd s.fst s.condition
  refine ⟨IsOpenImmersion.lift _ s.snd hs, ?_, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  · rw [← cancel_mono (Y.ofRestrict V.isOpenEmbedding)]
    simp only [PullbackCone.mk_fst, Category.assoc, restrictPreimage_ofRestrict,
      IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro m _ hm
    exact IsOpenImmersion.lift_uniq _ _ _ m hm

end PreAdicSpace.Hom

namespace AdicSpace

variable (X : AdicSpace.{u}) (U : Opens X.obj)

/-- The open adic subspace of an adic space `X` on an open subset `U`: the restriction of `X` to
`U`, which is again an adic space. -/
@[expose] noncomputable def restrict : AdicSpace.{u} :=
  ⟨X.obj.restrict U.isOpenEmbedding, PreAdicSpace.isAdic_restrict _ X.property⟩

/-- The pre-adic space underlying an open adic subspace is the restriction of the underlying
pre-adic space. -/
@[simp]
theorem restrict_obj : (X.restrict U).obj = X.obj.restrict U.isOpenEmbedding :=
  (rfl)

/-- The inclusion of an open adic subspace. -/
noncomputable def ofRestrict : X.restrict U ⟶ X :=
  ObjectProperty.homMk (X.obj.ofRestrict U.isOpenEmbedding)

/-- The underlying morphism of pre-adic spaces of the inclusion of an open adic subspace. -/
@[simp]
theorem ofRestrict_hom : (X.ofRestrict U).hom = X.obj.ofRestrict U.isOpenEmbedding :=
  (rfl)

instance : PreAdicSpace.IsOpenImmersion (X.ofRestrict U).hom :=
  PreAdicSpace.IsOpenImmersion.ofRestrict X.obj U.isOpenEmbedding

instance : Mono (X.ofRestrict U) :=
  (ObjectProperty.ι _).mono_of_mono_map
    (inferInstanceAs (Mono (X.ofRestrict U).hom))

section Hom

variable {X Y : AdicSpace.{u}} (f : X ⟶ Y) (V : Opens Y.obj)

/-- The restriction `f⁻¹(V) ⟶ V` of a morphism of adic spaces over an open of its target. -/
noncomputable def restrictPreimage :
    X.restrict ((Opens.map f.hom.base).obj V) ⟶ Y.restrict V :=
  ObjectProperty.homMk (f.hom.restrictPreimage V)

/-- The underlying morphism of pre-adic spaces of the restriction. -/
@[simp]
theorem restrictPreimage_hom : (restrictPreimage f V).hom = f.hom.restrictPreimage V :=
  (rfl)

/-- The restriction of a morphism commutes with the inclusions of the open subspaces. -/
@[reassoc (attr := simp)]
theorem restrictPreimage_ofRestrict :
    restrictPreimage f V ≫ Y.ofRestrict V = X.ofRestrict ((Opens.map f.hom.base).obj V) ≫ f := by
  apply ObjectProperty.hom_ext
  exact f.hom.restrictPreimage_ofRestrict V

/-- **Pullback along an open adic subspace.** For a morphism `f : X ⟶ Y` of adic spaces and an
open `V ⊆ Y`, the open adic subspace `f⁻¹(V)` is the fibre product `X ×_Y V`, with no hypothesis on
`f`. -/
theorem isPullback_restrictPreimage :
    IsPullback (restrictPreimage f V) (X.ofRestrict ((Opens.map f.hom.base).obj V))
      (Y.ofRestrict V) f := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (restrictPreimage_ofRestrict f V)) ?_
  refine PullbackCone.isLimitAux' _ fun s ↦ ?_
  have hlim := (f.hom.isPullback_restrictPreimage V).isLimit
  let s' : PullbackCone (Y.obj.ofRestrict V.isOpenEmbedding) f.hom :=
    PullbackCone.mk s.fst.hom s.snd.hom (congrArg (fun g ↦ g.hom) s.condition)
  refine ⟨ObjectProperty.homMk (hlim.lift s'), ?_, ?_, ?_⟩
  · exact ObjectProperty.hom_ext _ (hlim.fac s' .left)
  · exact ObjectProperty.hom_ext _ (hlim.fac s' .right)
  · intro m _ h₂
    rw [← cancel_mono (X.ofRestrict ((Opens.map f.hom.base).obj V))]
    exact h₂.trans (ObjectProperty.hom_ext _ (hlim.fac s' .right)).symm

end Hom

end AdicSpace

end TauCeti
