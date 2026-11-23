/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.WeaklyFiniteType
public import TauCeti.RingTheory.Huber.TensorProduct.Coherence
public import TauCeti.RingTheory.Huber.TensorProduct.Symmetry
public import TauCeti.RingTheory.Huber.TensorProduct.Unit

/-!
# Associativity, symmetry and unit of fibre products of adic spaces

Fibre products of adic spaces do not exist in general. When `f : X ⟶ S`, `g : Y ⟶ S` and
`h : Z ⟶ S` are locally of weakly finite type and `X`, `Z` are locally stably sheafy, the fibre
product theorems of `TauCeti.AlgebraicGeometry.AdicSpace.Pullback.WeaklyFiniteType` give all the
iterated fibre products of `X`, `Y`, `Z` over `S`
(`TauCeti.AdicSpace.FibreProduct.hasPullback_snd_comp`,
`TauCeti.AdicSpace.FibreProduct.hasPullback_fst_comp`). Given these, Mathlib's
`pullbackAssoc f g g h : (X ×_S Y) ×_S Z ≅ X ×_S (Y ×_S Z)`, `pullbackSymmetry f g` (using
`hasPullback_symmetry`) and `asIso (pullback.fst f (𝟙 S)) : X ×_S S ≅ X` are the associativity,
symmetry and unit isomorphisms, with Mathlib's projection lemmas; each is the unique isomorphism
compatible with the projections (`pullback.hom_ext`), so every coherence identity between
composites of them holds.

On affinoid charts these isomorphisms are `Spa` of the ring isomorphisms of completed tensor
products. Since `Spa` is contravariant, the geometric associator
`Spa((B ⊗̂_A C) ⊗̂_A D) ≅ Spa(B ⊗̂_A (C ⊗̂_A D))` is `Spa` of the inverse ring associator
(`FibreProduct.associatorAffinoid`), the symmetry is `Spa` of the exchange of the two factors
(`FibreProduct.symmetry_affinoid`), and the unit `Spa(B ⊗̂_A A) ≅ Spa(B)` is `Spa` of the left
coprojection, with inverse `Spa` of `b ⊗ a ↦ b·a` (`FibreProduct.unitAffinoid`).

## Main results

* `TauCeti.AdicSpace.FibreProduct.hasPullback_snd_comp`,
  `TauCeti.AdicSpace.FibreProduct.hasPullback_fst_comp`: existence of the iterated fibre products.
* `TauCeti.AdicSpace.FibreProduct.associatorAffinoid`,
  `TauCeti.AdicSpace.FibreProduct.symmetry_affinoid`,
  `TauCeti.AdicSpace.FibreProduct.unitAffinoid`: the chart formulas.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Proposition 3.7.
* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.6, Theorem 8.56.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.AdicSpace.FibreProduct

open Huber

universe u

section General

variable {X Y Z S : AdicSpace.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}

/-- The iterated fibre product `(X ×_S Y) ×_S Z` exists when `f` is adic, `g`, `h` are locally of
weakly finite type and `X` is locally stably sheafy; so does the inner `X ×_S Y`. -/
theorem hasPullback_snd_comp (hf : IsAdic f) (hg : LocallyOfWeaklyFiniteType g)
    (hh : LocallyOfWeaklyFiniteType h) (hX : X.IsLocallyStablySheafy) :
    haveI := hasPullback_of_locallyOfWeaklyFiniteType_right hf hg hX
    HasPullback (pullback.snd f g ≫ g) h :=
  haveI := hasPullback_of_locallyOfWeaklyFiniteType_right hf hg hX
  hasPullback_of_locallyOfWeaklyFiniteType_right
    (IsAdic.isMultiplicative.comp_mem _ _
      (IsAdic.pullback_snd_of_locallyOfWeaklyFiniteType hf hg hX) hg.isAdic) hh
    (isLocallyStablySheafy_pullback_of_locallyOfWeaklyFiniteType_right hf hg hX)

/-- The iterated fibre product `X ×_S (Y ×_S Z)` exists when `f`, `g` are locally of weakly finite
type, `h` is adic and `Z` is locally stably sheafy; so does the inner `Y ×_S Z`. -/
theorem hasPullback_fst_comp (hf : LocallyOfWeaklyFiniteType f)
    (hg : LocallyOfWeaklyFiniteType g) (hh : IsAdic h) (hZ : Z.IsLocallyStablySheafy) :
    haveI := hasPullback_of_locallyOfWeaklyFiniteType_left hg hh hZ
    HasPullback f (pullback.fst g h ≫ g) :=
  haveI := hasPullback_of_locallyOfWeaklyFiniteType_left hg hh hZ
  hasPullback_of_locallyOfWeaklyFiniteType_left hf
    (IsAdic.isMultiplicative.comp_mem _ _
      (IsAdic.pullback_fst_of_locallyOfWeaklyFiniteType hg hh hZ) hg.isAdic)
    (isLocallyStablySheafy_pullback_of_locallyOfWeaklyFiniteType_left hg hh hZ)

end General

/-! ### Chart formulas -/

section Affinoid

open PreAdicSpace ValuationSpectrum

section Symmetry

variable {A B C : Type u}
  [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T0Space B] [IsHuberRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [CompleteSpace C] [T0Space C] [IsHuberRing C]
  [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Symmetry on affinoid charts**: the comparison of the two affinoid fibre product squares
`Spa((B, B⁺) ⊗̂_A (C, C⁺))` and `Spa((C, C⁺) ⊗̂_A (B, B⁺))` of `Spa(B, B⁺)` and `Spa(C, C⁺)` over
`Spa(A, A⁺)` is `Spa` of the exchange of the two tensor factors. -/
theorem symmetry_affinoid {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus)
    (hUT : IsSheafyForEveryPresentation (U.completedTensor A T).plus)
    (f : Pair.Hom S T) (g : Pair.Hom S U)
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C) :
    ((affinoid_isPullback hS hT hU hTU f g hf hg).isoIsPullback _ _
        (affinoid_isPullback hS hU hT hUT g f hg hf).flip).hom =
      comapOfPair hUT hTU (Pair.completedTensor.commHom A U T) := by
  apply (affinoid_isPullback hS hU hT hUT g f hg hf).flip.hom_ext
  · rw [IsPullback.isoIsPullback_hom_fst, ← comapOfPair_comp,
      Pair.completedTensor.commHom_comp_inr]
  · rw [IsPullback.isoIsPullback_hom_snd, ← comapOfPair_comp,
      Pair.completedTensor.commHom_comp_inl]

end Symmetry

section Unit

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T2Space B] [IsHuberRing B] [Algebra A B] [IsAdicHom (algebraMap A B)]

/-- The identity structure map of `A` is adic, so `A` is a Huber `A`-algebra. -/
local instance isAdicHom_algebraMap_self : IsAdicHom (algebraMap A A) := by
  simpa using (IsAdicHom.id (A := A))

/-- **Unit on affinoid charts**: `Spa((B, B⁺) ⊗̂_A (A, A⁺)) ≅ Spa(B, B⁺)` is `Spa` of the left
coprojection, with inverse `Spa` of the multiplication `b ⊗ a ↦ b·a`. -/
@[expose, simps]
noncomputable def unitAffinoid (S : Pair A) {T : Pair B}
    (hT : IsSheafyForEveryPresentation T.plus)
    (hTS : IsSheafyForEveryPresentation (T.completedTensor A S).plus)
    (hplus : ∀ a ∈ S.plus, algebraMap A B a ∈ T.plus) :
    ofPair (T.completedTensor A S) hTS ≅ ofPair T hT where
  hom := comapOfPair hT hTS (Pair.completedTensor.inl A T S)
  inv := comapOfPair hTS hT (Pair.completedTensor.rightUnitorHom S T hplus)
  hom_inv_id := by
    rw [← comapOfPair_comp, Pair.completedTensor.inl_comp_rightUnitorHom, comapOfPair_id]
  inv_hom_id := by
    rw [← comapOfPair_comp, Pair.completedTensor.rightUnitorHom_comp_inl, comapOfPair_id]

/-- The inverse affinoid unit composed with the second projection is the structure morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)`, as for the unit `(𝟙, f)` of a general fibre product. -/
@[reassoc]
theorem unitAffinoid_inv_comp_inr {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (hTS : IsSheafyForEveryPresentation (T.completedTensor A S).plus)
    (f : Pair.Hom S T) (hf : f.toRingHom = algebraMap A B)
    (hplus : ∀ a ∈ S.plus, algebraMap A B a ∈ T.plus) :
    (unitAffinoid S hT hTS hplus).inv ≫ comapOfPair hS hTS (Pair.completedTensor.inr A T S) =
      comapOfPair hS hT f := by
  rw [unitAffinoid_inv, ← comapOfPair_comp]
  congr 1
  ext a
  simp [Pair.Hom.toRingHom_comp, hf]

end Unit

section Associator

variable {A B C D : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A D)]

/-- **Associativity on affinoid charts**: the geometric associator
`Spa(((B, B⁺) ⊗̂_A (C, C⁺)) ⊗̂_A (D, D⁺)) ≅ Spa((B, B⁺) ⊗̂_A ((C, C⁺) ⊗̂_A (D, D⁺)))` is `Spa` of
the inverse ring associator `b ⊗ (c ⊗ d) ↦ (b ⊗ c) ⊗ d`; its inverse is `Spa` of the ring
associator. -/
@[expose, simps]
noncomputable def associatorAffinoid (T : Pair B) (U : Pair C) (V : Pair D)
    (hTU_V : IsSheafyForEveryPresentation ((T.completedTensor A U).completedTensor A V).plus)
    (hT_UV : IsSheafyForEveryPresentation (T.completedTensor A (U.completedTensor A V)).plus) :
    ofPair _ hTU_V ≅ ofPair _ hT_UV where
  hom := comapOfPair hT_UV hTU_V (Pair.completedTensor.assocSymmHom A T U V)
  inv := comapOfPair hTU_V hT_UV (Pair.completedTensor.assocHom A T U V)
  hom_inv_id := by
    rw [← comapOfPair_comp, Pair.completedTensor.assocSymmHom_comp_assocHom, comapOfPair_id]
  inv_hom_id := by
    rw [← comapOfPair_comp, Pair.completedTensor.assocHom_comp_assocSymmHom, comapOfPair_id]

section AssociatorAffinoid

variable {T : Pair B} {U : Pair C} {V : Pair D}
  (hT : IsSheafyForEveryPresentation T.plus) (hU : IsSheafyForEveryPresentation U.plus)
  (hV : IsSheafyForEveryPresentation V.plus)
  (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus)
  (hUV : IsSheafyForEveryPresentation (U.completedTensor A V).plus)
  (hTU_V : IsSheafyForEveryPresentation ((T.completedTensor A U).completedTensor A V).plus)
  (hT_UV : IsSheafyForEveryPresentation (T.completedTensor A (U.completedTensor A V)).plus)

/-- The affinoid associator preserves the projection to `Spa(B, B⁺)`. -/
@[reassoc]
theorem associatorAffinoid_hom_inl :
    (associatorAffinoid T U V hTU_V hT_UV).hom ≫
        comapOfPair hT hT_UV (Pair.completedTensor.inl A T (U.completedTensor A V)) =
      comapOfPair hTU hTU_V (Pair.completedTensor.inl A (T.completedTensor A U) V) ≫
        comapOfPair hT hTU (Pair.completedTensor.inl A T U) := by
  rw [associatorAffinoid_hom, ← comapOfPair_comp, ← comapOfPair_comp,
    Pair.completedTensor.assocSymmHom_comp_inl]

/-- The affinoid associator preserves the projection to `Spa(C, C⁺)`. -/
@[reassoc]
theorem associatorAffinoid_hom_inr_inl :
    (associatorAffinoid T U V hTU_V hT_UV).hom ≫
        comapOfPair hUV hT_UV (Pair.completedTensor.inr A T (U.completedTensor A V)) ≫
          comapOfPair hU hUV (Pair.completedTensor.inl A U V) =
      comapOfPair hTU hTU_V (Pair.completedTensor.inl A (T.completedTensor A U) V) ≫
        comapOfPair hU hTU (Pair.completedTensor.inr A T U) := by
  rw [associatorAffinoid_hom, ← comapOfPair_comp, ← comapOfPair_comp, ← comapOfPair_comp,
    Pair.completedTensor.assocSymmHom_comp_inr_comp_inl]

/-- The affinoid associator preserves the projection to `Spa(D, D⁺)`. -/
@[reassoc]
theorem associatorAffinoid_hom_inr_inr :
    (associatorAffinoid T U V hTU_V hT_UV).hom ≫
        comapOfPair hUV hT_UV (Pair.completedTensor.inr A T (U.completedTensor A V)) ≫
          comapOfPair hV hUV (Pair.completedTensor.inr A U V) =
      comapOfPair hV hTU_V (Pair.completedTensor.inr A (T.completedTensor A U) V) := by
  rw [associatorAffinoid_hom, ← comapOfPair_comp, ← comapOfPair_comp,
    Pair.completedTensor.assocSymmHom_comp_inr_comp_inr]

end AssociatorAffinoid

end Associator

end Affinoid

end TauCeti.AdicSpace.FibreProduct
