/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.Affinoid
public import TauCeti.RingTheory.Huber.TensorProduct.Coherence
public import TauCeti.RingTheory.Huber.TensorProduct.Symmetry
public import TauCeti.RingTheory.Huber.TensorProduct.Unit

/-!
# Associativity, symmetry and unit of fibre products of adic spaces on affinoid charts

Fibre products of adic spaces do not exist in general. For `f : X ⟶ S`, `g : Y ⟶ S` and
`h : Z ⟶ S`, the two parenthesizations `(X ×_S Y) ×_S Z` and `X ×_S (Y ×_S Z)` of the ordered
triple exist under the hypotheses of `TauCeti.AdicSpace.hasPullback_snd_comp` and
`TauCeti.AdicSpace.hasPullback_fst_comp`. Whenever these composites exist, Mathlib's
`pullbackAssoc f g g h`, `pullbackSymmetry f g` and `asIso (pullback.fst f (𝟙 S))` are the
associativity, symmetry and unit isomorphisms. Each of them is determined by its composites with
the projections to the factors (`pullback.hom_ext`), so two composites of these isomorphisms
between the same existing fibre products agree as soon as they induce the same maps to the
factors.

This file computes these isomorphisms on affinoid charts, where they are isomorphisms of the
displayed `Spa` objects given by ring isomorphisms of completed tensor products. Since `Spa` is
contravariant, the associator `Spa((B ⊗̂_A C) ⊗̂_A D) ≅ Spa(B ⊗̂_A (C ⊗̂_A D))` is `Spa` of the
inverse ring associator (`TauCeti.AdicSpace.associatorAffinoid`), the comparison of the two chart
squares `Spa(B ⊗̂_A C)` and `Spa(C ⊗̂_A B)` is `Spa` of the exchange of the two factors
(`TauCeti.AdicSpace.affinoid_isoIsPullback_flip_hom`), and the right unitor
`Spa(B ⊗̂_A A) ≅ Spa(B)` is `Spa` of the left coprojection, with inverse `Spa` of `b ⊗ a ↦ b·a`
(`TauCeti.AdicSpace.rightUnitorAffinoid`). When the chart squares are pullback squares (for
instance by `TauCeti.AdicSpace.affinoid_isPullback`), the projection formulas below identify
these chart isomorphisms with the categorical comparisons above. The sheafiness of the second
parenthesization and of the unit tensor follow from that of the first parenthesization and of
`B` (`TauCeti.Huber.IsSheafyForEveryPresentation.completedTensor_comm`,
`TauCeti.Huber.IsSheafyForEveryPresentation.completedTensor_assoc`,
`TauCeti.Huber.IsSheafyForEveryPresentation.completedTensor_rightUnitor`).

## Main results

* `TauCeti.AdicSpace.associatorAffinoid`, `TauCeti.AdicSpace.affinoid_isoIsPullback_flip_hom`,
  `TauCeti.AdicSpace.rightUnitorAffinoid`: the chart formulas.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Proposition 3.7.
* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.6, Theorem 8.56.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Sheafiness of the rearranged completed tensor products -/

namespace TauCeti.Huber.IsSheafyForEveryPresentation

section Symmetry

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- Exchanging the two factors preserves `IsSheafyForEveryPresentation` of a completed tensor
product of Huber pairs. -/
theorem completedTensor_comm {T : Pair B} {U : Pair C}
    (h : IsSheafyForEveryPresentation (T.completedTensor A U).plus) :
    IsSheafyForEveryPresentation (U.completedTensor A T).plus :=
  (isSheafyForEveryPresentation_iff_of_ringEquiv (CompletedTensor.comm A B C)
    (CompletedTensor.continuous_comm A B C)
    (by simpa only [CompletedTensor.comm_symm] using CompletedTensor.continuous_comm A C B)
    (Pair.completedTensor.comm_plus A T U)).mp h

end Symmetry

section Associator

variable {A B C D : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsHuberRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A D)]

/-- Reassociating an iterated completed tensor product of Huber pairs preserves
`IsSheafyForEveryPresentation`. -/
theorem completedTensor_assoc {T : Pair B} {U : Pair C} {V : Pair D}
    (h : IsSheafyForEveryPresentation ((T.completedTensor A U).completedTensor A V).plus) :
    IsSheafyForEveryPresentation (T.completedTensor A (U.completedTensor A V)).plus :=
  (isSheafyForEveryPresentation_iff_of_ringEquiv (CompletedTensor.assoc A B C D)
    (CompletedTensor.continuous_assoc A B C D) (CompletedTensor.continuous_assoc_symm A B C D)
    (Pair.completedTensor.assoc_plus A T U V)).mp h

end Associator

section Unit

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T2Space B] [IsHuberRing B] [Algebra A B] [IsAdicHom (algebraMap A B)]

/-- If `A⁺` maps into `B⁺`, then `(B, B⁺) ⊗̂_A (A, A⁺)` satisfies `IsSheafyForEveryPresentation`
whenever `(B, B⁺)` does, since the right unitor identifies the two pairs. -/
theorem completedTensor_rightUnitor {T : Pair B} (h : IsSheafyForEveryPresentation T.plus)
    (S : Pair A) (hplus : ∀ a ∈ S.plus, algebraMap A B a ∈ T.plus) :
    IsSheafyForEveryPresentation (T.completedTensor A S).plus :=
  (isSheafyForEveryPresentation_iff_of_ringEquiv (CompletedTensor.rightUnitor A B)
    (CompletedTensor.continuous_rightUnitor A B) (CompletedTensor.continuous_rightUnitor_symm A B)
    (Pair.completedTensor.rightUnitor_plus S T hplus)).mpr h

end Unit

end TauCeti.Huber.IsSheafyForEveryPresentation

/-! ### Chart formulas -/

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

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
theorem affinoid_isoIsPullback_flip_hom {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus)
    (f : Pair.Hom S T) (g : Pair.Hom S U)
    (hf : f.toRingHom = algebraMap A B) (hg : g.toRingHom = algebraMap A C) :
    ((affinoid_isPullback hS hT hU hTU f g hf hg).isoIsPullback _ _
        (affinoid_isPullback hS hU hT hTU.completedTensor_comm g f hg hf).flip).hom =
      comapOfPair hTU.completedTensor_comm hTU (Pair.completedTensor.commHom A U T) := by
  apply (affinoid_isPullback hS hU hT hTU.completedTensor_comm g f hg hf).flip.hom_ext
  · rw [IsPullback.isoIsPullback_hom_fst, ← comapOfPair_comp,
      Pair.completedTensor.commHom_comp_inr]
  · rw [IsPullback.isoIsPullback_hom_snd, ← comapOfPair_comp,
      Pair.completedTensor.commHom_comp_inl]

end Symmetry

section Unit

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T2Space B] [IsHuberRing B] [Algebra A B] [IsAdicHom (algebraMap A B)]

/-- **Right unitor on affinoid charts**: `Spa((B, B⁺) ⊗̂_A (A, A⁺)) ≅ Spa(B, B⁺)` is `Spa` of the
left coprojection, with inverse `Spa` of the multiplication `b ⊗ a ↦ b·a`. -/
noncomputable def rightUnitorAffinoid (S : Pair A) {T : Pair B}
    (hT : IsSheafyForEveryPresentation T.plus)
    (hplus : ∀ a ∈ S.plus, algebraMap A B a ∈ T.plus) :
    ofPair (T.completedTensor A S) (hT.completedTensor_rightUnitor S hplus) ≅ ofPair T hT where
  hom := comapOfPair hT _ (Pair.completedTensor.inl A T S)
  inv := comapOfPair _ hT (Pair.completedTensor.rightUnitorHom S T hplus)
  hom_inv_id := by
    rw [← comapOfPair_comp, Pair.completedTensor.inl_comp_rightUnitorHom, comapOfPair_id]
  inv_hom_id := by
    rw [← comapOfPair_comp, Pair.completedTensor.rightUnitorHom_comp_inl, comapOfPair_id]

/-- The affinoid right unitor is `Spa` of the left coprojection. -/
@[simp]
theorem rightUnitorAffinoid_hom (S : Pair A) {T : Pair B}
    (hT : IsSheafyForEveryPresentation T.plus)
    (hplus : ∀ a ∈ S.plus, algebraMap A B a ∈ T.plus) :
    (rightUnitorAffinoid S hT hplus).hom = comapOfPair hT _ (Pair.completedTensor.inl A T S) :=
  (rfl)

/-- The inverse affinoid right unitor is `Spa` of the multiplication `b ⊗ a ↦ b·a`. -/
@[simp]
theorem rightUnitorAffinoid_inv (S : Pair A) {T : Pair B}
    (hT : IsSheafyForEveryPresentation T.plus)
    (hplus : ∀ a ∈ S.plus, algebraMap A B a ∈ T.plus) :
    (rightUnitorAffinoid S hT hplus).inv =
      comapOfPair _ hT (Pair.completedTensor.rightUnitorHom S T hplus) :=
  (rfl)

/-- The inverse affinoid right unitor composed with the second projection is the structure
morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)`, as for the unit `(𝟙, f)` of a general fibre product. -/
@[reassoc]
theorem rightUnitorAffinoid_inv_comp_inr {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (f : Pair.Hom S T) (hf : f.toRingHom = algebraMap A B) :
    (rightUnitorAffinoid S hT (fun a ha ↦ hf ▸ f.map_mem_plus a ha)).inv ≫
        comapOfPair hS _ (Pair.completedTensor.inr A T S) =
      comapOfPair hS hT f := by
  rw [rightUnitorAffinoid_inv, ← comapOfPair_comp]
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

/-- **Associativity on affinoid charts**: the associator
`Spa(((B, B⁺) ⊗̂_A (C, C⁺)) ⊗̂_A (D, D⁺)) ≅ Spa((B, B⁺) ⊗̂_A ((C, C⁺) ⊗̂_A (D, D⁺)))` is `Spa` of
the inverse ring associator `b ⊗ (c ⊗ d) ↦ (b ⊗ c) ⊗ d`; its inverse is `Spa` of the ring
associator. -/
noncomputable def associatorAffinoid (T : Pair B) (U : Pair C) (V : Pair D)
    (hTU_V : IsSheafyForEveryPresentation ((T.completedTensor A U).completedTensor A V).plus) :
    ofPair _ hTU_V ≅ ofPair _ hTU_V.completedTensor_assoc where
  hom := comapOfPair _ hTU_V (Pair.completedTensor.assocSymmHom A T U V)
  inv := comapOfPair hTU_V _ (Pair.completedTensor.assocHom A T U V)
  hom_inv_id := by
    rw [← comapOfPair_comp, Pair.completedTensor.assocSymmHom_comp_assocHom, comapOfPair_id]
  inv_hom_id := by
    rw [← comapOfPair_comp, Pair.completedTensor.assocHom_comp_assocSymmHom, comapOfPair_id]

/-- The affinoid associator is `Spa` of the inverse ring associator. -/
@[simp]
theorem associatorAffinoid_hom (T : Pair B) (U : Pair C) (V : Pair D)
    (hTU_V : IsSheafyForEveryPresentation ((T.completedTensor A U).completedTensor A V).plus) :
    (associatorAffinoid T U V hTU_V).hom =
      comapOfPair _ hTU_V (Pair.completedTensor.assocSymmHom A T U V) :=
  (rfl)

/-- The inverse affinoid associator is `Spa` of the ring associator. -/
@[simp]
theorem associatorAffinoid_inv (T : Pair B) (U : Pair C) (V : Pair D)
    (hTU_V : IsSheafyForEveryPresentation ((T.completedTensor A U).completedTensor A V).plus) :
    (associatorAffinoid T U V hTU_V).inv =
      comapOfPair hTU_V _ (Pair.completedTensor.assocHom A T U V) :=
  (rfl)

section AssociatorAffinoid

variable {T : Pair B} {U : Pair C} {V : Pair D}
  (hT : IsSheafyForEveryPresentation T.plus) (hU : IsSheafyForEveryPresentation U.plus)
  (hV : IsSheafyForEveryPresentation V.plus)
  (hTU : IsSheafyForEveryPresentation (T.completedTensor A U).plus)
  (hUV : IsSheafyForEveryPresentation (U.completedTensor A V).plus)
  (hTU_V : IsSheafyForEveryPresentation ((T.completedTensor A U).completedTensor A V).plus)

/-- The affinoid associator preserves the projection to `Spa(B, B⁺)`. -/
@[reassoc]
theorem associatorAffinoid_hom_inl :
    (associatorAffinoid T U V hTU_V).hom ≫
        comapOfPair hT hTU_V.completedTensor_assoc
          (Pair.completedTensor.inl A T (U.completedTensor A V)) =
      comapOfPair hTU hTU_V (Pair.completedTensor.inl A (T.completedTensor A U) V) ≫
        comapOfPair hT hTU (Pair.completedTensor.inl A T U) := by
  simp only [associatorAffinoid_hom, ← comapOfPair_comp,
    Pair.completedTensor.assocSymmHom_comp_inl]

/-- The affinoid associator preserves the projection to `Spa(C, C⁺)`. -/
@[reassoc]
theorem associatorAffinoid_hom_inr_inl :
    (associatorAffinoid T U V hTU_V).hom ≫
        comapOfPair hUV hTU_V.completedTensor_assoc
          (Pair.completedTensor.inr A T (U.completedTensor A V)) ≫
          comapOfPair hU hUV (Pair.completedTensor.inl A U V) =
      comapOfPair hTU hTU_V (Pair.completedTensor.inl A (T.completedTensor A U) V) ≫
        comapOfPair hU hTU (Pair.completedTensor.inr A T U) := by
  simp only [associatorAffinoid_hom, ← comapOfPair_comp,
    Pair.completedTensor.assocSymmHom_comp_inr_comp_inl]

/-- The affinoid associator preserves the projection to `Spa(D, D⁺)`. -/
@[reassoc]
theorem associatorAffinoid_hom_inr_inr :
    (associatorAffinoid T U V hTU_V).hom ≫
        comapOfPair hUV hTU_V.completedTensor_assoc
          (Pair.completedTensor.inr A T (U.completedTensor A V)) ≫
          comapOfPair hV hUV (Pair.completedTensor.inr A U V) =
      comapOfPair hV hTU_V (Pair.completedTensor.inr A (T.completedTensor A U) V) := by
  simp only [associatorAffinoid_hom, ← comapOfPair_comp,
    Pair.completedTensor.assocSymmHom_comp_inr_comp_inr]

end AssociatorAffinoid

end Associator

end TauCeti.AdicSpace
