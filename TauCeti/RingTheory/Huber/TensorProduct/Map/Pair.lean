/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Map.Basic
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Functoriality of completed tensor products of Huber pairs

Morphisms `(B, B⁺) → (B', B'⁺)` and `(C, C⁺) → (C', C'⁺)` of Huber pairs lying over a ring
homomorphism `α : A → A'` induce a morphism of completed tensor products of Huber pairs
`(B, B⁺) ⊗̂_A (C, C⁺) → (B', B'⁺) ⊗̂_{A'} (C', C'⁺)`, functorially in identities and
composites. The underlying ring homomorphism is `TauCeti.Huber.CompletedTensor.map` from
`TauCeti.RingTheory.Huber.TensorProduct.Map.Basic`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensor.map`: the induced morphism of completed tensor products of
  Huber pairs.

## Main results

* `TauCeti.Huber.Pair.completedTensor.map_id`, `TauCeti.Huber.Pair.completedTensor.map_comp`:
  functoriality.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, proof of Proposition 1.2.2(1).
* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1 (the universal property of the
  completed tensor product).
-/

public section

namespace TauCeti.Huber.Pair.completedTensor

variable {A B C A' B' C' A'' B'' C'' : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing A'] [CommRing B'] [CommRing C']
  [CommRing A''] [CommRing B''] [CommRing C'']
  [Algebra A B] [Algebra A C] [Algebra A' B'] [Algebra A' C'] [Algebra A'' B''] [Algebra A'' C'']
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace A'] [TopologicalSpace B'] [TopologicalSpace C']
  [TopologicalSpace A''] [TopologicalSpace B''] [TopologicalSpace C'']
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsTopologicalRing A'] [IsTopologicalRing B'] [IsTopologicalRing C']
  [IsTopologicalRing A''] [IsTopologicalRing B''] [IsTopologicalRing C'']
  [IsHuberRing B] [IsHuberRing C] [IsHuberRing B'] [IsHuberRing C'] [IsHuberRing B'']
  [IsHuberRing C'']
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A' B')] [IsAdicHom (algebraMap A' C')]
  [IsAdicHom (algebraMap A'' B'')] [IsAdicHom (algebraMap A'' C'')]
  {S : Pair B} {T : Pair C} {S' : Pair B'} {T' : Pair C'} {S'' : Pair B''} {T'' : Pair C''}
  (α : A →+* A') (f : Hom S S') (g : Hom T T')
  (hf : f.toRingHom.comp (algebraMap A B) = (algebraMap A' B').comp α)
  (hg : g.toRingHom.comp (algebraMap A C) = (algebraMap A' C').comp α)

/-- The morphism of completed tensor products of Huber pairs
`(B, B⁺) ⊗̂_A (C, C⁺) → (B', B'⁺) ⊗̂_{A'} (C', C'⁺)` induced by morphisms of Huber pairs
`(B, B⁺) → (B', B'⁺)` and `(C, C⁺) → (C', C'⁺)` lying over `α : A → A'`. -/
noncomputable def map : Hom (S.completedTensor A T) (S'.completedTensor A' T') :=
  lift ((inl A' S' T').comp f) ((inr A' S' T').comp g) (by
    simpa only [Hom.toRingHom_comp, toRingHom_inl, toRingHom_inr] using
      CompletedTensor.inl_comp_comp_algebraMap α f.toRingHom g.toRingHom hf hg)

/-- The underlying ring homomorphism of the induced morphism of Huber pairs is the induced map of
completed tensor rings. -/
@[simp] theorem toRingHom_map :
    (map α f g hf hg).toRingHom = CompletedTensor.map α f.toRingHom g.toRingHom hf hg
      f.continuous_toRingHom g.continuous_toRingHom :=
  (CompletedTensor.eq_map_iff (map α f g hf hg).continuous_toRingHom).mpr (by
    simp only [map, toRingHom_lift, CompletedTensor.lift_comp_inl, CompletedTensor.lift_comp_inr,
      Hom.toRingHom_comp, toRingHom_inl, toRingHom_inr, and_self])

/-- The induced morphism restricts to `f` on the left factor. -/
@[simp] theorem map_comp_inl : (map α f g hf hg).comp (inl A S T) = (inl A' S' T').comp f := by
  ext1
  simp

/-- The induced morphism restricts to `g` on the right factor. -/
@[simp] theorem map_comp_inr : (map α f g hf hg).comp (inr A S T) = (inr A' S' T').comp g := by
  ext1
  simp

variable (A S T) in
/-- The identity morphisms induce the identity of the completed tensor product. -/
@[simp] theorem map_id :
    map (RingHom.id A) (Hom.id S) (Hom.id T) (by simp) (by simp) =
      Hom.id (S.completedTensor A T) := by
  ext1
  simp

/-- The morphism induced by composites is the composite of the induced morphisms. -/
theorem map_comp (α' : A' →+* A'') (f' : Hom S' S'') (g' : Hom T' T'')
    (hf' : f'.toRingHom.comp (algebraMap A' B') = (algebraMap A'' B'').comp α')
    (hg' : g'.toRingHom.comp (algebraMap A' C') = (algebraMap A'' C'').comp α') :
    map (α'.comp α) (f'.comp f) (g'.comp g)
        (by rw [Hom.toRingHom_comp, RingHom.comp_assoc, hf, ← RingHom.comp_assoc, hf',
          RingHom.comp_assoc])
        (by rw [Hom.toRingHom_comp, RingHom.comp_assoc, hg, ← RingHom.comp_assoc, hg',
          RingHom.comp_assoc]) =
      (map α' f' g' hf' hg').comp (map α f g hf hg) := by
  ext1
  simpa using CompletedTensor.map_comp α f.toRingHom g.toRingHom hf hg f.continuous_toRingHom
    g.continuous_toRingHom α' f'.toRingHom g'.toRingHom hf' hg' f'.continuous_toRingHom
    g'.continuous_toRingHom

end TauCeti.Huber.Pair.completedTensor
