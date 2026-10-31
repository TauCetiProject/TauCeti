/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Functoriality of completed tensor products

Let `A → B`, `A → C`, `A' → B'` and `A' → C'` be adic homomorphisms of Huber rings, and let
`α : A → A'`, `φ : B → B'` and `ψ : C → C'` be ring homomorphisms forming commutative squares
with the structure maps, with `φ` and `ψ` continuous. Then `φ` and `ψ` induce a continuous ring
homomorphism `B ⊗̂_A C → B' ⊗̂_{A'} C'` of separated completed tensor rings, characterized by its
values on the two coprojections. The construction is functorial: it preserves identities and
composites. No continuity of `α` is needed, since it only enters through the two squares.

For Huber pairs, morphisms `(B, B⁺) → (B', B'⁺)` and `(C, C⁺) → (C', C'⁺)` over `α` induce a
morphism of completed tensor products of Huber pairs `(B, B⁺) ⊗̂_A (C, C⁺) → (B', B'⁺) ⊗̂_{A'}
(C', C'⁺)`, again functorially. Both constructions are instances of the universal property of the
completed tensor product, applied to the composites of `φ` and `ψ` with the target coprojections.

## Main definitions

* `TauCeti.Huber.CompletedTensor.map`: the continuous ring homomorphism of completed tensor rings
  induced by compatible continuous ring homomorphisms of the factors.
* `TauCeti.Huber.Pair.completedTensor.map`: the induced morphism of completed tensor products of
  Huber pairs.

## Main results

* `TauCeti.Huber.CompletedTensor.map_toCompletion`: on the dense image of the algebraic tensor
  product, `map` is Mathlib's heterobasic tensor product `Algebra.TensorProduct.mapRingHom` of
  the given maps.
* `TauCeti.Huber.CompletedTensor.map_id`, `TauCeti.Huber.CompletedTensor.map_comp`,
  `TauCeti.Huber.Pair.completedTensor.map_id`, `TauCeti.Huber.Pair.completedTensor.map_comp`:
  functoriality.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, proof of Proposition 1.2.2(1).
* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1 (the universal property of the
  completed tensor product).
-/

public section

open TensorProduct

namespace TauCeti.Huber

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
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A' B')] [IsAdicHom (algebraMap A' C')]
  [IsAdicHom (algebraMap A'' B'')] [IsAdicHom (algebraMap A'' C'')]

namespace CompletedTensor

omit [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalRing A]
  [IsTopologicalRing B] [IsTopologicalRing C] [IsAdicHom (algebraMap A B)]
  [IsAdicHom (algebraMap A C)] in
/-- The composites of `φ` and `ψ` with the target coprojections agree on `A`. -/
private theorem inl_comp_comp_algebraMap (α : A →+* A') (φ : B →+* B') (ψ : C →+* C')
    (hφ : φ.comp (algebraMap A B) = (algebraMap A' B').comp α)
    (hψ : ψ.comp (algebraMap A C) = (algebraMap A' C').comp α) :
    ((inl A' B' C').comp φ).comp (algebraMap A B) =
      ((inr A' B' C').comp ψ).comp (algebraMap A C) := by
  rw [RingHom.comp_assoc, hφ, RingHom.comp_assoc, hψ, ← RingHom.comp_assoc,
    inl_comp_algebraMap, RingHom.comp_assoc]

variable (α : A →+* A') (φ : B →+* B') (ψ : C →+* C')
  (hφ : φ.comp (algebraMap A B) = (algebraMap A' B').comp α)
  (hψ : ψ.comp (algebraMap A C) = (algebraMap A' C').comp α)
  (hφc : Continuous φ) (hψc : Continuous ψ)

/-- The continuous ring homomorphism `B ⊗̂_A C → B' ⊗̂_{A'} C'` of completed tensor rings induced
by continuous ring homomorphisms `φ : B → B'` and `ψ : C → C'` lying over `α : A → A'`. -/
noncomputable def map : CompletedTensor A B C →+* CompletedTensor A' B' C' :=
  lift ((inl A' B' C').comp φ) ((inr A' B' C').comp ψ) (inl_comp_comp_algebraMap α φ ψ hφ hψ)
    ((continuous_inl A' B' C').comp hφc) ((continuous_inr A' B' C').comp hψc)

/-- The induced map of completed tensor rings is continuous. -/
@[fun_prop] theorem continuous_map : Continuous (map α φ ψ hφ hψ hφc hψc) :=
  continuous_lift _ _ _ _ _

/-- The induced map sends the left coprojection of `b` to the left coprojection of `φ b`. -/
@[simp] theorem map_inl (b : B) :
    map α φ ψ hφ hψ hφc hψc (inl A B C b) = inl A' B' C' (φ b) :=
  lift_inl _ _ _ _ _ b

/-- The induced map sends the right coprojection of `c` to the right coprojection of `ψ c`. -/
@[simp] theorem map_inr (c : C) :
    map α φ ψ hφ hψ hφc hψc (inr A B C c) = inr A' B' C' (ψ c) :=
  lift_inr _ _ _ _ _ c

/-- The induced map restricts to `φ` on the left factor. -/
@[simp] theorem map_comp_inl :
    (map α φ ψ hφ hψ hφc hψc).comp (inl A B C) = (inl A' B' C').comp φ :=
  lift_comp_inl _ _ _ _ _

/-- The induced map restricts to `ψ` on the right factor. -/
@[simp] theorem map_comp_inr :
    (map α φ ψ hφ hψ hφc hψc).comp (inr A B C) = (inr A' B' C').comp ψ :=
  lift_comp_inr _ _ _ _ _

/-- On the algebraic tensor product, the induced map is the heterobasic tensor product
`Algebra.TensorProduct.mapRingHom` of `φ` and `ψ`. -/
@[simp] theorem map_toCompletion (x : B ⊗[A] C) :
    map α φ ψ hφ hψ hφc hψc (toCompletion A B C x) =
      toCompletion A' B' C' (Algebra.TensorProduct.mapRingHom α φ ψ hφ hψ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b c => simp
  | add x y hx hy => simp [hx, hy]

/-- The induced map is compatible with the canonical maps from the algebraic tensor products. -/
theorem map_comp_toCompletion :
    (map α φ ψ hφ hψ hφc hψc).comp (toCompletion A B C) =
      (toCompletion A' B' C').comp (Algebra.TensorProduct.mapRingHom α φ ψ hφ hψ) :=
  RingHom.ext (map_toCompletion α φ ψ hφ hψ hφc hψc)

variable {α φ ψ hφ hψ hφc hψc} in
/-- A continuous ring homomorphism `B ⊗̂_A C → B' ⊗̂_{A'} C'` is the induced map exactly when it
restricts to `φ` and `ψ` on the two factors. -/
theorem eq_map_iff {f : CompletedTensor A B C →+* CompletedTensor A' B' C'} (hf : Continuous f) :
    f = map α φ ψ hφ hψ hφc hψc ↔
      f.comp (inl A B C) = (inl A' B' C').comp φ ∧ f.comp (inr A B C) = (inr A' B' C').comp ψ := by
  refine ⟨fun h ↦ h ▸ ⟨map_comp_inl .., map_comp_inr ..⟩, fun ⟨hB, hC⟩ ↦ ?_⟩
  exact hom_ext hf (continuous_map ..) (by rw [hB, map_comp_inl]) (by rw [hC, map_comp_inr])

variable (A B C) in
/-- The identity maps induce the identity of the completed tensor ring. -/
@[simp] theorem map_id :
    map (RingHom.id A) (RingHom.id B) (RingHom.id C) rfl rfl continuous_id continuous_id =
      RingHom.id (CompletedTensor A B C) :=
  Eq.symm <| (eq_map_iff continuous_id).mpr ⟨rfl, rfl⟩

/-- The map induced by composites is the composite of the induced maps. -/
theorem map_comp (α' : A' →+* A'') (φ' : B' →+* B'') (ψ' : C' →+* C'')
    (hφ' : φ'.comp (algebraMap A' B') = (algebraMap A'' B'').comp α')
    (hψ' : ψ'.comp (algebraMap A' C') = (algebraMap A'' C'').comp α')
    (hφc' : Continuous φ') (hψc' : Continuous ψ') :
    map (α'.comp α) (φ'.comp φ) (ψ'.comp ψ)
        (by rw [RingHom.comp_assoc, hφ, ← RingHom.comp_assoc, hφ', RingHom.comp_assoc])
        (by rw [RingHom.comp_assoc, hψ, ← RingHom.comp_assoc, hψ', RingHom.comp_assoc])
        (hφc'.comp hφc) (hψc'.comp hψc) =
      (map α' φ' ψ' hφ' hψ' hφc' hψc').comp (map α φ ψ hφ hψ hφc hψc) := by
  have hc : Continuous ((map α' φ' ψ' hφ' hψ' hφc' hψc').comp (map α φ ψ hφ hψ hφc hψc)) := by
    rw [RingHom.coe_comp]
    fun_prop
  exact Eq.symm <| (eq_map_iff hc).mpr ⟨by ext; simp, by ext; simp⟩

end CompletedTensor

namespace Pair.completedTensor

variable [IsHuberRing B] [IsHuberRing C] [IsHuberRing B'] [IsHuberRing C'] [IsHuberRing B'']
  [IsHuberRing C''] {S : Pair B} {T : Pair C} {S' : Pair B'} {T' : Pair C'} {S'' : Pair B''}
  {T'' : Pair C''} (α : A →+* A') (f : Hom S S') (g : Hom T T')
  (hf : f.toRingHom.comp (algebraMap A B) = (algebraMap A' B').comp α)
  (hg : g.toRingHom.comp (algebraMap A C) = (algebraMap A' C').comp α)

/-- The morphism of completed tensor products of Huber pairs
`(B, B⁺) ⊗̂_A (C, C⁺) → (B', B'⁺) ⊗̂_{A'} (C', C'⁺)` induced by morphisms of Huber pairs
`(B, B⁺) → (B', B'⁺)` and `(C, C⁺) → (C', C'⁺)` lying over `α : A → A'`. -/
noncomputable def map : Hom (S.completedTensor A T) (S'.completedTensor A' T') :=
  lift ((inl A' S' T').comp f) ((inr A' S' T').comp g) (by
    simpa using CompletedTensor.inl_comp_comp_algebraMap α f.toRingHom g.toRingHom hf hg)

/-- The underlying ring homomorphism of the induced morphism of Huber pairs is the induced map of
completed tensor rings. -/
@[simp] theorem toRingHom_map :
    (map α f g hf hg).toRingHom = CompletedTensor.map α f.toRingHom g.toRingHom hf hg
      f.continuous_toRingHom g.continuous_toRingHom := by
  simp only [map, toRingHom_lift, Hom.toRingHom_comp, toRingHom_inl, toRingHom_inr]
  rfl

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

end Pair.completedTensor

end TauCeti.Huber
