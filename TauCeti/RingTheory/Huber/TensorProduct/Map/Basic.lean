/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Completion
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Functoriality of completed tensor rings

Let `A → B`, `A → C`, `A' → B'` and `A' → C'` be adic homomorphisms of Huber rings, and let
`α : A → A'`, `φ : B → B'` and `ψ : C → C'` be ring homomorphisms forming commutative squares
with the structure maps, with `φ` and `ψ` continuous. Then `φ` and `ψ` induce a continuous ring
homomorphism `B ⊗̂_A C → B' ⊗̂_{A'} C'` of separated completed tensor rings, characterized by its
values on the two coprojections. The construction is functorial: it preserves identities and
composites. No continuity of `α` is needed, since it only enters through the two squares.

Only the topological ring maps are constructed here; functoriality on completed tensor products of
Huber pairs is in `TauCeti.RingTheory.Huber.TensorProduct.Map.Pair`.

Continuous `A`-algebra isomorphisms `B ≃A[A] B'` and `C ≃A[A] C'` induce a continuous
`A`-algebra isomorphism `B ⊗̂_A C ≃A[A] B' ⊗̂_A C'` of completed tensor rings.

## Main definitions

* `TauCeti.Huber.CompletedTensor.map`: the continuous ring homomorphism of completed tensor rings
  induced by compatible continuous ring homomorphisms of the factors.
* `TauCeti.Huber.CompletedTensor.congr`: the continuous `A`-algebra isomorphism of completed
  tensor rings induced by continuous `A`-algebra isomorphisms of the factors.

## Main results

* `TauCeti.Huber.CompletedTensor.map_toCompletion`: on the dense image of the algebraic tensor
  product, `map` is Mathlib's heterobasic tensor product `Algebra.TensorProduct.mapRingHom` of
  the given maps.
* `TauCeti.Huber.CompletedTensor.map_id`, `TauCeti.Huber.CompletedTensor.map_comp`: functoriality.

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
theorem inl_comp_comp_algebraMap (α : A →+* A') (φ : B →+* B') (ψ : C →+* C')
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

section Congr

variable [Algebra A B'] [Algebra A C'] [IsAdicHom (algebraMap A B')] [IsAdicHom (algebraMap A C')]
  (e : B ≃A[A] B') (f : C ≃A[A] C')

/-- The isomorphism `B ⊗̂_A C ≃A[A] B' ⊗̂_A C'` of completed tensor rings induced by continuous
`A`-algebra isomorphisms `B ≃A[A] B'` and `C ≃A[A] C'`. -/
noncomputable def congr : CompletedTensor A B C ≃A[A] CompletedTensor A B' C' where
  toAlgEquiv := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom
    (map (RingHom.id A) e f (by ext; simp [AlgHomClass.commutes])
      (by ext; simp [AlgHomClass.commutes]) (by rw [RingHom.coe_coe]; fun_prop)
      (by rw [RingHom.coe_coe]; fun_prop))
    (map (RingHom.id A) e.symm f.symm (by ext; simp [AlgHomClass.commutes])
      (by ext; simp [AlgHomClass.commutes])
      (by rw [RingHom.coe_coe]; fun_prop) (by rw [RingHom.coe_coe]; fun_prop))
    (hom_ext ((continuous_map ..).comp (continuous_map ..)) continuous_id
      (by ext; simp) (by ext; simp))
    (hom_ext ((continuous_map ..).comp (continuous_map ..)) continuous_id
      (by ext; simp) (by ext; simp)))
    fun a ↦ by simp [← inl_algebraMap, AlgHomClass.commutes]
  continuous_toFun := continuous_map ..
  continuous_invFun := continuous_map ..

/-- The induced isomorphism sends the left coprojection of `b` to that of `e b`. -/
@[simp] theorem congr_inl (b : B) : congr e f (inl A B C b) = inl A B' C' (e b) :=
  map_inl ..

/-- The induced isomorphism sends the right coprojection of `c` to that of `f c`. -/
@[simp] theorem congr_inr (c : C) : congr e f (inr A B C c) = inr A B' C' (f c) :=
  map_inr ..

/-- The inverse of the induced isomorphism sends the left coprojection of `b'` to that of
`e.symm b'`. -/
@[simp] theorem congr_symm_inl (b : B') :
    (congr e f).symm (inl A B' C' b) = inl A B C (e.symm b) :=
  map_inl ..

/-- The inverse of the induced isomorphism sends the right coprojection of `c'` to that of
`f.symm c'`. -/
@[simp] theorem congr_symm_inr (c : C') :
    (congr e f).symm (inr A B' C' c) = inr A B C (f.symm c) :=
  map_inr ..

end Congr

end CompletedTensor

end TauCeti.Huber

namespace TauCeti.Huber.CompletedTensor

variable {A B A' B' : Type*}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B']
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace A'] [IsTopologicalRing A']
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace B'] [IsUniformAddGroup B'] [NonarchimedeanRing B'] [CompleteSpace B'] [T0Space B']
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A' B')]

/-- The map on completed diagonals commutes with multiplication. -/
@[simp] theorem mulRingHom_map (α : A →+* A') (φ : B →+* B')
    (hφ : φ.comp (algebraMap A B) = (algebraMap A' B').comp α)
    (hφc : Continuous φ) (x : CompletedTensor A B B) :
    mulRingHom A' B' (CompletedTensor.map α φ φ hφ hφ hφc hφc x) =
      φ (mulRingHom A B x) := by
  have h : (mulRingHom A' B').comp (CompletedTensor.map α φ φ hφ hφ hφc hφc) =
      φ.comp (mulRingHom A B) := by
    apply CompletedTensor.hom_ext (f := (mulRingHom A' B').comp
      (CompletedTensor.map α φ φ hφ hφ hφc hφc)) (g := φ.comp (mulRingHom A B))
      ((continuous_mulRingHom A' B').comp (CompletedTensor.continuous_map ..))
      (hφc.comp (continuous_mulRingHom A B)) <;> ext b <;> simp
  exact congrArg (fun f : CompletedTensor A B B →+* B' ↦ f x) h

end TauCeti.Huber.CompletedTensor
