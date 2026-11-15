/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Topological closures and pointwise limits in nonunital star algebras

This file provides:

* `NonUnitalStarSubalgebra.topologicalClosure_coe`: `@[simp]` lemma identifying the underlying set
  of `s.topologicalClosure` with `closure (s : Set A)`, matching
  `StarSubalgebra.topologicalClosure_coe`.
* `TauCeti.isClosed_setOfPred_map_star`: in a `T2Space` with continuous `star`, the set of
  functions `A → B` preserving `star` is closed in the topology of pointwise convergence.
* `NonUnitalStarAlgHom.ofMemClosureRangeCoe`, `NonUnitalStarAlgHom.ofTendsto`, and
  `NonUnitalStarAlgHom.isClosed_range_coe`: bundled nonunital star algebra homomorphisms from
  pointwise closure membership or pointwise limits, modeled on Mathlib's
  `mulHomOfMemClosureRangeCoe`, `mulHomOfTendsto`, `linearMapOfMemClosureRangeCoe`, and
  `linearMapOfTendsto`.
-/

public section

open Filter Topology

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
  [NonUnitalSemiring A] [Module R A] [ContinuousStar A]
  [ContinuousConstSMul R A] [IsSemitopologicalSemiring A]

/-- Coercing `s.topologicalClosure` to `Set A` gives the topological closure
`closure (s : Set A)`. -/
@[simp]
theorem topologicalClosure_coe (s : NonUnitalStarSubalgebra R A) :
    (s.topologicalClosure : Set A) = _root_.closure (s : Set A) :=
  (rfl)

end NonUnitalStarSubalgebra

namespace TauCeti

/-- In a `T2Space` with continuous `star`, the set of functions `A → B` preserving `star` is closed
in the topology of pointwise convergence. -/
theorem isClosed_setOfPred_map_star (A B : Type*) [Star A] [TopologicalSpace B] [T2Space B]
    [Star B] [ContinuousStar B] : IsClosed {f : A → B | ∀ x, f (star x) = star (f x)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_eq (continuous_apply _) (continuous_apply _).star

end TauCeti

namespace NonUnitalStarAlgHom

section PointwiseLimits

variable {R A B : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [TopologicalSpace B] [T2Space B] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
  [ContinuousAdd B] [ContinuousMul B] [ContinuousConstSMul R B] [ContinuousStar B]

section Closure

variable {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

/-- Construct a bundled `NonUnitalStarAlgHom` from a function `f : A → B` belonging to the
pointwise closure of the range of coercion from a type `F` of nonunital star algebra
homomorphisms. -/
def ofMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (Set.range fun (g : F) (a : A) ↦ g a)) : A →⋆ₙₐ[R] B where
  toFun := f
  map_zero' := (addMonoidHomOfMemClosureRangeCoe f hf).map_zero'
  map_add' := (addMonoidHomOfMemClosureRangeCoe f hf).map_add'
  map_mul' := (mulHomOfMemClosureRangeCoe f hf).map_mul'
  map_smul' := (isClosed_setOfPred_map_smul A B (id : R → R)).closure_subset_iff.2
    (Set.range_subset_iff.2 fun g r x ↦ map_smul g r x) hf
  map_star' := (TauCeti.isClosed_setOfPred_map_star A B).closure_subset_iff.2
    (Set.range_subset_iff.2 map_star) hf

/-- Coercing `NonUnitalStarAlgHom.ofMemClosureRangeCoe f hf` to a function recovers `f`. -/
@[simp]
theorem coeFn_ofMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (Set.range fun (g : F) (a : A) ↦ g a)) :
    ⇑(ofMemClosureRangeCoe (R := R) f hf) = f :=
  (rfl)

/-- Evaluating `NonUnitalStarAlgHom.ofMemClosureRangeCoe f hf` at `a` gives `f a`. -/
@[simp]
theorem ofMemClosureRangeCoe_apply (f : A → B)
    (hf : f ∈ closure (Set.range fun (g : F) (a : A) ↦ g a)) (a : A) :
    ofMemClosureRangeCoe (R := R) f hf a = f a :=
  (rfl)

/-- Construct a bundled `NonUnitalStarAlgHom` from the pointwise limit of a family of nonunital
star algebra homomorphisms along a nontrivial filter. -/
def ofTendsto {α : Type*} {l : Filter α} [l.NeBot] (f : A → B) (g : α → F)
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) : A →⋆ₙₐ[R] B :=
  ofMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ ↦ Set.mem_range_self _

/-- Coercing `NonUnitalStarAlgHom.ofTendsto f g h` to a function recovers `f`. -/
@[simp]
theorem coeFn_ofTendsto {α : Type*} {l : Filter α} [l.NeBot] (f : A → B) (g : α → F)
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) :
    ⇑(ofTendsto (R := R) f g h) = f :=
  (rfl)

/-- Evaluating `NonUnitalStarAlgHom.ofTendsto f g h` at `a` gives `f a`. -/
@[simp]
theorem ofTendsto_apply {α : Type*} {l : Filter α} [l.NeBot] (f : A → B) (g : α → F)
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) (a : A) :
    ofTendsto (R := R) f g h a = f a :=
  (rfl)

end Closure

variable (R A B) in
/-- The range of coercion `(A →⋆ₙₐ[R] B) → (A → B)` is closed in the topology of pointwise
convergence when `B` is Hausdorff with continuous operations. -/
theorem isClosed_range_coe : IsClosed (Set.range ((↑) : (A →⋆ₙₐ[R] B) → A → B)) :=
  isClosed_of_closure_subset fun f hf ↦ ⟨ofMemClosureRangeCoe f hf, rfl⟩

end PointwiseLimits

end NonUnitalStarAlgHom
