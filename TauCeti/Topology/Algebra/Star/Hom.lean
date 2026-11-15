/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Star

/-!
# Pointwise limits of star-algebra homomorphisms

When the target `B` is a Hausdorff topological space with continuous `star`, the star-preserving
maps `A → B` form a closed subset for the product topology (`TauCeti.isClosed_setOfPred_map_star`).
Combined with Mathlib's `addMonoidHomOfMemClosureRangeCoe`, `mulHomOfMemClosureRangeCoe`,
`monoidHomOfMemClosureRangeCoe`, and `isClosed_setOfPred_map_smul`, this upgrades any function in
the pointwise closure of bundled star-algebra homomorphisms — in particular, any pointwise limit
along a nontrivial filter — to a bundled `NonUnitalStarAlgHom` or `StarAlgHom`, and shows that the
coercion ranges of `A →⋆ₙₐ[R] B` and `A →⋆ₐ[R] B` in `A → B` are closed.

## Main definitions and results

* `TauCeti.isClosed_setOfPred_map_star`: `{f : A → B | ∀ a, f (star a) = star (f a)}` is closed in
  `A → B`.
* `NonUnitalStarAlgHom.ofMemClosureRangeCoe` and `NonUnitalStarAlgHom.ofTendsto`: bundle a function
  in the pointwise closure, or a pointwise limit along a nontrivial filter, of nonunital
  star-algebra homomorphisms as an `A →⋆ₙₐ[R] B`.
* `NonUnitalStarAlgHom.isClosed_range_coe`: `Set.range ((↑) : (A →⋆ₙₐ[R] B) → A → B)` is closed.
* `StarAlgHom.ofMemClosureRangeCoe`, `StarAlgHom.ofTendsto`, and `StarAlgHom.isClosed_range_coe`:
  the unital counterparts for `A →⋆ₐ[R] B` (requiring no continuity of scalar multiplication on `B`,
  since compatibility with `algebraMap` is checked at fixed ring elements).
-/

public section

open Filter Set Topology

section StarMap

/-- In the product topology on `A → B`, the maps intertwining `star` form a closed subset whenever
`B` is Hausdorff and has continuous `star`. -/
theorem TauCeti.isClosed_setOfPred_map_star (A B : Type*) [TopologicalSpace B] [T2Space B]
    [Star A] [Star B] [ContinuousStar B] :
    IsClosed {f : A → B | ∀ a, f (star a) = star (f a)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a ↦ isClosed_eq (continuous_apply (star a)) (by fun_prop)

end StarMap

namespace NonUnitalStarAlgHom

variable {α R A B F : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [TopologicalSpace B] [T2Space B] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
  [ContinuousAdd B] [ContinuousMul B] [ContinuousConstSMul R B] [ContinuousStar B]
  [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]
  {l : Filter α}

/-- Construct a bundled nonunital `⋆`-algebra homomorphism `A →⋆ₙₐ[R] B` from a function `f` in the
pointwise closure of the coercion range of any `NonUnitalAlgHomClass` + `StarHomClass` type `F`. -/
def ofMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (a : A) ↦ g a)) : A →⋆ₙₐ[R] B where
  toFun := f
  map_smul' := (isClosed_setOfPred_map_smul A B (MonoidHom.id R)).closure_subset_iff.2
    (range_subset_iff.2 fun g r a ↦ map_smul g r a) hf
  map_zero' := (addMonoidHomOfMemClosureRangeCoe f hf).map_zero'
  map_add' := (addMonoidHomOfMemClosureRangeCoe f hf).map_add'
  map_mul' := (mulHomOfMemClosureRangeCoe f hf).map_mul'
  map_star' := (TauCeti.isClosed_setOfPred_map_star A B).closure_subset_iff.2
    (range_subset_iff.2 map_star) hf

@[simp]
theorem coe_ofMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (a : A) ↦ g a)) :
    ⇑(ofMemClosureRangeCoe f hf) = f := (rfl)

theorem ofMemClosureRangeCoe_apply (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (a : A) ↦ g a)) (a : A) :
    ofMemClosureRangeCoe f hf a = f a := (rfl)

/-- Construct a bundled nonunital `⋆`-algebra homomorphism `A →⋆ₙₐ[R] B` from a pointwise limit
along a nontrivial filter. -/
def ofTendsto (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) : A →⋆ₙₐ[R] B :=
  ofMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ ↦ mem_range_self _

@[simp]
theorem coe_ofTendsto (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) :
    ⇑(ofTendsto f g h) = f := (rfl)

theorem ofTendsto_apply (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) (a : A) :
    ofTendsto f g h a = f a := (rfl)

/-- The coercion range of `A →⋆ₙₐ[R] B` in `A → B` is closed in the topology of pointwise
convergence. -/
theorem isClosed_range_coe (R A B : Type*) [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [TopologicalSpace B] [T2Space B] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    [ContinuousAdd B] [ContinuousMul B] [ContinuousConstSMul R B] [ContinuousStar B] :
    IsClosed (range ((↑) : (A →⋆ₙₐ[R] B) → A → B)) :=
  isClosed_of_closure_subset fun f hf ↦ ⟨ofMemClosureRangeCoe f hf, rfl⟩

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {α R A B F : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A]
  [TopologicalSpace B] [T2Space B] [Semiring B] [Algebra R B] [Star B]
  [ContinuousAdd B] [ContinuousMul B] [ContinuousStar B]
  [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B]
  {l : Filter α}

/-- Construct a bundled unital `⋆`-algebra homomorphism `A →⋆ₐ[R] B` from a function `f` in the
pointwise closure of the coercion range of any `AlgHomClass` + `StarHomClass` type `F`. -/
def ofMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (a : A) ↦ g a)) : A →⋆ₐ[R] B where
  toFun := f
  map_one' := (monoidHomOfMemClosureRangeCoe f hf).map_one'
  map_mul' := (monoidHomOfMemClosureRangeCoe f hf).map_mul'
  map_zero' := (addMonoidHomOfMemClosureRangeCoe f hf).map_zero'
  map_add' := (addMonoidHomOfMemClosureRangeCoe f hf).map_add'
  commutes' := by
    have hcl : IsClosed {h : A → B | ∀ r : R, h (algebraMap R A r) = algebraMap R B r} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun r ↦
        isClosed_eq (continuous_apply (algebraMap R A r)) continuous_const
    exact hcl.closure_subset_iff.2 (range_subset_iff.2 AlgHomClass.commutes) hf
  map_star' := (TauCeti.isClosed_setOfPred_map_star A B).closure_subset_iff.2
    (range_subset_iff.2 map_star) hf

@[simp]
theorem coe_ofMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (a : A) ↦ g a)) :
    ⇑(ofMemClosureRangeCoe f hf) = f := (rfl)

theorem ofMemClosureRangeCoe_apply (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (a : A) ↦ g a)) (a : A) :
    ofMemClosureRangeCoe f hf a = f a := (rfl)

/-- Construct a bundled unital `⋆`-algebra homomorphism `A →⋆ₐ[R] B` from a pointwise limit along a
nontrivial filter. -/
def ofTendsto (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) : A →⋆ₐ[R] B :=
  ofMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ ↦ mem_range_self _

@[simp]
theorem coe_ofTendsto (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) :
    ⇑(ofTendsto f g h) = f := (rfl)

theorem ofTendsto_apply (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i a ↦ g i a) l (𝓝 f)) (a : A) :
    ofTendsto f g h a = f a := (rfl)

/-- The coercion range of `A →⋆ₐ[R] B` in `A → B` is closed in the topology of pointwise
convergence. -/
theorem isClosed_range_coe (R A B : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A]
    [TopologicalSpace B] [T2Space B] [Semiring B] [Algebra R B] [Star B]
    [ContinuousAdd B] [ContinuousMul B] [ContinuousStar B] :
    IsClosed (range ((↑) : (A →⋆ₐ[R] B) → A → B)) :=
  isClosed_of_closure_subset fun f hf ↦ ⟨ofMemClosureRangeCoe f hf, rfl⟩

end StarAlgHom
