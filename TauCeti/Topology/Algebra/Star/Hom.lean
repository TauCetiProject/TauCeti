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
# Pointwise limits of star algebra homomorphisms

In a Hausdorff topological algebra with continuous addition, multiplication, scalar action, and
involution, the predicates defining non-unital and unital `⋆`-algebra homomorphisms are closed in
the product topology on `A → B`. Consequently, any function in the closure of the range of any
corresponding homomorphism class — and in particular any pointwise limit along a nontrivial filter
— bundles as a `NonUnitalStarAlgHom` or `StarAlgHom`, and the ranges of the coercions to functions
are closed.

The design and naming follow `mulHomOfMemClosureRangeCoe` in `Mathlib.Topology.Algebra.Monoid` and
`linearMapOfMemClosureRangeCoe` in `Mathlib.Topology.Algebra.Module.Basic`.

## Main definitions and results

* `isClosed_setOfPred_map_star`: star-preserving maps `A → B` form a closed subset in the topology
  of pointwise convergence when `B` is `T₂` with continuous `star`.
* `nonUnitalStarAlgHomOfMemClosureRangeCoe`, `nonUnitalStarAlgHomOfTendsto`,
  `NonUnitalStarAlgHom.isClosed_range_coe`: closure and pointwise-limit constructors and closed
  range for `A →⋆ₙₐ[R] B`.
* `starAlgHomOfMemClosureRangeCoe`, `starAlgHomOfTendsto`, `StarAlgHom.isClosed_range_coe`:
  closure and pointwise-limit constructors and closed range for `A →⋆ₐ[R] B`.
-/

public section

open Filter Set Topology

section Star

variable (A B : Type*) [TopologicalSpace B] [T2Space B] [Star A] [Star B] [ContinuousStar B]

/-- The star-preserving functions `A → B` form a closed subset for pointwise convergence when `B`
is Hausdorff with continuous involution. -/
theorem isClosed_setOfPred_map_star :
    IsClosed {f : A → B | ∀ x, f (star x) = star (f x)} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_eq (continuous_apply _) (by fun_prop)

end Star

section NonUnitalStarAlgHom

variable {α R A B F : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
  [TopologicalSpace B] [T2Space B] [ContinuousAdd B] [ContinuousMul B]
  [ContinuousConstSMul R B] [ContinuousStar B]
  [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]
  {l : Filter α}

/-- Construct a bundled `NonUnitalStarAlgHom` from a function `f` in the pointwise closure of any
class of non-unital `⋆`-algebra homomorphisms. -/
def nonUnitalStarAlgHomOfMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (x : A) ↦ g x)) : A →⋆ₙₐ[R] B where
  toFun := f
  map_smul' := (isClosed_setOfPred_map_smul A B (MonoidHom.id R)).closure_subset_iff.2
    (range_subset_iff.2 map_smul) hf
  map_zero' := (isClosed_setOfPred_map_zero A B).closure_subset_iff.2
    (range_subset_iff.2 map_zero) hf
  map_add' := (isClosed_setOfPred_map_add A B).closure_subset_iff.2
    (range_subset_iff.2 map_add) hf
  map_mul' := (isClosed_setOfPred_map_mul A B).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf
  map_star' := (isClosed_setOfPred_map_star A B).closure_subset_iff.2
    (range_subset_iff.2 map_star) hf

@[simp]
theorem coe_nonUnitalStarAlgHomOfMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (x : A) ↦ g x)) :
    ⇑(nonUnitalStarAlgHomOfMemClosureRangeCoe f hf) = f :=
  (rfl)

@[simp]
theorem nonUnitalStarAlgHomOfMemClosureRangeCoe_apply (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (x : A) ↦ g x)) (a : A) :
    nonUnitalStarAlgHomOfMemClosureRangeCoe f hf a = f a :=
  (rfl)

/-- Construct a bundled `NonUnitalStarAlgHom` from a pointwise limit of non-unital `⋆`-algebra
homomorphisms along a nontrivial filter. -/
def nonUnitalStarAlgHomOfTendsto (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i x ↦ g i x) l (𝓝 f)) : A →⋆ₙₐ[R] B :=
  nonUnitalStarAlgHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ ↦ mem_range_self _

@[simp]
theorem coe_nonUnitalStarAlgHomOfTendsto (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i x ↦ g i x) l (𝓝 f)) :
    ⇑(nonUnitalStarAlgHomOfTendsto f g h) = f :=
  (rfl)

@[simp]
theorem nonUnitalStarAlgHomOfTendsto_apply (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i x ↦ g i x) l (𝓝 f)) (a : A) :
    nonUnitalStarAlgHomOfTendsto f g h a = f a :=
  (rfl)

variable (R A B) in
/-- The coercion `(A →⋆ₙₐ[R] B) → (A → B)` has closed range in the product topology. -/
theorem NonUnitalStarAlgHom.isClosed_range_coe :
    IsClosed (range ((↑) : (A →⋆ₙₐ[R] B) → A → B)) :=
  isClosed_of_closure_subset fun f hf ↦ ⟨nonUnitalStarAlgHomOfMemClosureRangeCoe f hf, rfl⟩

end NonUnitalStarAlgHom

section StarAlgHom

variable {α R A B F : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]
  [TopologicalSpace B] [T2Space B] [ContinuousAdd B] [ContinuousMul B] [ContinuousStar B]
  [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B]
  {l : Filter α}

/-- Construct a bundled `StarAlgHom` from a function `f` in the pointwise closure of any class of
unital `⋆`-algebra homomorphisms. -/
def starAlgHomOfMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (x : A) ↦ g x)) : A →⋆ₐ[R] B where
  toFun := f
  map_one' := (isClosed_setOfPred_map_one A B).closure_subset_iff.2
    (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOfPred_map_mul A B).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf
  map_zero' := (isClosed_setOfPred_map_zero A B).closure_subset_iff.2
    (range_subset_iff.2 map_zero) hf
  map_add' := (isClosed_setOfPred_map_add A B).closure_subset_iff.2
    (range_subset_iff.2 map_add) hf
  commutes' := by
    have hc : IsClosed {f : A → B | ∀ r : R, f (algebraMap R A r) = algebraMap R B r} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun r ↦ isClosed_eq (continuous_apply _) continuous_const
    exact hc.closure_subset_iff.2 (range_subset_iff.2 AlgHomClass.commutes) hf
  map_star' := (isClosed_setOfPred_map_star A B).closure_subset_iff.2
    (range_subset_iff.2 map_star) hf

/-- Coercion of `starAlgHomOfMemClosureRangeCoe f hf` to a function agrees with `f`. -/
@[simp]
theorem coe_starAlgHomOfMemClosureRangeCoe (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (x : A) ↦ g x)) :
    ⇑(starAlgHomOfMemClosureRangeCoe f hf) = f :=
  (rfl)

/-- Applying `starAlgHomOfMemClosureRangeCoe f hf` agrees with applying `f`. -/
@[simp]
theorem starAlgHomOfMemClosureRangeCoe_apply (f : A → B)
    (hf : f ∈ closure (range fun (g : F) (x : A) ↦ g x)) (a : A) :
    starAlgHomOfMemClosureRangeCoe f hf a = f a :=
  (rfl)

/-- Construct a bundled `StarAlgHom` from a pointwise limit of unital `⋆`-algebra homomorphisms
along a nontrivial filter. -/
def starAlgHomOfTendsto (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i x ↦ g i x) l (𝓝 f)) : A →⋆ₐ[R] B :=
  starAlgHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ ↦ mem_range_self _

/-- Coercion of `starAlgHomOfTendsto f g h` to a function agrees with `f`. -/
@[simp]
theorem coe_starAlgHomOfTendsto (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i x ↦ g i x) l (𝓝 f)) :
    ⇑(starAlgHomOfTendsto f g h) = f :=
  (rfl)

/-- Applying `starAlgHomOfTendsto f g h` agrees with applying `f`. -/
@[simp]
theorem starAlgHomOfTendsto_apply (f : A → B) (g : α → F) [l.NeBot]
    (h : Tendsto (fun i x ↦ g i x) l (𝓝 f)) (a : A) :
    starAlgHomOfTendsto f g h a = f a :=
  (rfl)

variable (R A B) in
/-- The coercion `(A →⋆ₐ[R] B) → (A → B)` has closed range in the product topology. -/
theorem StarAlgHom.isClosed_range_coe :
    IsClosed (range ((↑) : (A →⋆ₐ[R] B) → A → B)) :=
  isClosed_of_closure_subset fun f hf ↦ ⟨starAlgHomOfMemClosureRangeCoe f hf, rfl⟩

end StarAlgHom
