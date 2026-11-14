/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Intertwining maps between direct sums of representations

For families of representations `ρ i` and `σ i` of a monoid `G`, Mathlib forms the direct-sum
representations `Representation.directSum ρ` and `Representation.directSum σ`. This file makes
the direct sum functorial in intertwining maps, and reindexes a direct sum of representations
along an equivalence of index types. Neither construction involves the group algebra, so the
scalars only need to form a semiring.

## Main definitions

* `Representation.IntertwiningMap.directSumMap`: the direct sum of a family of intertwining maps,
  compatible with identities and composition.
* `Representation.directSumEquivCongrLeft`: reindexing a direct sum of representations along an
  equivalence of index types; its underlying linear equivalence is `DirectSum.lequivCongrLeft`.
-/

public section

open DirectSum

namespace Representation

variable {k G ι : Type*} [Semiring k] [Monoid G]
  {V W : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommMonoid (W i)] [∀ i, Module k (W i)]

section Naturality

variable {ρ : ∀ i, Representation k G (V i)} {σ : ∀ i, Representation k G (W i)}

/-- **The direct sum of a family of intertwining maps**, acting summand by summand. -/
noncomputable def IntertwiningMap.directSumMap (f : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    IntertwiningMap (directSum ρ) (directSum σ) where
  toLinearMap := DirectSum.lmap fun i ↦ (f i).toLinearMap
  isIntertwining' g := by
    ext x i
    simp [directSum_apply, (f i).isIntertwining]

@[simp]
theorem IntertwiningMap.directSumMap_toLinearMap (f : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    (directSumMap f).toLinearMap = DirectSum.lmap fun i ↦ (f i).toLinearMap :=
  (rfl)

@[simp]
theorem IntertwiningMap.directSumMap_apply (f : ∀ i, IntertwiningMap (ρ i) (σ i))
    (x : ⨁ i, V i) (i : ι) : directSumMap f x i = f i (x i) :=
  (rfl)

/-- The direct sum of intertwining maps sends `v` in summand `i` to `f i v` in summand `i`. -/
@[simp]
theorem IntertwiningMap.directSumMap_lof [DecidableEq ι] (f : ∀ i, IntertwiningMap (ρ i) (σ i))
    (i : ι) (v : V i) : directSumMap f (lof k ι V i v) = lof k ι W i (f i v) :=
  DirectSum.lmap_lof _ i v

/-- The direct sum of identity maps is the identity. -/
@[simp]
theorem IntertwiningMap.directSumMap_id :
    directSumMap (fun i ↦ IntertwiningMap.id (ρ i)) = IntertwiningMap.id (directSum ρ) := by
  ext x i
  simp

/-- The direct sum of composites is the composite of the direct sums. -/
@[simp]
theorem IntertwiningMap.directSumMap_comp {U : ι → Type*} [∀ i, AddCommMonoid (U i)]
    [∀ i, Module k (U i)] {τ : ∀ i, Representation k G (U i)}
    (f : ∀ i, IntertwiningMap (σ i) (τ i)) (g : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    directSumMap (fun i ↦ (f i).comp (g i)) = (directSumMap f).comp (directSumMap g) := by
  ext x i
  simp

end Naturality

section Reindex

variable (ρ : ∀ i, Representation k G (V i)) {κ : Type*} (h : ι ≃ κ)

/-- **Reindexing a direct sum of representations** along an equivalence `h : ι ≃ κ`: the
summand of index `j` of the reindexed family is the summand of index `h.symm j` of the original
one. The underlying linear equivalence is `DirectSum.lequivCongrLeft`. -/
noncomputable def directSumEquivCongrLeft :
    (directSum ρ).Equiv (directSum fun j ↦ ρ (h.symm j)) :=
  .mk (DirectSum.lequivCongrLeft k h) fun g ↦ by
    ext x j
    simp [directSum_apply, DirectSum.lequivCongrLeft_apply]

@[simp]
theorem directSumEquivCongrLeft_toLinearEquiv :
    (directSumEquivCongrLeft ρ h).toLinearEquiv = DirectSum.lequivCongrLeft k h :=
  (rfl)

@[simp]
theorem directSumEquivCongrLeft_apply (x : ⨁ i, V i) (j : κ) :
    directSumEquivCongrLeft ρ h x j = x (h.symm j) :=
  (rfl)

/-- The inverse reindexing reads the summand of index `h.symm j` off the summand of index `j`. -/
@[simp]
theorem directSumEquivCongrLeft_symm_apply (y : ⨁ j, V (h.symm j)) (j : κ) :
    (directSumEquivCongrLeft ρ h).symm y (h.symm j) = y j := by
  rw [← directSumEquivCongrLeft_apply ρ h, Representation.Equiv.apply_symm_apply]

/-- Reindexing sends `v` in summand `h.symm j` to `v` in summand `j`. -/
@[simp]
theorem directSumEquivCongrLeft_lof [DecidableEq ι] [DecidableEq κ] (j : κ) (v : V (h.symm j)) :
    directSumEquivCongrLeft ρ h (lof k ι V (h.symm j) v) =
      lof k κ (fun j ↦ V (h.symm j)) j v :=
  DirectSum.lequivCongrLeft_lof _ rfl _ _ rfl

/-- The inverse reindexing sends `v` in summand `j` to `v` in summand `h.symm j`. -/
@[simp]
theorem directSumEquivCongrLeft_symm_lof [DecidableEq ι] [DecidableEq κ] (j : κ)
    (v : V (h.symm j)) :
    (directSumEquivCongrLeft ρ h).symm (lof k κ (fun j ↦ V (h.symm j)) j v) =
      lof k ι V (h.symm j) v :=
  DirectSum.lequivCongrLeft_symm_lof k

end Reindex

end Representation
