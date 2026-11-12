/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.RepresentationTheory.AsModule

/-!
# The group-algebra module of a direct sum of representations

For a family of representations `ρ i` of a monoid `G` on `k`-modules `V i`, Mathlib forms the
direct-sum representation `Representation.directSum ρ` on `⨁ i, V i`. This file identifies its
group-algebra module with the direct sum `Π₀ i, (ρ i).asModule` of the group-algebra modules of
the summands, by a `k[G]`-linear equivalence `Representation.directSumAsModuleEquiv` that sends a
vector supported in summand `i` to the same vector in the `i`-th component.

This is the dictionary between group representations and group-algebra modules
(Fulton–Harris, *Representation Theory*, §3.4) applied to direct sums: a decomposition of
`ρ.asModule` into a direct sum of `k[G]`-modules, as produced by the theory of semisimple modules,
becomes a decomposition of the representation into a direct sum of representations once each
summand is read back through `TauCeti.Representation.equivOfAsModuleLinearEquiv`.

## Main definitions

* `Representation.IntertwiningMap.directSumMap`: the direct sum of a family of intertwining maps,
  compatible with identities and composition.
* `Representation.directSumEquivCongrLeft`: reindexing a direct sum of representations along an
  equivalence of index types.
* `Representation.directSumAsModuleEquiv`: the `k[G]`-linear equivalence
  `(directSum ρ).asModule ≃ₗ[k[G]] Π₀ i, (ρ i).asModule`.

## Main results

* `Representation.asAlgebraHom_directSum`: an element of `k[G]` acts on a direct sum summand by
  summand.
* `Representation.directSumAsModuleEquiv_symm_single`: the inverse sends the `i`-th component
  `v` to the vector `v` placed in summand `i`.
* `Representation.directSumAsModuleEquiv_comp_directSumMap`: the comparison is natural for a
  family of intertwining maps.
* `Representation.directSumAsModuleEquiv_directSumEquivCongrLeft`: the comparison commutes with
  reindexing the family.
-/

public section

open DirectSum
open scoped MonoidAlgebra

namespace Representation

variable {k G ι : Type*} [CommSemiring k] [Monoid G]
  {V W : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommMonoid (W i)] [∀ i, Module k (W i)]
  (ρ : ∀ i, Representation k G (V i)) (σ : ∀ i, Representation k G (W i))

/-- **The group algebra acts on a direct sum summand by summand.** The linear extension of the
direct-sum representation to `k[G]` is the direct sum of the linear extensions of the
summands. -/
theorem asAlgebraHom_directSum (r : k[G]) :
    asAlgebraHom (directSum ρ) r = DirectSum.lmap fun i ↦ asAlgebraHom (ρ i) r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => ext; simp
  | add r s hr hs => ext; simp [hr, hs]
  | single g t => ext; simp [asAlgebraHom_single, directSum_apply, DirectSum.smul_apply]

/-- **The group-algebra module of a direct sum is the direct sum of the group-algebra modules.**
The underlying map sends a vector of `⨁ i, V i` to the family of its components, each read as a
vector of `(ρ i).asModule`; `k[G]`-linearity is `Representation.asAlgebraHom_directSum`. -/
noncomputable def directSumAsModuleEquiv :
    (directSum ρ).asModule ≃ₗ[k[G]] Π₀ i, (ρ i).asModule where
  toFun x := DFinsupp.mapRange.linearEquiv (fun i ↦ (ρ i).asModuleEquiv.symm)
    ((directSum ρ).asModuleEquiv x)
  invFun y := (directSum ρ).asModuleEquiv.symm
    ((DFinsupp.mapRange.linearEquiv fun i ↦ (ρ i).asModuleEquiv.symm).symm y)
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    ext i
    apply (ρ i).asModuleEquiv.injective
    simp only [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply,
      LinearEquiv.apply_symm_apply, RingHom.id_apply, DFinsupp.smul_apply, asModuleEquiv_map_smul,
      asAlgebraHom_directSum, DirectSum.lmap_apply]
  left_inv x := by simp only [LinearEquiv.symm_apply_apply]
  right_inv y := by simp only [LinearEquiv.apply_symm_apply]

/-- The comparison reads off the `i`-th component of a vector of the direct sum. -/
@[simp]
theorem directSumAsModuleEquiv_apply (x : (directSum ρ).asModule) (i : ι) :
    directSumAsModuleEquiv ρ x i = (ρ i).asModuleEquiv.symm ((directSum ρ).asModuleEquiv x i) :=
  (rfl)

/-- The inverse comparison assembles a family of components into a vector of the direct sum. -/
theorem directSumAsModuleEquiv_symm_apply (y : Π₀ i, (ρ i).asModule) (i : ι) :
    (directSum ρ).asModuleEquiv ((directSumAsModuleEquiv ρ).symm y) i =
      (ρ i).asModuleEquiv (y i) :=
  (rfl)

/-- **The inverse comparison sends the `i`-th component `v` to `v` in summand `i`.** -/
@[simp]
theorem directSumAsModuleEquiv_symm_single [DecidableEq ι] (i : ι) (v : (ρ i).asModule) :
    (directSumAsModuleEquiv ρ).symm (DFinsupp.single i v) =
      (directSum ρ).asModuleEquiv.symm (DirectSum.lof k ι V i ((ρ i).asModuleEquiv v)) := by
  apply (directSum ρ).asModuleEquiv.injective
  ext j
  rw [directSumAsModuleEquiv_symm_apply, LinearEquiv.apply_symm_apply]
  obtain rfl | hij := eq_or_ne i j
  · rw [DFinsupp.single_eq_same, DirectSum.lof_apply]
  · rw [DFinsupp.single_eq_of_ne hij.symm, map_zero, DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne _ _ _ hij.symm]

/-- **The comparison sends `v` in summand `i` to the `i`-th component `v`.** -/
theorem directSumAsModuleEquiv_lof [DecidableEq ι] (i : ι) (v : V i) :
    directSumAsModuleEquiv ρ ((directSum ρ).asModuleEquiv.symm (DirectSum.lof k ι V i v)) =
      (DFinsupp.single i ((ρ i).asModuleEquiv.symm v) : Π₀ i, (ρ i).asModule) := by
  refine ((directSumAsModuleEquiv ρ).eq_symm_apply).mp ?_
  rw [directSumAsModuleEquiv_symm_single, LinearEquiv.apply_symm_apply]

section Naturality

variable {ρ σ}

/-- **The direct sum of a family of intertwining maps**, acting summand by summand. -/
noncomputable def IntertwiningMap.directSumMap (f : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    IntertwiningMap (directSum ρ) (directSum σ) where
  toLinearMap := DirectSum.lmap fun i ↦ (f i).toLinearMap
  isIntertwining' g := by
    ext x i
    simp [directSum_apply, (f i).isIntertwining]

@[simp]
theorem IntertwiningMap.directSumMap_apply (f : ∀ i, IntertwiningMap (ρ i) (σ i))
    (x : ⨁ i, V i) (i : ι) : directSumMap f x i = f i (x i) :=
  (rfl)

/-- The direct sum of identity maps is the identity. -/
@[simp]
theorem IntertwiningMap.directSumMap_id :
    directSumMap (fun i ↦ IntertwiningMap.id (ρ i)) = IntertwiningMap.id (directSum ρ) := by
  ext x i
  simp

/-- The direct sum of composites is the composite of the direct sums. -/
theorem IntertwiningMap.directSumMap_comp {U : ι → Type*} [∀ i, AddCommMonoid (U i)]
    [∀ i, Module k (U i)] {τ : ∀ i, Representation k G (U i)}
    (f : ∀ i, IntertwiningMap (σ i) (τ i)) (g : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    directSumMap (fun i ↦ (f i).comp (g i)) = (directSumMap f).comp (directSumMap g) := by
  ext x i
  simp

/-- **The comparison is natural for a family of intertwining maps.** Under the comparisons, the
`k[G]`-linear map attached to the direct sum of the `f i` is the direct sum of the `k[G]`-linear
maps attached to the `f i`. -/
theorem directSumAsModuleEquiv_comp_directSumMap (f : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    (directSumAsModuleEquiv σ).toLinearMap ∘ₗ
        IntertwiningMap.equivLinearMapAsModule _ _ (IntertwiningMap.directSumMap f) =
      DFinsupp.mapRange.linearMap (fun i ↦ IntertwiningMap.equivLinearMapAsModule _ _ (f i)) ∘ₗ
        (directSumAsModuleEquiv ρ).toLinearMap :=
  -- Both sides apply `f i` to the `i`-th component, through the identity maps
  -- `Representation.asModuleEquiv`.
  LinearMap.ext fun _ ↦ DFinsupp.ext fun _ ↦ (rfl)

end Naturality

section Reindex

variable {κ : Type*} (h : ι ≃ κ)

/-- **Reindexing a direct sum of representations** along an equivalence `h : ι ≃ κ`: the
summand of index `j` of the reindexed family is the summand of index `h.symm j` of the original
one. The underlying linear equivalence is `DirectSum.lequivCongrLeft`. -/
noncomputable def directSumEquivCongrLeft :
    (directSum ρ).Equiv (directSum fun j ↦ ρ (h.symm j)) :=
  .mk (DirectSum.lequivCongrLeft k h) fun g ↦ by
    ext x j
    simp [directSum_apply, DirectSum.lequivCongrLeft_apply]

@[simp]
theorem directSumEquivCongrLeft_apply (x : ⨁ i, V i) (j : κ) :
    directSumEquivCongrLeft ρ h x j = x (h.symm j) :=
  (rfl)

/-- **The comparison commutes with reindexing the family.** Reindexing the direct-sum
representation corresponds to reindexing the direct sum of the group-algebra modules by
`DFinsupp.domLCongr`. -/
theorem directSumAsModuleEquiv_directSumEquivCongrLeft (x : (directSum ρ).asModule) :
    directSumAsModuleEquiv (fun j ↦ ρ (h.symm j))
        (TauCeti.Representation.asModuleLinearEquivOfEquiv (directSumEquivCongrLeft ρ h) x) =
      DFinsupp.domLCongr (R := k[G]) h (directSumAsModuleEquiv ρ x) := by
  ext j
  rw [directSumAsModuleEquiv_apply, TauCeti.Representation.asModuleLinearEquivOfEquiv_apply,
    LinearEquiv.apply_symm_apply, directSumEquivCongrLeft_apply, DFinsupp.domLCongr_apply,
    DFinsupp.comapDomain'_apply, directSumAsModuleEquiv_apply]

end Reindex

end Representation
