/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsAlgebraHom
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Intertwining.DirectSum

/-!
# The group-algebra module of a direct sum of representations

For a family of representations `ρ i` of a monoid `G` on `k`-modules `V i`, Mathlib forms the
direct-sum representation `Representation.directSum ρ` on `⨁ i, V i`. This file identifies its
group-algebra module with the direct sum `Π₀ i, (ρ i).asModule` of the group-algebra modules of
the summands, by a `k[G]`-linear equivalence `Representation.directSumAsModuleEquiv` that sends a
vector supported in summand `i` to the same vector in the `i`-th component.

This is the dictionary between group representations and group-algebra modules
(Fulton–Harris, *Representation Theory*, §3.4) applied to direct sums. Suppose `ρ.asModule` is
decomposed into a direct sum of `k[G]`-modules, as produced by the theory of semisimple modules,
and each summand is identified with `(σ i).asModule` for a representation `σ i` (for instance via
`Subrepresentation.asModuleEquivAsSubmodule`). Composing with
`(Representation.directSumAsModuleEquiv σ).symm` gives a `k[G]`-linear equivalence
`ρ.asModule ≃ₗ[k[G]] (directSum σ).asModule`, which
`TauCeti.Representation.equivOfAsModuleLinearEquiv` turns into an equivalence of representations
`ρ.Equiv (directSum σ)`.

The direct sum of intertwining maps and the reindexing of a direct sum, which do not involve the
group algebra, are in `TauCeti.RepresentationTheory.Intertwining.DirectSum`.

## Main definitions

* `Representation.directSumAsModuleEquiv`: the `k[G]`-linear equivalence
  `(directSum ρ).asModule ≃ₗ[k[G]] Π₀ i, (ρ i).asModule`.

## Main results

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
      (ρ i).asModuleEquiv (y i) := by
  refine ((ρ i).asModuleEquiv.symm_apply_eq).mp ?_
  rw [← directSumAsModuleEquiv_apply, LinearEquiv.apply_symm_apply]

/-- **The inverse comparison sends the `i`-th component `v` to `v` in summand `i`.** -/
@[simp]
theorem directSumAsModuleEquiv_symm_single [DecidableEq ι] (i : ι) (v : (ρ i).asModule) :
    (directSumAsModuleEquiv ρ).symm (DFinsupp.single i v) =
      (directSum ρ).asModuleEquiv.symm (DirectSum.lof k ι V i ((ρ i).asModuleEquiv v)) := by
  apply (directSum ρ).asModuleEquiv.injective
  rw [directSumAsModuleEquiv, LinearEquiv.coe_symm_mk', LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, DFinsupp.mapRange.linearEquiv_symm,
    DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_single, DirectSum.single_eq_lof k,
    LinearEquiv.symm_symm]

/-- **The comparison sends `v` in summand `i` to the `i`-th component `v`.** -/
theorem directSumAsModuleEquiv_lof [DecidableEq ι] (i : ι) (v : V i) :
    directSumAsModuleEquiv ρ ((directSum ρ).asModuleEquiv.symm (DirectSum.lof k ι V i v)) =
      (DFinsupp.single i ((ρ i).asModuleEquiv.symm v) : Π₀ i, (ρ i).asModule) := by
  refine ((directSumAsModuleEquiv ρ).eq_symm_apply).mp ?_
  rw [directSumAsModuleEquiv_symm_single, LinearEquiv.apply_symm_apply]

section Naturality

variable {ρ σ}

/-- **The comparison is natural for a family of intertwining maps.** Under the comparisons, the
`k[G]`-linear map attached to the direct sum of the `f i` is the direct sum of the `k[G]`-linear
maps attached to the `f i`. -/
theorem directSumAsModuleEquiv_comp_directSumMap (f : ∀ i, IntertwiningMap (ρ i) (σ i)) :
    (directSumAsModuleEquiv σ).toLinearMap ∘ₗ
        IntertwiningMap.equivLinearMapAsModule _ _ (IntertwiningMap.directSumMap f) =
      DFinsupp.mapRange.linearMap (fun i ↦ IntertwiningMap.equivLinearMapAsModule _ _ (f i)) ∘ₗ
        (directSumAsModuleEquiv ρ).toLinearMap := by
  ext x i
  obtain ⟨v, rfl⟩ := (directSum ρ).asModuleEquiv.symm.surjective x
  apply (σ i).asModuleEquiv.injective
  -- Write each attached `k[G]`-linear map as the image of its intertwining map, so that
  -- `IntertwiningMap.equivLinearMapAsModule_symm_apply` evaluates both sides.
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    directSumAsModuleEquiv_apply, LinearEquiv.apply_symm_apply,
    DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, directSumAsModuleEquiv_apply,
    LinearEquiv.apply_symm_apply, ← IntertwiningMap.equivLinearMapAsModule_symm_apply,
    ← IntertwiningMap.equivLinearMapAsModule_symm_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, IntertwiningMap.directSumMap_apply]

end Naturality

section Reindex

variable {κ : Type*} (h : ι ≃ κ)

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
