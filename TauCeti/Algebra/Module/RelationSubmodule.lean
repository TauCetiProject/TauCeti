/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Locally constant functions obeying matrix linear relations and torsion identification

Given a topological space `G`, a finite index type `n`, a commutative ring `O`, a family of
matrix linear relations `L : Set (G →₀ Matrix n n O)`, and an `O`-module `B`, we define the
submodule `TauCeti.RelationSubmodule.locallyConstantObeying L B` of locally constant functions
`z : G → n → B` satisfying `∑ g, r g *ᵥ z g = 0` for every `r ∈ L`.

An injective `O`-linear map `f : B →ₗ[O] B'` preserves and reflects membership and induces an
injective `O`-linear map on these submodules. When `f : (O ⧸ Ideal.span {a}) →ₗ[O] B` surjects
onto the `a`-torsion of `B`, its range is precisely the `a`-torsion submodule of
`locallyConstantObeying L B`.

## Main definitions and results

* `TauCeti.RelationSubmodule.locallyConstantObeying`: locally constant functions obeying `L`.
* `TauCeti.RelationSubmodule.comp_mem_iff`: injective `f` preserves and reflects membership.
* `TauCeti.RelationSubmodule.mapOfInjective`: induced linear map for injective `f`.
* `TauCeti.RelationSubmodule.mapOfInjective_injective`: injectivity of `mapOfInjective`.
* `TauCeti.RelationSubmodule.range_mapOfInjective_eq_torsionBy`: identification of the `a`-torsion
  with the quotient-coefficient submodule.

## Provenance

Adapted from `New.Selmer.comp_mem_selmerModule_iff`, `New.Selmer.selmerModuleMapOfInjective`,
`New.Selmer.selmerModuleMapOfInjective_injective`, and
`New.Selmer.range_selmerModuleMapOfInjective` in
`src/Lib/GaloisRep/Main/DivisibleSelmerModules.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti.RelationSubmodule

open Submodule Matrix

section Basic

variable {O G n : Type*} [CommRing O] [TopologicalSpace G] [Fintype n]
  (L : Set (G →₀ Matrix n n O))
  {B B' : Type*} [AddCommGroup B] [Module O B] [AddCommGroup B'] [Module O B']

/-- The `O`-submodule of locally constant functions `z : G → n → B` obeying every matrix linear
relation `r ∈ L`, meaning `∑ g ∈ r.support, ∑ j, r g i j • z g j = 0` for all `i : n`. -/
def locallyConstantObeying (B : Type*) [AddCommGroup B] [Module O B] :
    Submodule O (G → n → B) where
  carrier := {z | (∀ r ∈ L, ∀ i : n, r.sum (fun g M ↦ ∑ j : n, M i j • z g j) = 0) ∧
    IsLocallyConstant z}
  zero_mem' := ⟨fun r _ i ↦ by simp, IsLocallyConstant.const _⟩
  add_mem' := fun {x y} hx hy ↦
    ⟨fun r hr i ↦ by
      have hx' := hx.left r hr i
      have hy' := hy.left r hr i
      simp only [Finsupp.sum, Pi.add_apply, smul_add, Finset.sum_add_distrib] at hx' hy' ⊢
      rw [hx', hy', add_zero],
     hx.right.add hy.right⟩
  smul_mem' := fun c {x} hx ↦
    ⟨fun r hr i ↦ by
      have hx' := hx.left r hr i
      simp only [Finsupp.sum] at hx' ⊢
      simp only [Pi.smul_apply, smul_comm _ c, ← Finset.smul_sum]
      rw [hx', smul_zero],
     hx.right.comp (fun v : n → B ↦ c • v)⟩

/-- An injective `O`-linear map `f : B →ₗ[O] B'` preserves and reflects membership in
`locallyConstantObeying L`. -/
theorem comp_mem_iff {f : B →ₗ[O] B'} (hf : Function.Injective f) {z : G → n → B} :
    (fun g i ↦ f (z g i)) ∈ locallyConstantObeying L B' ↔ z ∈ locallyConstantObeying L B := by
  have h_rel :
      (∀ r ∈ L, ∀ i : n, r.sum (fun g M ↦ ∑ j : n, M i j • f (z g j)) = 0) ↔
        ∀ r ∈ L, ∀ i : n, r.sum (fun g M ↦ ∑ j : n, M i j • z g j) = 0 := by
    refine forall₂_congr fun r _ ↦ forall_congr' fun i ↦ ?_
    have hmap : r.sum (fun g M ↦ ∑ j : n, M i j • f (z g j)) =
        f (r.sum (fun g M ↦ ∑ j : n, M i j • z g j)) := by
      simp [Finsupp.sum, map_sum, map_smul]
    rw [hmap, map_eq_zero_iff f hf]
  have h_lc : IsLocallyConstant (fun g i ↦ f (z g i)) ↔ IsLocallyConstant z :=
    ⟨fun h ↦ IsLocallyConstant.desc z (fun v : n → B ↦ f ∘ v) h hf.comp_left,
      fun h ↦ h.comp fun v : n → B ↦ f ∘ v⟩
  exact and_congr h_rel h_lc

/-- The `O`-linear map on `locallyConstantObeying L` induced by an injective
`f : B →ₗ[O] B'`. -/
def mapOfInjective {f : B →ₗ[O] B'} (hf : Function.Injective f) :
    locallyConstantObeying L B →ₗ[O] locallyConstantObeying L B' where
  toFun z := ⟨fun g i ↦ f (z.val g i), (comp_mem_iff L hf).mpr z.property⟩
  map_add' _ _ := by ext g i; simp
  map_smul' _ _ := by ext g i; simp

/-- An injective map of coefficient modules induces an injective map on
`locallyConstantObeying L`. -/
theorem mapOfInjective_injective {f : B →ₗ[O] B'} (hf : Function.Injective f) :
    Function.Injective (mapOfInjective L hf) :=
  fun _ _ h ↦ Subtype.ext (hf.comp_left.comp_left (congrArg Subtype.val h))

/-- If `f : (O ⧸ Ideal.span {a}) →ₗ[O] B` is injective and surjects onto the `a`-torsion of `B`,
then the range of `mapOfInjective L hf` is the `a`-torsion submodule of
`locallyConstantObeying L B`. -/
theorem range_mapOfInjective_eq_torsionBy {a : O} {f : (O ⧸ Ideal.span {a}) →ₗ[O] B}
    (hf : Function.Injective f)
    (h_onto : ∀ y : B, a • y = 0 → ∃ x : O ⧸ Ideal.span {a}, f x = y) :
    LinearMap.range (mapOfInjective L hf) = torsionBy O (locallyConstantObeying L B) a := by
  ext ⟨y, hy_mem⟩
  constructor
  · rintro ⟨z, hz⟩
    have hz_smul : a • z = 0 := by
      ext g i
      change a • z.val g i = 0
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z.val g i)
      rw [← hr]
      change Ideal.Quotient.mk (Ideal.span {a}) a * Ideal.Quotient.mk (Ideal.span {a}) r = 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right r _ (Ideal.subset_span (Set.mem_singleton a))
    rw [mem_torsionBy_iff, ← hz, ← map_smul, hz_smul, map_zero]
  · intro hy
    have hy_smul : a • y = 0 := by simpa [Subtype.ext_iff] using hy
    have h_lift (g : G) (i : n) : ∃ x : O ⧸ Ideal.span {a}, f x = y g i :=
      h_onto (y g i) (congrFun₂ hy_smul g i)
    choose z hz using h_lift
    have hz_mem : z ∈ locallyConstantObeying L (O ⧸ Ideal.span {a}) :=
      (comp_mem_iff L hf).mp (by simpa only [hz] using hy_mem)
    exact ⟨⟨z, hz_mem⟩, Subtype.ext (funext fun g ↦ funext fun i ↦ hz g i)⟩

end Basic

end TauCeti.RelationSubmodule
