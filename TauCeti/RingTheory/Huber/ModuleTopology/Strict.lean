/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Basic
public import Mathlib.Topology.Maps.Strict.Module

import TauCeti.RingTheory.Ideal.ArtinRees

/-!
# Strict linear maps of finite modules over a Huber ring with a noetherian ring of definition

Let `A` be a Huber ring with a pair of definition `(A₀, I)` such that `A₀` is noetherian. Every
`A`-linear map `u : M → N` between finitely generated `A`-modules with their natural topologies is
strict: it is continuous, and open onto its image with the subspace topology
(Huber, *A generalization of formal schemes and rigid analytic varieties*, Lemma 2.3(i)).
Neither completeness nor the Tate property is assumed; the complete Tate case, with a noetherian
target module in place of a noetherian ring of definition, is
`LinearMap.isStrictMap_of_module_finite`.

Strictness is what lets a complex of finite modules be completed term by term without losing
exactness (`AddMonoidHom.exact_completion`), which is how algebraic Čech complexes become
complexes of completed modules in Huber's sheafiness theorem.

## Main results

* `TauCeti.Huber.PairOfDefinition.isStrictMap_of_isNoetherianRing`: every linear map between
  finite modules with their natural topologies is strict.

## Implementation notes

The proof reduces to the `I`-adic topology over `A₀`. Choose finitely generated `A₀`-lattices
`M₀ ⊆ M` and `N₀ ⊆ N` spanning over `A`; their `I`-adic filtrations are neighbourhood bases
(`TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero_idealOfDefinition_pow_smul`). The image
`K = u(M₀)` spans `u(M)`, so a power `Iʲ` carries the finitely generated `A₀`-module
`L = N₀ ∩ u(M)` into `K` (`TauCeti.Huber.PairOfDefinition.exists_pow_smul_le`), and the
Artin–Rees lemma in the noetherian `A₀`-module `N₀` bounds `Iᵐ N₀ ∩ L` by
`Iⁿ⁺ʲ L ⊆ Iⁿ K = u(Iⁿ M₀)`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Lemma 2.3(i) and its proof.
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I*, Chapitre 0, (7.3.2).
-/

public section

open Filter Topology

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A finite `A`-module has a finitely generated `A₀`-lattice spanning it over `A`. -/
private theorem exists_fg_span_eq_top (P : PairOfDefinition A) (M : Type*) [AddCommGroup M]
    [Module A M] [Module.Finite A M] :
    ∃ M₀ : Submodule P.ringOfDefinition M, M₀.FG ∧ Submodule.span A (M₀ : Set M) = ⊤ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  exact ⟨Submodule.span P.ringOfDefinition s, ⟨s, rfl⟩, by rw [Submodule.span_span_of_tower, hs]⟩

variable [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
  [TopologicalSpace M] [IsModuleTopology A M]
  {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
  [TopologicalSpace N] [IsModuleTopology A N]

/-- **Linear maps of finite modules over a Huber ring with a noetherian ring of definition are
strict** (Huber, Lemma 2.3(i)). If `A₀` is noetherian, every `A`-linear map between finitely
generated `A`-modules with their natural topologies is continuous and open onto its image. -/
theorem isStrictMap_of_isNoetherianRing (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] (u : M →ₗ[A] N) : IsStrictMap u := by
  have := IsModuleTopology.isTopologicalAddGroup A M
  have := IsModuleTopology.isTopologicalAddGroup A N
  obtain ⟨M₀, hM₀, hM₀span⟩ := P.exists_fg_span_eq_top M
  obtain ⟨N₀, hN₀, hN₀span⟩ := P.exists_fg_span_eq_top N
  let u₀ := u.restrictScalars P.ringOfDefinition
  -- `L = N₀ ∩ u(M)` is finitely generated over `A₀` and a power of `I` carries it into `u(M₀)`.
  let L := N₀ ⊓ (LinearMap.range u).restrictScalars P.ringOfDefinition
  have hL : L ≤ N₀ := inf_le_left
  have hLK : (L : Set N) ⊆ Submodule.span A (M₀.map u₀ : Set N) := by
    rintro x ⟨-, hx⟩
    rwa [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hM₀span,
      Submodule.map_top]
  obtain ⟨j, hj⟩ := P.exists_pow_smul_le (M₀.map u₀) (hN₀.of_le hL) hLK
  rw [LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict]
  refine ⟨u.surjective_rangeRestrict, IsModuleTopology.continuous_of_linearMap _, ?_⟩
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  refine ((P.hasBasis_nhds_zero_idealOfDefinition_pow_smul hM₀ hM₀span).map _).ge_iff.mpr
    fun n _ ↦ ?_
  -- Artin–Rees in `N₀` gives a level `m` of the filtration of `N` meeting `u(M)` inside
  -- `Iⁿ⁺ʲ L ⊆ Iⁿ u(M₀) = u(Iⁿ M₀)`.
  obtain ⟨m, hm⟩ := TauCeti.ArtinRees.exists_pow_smul_inf_le_pow_smul P.idealOfDefinition hN₀ hL
    (n + j)
  have hnhds : {y : LinearMap.range u | (y : N) ∈ P.idealOfDefinition ^ m • N₀} ∈ 𝓝 0 :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((P.hasBasis_nhds_zero_idealOfDefinition_pow_smul hN₀ hN₀span).mem_of_mem trivial)
  refine mem_of_superset hnhds fun y hy ↦ ?_
  have hyL : (y : N) ∈ P.idealOfDefinition ^ m • N₀ ⊓ L :=
    ⟨hy, Submodule.smul_le_right hy, y.2⟩
  have hyK : (y : N) ∈ (P.idealOfDefinition ^ n • M₀).map u₀ := by
    rw [Submodule.map_smul'']
    refine Submodule.smul_mono le_rfl hj ?_
    rw [← mul_smul, ← pow_add]
    exact hm hyL
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hyK
  exact ⟨x, hx, Subtype.ext hxy⟩

end TauCeti.Huber.PairOfDefinition
