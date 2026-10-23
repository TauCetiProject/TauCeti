/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.Extend
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic

/-!
# Duality in degree two makes `H²` right exact

Let `0 → A → B → C → 0` be a short exact sequence of discrete `G`-modules with `B` killed by a
prime `p`, and let `N` be a discrete `G`-module. Tate's duality map in degree two,
`α₂ : H²(G, M) → Hom(H⁰(G, M'), H²(G, N))` with `M' = InternalHom G M N`
(`TauCeti.ContCohomology.dualityMap2`), is natural in `M`: `α₂ (f_* b) = α₂ b ∘ f^*`, where
`f^* : H⁰(G, C') → H⁰(G, B')` is precomposition with `f = proj`. If `α₂` is surjective on `B` and
injective on `C`, then `H²(G, B) → H²(G, C)` is surjective.

The argument is the one of Serre's exposé, §9.1: `f^*` is injective because `f` is surjective, and
`H⁰(G, B')` is killed by `p`, so every functional on `H⁰(G, C')` extends along `f^*` to a functional
on `H⁰(G, B')` (`AddMonoidHom.exists_comp_eq_of_injective`). Given `y ∈ H²(G, C)`, extend `α₂ y`
to `ψ`, lift `ψ` to `b ∈ H²(G, B)` by surjectivity, and compare `α₂ (f_* b) = ψ ∘ f^* = α₂ y`;
injectivity gives `f_* b = y`.

The statement is made both on the explicit cocycle model (`explicitCoeff2`) and on the canonical
coefficient map `TauCeti.ContinuousCohomology.coeffMap` in degree two, which is the form consumed
by Tate's criterion `TauCeti.IsProP.cohomologicalDimensionAt_le_of_forall_coeffMap_proj_surjective`:
perfect duality in degree two on the finite modules killed by `p` bounds the cohomological
dimension of a pro-`p` group by `2`.

## Main results

* `TauCeti.ContCohomology.DiscreteShortExact.explicitCoeff2_proj_surjective_of_dualityMap2`: if
  `α₂` is surjective on `B` and injective on `C`, then `H²(G, B) → H²(G, C)` is surjective, on the
  explicit model.
* `TauCeti.ContCohomology.DiscreteShortExact.coeffMap_proj_surjective_of_dualityMap2`: the same for
  the canonical coefficient map in degree two.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.1.
-/

public section

namespace TauCeti.ContCohomology

universe u uG uA uB uC uN

section Explicit

variable {G : Type uG} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type uB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
    [ContinuousSMul G B]
  {C : Type uC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
    [ContinuousSMul G C]
  (S : DiscreteShortExact G A B C)
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
    [ContinuousSMul G N]
  {p : ℕ} [Fact p.Prime]

/-- **Duality in degree two makes `H²` right exact**, on the explicit model. For a short exact
sequence `0 → A → B → C → 0` of discrete `G`-modules with `B` killed by a prime `p`, if Tate's
duality map `α₂ : H²(G, M) → Hom(H⁰(G, InternalHom G M N), H²(G, N))` is surjective for `M = B`
and injective for `M = C`, then `H²(G, B) → H²(G, C)` is surjective. -/
theorem DiscreteShortExact.explicitCoeff2_proj_surjective_of_dualityMap2 (hB : ∀ b : B, p • b = 0)
    (hsurj : Function.Surjective (dualityMap2 G B N))
    (hinj : Function.Injective (dualityMap2 G C N)) :
    Function.Surjective
      (explicitCoeff2 G B S.projDistribMulActionHom continuous_of_discreteTopology) := by
  intro y
  -- `f^* : H⁰(G, C') → H⁰(G, B')` is injective, because `f = proj` is surjective.
  have hf : Function.Surjective S.projDistribMulActionHom :=
    fun c ↦ (S.proj_surjective c).imp fun _ hb ↦ (S.projDistribMulActionHom_apply _).trans hb
  have hι : Function.Injective
      (explicitCoeff0 G (InternalHom G C N) (InternalHom.precomp G S.projDistribMulActionHom)) :=
    fun φ φ' h ↦ Subtype.ext (InternalHom.precomp_injective hf
      (by simpa only [coe_explicitCoeff0] using congrArg Subtype.val h))
  -- `H⁰(G, B')` is killed by `p`, because `B` is.
  have hB' : ∀ x : H0 G (InternalHom G B N), p • x = 0 := fun x ↦ Subtype.ext <| by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
    exact InternalHom.ext (AddMonoidHom.ext fun b ↦ by simp [← map_nsmul, hB])
  -- Extend `α₂ y` along `f^*` to `ψ`, and lift `ψ` to `b ∈ H²(G, B)`.
  obtain ⟨ψ, hψ⟩ := AddMonoidHom.exists_comp_eq_of_injective hB' hι (dualityMap2 G C N y)
  obtain ⟨b, hb⟩ := hsurj ψ
  refine ⟨b, hinj (AddMonoidHom.ext fun φ ↦ ?_)⟩
  -- `α₂ (f_* b) φ = ⟨φ, f_* b⟩ = ⟨f^* φ, b⟩ = α₂ b (f^* φ) = ψ (f^* φ) = α₂ y φ`.
  rw [dualityMap2_eq_explicitDualityPairing02, explicitDualityPairing02_explicitCoeff2,
    ← dualityMap2_eq_explicitDualityPairing02, hb, ← hψ, AddMonoidHom.comp_apply]

end Explicit

section Canonical

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
    [ContinuousSMul G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
    [ContinuousSMul G C]
  (S : DiscreteShortExact G A B C)
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
    [ContinuousSMul G N]
  {p : ℕ} [Fact p.Prime]

/-- **Duality in degree two makes `H²` right exact**, for the canonical coefficient map. For a
short exact sequence `0 → A → B → C → 0` of discrete `G`-modules with `B` killed by a prime `p`, if
Tate's duality map `α₂` is surjective for `M = B` and injective for `M = C`, then the canonical
`H²(G, B) → H²(G, C)` is surjective. This is the hypothesis of Tate's criterion
`TauCeti.IsProP.cohomologicalDimensionAt_le_of_forall_coeffMap_proj_surjective` in degree `2`. -/
theorem DiscreteShortExact.coeffMap_proj_surjective_of_dualityMap2 (hB : ∀ b : B, p • b = 0)
    (hsurj : Function.Surjective (dualityMap2 G B N))
    (hinj : Function.Injective (dualityMap2 G C N)) :
    Function.Surjective (TauCeti.ContinuousCohomology.coeffMap
      (ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) 2) := by
  intro y
  obtain ⟨b, hb⟩ := S.explicitCoeff2_proj_surjective_of_dualityMap2 N hB hsurj hinj
    ((explicitH2AddEquivContinuousCohomology G C).symm y)
  refine ⟨explicitH2AddEquivContinuousCohomology G B b, ?_⟩
  rw [← S.ofDiscreteModuleMap_projDistribMulActionHom,
    explicitH2AddEquivContinuousCohomology_coeffMap, hb, AddEquiv.apply_symm_apply]

end Canonical

end TauCeti.ContCohomology
