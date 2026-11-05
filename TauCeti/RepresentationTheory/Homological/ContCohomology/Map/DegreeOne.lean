/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

/-!
# Canonical first continuous cohomology along compatible pairs in independent universes

Mathlib's `ContinuousCohomology.map` pulls continuous cohomology back along a compatible pair
`(φ : H →ₜ* G, f : res φ X ⟶ Y)`, but it is a morphism in a single category of topological
modules, so it binds both groups to one universe and both coefficient objects to one universe.
For discrete coefficient modules this file constructs the same pullback on Mathlib's
`continuousCohomology 1` with the universes of `G` and `M` independent of those of `H` and `N`.
This is what a field isomorphism `K ≃+* L` between fields in different universes, such as
`K ≃+* ULift K`, induces on the canonical first Galois cohomology groups, where the Kummer
classes live.

The construction passes through the explicit inhomogeneous model, in which cochains are plain
functions and pullback needs no common universe: the explicit pullback
`TauCeti.ContCohomology.explicitMap1` is read through the degree-one comparison
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` at both ends. Unlike degree two, no
local compactness is needed, because the degree-one comparison holds over every topological group.
When all four types share one universe it is Mathlib's map
(`TauCeti.ContCohomology.continuousCohomologyMap1_eq_map`).

## Main definitions

* `TauCeti.ContCohomology.continuousCohomologyMap1`: the induced map on `continuousCohomology 1`.
* `TauCeti.ContCohomology.continuousCohomologyMap1Equiv`: the additive equivalence induced by a
  compatible pair of equivalences.

## Main results

* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1`: the
  comparison with the explicit model carries `explicitMap1` to `continuousCohomologyMap1`.
* `TauCeti.ContCohomology.continuousCohomologyMap1_eq_map`: in a single universe this is
  Mathlib's `ContinuousCohomology.map`.
* `TauCeti.ContCohomology.continuousCohomologyMap1_id` and
  `TauCeti.ContCohomology.continuousCohomologyMap1_comp`: functoriality, with the three groups in
  independent universes.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2 and
  §5: compatible pairs and the induced maps on inhomogeneous cochains.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u v w

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (H N : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction H N] [ContinuousSMul H N]

/-- Pullback along a compatible pair on Mathlib's `continuousCohomology 1`, with the universes
of `G` and `M` independent of those of `H` and `N`. On the explicit model it is
`TauCeti.ContCohomology.explicitMap1`
(`explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1`), and in a single universe it
is Mathlib's `ContinuousCohomology.map` (`continuousCohomologyMap1_eq_map`). -/
def continuousCohomologyMap1 (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    continuousCohomology 1 (ofDiscreteModule ℤ G M) →+
      continuousCohomology 1 (ofDiscreteModule ℤ H N) :=
  (explicitH1AddEquivContinuousCohomology H N).toAddMonoidHom.comp
    ((explicitMap1 G M H N φ f continuous_of_discreteTopology hf).comp
      (explicitH1AddEquivContinuousCohomology G M).symm.toAddMonoidHom)

/-- The comparison with the explicit model carries the explicit pullback `explicitMap1` to
`continuousCohomologyMap1`. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1 (φ : H →ₜ* G)
    (f : M →+ N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : H1 G M) :
    continuousCohomologyMap1 G M H N φ f hf (explicitH1AddEquivContinuousCohomology G M x) =
      explicitH1AddEquivContinuousCohomology H N
        (explicitMap1 G M H N φ f continuous_of_discreteTopology hf x) := by
  simp [continuousCohomologyMap1]

/-- **The map on classes is induced by the map on cocycles.** The canonical class of an explicit
one-cocycle goes to the canonical class of its pullback. -/
@[simp]
theorem continuousCohomologyMap1_homologyπ (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z1 G M) :
    continuousCohomologyMap1 G M H N φ f hf
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1
          (cocycleEquiv1 G M c)) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ H N)).homologyπ 1
        (cocycleEquiv1 H N (cocyclesMap1 G M H N φ f continuous_of_discreteTopology hf c)) := by
  rw [← explicitH1AddEquivContinuousCohomology_apply,
    explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1, explicitMap1_mk,
    explicitH1AddEquivContinuousCohomology_apply]

section SameUniverse

variable (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction H N] [ContinuousSMul H N]

/-- In a single universe, `continuousCohomologyMap1` is Mathlib's `ContinuousCohomology.map`
along the same compatible pair. -/
theorem continuousCohomologyMap1_eq_map (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (x : continuousCohomology 1 (ofDiscreteModule ℤ G M)) :
    continuousCohomologyMap1 G M H N φ f hf x =
      _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 1 x := by
  obtain ⟨y, rfl⟩ := (explicitH1AddEquivContinuousCohomology G M).surjective x
  rw [explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1,
    explicitH1AddEquivContinuousCohomology_map]

end SameUniverse

/-- Pullback along the identity compatible pair is the identity. -/
@[simp]
theorem continuousCohomologyMap1_id (hid : ∀ (g : G) (m : M),
    (AddMonoidHom.id M) ((ContinuousMonoidHom.id G) g • m) = g • (AddMonoidHom.id M) m :=
      fun _ _ ↦ rfl) :
    continuousCohomologyMap1 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) hid =
      AddMonoidHom.id _ := by
  ext x
  obtain ⟨y, rfl⟩ := (explicitH1AddEquivContinuousCohomology G M).surjective x
  rw [explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1, explicitMap1_id G M hid,
    AddMonoidHom.id_apply, AddMonoidHom.id_apply]

/-- Pullback respects composition of compatible pairs, with the three groups and their
coefficient modules in independent universes. -/
theorem continuousCohomologyMap1_comp (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K P : Type w) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction K P] [ContinuousSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n) :
    continuousCohomologyMap1 G M K P (φ.comp ψ) (q.comp f) (φ.comp_map_smul ψ f q hf hq) =
      (continuousCohomologyMap1 H N K P ψ q hq).comp
        (continuousCohomologyMap1 G M H N φ f hf) := by
  ext x
  obtain ⟨y, rfl⟩ := (explicitH1AddEquivContinuousCohomology G M).surjective x
  rw [AddMonoidHom.comp_apply, explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1,
    explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1,
    explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1,
    explicitMap1_comp G M H N φ f continuous_of_discreteTopology hf K P ψ q
      continuous_of_discreteTopology hq, AddMonoidHom.comp_apply]

/-- The additive equivalence of canonical first continuous cohomology groups induced by a
compatible pair of a continuous multiplicative equivalence `φ : H ≃ₜ* G` and an additive
equivalence `e : M ≃+ N`, with the universes of `G` and `M` independent of those of `H` and
`N`. Its forward and inverse maps are `continuousCohomologyMap1` along the pair and along its
inverse. -/
def continuousCohomologyMap1Equiv (φ : H ≃ₜ* G) (e : M ≃+ N)
    (he : ∀ (h : H) (m : M), e (φ h • m) = h • e m) :
    continuousCohomology 1 (ofDiscreteModule ℤ G M) ≃+
      continuousCohomology 1 (ofDiscreteModule ℤ H N) :=
  (explicitH1AddEquivContinuousCohomology G M).symm.trans
    ((explicitMap1Equiv G M H N φ e continuous_of_discreteTopology continuous_of_discreteTopology
      he).trans (explicitH1AddEquivContinuousCohomology H N))

/-- The equivalence is pullback along its forward compatible pair. -/
@[simp]
theorem continuousCohomologyMap1Equiv_apply (φ : H ≃ₜ* G) (e : M ≃+ N)
    (he : ∀ (h : H) (m : M), e (φ h • m) = h • e m)
    (x : continuousCohomology 1 (ofDiscreteModule ℤ G M)) :
    continuousCohomologyMap1Equiv G M H N φ e he x =
      continuousCohomologyMap1 G M H N φ e.toAddMonoidHom he x := by
  simp [continuousCohomologyMap1Equiv, continuousCohomologyMap1]

/-- The inverse equivalence is pullback along the inverse compatible pair. -/
@[simp]
theorem continuousCohomologyMap1Equiv_symm_apply (φ : H ≃ₜ* G) (e : M ≃+ N)
    (he : ∀ (h : H) (m : M), e (φ h • m) = h • e m)
    (x : continuousCohomology 1 (ofDiscreteModule ℤ H N)) :
    (continuousCohomologyMap1Equiv G M H N φ e he).symm x =
      continuousCohomologyMap1 H N G M φ.symm e.symm.toAddMonoidHom
        (AddEquiv.symm_map_smul_of_map_mulEquiv_smul e φ.toMulEquiv he) x := by
  simp [continuousCohomologyMap1Equiv, continuousCohomologyMap1]

end TauCeti.ContCohomology
