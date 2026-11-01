/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison

/-!
# Canonical second continuous cohomology along compatible pairs in independent universes

Mathlib's `ContinuousCohomology.map` pulls continuous cohomology back along a compatible pair
`(φ : H →ₜ* G, f : res φ X ⟶ Y)`, but it is a morphism in a single category of topological
modules, so it binds both groups to one universe and both coefficient objects to one universe.
For discrete coefficient modules and locally compact groups this file constructs the same
pullback on Mathlib's `continuousCohomology 2` with the universes of `G` and `M` independent of
those of `H` and `N`. This is what a field isomorphism `K ≃+* L` between fields in different
universes, such as `K ≃+* ULift K`, induces on the canonical second Galois cohomology groups.

On canonical homogeneous cocycles the construction is the expected cochain pullback: a cocycle
`σ` of `G` goes to the cocycle `(h₀, h₁, h₂) ↦ f (σ (φ h₀) (φ h₁) (φ h₂))` of `H`
(`TauCeti.ContCohomology.iCycles_homogeneousCocyclesMap2_apply`), and classes go to classes
(`TauCeti.ContCohomology.continuousCohomologyMap2_homologyπ`). Since the pullback of a canonical
cocycle lives in a category of a different universe, it is constructed through the explicit
inhomogeneous model, in which cochains are plain functions and pullback needs no common
universe. When all four types share one universe it is Mathlib's map
(`TauCeti.ContCohomology.continuousCohomologyMap2_eq_map`).

## Main definitions

* `TauCeti.ContCohomology.homogeneousCocyclesMap2`: pullback of canonical continuous
  two-cocycles along a compatible pair.
* `TauCeti.ContCohomology.continuousCohomologyMap2`: the induced map on `continuousCohomology 2`.
* `TauCeti.ContCohomology.continuousCohomologyMap2Equiv`: the additive equivalence induced by a
  compatible pair of equivalences.

## Main results

* `TauCeti.ContCohomology.iCycles_homogeneousCocyclesMap2_apply`: the value of a pulled-back
  canonical cocycle.
* `TauCeti.ContCohomology.continuousCohomologyMap2_homologyπ`: the map on classes is induced by
  the map on cocycles.
* `TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2`: the
  comparison with the explicit model carries `explicitMap2` to `continuousCohomologyMap2`.
* `TauCeti.ContCohomology.homogeneousCocyclesMap2_eq_cocyclesMap` and
  `TauCeti.ContCohomology.continuousCohomologyMap2_eq_map`: in a single universe these are
  Mathlib's `ContinuousCohomology.cocyclesMap` and `ContinuousCohomology.map`.
* `TauCeti.ContCohomology.continuousCohomologyMap2_id` and
  `TauCeti.ContCohomology.continuousCohomologyMap2_comp`: functoriality, with the three groups in
  independent universes.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2 and
  §5: compatible pairs and the induced maps on homogeneous and inhomogeneous cochains.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u v w

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (H N : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction H N] [ContinuousSMul H N]

/-- Pullback of canonical continuous two-cocycles along a compatible pair `(φ, f)`, with the
universes of `G` and `M` independent of those of `H` and `N`. Its value is computed by
`TauCeti.ContCohomology.iCycles_homogeneousCocyclesMap2_apply`. -/
def homogeneousCocyclesMap2 (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2 →+
      _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ H N) 2 :=
  (cocycleEquiv2 H N).toAddMonoidHom.comp
    ((cocyclesMap2 G M H N φ f continuous_of_discreteTopology hf).comp
      (cocycleEquiv2 G M).symm.toAddMonoidHom)

/-- On explicit cocycles, pullback of canonical cocycles is the explicit pullback. -/
@[simp]
theorem homogeneousCocyclesMap2_cocycleEquiv2 (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (c : Z2 G M) :
    homogeneousCocyclesMap2 G M H N φ f hf (cocycleEquiv2 G M c) =
      cocycleEquiv2 H N (cocyclesMap2 G M H N φ f continuous_of_discreteTopology hf c) := by
  simp [homogeneousCocyclesMap2]

/-- **The pulled-back canonical cocycle.** The homogeneous cocycle `σ` of `G` goes to the
homogeneous cocycle `(h₀, h₁, h₂) ↦ f (σ (φ h₀) (φ h₁) (φ h₂))` of `H`. -/
theorem iCycles_homogeneousCocyclesMap2_apply (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (σ : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2) (h₀ h₁ h₂ : H) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ H N)).iCycles 2
        (homogeneousCocyclesMap2 G M H N φ f hf σ)).val h₀ h₁ h₂ =
      f (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 2 σ).val
        (φ h₀) (φ h₁) (φ h₂)) := by
  obtain ⟨c, rfl⟩ := (cocycleEquiv2 G M).surjective σ
  rw [homogeneousCocyclesMap2_cocycleEquiv2]
  -- `iCycles_cocycleEquiv2` uses the short-complex spelling of the same inclusion.
  have hH : (TopRep.homogeneousCochains (ofDiscreteModule ℤ H N)).iCycles 2
      (cocycleEquiv2 H N (cocyclesMap2 G M H N φ f continuous_of_discreteTopology hf c)) =
      cochainEquiv2 H N ⟨_, Z2_le_C2 H N
        (cocyclesMap2 G M H N φ f continuous_of_discreteTopology hf c).property⟩ :=
    iCycles_cocycleEquiv2 H N _
  have hG : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles 2
      (cocycleEquiv2 G M c) = cochainEquiv2 G M ⟨c.val, Z2_le_C2 G M c.property⟩ :=
    iCycles_cocycleEquiv2 G M c
  rw [hH, hG, cochainEquiv2_apply, cochainEquiv2_apply]
  simp only [homogeneous2_apply, cocyclesMap2_coe, cochainsMap2_apply,
    MonoidHom.coe_ofClass, map_mul, map_inv, hf]
  -- The two sides differ only in the instance path of the action of `H`, on `N` and on the
  -- carrier of `ofDiscreteModule ℤ H N`, which is `N` by definition.
  rfl

/-- Pullback along a compatible pair on Mathlib's `continuousCohomology 2`, with the universes
of `G` and `M` independent of those of `H` and `N`. It is induced by
`TauCeti.ContCohomology.homogeneousCocyclesMap2` (`continuousCohomologyMap2_homologyπ`), and in
a single universe it is Mathlib's `ContinuousCohomology.map` (`continuousCohomologyMap2_eq_map`).
-/
def continuousCohomologyMap2 (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    continuousCohomology 2 (ofDiscreteModule ℤ G M) →+
      continuousCohomology 2 (ofDiscreteModule ℤ H N) :=
  (explicitH2AddEquivContinuousCohomology H N).toAddMonoidHom.comp
    ((explicitMap2 G M H N φ f continuous_of_discreteTopology hf).comp
      (explicitH2AddEquivContinuousCohomology G M).symm.toAddMonoidHom)

/-- The comparison with the explicit model carries the explicit pullback `explicitMap2` to
`continuousCohomologyMap2`. -/
@[simp]
theorem explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2 (φ : H →ₜ* G)
    (f : M →+ N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : H2 G M) :
    continuousCohomologyMap2 G M H N φ f hf (explicitH2AddEquivContinuousCohomology G M x) =
      explicitH2AddEquivContinuousCohomology H N
        (explicitMap2 G M H N φ f continuous_of_discreteTopology hf x) := by
  simp [continuousCohomologyMap2]

/-- **The map on classes is induced by the map on cocycles.** The class of a canonical cocycle
goes to the class of its pullback. -/
@[simp]
theorem continuousCohomologyMap2_homologyπ (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (σ : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2) :
    continuousCohomologyMap2 G M H N φ f hf
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2 σ) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ H N)).homologyπ 2
        (homogeneousCocyclesMap2 G M H N φ f hf σ) := by
  obtain ⟨c, rfl⟩ := (cocycleEquiv2 G M).surjective σ
  rw [← explicitH2AddEquivContinuousCohomology_apply,
    explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2, explicitMap2_mk,
    explicitH2AddEquivContinuousCohomology_apply, homogeneousCocyclesMap2_cocycleEquiv2]

section SameUniverse

variable (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction H N] [ContinuousSMul H N]

/-- In a single universe, pullback of canonical cocycles is Mathlib's
`ContinuousCohomology.cocyclesMap` along the same compatible pair. -/
theorem homogeneousCocyclesMap2_eq_cocyclesMap (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (σ : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2) :
    homogeneousCocyclesMap2 G M H N φ f hf σ =
      _root_.ContinuousCohomology.cocyclesMap φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 2 σ := by
  obtain ⟨c, rfl⟩ := (cocycleEquiv2 G M).surjective σ
  rw [homogeneousCocyclesMap2_cocycleEquiv2, cocycleEquiv2_naturality]

/-- In a single universe, `continuousCohomologyMap2` is Mathlib's `ContinuousCohomology.map`
along the same compatible pair. -/
theorem continuousCohomologyMap2_eq_map (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (x : continuousCohomology 2 (ofDiscreteModule ℤ G M)) :
    continuousCohomologyMap2 G M H N φ f hf x =
      _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 2 x := by
  obtain ⟨y, rfl⟩ := (explicitH2AddEquivContinuousCohomology G M).surjective x
  rw [explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2,
    explicitH2AddEquivContinuousCohomology_map]

end SameUniverse

/-- Pullback along the identity compatible pair is the identity. -/
@[simp]
theorem continuousCohomologyMap2_id (hid : ∀ (g : G) (m : M),
    (AddMonoidHom.id M) ((ContinuousMonoidHom.id G) g • m) = g • (AddMonoidHom.id M) m :=
      fun _ _ ↦ rfl) :
    continuousCohomologyMap2 G M G M (ContinuousMonoidHom.id G) (AddMonoidHom.id M) hid =
      AddMonoidHom.id _ := by
  ext x
  obtain ⟨y, rfl⟩ := (explicitH2AddEquivContinuousCohomology G M).surjective x
  rw [explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2, explicitMap2_id G M hid,
    AddMonoidHom.id_apply, AddMonoidHom.id_apply]

/-- Pullback respects composition of compatible pairs, with the three groups and their
coefficient modules in independent universes. -/
theorem continuousCohomologyMap2_comp (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (K P : Type w) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [LocallyCompactSpace K] [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction K P] [ContinuousSMul K P]
    (ψ : K →ₜ* H) (q : N →+ P) (hq : ∀ (k : K) (n : N), q (ψ k • n) = k • q n) :
    continuousCohomologyMap2 G M K P (φ.comp ψ) (q.comp f) (φ.comp_map_smul ψ f q hf hq) =
      (continuousCohomologyMap2 H N K P ψ q hq).comp
        (continuousCohomologyMap2 G M H N φ f hf) := by
  ext x
  obtain ⟨y, rfl⟩ := (explicitH2AddEquivContinuousCohomology G M).surjective x
  rw [AddMonoidHom.comp_apply, explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2,
    explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2,
    explicitH2AddEquivContinuousCohomology_continuousCohomologyMap2,
    explicitMap2_comp G M H N φ f continuous_of_discreteTopology hf K P ψ q
      continuous_of_discreteTopology hq, AddMonoidHom.comp_apply]

/-- The additive equivalence of canonical second continuous cohomology groups induced by a
compatible pair of a continuous multiplicative equivalence `φ : H ≃ₜ* G` and an additive
equivalence `e : M ≃+ N`, with the universes of `G` and `M` independent of those of `H` and
`N`. Its forward and inverse maps are `continuousCohomologyMap2` along the pair and along its
inverse. -/
def continuousCohomologyMap2Equiv (φ : H ≃ₜ* G) (e : M ≃+ N)
    (he : ∀ (h : H) (m : M), e (φ h • m) = h • e m) :
    continuousCohomology 2 (ofDiscreteModule ℤ G M) ≃+
      continuousCohomology 2 (ofDiscreteModule ℤ H N) :=
  (explicitH2AddEquivContinuousCohomology G M).symm.trans
    ((explicitMap2Equiv G M H N φ e continuous_of_discreteTopology continuous_of_discreteTopology
      he).trans (explicitH2AddEquivContinuousCohomology H N))

/-- The equivalence is pullback along its forward compatible pair. -/
@[simp]
theorem continuousCohomologyMap2Equiv_apply (φ : H ≃ₜ* G) (e : M ≃+ N)
    (he : ∀ (h : H) (m : M), e (φ h • m) = h • e m)
    (x : continuousCohomology 2 (ofDiscreteModule ℤ G M)) :
    continuousCohomologyMap2Equiv G M H N φ e he x =
      continuousCohomologyMap2 G M H N φ e.toAddMonoidHom he x := by
  simp [continuousCohomologyMap2Equiv, continuousCohomologyMap2]

/-- The inverse equivalence is pullback along the inverse compatible pair. -/
@[simp]
theorem continuousCohomologyMap2Equiv_symm_apply (φ : H ≃ₜ* G) (e : M ≃+ N)
    (he : ∀ (h : H) (m : M), e (φ h • m) = h • e m)
    (x : continuousCohomology 2 (ofDiscreteModule ℤ H N)) :
    (continuousCohomologyMap2Equiv G M H N φ e he).symm x =
      continuousCohomologyMap2 H N G M φ.symm e.symm.toAddMonoidHom
        (AddEquiv.symm_map_smul_of_map_mulEquiv_smul e φ.toMulEquiv he) x := by
  simp [continuousCohomologyMap2Equiv, continuousCohomologyMap2]

end TauCeti.ContCohomology
