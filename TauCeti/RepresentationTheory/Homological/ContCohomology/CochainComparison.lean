/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Homogeneous
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Inhomogeneous coordinates on continuous homogeneous cochains

As additive groups, the first three terms of Mathlib's homogeneous cochain complex are identified
with `M`, `C1 G M`, and `C2 G M`. The forward maps are the classical formulas
`g₀ • m`, `g₀ • c (g₀⁻¹ * g₁)`, and `g₀ • c (g₀⁻¹ * g₁, g₁⁻¹ * g₂)`;
the inverse maps evaluate at `1`, at `(1, g)`, and at `(1, g, g * h)`.
The differential compatibilities identify the canonical differentials with `d0` and `d1`,
providing the cochain comparison needed to identify first cohomology and its coboundaries.
All three comparisons are natural in compatible pairs of group and coefficient maps.
These are additive equivalences; no identification of the pointwise and compact-open
topologies is asserted.

Degrees zero and one need no local compactness. The degree-two inverse uses
`ContinuousMap.uncurry`, so the group is locally compact.
In particular the construction applies to profinite groups. Coefficients are discrete modules
with a jointly continuous action; the canonical complex is always the one attached to
`ofDiscreteModule ℤ G M`.

The formulas follow Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.,
Chapter I §2. The pointwise homogeneous formulas are reused from `Homogeneous.lean`;
Mathlib's `TopRep.homogeneousCochains` supplies the actual complex. Its terms are written
as the invariant submodules of the iterated coinduced representation, the normal form needed
by the simplifier for the application lemmas.
-/

public section

namespace TauCeti.ContCohomology

universe u

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

omit [ContinuousSMul G M] in
/-- A homogeneous zero-cochain is determined by its value at the identity. -/
theorem homogeneousCochains_zero_apply
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.invariants) (g : G) :
    (SMul.smul g : M → M) (c.val 1) = c.val g := by
  have h := congrArg (fun f : C(G, M) ↦ f g) (c.property g)
  -- Evaluate the invariant equation in the underlying continuous function space.
  change (SMul.smul g : M → M) (c.val (g⁻¹ * g)) = c.val g at h
  simpa using h

/-- Degree-zero inhomogeneous cochains as canonical homogeneous cochains. -/
def cochainEquiv0 : M ≃+ (ofDiscreteModule ℤ G M).ρ.coind₁.invariants where
  toFun m := ⟨(⟨fun g ↦ g • m, continuous_id.smul continuous_const⟩ : C(G, M)), by
    intro g
    ext h
    -- Unpack the coinduced action on the explicitly constructed continuous map.
    change g • ((g⁻¹ * h) • m) = h • m
    simp [← mul_smul]⟩
  invFun c := c.val 1
  left_inv m := one_smul G m
  right_inv c := by
    apply Subtype.ext
    ext g
    exact homogeneousCochains_zero_apply G M c g
  map_add' m n := by
    apply Subtype.ext
    ext g
    exact smul_add g m n

@[simp]
theorem cochainEquiv0_apply (m : M) (g : G) :
    (cochainEquiv0 G M m).val g = g • m := (rfl)

@[simp]
theorem cochainEquiv0_symm_apply
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.invariants) :
    (cochainEquiv0 G M).symm c = c.val 1 := (rfl)

omit [ContinuousSMul G M] in
/-- A homogeneous one-cochain is determined by evaluation with first argument `1`. -/
theorem homogeneousCochains_one_apply
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.invariants) (g h : G) :
    (SMul.smul g : M → M) (c.val 1 (g⁻¹ * h)) = c.val g h := by
  have e := congrArg (fun f : C(G, C(G, M)) ↦ f g h) (c.property g)
  -- The iterated coinduced action translates both arguments.
  change (SMul.smul g : M → M) (c.val (g⁻¹ * g) (g⁻¹ * h)) = c.val g h at e
  simpa using e

/-- Continuous one-cochains as canonical homogeneous cochains, by currying their homogeneous
form. -/
def cochainEquiv1 : C1 G M ≃+
    (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.invariants where
  toFun c := ⟨ContinuousMap.curry
    (⟨fun p ↦ homogeneous1 c.val p.1 p.2,
      continuous_homogeneous1 (mem_C1_iff.mp c.property) continuous_fst
        continuous_snd⟩ : C(G × G, M)), by
    intro g
    ext h k
    -- Unpack the two coinduced actions and the curried map.
    change g • homogeneous1 c.val (g⁻¹ * h) (g⁻¹ * k) = homogeneous1 c.val h k
    simp [← mul_smul, mul_assoc]⟩
  invFun c := ⟨c.val 1, mem_C1_iff.mpr (c.val 1).continuous⟩
  left_inv c := by
    apply Subtype.ext
    funext g
    exact homogeneous1_one_left c.val g
  right_inv c := by
    apply Subtype.ext
    ext g h
    exact (homogeneous1_apply (M := M) (c.val 1) g h).trans
      (homogeneousCochains_one_apply G M c g h)
  map_add' c d := by
    apply Subtype.ext
    ext g h
    -- Evaluate the addition of the curried continuous maps.
    change homogeneous1 (c + d).val g h = homogeneous1 c.val g h + homogeneous1 d.val g h
    simp

@[simp]
theorem cochainEquiv1_apply (c : C1 G M) (g h : G) :
    (cochainEquiv1 G M c).val g h = homogeneous1 c.val g h := (rfl)

@[simp]
theorem cochainEquiv1_symm_apply
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.invariants) (g : G) :
    ((cochainEquiv1 G M).symm c).val g = c.val 1 g := (rfl)

omit [ContinuousSMul G M] in
/-- A homogeneous two-cochain is determined by evaluation with first argument `1`. -/
theorem homogeneousCochains_two_apply
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.coind₁.invariants) (g h k : G) :
    (SMul.smul g : M → M) (c.val 1 (g⁻¹ * h) (g⁻¹ * k)) = c.val g h k := by
  have e := congrArg (fun f : C(G, C(G, C(G, M))) ↦ f g h k) (c.property g)
  -- The three coinduced actions translate all three arguments.
  change (SMul.smul g : M → M) (c.val (g⁻¹ * g) (g⁻¹ * h) (g⁻¹ * k)) =
    c.val g h k at e
  simpa using e

/-- The degree-zero comparison carries `d0` to Mathlib's homogeneous differential. -/
theorem cochainEquiv_d0 (m : M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 0 1).hom
        (cochainEquiv0 G M m) =
      cochainEquiv1 G M ⟨d0 G M m, mem_C1_iff.mpr (continuous_d0_apply m)⟩ := by
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply]
  ext g h
  -- The recursive differential in degree zero evaluates to the difference of two values.
  change h • m - g • m = homogeneous1 (d0 G M m) g h
  simp [smul_sub, ← mul_smul]

variable [LocallyCompactSpace G]

/-- Continuous two-cochains as canonical homogeneous cochains. Local compactness supplies
uncurrying for the inverse. -/
def cochainEquiv2 : C2 G M ≃+
    (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.coind₁.invariants where
  toFun c := ⟨⟨fun g ↦ ContinuousMap.curry
    (⟨fun p ↦ homogeneous2 c.val g p.1 p.2,
      continuous_homogeneous2 (mem_C2_iff.mp c.property) continuous_const
        continuous_fst continuous_snd⟩ : C(G × G, M)),
    ContinuousMap.continuous_of_continuous_uncurry _ <|
      ContinuousMap.continuous_of_continuous_uncurry _ <|
        continuous_homogeneous2 (mem_C2_iff.mp c.property)
          (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst)
          continuous_snd⟩, by
    intro g
    ext h k l
    -- Unpack the three coinduced actions and the two currying operations.
    change g • homogeneous2 c.val (g⁻¹ * h) (g⁻¹ * k) (g⁻¹ * l) =
      homogeneous2 c.val h k l
    simp [← mul_smul, mul_assoc]⟩
  invFun c := ⟨fun p ↦ c.val 1 p.1 (p.1 * p.2),
    mem_C2_iff.mpr <| (c.val 1).uncurry.continuous.comp
      (continuous_fst.prodMk (continuous_fst.mul continuous_snd))⟩
  left_inv c := by
    apply Subtype.ext
    funext p
    exact (homogeneous2_apply c.val 1 p.1 (p.1 * p.2)).trans (by simp)
  right_inv c := by
    apply Subtype.ext
    ext g h k
    have e := homogeneous2_apply (M := M)
      (fun p : G × G ↦ c.val 1 p.1 (p.1 * p.2)) g h k
    simp only [mul_assoc, mul_inv_cancel_left] at e
    exact e.trans (homogeneousCochains_two_apply G M c g h k)
  map_add' c d := by
    apply Subtype.ext
    ext g h k
    -- Evaluate addition in the iterated continuous function spaces.
    change homogeneous2 (c + d).val g h k =
      homogeneous2 c.val g h k + homogeneous2 d.val g h k
    simp

@[simp]
theorem cochainEquiv2_apply (c : C2 G M) (g h k : G) :
    (cochainEquiv2 G M c).val g h k = homogeneous2 c.val g h k := (rfl)

@[simp]
theorem cochainEquiv2_symm_apply
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.coind₁.invariants) (g h : G) :
    ((cochainEquiv2 G M).symm c).val (g, h) = c.val 1 g (g * h) := (rfl)

/-- The degree-one comparison carries `d1` to Mathlib's homogeneous differential. -/
theorem cochainEquiv_d1 (c : C1 G M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom
        (cochainEquiv1 G M c) =
      cochainEquiv2 G M ⟨d1 G M c.val,
        mem_C2_iff.mpr (continuous_d1_apply (mem_C1_iff.mp c.property))⟩ := by
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply]
  ext g h k
  -- Mathlib's recursive differential is the alternating sum on three arguments.
  change homogeneous1 c.val h k -
    (homogeneous1 c.val g k - homogeneous1 c.val g h) =
      homogeneous2 (d1 G M c.val) g h k
  rw [homogeneous2_d1]
  abel

section Naturality

variable (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction H N] [ContinuousSMul H N]
  (φ : H →ₜ* G) (f : M →+ N)
  (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)

omit [LocallyCompactSpace G] in
/-- The degree-zero cochain comparison is natural in compatible pairs. -/
theorem cochainEquiv0_naturality (m : M) :
    ((_root_.ContinuousCohomology.cochainsMap φ
      (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m))).f 0).hom
        (cochainEquiv0 G M m) = cochainEquiv0 H N (f m) := by
  apply Subtype.ext
  ext h
  -- Evaluate the canonical map on a coinduced function.
  change (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap
    (fun h m ↦ hf h m)).hom (φ h • m) = h • f m
  exact (ofDiscreteModulePair_hom_apply (φ : H →* G) f.toIntLinearMap
    (fun h m ↦ hf h m) (φ h • m)).trans (hf h m)

omit [LocallyCompactSpace G] in
/-- The degree-one cochain comparison is natural in compatible pairs. -/
theorem cochainEquiv1_naturality (c : C1 G M) :
    ((_root_.ContinuousCohomology.cochainsMap φ
      (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m))).f 1).hom
        (cochainEquiv1 G M c) =
      cochainEquiv1 H N ⟨cochainsMap1 (φ : H →* G) f c.val,
        mem_C1_iff.mpr (continuous_cochainsMap1 φ f continuous_of_discreteTopology
          (mem_C1_iff.mp c.property))⟩ := by
  apply Subtype.ext
  ext h k
  -- Evaluate the canonical map on the two curried arguments.
  change (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m)).hom
    (homogeneous1 (M := M) c.val (φ h) (φ k)) =
      homogeneous1 (cochainsMap1 (φ : H →* G) f c.val) h k
  refine (ofDiscreteModulePair_hom_apply (φ : H →* G) f.toIntLinearMap
    (fun h m ↦ hf h m) _).trans ?_
  simp [hf]
  rfl

/-- The degree-two cochain comparison is natural in compatible pairs. -/
theorem cochainEquiv2_naturality [LocallyCompactSpace H] (c : C2 G M) :
    ((_root_.ContinuousCohomology.cochainsMap φ
      (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m))).f 2).hom
        (cochainEquiv2 G M c) =
      cochainEquiv2 H N ⟨cochainsMap2 (φ : H →* G) f c.val,
        mem_C2_iff.mpr (continuous_cochainsMap2 φ f continuous_of_discreteTopology
          (mem_C2_iff.mp c.property))⟩ := by
  apply Subtype.ext
  ext h k l
  -- Evaluate the canonical map on the three curried arguments.
  change (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m)).hom
    (homogeneous2 (M := M) c.val (φ h) (φ k) (φ l)) =
      homogeneous2 (cochainsMap2 (φ : H →* G) f c.val) h k l
  refine (ofDiscreteModulePair_hom_apply (φ : H →* G) f.toIntLinearMap
    (fun h m ↦ hf h m) _).trans ?_
  simp [hf]
  rfl

end Naturality

end TauCeti.ContCohomology
