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
The differential compatibilities identify the canonical differentials with `d0`, `d1`, and `d2`,
including the cocycle condition in degree two.
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
private theorem smul_homogeneousCochain0
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.invariants) (g : G) :
    (SMul.smul g : M → M) (c.val 1) = c.val g := by
  have h := congrArg (fun f : C(G, M) ↦ f g) (c.property g)
  -- The bundled carrier `(ofDiscreteModule ℤ G M).V` is only semireducibly `M`.
  -- `simp [coind₁_apply_apply, ofDiscreteModule_ρ_apply_apply]` cannot match that
  -- carrier with the explicit `C(G, M)` evaluation; normalize it before simplifying.
  change (SMul.smul g : M → M) (c.val (g⁻¹ * g)) = c.val g at h
  simpa using h

/-- Degree-zero inhomogeneous cochains as canonical homogeneous cochains. -/
def cochainEquiv0 : M ≃+ (ofDiscreteModule ℤ G M).ρ.coind₁.invariants where
  toFun m := ⟨(⟨fun g ↦ g • m, continuous_id.smul continuous_const⟩ : C(G, M)), by
    intro g
    ext h
    -- The bundled topology on `ofDiscreteModule` is only semireducibly the topology
    -- of `M`, so the coinduction/currying evaluation lemmas do not match these
    -- explicitly constructed continuous maps. Normalize the carrier and topology first.
    change g • ((g⁻¹ * h) • m) = h • m
    simp [← mul_smul]⟩
  invFun c := c.val 1
  left_inv m := one_smul G m
  right_inv c := by
    apply Subtype.ext
    ext g
    exact smul_homogeneousCochain0 G M c g
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
private theorem smul_homogeneousCochain1
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.invariants) (g h : G) :
    (SMul.smul g : M → M) (c.val 1 (g⁻¹ * h)) = c.val g h := by
  have e := congrArg (fun f : C(G, C(G, M)) ↦ f g h) (c.property g)
  -- The bundled carrier `(ofDiscreteModule ℤ G M).V` is only semireducibly `M`.
  -- `simp [coind₁_apply_apply, ofDiscreteModule_ρ_apply_apply]` cannot match that
  -- carrier with the explicit `C(G, M)` evaluation; normalize it before simplifying.
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
    -- The bundled topology on `ofDiscreteModule` is only semireducibly the topology
    -- of `M`, so the coinduction/currying evaluation lemmas do not match these
    -- explicitly constructed continuous maps. Normalize the carrier and topology first.
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
      (smul_homogeneousCochain1 G M c g h)
  map_add' c d := by
    apply Subtype.ext
    ext g h
    simp only [homogeneous1_apply]
    exact smul_add g (c.val (g⁻¹ * h)) (d.val (g⁻¹ * h))

@[simp]
theorem cochainEquiv1_apply (c : C1 G M) (g h : G) :
    (cochainEquiv1 G M c).val g h = homogeneous1 c.val g h := (rfl)

@[simp]
theorem cochainEquiv1_symm_apply
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.invariants) (g : G) :
    ((cochainEquiv1 G M).symm c).val g = c.val 1 g := (rfl)

omit [ContinuousSMul G M] in
/-- A homogeneous two-cochain is determined by evaluation with first argument `1`. -/
private theorem smul_homogeneousCochain2
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.coind₁.invariants) (g h k : G) :
    (SMul.smul g : M → M) (c.val 1 (g⁻¹ * h) (g⁻¹ * k)) = c.val g h k := by
  have e := congrArg (fun f : C(G, C(G, C(G, M))) ↦ f g h k) (c.property g)
  -- The bundled carrier `(ofDiscreteModule ℤ G M).V` is only semireducibly `M`.
  -- `simp [coind₁_apply_apply, ofDiscreteModule_ρ_apply_apply]` cannot match that
  -- carrier with the explicit `C(G, M)` evaluation; normalize it before simplifying.
  change (SMul.smul g : M → M) (c.val (g⁻¹ * g) (g⁻¹ * h) (g⁻¹ * k)) =
    c.val g h k at e
  simpa using e

/-- The degree-zero comparison carries `d0` to Mathlib's homogeneous differential. -/
theorem d_cochainEquiv0 (m : M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 0 1).hom
        (cochainEquiv0 G M m) =
      cochainEquiv1 G M ⟨d0 G M m, mem_C1_iff.mpr (continuous_d0_apply m)⟩ := by
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply]
  ext g h
  simp only [TopRep.hom_d_succ, TopRep.d_zero, TopRep.hom_ofHom, ContIntertwiningMap.sub_apply,
    ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  simp [smul_sub, ← mul_smul]
  rfl

/-- The inverse degree-one comparison carries the canonical differential to `d0`. -/
theorem cochainEquiv1_symm_d
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.invariants) :
    (cochainEquiv1 G M).symm
        (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 0 1).hom c) =
      ⟨d0 G M ((cochainEquiv0 G M).symm c),
        mem_C1_iff.mpr (continuous_d0_apply _)⟩ := by
  apply (cochainEquiv1 G M).injective
  simpa only [AddEquiv.apply_symm_apply] using d_cochainEquiv0 G M ((cochainEquiv0 G M).symm c)

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
    -- The bundled topology on `ofDiscreteModule` is only semireducibly the topology
    -- of `M`, so the coinduction/currying evaluation lemmas do not match these
    -- explicitly constructed continuous maps. Normalize the carrier and topology first.
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
    exact e.trans (smul_homogeneousCochain2 G M c g h k)
  map_add' c d := by
    apply Subtype.ext
    ext g h k
    simp only [homogeneous2_apply]
    exact smul_add g (c.val (g⁻¹ * h, h⁻¹ * k)) (d.val (g⁻¹ * h, h⁻¹ * k))

@[simp]
theorem cochainEquiv2_apply (c : C2 G M) (g h k : G) :
    (cochainEquiv2 G M c).val g h k = homogeneous2 c.val g h k := (rfl)

@[simp]
theorem cochainEquiv2_symm_apply
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.coind₁.invariants) (g h : G) :
    ((cochainEquiv2 G M).symm c).val (g, h) = c.val 1 g (g * h) := (rfl)

/-- The degree-one comparison carries `d1` to Mathlib's homogeneous differential. -/
theorem d_cochainEquiv1 (c : C1 G M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom
        (cochainEquiv1 G M c) =
      cochainEquiv2 G M ⟨d1 G M c.val,
        mem_C2_iff.mpr (continuous_d1_apply (mem_C1_iff.mp c.property))⟩ := by
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply]
  ext g h k
  simp only [TopRep.hom_d_succ, TopRep.d_zero, TopRep.hom_ofHom,
    ContIntertwiningMap.sub_apply, ContRepresentation.coind₁ι_toFun,
    ContRepresentation.coind₁Map_toFun, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [cochainEquiv1_apply, cochainEquiv1_apply, cochainEquiv1_apply,
    cochainEquiv2_apply, homogeneous2_d1]
  exact (sub_sub_eq_add_sub (homogeneous1 c.val h k) (homogeneous1 c.val g k)
    (homogeneous1 c.val g h)).trans (add_sub_right_comm _ _ _)

/-- The inverse degree-two comparison carries the canonical differential to `d1`. -/
theorem cochainEquiv2_symm_d
    (c : (ofDiscreteModule ℤ G M).ρ.coind₁.coind₁.invariants) :
    (cochainEquiv2 G M).symm
        (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom c) =
      ⟨d1 G M ((cochainEquiv1 G M).symm c).val,
        mem_C2_iff.mpr (continuous_d1_apply
          (mem_C1_iff.mp ((cochainEquiv1 G M).symm c).property))⟩ := by
  apply (cochainEquiv2 G M).injective
  simpa only [AddEquiv.apply_symm_apply] using d_cochainEquiv1 G M ((cochainEquiv1 G M).symm c)

/-- The differential of the degree-two comparison is the homogeneous form of `d2`. -/
theorem d_cochainEquiv2_apply (c : C2 G M) (g h k l : G) :
    (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 2 3).hom
        (cochainEquiv2 G M c)).val g h k l =
      g • d2 G M c.val (g⁻¹ * h, h⁻¹ * k, k⁻¹ * l) := by
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [TopRep.hom_d_succ, TopRep.d_zero, TopRep.hom_ofHom,
    ContIntertwiningMap.sub_apply, ContRepresentation.coind₁ι_toFun,
    ContRepresentation.coind₁Map_toFun, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    cochainEquiv2_apply, homogeneous2_apply, d2_apply, smul_sub, smul_add, ← mul_smul]
  simp only [mul_assoc, mul_inv_cancel_left]
  -- Fix the coefficient carrier explicitly so that the constant-map evaluation matches.
  have hi (m : M) : ((ofDiscreteModule ℤ G M).ρ.coind₁ι m) l = m := rfl
  rw [hi]
  -- All four evaluations live in `M`; normalize the bundled additive instances for `abel`.
  change (h • c.val (h⁻¹ * k, k⁻¹ * l) : M) -
      (g • c.val (g⁻¹ * k, k⁻¹ * l) -
        (g • c.val (g⁻¹ * h, h⁻¹ * l) - g • c.val (g⁻¹ * h, h⁻¹ * k))) =
    h • c.val (h⁻¹ * k, k⁻¹ * l) - g • c.val (g⁻¹ * k, k⁻¹ * l) +
      g • c.val (g⁻¹ * h, h⁻¹ * l) - g • c.val (g⁻¹ * h, h⁻¹ * k)
  abel

/-- The degree-two comparison detects precisely the continuous inhomogeneous cocycles. -/
theorem d_cochainEquiv2_eq_zero_iff (c : C2 G M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 2 3).hom
        (cochainEquiv2 G M c) = 0 ↔ c.val ∈ Z2 G M := by
  rw [mem_Z2_iff, and_iff_right (mem_C2_iff.mp c.property), ← d2_apply_eq_zero_iff]
  constructor
  · intro hc
    funext ⟨g, h, k⟩
    have e := congrArg (fun z => z.val 1 g (g * h) (g * h * k)) hc
    rw [d_cochainEquiv2_apply] at e
    -- Normalize the bundled coefficient carrier before simplifying the group coordinates.
    change (1 : G) • d2 G M c.val (1⁻¹ * g, g⁻¹ * (g * h),
      (g * h)⁻¹ * (g * h * k)) = (0 : M) at e
    simpa only [inv_one, one_mul, inv_mul_cancel_left, one_smul, Pi.zero_apply] using e
  · intro hc
    apply Subtype.ext
    ext g h k l
    rw [d_cochainEquiv2_apply]
    -- The right side is the zero continuous map, evaluated in the bundled carrier.
    change g • d2 G M c.val (g⁻¹ * h, h⁻¹ * k, k⁻¹ * l) = (0 : M)
    rw [hc, Pi.zero_apply, smul_zero]

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
  simp only [_root_.ContinuousCohomology.cochainsMap_f, TopRep.invariantsResMap,
    TopModuleCat.hom_ofHom]
  rw [ContIntertwiningMap.mapInvariantsOfRes_apply]
  simp only [_root_.ContinuousCohomology.resolutionMap_succ, TopRep.hom_ofHom,
    ContRepresentation.coind₁ResMap_apply, _root_.ContinuousCohomology.resolutionMap_zero,
    cochainEquiv0_apply]
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
  simp only [_root_.ContinuousCohomology.cochainsMap_f, TopRep.invariantsResMap,
    TopModuleCat.hom_ofHom]
  rw [ContIntertwiningMap.mapInvariantsOfRes_apply]
  simp only [_root_.ContinuousCohomology.resolutionMap_succ, TopRep.hom_ofHom,
    ContRepresentation.coind₁ResMap_apply, _root_.ContinuousCohomology.resolutionMap_zero,
    cochainEquiv1_apply]
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
  simp only [_root_.ContinuousCohomology.cochainsMap_f, TopRep.invariantsResMap,
    TopModuleCat.hom_ofHom]
  rw [ContIntertwiningMap.mapInvariantsOfRes_apply]
  simp only [_root_.ContinuousCohomology.resolutionMap_succ, TopRep.hom_ofHom,
    ContRepresentation.coind₁ResMap_apply, _root_.ContinuousCohomology.resolutionMap_zero,
    cochainEquiv2_apply]
  refine (ofDiscreteModulePair_hom_apply (φ : H →* G) f.toIntLinearMap
    (fun h m ↦ hf h m) _).trans ?_
  simp [hf]
  rfl

end Naturality

end TauCeti.ContCohomology
