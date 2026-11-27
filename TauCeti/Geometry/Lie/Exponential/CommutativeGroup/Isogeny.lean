/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character
public import Mathlib.GroupTheory.Index

/-!
# Period lattices under isogenies and quotient maps

Let `f : G → G'` be a continuous homomorphism of commutative finite-dimensional real Lie groups,
with `G` connected. Its Lie map `df : 𝔤 → 𝔤'` carries the period lattice
`Λ_ℤ(G) = (2π)⁻¹ ker(exp)` into `Λ_ℤ(G')` (`ContinuousMonoidHom.lieMap_mem_periodLattice`), but in
general not onto it. When `df` is surjective, for instance when `f` is a quotient map, the image
has index

`[Λ_ℤ(G') : df(Λ_ℤ(G))] = [ker f : exp(ker df)]`

(`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice_of_surjective`), where `exp(ker df)` is
the subgroup of exponentials of the kernel of `df`. Indeed, for a linear right inverse `s` of
`df`, the map `Y ↦ exp(s(2π Y))` sends `Λ_ℤ(G')` into `ker f`, every element of `ker f` is reached
up to `exp(ker df)`, since every element of the connected group `G` is an exponential, and modulo
`exp(ker df)` its kernel on `Λ_ℤ(G')` is exactly `df(Λ_ℤ(G))`. The subgroup `exp(ker df)` is the
identity component of `ker f`
(`ContinuousMonoidHom.image_lieExp_ker_lieMap` in
`TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Quotient`), which gives the quotient form of the
index.

When `df` is a linear isomorphism, for instance for a surjective homomorphism with finite kernel
between groups of the same dimension (an *isogeny*), `exp(ker df)` is trivial and the index is the
order of the kernel of `f`,

`[Λ_ℤ(G') : df(Λ_ℤ(G))] = |ker f|`

(`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice`).

The hypothesis on `df` is met by isogenies: if `ker f` is discrete then `df` is injective
(`ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker` in
`TauCeti.Geometry.Lie.Subgroup.Kernel`). The central isogeny of the torus
of `U(2)` is worked out in `TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Isogeny.UnitaryTorus`.

## Main results

* `ContinuousMonoidHom.relIndex_map_lieMap_periodLattice_of_surjective`: for commutative groups
  with connected source and surjective Lie map, the image of the period lattice of the source has
  index `[ker f : exp(ker df)]` in the period lattice of the target.
* `ContinuousMonoidHom.relIndex_map_lieMap_periodLattice`: for commutative groups with connected
  source and bijective Lie map, the image of the period lattice of the source has index the order
  of the kernel in the period lattice of the target.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
-/

public section

noncomputable section

open Real
open scoped ContDiff Manifold

namespace ContinuousMonoidHom

open TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']
  [T2Space G] [BoundarylessManifold I G] [T2Space G'] [BoundarylessManifold I' G']
  [IsMulCommutative G] [IsMulCommutative G']

/-- Membership in the period lattice, read through the additive exponential. -/
private theorem mem_periodLattice_iff_lieExpAddMonoidHom {X : LeftInvariantDerivation I G} :
    X ∈ periodLattice I G ↔ lieExpAddMonoidHom (I := I) (G := G) ((2 * π) • X) = 0 := by
  rw [mem_periodLattice, ← mem_ker_lieExpAddMonoidHom, AddMonoidHom.mem_ker]

omit [T2Space G'] [BoundarylessManifold I' G'] [IsMulCommutative G'] in
/-- The kernel step of the index formula: for a right inverse `s` of the Lie map `df` and `Y` in
the period lattice of `G'`, `exp(s(2π Y))` lies in `exp(ker df)` exactly when `Y` lies in
`df(Λ_ℤ(G))`. -/
private theorem lieExpAddMonoidHom_mem_map_ker_iff (f : G →ₜ* G')
    (s : LeftInvariantDerivation I' G' →ₗ[ℝ] LeftInvariantDerivation I G)
    (hs : ∀ Y, lieMap (I := I) (I' := I') f (s Y) = Y) {Y : LeftInvariantDerivation I' G'} :
    lieExpAddMonoidHom (I := I) (G := G) (s ((2 * π) • Y)) ∈
        (LinearMap.ker (lieMap (I := I) (I' := I') f).toLinearMap).toAddSubgroup.map
          (lieExpAddMonoidHom (I := I) (G := G)) ↔
      Y ∈ (periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom := by
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.mem_ker,
    LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap]
  constructor
  · rintro ⟨Z, hZ, hZY⟩
    refine ⟨(2 * π)⁻¹ • (s ((2 * π) • Y) - Z),
      mem_periodLattice_iff_lieExpAddMonoidHom.2 ?_, ?_⟩
    · rw [smul_inv_smul₀ two_pi_pos.ne', map_sub, hZY, sub_self]
    · rw [map_smul, map_sub, hs, hZ, sub_zero, inv_smul_smul₀ two_pi_pos.ne']
  · rintro ⟨X, hX, rfl⟩
    refine ⟨s ((2 * π) • lieMap (I := I) (I' := I') f X) - (2 * π) • X, ?_, ?_⟩
    · rw [map_sub, hs, map_smul, sub_self]
    · rw [map_sub, mem_periodLattice_iff_lieExpAddMonoidHom.1 hX, sub_zero]

variable [PreconnectedSpace G]

/-- The image step of the index formula: for a right inverse `s` of the Lie map `df`, the map
`Y ↦ exp(s(2π Y))` modulo `exp(ker df)` sends the period lattice of `G'` onto the image of
`ker f`. -/
private theorem map_periodLattice_eq_map_ker (f : G →ₜ* G')
    (s : LeftInvariantDerivation I' G' →ₗ[ℝ] LeftInvariantDerivation I G)
    (hs : ∀ Y, lieMap (I := I) (I' := I') f (s Y) = Y) :
    (periodLattice I' G').map ((QuotientAddGroup.mk'
        ((LinearMap.ker (lieMap (I := I) (I' := I') f).toLinearMap).toAddSubgroup.map
          (lieExpAddMonoidHom (I := I) (G := G)))).comp
        ((lieExpAddMonoidHom (I := I) (G := G)).comp
          (s.comp ((2 * π) • LinearMap.id)).toAddMonoidHom)) =
      f.ker.toAddSubgroup.map (QuotientAddGroup.mk'
        ((LinearMap.ker (lieMap (I := I) (I' := I') f).toLinearMap).toAddSubgroup.map
          (lieExpAddMonoidHom (I := I) (G := G)))) := by
  have hexp (X : LeftInvariantDerivation I G) :
      f.toMonoidHom.toAdditive (lieExpAddMonoidHom (I := I) (G := G) X) =
        lieExpAddMonoidHom (I := I') (G := G') (lieMap (I := I) (I' := I') f X) := by
    simp [lieExpAddMonoidHom_apply, map_lieExp (I' := I')]
  ext q
  simp only [AddSubgroup.mem_map, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨_, ?_, rfl⟩
    have h := hexp (s ((2 * π) • Y))
    rw [hs, mem_periodLattice_iff_lieExpAddMonoidHom.1 hY] at h
    rw [Additive.mem_toAddSubgroup, MonoidHom.mem_ker]
    simpa using h
  · rintro ⟨g, hg, rfl⟩
    -- `g = exp X`, since every element of the connected group `G` is an exponential.
    obtain ⟨X, hX⟩ := lieExp_surjective_of_preconnectedSpace (I := I) (G := G) (Additive.toMul g)
    obtain rfl : g = lieExpAddMonoidHom (I := I) (G := G) X := by
      rw [lieExpAddMonoidHom_apply, hX, ofMul_toMul]
    refine ⟨(2 * π)⁻¹ • lieMap (I := I) (I' := I') f X,
      mem_periodLattice_iff_lieExpAddMonoidHom.2 ?_, ?_⟩
    · rw [smul_inv_smul₀ two_pi_pos.ne', ← hexp]
      rw [Additive.mem_toAddSubgroup, MonoidHom.mem_ker] at hg
      simpa using hg
    · rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
        smul_inv_smul₀ two_pi_pos.ne', ← map_neg, ← map_add]
      exact ⟨-s (lieMap (I := I) (I' := I') f X) + X, by simp [hs], rfl⟩

/-- **The index of the period lattice under a homomorphism with surjective Lie map.** Let
`f : G → G'` be a continuous homomorphism of commutative Lie groups, with `G` connected, whose Lie
map `df` is surjective. Then the image `df(Λ_ℤ(G))` of the period lattice of `G` has index
`[ker f : exp(ker df)]` in the period lattice of `G'`, where `exp(ker df)` is the image of the
kernel of `df` under the exponential, a subgroup of `ker f`. -/
theorem relIndex_map_lieMap_periodLattice_of_surjective (f : G →ₜ* G')
    (hf : Function.Surjective (lieMap (I := I) (I' := I') f)) :
    ((periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom).relIndex
        (periodLattice I' G') =
      ((LinearMap.ker (lieMap (I := I) (I' := I') f).toLinearMap).toAddSubgroup.map
        (lieExpAddMonoidHom (I := I) (G := G))).relIndex f.ker.toAddSubgroup := by
  obtain ⟨s, hs⟩ := (lieMap (I := I) (I' := I') f).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hf)
  have hs' (Y : LeftInvariantDerivation I' G') : lieMap (I := I) (I' := I') f (s Y) = Y := by
    simpa using LinearMap.congr_fun hs Y
  -- `φ Y = exp(s(2π Y))` modulo `exp(ker df)`, an additive map because `G` is commutative.
  set K₀ := (LinearMap.ker (lieMap (I := I) (I' := I') f).toLinearMap).toAddSubgroup.map
    (lieExpAddMonoidHom (I := I) (G := G))
  set φ := (QuotientAddGroup.mk' K₀).comp ((lieExpAddMonoidHom (I := I) (G := G)).comp
    (s.comp ((2 * π) • LinearMap.id)).toAddMonoidHom) with hφ
  -- On the period lattice of `G'`, the kernel of `φ` is the image of the period lattice of `G`.
  have hker : (periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom ⊓
      periodLattice I' G' = φ.ker ⊓ periodLattice I' G' := by
    ext Y
    simp only [AddSubgroup.mem_inf, and_congr_left_iff]
    intro _
    simp only [AddMonoidHom.mem_ker, hφ, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    exact (lieExpAddMonoidHom_mem_map_ker_iff f s hs').symm
  rw [← AddSubgroup.inf_relIndex_right, hker, AddSubgroup.inf_relIndex_right,
    AddSubgroup.relIndex_ker, hφ, map_periodLattice_eq_map_ker f s hs',
    ← AddSubgroup.relIndex_ker, QuotientAddGroup.ker_mk']

/-- **The index of the period lattice under an isogeny.** Let `f : G → G'` be a continuous
homomorphism of commutative Lie groups, with `G` connected, whose Lie map `df` is bijective. Then
the image `df(Λ_ℤ(G))` of the period lattice of `G` has index `|ker f|` in the period lattice of
`G'`. In particular it has finite index exactly when `ker f` is finite. -/
theorem relIndex_map_lieMap_periodLattice (f : G →ₜ* G')
    (hf : Function.Bijective (lieMap (I := I) (I' := I') f)) :
    ((periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom).relIndex
        (periodLattice I' G') = Nat.card f.ker := by
  rw [relIndex_map_lieMap_periodLattice_of_surjective f hf.2,
    (LinearMap.ker_eq_bot (f := (lieMap (I := I) (I' := I') f).toLinearMap)).2 hf.1,
    Submodule.bot_toAddSubgroup, AddSubgroup.map_bot, AddSubgroup.relIndex_bot_left]
  exact Nat.card_congr (Additive.toMul.subtypeEquiv fun g ↦ Additive.mem_toAddSubgroup _ g)

end ContinuousMonoidHom
