/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character
public import Mathlib.GroupTheory.Index

/-!
# Period lattices under isogenies

Let `f : G → G'` be a continuous homomorphism of finite-dimensional real Lie groups whose Lie map
`df : 𝔤 → 𝔤'` is a linear isomorphism, for instance a surjective homomorphism with finite kernel
between groups of the same dimension (an *isogeny*). Then `df` carries the period lattice
`Λ_ℤ(G) = (2π)⁻¹ ker(exp)` into `Λ_ℤ(G')` (`ContinuousMonoidHom.lieMap_mem_periodLattice`), but in
general not onto it: for commutative `G` and `G'` with `G` connected, the image has index the order
of the kernel of `f`,

`[Λ_ℤ(G') : df(Λ_ℤ(G))] = |ker f|`

(`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice`). Indeed, `Y ↦ exp(df⁻¹(2π Y))` maps
`Λ_ℤ(G')` onto `ker f`, since every element of the connected group `G` is an exponential, and its
kernel is exactly `df(Λ_ℤ(G))`.

The hypothesis on `df` is met by isogenies: if `ker f` is discrete then `df` is injective
(`ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker` in
`TauCeti.Geometry.Lie.Subgroup.Kernel`). The central isogeny of the torus
of `U(2)` is worked out in `TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Isogeny.UnitaryTorus`.

## Main results

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
  [IsMulCommutative G] [IsMulCommutative G'] [PreconnectedSpace G]

/-- **The index of the period lattice under an isogeny.** Let `f : G → G'` be a continuous
homomorphism of commutative Lie groups, with `G` connected, whose Lie map `df` is bijective. Then
the image `df(Λ_ℤ(G))` of the period lattice of `G` has index `|ker f|` in the period lattice of
`G'`. In particular it has finite index exactly when `ker f` is finite. -/
theorem relIndex_map_lieMap_periodLattice (f : G →ₜ* G')
    (hf : Function.Bijective (lieMap (I := I) (I' := I') f)) :
    ((periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom).relIndex
        (periodLattice I' G') = Nat.card f.ker := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  set e := LinearEquiv.ofBijective (lieMap (I := I) (I' := I') f).toLinearMap hf
  have he (X : LeftInvariantDerivation I G) : e X = lieMap (I := I) (I' := I') f X :=
    LinearEquiv.ofBijective_apply _ _
  -- `ψ Y = exp(df⁻¹(2π Y))`, an additive homomorphism because `G` is commutative.
  let ψ : LeftInvariantDerivation I' G' →+ Additive G :=
    (lieExpAddMonoidHom (I := I) (G := G)).comp
      ((e.symm.toLinearMap.comp ((2 * π) • LinearMap.id)).toAddMonoidHom)
  have hψ (Y : LeftInvariantDerivation I' G') :
      ψ Y = Additive.ofMul (lieExp (I := I) (G := G) (e.symm ((2 * π) • Y))) :=
    lieExpAddMonoidHom_apply _
  -- The kernel of `ψ` is the image of the period lattice of `G`.
  have hkerψ : ψ.ker =
      (periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom := by
    ext Y
    rw [AddMonoidHom.mem_ker, hψ, ofMul_eq_zero, AddSubgroup.mem_map]
    constructor
    · intro hY
      refine ⟨e.symm Y, ?_, by simp [← he]⟩
      rwa [mem_periodLattice, ← map_smul]
    · rintro ⟨X, hX, rfl⟩
      rw [mem_periodLattice] at hX
      simpa [← he, ← map_smul] using hX
  -- The image under `ψ` of the period lattice of `G'` is the kernel of `f`.
  have hmap : (periodLattice I' G').map ψ = f.ker.toAddSubgroup := by
    ext g
    rw [AddSubgroup.mem_map, Additive.mem_toAddSubgroup, MonoidHom.mem_ker,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rw [mem_periodLattice] at hY
      rw [hψ, toMul_ofMul, map_lieExp (I' := I'), ← he, e.apply_symm_apply, hY]
    · intro hg
      obtain ⟨X, hX⟩ := lieExp_surjective_of_preconnectedSpace (I := I) (G := G) (Additive.toMul g)
      refine ⟨(2 * π)⁻¹ • e X, ?_, ?_⟩
      · rw [mem_periodLattice, smul_inv_smul₀ two_pi_pos.ne', he, ← map_lieExp (I' := I'), hX, hg]
      · rw [hψ, smul_inv_smul₀ two_pi_pos.ne', e.symm_apply_apply, hX, ofMul_toMul]
  rw [← hkerψ, AddSubgroup.relIndex_ker, hmap]
  exact Nat.card_congr (Additive.toMul.subtypeEquiv fun g ↦ Additive.mem_toAddSubgroup _ g)

end ContinuousMonoidHom
