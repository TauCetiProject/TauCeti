/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.FanDominance

/-!
# Unitary-orbit estimates for orthogonal block sums

The orthogonal block sum of `A : E₁ →ₗ[𝕜] F₁` and `B : E₂ →ₗ[𝕜] F₂` is Mathlib's
`(A.prodMap B).withLpMap 2`, acting componentwise on the Hilbert `L²` products. No separate
block-sum construction is needed.

Two-sided unitary orbits and their convex hulls are stable under block sums. Consequently,
Ky Fan domination on each block implies domination of the block sum, both for Ky Fan sums
and for every rectangular unitarily invariant seminorm. These estimates combine independent
bounds on orthogonal pieces without increasing their constants.

The orbit and orbit-hull statements require neither finite dimension nor completeness.
Only the consequences using Fan dominance require finite-dimensional spaces.

## Main results

* `LinearMap.prodMap_withLpMap_mem_twoSidedUnitaryOrbitHull`: stability of orbit hulls.
* `LinearMap.kyFanSum_prodMap_withLpMap_le`: blockwise Ky Fan domination.
* `TauCeti.UnitarilyInvariantSeminorm.map_prodMap_withLpMap_le`: the sharp block-sum
  comparison for all unitarily invariant seminorms.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997,
  Section IV.2.
-/

public section

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

namespace LinearMap

/-- Block sums of points in two-sided unitary orbits lie in the orbit of the block sum. -/
theorem prodMap_withLpMap_mem_twoSidedUnitaryOrbit
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : A ∈ C.twoSidedUnitaryOrbit) (hB : B ∈ D.twoSidedUnitaryOrbit) :
    (A.prodMap B).withLpMap 2 ∈ ((C.prodMap D).withLpMap 2).twoSidedUnitaryOrbit := by
  obtain ⟨U, V, rfl⟩ := mem_twoSidedUnitaryOrbit.mp hA
  obtain ⟨U', V', rfl⟩ := mem_twoSidedUnitaryOrbit.mp hB
  refine mem_twoSidedUnitaryOrbit.mpr
    ⟨U.withLpProdCongr 2 U', V.withLpProdCongr 2 V', ?_⟩
  ext x
  simp [LinearIsometryEquiv.withLpProdCongr_apply, WithLp.map, prodMap_apply]

/-- Convex unitary-orbit bounds on two blocks combine into the same bound on their
orthogonal block sum. -/
theorem prodMap_withLpMap_mem_twoSidedUnitaryOrbitHull
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : A ∈ C.twoSidedUnitaryOrbitHull) (hB : B ∈ D.twoSidedUnitaryOrbitHull) :
    (A.prodMap B).withLpMap 2 ∈ ((C.prodMap D).withLpMap 2).twoSidedUnitaryOrbitHull := by
  -- Restrict scalars locally so that Mathlib's convex-hull product theorem applies.
  let := Module.compHom F₁ (algebraMap ℝ 𝕜)
  let := Module.compHom F₂ (algebraMap ℝ 𝕜)
  let : IsScalarTower ℝ 𝕜 F₁ := IsScalarTower.of_compHom ℝ 𝕜 F₁
  let : IsScalarTower ℝ 𝕜 F₂ := IsScalarTower.of_compHom ℝ 𝕜 F₂
  rw [twoSidedUnitaryOrbitHull_eq_convexHull] at hA hB ⊢
  let L := ((LinearEquiv.arrowCongr
    (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).symm
    (WithLp.linearEquiv 2 𝕜 (F₁ × F₂)).symm).toLinearMap.comp
      (prodMapLinear 𝕜 E₁ E₂ F₁ F₂ (S := 𝕜))).restrictScalars ℝ
  have hL (p : (E₁ →ₗ[𝕜] F₁) × (E₂ →ₗ[𝕜] F₂)) :
      L p = (p.1.prodMap p.2).withLpMap 2 := by
    ext x
    simp [L, WithLp.map, prodMap_apply]
  have hmem : L (A, B) ∈
      convexHull ℝ (L '' (C.twoSidedUnitaryOrbit ×ˢ D.twoSidedUnitaryOrbit)) := by
    rw [← L.image_convexHull]
    exact ⟨(A, B), mk_mem_convexHull_prod hA hB, rfl⟩
  rw [hL] at hmem
  refine convexHull_mono (fun Z hZ ↦ ?_) hmem
  obtain ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩ := hZ
  rw [hL]
  exact prodMap_withLpMap_mem_twoSidedUnitaryOrbit hX hY

section FiniteDimensional

variable [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
  [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]

/-- Ky Fan domination on each block implies Ky Fan domination on the orthogonal block sum. -/
theorem kyFanSum_prodMap_withLpMap_le
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : ∀ k, A.kyFanSum k ≤ C.kyFanSum k) (hB : ∀ k, B.kyFanSum k ≤ D.kyFanSum k)
    (k : ℕ) :
    ((A.prodMap B).withLpMap 2).kyFanSum k ≤ ((C.prodMap D).withLpMap 2).kyFanSum k :=
  (mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mp
    (prodMap_withLpMap_mem_twoSidedUnitaryOrbitHull
      (mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr hA)
      (mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr hB))) k

end FiniteDimensional

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

/-- Blockwise Ky Fan estimates give the sharp comparison for every unitarily invariant
seminorm on the orthogonal block sums. -/
theorem map_prodMap_withLpMap_le
    [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
    [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (F₁ × F₂)))
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : ∀ k, A.kyFanSum k ≤ C.kyFanSum k) (hB : ∀ k, B.kyFanSum k ≤ D.kyFanSum k) :
    N ((A.prodMap B).withLpMap 2) ≤ N ((C.prodMap D).withLpMap 2) :=
  N.map_le_of_kyFanSum_le (LinearMap.kyFanSum_prodMap_withLpMap_le hA hB)

end TauCeti.UnitarilyInvariantSeminorm
