/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Geometry.Manifold.Instances.MappingTorus
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Mapping tori of integer iterates

The mapping torus of `φ ^ k` maps naturally to the mapping torus of `φ` by
`[t, x] ↦ [k * t, x]`. The map intertwines the suspension flows with time multiplied by `k`
and covers multiplication by `k` on the base circle. For `k ≠ 0` it is a surjective local
diffeomorphism. Negative iterates reverse time; the zero iterate collapses the time direction.

These comparisons relate periodic trajectories of an iterate to trajectories of the original
diffeomorphism, without choosing a representative for points in either mapping torus.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} (φ : M ≃ₘ^n⟮I, I⟯ M) (k : ℤ)

/-- The natural map from the mapping torus of `φ ^ k` to that of `φ`, multiplying time by `k`.
For nonzero `k` this is a surjective local diffeomorphism. -/
def iterateMap : SmoothMappingTorus (φ ^ k) → SmoothMappingTorus φ :=
  MulAction.orbitRelQuotientLift
    (fun z : Cover (φ ^ k) ↦ mk φ ((k : ℝ) * ((Cover.ofProd (φ ^ k)).symm z).1)
      ((Cover.ofProd (φ ^ k)).symm z).2) fun j z ↦ by
    obtain ⟨⟨t, x⟩, rfl⟩ := (Cover.ofProd (φ ^ k)).surjective z
    simp only [Cover.smul_ofProd, Equiv.symm_apply_apply]
    rw [mul_add, ← Int.cast_mul, mk_add_intCast, ← zpow_mul]
    simp

/-- On representatives, the iterate map multiplies time by `k` and preserves the fiber point. -/
@[simp]
theorem iterateMap_mk (t : ℝ) (x : M) :
    iterateMap φ k (mk (φ ^ k) t x) = mk φ ((k : ℝ) * t) x := by
  simp only [mk_def, iterateMap, MulAction.orbitRelQuotientLift_mk, Equiv.symm_apply_apply]

/-- The defining lift of the iterate map to the real cylinder. -/
theorem iterateMap_comp_uncurry_mk :
    iterateMap φ k ∘ uncurry (mk (φ ^ k)) =
      uncurry (mk φ) ∘ fun p : ℝ × M ↦ ((k : ℝ) * p.1, p.2) :=
  funext fun p ↦ iterateMap_mk φ k p.1 p.2

/-- The iterate map covers multiplication by `k` on the unit-period base circle. -/
@[simp]
theorem proj_iterateMap (y : SmoothMappingTorus (φ ^ k)) :
    proj φ (iterateMap φ k y) = k • proj (φ ^ k) y := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective (φ ^ k) y
  simp only [uncurry_apply_pair, iterateMap_mk, proj_mk]
  simpa only [zsmul_eq_mul] using (AddCircle.coe_zsmul 1 (n := k) (x := t))

/-- The iterate map intertwines the suspension flows with the time rescaling `s ↦ k * s`. -/
@[simp]
theorem iterateMap_flow (s : ℝ) (y : SmoothMappingTorus (φ ^ k)) :
    iterateMap φ k (flow (φ ^ k) s y) = flow φ ((k : ℝ) * s) (iterateMap φ k y) := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective (φ ^ k) y
  simp [mul_add]

/-- For nonzero `k`, every point has a preimage under the iterate map. -/
theorem iterateMap_surjective (hk : k ≠ 0) : Function.Surjective (iterateMap φ k) := by
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  intro y
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ y
  refine ⟨mk (φ ^ k) (t / k) x, ?_⟩
  simp only [iterateMap_mk, mul_div_cancel₀ t hk', uncurry_apply_pair]

/-- The fiber over `[t, x]` consists of the classes
`[(t + j) / k, φ ^ (-j) x]`, for integers `j`. -/
theorem preimage_iterateMap_mk (hk : k ≠ 0) (t : ℝ) (x : M) :
    iterateMap φ k ⁻¹' {mk φ t x} =
      Set.range (fun j : ℤ ↦ mk (φ ^ k) ((t + j) / k) ((φ ^ (-j)) x)) := by
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  ext y
  obtain ⟨⟨s, z⟩, rfl⟩ := uncurry_mk_surjective (φ ^ k) y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range, uncurry_apply_pair]
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := (mk_eq_mk_iff φ).1 ((iterateMap_mk φ k s z).symm.trans h)
    exact ⟨j, by rw [← hj, mul_div_cancel_left₀ s hk']⟩
  · rintro ⟨j, hj⟩
    rw [← hj, iterateMap_mk, mul_div_cancel₀ _ hk']
    exact (mk_eq_mk_iff φ).2 ⟨j, rfl, rfl⟩

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- The iterate map is `C^n`, including for the zero iterate. -/
theorem contMDiff_iterateMap :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) n (iterateMap φ k) := by
  apply ((isLocalDiffeomorph_uncurry_mk (φ ^ k)).contMDiff_comp_iff
    (uncurry_mk_surjective (φ ^ k)) le_rfl).1
  rw [iterateMap_comp_uncurry_mk]
  exact (contMDiff_uncurry_mk φ).comp
    (((contDiff_const.mul contDiff_id : ContDiff ℝ n fun t : ℝ ↦ (k : ℝ) * t).contMDiff.comp
      contMDiff_fst).prodMk contMDiff_snd)

/-- For a nonzero integer iterate, the natural map of mapping tori is a local diffeomorphism.
This uses the explicit inverse time rescaling upstairs, and needs no compactness of `M`. -/
theorem isLocalDiffeomorph_iterateMap (hk : k ≠ 0) :
    IsLocalDiffeomorph (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) n (iterateMap φ k) := by
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  let scale : (ℝ × M) ≃ₘ^n⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod I⟯ (ℝ × M) :=
    { toEquiv := (Equiv.mulLeft₀ (k : ℝ) hk').prodCongr (Equiv.refl M)
      contMDiff_toFun :=
        ((contDiff_const.mul contDiff_id : ContDiff ℝ n fun t : ℝ ↦ (k : ℝ) * t).contMDiff.comp
          contMDiff_fst).prodMk contMDiff_snd
      contMDiff_invFun :=
        ((contDiff_const.mul contDiff_id : ContDiff ℝ n fun t : ℝ ↦ (k : ℝ)⁻¹ * t).contMDiff.comp
          contMDiff_fst).prodMk contMDiff_snd }
  intro y
  obtain ⟨p, rfl⟩ := uncurry_mk_surjective (φ ^ k) y
  have hcomp : IsLocalDiffeomorphAt (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) n
      (iterateMap φ k ∘ uncurry (mk (φ ^ k))) p := by
    rw [iterateMap_comp_uncurry_mk]
    exact (scale.isLocalDiffeomorph p).comp _ _ (isLocalDiffeomorph_uncurry_mk φ (scale p))
  exact hcomp.of_comp_right (isLocalDiffeomorph_uncurry_mk (φ ^ k) p)

end TauCeti.SmoothMappingTorus
