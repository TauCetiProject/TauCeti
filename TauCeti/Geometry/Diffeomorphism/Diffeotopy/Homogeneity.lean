/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.VectorField.Chart

/-!
# Homogeneity of connected manifolds

For any two points `x` and `y` of a connected open subset `U` of a finite-dimensional
boundaryless manifold `M`, some diffeotopy of `M` which fixes every point outside a compact subset
of `U` carries `x` to `y`.
In particular the diffeomorphisms of a connected manifold isotopic to the identity act
transitively on it. Without connectedness, the orbits of the diffeomorphism group of a
finite-dimensional boundaryless manifold are open and closed.

Near a point `x`, take a bump function `ρ` in a chart around `x` and, for a nearby point `y`, the
vector field `ρ • (y - x)` read in that chart (`TauCeti.bumpChartField`). Extended by zero, it is
a compactly supported vector field on `M` whose flow line through `x` is the straight segment from
`x` to `y` in the chart, so its compactly supported flow diffeotopy moves `x` to `y`. Diffeotopies
compose and invert, and the points reachable in this way from a given point form an open and
closed subset of `U`.

This is the first step in comparing two ball embeddings in a connected manifold (the disc
theorem): it moves the centre of one ball to the centre of the other.

## Main results

* `TauCeti.eventually_exists_diffeotopy_final_apply_eq`: every point near `x` is reached from `x`
  by a diffeotopy fixing everything outside a compact subset of a given neighbourhood of `x`.
* `TauCeti.exists_diffeotopy_final_apply_eq_of_isPreconnected`: a point of a preconnected
  open set `U` is carried to any other point of `U` by a diffeotopy fixing everything outside a
  compact subset of `U`.
* `TauCeti.exists_diffeotopy_final_apply_eq`: a point of a connected manifold is carried to any
  other point by a compactly supported diffeotopy.
* `TauCeti.isClopen_orbit_diffeomorph`: the orbits of the diffeomorphism group are open and
  closed.
* `TauCeti.orbit_diffeomorph_eq_univ`: on a connected manifold, the diffeomorphism group acts
  transitively.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, Homogeneity Lemma; the flow of a cut-off constant vector field is the one used
  there.
-/

public section

noncomputable section

open Set Filter Metric Topology VectorField
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-! ### Homogeneity -/

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] {n : ℕ∞ω}
  [IsManifold I n M] {m : ℕ∞}

/-- Every point near `x` is reached from `x` by a diffeotopy fixing everything outside a compact
subset of a given open neighbourhood `U` of `x`. -/
theorem eventually_exists_diffeotopy_final_apply_eq (hm : 1 ≤ m)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, ∃ (Φ : Diffeotopy I m M) (K : Set M), IsCompact K ∧ K ⊆ U ∧
      (∀ t, EqOn (fun z ↦ Φ (t, z)) id Kᶜ) ∧ Φ.final x = y := by
  have : IsManifold I m M := .of_le (le_self_add.trans hmn)
  have : IsManifold I 1 M := .of_le ((by exact_mod_cast hm : (1 : ℕ∞ω) ≤ m).trans
    (le_self_add.trans hmn))
  set e := extChartAt I x with he
  -- A bump function `ρ` around `e x`, supported in the chart target and in the image of `U`.
  obtain ⟨ρ, hρt, hρU⟩ := exists_contDiffBump_extChartAt_subset (I := I) hU hx
  filter_upwards [extChartAt_source_mem_nhds (I := I) x,
    (continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds (e x) (half_pos ρ.rIn_pos))]
    with y hys hyr
  -- The vector field `ρ • d` in the chart, with `ρ = 1` on the inner ball of `ρ`.
  set d : E := e y - e x with hd
  have hdr : ‖d‖ < ρ.rIn / 2 := by rwa [mem_preimage, mem_ball, dist_eq_norm] at hyr
  have hv := contMDiff_bumpChartField d hmn hρt
  have hL := isCompact_extChartAt_symm_image_closedBall hρt
  refine ⟨compactlySupportedFlowDiffeotopy hm hv hL (fun z hz ↦ bumpChartField_eq_zero d hz) 1,
    _, hL, hρU, compactlySupportedFlowDiffeotopy_eqOn_compl hm hv hL _ 1, ?_⟩
  -- The segment `s ↦ e.symm (e x + s • d)` is the flow line of `x`.
  have hseg : ∀ s ∈ Ioo (-2 : ℝ) 2, e x + s • d ∈ ball (e x) ρ.rIn := fun s hs ↦ by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hs' : |s| < 2 := abs_lt.2 hs
    nlinarith [abs_nonneg s, norm_nonneg d, ρ.rIn_pos]
  have h1 := (isMIntegralCurveOn_bumpChartField d hρt hseg).eqOn_maximalIntegralCurve (x := x)
    (hv.of_le (by exact_mod_cast hm)) (by norm_num) (by simp [he])
    (by norm_num : (1 : ℝ) ∈ Ioo (-2) 2)
  rw [Diffeotopy.final_apply, compactlySupportedFlowDiffeotopy_apply]
  dsimp only
  rw [Set.Icc.coe_one, one_mul, h1]
  simp only [one_smul, hd, add_sub_cancel]
  exact e.left_inv hys

/-- **Homogeneity lemma.** For two points `x` and `y` of a preconnected open subset `U` of a
finite-dimensional boundaryless manifold, some diffeotopy fixing everything outside a compact
subset of `U` has final map sending `x` to `y`. For a `C^n` manifold the diffeotopy is `C^m`
for every `m` with `1 ≤ m` and `m + 1 ≤ n`; in particular it is smooth on a smooth manifold. -/
theorem exists_diffeotopy_final_apply_eq_of_isPreconnected (hm : 1 ≤ m)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) {x y : M}
    (hx : x ∈ U) (hy : y ∈ U) :
    ∃ (Φ : Diffeotopy I m M) (K : Set M), IsCompact K ∧ K ⊆ U ∧
      (∀ t, EqOn (fun z ↦ Φ (t, z)) id Kᶜ) ∧ Φ.final x = y := by
  refine hUc.induction₂ _ (fun a ha ↦ nhdsWithin_le_nhds
    (eventually_exists_diffeotopy_final_apply_eq hm hmn hU ha)) ?_ ?_ hx hy
  · rintro a b c - - - ⟨Φ, K, hK, hKU, hΦK, hab⟩ ⟨Ψ, L, hL, hLU, hΨL, hbc⟩
    refine ⟨Φ.trans Ψ, K ∪ L, hK.union hL, union_subset hKU hLU, fun t z hz ↦ ?_, ?_⟩
    · rw [compl_union] at hz
      simp [hΦK t hz.1, hΨL t hz.2]
    · simp [hab, hbc]
  · rintro a b - - ⟨Φ, K, hK, hKU, hΦK, hab⟩
    refine ⟨Φ.symm, K, hK, hKU, fun t z hz ↦ Φ.symm_apply_eq_self_iff.2 (hΦK t hz), ?_⟩
    rw [Diffeotopy.final_symm, ← hab, Diffeomorph.symm_apply_apply]

/-- **Homogeneity lemma.** For two points `x` and `y` of a connected finite-dimensional
boundaryless manifold, some compactly supported diffeotopy has final map sending `x` to `y`.
For a `C^n` manifold the diffeotopy is `C^m` for every `m` with `1 ≤ m` and `m + 1 ≤ n`. -/
theorem exists_diffeotopy_final_apply_eq [PreconnectedSpace M] (hm : 1 ≤ m)
    (hmn : (m : ℕ∞ω) + 1 ≤ n) (x y : M) :
    ∃ (Φ : Diffeotopy I m M) (K : Set M), IsCompact K ∧
      (∀ t, EqOn (fun z ↦ Φ (t, z)) id Kᶜ) ∧ Φ.final x = y := by
  obtain ⟨Φ, K, hK, -, hΦK, hxy⟩ :=
    exists_diffeotopy_final_apply_eq_of_isPreconnected (I := I) hm hmn isOpen_univ
      isPreconnected_univ (mem_univ x) (mem_univ y)
  exact ⟨Φ, K, hK, hΦK, hxy⟩

/-! ### Orbits of the diffeomorphism group -/

open MulAction

/-- The orbits of the diffeomorphism group of a finite-dimensional boundaryless manifold are
open. -/
theorem isOpen_orbit_diffeomorph (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n) (x₀ : M) :
    IsOpen (orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) := by
  refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
  obtain ⟨g, rfl⟩ := hy
  filter_upwards [eventually_exists_diffeotopy_final_apply_eq (I := I) hm hmn isOpen_univ
    (mem_univ (g • x₀))] with z hz
  obtain ⟨Φ, -, -, -, -, hz⟩ := hz
  refine ⟨Φ.final * g, ?_⟩
  dsimp only
  rw [mul_smul, Diffeomorph.smul_def, hz]

/-- The orbits of the diffeomorphism group of a finite-dimensional boundaryless manifold are open
and closed. -/
theorem isClopen_orbit_diffeomorph (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n) (x₀ : M) :
    IsClopen (orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) := by
  refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun z hz ↦ ?_),
    isOpen_orbit_diffeomorph hm hmn x₀⟩
  refine mem_of_superset ((isOpen_orbit_diffeomorph (I := I) hm hmn z).mem_nhds (mem_orbit_self z))
    fun w hw hw₀ ↦ hz ?_
  rw [← (orbit_eq_iff.2 hw).symm.trans (orbit_eq_iff.2 hw₀)]
  exact mem_orbit_self z

/-- **Transitivity.** The diffeomorphism group of a connected finite-dimensional boundaryless
manifold acts transitively. -/
theorem orbit_diffeomorph_eq_univ [PreconnectedSpace M] (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    (x₀ : M) : orbit (M ≃ₘ^m⟮I, I⟯ M) x₀ = univ :=
  (isClopen_orbit_diffeomorph (I := I) hm hmn x₀).eq_univ ⟨x₀, mem_orbit_self x₀⟩

end TauCeti
