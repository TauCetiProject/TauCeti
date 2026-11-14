/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SubgradientImage
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Lipschitz graphs covering convex frontiers and singular sets

For a function on `E × ℝ`, points admitting two continuous subgradients with different vertical
components lie in a countable union of globally Lipschitz graphs over `E`. No convexity or
regularity assumption on the function is needed: the monotonicity of its subdifferential suffices.
The quantitative step separates the vertical components by `b - a > 0` and bounds the norms of the
subgradients by `M`. On such a slice, the height is `2 * M / (b - a)`-Lipschitz; rational
separations, natural norm bounds, and McShane's extension `LipschitzOnWith.extend_real` yield a
countable cover by globally Lipschitz graphs.

On a real inner product space, decomposing along a unit vector `v` and its orthogonal complement
`(ℝ ∙ v)ᗮ` transfers this covering to hyperplane graphs
`{x | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)}`. In finite dimension `n`, each such
Lipschitz graph is closed and has Hausdorff dimension at most `n - 1`.

Combining these directional coverings over an orthonormal basis with a countable Lipschitz-graph
covering of the frontier of any convex set yields two consequences in finite dimensions:

* the frontier of a convex set is covered by countably many Lipschitz hyperplane graphs, hence has
  Hausdorff dimension at most `n - 1`;
* for an extended-real convex function `f : E → EReal`, the points of its effective domain where
  `f` fails to be finite nearby and differentiable are covered by countably many Lipschitz
  hyperplane graphs (boundary points of the effective domain together with interior points admitting
  two distinct subgradients, by Rockafellar's Theorem 25.1).

Consequently, any measure vanishing on Lipschitz hyperplane graphs—in particular any Borel measure
vanishing on measurable sets of Hausdorff codimension at least `1`—sees `f` finite nearby and
differentiable at almost every point of its effective domain.

## Main statements

* `TauCeti.exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne` and
  `TauCeti.exists_lipschitzWith_graphs_cover_subdifferential_inner_ne` — countable Lipschitz-graph
  coverings of points where subgradients differ in a vertical or unit-vector direction;
* `LipschitzWith.dimH_setOf_inner_eq_orthogonalProjectionOnto_le` — a Lipschitz graph over a
  hyperplane in dimension `n` has Hausdorff dimension at most `n - 1`;
* `Convex.exists_lipschitzWith_graphs_cover_frontier` and `Convex.dimH_frontier_le` — countable
  Lipschitz-graph covering and `(n - 1)`-dimensional Hausdorff bound for the frontier of a convex
  set;
* `TauCeti.exists_lipschitzWith_graphs_cover_not_differentiableAt_toReal` and
  `TauCeti.dimH_setOf_ne_top_and_not_differentiableAt_toReal_le` — the same covering and Hausdorff
  dimension bound for the singular set of an extended-real convex function;
* `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs` and
  `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal_of_null_dimH_add_one_le` — almost
  everywhere differentiability of convex potentials for measures null on Lipschitz hyperplane
  graphs or on Borel sets of Hausdorff codimension at least `1`.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Mathematical Journal 29 (1979), 340–348.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003, §2.4.
* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904–924, Definition 3.2 and Proposition 3.5.
-/

public section

open Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E × ℝ → EReal}

/-- Separating the vertical components of bounded subgradients controls differences of heights.
The subgradient at the lower point has vertical component at least `b`, and that at the higher
point has vertical component at most `a`. -/
private theorem sub_mul_le_norm_fst_sub_of_mem_subdifferential
    {x y : E × ℝ} {α β : (E × ℝ) →L[ℝ] ℝ} {a b M : ℝ}
    (hα : α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x)
    (hβ : β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f y)
    (hαM : ‖α‖ ≤ M) (hβM : ‖β‖ ≤ M)
    (hαa : α (0, 1) ≤ a) (hbβ : b ≤ β (0, 1)) (hyx : y.2 ≤ x.2) :
    (b - a) * (x.2 - y.2) ≤ 2 * M * ‖x.1 - y.1‖ := by
  have hmono := apply_le_apply_of_mem_subdifferential
    (topDualPairing ℝ (E × ℝ)).flip hβ hα
  simp only [LinearMap.flip_apply, topDualPairing_apply] at hmono
  have hsplit (ℓ : (E × ℝ) →L[ℝ] ℝ) :
      ℓ (x - y) = ℓ (x.1 - y.1, 0) + (x.2 - y.2) * ℓ (0, 1) := by
    have heq : x - y = (x.1 - y.1, 0) + (x.2 - y.2) • (0, 1) := by ext <;> simp
    rw [heq, map_add, map_smul, smul_eq_mul]
  rw [hsplit α, hsplit β] at hmono
  have hαbound : α (x.1 - y.1, 0) ≤ M * ‖x.1 - y.1‖ := by
    exact (le_abs_self _).trans <| (α.le_opNorm _).trans <| by
      simpa using mul_le_mul_of_nonneg_right hαM (norm_nonneg (x.1 - y.1))
  have hβbound : -(M * ‖x.1 - y.1‖) ≤ β (x.1 - y.1, 0) := by
    have h := (β.le_opNorm (x.1 - y.1, 0)).trans
      (by simpa using mul_le_mul_of_nonneg_right hβM (norm_nonneg (x.1 - y.1)))
    exact (neg_le_neg h).trans (neg_abs_le _)
  have ht : 0 ≤ x.2 - y.2 := sub_nonneg.mpr hyx
  have ha := mul_le_mul_of_nonneg_left hαa ht
  have hb := mul_le_mul_of_nonneg_left hbβ ht
  nlinarith

/-- The symmetric height estimate for two points with separated bounded subgradients. -/
private theorem mul_abs_sub_le_norm_fst_sub_of_mem_subdifferential
    {x y : E × ℝ} {a b M : ℝ}
    (hx : ∃ α β : (E × ℝ) →L[ℝ] ℝ,
      α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      ‖α‖ ≤ M ∧ ‖β‖ ≤ M ∧ α (0, 1) ≤ a ∧ b ≤ β (0, 1))
    (hy : ∃ α β : (E × ℝ) →L[ℝ] ℝ,
      α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f y ∧
      β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f y ∧
      ‖α‖ ≤ M ∧ ‖β‖ ≤ M ∧ α (0, 1) ≤ a ∧ b ≤ β (0, 1)) :
    (b - a) * |x.2 - y.2| ≤ 2 * M * ‖x.1 - y.1‖ := by
  obtain ⟨αx, βx, hαx, hβx, hαxM, hβxM, hαxa, hbβx⟩ := hx
  obtain ⟨αy, βy, hαy, hβy, hαyM, hβyM, hαya, hbβy⟩ := hy
  rcases le_total y.2 x.2 with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact sub_mul_le_norm_fst_sub_of_mem_subdifferential hαx hβy hαxM hβyM hαxa hbβy h
  · simpa only [abs_of_nonpos (sub_nonpos.mpr h), neg_sub, norm_sub_rev y.1 x.1] using
      sub_mul_le_norm_fst_sub_of_mem_subdifferential hαy hβx hαyM hβxM hαya hbβx h

/-- A set on which bounded subgradients have uniformly separated vertical components lies on a
globally Lipschitz graph. The bound is quantitative and does not require a finite-dimensional
base or a convexity assumption on `f`. -/
theorem exists_lipschitzWith_graph_of_subdifferential_separation
    {s : Set (E × ℝ)} {a b : ℝ} (hab : a < b) (M : ℝ≥0)
    (hs : ∀ x ∈ s, ∃ α β : (E × ℝ) →L[ℝ] ℝ,
      α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      ‖α‖ ≤ M ∧ ‖β‖ ≤ M ∧ α (0, 1) ≤ a ∧ b ≤ β (0, 1)) :
    ∃ g : E → ℝ, LipschitzWith (2 * M / NNReal.mk (b - a) (sub_nonneg.mpr hab.le)) g ∧
      ∀ x ∈ s, x.2 = g x.1 := by
  classical
  let K : ℝ≥0 := 2 * M / NNReal.mk (b - a) (sub_nonneg.mpr hab.le)
  have hheight (x : E × ℝ) (hx : x ∈ s) (y : E × ℝ) (hy : y ∈ s) :
      dist x.2 y.2 ≤ K * dist x.1 y.1 := by
    have hbound := mul_abs_sub_le_norm_fst_sub_of_mem_subdifferential (hs x hx) (hs y hy)
    have hK : (K : ℝ) = 2 * M / (b - a) := by
      simp [K]
    rw [hK, Real.dist_eq, dist_eq_norm]
    calc
      |x.2 - y.2| ≤ (2 * M * ‖x.1 - y.1‖) / (b - a) :=
        (le_div_iff₀ (sub_pos.mpr hab)).mpr (by nlinarith)
      _ = 2 * M / (b - a) * ‖x.1 - y.1‖ := by ring
  let g : E → ℝ := fun u => (Function.invFunOn Prod.fst s u).2
  have hg (x : E × ℝ) (hx : x ∈ s) : g x.1 = x.2 := by
    have hex : ∃ y ∈ s, y.1 = x.1 := ⟨x, hx, rfl⟩
    have h := hheight _ (Function.invFunOn_mem hex) x hx
    rw [Function.invFunOn_eq hex, dist_self, mul_zero] at h
    exact dist_le_zero.mp h
  have hgL : LipschitzOnWith K g (Prod.fst '' s) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hg x hx, hg y hy]
    exact hheight x hx y hy
  obtain ⟨G, hG, hGg⟩ := hgL.extend_real
  exact ⟨G, hG, fun x hx => (hg x hx).symm.trans (hGg ⟨x, hx, rfl⟩)⟩

/-- The points with two subgradients having different vertical components are covered by a
countable family of globally Lipschitz graphs. The index records two rational slope cutoffs
and a natural bound for the norms of the subgradients. -/
theorem exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne
    (f : E × ℝ → EReal) :
    ∃ (K : ℚ × ℚ × ℕ → ℝ≥0) (g : (ℚ × ℚ × ℕ) → E → ℝ),
      (∀ i, LipschitzWith (K i) (g i)) ∧
      ∀ (x : E × ℝ) (α β : (E × ℝ) →L[ℝ] ℝ),
        α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x →
        β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x →
        α (0, 1) ≠ β (0, 1) → ∃ i, x.2 = g i x.1 := by
  classical
  let s : (ℚ × ℚ × ℕ) → Set (E × ℝ) := fun i =>
    {x | ∃ α β : (E × ℝ) →L[ℝ] ℝ,
      α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      ‖α‖ ≤ (i.2.2 : ℝ) ∧ ‖β‖ ≤ (i.2.2 : ℝ) ∧
      α (0, 1) ≤ (i.1 : ℝ) ∧ (i.2.1 : ℝ) ≤ β (0, 1)}
  have hex (i : ℚ × ℚ × ℕ) :
      ∃ (K : ℝ≥0) (g : E → ℝ), LipschitzWith K g ∧
        (i.1 < i.2.1 → ∀ x ∈ s i, x.2 = g x.1) := by
    by_cases h : i.1 < i.2.1
    · obtain ⟨g, hg, hs⟩ := exists_lipschitzWith_graph_of_subdifferential_separation
        (f := f) (s := s i) (a := i.1) (b := i.2.1) (by exact_mod_cast h)
        (i.2.2 : ℝ≥0) (by simp [s])
      exact ⟨_, g, hg, fun _ => hs⟩
    · exact ⟨0, 0, LipschitzWith.const 0, fun h' => (h h').elim⟩
  choose K g hg hsg using hex
  refine ⟨K, g, hg, ?_⟩
  have hcover (x : E × ℝ) (α β : (E × ℝ) →L[ℝ] ℝ)
      (hα : α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x)
      (hβ : β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x)
      (hαβ : α (0, 1) < β (0, 1)) : ∃ i, x.2 = g i x.1 := by
    obtain ⟨a, hαa, haβ⟩ := exists_rat_btwn hαβ
    obtain ⟨b, hab, hbβ⟩ := exists_rat_btwn haβ
    obtain ⟨N, hN⟩ := exists_nat_gt (max ‖α‖ ‖β‖)
    have hab' : a < b := by exact_mod_cast hab
    refine ⟨(a, b, N), hsg (a, b, N) hab' x ?_⟩
    exact ⟨α, β, hα, hβ, (le_max_left _ _).trans hN.le,
      (le_max_right _ _).trans hN.le, hαa.le, hbβ.le⟩
  intro x α β hα hβ hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hcover x α β hα hβ h
  · exact hcover x β α hβ hα h

/-- A measure vanishing on every Lipschitz graph sees no ambiguity in the vertical component of
subgradients almost everywhere. No measurability assumption on `f` or finiteness of the measure
is needed. -/
theorem ae_subdifferential_vertical_eq_of_null_lipschitz_graphs
    [MeasurableSpace (E × ℝ)] (f : E × ℝ → EReal) {μ : MeasureTheory.Measure (E × ℝ)}
    (hμ : ∀ (K : ℝ≥0) (g : E → ℝ), LipschitzWith K g → μ {x | x.2 = g x.1} = 0) :
    ∀ᵐ x ∂μ, ∀ α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x,
      ∀ β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x, α (0, 1) = β (0, 1) := by
  obtain ⟨K, g, hg, hcover⟩ := exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne f
  have hnull : μ (⋃ i, {x | x.2 = g i x.1}) = 0 :=
    MeasureTheory.measure_iUnion_null fun i => hμ (K i) (g i) (hg i)
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  intro α hα β hβ
  by_contra hne
  obtain ⟨i, hi⟩ := hcover x α β hα hβ hne
  exact hx (mem_iUnion.mpr ⟨i, hi⟩)

section HyperplaneGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Decomposing a vector along a vector `v` and its orthogonal complement `(ℝ ∙ v)ᗮ`. -/
private theorem orthogonalProjectionOnto_add_inner_div_norm_sq_smul (v x : E) :
    ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x : E) + (⟪v, x⟫ / ‖v‖ ^ 2) • v = x := by
  have h : (ℝ ∙ v).starProjection x = (⟪v, x⟫ / ‖v‖ ^ 2) • v := by
    simpa using Submodule.starProjection_singleton ℝ (v := v) x
  rw [← Submodule.starProjection_apply, ← h, add_comm,
    Submodule.starProjection_add_starProjection_orthogonal]

/-- Decomposing a vector along a unit vector `v` and its orthogonal complement `(ℝ ∙ v)ᗮ`. -/
private theorem orthogonalProjectionOnto_add_inner_smul {v : E} (hv : ‖v‖ = 1) (x : E) :
    ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x : E) + ⟪v, x⟫ • v = x := by
  simpa [hv] using orthogonalProjectionOnto_add_inner_div_norm_sq_smul v x

private theorem orthogonalProjectionOnto_coe_add_smul (v : E) (u : (ℝ ∙ v)ᗮ) (t : ℝ) :
    (ℝ ∙ v)ᗮ.orthogonalProjectionOnto ((u : E) + t • v) = u := by
  rw [map_add, map_smul, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero, add_zero]

private theorem inner_coe_add_div_norm_sq_smul {v : E} (hv : v ≠ 0) (u : (ℝ ∙ v)ᗮ) (t : ℝ) :
    ⟪v, (u : E) + (t / ‖v‖ ^ 2) • v⟫ = t := by
  have hu : ⟪v, (u : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp u.2
  have hvn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  rw [inner_add_right, hu, zero_add, real_inner_smul_right, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ t hvn]

private theorem inner_coe_add_smul {v : E} (hv : ‖v‖ = 1) (u : (ℝ ∙ v)ᗮ) (t : ℝ) :
    ⟪v, (u : E) + t • v⟫ = t := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  simpa [hv] using inner_coe_add_div_norm_sq_smul hv0 u t

/-- The hyperplane graph of `g : (ℝ ∙ v)ᗮ → ℝ` in a nonzero direction `v` is the range of its
graph parametrization `u ↦ u + (g u / ‖v‖ ^ 2) • v`. -/
theorem setOf_inner_eq_orthogonalProjectionOnto_eq_range_of_ne_zero {v : E} (hv : v ≠ 0)
    (g : (ℝ ∙ v)ᗮ → ℝ) :
    {x : E | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} =
      range fun u : (ℝ ∙ v)ᗮ => (u : E) + (g u / ‖v‖ ^ 2) • v := by
  ext x
  refine ⟨fun hx => ⟨(ℝ ∙ v)ᗮ.orthogonalProjectionOnto x, ?_⟩, ?_⟩
  · dsimp only at hx ⊢
    rw [← hx, orthogonalProjectionOnto_add_inner_div_norm_sq_smul]
  · rintro ⟨u, rfl⟩
    simp [orthogonalProjectionOnto_coe_add_smul, inner_coe_add_div_norm_sq_smul hv]

/-- The hyperplane graph of `g : (ℝ ∙ v)ᗮ → ℝ` in the unit direction `v` is the range of its
graph parametrization `u ↦ u + g u • v`. -/
theorem setOf_inner_eq_orthogonalProjectionOnto_eq_range {v : E} (hv : ‖v‖ = 1)
    (g : (ℝ ∙ v)ᗮ → ℝ) :
    {x : E | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} =
      range fun u : (ℝ ∙ v)ᗮ => (u : E) + g u • v := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  simpa [hv] using setOf_inner_eq_orthogonalProjectionOnto_eq_range_of_ne_zero hv0 g

/-- The hyperplane graph of a continuous function over `(ℝ ∙ v)ᗮ` is closed. -/
theorem isClosed_setOf_inner_eq_orthogonalProjectionOnto {v : E} {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : Continuous g) :
    IsClosed {x : E | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} :=
  isClosed_eq (continuous_const.inner continuous_id)
    (hg.comp (ℝ ∙ v)ᗮ.orthogonalProjectionOnto.continuous)

/-- **Hausdorff dimension of a Lipschitz hyperplane graph.** In a finite-dimensional real inner
product space `E`, the graph of a Lipschitz map over `(ℝ ∙ v)ᗮ` for a nonzero vector `v` has
Hausdorff dimension at most `finrank ℝ E - 1`, with `dimH + 1 ≤ finrank ℝ E`. -/
theorem _root_.LipschitzWith.dimH_setOf_inner_eq_orthogonalProjectionOnto_add_one_le
    [FiniteDimensional ℝ E] {v : E} {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : LipschitzWith K g) (hv : v ≠ 0) :
    dimH {x : E | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} + 1 ≤
      Module.finrank ℝ E := by
  have hlip :
      LipschitzWith (1 + K * (‖v‖₊)⁻¹)
        (fun u : (ℝ ∙ v)ᗮ => (u : E) + (g u / ‖v‖ ^ 2) • v) := by
    refine LipschitzWith.of_dist_le_mul fun u₁ u₂ => ?_
    have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    calc dist ((u₁ : E) + (g u₁ / ‖v‖ ^ 2) • v) ((u₂ : E) + (g u₂ / ‖v‖ ^ 2) • v)
        = ‖((u₁ : E) - (u₂ : E)) + ((g u₁ - g u₂) / ‖v‖ ^ 2) • v‖ := by
          rw [dist_eq_norm]
          congr 1
          rw [sub_div]
          module
      _ ≤ ‖(u₁ : E) - (u₂ : E)‖ + |g u₁ - g u₂| * ‖v‖⁻¹ := by
          refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
          rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖v‖), sq,
            div_mul_eq_mul_div, mul_div_mul_right _ _ hv0, div_eq_mul_inv]
      _ ≤ 1 * dist u₁ u₂ + (K : ℝ) * ‖v‖⁻¹ * dist u₁ u₂ := by
          rw [one_mul, ← dist_eq_norm, ← Subtype.dist_eq, mul_right_comm]
          gcongr
          simpa only [Real.dist_eq] using hg.dist_le_mul u₁ u₂
      _ = ↑(1 + K * (‖v‖₊)⁻¹) * dist u₁ u₂ := by
          push_cast
          ring
  have hdim : Module.finrank ℝ (ℝ ∙ v)ᗮ + 1 = Module.finrank ℝ E := by
    simpa only [finrank_span_singleton hv, add_comm] using
      (ℝ ∙ v).finrank_add_finrank_orthogonal
  rw [setOf_inner_eq_orthogonalProjectionOnto_eq_range_of_ne_zero hv g, ← hdim, Nat.cast_add,
    Nat.cast_one]
  gcongr
  exact hlip.dimH_range_le.trans_eq (Real.dimH_univ_eq_finrank _)

/-- In a finite-dimensional real inner product space `E`, the graph of a Lipschitz map over
`(ℝ ∙ v)ᗮ` for a nonzero vector `v` has Hausdorff dimension at most `finrank ℝ E - 1`. -/
theorem _root_.LipschitzWith.dimH_setOf_inner_eq_orthogonalProjectionOnto_le
    [FiniteDimensional ℝ E] {v : E} {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : LipschitzWith K g) (hv : v ≠ 0) :
    dimH {x : E | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} ≤
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
  have hpos : 1 ≤ Module.finrank ℝ E := by
    have := (ℝ ∙ v).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hv] at this
    omega
  have h := hg.dimH_setOf_inner_eq_orthogonalProjectionOnto_add_one_le hv
  have heq : ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) + 1 = Module.finrank ℝ E := by
    exact_mod_cast Nat.sub_add_cancel hpos
  exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp (h.trans_eq heq.symm)

/-- **Points with subgradients separated in a direction lie on countably many Lipschitz graphs.**
For any `f : E → EReal` on a real inner product space `E` and any vector `v : E`, the points `x`
admitting two subgradients with different inner products against `v` are covered by a countable
family of Lipschitz hyperplane graphs orthogonal to `v`. -/
theorem exists_lipschitzWith_graphs_cover_subdifferential_inner_ne
    (f : E → EReal) (v : E) :
    ∃ (K : ℚ × ℚ × ℕ → ℝ≥0) (g : (ℚ × ℚ × ℕ) → (ℝ ∙ v)ᗮ → ℝ),
      (∀ i, LipschitzWith (K i) (g i)) ∧
      ∀ (x y₁ y₂ : E),
        y₁ ∈ subdifferential (innerₗ E) f x →
        y₂ ∈ subdifferential (innerₗ E) f x →
        ⟪v, y₁⟫ ≠ ⟪v, y₂⟫ →
        ∃ i, ⟪v, x⟫ = g i ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x) := by
  by_cases hv : v = 0
  · refine ⟨fun _ => 0, fun _ _ => 0, fun _ => LipschitzWith.const 0, fun _ _ _ _ _ hne => ?_⟩
    simp [hv] at hne
  let H := (ℝ ∙ v)ᗮ
  let Φ : H × ℝ →L[ℝ] E :=
    H.subtypeL.comp (ContinuousLinearMap.fst ℝ H ℝ) +
      (ContinuousLinearMap.snd ℝ H ℝ).smulRight ((‖v‖ ^ 2)⁻¹ • v)
  let Ψ : E →L[ℝ] H × ℝ := H.orthogonalProjectionOnto.prod (innerSL ℝ v)
  have hΦΨ (x : E) : Φ (Ψ x) = x := by
    simpa [Φ, Ψ, H, smul_smul, ← div_eq_mul_inv] using
      orthogonalProjectionOnto_add_inner_div_norm_sq_smul v x
  have hΦ01 : Φ (0, 1) = (‖v‖ ^ 2)⁻¹ • v := by simp [Φ]
  obtain ⟨K, g, hg, hcover⟩ :=
    exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne (fun p : H × ℝ => f (Φ p))
  refine ⟨K, g, hg, fun x y₁ y₂ hy₁ hy₂ hne => ?_⟩
  have hmem (y : E) (hy : y ∈ subdifferential (innerₗ E) f x) :
      (innerSL ℝ y).comp Φ ∈
        subdifferential (topDualPairing ℝ (H × ℝ)).flip (fun p => f (Φ p)) (Ψ x) := by
    rw [mem_subdifferential_iff]
    refine ⟨by simpa only [hΦΨ x] using ne_bot_of_mem_subdifferential (innerₗ E) hy,
      by simpa only [hΦΨ x] using ne_top_of_mem_subdifferential (innerₗ E) hy, fun q => ?_⟩
    have h := add_le_of_mem_subdifferential (innerₗ E) hy (Φ q)
    simpa only [LinearMap.sub_apply, sub_apply, map_sub, LinearMap.flip_apply,
      topDualPairing_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hΦΨ x,
      innerₗ_apply_apply, real_inner_comm y] using h
  have hne' : ((innerSL ℝ y₁).comp Φ) (0, 1) ≠ ((innerSL ℝ y₂).comp Φ) (0, 1) := by
    have hvn : (‖v‖ ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
    simpa only [ContinuousLinearMap.comp_apply, hΦ01, innerSL_apply_apply, real_inner_smul_right,
      ne_eq, mul_eq_mul_left_iff, hvn, or_false, real_inner_comm _ v] using hne
  exact hcover (Ψ x) _ _ (hmem y₁ hy₁) (hmem y₂ hy₂) hne'

end HyperplaneGraph

section ConvexFrontier

/-- Interior-ball cone bound on `frontier s ∩ Metric.ball z (r / 4)`: two frontier points near `z`
cannot separate faster in the radial unit direction `v = ‖x₀ - z‖⁻¹ • (x₀ - z)` than a Lipschitz
multiple of their orthogonal-projection separation. -/
private theorem inner_sub_le_mul_norm_orthogonalProjectionOnto_of_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : Set E} (hs : Convex ℝ s)
    {x₀ z x y : E} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x₀ r ⊆ interior s)
    (hrz : r ≤ ‖x₀ - z‖) (hx : x ∈ frontier s ∩ Metric.ball z (r / 4))
    (hy : y ∈ frontier s ∩ Metric.ball z (r / 4)) :
    let v := ‖x₀ - z‖⁻¹ • (x₀ - z)
    let P := (ℝ ∙ v)ᗮ.orthogonalProjectionOnto
    ⟪v, x⟫ - ⟪v, y⟫ ≤ (4 * ‖x₀ - z‖ / (3 * r)) * ‖P x - P y‖ := by
  intro v P
  set L := ‖x₀ - z‖
  have hL : 0 < L := hr.trans_le hrz
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hL), inv_mul_cancel₀ hL.ne']
  have hLv : L • v = x₀ - z := smul_inv_smul₀ hL.ne' (x₀ - z)
  by_contra! hgt
  set t := ⟪v, x⟫ - ⟪v, y⟫
  have ht0 : 0 < t := (mul_nonneg (by positivity) (norm_nonneg _)).trans_lt hgt
  have htL : t < L := by
    have hxy : ‖x - y‖ < r / 2 := by
      calc ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
        _ ≤ dist x z + dist z y := dist_triangle x z y
        _ < r / 4 + r / 4 := add_lt_add (Metric.mem_ball.1 hx.2)
            (by rw [dist_comm]; exact Metric.mem_ball.1 hy.2)
        _ = r / 2 := by ring
    calc t = ⟪v, x - y⟫ := (inner_sub_right (𝕜 := ℝ) v x y).symm
      _ ≤ ‖v‖ * ‖x - y‖ := real_inner_le_norm v (x - y)
      _ < L := by rw [hv, one_mul]; linarith
  set θ := t / L
  have hθ0 : 0 < θ := div_pos ht0 hL
  have hθ1 : θ < 1 := (div_lt_one hL).2 htL
  set p : E := y + L • v + θ⁻¹ • ((P x : E) - (P y : E))
  have hp : p ∈ interior s := by
    refine hball (Metric.mem_ball.2 ?_)
    have hstep : ‖θ⁻¹ • ((P x : E) - (P y : E))‖ < 3 * r / 4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hθ0), ← Submodule.coe_sub,
        Submodule.norm_coe, show θ⁻¹ = L / t from inv_div t L, div_mul_eq_mul_div, div_lt_iff₀ ht0]
      have hr3 : (0 : ℝ) < 3 * r := by positivity
      have hK' : 4 * L * ‖P x - P y‖ / (3 * r) < t := by
        simpa only [div_mul_eq_mul_div] using hgt
      have := (div_lt_iff₀ hr3).1 hK'
      linarith
    have hyz : ‖y - z‖ < r / 4 := by simpa only [dist_eq_norm] using Metric.mem_ball.1 hy.2
    rw [dist_eq_norm, show p - x₀ = (y - z) + θ⁻¹ • ((P x : E) - (P y : E)) by
      simp only [p, hLv]; abel]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hcomb : (1 - θ) • y + θ • p = x := by
    have hy_dec : y - (P y : E) = ⟪v, y⟫ • v :=
      (eq_sub_of_add_eq' (orthogonalProjectionOnto_add_inner_smul hv y)).symm
    calc (1 - θ) • y + θ • p
        = y + (θ * L) • v + (θ * θ⁻¹) • ((P x : E) - (P y : E)) := by
            simp only [p, smul_add, sub_smul, one_smul, smul_smul]; abel
      _ = (y - (P y : E)) + t • v + (P x : E) := by
            rw [div_mul_cancel₀ t hL.ne', mul_inv_cancel₀ hθ0.ne', one_smul]; abel
      _ = (P x : E) + ⟪v, x⟫ • v := by rw [hy_dec, ← add_smul, add_sub_cancel, add_comm]
      _ = x := orthogonalProjectionOnto_add_inner_smul hv x
  exact hx.1.2 (hcomb ▸ hs.combo_closure_interior_mem_interior hy.1.1 hp
    (sub_nonneg.2 hθ1.le) hθ0 (sub_add_cancel 1 θ))

/-- Near any frontier point `z` of a convex set `s` whose interior contains `Metric.ball x₀ r`,
`frontier s ∩ Metric.ball z (r / 4)` lies on a Lipschitz hyperplane graph orthogonal to
`x₀ - z`. -/
private theorem exists_lipschitzWith_graph_frontier_inter_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : Set E} (hs : Convex ℝ s)
    {x₀ z : E} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x₀ r ⊆ interior s)
    (hz : z ∈ frontier s) :
    ∃ (v : E) (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), ‖v‖ = 1 ∧ LipschitzWith K g ∧
      ∀ x ∈ frontier s ∩ Metric.ball z (r / 4),
        ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x) := by
  classical
  have hrz : r ≤ ‖x₀ - z‖ := by
    by_contra! hlt
    rw [← dist_eq_norm, dist_comm] at hlt
    exact hz.2 (hball hlt)
  have hL : 0 < ‖x₀ - z‖ := hr.trans_le hrz
  set v := ‖x₀ - z‖⁻¹ • (x₀ - z)
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hL), inv_mul_cancel₀ hL.ne']
  let P := (ℝ ∙ v)ᗮ.orthogonalProjectionOnto
  let S := frontier s ∩ Metric.ball z (r / 4)
  let K : ℝ≥0 := ⟨4 * ‖x₀ - z‖ / (3 * r), by positivity⟩
  have hsymm (x y : E) (hx : x ∈ S) (hy : y ∈ S) :
      dist ⟪v, x⟫ ⟪v, y⟫ ≤ K * dist (P x) (P y) := by
    rw [Real.dist_eq, dist_eq_norm]
    rcases le_total ⟪v, y⟫ ⟪v, x⟫ with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact inner_sub_le_mul_norm_orthogonalProjectionOnto_of_frontier hs hr hball hrz hx hy
    · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub, norm_sub_rev]
      exact inner_sub_le_mul_norm_orthogonalProjectionOnto_of_frontier hs hr hball hrz hy hx
  let g₀ : (ℝ ∙ v)ᗮ → ℝ := fun u => ⟪v, Function.invFunOn P S u⟫
  have hg₀ (x : E) (hx : x ∈ S) : g₀ (P x) = ⟪v, x⟫ := by
    have hex : ∃ y ∈ S, P y = P x := ⟨x, hx, rfl⟩
    have h := hsymm _ x (Function.invFunOn_mem hex) hx
    rw [Function.invFunOn_eq hex, dist_self, mul_zero] at h
    exact dist_le_zero.mp h
  have hg₀L : LipschitzOnWith K g₀ (P '' S) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hg₀ x hx, hg₀ y hy]
    exact hsymm x y hx hy
  obtain ⟨g, hg, hgg₀⟩ := hg₀L.extend_real
  exact ⟨v, K, g, hv, hg, fun x hx => (hg₀ x hx).symm.trans (hgg₀ ⟨x, hx, rfl⟩)⟩

/-- If `s` has improper affine span in a finite-dimensional real inner product space, its frontier
is covered by at most one flat hyperplane graph. -/
private theorem exists_lipschitzWith_graphs_cover_frontier_of_affineSpan_ne_top
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hspan : affineSpan ℝ s ≠ ⊤) :
    ∃ (ι : Type) (_ : Countable ι) (v : ι → E) (K : ι → ℝ≥0)
      (g : ∀ i, (ℝ ∙ v i)ᗮ → ℝ),
      (∀ i, ‖v i‖ = 1) ∧ (∀ i, LipschitzWith (K i) (g i)) ∧
      frontier s ⊆ ⋃ i, {x | ⟪v i, x⟫ = g i ((ℝ ∙ v i)ᗮ.orthogonalProjectionOnto x)} := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun i => i.elim,
      fun i => i.elim, fun i => i.elim, ?_⟩
    simp
  have hdir : (affineSpan ℝ s).direction ≠ ⊤ := fun htop =>
    hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x₀, subset_affineSpan ℝ s hx₀⟩).1 htop)
  have horth : (affineSpan ℝ s).directionᗮ ≠ ⊥ := by
    intro hbot
    apply hdir
    rw [← (affineSpan ℝ s).direction.orthogonal_orthogonal, hbot, Submodule.bot_orthogonal_eq_top]
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 horth
  set v := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hw0)),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
  refine ⟨Unit, inferInstance, fun _ => v, fun _ => 0, fun _ _ => ⟪v, x₀⟫,
    fun _ => hv, fun _ => LipschitzWith.const _, fun x hx => mem_iUnion.2 ⟨(), ?_⟩⟩
  have hxA : x ∈ affineSpan ℝ s :=
    (frontier_subset_closure.trans (closure_minimal (subset_affineSpan ℝ s)
      (affineSpan ℝ s).isClosed_of_finiteDimensional)) hx
  have hsub : x - x₀ ∈ (affineSpan ℝ s).direction := by
    simpa only [vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction hxA (subset_affineSpan ℝ s hx₀)
  have h0 : ⟪v, x - x₀⟫ = 0 := by
    rw [real_inner_smul_left, (Submodule.mem_orthogonal' _ _).1 hw _ hsub, mul_zero]
  rw [inner_sub_right (𝕜 := ℝ) v x x₀] at h0
  exact sub_eq_zero.1 h0

/-- **The frontier of a convex set is covered by countably many Lipschitz hyperplane graphs.** -/
theorem _root_.Convex.exists_lipschitzWith_graphs_cover_frontier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) :
    ∃ (ι : Type) (_ : Countable ι) (v : ι → E) (K : ι → ℝ≥0)
      (g : ∀ i, (ℝ ∙ v i)ᗮ → ℝ),
      (∀ i, ‖v i‖ = 1) ∧ (∀ i, LipschitzWith (K i) (g i)) ∧
      frontier s ⊆ ⋃ i, {x | ⟪v i, x⟫ = g i ((ℝ ∙ v i)ᗮ.orthogonalProjectionOnto x)} := by
  rcases ne_or_eq (affineSpan ℝ s) ⊤ with hspan | hspan
  · exact exists_lipschitzWith_graphs_cover_frontier_of_affineSpan_ne_top hspan
  obtain ⟨x₀, hx₀⟩ := hs.interior_nonempty_iff_affineSpan_eq_top.2 hspan
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  choose v K g hv hg hmem using fun z : frontier s =>
    exists_lipschitzWith_graph_frontier_inter_ball hs hr hball z.2
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : frontier s => Metric.ball (z : E) (r / 4)) (fun _ => Metric.isOpen_ball)
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun i => i.elim,
      fun i => i.elim, fun i => i.elim, fun x hx => ?_⟩
    have hxU : x ∈ ⋃ z : frontier s, Metric.ball (z : E) (r / 4) :=
      mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (by positivity)⟩
    rw [← hTU] at hxU
    simp at hxU
  · obtain ⟨e, rfl⟩ := hTc.exists_eq_range hTne
    refine ⟨ℕ, inferInstance, fun n => v (e n), fun n => K (e n), fun n => g (e n),
      fun n => hv (e n), fun n => hg (e n), fun x hx => ?_⟩
    have hxU : x ∈ ⋃ z : frontier s, Metric.ball (z : E) (r / 4) :=
      mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (by positivity)⟩
    rw [← hTU, biUnion_range] at hxU
    obtain ⟨n, hn⟩ := mem_iUnion.1 hxU
    exact mem_iUnion.2 ⟨n, hmem (e n) x ⟨hx, hn⟩⟩

/-- **Hausdorff dimension of the frontier of a convex set.** In a finite-dimensional real normed
space `E`, the frontier of any convex set has Hausdorff dimension at most `finrank ℝ E - 1`. -/
theorem _root_.Convex.dimH_frontier_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) :
    dimH (frontier s) ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  have hfin : Module.finrank ℝ E = Module.finrank ℝ F := (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  let e : E ≃L[ℝ] F := (LinearEquiv.ofFinrankEq E F hfin).toContinuousLinearEquiv
  obtain ⟨ι, _, v, K, g, hv, hg, hcov⟩ :=
    Convex.exists_lipschitzWith_graphs_cover_frontier (hs.linear_image e.toLinearMap)
  have hfr : e '' frontier s = frontier (e.toLinearMap '' s) := e.toHomeomorph.image_frontier s
  rw [← e.dimH_image (frontier s), hfr]
  refine ((dimH_mono hcov).trans ?_).trans_eq
    (congrArg (fun n : ℕ => ((n - 1 : ℕ) : ℝ≥0∞)) hfin.symm)
  rw [dimH_iUnion]
  exact iSup_le fun i =>
    (hg i).dimH_setOf_inner_eq_orthogonalProjectionOnto_le (ne_of_apply_ne norm (by simp [hv i]))

/-- In a nontrivial finite-dimensional real normed space `E`, `dimH (frontier s) + 1 ≤ finrank ℝ E`
for every convex set `s`. -/
theorem _root_.Convex.dimH_frontier_add_one_le_finrank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    {s : Set E} (hs : Convex ℝ s) :
    dimH (frontier s) + 1 ≤ Module.finrank ℝ E := by
  have hpos : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  calc dimH (frontier s) + 1
      ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) + 1 := by gcongr; exact hs.dimH_frontier_le
    _ = Module.finrank ℝ E := by exact_mod_cast Nat.sub_add_cancel hpos

end ConvexFrontier

section ConvexSingularSet

/-- **Countable Lipschitz-graph covering of the singular set of a convex function.** Let
`f : E → EReal` have convex epigraph on a finite-dimensional real inner product space `E`. The
points of the effective domain `{x | f x ≠ ⊤}` where `f` fails to be finite nearby and
differentiable are covered by countably many Lipschitz hyperplane graphs. -/
theorem exists_lipschitzWith_graphs_cover_not_differentiableAt_toReal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) :
    ∃ (ι : Type) (_ : Countable ι) (v : ι → E) (K : ι → ℝ≥0)
      (g : ∀ i, (ℝ ∙ v i)ᗮ → ℝ),
      (∀ i, ‖v i‖ = 1) ∧ (∀ i, LipschitzWith (K i) (g i)) ∧
      {x | f x ≠ ⊤ ∧ ¬((∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧
        DifferentiableAt ℝ (fun x' => (f x').toReal) x)} ⊆
        ⋃ i, {x | ⟪v i, x⟫ = g i ((ℝ ∙ v i)ᗮ.orthogonalProjectionOnto x)} := by
  obtain ⟨ι₁, _, v₁, K₁, g₁, hv₁, hg₁, hcov₁⟩ :=
    (convex_setOf_ne_top hf).exists_lipschitzWith_graphs_cover_frontier
  let b := stdOrthonormalBasis ℝ E
  choose K₂ g₂ hg₂ hcov₂ using fun k : Fin (Module.finrank ℝ E) =>
    exists_lipschitzWith_graphs_cover_subdifferential_inner_ne f (b k)
  let ι := ι₁ ⊕ (Fin (Module.finrank ℝ E) × (ℚ × ℚ × ℕ))
  refine ⟨ι, inferInstance, Sum.elim v₁ (fun p => b p.1),
    Sum.elim K₁ (fun p => K₂ p.1 p.2),
    fun i => match i with | Sum.inl j => g₁ j | Sum.inr p => g₂ p.1 p.2,
    fun i => by cases i with | inl j => exact hv₁ j | inr p => exact b.norm_eq_one p.1,
    fun i => by cases i with | inl j => exact hg₁ j | inr p => exact hg₂ p.1 p.2,
    fun x ⟨hx, hnd⟩ => ?_⟩
  by_cases hxint : x ∈ interior {z | f z ≠ ⊤}
  · have hdom : ∀ᶠ x' in 𝓝 x, f x' ≠ ⊤ := mem_interior_iff_mem_nhds.1 hxint
    have hnd' : ¬DifferentiableAt ℝ (fun x' => (f x').toReal) x := fun hd => hnd ⟨hdom, hd⟩
    rw [differentiableAt_toReal_iff_subsingleton_subdifferential hf hxint,
      Set.Subsingleton] at hnd'
    push Not at hnd'
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hnd'
    have hex : ∃ k, ⟪b k, y₁⟫ ≠ ⟪b k, y₂⟫ := by
      by_contra! hall
      exact hne (b.repr.injective (by ext k; simpa only [b.repr_apply_apply] using hall k))
    obtain ⟨k, hk⟩ := hex
    obtain ⟨m, hm⟩ := hcov₂ k x y₁ y₂ hy₁ hy₂ hk
    exact mem_iUnion.2 ⟨Sum.inr (k, m), hm⟩
  · have hfr : x ∈ frontier {z | f z ≠ ⊤} := ⟨subset_closure hx, hxint⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov₁ hfr)
    exact mem_iUnion.2 ⟨Sum.inl j, hj⟩

/-- **Hausdorff dimension of the singular set of a convex function.** On a finite-dimensional real
normed space `E`, for any `f : E → EReal` with convex epigraph, the set of effective-domain points
where `f` fails to be finite nearby and differentiable has Hausdorff dimension at most
`finrank ℝ E - 1`. -/
theorem dimH_setOf_ne_top_and_not_differentiableAt_toReal_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) :
    dimH {x | f x ≠ ⊤ ∧ ¬((∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧
      DifferentiableAt ℝ (fun x' => (f x').toReal) x)} ≤
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  have hfin : Module.finrank ℝ E = Module.finrank ℝ F := (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  let e : E ≃L[ℝ] F := (LinearEquiv.ofFinrankEq E F hfin).toContinuousLinearEquiv
  let f' : F → EReal := fun y => f (e.symm y)
  have hf' : Convex ℝ {p : F × ℝ | f' p.1 ≤ p.2} :=
    hf.linear_preimage (e.symm.toLinearMap.prodMap LinearMap.id)
  obtain ⟨ι, _, v, K, g, hv, hg, hcov⟩ :=
    exists_lipschitzWith_graphs_cover_not_differentiableAt_toReal hf'
  have hsub : {x | f x ≠ ⊤ ∧ ¬((∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧
      DifferentiableAt ℝ (fun x' => (f x').toReal) x)} ⊆
      e ⁻¹' ⋃ i, {y | ⟪v i, y⟫ = g i ((ℝ ∙ v i)ᗮ.orthogonalProjectionOnto y)} := by
    intro x ⟨hx, hnd⟩
    refine hcov ⟨by simpa [f'] using hx, fun ⟨hdom, hd⟩ => hnd ⟨?_, ?_⟩⟩
    · simpa [f'] using e.continuousAt.eventually hdom
    · convert hd.comp x e.differentiableAt using 1
      ext x'
      simp [f']
  refine ((dimH_mono hsub).trans ?_).trans_eq
    (congrArg (fun n : ℕ => ((n - 1 : ℕ) : ℝ≥0∞)) hfin.symm)
  rw [e.dimH_preimage, dimH_iUnion]
  exact iSup_le fun i =>
    (hg i).dimH_setOf_inner_eq_orthogonalProjectionOnto_le (ne_of_apply_ne norm (by simp [hv i]))

/-- **Almost-everywhere differentiability of convex functions for measures null on Lipschitz
hyperplane graphs.** Let `f : E → EReal` have convex epigraph on a finite-dimensional real inner
product space `E`. If `μ` assigns measure zero to every Lipschitz hyperplane graph, then at
`μ`-almost every point of `{x | f x ≠ ⊤}`, `f` is finite nearby and its real representative is
differentiable. -/
theorem ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] {μ : MeasureTheory.Measure E} {f : E → EReal}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ {x | ⟪v, x⟫ = g ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x)} = 0) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x := by
  obtain ⟨ι, _, v, K, g, hv, hg, hcov⟩ :=
    exists_lipschitzWith_graphs_cover_not_differentiableAt_toReal hf
  have hnull : μ (⋃ i, {x | ⟪v i, x⟫ = g i ((ℝ ∙ v i)ᗮ.orthogonalProjectionOnto x)}) = 0 :=
    MeasureTheory.measure_iUnion_null fun i => hμ (v i) (hv i) (K i) (g i) (hg i)
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
    (MeasureTheory.measure_mono_null hcov hnull)] with x hx hfx
  by_contra hnd
  exact hx ⟨hfx, hnd⟩

/-- **Almost-everywhere differentiability of convex functions for measures null on sets of
Hausdorff codimension at least `1`.** Let `f : E → EReal` have convex epigraph on a
finite-dimensional real normed space `E`. If a Borel measure `μ` assigns measure zero to every
Borel set `A` with `dimH A + 1 ≤ finrank ℝ E`, then at `μ`-almost every point of `{x | f x ≠ ⊤}`,
`f` is finite nearby and its real representative is differentiable. -/
theorem ae_eventually_ne_top_and_differentiableAt_toReal_of_null_dimH_add_one_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E} {f : E → EReal}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hμ : ∀ ⦃A : Set E⦄, MeasurableSet A → dimH A + 1 ≤ Module.finrank ℝ E → μ A = 0) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  have hfin : Module.finrank ℝ E = Module.finrank ℝ F := (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  let e : E ≃L[ℝ] F := (LinearEquiv.ofFinrankEq E F hfin).toContinuousLinearEquiv
  let f' : F → EReal := fun y => f (e.symm y)
  have hf' : Convex ℝ {p : F × ℝ | f' p.1 ≤ p.2} :=
    hf.linear_preimage (e.symm.toLinearMap.prodMap LinearMap.id)
  obtain ⟨ι, _, v, K, g, hv, hg, hcov⟩ :=
    exists_lipschitzWith_graphs_cover_not_differentiableAt_toReal hf'
  have hsub : {x | f x ≠ ⊤ ∧ ¬((∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧
      DifferentiableAt ℝ (fun x' => (f x').toReal) x)} ⊆
      ⋃ i, e ⁻¹' {y | ⟪v i, y⟫ = g i ((ℝ ∙ v i)ᗮ.orthogonalProjectionOnto y)} := by
    intro x ⟨hx, hnd⟩
    rw [← preimage_iUnion]
    refine hcov ⟨by simpa [f'] using hx, fun ⟨hdom, hd⟩ => hnd ⟨?_, ?_⟩⟩
    · simpa [f'] using e.continuousAt.eventually hdom
    · convert hd.comp x e.differentiableAt using 1
      ext x'
      simp [f']
  have hnull :
      μ (⋃ i, e ⁻¹' {y | ⟪v i, y⟫ = g i ((ℝ ∙ v i)ᗮ.orthogonalProjectionOnto y)}) = 0 := by
    refine MeasureTheory.measure_iUnion_null fun i => hμ ?_ ?_
    · exact ((isClosed_setOf_inner_eq_orthogonalProjectionOnto
        (hg i).continuous).preimage e.continuous).measurableSet
    · rw [e.dimH_preimage]
      exact ((hg i).dimH_setOf_inner_eq_orthogonalProjectionOnto_add_one_le
        (ne_of_apply_ne norm (by simp [hv i]))).trans_eq (by rw [← hfin])
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
    (MeasureTheory.measure_mono_null hsub hnull)] with x hx hfx
  by_contra hnd
  exact hx ⟨hfx, hnd⟩

end ConvexSingularSet

end TauCeti
