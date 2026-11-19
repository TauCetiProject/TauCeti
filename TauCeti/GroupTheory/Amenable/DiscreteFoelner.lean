/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Average
public import TauCeti.GroupTheory.Amenable.Reiter
public import TauCeti.GroupTheory.Amenable.Sequence
public import TauCeti.Analysis.Normed.Lp.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Amenable discrete groups have Følner sets

Let `G` be a discrete group. We prove that `G` is amenable, in the sense of a left-invariant mean
on `TauCeti.UCB G` (which for discrete `G` consists of all bounded functions), exactly when it has
Følner sets: for every finite `K ⊆ G` and `ε > 0` there is a finite nonempty `F ⊆ G` with
`|gF △ F| < ε · |F|` for all `g ∈ K`.

The implication from Følner sets to amenability is `TauCeti.Amenable.of_hasFoelnerSets`. For the
converse we first establish **Reiter's condition**: for every finite `K ⊆ G` and `ε > 0` there is
a finitely supported probability density `p : G → ℝ` with

```text
∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε.
```

In `ℓ¹(G)` with its left translations `L_g` (`lp.leftTranslation`), this says that there is a
finitely supported probability vector `u ∈ lp.stdSimplex G` with `∑_{g ∈ K} ‖L_g u - u‖ < ε`.

The proof is by Hahn–Banach separation in the finite product `K → ℓ¹(G)`. Since `lp.stdSimplex G`
is the convex hull of the unit vectors `δ_x`, its image under the linear map
`u ↦ (L_g u - u)_{g ∈ K}` is the convex hull of the vectors `(δ_{g x} - δ_x)_{g ∈ K}`. If `0`
were not in the closure of this convex set, a continuous functional `Λ` would separate them, so
that `Λ (δ_{g x} - δ_x)_{g ∈ K} ≥ c > 0` for every `x`. Writing `f_g y = Λ (ι_g δ_y)`, these
functions are bounded by `‖Λ‖`, and the bounded function `x ↦ ∑_{g ∈ K} (f_g (g x) - f_g x)` is
at least `c` everywhere; but a left-invariant mean assigns it the value `0`. Reiter's condition
then yields Følner sets among the superlevel sets of `p`, by
`TauCeti.hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt`.

## Main results

* `TauCeti.Amenable.exists_mem_stdSimplex_sum_norm_leftTranslation_sub_lt`: an amenable discrete
  group satisfies Reiter's condition in `ℓ¹(G)`.
* `TauCeti.Amenable.exists_sum_tsum_abs_sub_lt`: the same condition for densities `p : G → ℝ`.
* `TauCeti.amenable_iff_exists_mem_stdSimplex_sum_norm_leftTranslation_sub_lt`,
  `TauCeti.amenable_iff_exists_sum_tsum_abs_sub_lt`: a discrete group is amenable exactly when it
  satisfies Reiter's condition, in either form.
* `TauCeti.Amenable.hasFoelnerSets`: an amenable discrete group has Følner sets.
* `TauCeti.amenable_iff_hasFoelnerSets`: a discrete group is amenable exactly when it has Følner
  sets.
* `TauCeti.amenable_iff_maxFoelner_neBot`: for any measurable space with measurable singletons, a
  discrete group is amenable exactly when `maxFoelner G Measure.count` is nontrivial.
* `TauCeti.amenable_iff_exists_finset`: the same characterization in terms of finite sets.
* `TauCeti.amenable_iff_exists_seq`: a countable discrete group is amenable exactly when it admits
  a Følner sequence of finite nonempty sets.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.3.1 and
  Theorem G.5.1.
* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
-/

public section

noncomputable section

open Filter Finset Function Topology
open scoped Pointwise symmDiff

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The vector `(L_g u - u)_{g ∈ K}` in the finite product `K → ℓ¹(G)`, as a linear function of
`u ∈ ℓ¹(G)`. -/
private def translateSub (K : Finset G) : lp (fun _ : G ↦ ℝ) 1 →ₗ[ℝ] K → lp (fun _ : G ↦ ℝ) 1 :=
  LinearMap.pi fun g ↦ (lp.leftTranslation 1 ℝ (g : G)).toLinearMap - LinearMap.id

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem translateSub_apply (K : Finset G) (u : lp (fun _ : G ↦ ℝ) 1) (g : K) :
    translateSub K u g = lp.leftTranslation 1 ℝ (g : G) u - u :=
  rfl

/-- For an amenable discrete group, `0` lies in the closure of the image under
`u ↦ (L_g u - u)_{g ∈ K}` of the finitely supported probability vectors. Otherwise a separating
functional `Λ` gives bounded functions `f_g y = Λ (ι_g δ_y)` with
`∑_{g ∈ K} (f_g (g x) - f_g x)` bounded below by a positive constant, contradicting left
invariance of a mean. -/
private theorem zero_mem_closure_image_translateSub_stdSimplex [DiscreteTopology G] [Amenable G]
    (K : Finset G) : 0 ∈ closure (translateSub K '' lp.stdSimplex G) := by
  classical
  rw [← lp.convexHull_range_single_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  by_contra h
  obtain ⟨Λ, u, hΛ0, hΛ⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ _).closure isClosed_closure h
  rw [map_zero] at hΛ0
  set f : K → G → ℝ := fun g y ↦ Λ (Pi.single g (lp.single 1 y 1))
  have hf (g : K) (y : G) : ‖f g y‖ ≤ ‖Λ‖ := by
    simpa [f, Pi.norm_single] using Λ.le_opNorm (Pi.single g (lp.single 1 y 1))
  have hv (x : G) : Λ (translateSub K (lp.single 1 x 1)) = ∑ g : K, (f g (g * x) - f g x) := by
    conv_lhs => rw [← Finset.univ_sum_single (translateSub K (lp.single 1 x 1))]
    simp only [translateSub_apply, lp.leftTranslation_single, smul_eq_mul, Pi.single_sub,
      map_sum, map_sub, sum_sub_distrib, f]
  -- The functions `f g` are bounded, hence lie in `UCB G` since `G` is discrete.
  let F (g : K) : UCB G :=
    ⟨.ofNormedAddCommGroupDiscrete (f g) ‖Λ‖ (hf g), by simp [ucb_eq_top]⟩
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  have h0 : m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) = 0 := by
    simp only [map_sum, map_sub, hm.apply_leftTranslation, sub_self, sum_const_zero]
  -- `map_inv` would turn `UCB.leftTranslation g⁻¹` into `(UCB.leftTranslation g).symm`.
  have hu : u ≤ m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) :=
    m.le_apply_of_forall_le fun x ↦ by
      simpa [hv, F, -map_inv] using (hΛ _ (subset_closure (subset_convexHull ℝ _ ⟨x, rfl⟩))).le
  linarith

/-- **Reiter's condition** in `ℓ¹(G)`. In an amenable discrete group, for every finite `K` and
`ε > 0` there is a finitely supported probability vector `u ∈ ℓ¹(G)` with
`∑_{g ∈ K} ‖L_g u - u‖ < ε`. -/
theorem Amenable.exists_mem_stdSimplex_sum_norm_leftTranslation_sub_lt [DiscreteTopology G]
    [Amenable G] (K : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ lp.stdSimplex G, ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g u - u‖ < ε := by
  obtain ⟨_, ⟨u, hu, rfl⟩, hcε⟩ := Metric.mem_closure_iff.1
    (zero_mem_closure_image_translateSub_stdSimplex K) (ε / (#K + 1)) (by positivity)
  rw [dist_zero_left] at hcε
  refine ⟨u, hu, ?_⟩
  calc ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g u - u‖
      = ∑ g : K, ‖translateSub K u g‖ := (sum_coe_sort K _).symm
    _ ≤ ∑ _g : K, ‖translateSub K u‖ := sum_le_sum fun g _ ↦ norm_le_pi_norm _ g
    _ = #K * ‖translateSub K u‖ := by simp
    _ ≤ #K * (ε / (#K + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A finitely supported probability vector `u ∈ ℓ¹(G)` with `∑_{g ∈ K} ‖L_g u - u‖ < ε` is a
finitely supported probability density with `∑_{g ∈ K} ∑_x |u (g⁻¹ x) - u x| < ε`. -/
private theorem exists_sum_tsum_abs_sub_lt_of_mem_stdSimplex {K : Finset G} {ε : ℝ}
    {u : lp (fun _ : G ↦ ℝ) 1} (hmem : u ∈ lp.stdSimplex G)
    (hu : ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g u - u‖ < ε) :
    ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε := by
  obtain ⟨hu0, hufin, hu1⟩ := lp.mem_stdSimplex_iff.1 hmem
  refine ⟨u, hu0, hufin, hu1, ?_⟩
  simp_rw [lp.norm_leftTranslation_sub_eq_tsum_norm, smul_eq_mul, Real.norm_eq_abs] at hu
  exact hu

/-- **Reiter's condition.** In an amenable discrete group, for every finite `K` and `ε > 0` there
is a finitely supported probability density `p` with `∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem Amenable.exists_sum_tsum_abs_sub_lt [DiscreteTopology G] [Amenable G] (K : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε := by
  obtain ⟨u, hmem, hu⟩ := Amenable.exists_mem_stdSimplex_sum_norm_leftTranslation_sub_lt K hε
  exact exists_sum_tsum_abs_sub_lt_of_mem_stdSimplex hmem hu

/-- A discrete group is amenable exactly when it satisfies **Reiter's condition**: for every
finite `K` and `ε > 0` there is a finitely supported probability density `p` with
`∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem amenable_iff_exists_sum_tsum_abs_sub_lt [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
        ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε :=
  ⟨fun _ K _ hε ↦ Amenable.exists_sum_tsum_abs_sub_lt K hε,
    fun h ↦ .of_hasFoelnerSets (hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt h)⟩

/-- A discrete group is amenable exactly when it satisfies **Reiter's condition** in `ℓ¹(G)`: for
every finite `K` and `ε > 0` there is a finitely supported probability vector `u ∈ ℓ¹(G)` with
`∑_{g ∈ K} ‖L_g u - u‖ < ε`. -/
theorem amenable_iff_exists_mem_stdSimplex_sum_norm_leftTranslation_sub_lt [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ u ∈ lp.stdSimplex G, ∑ g ∈ K, ‖lp.leftTranslation 1 ℝ g u - u‖ < ε := by
  refine ⟨fun _ K _ hε ↦ Amenable.exists_mem_stdSimplex_sum_norm_leftTranslation_sub_lt K hε,
    fun h ↦ amenable_iff_exists_sum_tsum_abs_sub_lt.2 fun K ε hε ↦ ?_⟩
  obtain ⟨u, hmem, hu⟩ := h K ε hε
  exact exists_sum_tsum_abs_sub_lt_of_mem_stdSimplex hmem hu

/-- An amenable discrete group has Følner sets. -/
theorem Amenable.hasFoelnerSets [DiscreteTopology G] [Amenable G] : HasFoelnerSets G :=
  hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt fun K _ hε ↦
    Amenable.exists_sum_tsum_abs_sub_lt K hε

/-- A discrete group is amenable exactly when it has Følner sets. -/
theorem amenable_iff_hasFoelnerSets [DiscreteTopology G] : Amenable G ↔ HasFoelnerSets G :=
  ⟨fun _ ↦ Amenable.hasFoelnerSets, .of_hasFoelnerSets⟩

/-- For any measurable space on `G` with measurable singletons, a discrete group `G` is amenable
exactly when Mathlib's maximal counting-measure Følner filter `maxFoelner G Measure.count` is
nontrivial. -/
theorem amenable_iff_maxFoelner_neBot [DiscreteTopology G] [MeasurableSpace G]
    [MeasurableSingletonClass G] :
    Amenable G ↔ NeBot (maxFoelner G (MeasureTheory.Measure.count : MeasureTheory.Measure G)) :=
  amenable_iff_hasFoelnerSets.trans hasFoelnerSets_iff_maxFoelner_neBot

/-- A discrete group is amenable exactly when for every finite `K ⊆ G` and every `ε > 0` there is
a finite nonempty `F ⊆ G` with `|gF △ F| < ε · |F|` for all `g ∈ K`. -/
theorem amenable_iff_exists_finset [DiscreteTopology G] [DecidableEq G] :
    Amenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  rw [amenable_iff_hasFoelnerSets, hasFoelnerSets_iff]

/-- A countable discrete group is amenable exactly when there is a sequence of finite nonempty
sets whose relative translation boundaries tend to zero for every group element. -/
theorem amenable_iff_exists_seq [DiscreteTopology G] [Countable G] [DecidableEq G] :
    Amenable G ↔ ∃ F : ℕ → Finset G, (∀ n, (F n).Nonempty) ∧
      ∀ g : G, Tendsto (fun n => (#((g • F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) :=
  amenable_iff_hasFoelnerSets.trans hasFoelnerSets_iff_exists_seq

end TauCeti
