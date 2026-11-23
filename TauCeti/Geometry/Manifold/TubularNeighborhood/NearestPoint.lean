/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
public import TauCeti.Geometry.Manifold.TubularNeighborhood.LocalInverse
import TauCeti.Geometry.Manifold.Immersion.ShapeOperator
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Topology.MetricSpace.HausdorffDistance

/-!
# Nearest points in a Euclidean tubular neighbourhood

Let `f : M → V` be a `C¹` map from a boundaryless manifold into a real inner product space. If
`f x` is, locally in `x`, a nearest point of `f` to `q`, then the displacement `q - f x` is normal
to `f` at `x` (`TauCeti.sub_mem_normalSubspace_of_isLocalMin`): the derivative of the squared
distance `y ↦ ‖f y - q‖²` at `x` is `u ↦ 2 ⟪f x - q, df_x u⟫`, and it vanishes at a local minimum.

This first variation formula compares the length of a normal vector with the distance to the
image. Suppose that normal addition `(x, v) ↦ f x + v` is injective on the normal vectors of
length less than `ε`, as it is for a compact embedded submanifold and small `ε` by the tubular
neighbourhood theorem `TauCeti.exists_isOpenEmbedding_normalTube`. A nearest point `f y` to
`q = f x + v`, with `v` normal at `x` and `‖v‖ < ε`, satisfies `‖q - f y‖ ≤ ‖v‖ < ε`, so
`q - f y` is also a normal vector of length less than `ε`, at `y`
(`TauCeti.mk_sub_mem_normalTube_of_isLocalMin`), and injectivity forces `y = x`. Hence, for a
compact `M`:

* `f x` is the unique nearest point of `f` to `f x + v`
  (`TauCeti.isMinOn_dist_add_iff_of_mem_normalTube`), and the length of `v` is the distance from
  `f x + v` to the image, `infDist (f x + v) (range f) = ‖v‖`
  (`TauCeti.infDist_add_eq_norm_of_mem_normalTube`);
* the tube is the metric neighbourhood of radius `ε` of the image
  (`TauCeti.image_normalTube_eq_thickening`); the inclusion of that neighbourhood in the tube
  holds without any injectivity (`TauCeti.thickening_range_subset_image_normalTube`);
* sending a point of the neighbourhood to its nearest point of `M` is a retraction, continuous on
  the neighbourhood since its graph is closed
  (`TauCeti.exists_continuousOn_nearestPoint_retraction`);
* when `f` is a `C^(n + 1)` immersion, `n ≥ 1`, this retraction is `C^n` on a smaller
  neighbourhood of the image, where it agrees with the local normal retractions
  `TauCeti.exists_contMDiffOn_normalRetraction`
  (`TauCeti.exists_contMDiffOn_nearestPoint_retraction`).

For a compact embedded submanifold the tubular neighbourhood theorem supplies the injectivity:
`TauCeti.exists_isOpenEmbedding_normalTube` gives a radius `ε > 0` for which normal addition is an
open embedding of the tube, so the results above apply to it, and there is a neighbourhood of the
image on which the nearest-point retraction is unique and `C^n`
(`TauCeti.exists_contMDiffOn_nearestPoint_retraction_of_injective`). These comparisons between the
length of normal vectors and the distance to the submanifold are what places a map whose boundary
lies near a submanifold into its tube, and the retraction projects such boundary values back onto
the submanifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Theorem 6.24.
* H. Federer, *Curvature measures*, Trans. Amer. Math. Soc. **93** (1959), §4 (nearest points
  and the normal cone of a set of positive reach).
-/

public section

open Set Function Filter Topology Metric
open scoped Manifold InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  {f : M → V}

/-- **First variation of the distance.** If `f x` is, locally in `x`, a nearest point of `f` to
`q`, then the displacement `q - f x` is normal to `f` at `x`. -/
theorem sub_mem_normalSubspace_of_isLocalMin {x : M} {q : V}
    (hf : MDifferentiableAt I 𝓘(ℝ, V) f x) (h : IsLocalMin (fun y => dist q (f y)) x) :
    q - f x ∈ normalSubspace I f x := by
  -- The squared distance `y ↦ ‖f y - q‖ ^ 2` also has a local minimum at `x`.
  have hsq : IsLocalMin (fun y => ‖f y - q‖ ^ 2) x := by
    filter_upwards [h] with y hy
    rw [dist_comm q, dist_comm q, dist_eq_norm, dist_eq_norm] at hy
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  -- So `x` is a critical point of it, which says that `f x - q` is normal at `x`.
  rw [← neg_sub]
  exact neg_mem ((mem_criticalPoints_norm_sq_sub_comp_iff (a := q) hf).mp
    (hsq.mem_criticalPoints (I := I)))

section Tube

variable {ε : ℝ}

/-- If `f y` is, locally in `y`, a nearest point of `f` to `q`, at distance less than `ε`, then the
displacement `q - f y` is a normal vector at `y` of length less than `ε`. -/
theorem mk_sub_mem_normalTube_of_isLocalMin {q : V} {y : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, V) f y) (hy : IsLocalMin (fun z => dist q (f z)) y)
    (h : dist q (f y) < ε) : (y, q - f y) ∈ normalTube I f ε :=
  mem_normalTube.mpr ⟨sub_mem_normalSubspace_of_isLocalMin hf hy, by rwa [← dist_eq_norm]⟩

/-- If normal addition is injective on the normal vectors of length less than `ε`, then every
nearest point of `f` to the endpoint `f x + v` of such a normal vector `v` at `x` is the base
point `x`. -/
theorem eq_fst_of_isMinOn_dist_of_mem_normalTube (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {p : M × V}
    (hp : p ∈ normalTube I f ε) {y : M}
    (hy : IsMinOn (fun z => dist (f p.1 + p.2) (f z)) univ y) : y = p.1 := by
  set q := f p.1 + p.2
  have hlt : dist q (f y) < ε :=
    calc dist q (f y) ≤ dist q (f p.1) := hy (mem_univ p.1)
      _ = ‖p.2‖ := by simp [q, dist_eq_norm]
      _ < ε := (mem_normalTube.mp hp).2
  exact congrArg Prod.fst
    (hinj (mk_sub_mem_normalTube_of_isLocalMin (hf y) (hy.isLocalMin univ_mem) hlt) hp
      (by simp [q]))

variable [CompactSpace M]

/-- If normal addition is injective on the normal vectors of length less than `ε`, the length of
such a normal vector `v` at `x` is at most the distance from `f x + v` to any point of the
image. -/
theorem norm_le_dist_add_of_mem_normalTube (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {p : M × V}
    (hp : p ∈ normalTube I f ε) (z : M) : ‖p.2‖ ≤ dist (f p.1 + p.2) (f z) := by
  have : Nonempty M := ⟨p.1⟩
  obtain ⟨y, hy⟩ := hf.continuous.exists_isMinOn_dist (f p.1 + p.2)
  obtain rfl := eq_fst_of_isMinOn_dist_of_mem_normalTube hf hinj hp hy
  simpa [dist_eq_norm] using hy (mem_univ z)

/-- If normal addition is injective on the normal vectors of length less than `ε`, the length of
such a normal vector `v` at `x` is the distance from `f x + v` to the image of `f`. -/
theorem infDist_add_eq_norm_of_mem_normalTube (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {p : M × V}
    (hp : p ∈ normalTube I f ε) : infDist (f p.1 + p.2) (range f) = ‖p.2‖ := by
  refine le_antisymm ?_ ((le_infDist (range_nonempty_iff_nonempty.mpr ⟨p.1⟩)).mpr ?_)
  · simpa [dist_eq_norm] using
      infDist_le_dist_of_mem (x := f p.1 + p.2) (mem_range_self (f := f) p.1)
  · rintro _ ⟨z, rfl⟩
    exact norm_le_dist_add_of_mem_normalTube hf hinj hp z

/-- If normal addition is injective on the normal vectors of length less than `ε`, the base point
`x` of such a normal vector `v` is a nearest point of `f` to `f x + v`, and the only one. -/
theorem isMinOn_dist_add_iff_of_mem_normalTube (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {p : M × V}
    (hp : p ∈ normalTube I f ε) {z : M} :
    IsMinOn (fun w => dist (f p.1 + p.2) (f w)) univ z ↔ z = p.1 := by
  refine ⟨eq_fst_of_isMinOn_dist_of_mem_normalTube hf hinj hp, ?_⟩
  rintro rfl w -
  simpa [dist_eq_norm] using norm_le_dist_add_of_mem_normalTube hf hinj hp w

/-- Every point at distance less than `ε` from the image of `f` is the endpoint `f x + v` of a
normal vector `v` at `x` of length less than `ε`: take for `f x` a nearest point. No injectivity of
normal addition is needed. -/
theorem thickening_range_subset_image_normalTube (hf : MDifferentiable I 𝓘(ℝ, V) f) :
    thickening ε (range f) ⊆ (fun p : M × V => f p.1 + p.2) '' normalTube I f ε := by
  intro q hq
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := mem_thickening_iff.mp hq
  have : Nonempty M := ⟨z⟩
  obtain ⟨y, hy⟩ := hf.continuous.exists_isMinOn_dist q
  exact ⟨(y, q - f y), mk_sub_mem_normalTube_of_isLocalMin (hf y) (hy.isLocalMin univ_mem)
    ((hy (mem_univ z)).trans_lt hz), by simp⟩

/-- If normal addition is injective on the normal vectors of length less than `ε`, it maps them
onto the `ε`-neighbourhood of the image of `f`. -/
theorem image_normalTube_eq_thickening (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) :
    (fun p : M × V => f p.1 + p.2) '' normalTube I f ε = thickening ε (range f) := by
  refine (Subset.antisymm ?_ (thickening_range_subset_image_normalTube hf))
  rintro _ ⟨p, hp, rfl⟩
  rw [mem_thickening_iff_infDist_lt (range_nonempty_iff_nonempty.mpr ⟨p.1⟩),
    infDist_add_eq_norm_of_mem_normalTube hf hinj hp]
  exact (mem_normalTube.mp hp).2

/-- **The nearest-point retraction.** If normal addition is injective on the normal vectors of
length less than `ε > 0`, there is a retraction `r` of `V` onto `M`, continuous on the
`ε`-neighbourhood of the image of `f`, which sends each `q ∈ V` to a nearest point of `f`. On
that neighbourhood the nearest point is unique. By `TauCeti.sub_mem_normalSubspace_of_isLocalMin`,
the displacement `q - f (r q)` is then normal at `r q`. -/
theorem exists_continuousOn_nearestPoint_retraction [Nonempty M]
    (hf : MDifferentiable I 𝓘(ℝ, V) f) (hε : 0 < ε)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) :
    ∃ r : V → M, ContinuousOn r (thickening ε (range f)) ∧ (∀ x, r (f x) = x) ∧
      (∀ q, IsMinOn (fun z => dist q (f z)) univ (r q)) ∧ ∀ q ∈ thickening ε (range f), ∀ z,
        IsMinOn (fun w => dist q (f w)) univ z ↔ z = r q := by
  choose r hr using hf.continuous.exists_isMinOn_dist
  -- On the neighbourhood, every point is the endpoint of a short normal vector, whose base point
  -- is its unique nearest point.
  have hmin : ∀ q ∈ thickening ε (range f), ∀ z,
      IsMinOn (fun w => dist q (f w)) univ z ↔ z = r q := by
    intro q hq z
    obtain ⟨p, hp, rfl⟩ := thickening_range_subset_image_normalTube hf hq
    rw [isMinOn_dist_add_iff_of_mem_normalTube hf hinj hp,
      (isMinOn_dist_add_iff_of_mem_normalTube hf hinj hp).mp (hr _)]
  refine ⟨r, ?_, fun x => ?_, hr, hmin⟩
  · -- The graph of `r` on the neighbourhood is the closed set of pairs `(q, z)` for which `f z`
    -- is a nearest point to `q`, and `M` is compact.
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_of_isClosed_graph ?_
    have hgraph : ((thickening ε (range f)).domRestrict r).graph =
        ⋂ w, {p : thickening ε (range f) × M | dist p.1.val (f p.2) ≤ dist p.1.val (f w)} := by
      ext ⟨⟨q, hq⟩, z⟩
      simp [Function.mem_graph, eq_comm (a := r q), ← hmin q hq z, isMinOn_iff]
    rw [hgraph]
    exact isClosed_iInter fun w => isClosed_le
      ((continuous_subtypeVal.comp continuous_fst).dist (hf.continuous.comp continuous_snd))
      ((continuous_subtypeVal.comp continuous_fst).dist continuous_const)
  · exact ((hmin (f x) (self_subset_thickening hε _ (mem_range_self x)) x).mp
      fun w _ => by simp).symm

/-- **The nearest-point retraction is smooth.** Let `f` be a `C^(n + 1)` immersion of a compact
manifold, `n ≥ 1`, for which normal addition is injective on the normal vectors of length less
than `ε > 0`. Then there is a retraction `r` of `V` onto `M` sending each `q ∈ V` to a nearest
point of `f`, which is `C^n` on the `δ`-neighbourhood of the image for some `0 < δ ≤ ε`. On the
`ε`-neighbourhood the nearest point is unique. -/
theorem exists_contMDiffOn_nearestPoint_retraction [Nonempty M] [FiniteDimensional ℝ V]
    {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f) (hn : 1 ≤ n)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hε : 0 < ε)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) :
    ∃ δ > 0, δ ≤ ε ∧ ∃ r : V → M, ContMDiffOn 𝓘(ℝ, V) I n r (thickening δ (range f)) ∧
      (∀ x, r (f x) = x) ∧ (∀ q, IsMinOn (fun z => dist q (f z)) univ (r q)) ∧
      ∀ q ∈ thickening ε (range f), ∀ z, IsMinOn (fun w => dist q (f w)) univ z → z = r q := by
  obtain ⟨x₁⟩ := ‹Nonempty M›
  have : FiniteDimensional ℝ E := finiteDimensional_of_injective_mfderiv (himm x₁)
  have hd : MDifferentiable I 𝓘(ℝ, V) f := hf.mdifferentiable (by simp)
  obtain ⟨r, -, hrf, hr, hmin⟩ := exists_continuousOn_nearestPoint_retraction hd hε hinj
  -- A nearest point to the endpoint of a short normal vector is its base point.
  have hbase : ∀ q (p : M × V), p ∈ normalTube I f ε → f p.1 + p.2 = q → r q = p.1 :=
    fun q p hp hpq =>
      eq_fst_of_isMinOn_dist_of_mem_normalTube hd hinj hp (by rw [hpq]; exact hr q)
  -- Near each point of the image, `r` is a local `C^n` normal retraction.
  have hloc : ∀ x₀ : M, ∃ t : Set V, IsOpen t ∧ f x₀ ∈ t ∧ ContMDiffOn 𝓘(ℝ, V) I n r t := by
    intro x₀
    obtain ⟨U, -, hx₀U, t, ht, hx₀t, -, ρ, hρ, hρf, hρn⟩ :=
      exists_contMDiffOn_normalRetraction hf x₀ (himm x₀) hn
    have hc : ContinuousOn (fun q => ‖q - f (ρ q)‖) t :=
      (continuousOn_id.sub (hf.continuous.comp_continuousOn hρ.continuousOn)).norm
    refine ⟨t ∩ (fun q => ‖q - f (ρ q)‖) ⁻¹' Iio ε, hc.isOpen_inter_preimage ht isOpen_Iio,
      ⟨hx₀t, by simpa [hρf x₀ hx₀U] using hε⟩, (hρ.mono inter_subset_left).congr ?_⟩
    rintro q ⟨hqt, hqε⟩
    exact hbase q (ρ q, q - f (ρ q)) (mem_normalTube.mpr ⟨(hρn q hqt).2, hqε⟩) (by simp)
  choose t ht hft hrt using hloc
  have hW := ContMDiffOn.iUnion_of_isOpen hrt ht
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_range hf.continuous).exists_thickening_subset_open
    (isOpen_iUnion ht) (range_subset_iff.mpr fun x => mem_iUnion.mpr ⟨x, hft x⟩)
  exact ⟨min δ ε, lt_min hδ hε, min_le_right _ _, r,
    hW.mono ((thickening_mono (min_le_left _ _) _).trans hδW), hrf, hr,
    fun q hq z => (hmin q hq z).mp⟩

end Tube

section Embedding

variable [FiniteDimensional ℝ V] [CompactSpace M]

/-- **The smooth nearest-point retraction onto a compact submanifold.** For a compact `C^(n + 1)`
embedded submanifold of a finite-dimensional inner product space, `n ≥ 1`, there is a retraction
`r` of `V` onto `M` sending each `q ∈ V` to a nearest point of `f`, which is `C^n` on the
`δ`-neighbourhood of the image for some `δ > 0`. On that neighbourhood the nearest point is
unique. By `TauCeti.sub_mem_normalSubspace_of_isLocalMin`, the displacement `q - f (r q)` is then
normal at `r q`. -/
theorem exists_contMDiffOn_nearestPoint_retraction_of_injective [Nonempty M] {n : WithTop ℕ∞}
    [IsManifold I (n + 1) M] (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f) (hn : 1 ≤ n)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hinj : Injective f) :
    ∃ δ > 0, ∃ r : V → M, ContMDiffOn 𝓘(ℝ, V) I n r (thickening δ (range f)) ∧
      (∀ x, r (f x) = x) ∧ (∀ q, IsMinOn (fun z => dist q (f z)) univ (r q)) ∧
      ∀ q ∈ thickening δ (range f), ∀ z, IsMinOn (fun w => dist q (f w)) univ z → z = r q := by
  have h2 : (2 : WithTop ℕ∞) ≤ n + 1 := by
    simpa [one_add_one_eq_two] using add_le_add_left hn 1
  have : IsManifold I 2 M := .of_le h2
  obtain ⟨ε, hε, hemb⟩ := exists_isOpenEmbedding_normalTube (hf.of_le h2) himm hinj
  obtain ⟨δ, hδ, hδε, r, hr, hrf, hmin, huniq⟩ :=
    exists_contMDiffOn_nearestPoint_retraction hf hn himm hε
      (injOn_iff_injective.mpr hemb.injective)
  exact ⟨δ, hδ, r, hr, hrf, hmin, fun q hq => huniq q (thickening_mono hδε _ hq)⟩

end Embedding

end TauCeti
