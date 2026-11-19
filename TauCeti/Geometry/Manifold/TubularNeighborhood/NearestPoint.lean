/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
public import TauCeti.Geometry.Manifold.TubularNeighborhood.LocalInverse
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

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
`q = f x + v`, with `v` normal at `x` and `‖v‖ < ε`, satisfies `‖q - f y‖ ≤ ‖v‖ < ε`, and
`q - f y` is normal at `y`, so injectivity forces `y = x`. Hence, for a compact `M`:

* `f x` is the unique nearest point of `f` to `f x + v` (`TauCeti.isMinOn_dist_add_iff`), and the
  length of `v` is the distance from `f x + v` to the image, `infDist (f x + v) (range f) = ‖v‖`
  (`TauCeti.infDist_add_eq_norm`);
* the tube is the metric neighbourhood of radius `ε` of the image
  (`TauCeti.image_normalTube_eq_thickening`); the inclusion of that neighbourhood in the tube
  holds without any injectivity (`TauCeti.thickening_range_subset_image_normalTube`);
* when normal addition is an open embedding of the tube, sending a point of the neighbourhood to
  its nearest point of `M` is a retraction, continuous on the neighbourhood
  (`TauCeti.exists_continuousOn_nearestPoint_retraction`);
* when `f` is a `C^(n + 1)` immersion, `n ≥ 1`, this retraction is `C^n` on a smaller
  neighbourhood of the image, where it agrees with the local normal retractions
  `TauCeti.exists_contMDiffOn_normalRetraction`
  (`TauCeti.exists_contMDiffOn_nearestPoint_retraction`).

For a compact embedded submanifold the tubular neighbourhood theorem supplies the injectivity:
there is a radius `ε > 0` for which the normal tube is the `ε`-neighbourhood of the image
(`TauCeti.exists_isOpenEmbedding_normalTube_image_eq_thickening`), and a neighbourhood of the image
on which the nearest-point retraction is unique and `C^n`
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
  -- Its derivative `u ↦ 2 ⟪f x - q, df_x u⟫` vanishes there.
  have hφ : HasFDerivAt (fun v : V => ‖v - q‖ ^ 2) (2 • innerSL ℝ (f x - q)) (f x) := by
    simpa using ((hasFDerivAt_id (f x)).sub_const q).norm_sq
  have hcrit : mvfderiv I ((fun v : V => ‖v - q‖ ^ 2) ∘ f) x = 0 :=
    mem_criticalPoints.mp (hsq.mem_criticalPoints (I := I))
  rw [mem_normalSubspace_iff_mvfderiv]
  intro u
  have hu := mvfderiv_comp_apply_of_differentiableAt hφ.differentiableAt hf u
  rw [hcrit, hφ.fderiv] at hu
  have hu' : 2 * ⟪f x - q, mvfderiv I f x u⟫_ℝ = 0 := by
    simpa only [smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat, zero_apply]
      using hu.symm
  rw [← neg_sub, inner_neg_left, (mul_eq_zero.mp hu').resolve_left two_ne_zero, neg_zero]

section Tube

variable {ε : ℝ}

/-- If normal addition is injective on the normal vectors of length less than `ε`, then the base
point `x` of such a normal vector `v` is the only nearest point of `f` to `f x + v`. -/
theorem eq_fst_of_isMinOn_dist (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {p : M × V}
    (hp : p ∈ normalTube I f ε) {y : M}
    (hy : IsMinOn (fun z => dist (f p.1 + p.2) (f z)) univ y) : y = p.1 := by
  set q := f p.1 + p.2
  have hy' : ∀ z, dist q (f y) ≤ dist q (f z) := fun z => hy (mem_univ z)
  have hn : q - f y ∈ normalSubspace I f y :=
    sub_mem_normalSubspace_of_isLocalMin (hf y) (Eventually.of_forall hy')
  have hlt : ‖q - f y‖ < ε :=
    calc ‖q - f y‖ = dist q (f y) := (dist_eq_norm _ _).symm
      _ ≤ dist q (f p.1) := hy' p.1
      _ = ‖p.2‖ := by simp [q, dist_eq_norm]
      _ < ε := (mem_normalTube.mp hp).2
  exact congrArg Prod.fst
    (hinj (x₁ := (y, q - f y)) (mem_normalTube.mpr ⟨hn, hlt⟩) hp (by simp [q]))

variable [CompactSpace M]

/-- If normal addition is injective on the normal vectors of length less than `ε`, the length of
such a normal vector `v` at `x` is at most the distance from `f x + v` to any point of the
image. -/
theorem norm_le_dist_add (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {p : M × V}
    (hp : p ∈ normalTube I f ε) (z : M) : ‖p.2‖ ≤ dist (f p.1 + p.2) (f z) := by
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMinOn ⟨p.1, mem_univ _⟩
    (continuous_const.dist hf.continuous).continuousOn
  obtain rfl := eq_fst_of_isMinOn_dist hf hinj hp hy
  simpa [dist_eq_norm] using hy (mem_univ z)

/-- If normal addition is injective on the normal vectors of length less than `ε`, the length of
such a normal vector `v` at `x` is the distance from `f x + v` to the image of `f`. -/
theorem infDist_add_eq_norm (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {p : M × V}
    (hp : p ∈ normalTube I f ε) : infDist (f p.1 + p.2) (range f) = ‖p.2‖ := by
  refine le_antisymm ?_ ((le_infDist (range_nonempty_iff_nonempty.mpr ⟨p.1⟩)).mpr ?_)
  · simpa [dist_eq_norm] using
      infDist_le_dist_of_mem (x := f p.1 + p.2) (mem_range_self (f := f) p.1)
  · rintro _ ⟨z, rfl⟩
    exact norm_le_dist_add hf hinj hp z

/-- If normal addition is injective on the normal vectors of length less than `ε`, the base point
`x` of such a normal vector `v` is a nearest point of `f` to `f x + v`, and the only one. -/
theorem isMinOn_dist_add_iff (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {p : M × V}
    (hp : p ∈ normalTube I f ε) {z : M} :
    IsMinOn (fun w => dist (f p.1 + p.2) (f w)) univ z ↔ z = p.1 := by
  refine ⟨eq_fst_of_isMinOn_dist hf hinj hp, ?_⟩
  rintro rfl w -
  simpa [dist_eq_norm] using norm_le_dist_add hf hinj hp w

/-- Every point at distance less than `ε` from the image of `f` is the endpoint `f x + v` of a
normal vector `v` at `x` of length less than `ε`: take for `f x` a nearest point. No injectivity of
normal addition is needed. -/
theorem thickening_range_subset_image_normalTube (hf : MDifferentiable I 𝓘(ℝ, V) f) :
    thickening ε (range f) ⊆ (fun p : M × V => f p.1 + p.2) '' normalTube I f ε := by
  intro q hq
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := mem_thickening_iff.mp hq
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMinOn ⟨z, mem_univ _⟩
    (continuous_const.dist hf.continuous).continuousOn
  have hlt : ‖q - f y‖ < ε := by
    rw [← dist_eq_norm]
    exact (hy (mem_univ z)).trans_lt hz
  have hn := sub_mem_normalSubspace_of_isLocalMin (hf y) (hy.isLocalMin univ_mem)
  exact ⟨(y, q - f y), mem_normalTube.mpr ⟨hn, hlt⟩, by simp⟩

/-- If normal addition is injective on the normal vectors of length less than `ε`, it maps them
onto the `ε`-neighbourhood of the image of `f`. -/
theorem image_normalTube_eq_thickening (hf : MDifferentiable I 𝓘(ℝ, V) f)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) :
    (fun p : M × V => f p.1 + p.2) '' normalTube I f ε = thickening ε (range f) := by
  refine (Subset.antisymm ?_ (thickening_range_subset_image_normalTube hf))
  rintro _ ⟨p, hp, rfl⟩
  rw [mem_thickening_iff_infDist_lt (range_nonempty_iff_nonempty.mpr ⟨p.1⟩),
    infDist_add_eq_norm hf hinj hp]
  exact (mem_normalTube.mp hp).2

/-- **The nearest-point retraction.** If normal addition is an open embedding of the normal
vectors of length less than `ε > 0`, there is a retraction `r` of `V` onto `M`, continuous on the
`ε`-neighbourhood of the image of `f`, which sends each point `q` of that neighbourhood to its
unique nearest point. It is the base point of the inverse of the tube coordinates, and the
displacement `q - f (r q)` is normal at `r q` (`TauCeti.sub_mem_normalSubspace_of_isLocalMin`). -/
theorem exists_continuousOn_nearestPoint_retraction [Nonempty M]
    (hf : MDifferentiable I 𝓘(ℝ, V) f) (hε : 0 < ε)
    (hemb : IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2)) :
    ∃ r : V → M, ContinuousOn r (thickening ε (range f)) ∧ (∀ x, r (f x) = x) ∧
      ∀ q ∈ thickening ε (range f), ∀ z,
        IsMinOn (fun w => dist q (f w)) univ z ↔ z = r q := by
  set g := (normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2
  have hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε) :=
    injOn_iff_injective.mpr hemb.injective
  have hrange : range g = thickening ε (range f) := by
    rw [range_domRestrict, image_normalTube_eq_thickening hf hinj]
  obtain ⟨x₀⟩ := ‹Nonempty M›
  have hzero : ∀ x, ((x, 0) : M × V) ∈ normalTube I f ε := fun x =>
    mem_normalTube.mpr ⟨zero_mem _, by simpa using hε⟩
  have : Nonempty (normalTube I f ε) := ⟨⟨(x₀, 0), hzero x₀⟩⟩
  -- The retraction is the base point of the inverse of the tube coordinates.
  set e := hemb.toOpenPartialHomeomorph g
  refine ⟨fun q => (e.symm q).val.1, ?_, fun x => ?_, fun q hq z => ?_⟩
  · refine (continuous_fst.comp continuous_subtype_val).comp_continuousOn
      (e.continuousOn_symm.mono ?_)
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_target, hrange]
  · have hx : g ⟨(x, 0), hzero x⟩ = f x := by simp [g]
    simp only [e, ← hx, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  · have hq' : f (e.symm q).val.1 + (e.symm q).val.2 = q :=
      hemb.toOpenPartialHomeomorph_right_inv g (hrange ▸ hq)
    simpa only [hq'] using isMinOn_dist_add_iff hf hinj (e.symm q).2 (z := z)

/-- **The nearest-point retraction is smooth.** Let `f` be a `C^(n + 1)` immersion of a compact
manifold, `n ≥ 1`, for which normal addition is injective on the normal vectors of length less
than `ε > 0`. A choice `r q` of a nearest point of `f` to each `q ∈ V` is a retraction of `V` onto
`M`, and it is `C^n` on the `δ`-neighbourhood of the image for some `0 < δ ≤ ε`. On the
`ε`-neighbourhood the nearest point is unique. Near each point of the image the retraction agrees
with the local `C^n` normal retraction `TauCeti.exists_contMDiffOn_normalRetraction`, since both
give nearest points there. -/
theorem exists_contMDiffOn_nearestPoint_retraction [Nonempty M] [FiniteDimensional ℝ V]
    {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f) (hn : 1 ≤ n)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hε : 0 < ε)
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) :
    ∃ δ > 0, δ ≤ ε ∧ ∃ r : V → M, ContMDiffOn 𝓘(ℝ, V) I n r (thickening δ (range f)) ∧
      (∀ x, r (f x) = x) ∧ (∀ q, IsMinOn (fun z => dist q (f z)) univ (r q)) ∧
      ∀ q ∈ thickening ε (range f), ∀ z, IsMinOn (fun w => dist q (f w)) univ z → z = r q := by
  obtain ⟨x₁⟩ := ‹Nonempty M›
  have : FiniteDimensional ℝ E :=
    Module.Finite.of_injective (mfderiv I 𝓘(ℝ, V) f x₁ : E →L[ℝ] V).toLinearMap (himm x₁)
  have hd : MDifferentiable I 𝓘(ℝ, V) f := hf.mdifferentiable (by simp)
  have hmin : ∀ q, ∃ y, IsMinOn (fun z => dist q (f z)) univ y := fun q =>
    let ⟨y, _, hy⟩ := isCompact_univ.exists_isMinOn univ_nonempty
      (continuous_const.dist hf.continuous).continuousOn
    ⟨y, hy⟩
  choose r hr using hmin
  -- A nearest point to the endpoint of a short normal vector is its base point.
  have hbase : ∀ q (p : M × V), p ∈ normalTube I f ε → f p.1 + p.2 = q → r q = p.1 :=
    fun q p hp hpq => eq_fst_of_isMinOn_dist hd hinj hp (by rw [hpq]; exact hr q)
  have hrf : ∀ x, r (f x) = x := fun x =>
    hbase (f x) (x, 0) (mem_normalTube.mpr ⟨zero_mem _, by simpa using hε⟩) (add_zero _)
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
  have hW : ContMDiffOn 𝓘(ℝ, V) I n r (⋃ x, t x) := by
    intro q hq
    obtain ⟨x, hx⟩ := mem_iUnion.mp hq
    exact ((hrt x).contMDiffAt ((ht x).mem_nhds hx)).contMDiffWithinAt
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_range hf.continuous).exists_thickening_subset_open
    (isOpen_iUnion ht) (range_subset_iff.mpr fun x => mem_iUnion.mpr ⟨x, hft x⟩)
  -- On the `ε`-neighbourhood the nearest point is unique.
  have huniq : ∀ q ∈ thickening ε (range f), ∀ z,
      IsMinOn (fun w => dist q (f w)) univ z → z = r q := by
    intro q hq z hz
    obtain ⟨p, hp, rfl⟩ := thickening_range_subset_image_normalTube hd hq
    rw [eq_fst_of_isMinOn_dist hd hinj hp hz, hbase _ p hp rfl]
  exact ⟨min δ ε, lt_min hδ hε, min_le_right _ _, r,
    hW.mono ((thickening_mono (min_le_left _ _) _).trans hδW), hrf, hr, huniq⟩

end Tube

section Embedding

variable [FiniteDimensional ℝ V] [CompactSpace M]

/-- **Tubular neighbourhoods are metric neighbourhoods.** For a compact `C²` embedded submanifold
of a finite-dimensional inner product space there is `ε > 0` such that normal addition is an open
embedding of the normal vectors of length less than `ε` onto the `ε`-neighbourhood of the image,
and the length of each such normal vector `v` at `x` is the distance from `f x + v` to the
image. -/
theorem exists_isOpenEmbedding_normalTube_image_eq_thickening [IsManifold I 2 M]
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f) (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hinj : Injective f) :
    ∃ ε > 0, IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2) ∧
      (fun p : M × V => f p.1 + p.2) '' normalTube I f ε = thickening ε (range f) ∧
      ∀ p ∈ normalTube I f ε, infDist (f p.1 + p.2) (range f) = ‖p.2‖ := by
  obtain ⟨ε, hε, hemb⟩ := exists_isOpenEmbedding_normalTube hf himm hinj
  have hd : MDifferentiable I 𝓘(ℝ, V) f := hf.mdifferentiable (by norm_num)
  have hinjOn : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε) :=
    injOn_iff_injective.mpr hemb.injective
  exact ⟨ε, hε, hemb, image_normalTube_eq_thickening hd hinjOn,
    fun p hp => infDist_add_eq_norm hd hinjOn hp⟩

/-- **The smooth nearest-point retraction onto a compact submanifold.** For a compact `C^(n + 1)`
embedded submanifold of a finite-dimensional inner product space, `n ≥ 1`, a choice `r q` of a
nearest point of `f` to each `q ∈ V` is a retraction of `V` onto `M` which is `C^n` on the
`δ`-neighbourhood of the image, for some `δ > 0`. On that neighbourhood the nearest point is
unique, and the displacement `q - f (r q)` is normal at `r q`
(`TauCeti.sub_mem_normalSubspace_of_isLocalMin`). -/
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
