/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
import TauCeti.Geometry.Manifold.Immersion.ShapeOperator
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# The nearest-point retraction onto a Euclidean submanifold

Let `f : M → V` be a map from a boundaryless manifold into a finite-dimensional real inner
product space, with closed image. Every point `y` of `V` has a nearest point on `f '' M`, and
`TauCeti.nearestPointRetraction f y` chooses a point of `M` mapped to one. The displacement from a
nearest point is normal to `f`, since a minimum of `x ↦ ‖f x - y‖²` is a critical point.

Normal addition `(x, v) ↦ f x + v` maps the normal vectors of length less than `ε` (the normal
tube `TauCeti.normalTube I f ε`) onto the open `ε`-neighbourhood of `f '' M`. Suppose it is
injective there. Then the ε-tube is inverted by the nearest-point retraction: every point `y` of
the `ε`-neighbourhood has a unique nearest point, and `nearestPointRetraction f (f x + v) = x` for
every normal vector `v` at `x` of length less than `ε`, whose distance to `f '' M` is `‖v‖`.
When normal addition is moreover an open embedding of the normal tube, the retraction is
continuous on the `ε`-neighbourhood. For a compact `C²` embedded submanifold, the tubular
neighbourhood theorem `TauCeti.exists_isOpenEmbedding_normalTube` supplies such a uniform radius.

## Main definitions

* `TauCeti.nearestPointRetraction f y`: a point of `M` whose image is nearest to `y`.

## Main results

* `TauCeti.sub_mem_normalSubspace_of_forall_norm_sub_le`: the displacement from a nearest point is
  normal.
* `TauCeti.nearestPointRetraction_add`: the retraction inverts normal addition on the normal tube.
* `TauCeti.image_normalTube_eq_thickening`: the image of the normal tube is the
  `ε`-neighbourhood of the image.
* `TauCeti.forall_norm_sub_le_iff_eq_nearestPointRetraction`: nearest points in the
  `ε`-neighbourhood are unique.
* `TauCeti.continuousOn_nearestPointRetraction`: continuity on the `ε`-neighbourhood.
* `TauCeti.exists_pos_continuousOn_nearestPointRetraction`: the uniform radius for a compact `C²`
  embedded submanifold.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 4, Section 5.
* J. W. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press
  (1963), Section 6.
-/

public section

open Set Function Metric Filter Topology
open scoped Manifold

namespace TauCeti

variable {M V : Type*} [NormedAddCommGroup V] {f : M → V}

section Definition

variable [Nonempty M]

/-- The **nearest-point retraction** onto the image of `f : M → V`: a point of `M` whose image is
nearest to `y`, chosen arbitrarily when no nearest point exists or when there are several. It is
characterised by `TauCeti.forall_norm_sub_nearestPointRetraction_le` when `f` has closed image in a
finite-dimensional space, and inverts normal addition on a normal tube on which normal addition is
injective (`TauCeti.nearestPointRetraction_add`). -/
@[expose] noncomputable def nearestPointRetraction (f : M → V) (y : V) : M :=
  Classical.epsilon fun x => ∀ x', ‖y - f x‖ ≤ ‖y - f x'‖

/-- `TauCeti.nearestPointRetraction f y` is a chosen minimiser of `x ↦ ‖y - f x‖`. -/
theorem nearestPointRetraction_def (f : M → V) (y : V) :
    nearestPointRetraction f y = Classical.epsilon fun x => ∀ x', ‖y - f x‖ ≤ ‖y - f x'‖ :=
  rfl

/-- If `y` has a nearest point on the image of `f`, then `nearestPointRetraction f y` is mapped to
one. -/
theorem forall_norm_sub_nearestPointRetraction_le_of_exists {y : V}
    (h : ∃ x, ∀ x', ‖y - f x‖ ≤ ‖y - f x'‖) (x' : M) :
    ‖y - f (nearestPointRetraction f y)‖ ≤ ‖y - f x'‖ :=
  Classical.epsilon_spec (p := fun x => ∀ x', ‖y - f x‖ ≤ ‖y - f x'‖) h x'

/-- An injective map is recovered from its nearest-point retraction on its image. -/
theorem nearestPointRetraction_self (hinj : Injective f) (x : M) :
    nearestPointRetraction f (f x) = x := by
  have h := forall_norm_sub_nearestPointRetraction_le_of_exists (f := f) (y := f x)
    ⟨x, fun x' => by simp⟩ x
  rw [sub_self, norm_zero] at h
  exact (hinj (sub_eq_zero.mp (norm_le_zero_iff.mp h))).symm

end Definition

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [InnerProductSpace ℝ V]

/-- **The displacement from a nearest point is normal.** If `f x` is a point of the image of a map
`f` from a boundaryless manifold nearest to `y`, then `y - f x` is normal to `f` at `x`. Where `f`
is not differentiable its normal space is all of `V`. -/
theorem sub_mem_normalSubspace_of_forall_norm_sub_le [TopologicalSpace M] [ChartedSpace H M]
    [I.Boundaryless] {x : M} {y : V} (hmin : ∀ x', ‖y - f x‖ ≤ ‖y - f x'‖) :
    y - f x ∈ normalSubspace I f x := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, V) f x
  swap
  · rw [mem_normalSubspace_iff, mfderiv_zero_of_not_mdifferentiableAt hf]
    exact fun _ => inner_zero_right _
  have hloc : IsLocalMin (fun x' => ‖f x' - y‖ ^ 2) x :=
    Eventually.of_forall fun x' => by
      simpa only [norm_sub_rev (f _) y] using pow_le_pow_left₀ (norm_nonneg _) (hmin x') 2
  have h := (mem_criticalPoints_norm_sq_sub_comp_iff (a := y) hf).1 hloc.mem_criticalPoints
  simpa only [neg_sub] using neg_mem h

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- In a finite-dimensional space, every point has a nearest point on a nonempty closed image. -/
theorem exists_forall_norm_sub_le [Nonempty M] (hcl : IsClosed (range f)) (y : V) :
    ∃ x, ∀ x', ‖y - f x‖ ≤ ‖y - f x'‖ := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hcl.exists_infDist_eq_dist (range_nonempty f) y
  refine ⟨x, fun x' => ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm, ← hx]
  exact infDist_le_dist_of_mem (mem_range_self x')

/-- For a map with closed image in a finite-dimensional space, `nearestPointRetraction f y` is
mapped to a point of the image nearest to `y`. -/
theorem forall_norm_sub_nearestPointRetraction_le [Nonempty M] (hcl : IsClosed (range f)) (y : V)
    (x' : M) : ‖y - f (nearestPointRetraction f y)‖ ≤ ‖y - f x'‖ :=
  forall_norm_sub_nearestPointRetraction_le_of_exists (exists_forall_norm_sub_le hcl y) x'

/-- For a map with closed image in a finite-dimensional space, the distance from `y` to the image
is attained at `nearestPointRetraction f y`. -/
theorem dist_nearestPointRetraction_eq_infDist [Nonempty M] (hcl : IsClosed (range f)) (y : V) :
    dist y (f (nearestPointRetraction f y)) = infDist y (range f) := by
  refine le_antisymm ?_ (infDist_le_dist_of_mem (mem_range_self _))
  refine (le_infDist (range_nonempty f)).2 ?_
  rintro _ ⟨x', rfl⟩
  rw [dist_eq_norm, dist_eq_norm]
  exact forall_norm_sub_nearestPointRetraction_le hcl y x'

variable [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless] {ε : ℝ}

omit [FiniteDimensional ℝ V] in
/-- Below the injectivity threshold of normal addition, a nearest point to `f x + v`, for `v`
normal at `x` of length less than `ε`, is `f x` itself and comes only from `x`. -/
theorem eq_of_forall_norm_add_sub_le
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {x x' : M} {v : V}
    (hv : (x, v) ∈ normalTube I f ε) (hmin : ∀ x'', ‖f x + v - f x'‖ ≤ ‖f x + v - f x''‖) :
    x' = x := by
  have hlt : ‖f x + v - f x'‖ < ε := by
    simpa using (hmin x).trans_lt (by simpa using (mem_normalTube.1 hv).2)
  have hmem : (x', f x + v - f x') ∈ normalTube I f ε := mem_normalTube.2
    ⟨sub_mem_normalSubspace_of_forall_norm_sub_le hmin, hlt⟩
  have := hinj hmem hv (by simp)
  exact congrArg Prod.fst this

/-- For a map with closed image, below the injectivity threshold of normal addition on the normal
tube, the nearest-point retraction inverts normal addition. -/
theorem nearestPointRetraction_add [Nonempty M] (hcl : IsClosed (range f))
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {x : M} {v : V}
    (hv : (x, v) ∈ normalTube I f ε) : nearestPointRetraction f (f x + v) = x :=
  eq_of_forall_norm_add_sub_le hinj hv (forall_norm_sub_nearestPointRetraction_le hcl _)

/-- Below the injectivity threshold of normal addition, the distance from `f x + v` to the image
of `f` is `‖v‖`, for `v` normal at `x` of length less than `ε`. -/
theorem infDist_add_eq_norm (hcl : IsClosed (range f))
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {x : M} {v : V}
    (hv : (x, v) ∈ normalTube I f ε) :
    infDist (f x + v) (range f) = ‖v‖ := by
  have : Nonempty M := ⟨x⟩
  rw [← dist_nearestPointRetraction_eq_infDist hcl, nearestPointRetraction_add hcl hinj hv,
    dist_eq_norm, add_sub_cancel_left]

/-- **The normal tube fills the ε-neighbourhood.** For a map with closed image,
the image of the normal tube of radius `ε` under normal addition is the open `ε`-neighbourhood of
the image of `f`: every point of it is reached from a nearest point. -/
theorem image_normalTube_eq_thickening (hcl : IsClosed (range f)) :
    (fun p : M × V => f p.1 + p.2) '' normalTube I f ε = thickening ε (range f) := by
  ext y
  constructor
  · rintro ⟨⟨x, v⟩, hv, rfl⟩
    exact mem_thickening_iff.2
      ⟨f x, mem_range_self x, by simpa [dist_eq_norm] using (mem_normalTube.1 hv).2⟩
  · intro hy
    obtain ⟨_, ⟨x₀, rfl⟩, -⟩ := mem_thickening_iff.1 hy
    have : Nonempty M := ⟨x₀⟩
    set x := nearestPointRetraction f y
    have hmin := forall_norm_sub_nearestPointRetraction_le hcl y
    refine ⟨(x, y - f x),
      mem_normalTube.2 ⟨sub_mem_normalSubspace_of_forall_norm_sub_le hmin, ?_⟩,
      add_sub_cancel _ _⟩
    rw [← dist_eq_norm, dist_nearestPointRetraction_eq_infDist hcl]
    exact (mem_thickening_iff_infDist_lt (range_nonempty f)).1 hy

/-- For a map with closed image, the nearest-point retraction of a point `y` of the
`ε`-neighbourhood of the image, with its displacement `y - f (nearestPointRetraction f y)`, lies in
the normal tube of radius `ε`. -/
theorem mk_nearestPointRetraction_mem_normalTube [Nonempty M] (hcl : IsClosed (range f)) {y : V}
    (hy : y ∈ thickening ε (range f)) :
    (nearestPointRetraction f y, y - f (nearestPointRetraction f y)) ∈ normalTube I f ε := by
  refine mem_normalTube.2 ⟨sub_mem_normalSubspace_of_forall_norm_sub_le
    (forall_norm_sub_nearestPointRetraction_le hcl y), ?_⟩
  rw [← dist_eq_norm, dist_nearestPointRetraction_eq_infDist hcl]
  exact (mem_thickening_iff_infDist_lt (range_nonempty f)).1 hy

/-- **Uniqueness of nearest points.** For a map with closed image, below the injectivity threshold
of normal addition, a point `y` of the `ε`-neighbourhood of the image has exactly one point of `M`
mapped to a point nearest to `y`, namely `nearestPointRetraction f y`. -/
theorem forall_norm_sub_le_iff_eq_nearestPointRetraction [Nonempty M]
    (hcl : IsClosed (range f))
    (hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε)) {y : V}
    (hy : y ∈ thickening ε (range f)) {x : M} :
    (∀ x', ‖y - f x‖ ≤ ‖y - f x'‖) ↔ x = nearestPointRetraction f y := by
  refine ⟨fun hmin => ?_, fun h => h ▸ forall_norm_sub_nearestPointRetraction_le hcl y⟩
  have hv := mk_nearestPointRetraction_mem_normalTube (I := I) hcl hy
  refine eq_of_forall_norm_add_sub_le hinj hv ?_
  simpa only [add_sub_cancel] using hmin

/-- For a map with closed image, if normal addition is an open embedding of the normal tube of
radius `ε`, then the nearest-point retraction is continuous on the `ε`-neighbourhood of the image:
there it is the base point of the inverse of normal addition. -/
theorem continuousOn_nearestPointRetraction [Nonempty M] (hcl : IsClosed (range f))
    (hemb : IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2)) :
    ContinuousOn (nearestPointRetraction f) (thickening ε (range f)) := by
  have hinj : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε) :=
    injOn_iff_injective.2 hemb.injective
  have hrange : range ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2) =
      thickening ε (range f) := by
    rw [← image_normalTube_eq_thickening (I := I) hcl, range_domRestrict]
  let e := hemb.isEmbedding.toHomeomorph
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun y : thickening ε (range f) =>
      ((e.symm ⟨y.1, hrange.symm.subset y.2⟩ : normalTube I f ε) : M × V).1 :=
    continuous_fst.comp (continuous_subtype_val.comp
      (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)))
  convert hc using 1
  funext y
  set q := e.symm ⟨y.1, hrange.symm.subset y.2⟩
  have hq : f (q : M × V).1 + (q : M × V).2 = y.1 :=
    congrArg Subtype.val (e.apply_symm_apply ⟨y.1, hrange.symm.subset y.2⟩)
  simp only [domRestrict_apply]
  rw [← hq]
  exact nearestPointRetraction_add hcl hinj q.2

variable [IsManifold I 2 M] [CompactSpace M]

/-- **Nearest-point retraction onto a compact Euclidean submanifold.** For a compact `C²` embedded
boundaryless submanifold of a finite-dimensional real inner product space there is a uniform
radius `ε > 0` such that normal addition is an open embedding of the normal tube of radius `ε` onto
the `ε`-neighbourhood of the image, the nearest-point retraction inverts it, and the retraction is
continuous on that neighbourhood. -/
theorem exists_pos_continuousOn_nearestPointRetraction [Nonempty M]
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f) (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hinj : Injective f) :
    ∃ ε > 0, IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2) ∧
      (fun p : M × V => f p.1 + p.2) '' normalTube I f ε = thickening ε (range f) ∧
      (∀ p ∈ normalTube I f ε, nearestPointRetraction f (f p.1 + p.2) = p.1) ∧
      ContinuousOn (nearestPointRetraction f) (thickening ε (range f)) := by
  obtain ⟨ε, hε, hemb⟩ := exists_isOpenEmbedding_normalTube hf himm hinj
  have hcl : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  have hinjOn : InjOn (fun p : M × V => f p.1 + p.2) (normalTube I f ε) :=
    injOn_iff_injective.2 hemb.injective
  exact ⟨ε, hε, hemb, image_normalTube_eq_thickening hcl,
    fun p hp => nearestPointRetraction_add hcl hinjOn hp,
    continuousOn_nearestPointRetraction hcl hemb⟩

end FiniteDimensional

end TauCeti
