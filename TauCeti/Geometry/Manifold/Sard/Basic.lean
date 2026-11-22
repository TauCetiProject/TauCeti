/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Analysis.Calculus.Sard.LowDimension
import TauCeti.Analysis.Calculus.Sard.OutermostStratum
import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Sard's theorem for maps between manifolds of arbitrary dimensions

Let `f : M → N` be a map between real manifolds modelled on finite-dimensional spaces `E` and
`E'`, of dimensions `m` and `n`, with `M` Lindelöf (for instance second countable). This file
proves that the critical values of `f`, the images of the points where `mfderiv I J f` is not
surjective, form a null set of `N`: their image in every chart of `N` is null for every Haar
measure on `E'` (`TauCeti.IsNullSet`). No measure on `N` itself is chosen. The regularity needed
depends on the dimensions.

* If `m < n`, every point is critical and the whole image of a differentiable map is null; here
  `M` and `N` may have boundary or corners.
* In general, a `C^k` map with `k > m - n` and `k ≥ 1` suffices, in particular a smooth map. This
  is the sharp regularity of Sard's theorem: Whitney's example shows that a `C¹` function on the
  plane can have critical values of positive measure.

Each statement only asks for the regularity at the points of a given set `s` of critical points,
so it applies to maps that are only defined, or only regular, on an open subset of `M`. Except in
the first case, the points of `s` must be interior points of `M`. This is automatic when `M` has
empty intrinsic boundary, even if its model has corners.

The proofs read `f` in pairs of extended charts and apply the corresponding theorem for maps
between normed spaces (`TauCeti.addHaar_image_criticalPoints_eq_zero` and
`DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank`). A countable family of charts
covers `M` (`TauCeti.isNullSet_image_of_forall_addHaar_image_extChartAt`), and since nullity is
tested in every chart of `N`, no comparison of target charts is needed. The equal-dimensional
case, which needs only first derivatives and allows boundary in the source, is
`TauCeti.isNullSet_image_of_not_isRegularPoint`.

## Main results

* `TauCeti.isNullSet_image_of_finrank_lt_finrank`: the image of a differentiable map from a
  manifold of smaller dimension is null.
* `MDifferentiable.finrank_le_finrank_of_surjective`: a differentiable surjection from a Lindelöf
  manifold onto a nonempty manifold forces `dim N ≤ dim M`.
* `TauCeti.finrank_sub_le_finrank_of_isRegularValue_of_surjective`: a `C¹` surjection from a
  Lindelöf manifold onto a nonempty regular fibre forces `dim P - dim B ≤ dim M`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_isInteriorPoint`: Sard's theorem on a set
  of interior critical points, for an arbitrary model with corners.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt`: Sard's theorem at the sharp
  regularity `k > m - n`, `k ≥ 1`, for arbitrary dimensions and a boundaryless source
  (`BoundarylessManifold I M`).
* `ContMDiff.isNullSet_image_criticalPoints` and `ContMDiff.dense_isRegularValue`: the critical
  values of such a map with boundaryless source (`BoundarylessManifold I M`) are null, and its
  regular values are dense.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 and its proof (passage from coordinates to manifolds).
-/

public section

open Function Module Set MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {s : Set M}

section LowDimension

variable [IsManifold I 1 M] [IsManifold J 1 N]

omit [FiniteDimensional ℝ E'] in
/-- **Sard's theorem when the source has smaller dimension.** If the model of `M` has smaller
dimension than the model of `N` and `f` is differentiable at every point of `s`, then `f '' s` is
null in `N`. Both manifolds may have boundary or corners. -/
theorem isNullSet_image_of_finrank_lt_finrank (hdim : finrank ℝ E < finrank ℝ E')
    (hf : ∀ x ∈ s, MDifferentiableAt I J f x) : IsNullSet J (f '' s) := by
  refine isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ μ _ ↦ ?_
  refine DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank μ ?_ hdim
  rintro _ ⟨x, hx, rfl⟩
  refine ((mdifferentiableAt_iff_of_mem_source hx.1.2 hx.2).1 (hf x hx.1.1)).2.mono ?_
  rintro _ ⟨x', -, rfl⟩
  rw [extChartAt_coe]
  exact mem_range_self _

omit [FiniteDimensional ℝ E'] in
/-- The range of a differentiable map from a Lindelöf manifold to a manifold of larger dimension is
null. -/
theorem _root_.MDifferentiable.isNullSet_range_of_finrank_lt_finrank
    (hf : MDifferentiable I J f) (hdim : finrank ℝ E < finrank ℝ E') :
    IsNullSet J (range f) := by
  rw [← image_univ]
  exact isNullSet_image_of_finrank_lt_finrank hdim fun x _ ↦ hf x

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- A differentiable surjection from a Lindelöf manifold onto a nonempty manifold forces the
dimension of the target to be at most that of the source. -/
theorem _root_.MDifferentiable.finrank_le_finrank_of_surjective [Nonempty N]
    (hf : MDifferentiable I J f) (hsurj : Surjective f) :
    finrank ℝ E' ≤ finrank ℝ E := by
  borelize E'
  by_contra hlt
  have hnull := hf.isNullSet_range_of_finrank_lt_finrank (not_le.1 hlt)
  have hdense : Dense (∅ : Set N) := by simpa [hsurj.range_eq] using hnull.dense_compl
  exact Set.not_nonempty_empty hdense.nonempty

end LowDimension

section Interior

variable {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

omit [FiniteDimensional ℝ E] [LindelofSpace M] [FiniteDimensional ℝ E'] [MeasurableSpace E']
  [BorelSpace E'] in
/-- At a non-regular point where `f` is `C^n`, `n ≠ 0`, the coordinate expression of `f` in charts
containing the interior point and its image is `C^n` and has nonsurjective derivative. -/
private theorem contDiffAt_and_not_surjective_fderiv_extChartAt (hn : n ≠ 0) {x₀ x : M} {y₀ : N}
    (hf : ContMDiffAt I J n f x) (hreg : ¬ IsRegularPoint I J f x)
    (hxi : I.IsInteriorPoint x)
    (hx : x ∈ (chartAt H x₀).source) (hfx : f x ∈ (chartAt H' y₀).source) :
    ContDiffAt ℝ n (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ x) ∧
      ¬ Surjective (fderiv ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
        (extChartAt I x₀ x)) := by
  have : IsManifold I 1 M := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold J 1 N := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have hcoord : extChartAt I x₀ x ∈ interior (range I) :=
    (chartAt H x₀).interior_extend_target_subset_interior_range
      ((I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x₀) hx).1 hxi)
  have hnhds := mem_interior_iff_mem_nhds.1 hcoord
  refine ⟨((contMDiffAt_iff_of_mem_source hx hfx).1 hf).2.contDiffAt hnhds, ?_⟩
  have h := isRegularPoint_iff_surjective_fderivWithin (hf.mdifferentiableAt hn) hx hfx
  simpa only [fderivWithin_of_mem_nhds hnhds] using h.not.mp hreg

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Transfer of a Sard theorem for maps between normed spaces to manifolds. If every map `E → E'`
that is `C^n` at the points of a set `U` sends the points of `U` where its derivative is not
surjective to a Haar-null set, then the same holds for sets of interior critical points of maps
between manifolds modelled on `E` and `E'`. -/
private theorem isNullSet_image_of_forall_addHaar_image_criticalPoints (hn : n ≠ 0)
    (hflat : ∀ (g : E → E') (U : Set E) (μ : Measure E') [μ.IsAddHaarMeasure],
      (∀ z ∈ U, ContDiffAt ℝ n g z) → μ (g '' (U ∩ {z | ¬ Surjective (fderiv ℝ g z)})) = 0)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (hsi : ∀ x ∈ s, I.IsInteriorPoint x) :
    IsNullSet J (f '' s) := by
  refine isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ μ _ ↦ ?_
  have key : ∀ z ∈ extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source),
      ContDiffAt ℝ n (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z ∧
        ¬ Surjective (fderiv ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z) := by
    rintro _ ⟨x, hx, rfl⟩
    exact contDiffAt_and_not_surjective_fderiv_extChartAt hn
      (hf x hx.1.1) (hs x hx.1.1) (hsi x hx.1.1) hx.1.2 hx.2
  refine measure_mono_null (image_mono fun z hz ↦ ?_) (hflat
    (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
    (extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source)) μ
    fun z hz ↦ (key z hz).1)
  exact ⟨hz, (key z hz).2⟩

/-- **Sard's theorem on the interior.** For a Lindelöf manifold with any model with corners,
a set of interior critical points where `f` is `C^k` has null image if
`k > dim M - dim N` and `k ≥ 1`. No boundarylessness assumption is made on either model. -/
theorem isNullSet_image_of_not_isRegularPoint_of_isInteriorPoint
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (hsi : ∀ x ∈ s, I.IsInteriorPoint x) : IsNullSet J (f '' s) :=
  isNullSet_image_of_forall_addHaar_image_criticalPoints
    (fun h ↦ by simp [h] at hk)
    (fun _ _ μ _ hg ↦ addHaar_image_criticalPoints_eq_zero μ hg hk) hf hs hsi

end Interior

section Boundaryless

variable [BoundarylessManifold I M] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- **Sard's theorem.** Let `M` be a boundaryless Lindelöf manifold modelled on a space of
dimension `m` and `N` a manifold modelled on a space of dimension `n`. If `f` is `C^k` at every
point of `s` with `k > m - n` and `k ≥ 1`, and no point of `s` is regular, then `f '' s` is null in
`N`. This is the sharp regularity of Sard's theorem. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_isInteriorPoint hk hf hs
    fun _ _ ↦ BoundarylessManifold.isInteriorPoint

/-- **Sard's theorem.** The critical values of a `C^k` map from a boundaryless Lindelöf manifold
of dimension `m` to a manifold of dimension `n` form a null set when `k > m - n` and `k ≥ 1`, in
particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map from a boundaryless Lindelöf manifold of dimension `m` to a
manifold of dimension `n` are dense when `k > m - n` and `k ≥ 1`, in particular when the map is
smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints hk).dense_compl

end Boundaryless

section RegularFiber

/-- **Dimension lower bound for a smooth surjection onto a nonempty regular fibre.** If `p : P → B`
is `C¹` from a finite-dimensional boundaryless real manifold `P` to a finite-dimensional real
manifold `B`, `c : B` is a regular value of `p` with nonempty fibre, and `θ : M → P` is a `C¹` map
from a Lindelöf manifold surjecting onto `p ⁻¹' {c}`, then `finrank ℝ EP - finrank ℝ EB ≤
finrank ℝ EM`. -/
theorem finrank_sub_le_finrank_of_isRegularValue_of_surjective
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless]
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB 1 B]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM 1 M] [LindelofSpace M]
    {p : P → B} (hp : ContMDiff IP IB 1 p) {c : B} (hne : (p ⁻¹' {c}).Nonempty)
    (hreg : IsRegularValue IP IB p c) {θ : M → P} (hθ : ContMDiff IM IP 1 θ)
    (hmem : ∀ m : M, p (θ m) = c) (hsurj : ∀ y : P, p y = c → ∃ m : M, θ m = y) :
    finrank ℝ EP - finrank ℝ EB ≤ finrank ℝ EM := by
  obtain ⟨x, rfl⟩ := hne
  have hc : IB.IsInteriorPoint (p x) :=
    ((hp x).mdifferentiableAt one_ne_zero).isInteriorPoint_of_surjective_mfderiv
      (isRegularPoint_iff.1 (hreg.isRegularPoint rfl)) BoundarylessManifold.isInteriorPoint
  let := regularFiberChartedSpace (le_refl 1) hp hc hreg
  have := isManifold_regularFiber (le_refl 1) hp hc hreg
  let θ' : M → {y : P // p y = p x} := fun m ↦ ⟨θ m, hmem m⟩
  have hθ' : ContMDiff IM 𝓘(ℝ, Fin (finrank ℝ EP - finrank ℝ EB) → ℝ) 1 θ' :=
    (isSmoothEmbedding_coe_regularFiber (le_refl 1) hp hc hreg).contMDiff_iff_comp.2 hθ
  have hθ'_surj : Surjective θ' := fun ⟨y, hy⟩ ↦ by
    obtain ⟨m, hm⟩ := hsurj y hy
    exact ⟨m, Subtype.ext hm⟩
  have : Nonempty {y : P // p y = p x} := ⟨⟨x, rfl⟩⟩
  simpa [Module.finrank_fin_fun] using
    (hθ'.mdifferentiable one_ne_zero).finrank_le_finrank_of_surjective hθ'_surj

end RegularFiber

end TauCeti
