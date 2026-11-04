/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# The rank of a map between manifolds

The *rank* of a map `f : M → N` at a point `x` is the dimension (`Module.finrank`) of the image
of its manifold derivative `df_x : T_x M → T_{f x} N` (`TauCeti.mfderivRank I J f x`). At a point
where `f` is not differentiable the derivative is zero and so is the rank. As for any `finrank`, an
infinite-dimensional image also gives rank zero by convention; the image is finite-dimensional
whenever the source or the target is.

Into a manifold modelled on a finite-dimensional space `E'`, the rank is at most `dim E'`, and a
point is a regular point of `f` exactly when the rank there is maximal, equal to `dim E'`
(`TauCeti.isRegularPoint_iff_mfderivRank_eq`). The critical points are therefore the points of rank
loss (`TauCeti.not_isRegularPoint_iff_mfderivRank_lt`). On a manifold modelled on a
finite-dimensional space `E`, the rank and the dimension of the kernel of `df_x` add up to `dim E`
(`TauCeti.finrank_ker_mfderiv_add_mfderivRank`).

The rank does not depend on coordinates. It is computed in any pair of charts by the derivative of
the coordinate expression of `f` (`TauCeti.mfderivRank_eq_finrank_range_fderivWithin`), and it is
unchanged by composition on the left with maps of injective derivative and on the right with maps
of surjective derivative (`TauCeti.mfderivRank_comp_of_injective` and
`TauCeti.mfderivRank_comp_of_surjective`). Composition on either side with a diffeomorphism
preserves it without any differentiability assumption on `f`
(`Diffeomorph.mfderivRank_diffeomorph_comp` and `Diffeomorph.mfderivRank_comp_diffeomorph`).

For a `C¹` map into a manifold modelled on a finite-dimensional space, the rank is lower
semicontinuous: it can only go up near a point
(`TauCeti.eventually_mfderivRank_le_mfderivRank`, `TauCeti.lowerSemicontinuous_mfderivRank`). So
each set `{x | r ≤ rank_x f}` is open (`TauCeti.isOpen_setOf_le_mfderivRank`); for `r = dim E'`
this is the openness of the set of regular points.

The rank stratifies the critical points of a smooth map, such as the singular points of a
completely integrable system, where the rank of the family of integrals drops.

## Main definitions

* `TauCeti.mfderivRank I J f x`: the rank of `f` at `x`.

## Main results

* `TauCeti.isRegularPoint_iff_mfderivRank_eq`: regular points are the points of maximal rank.
* `TauCeti.mfderivRank_eq_finrank_range_fderivWithin`: the rank read in arbitrary charts.
* `TauCeti.mfderivRank_comp_of_injective`, `TauCeti.mfderivRank_comp_of_surjective`,
  `Diffeomorph.mfderivRank_diffeomorph_comp`, `Diffeomorph.mfderivRank_comp_diffeomorph`:
  invariance of the rank under changes of coordinates.
* `TauCeti.lowerSemicontinuous_mfderivRank`, `TauCeti.isOpen_setOf_le_mfderivRank`: the rank of a
  `C¹` map is lower semicontinuous.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 4 (the rank of a smooth map) and Exercise 4-1 (lower semicontinuity).
-/

public section

open Function Set Filter Module
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {x : M}

variable (I J) in
/-- The **rank** of a map `f` at `x`: the dimension (`Module.finrank`) of the image of the
manifold derivative `df_x : T_x M → T_{f x} N`. It is zero at points where `f` is not
differentiable, and, by the convention of `Module.finrank`, also when that image is
infinite-dimensional. -/
noncomputable def mfderivRank (f : M → N) (x : M) : ℕ :=
  finrank 𝕜 (LinearMap.range (mfderiv I J f x).toLinearMap)

variable (I J) in
theorem mfderivRank_def (f : M → N) (x : M) :
    mfderivRank I J f x = finrank 𝕜 (LinearMap.range (mfderiv I J f x).toLinearMap) := (rfl)

/-- The rank of a map at a point where it is not differentiable is zero. -/
theorem mfderivRank_eq_zero_of_not_mdifferentiableAt (hf : ¬MDifferentiableAt I J f x) :
    mfderivRank I J f x = 0 := by
  rw [mfderivRank_def, mfderiv_zero_of_not_mdifferentiableAt hf,
    ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, finrank_bot]

/-- The rank of a map is at most the dimension of its source. -/
theorem mfderivRank_le_finrank_source [FiniteDimensional 𝕜 E] :
    mfderivRank I J f x ≤ finrank 𝕜 E :=
  LinearMap.finrank_range_le _

/-- The rank of a map is at most the dimension of its target. -/
theorem mfderivRank_le_finrank_target [FiniteDimensional 𝕜 E'] :
    mfderivRank I J f x ≤ finrank 𝕜 E' :=
  Submodule.finrank_le _

/-- **Rank–nullity for manifold derivatives.** The dimension of the kernel of `df_x` and the rank
of `f` at `x` add up to the dimension of the source. -/
theorem finrank_ker_mfderiv_add_mfderivRank [FiniteDimensional 𝕜 E] :
    finrank 𝕜 (mfderiv I J f x).ker + mfderivRank I J f x = finrank 𝕜 E := by
  rw [mfderivRank_def, add_comm]
  exact LinearMap.finrank_range_add_finrank_ker (mfderiv I J f x).toLinearMap

/-- A map has rank zero at `x` exactly when its derivative there vanishes. The image of the
derivative only needs to be finite-dimensional, as it is when the source or the target is. -/
theorem mfderivRank_eq_zero_iff
    [FiniteDimensional 𝕜 (LinearMap.range (mfderiv I J f x).toLinearMap)] :
    mfderivRank I J f x = 0 ↔ mfderiv I J f x = 0 := by
  rw [mfderivRank_def, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ LinearMap.congr_fun h v, fun h ↦ ?_⟩
  rw [h, ContinuousLinearMap.toLinearMap_zero]

/-- **Regular points are the points of maximal rank.** Into a manifold modelled on a
finite-dimensional space `E'`, a point is a regular point of `f` exactly when the rank of `f` there
is `dim E'`. -/
theorem isRegularPoint_iff_mfderivRank_eq [FiniteDimensional 𝕜 E'] :
    IsRegularPoint I J f x ↔ mfderivRank I J f x = finrank 𝕜 E' := by
  rw [isRegularPoint_iff, mfderivRank_def, ← finrank_tangentSpace (I := J) (f x),
    ← Submodule.eq_top_iff_finrank_eq, LinearMap.range_eq_top, ContinuousLinearMap.coe_coe]

/-- **Critical points are the points of rank loss.** Into a manifold modelled on a
finite-dimensional space `E'`, a point is not a regular point of `f` exactly when the rank of `f`
there is less than `dim E'`. -/
theorem not_isRegularPoint_iff_mfderivRank_lt [FiniteDimensional 𝕜 E'] :
    ¬IsRegularPoint I J f x ↔ mfderivRank I J f x < finrank 𝕜 E' := by
  rw [isRegularPoint_iff_mfderivRank_eq, ← ne_eq]
  exact ⟨fun h ↦ mfderivRank_le_finrank_target.lt_of_ne h, ne_of_lt⟩

/-! ### Invariance under changes of coordinates -/

section Comp

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- **Composition on the left with an immersion preserves the rank.** If `g` has injective
derivative at `f x`, then `g ∘ f` and `f` have the same rank at `x`. -/
theorem mfderivRank_comp_of_injective {g : N → P} (hg : MDifferentiableAt J K g (f x))
    (hf : MDifferentiableAt I J f x) (hinj : Injective (mfderiv J K g (f x))) :
    mfderivRank I K (g ∘ f) x = mfderivRank I J f x := by
  rw [mfderivRank_def, mfderivRank_def, mfderiv_comp x hg hf, ContinuousLinearMap.toLinearMap_comp]
  simpa using LinearMap.finrank_range_comp_comp _ (mfderiv I J f x).toLinearMap LinearMap.id hinj
    surjective_id

/-- **Composition on the right with a submersion preserves the rank.** If `h` has surjective
derivative at `p`, then `f ∘ h` has the same rank at `p` as `f` at `h p`. -/
theorem mfderivRank_comp_of_surjective {h : P → M} {p : P} (hf : MDifferentiableAt I J f (h p))
    (hh : MDifferentiableAt K I h p) (hsurj : Surjective (mfderiv K I h p)) :
    mfderivRank K J (f ∘ h) p = mfderivRank I J f (h p) := by
  rw [mfderivRank_def, mfderivRank_def, mfderiv_comp p hf hh, ContinuousLinearMap.toLinearMap_comp,
    Function.comp_apply]
  simpa using LinearMap.finrank_range_comp_comp LinearMap.id (mfderiv I J f (h p)).toLinearMap _
    injective_id hsurj

/-- **Diffeomorphisms of the target preserve the rank.** For a diffeomorphism `h`, the maps
`h ∘ f` and `f` have the same rank at every point. No differentiability of `f` is assumed. -/
@[simp]
theorem _root_.Diffeomorph.mfderivRank_diffeomorph_comp {n : ℕ∞ω} (h : N ≃ₘ^n⟮J, K⟯ P)
    (hn : n ≠ 0) (f : M → N) (x : M) :
    mfderivRank I K (h ∘ f) x = mfderivRank I J f x := by
  rw [mfderivRank_def, mfderivRank_def, h.range_mfderiv_diffeomorph_comp hn,
    LinearEquiv.finrank_map_eq]

/-- **Diffeomorphisms of the source preserve the rank.** For a diffeomorphism `h`, the map `f ∘ h`
has the same rank at `p` as `f` at `h p`. No differentiability of `f` is assumed. -/
@[simp]
theorem _root_.Diffeomorph.mfderivRank_comp_diffeomorph {n : ℕ∞ω} (h : P ≃ₘ^n⟮K, I⟯ M)
    (hn : n ≠ 0) (f : M → N) (p : P) :
    mfderivRank K J (f ∘ h) p = mfderivRank I J f (h p) := by
  rw [mfderivRank_def, mfderivRank_def, h.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]

end Comp

/-- **The rank read in charts.** If `f` is differentiable at `x`, its rank there is the rank of the
derivative of its coordinate expression in any charts around `x` and `f x`. -/
theorem mfderivRank_eq_finrank_range_fderivWithin [IsManifold I 1 M] [IsManifold J 1 N]
    {x₀ : M} {y₀ : N} (hf : MDifferentiableAt I J f x) (hx : x ∈ (chartAt H x₀).source)
    (hfx : f x ∈ (chartAt H' y₀).source) :
    mfderivRank I J f x = finrank 𝕜 (LinearMap.range (fderivWithin 𝕜
      (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (range I)
        (extChartAt I x₀ x)).toLinearMap) := by
  have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hfx' : f x ∈ (extChartAt J y₀).source := by rwa [extChartAt_source]
  have hmem : extChartAt I x₀ x ∈ range I :=
    extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hx')
  rw [(hf.hasMFDerivAt.hasFDerivWithinAt_of_mem_source hx hfx).fderivWithin
    (I.uniqueDiffOn _ hmem)]
  -- Both chart derivatives are invertible: the one on the right does not change the range, and
  -- the one on the left maps it isomorphically.
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_extChartAt (I := J) hfx'
  obtain ⟨B, hB⟩ := isInvertible_mfderivWithin_extChartAt_symm (I := I)
    ((extChartAt I x₀).map_source hx')
  -- The rank of a linear map is unchanged by composition with linear equivalences.
  have key (L : TangentSpace I x →ₗ[𝕜] TangentSpace J (f x)) (D : E →ₗ[𝕜] E')
      (A : TangentSpace J (f x) ≃ₗ[𝕜] E') (B : E ≃ₗ[𝕜] TangentSpace I x)
      (h : ∀ v, D v = A (L (B v))) :
      finrank 𝕜 (LinearMap.range D) = finrank 𝕜 (LinearMap.range L) := by
    rw [show D = A.toLinearMap ∘ₗ L ∘ₗ B.toLinearMap from LinearMap.ext h]
    exact LinearMap.finrank_range_comp_comp _ _ _ A.injective B.surjective
  refine (key (mfderiv I J f x).toLinearMap _ A.toLinearEquiv B.toLinearEquiv fun v ↦ ?_).symm
  simp only [ContinuousLinearMap.coe_coe]
  rw [← hA, ← hB]
  -- The chart derivatives act on tangent spaces which are definitionally the model spaces, so the
  -- composite and its pointwise expression agree by unfolding the composition.
  rfl

/-! ### Lower semicontinuity -/

section Semicontinuity

variable [CompleteSpace 𝕜] [IsManifold I 1 M] [FiniteDimensional 𝕜 E'] [IsManifold J 1 N]
  {n : ℕ∞ω}

/-- **The rank can only go up nearby.** At every point near a point `x` where `f` is `C¹`, the rank
of `f` is at least its rank at `x`. -/
theorem eventually_mfderivRank_le_mfderivRank (hf : ContMDiffAt I J n f x) (hn : 1 ≤ n) :
    ∀ᶠ y in 𝓝 x, mfderivRank I J f x ≤ mfderivRank I J f y := by
  have hf₁ : ContMDiffAt I J 1 f x := hf.of_le hn
  set g := extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm
  have hz : extChartAt I x x ∈ range I := mem_range_self _
  -- The coordinate expression `g` is `C¹` on `range I ∩ u` for an open neighbourhood `u` of the
  -- chart image of `x`, so its derivative within `range I` is continuous there.
  obtain ⟨u, hu, hzu, hg⟩ := (contMDiffAt_iff.1 hf₁).2.contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem hz] at hg
  have hcont := hg.continuousOn_fderivWithin (I.uniqueDiffOn.inter hu) le_rfl _ ⟨hz, hzu⟩
  have hD : ∀ w ∈ range I ∩ u, fderivWithin 𝕜 g (range I ∩ u) w = fderivWithin 𝕜 g (range I) w :=
    fun w hw ↦ fderivWithin_inter (hu.mem_nhds hw.2)
  -- In finite dimensions the rank of a linear map is a natural number, and maps of rank at least
  -- that of the derivative at the chart image of `x` form an open set.
  have hrank : ∀ L : E →L[𝕜] E',
      (mfderivRank I J f x : Cardinal) ≤ (L : E →ₗ[𝕜] E').rank ↔
        mfderivRank I J f x ≤ finrank 𝕜 (LinearMap.range (L : E →ₗ[𝕜] E')) := fun L ↦ by
    rw [LinearMap.rank, ← finrank_eq_rank, Nat.cast_le]
  have hx := mfderivRank_eq_finrank_range_fderivWithin (hf₁.mdifferentiableAt one_ne_zero)
    (mem_chart_source H x) (mem_chart_source H' (f x))
  have hopen := isOpen_setOfPred_nat_le_rank (𝕜 := 𝕜) (E := E) (F := E') (mfderivRank I J f x)
  have hev : ∀ᶠ w in 𝓝[range I] extChartAt I x x,
      w ∈ u ∧ mfderivRank I J f x ≤
        finrank 𝕜 (LinearMap.range (fderivWithin 𝕜 g (range I) w : E →ₗ[𝕜] E')) := by
    rw [← nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (hu.mem_nhds hzu))]
    have hmem : fderivWithin 𝕜 g (range I ∩ u) (extChartAt I x x) ∈
        {L : E →L[𝕜] E' | (mfderivRank I J f x : Cardinal) ≤ (L : E →ₗ[𝕜] E').rank} := by
      rw [Set.mem_ofPred_eq, hrank, hD _ ⟨hz, hzu⟩, ← hx]
    filter_upwards [hcont (hopen.mem_nhds hmem), self_mem_nhdsWithin] with w hw hwu
    rw [Set.mem_preimage, Set.mem_ofPred_eq, hrank, hD w hwu] at hw
    exact ⟨hwu.2, hw⟩
  rw [← map_extChartAt_nhds, eventually_map] at hev
  filter_upwards [hev, (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf₁,
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x),
    hf₁.continuousAt.preimage_mem_nhds
      ((chartAt H' (f x)).open_source.mem_nhds (mem_chart_source H' (f x)))] with y hy hfy hyx hfyx
  rw [mfderivRank_eq_finrank_range_fderivWithin (hfy.mdifferentiableAt one_ne_zero) hyx hfyx]
  exact hy.2

/-- **The rank of a `C¹` map is lower semicontinuous.** -/
theorem lowerSemicontinuous_mfderivRank (hf : ContMDiff I J n f) (hn : 1 ≤ n) :
    LowerSemicontinuous (mfderivRank I J f) := fun x _ hr ↦
  (eventually_mfderivRank_le_mfderivRank (hf x) hn).mono fun _ hy ↦ hr.trans_le hy

/-- **The points of rank at least `r` of a `C¹` map form an open set.** -/
theorem isOpen_setOf_le_mfderivRank (hf : ContMDiff I J n f) (hn : 1 ≤ n) (r : ℕ) :
    IsOpen {x | r ≤ mfderivRank I J f x} :=
  isOpen_iff_mem_nhds.2 fun x hx ↦ (eventually_mfderivRank_le_mfderivRank (hf x) hn).mono
    fun _ hy ↦ (Set.mem_ofPred_eq ▸ hx).trans hy

end Semicontinuity

end TauCeti
