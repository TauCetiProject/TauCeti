/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Vertical
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# The Poincaré lemma on manifolds

A closed differential form of positive degree on a manifold is locally exact: near every point
it is the exterior derivative of a globally defined form of the same regularity
(`TauCeti.exists_mextDeriv_eq_nhds`). Boundary and corner points are included.

The form is read in the preferred extended chart at the point. Mathlib's `range I` is convex, so
the intersection of a small ball about the chart point with `range I` is a convex set with unique
derivatives inside the chart target, although it need not be open. The relative flat Poincaré
lemma (`Convex.extDerivWithin_poincareHomotopy`) makes the Poincaré homotopy operator, centred at
the chart point, a primitive there. Its pullback along the chart is cut off by a smooth bump
function supported in the chart domain, which gives a primitive on all of `M` near the point.

The same construction applies to a smooth family of forms, recorded as a form `φ` on a product
`N × M` with slices `ι_p^* φ` along the inclusions `ι_p : y ↦ (p, y)`
(`TauCeti.exists_mextDeriv_eq_mpullback_prodMk_nhds`). If the slices are closed near `x`, uniformly
in `p`, the primitives built from one chart and one bump function for all slices form a smooth
family: their vertical form on `N × M` (`TauCeti.verticalForm`) is as smooth as `φ`. This is
because the Poincaré homotopy operator depends smoothly on parameters
(`Convex.contDiffOn_uncurry_poincareHomotopy`) and the coordinate expressions of the slices are
jointly smooth (`TauCeti.IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk`). The primitives
vanish at `x`, the centre of the homotopy. Smooth families of primitives of the time derivatives
of a family of forms are what Moser's argument integrates.

The cutoff is the only place where `[FiniteDimensional ℝ E]` and `[T2Space M]` are used: smooth
bump functions need both. The coefficient space is complete because the flat primitive is an
integral.

## Main declarations

* `TauCeti.exists_mextDeriv_eq_nhds`: the manifold Poincaré lemma.
* `TauCeti.exists_mextDeriv_eq_mpullback_prodMk_nhds`: the Poincaré lemma for smooth families of
  forms, with primitives depending smoothly on the parameter and vanishing at the point.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 17.14 and Corollary 17.15.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument, which uses smooth families of primitives).
-/

public section

noncomputable section

open Set Filter Metric Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- A form which is closed over a ball about the chart point of `x`, intersected with the model
range, has a flat primitive there in the chart at `x`: the Poincaré homotopy operator centred at
the chart point of `x` of its coordinate expression. It is as smooth as the form and vanishes at
the centre. -/
private theorem poincareHomotopy_inChartAt [IsManifold I ∞ M] {r : ℕ∞} (hr : 1 ≤ r)
    {φ : RoughForm I M F (k + 1)} (hφ : IsSmoothForm I r φ) {x : M} {ε : ℝ} (hε : 0 < ε)
    (hsub : ball (extChartAt I x x) ε ∩ range I ⊆
      (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' {y | mextDeriv φ y = 0}) :
    ContDiffOn ℝ r (poincareHomotopy (extChartAt I x x) (φ.inChartAt x))
        (ball (extChartAt I x x) ε ∩ range I) ∧
      ∀ z ∈ ball (extChartAt I x x) ε ∩ range I,
        extDerivWithin (poincareHomotopy (extChartAt I x x) (φ.inChartAt x))
          (ball (extChartAt I x x) ε ∩ range I) z = φ.inChartAt x z := by
  have : IsManifold I ((r : WithTop ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hφ₁ : IsSmoothForm I 1 φ :=
    hφ.of_le (by exact_mod_cast hr)
  obtain ⟨hconv, hsu, hxs⟩ := convex_uniqueDiffOn_ball_inter_range_extChartAt (I := I) x hε
  have hω : ContDiffOn ℝ r (φ.inChartAt x) (ball (extChartAt I x x) ε ∩ range I) :=
    fun z hz ↦ (φ.contDiffWithinAt_inChartAt_of_contDiffWithinAt_inChartAt (hsub hz).1
      (mem_extChartAt_source _) (hφ.contDiffWithinAt_inChartAt_self _)).mono inter_subset_right
  -- Closedness in the chart: `mextDeriv φ` read in the chart is the flat derivative within
  -- `range I`, which agrees with the derivative within the ball near each of its points.
  have hcl (z : E) (hz : z ∈ ball (extChartAt I x x) ε ∩ range I) :
      extDerivWithin (φ.inChartAt x) (ball (extChartAt I x x) ε ∩ range I) z = 0 := by
    have hset : ball (extChartAt I x x) ε ∩ range I =ᶠ[𝓝 z] range I :=
      inter_eventuallyEqSet_right.mpr (eventually_of_mem (isOpen_ball.mem_nhds hz.1) fun _ h _ ↦ h)
    rw [extDerivWithin_congr_set hset, ← hφ₁.inChartAt_mextDeriv_eq x (hsub hz).1]
    ext v
    rw [RoughForm.inChartAt_apply, show mextDeriv φ ((extChartAt I x).symm z) = 0 from (hsub hz).2]
    simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  exact ⟨hconv.contDiffOn_poincareHomotopy hsu hxs hω, fun z hz ↦
    hconv.extDerivWithin_poincareHomotopy hsu hxs (hω.of_le (by exact_mod_cast hr)) hcl hz⟩

omit [CompleteSpace F] in
/-- A flat primitive `α` of the coordinate expression of `φ` over a ball about the chart point of
`x`, intersected with the model range, pulled back along the chart and cut off by a bump function
supported over that ball, is a primitive of `φ` on the interior of the set where the bump function
is `1`. -/
private theorem mextDeriv_smul_mpullback_extChartAt_eq [IsManifold I ∞ M] {x : M} {ε : ℝ}
    {α : E → E [⋀^Fin k]→L[ℝ] F} {φ : RoughForm I M F (k + 1)}
    (hdα : ∀ z ∈ ball (extChartAt I x x) ε ∩ range I,
      extDerivWithin α (ball (extChartAt I x x) ε ∩ range I) z = φ.inChartAt x z)
    {χ : M → ℝ}
    (hχu : tsupport χ ⊆ (chartAt H x).source ∩ extChartAt I x ⁻¹' ball (extChartAt I x x) ε)
    (hψ : IsSmoothForm I 1
      (fun y ↦ χ y • mpullback I 𝓘(ℝ, E) (extChartAt I x) (α : RoughForm 𝓘(ℝ, E) E F k) y))
    {y : M} (hy : y ∈ interior {y | χ y = 1}) :
    mextDeriv
      (fun y ↦ χ y • mpullback I 𝓘(ℝ, E) (extChartAt I x) (α : RoughForm 𝓘(ℝ, E) E F k) y) y =
      φ y := by
  have hχy : χ y = 1 := interior_subset hy
  have hyu := hχu (subset_tsupport _ (Function.mem_support.mpr (by rw [hχy]; exact one_ne_zero)))
  obtain ⟨hys, hyb⟩ := mem_extChartAt_source_and_mem_of_mem_preimage hyu
  -- Near the chart point of `y` the bump is `1`, so the chart expression of the cut-off
  -- pullback is the flat primitive `α`.
  have hone : ∀ᶠ w in 𝓝[range I] extChartAt I x y, χ ((extChartAt I x).symm w) = 1 := by
    have h : {y | χ y = 1} ∈ 𝓝 y := mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset
    rw [← map_extChartAt_symm_nhdsWithin_range' hys] at h
    exact h
  have hψα : RoughForm.inChartAt (I := I) (fun y ↦ χ y •
      mpullback I 𝓘(ℝ, E) (extChartAt I x) (α : RoughForm 𝓘(ℝ, E) E F k) y) x
      =ᶠ[𝓝[range I] extChartAt I x y] α := by
    filter_upwards [extChartAt_target_mem_nhdsWithin' hys, hone] with w hw hw₁
    rw [RoughForm.inChartAt_fun_smul, hw₁, one_smul]
    exact RoughForm.inChartAt_mpullback_extChartAt _ x hw
  have hset : ball (extChartAt I x x) ε ∩ range I =ᶠ[𝓝 (extChartAt I x y)] range I :=
    inter_eventuallyEqSet_right.mpr (eventually_of_mem (isOpen_ball.mem_nhds hyb.1) fun _ h _ ↦ h)
  rw [← RoughForm.inChartAt_chart_eq_iff hys,
    hψ.inChartAt_mextDeriv_eq x ((extChartAt I x).map_source hys), ← hdα _ hyb,
    extDerivWithin_congr_set hset]
  exact hψα.extDerivWithin_eq (hψα.self_of_nhdsWithin hyb.2)

/-- **The Poincaré lemma on manifolds.** A `C^r` form of positive degree, `r ≥ 1`, that is closed
near a point `x` is, on a neighbourhood of `x`, the exterior derivative of a `C^r` form defined on
the whole manifold. The manifold may have boundary or corners.

The coefficient space is complete: with values in the finitely supported sequences there is a
smooth closed `1`-form on `ℝ` with no local primitive. Finite dimensionality of the model and the
Hausdorff property are used only to cut the local primitive off by a smooth bump function. -/
theorem exists_mextDeriv_eq_nhds [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    {r : ℕ∞} (hr : 1 ≤ r) {φ : RoughForm I M F (k + 1)} (hφ : IsSmoothForm I r φ) {x : M}
    (hclosed : ∀ᶠ y in 𝓝 x, mextDeriv φ y = 0) :
    ∃ U ∈ 𝓝 x, ∃ ψ : RoughForm I M F k, IsSmoothForm I r ψ ∧ ∀ y ∈ U, mextDeriv ψ y = φ y := by
  have : IsManifold I ((r : WithTop ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨ε, hε, hsub⟩ := exists_ball_inter_range_subset_extChartAt (I := I) hclosed
  obtain ⟨hα, hdα⟩ := poincareHomotopy_inChartAt hr hφ hε hsub
  obtain ⟨χ, -, hχu⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    ((isOpen_extChartAt_preimage x (isOpen_ball (x := extChartAt I x x) (ε := ε))).mem_nhds
      ⟨mem_chart_source H x, mem_ball_self hε⟩)
  have hψ := isSmoothForm_smul_mpullback_extChartAt isOpen_ball hα
    (χ.contMDiff.of_le (by exact_mod_cast le_top)) hχu
  exact ⟨interior {y | χ y = 1}, interior_mem_nhds.mpr χ.eventuallyEq_one, _, hψ, fun y hy ↦
    mextDeriv_smul_mpullback_extChartAt_eq hdα hχu (hψ.of_le (by exact_mod_cast hr)) hy⟩

/-! ### Families of closed forms -/

section Family

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]

omit [CompleteSpace F] in
/-- The Poincaré homotopy operators, centred at the chart point of `x`, of the coordinate
expressions in the chart at `x` of the slices of a `C^r` form on `N × M` are jointly `C^r` in the
chart coordinates of the slice parameter and the point, over a ball about the chart point of `x`
intersected with the model range and contained in the chart target. -/
private theorem contDiffWithinAt_poincareHomotopy_inChartAt_mpullback_prodMk [IsManifold I ∞ M]
    [IsManifold J ∞ N] {r : ℕ∞} {φ : RoughForm (J.prod I) (N × M) F (k + 1)}
    (hφ : IsSmoothForm (J.prod I) r φ) {x : M} {ε : ℝ}
    (hsub : ball (extChartAt I x x) ε ∩ range I ⊆ (extChartAt I x).target) (p₀ : N) {w : E}
    (hw : w ∈ ball (extChartAt I x x) ε ∩ range I) :
    ContDiffWithinAt ℝ r (fun X : EN × E ↦ poincareHomotopy (extChartAt I x x)
        ((mpullback I (J.prod I) (Prod.mk ((extChartAt J p₀).symm X.1)) φ).inChartAt x) X.2)
      (range J ×ˢ range I) (extChartAt J p₀ p₀, w) := by
  have : IsManifold I ((r : WithTop ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have : IsManifold J ((r : WithTop ℕ∞) + 1) N :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨t, hts, htu, htc, htn, -, -⟩ := exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt
    (I := J) p₀
  obtain ⟨hs, hsu, hc⟩ :=
    convex_uniqueDiffOn_ball_inter_range_extChartAt (I := I) x (pos_of_mem_ball hw.1)
  set s := ball (extChartAt I x x) ε ∩ range I
  -- The coordinate expressions of the slices are jointly `C^r` on the product chart target.
  have hω : ContDiffOn ℝ r (Function.uncurry fun (q : EN) (z : E) ↦
      (mpullback I (J.prod I) (Prod.mk ((extChartAt J p₀).symm q)) φ).inChartAt x z) (t ×ˢ s) :=
    (hφ.contDiffOn_inChartAt_mpullback_prodMk (p₀, x)).mono fun X hX ↦ by
      rw [extChartAt_prod, PartialEquiv.prod_target]
      exact ⟨hts hX.1, hsub hX.2⟩
  have hK := Convex.contDiffOn_uncurry_poincareHomotopy htc htu hs hsu hc hω
  have hmem : t ×ˢ s ∈ 𝓝[range J ×ˢ range I] (extChartAt J p₀ p₀, w) := by
    rw [nhdsWithin_prod_eq]
    exact prod_mem_prod htn
      (inter_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hw.1)) self_mem_nhdsWithin)
  exact (hK _ ⟨mem_of_mem_nhdsWithin (extChartAt_target_subset_range p₀
    (mem_extChartAt_target p₀)) htn, hw⟩).mono_of_mem_nhdsWithin hmem

/-- **The Poincaré lemma for smooth families of forms.** Let `φ` be a `C^r` form of positive
degree on `N × M`, `r ≥ 1`, whose slices `ι_p^* φ`, along the inclusions `ι_p : y ↦ (p, y)`, are
closed near `x` uniformly in `p`. Then there are a neighbourhood `U` of `x` and a family `σ` of
forms on `M`, jointly `C^r` in the sense that its vertical form on `N × M` is `C^r`, such that
`d (σ p) = ι_p^* φ` on `U` and `σ p` vanishes at `x`, for every `p`.

The parameter manifold `N` is arbitrary, and `M` may have boundary or corners. -/
theorem exists_mextDeriv_eq_mpullback_prodMk_nhds [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I ∞ M] [IsManifold J ∞ N] {r : ℕ∞} (hr : 1 ≤ r)
    {φ : RoughForm (J.prod I) (N × M) F (k + 1)} (hφ : IsSmoothForm (J.prod I) r φ) {x : M}
    (hclosed : ∀ᶠ y in 𝓝 x, ∀ p, mextDeriv (mpullback I (J.prod I) (Prod.mk p) φ) y = 0) :
    ∃ U ∈ 𝓝 x, ∃ σ : N → RoughForm I M F k, IsSmoothForm (J.prod I) r (verticalForm J σ) ∧
      (∀ p, ∀ y ∈ U, mextDeriv (σ p) y = mpullback I (J.prod I) (Prod.mk p) φ y) ∧
      ∀ p, σ p x = 0 := by
  have : IsManifold I ((r : WithTop ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have : IsManifold J ((r : WithTop ℕ∞) + 1) N :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  obtain ⟨ε, hε, hsub⟩ := exists_ball_inter_range_subset_extChartAt (I := I) hclosed
  -- The slices are `C^r`, and over the ball each has the flat primitive `K p`.
  have hslice (p : N) : IsSmoothForm I r (mpullback I (J.prod I) (Prod.mk p) φ) :=
    hφ.mpullback ((contMDiff_const.prodMk contMDiff_id).of_le le_top)
  have hK (p : N) := poincareHomotopy_inChartAt hr (hslice p) hε fun z hz ↦
    ⟨(hsub hz).1, (hsub hz).2 p⟩
  set K : N → E → E [⋀^Fin k]→L[ℝ] F := fun p ↦ poincareHomotopy (extChartAt I x x)
    ((mpullback I (J.prod I) (Prod.mk p) φ).inChartAt x)
  -- Each `σ p` is `K p` pulled back along the chart and cut off by one bump function for all `p`.
  obtain ⟨χ, -, hχu⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    ((isOpen_extChartAt_preimage x (isOpen_ball (x := extChartAt I x x) (ε := ε))).mem_nhds
      ⟨mem_chart_source H x, mem_ball_self hε⟩)
  have hχ : ContMDiff I 𝓘(ℝ) r χ := χ.contMDiff.of_le (by exact_mod_cast le_top)
  refine ⟨interior {y | χ y = 1}, interior_mem_nhds.mpr χ.eventuallyEq_one,
    fun p y ↦ χ y • mpullback I 𝓘(ℝ, E) (extChartAt I x) (K p : RoughForm 𝓘(ℝ, E) E F k) y,
    isSmoothForm_verticalForm_smul_mpullback_extChartAt isOpen_ball (fun p₀ w hw ↦
      contDiffWithinAt_poincareHomotopy_inChartAt_mpullback_prodMk hφ (fun z hz ↦ (hsub hz).1)
        p₀ hw) hχ hχu,
    fun p y hy ↦ mextDeriv_smul_mpullback_extChartAt_eq (hK p).2 hχu
      ((isSmoothForm_smul_mpullback_extChartAt isOpen_ball (hK p).1 hχ hχu).of_le
        (by exact_mod_cast hr)) hy,
    fun p ↦ ?_⟩
  -- The Poincaré homotopy operator vanishes at its centre, the chart point of `x`.
  have h0 : mpullback I 𝓘(ℝ, E) (extChartAt I x) (K p : RoughForm 𝓘(ℝ, E) E F k) x = 0 := by
    ext v
    refine (mpullback_apply _ _ x v).trans ?_
    simp only [K, poincareHomotopy_self]
    -- The zero alternating map of the model fibre takes the value `0`; the fibre of the trivial
    -- value bundle is `F` by definition, which the `simp` lemma for `0` does not see through.
    rfl
  dsimp only
  simp only [h0, smul_zero]

end Family

end TauCeti
