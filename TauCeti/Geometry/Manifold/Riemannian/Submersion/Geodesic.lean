/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.AlongCurve
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Uniqueness
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Hom
import TauCeti.Analysis.ODE.Gronwall

/-!
# Horizontal geodesics and horizontal lifting under Riemannian submersions

For a Riemannian submersion `f : M → N` between smooth Riemannian manifolds, this file develops the
interaction between geodesics in the total space `M` and geodesics in the base `N`:

1. **Horizontal curves and acceleration.** A `C²` curve in `M` whose velocity is everywhere
   horizontal is a geodesic if and only if its projection `f ∘ γ` is a geodesic in `N`
   (`isGeodesicCurveOn_iff_comp`).
2. **Horizontal invariance of geodesics.** Along any geodesic `γ` in `M`, the squared norm of the
   vertical velocity `Q γ'` satisfies `(d/dt) ‖Q γ'‖² = 2 ⟪P γ', T_{Q γ'}(Q γ')⟫`
   (`hasDerivWithinAt_norm_starProjection_ker_curveVelocityWithin_sq`). Consequently, any geodesic
   on a preconnected parameter set which is horizontal at one parameter remains horizontal
   everywhere (`mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn`) and projects to a base
   geodesic of the same speed and Riemannian path length
   (`isGeodesicCurveOn_comp_of_mem_orthogonal_ker`, `pathELength_comp_eq_of_isGeodesicCurveOn`).
3. **Exponential map and geodesic completeness.** For any horizontal vector `v ∈ T_p M` (and in
   particular any lifted vector `horizontalLift p w`), `f` maps the maximal geodesic interval at
   `(p, v)` into that at `(f p, df_p v)` (`geodesicInterval_subset_geodesicInterval_mfderiv`,
   `geodesicInterval_horizontalLift_subset`), pushes geodesic completeness at `p` forward to `f p`
   (`isGeodesicallyCompleteAt`), and intertwines `maximalGeodesic` and `riemannianExp`
   (`map_maximalGeodesic_of_mem`, `map_riemannianExp_of_mem`,
   `map_maximalGeodesic_horizontalLift`, `map_riemannianExp_horizontalLift`).
4. **Horizontal lifting of base geodesics.** On a boundaryless Hausdorff total space `M`, horizontal
   geodesic lifts of a base geodesic through a prescribed point in the fibre are unique on any
   preconnected parameter set (`eqOn_of_isGeodesicCurveOn_horizontalLift`), exist locally around any
   interior parameter (`exists_Ioo_isGeodesicCurveOn_horizontalLift`), and exist globally on `ℝ`
   whenever `M` is geodesically complete at the starting point (in particular when `M` is metrically
   complete, `exists_isGeodesicCurve_horizontalLift_of_completeSpace`).

## Main results

* `TauCeti.IsRiemannianSubmersion.isGeodesicCurveOn_iff_comp`,
  `TauCeti.IsRiemannianSubmersion.isGeodesicCurve_iff_comp`: a `C²` horizontal curve is a geodesic
  if and only if its projection is a geodesic.
* `TauCeti.IsRiemannianSubmersion.hasDerivWithinAt_norm_starProjection_ker_curveVelocityWithin_sq`:
  derivative of the squared vertical speed along any geodesic in terms of `oneillT`.
* `TauCeti.IsRiemannianSubmersion.mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn`,
  `TauCeti.IsRiemannianSubmersion.mem_orthogonal_ker_curveVelocity_of_isGeodesicCurve`: horizontal
  invariance of geodesics on preconnected parameter sets.
* `TauCeti.IsRiemannianSubmersion.isGeodesicCurveOn_comp_of_mem_orthogonal_ker`,
  `TauCeti.IsRiemannianSubmersion.isGeodesicCurveOnFrom_comp_horizontalLift`: horizontal geodesics
  project to base geodesics with projected initial data.
* `TauCeti.IsRiemannianSubmersion.geodesicInterval_horizontalLift_subset`,
  `TauCeti.IsRiemannianSubmersion.isGeodesicallyCompleteAt`,
  `TauCeti.IsRiemannianSubmersion.map_maximalGeodesic_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.map_riemannianExp_horizontalLift`: maximal intervals, geodesic
  completeness, and naturality of the exponential map on horizontal vectors.
* `TauCeti.IsRiemannianSubmersion.eqOn_of_isGeodesicCurveOn_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.exists_Ioo_isGeodesicCurveOn_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.exists_isGeodesicCurve_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.exists_isGeodesicCurve_horizontalLift_of_completeSpace`:
  uniqueness and local/global existence of horizontal geodesic lifts of base geodesics.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966), 459–469,
  Corollary 2.
* A. L. Besse, *Einstein Manifolds*, Ergebnisse der Mathematik und ihrer Grenzgebiete (3) 10,
  Springer-Verlag (1987), Chapter 9, §C (9.28–9.30).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 5–6.
-/

public section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

/-! ### Horizontal curves, horizontal invariance, and projected geodesics -/

section HorizontalInvariance

include h

/-- A `C²` curve in `M` whose velocity is horizontal at every parameter of `s` is a geodesic on `s`
if and only if its projection `f ∘ γ` is a geodesic on `s`. -/
theorem isGeodesicCurveOn_iff_comp {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s)
    (hhor : ∀ r ∈ s, curveVelocityWithin I γ s r ∈ (mfderiv I J f (γ r)).kerᗮ) :
    IsGeodesicCurveOn I γ s ↔ IsGeodesicCurveOn J (f ∘ γ) s := by
  refine ⟨fun hgeo ↦ ⟨hgeo.uniqueDiffOn,
    (h.isSubmersion.contMDiff.of_le (by norm_num)).comp_contMDiffOn hγ, fun t ht ↦
      (h.accelerationWithin_eq_zero_iff_comp hgeo.uniqueDiffOn hγ hhor ht).mp
        (hgeo.accelerationWithin_eq_zero t ht)⟩,
    fun hgeo ↦ ⟨hgeo.uniqueDiffOn, hγ, fun t ht ↦
      (h.accelerationWithin_eq_zero_iff_comp hgeo.uniqueDiffOn hγ hhor ht).mpr
        (hgeo.accelerationWithin_eq_zero t ht)⟩⟩

/-- A globally `C²` horizontal curve in `M` is an all-time geodesic if and only if its projection
`f ∘ γ` is an all-time geodesic in `N`. -/
theorem isGeodesicCurve_iff_comp {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    (hhor : ∀ r, curveVelocity I γ r ∈ (mfderiv I J f (γ r)).kerᗮ) :
    IsGeodesicCurve I γ ↔ IsGeodesicCurve J (f ∘ γ) := by
  rw [← isGeodesicCurveOn_univ, ← isGeodesicCurveOn_univ]
  exact h.isGeodesicCurveOn_iff_comp hγ.contMDiffOn
    fun r _ ↦ by rw [curveVelocityWithin_univ]; exact hhor r

/-- Along any geodesic `γ` on `s`, the squared norm of the vertical component `Q γ'` of its
velocity has derivative `2 ⟪P γ', T_{Q γ'}(Q γ')⟫` within `s`, where `P` and `Q` are the
horizontal and vertical orthogonal projections. -/
theorem hasDerivWithinAt_norm_starProjection_ker_curveVelocityWithin_sq
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} (hγ : IsGeodesicCurveOn I γ s) (ht : t ∈ s) :
    HasDerivWithinAt
      (fun r ↦ ‖(mfderiv I J f (γ r)).ker.starProjection (curveVelocityWithin I γ s r)‖ ^ 2)
      (2 * ⟪(mfderiv I J f (γ t)).kerᗮ.starProjection (curveVelocityWithin I γ s t),
        h.oneillT (γ t) ((mfderiv I J f (γ t)).ker.starProjection (curveVelocityWithin I γ s t))
          ((mfderiv I J f (γ t)).ker.starProjection (curveVelocityWithin I γ s t))⟫_ℝ) s t := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set V := curveVelocityWithin I γ s
  set P : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x ↦ (mfderiv I J f x).kerᗮ.starProjection
  set Q : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x ↦ (mfderiv I J f x).ker.starProjection
  -- Step 1: bundle-coordinate differentiability of `V` and its vertical component `Q V`.
  have hs : UniqueDiffWithinAt ℝ s t := hγ.uniqueDiffOn t ht
  have hγd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t := hγ.mdifferentiableOn t ht
  have hVt : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t := by
    have hlift := (hγ.contMDiffOn.contMDiffOn_curveVelocityLiftWithin (m := 1) (by norm_num)
      hγ.uniqueDiffOn.uniqueMDiffOn).mdifferentiableOn one_ne_zero t ht
    exact hlift.congr (fun r _ ↦ (curveVelocityLiftWithin_apply (I := I) γ s r).symm)
      (curveVelocityLiftWithin_apply (I := I) γ s t).symm
  have hVcoord : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t :=
    differentiableWithinAt_sectionCoord_curveVelocityWithin γ hγ.uniqueDiffOn hγ.contMDiffOn ht
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hQVeq (r : ℝ) : Q (γ r) (V r) =
      V r - h.horizontalLift (γ r) (mfderiv I J f (γ r) (V r)) := by
    simp only [Q, h.horizontalLift_mfderiv, Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply, sub_sub_cancel]
  have hQVcoord : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ Q (γ r) (V r)) (γ t)) s t := by
    have hfV := h.isSubmersion.contMDiff.contMDiffAt.differentiableWithinAt_sectionCoord_mfderiv
      (by simp) hγd hVcoord
    have hQVfun : (fun r ↦ Q (γ r) (V r)) =
        fun r ↦ V r - h.horizontalLift (γ r) (mfderiv I J f (γ r) (V r)) := funext hQVeq
    rw [hQVfun, sectionCoord_sub]
    exact hVcoord.sub (h.differentiableWithinAt_sectionCoord_horizontalLift hγd hfV)
  -- Step 2: compute `D_t (Q V)` via the `Hom` Leibniz rule and O'Neill tensor identities.
  have hQd := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := γ t)
  have hclm := CovariantDerivative.alongCurveWithin_clm_apply
    (leviCivitaConnection I M) γ V Q hs hQd hVt
  rw [← accelerationWithin_def, hγ.accelerationWithin_eq_zero t ht, map_zero, add_zero,
    h.hom_starProjection_ker_apply] at hclm
  have hsplit : V t = P (γ t) (V t) + Q (γ t) (V t) := by
    simp only [P, Q, Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply, sub_add_cancel]
  have hQA : Q (γ t) (h.oneillA (γ t) (V t) (V t)) = 0 := by
    have hAV : h.oneillA (γ t) (V t) (V t) =
        h.oneillA (γ t) (P (γ t) (V t)) (Q (γ t) (V t)) := by
      calc h.oneillA (γ t) (V t) (V t)
          = h.oneillA (γ t) (P (γ t) (V t) + Q (γ t) (V t)) (V t) :=
            congrArg (fun u ↦ h.oneillA (γ t) u (V t)) hsplit
        _ = h.oneillA (γ t) (P (γ t) (V t)) (P (γ t) (V t) + Q (γ t) (V t)) := by
            rw [map_add, add_apply, h.oneillA_starProjection_ker, zero_apply, add_zero, ← hsplit]
        _ = h.oneillA (γ t) (P (γ t) (V t)) (Q (γ t) (V t)) := by
            rw [map_add, h.oneillA_self (Submodule.starProjection_apply_mem _ _), zero_add]
    rw [hAV]
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (h.oneillA_apply_mem_orthogonal_ker _ (Submodule.starProjection_apply_mem _ _))
  have hQT : Q (γ t) (h.oneillT (γ t) (V t) (V t)) =
      h.oneillT (γ t) (Q (γ t) (V t)) (P (γ t) (V t)) := by
    have hTV : h.oneillT (γ t) (V t) (V t) =
        h.oneillT (γ t) (Q (γ t) (V t)) (P (γ t) (V t)) +
          h.oneillT (γ t) (Q (γ t) (V t)) (Q (γ t) (V t)) := by
      calc h.oneillT (γ t) (V t) (V t)
          = h.oneillT (γ t) (P (γ t) (V t) + Q (γ t) (V t)) (V t) :=
            congrArg (fun u ↦ h.oneillT (γ t) u (V t)) hsplit
        _ = h.oneillT (γ t) (Q (γ t) (V t)) (P (γ t) (V t) + Q (γ t) (V t)) := by
            rw [map_add, add_apply, h.oneillT_starProjection_orthogonal_ker, zero_apply,
              zero_add, ← hsplit]
        _ = _ := map_add _ _ _
    rw [hTV, map_add,
      Submodule.starProjection_eq_self_iff.mpr
        (h.oneillT_apply_mem_ker _ (Submodule.starProjection_apply_mem _ _)),
      (Submodule.starProjection_apply_eq_zero_iff _).mpr
        (h.oneillT_apply_mem_orthogonal_ker _ (Submodule.starProjection_apply_mem _ _)),
      add_zero]
  have hinner : ⟪alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ Q (γ r) (V r)) s t,
      Q (γ t) (V t)⟫_ℝ =
      ⟪P (γ t) (V t), h.oneillT (γ t) (Q (γ t) (V t)) (Q (γ t) (V t))⟫_ℝ := by
    have hPQ0 : ⟪P (γ t) (h.oneillA (γ t) (V t) (V t) + h.oneillT (γ t) (V t) (V t)),
        Q (γ t) (V t)⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal' _ _).mp (Submodule.starProjection_apply_mem _ _) _
        (Submodule.starProjection_apply_mem _ _)
    rw [hclm, inner_sub_left, hPQ0, map_add, hQA, zero_add, hQT, zero_sub, h.inner_oneillT,
      neg_neg]
  -- Step 3: differentiate `‖Q V‖² = ⟪Q V, Q V⟫` using metric compatibility.
  have hd := (isLeviCivitaConnection_leviCivitaConnection I (M := M)).isMetricCompatible
    |>.hasDerivWithinAt_inner_alongCurveWithin hγd hQVcoord hQVcoord
  rw [real_inner_comm _ (Q (γ t) (V t)), hinner, ← two_mul] at hd
  simpa only [real_inner_self_eq_norm_sq] using hd

/-- **Horizontal invariance of geodesics.** If a geodesic `γ` on a preconnected parameter set `s`
has horizontal velocity at one parameter `t₀ ∈ s`, then its velocity is horizontal at every
parameter `t ∈ s`. Neither completeness, boundarylessness, nor Hausdorffness is assumed. -/
theorem mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn
    {γ : ℝ → M} {s : Set ℝ} {t₀ t : ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    (ht₀ : t₀ ∈ s) (hhor : curveVelocityWithin I γ s t₀ ∈ (mfderiv I J f (γ t₀)).kerᗮ)
    (ht : t ∈ s) :
    curveVelocityWithin I γ s t ∈ (mfderiv I J f (γ t)).kerᗮ := by
  rcases eq_or_ne t t₀ with rfl | htt₀
  · exact hhor
  -- Restrict to the compact subinterval `[min t₀ t, max t₀ t]` where `oneillT` is bounded.
  let a := min t₀ t
  let b := max t₀ t
  have hab : a < b := min_lt_max.mpr htt₀.symm
  have hsub : Icc a b ⊆ s :=
    hs.Icc_subset (min_rec' (· ∈ s) ht₀ ht) (max_rec' (· ∈ s) ht₀ ht)
  have huIcc : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hγIcc : IsGeodesicCurveOn I γ (Icc a b) := hγ.mono huIcc hsub
  have hveq (r : ℝ) (hr : r ∈ Icc a b) :
      curveVelocityWithin I γ (Icc a b) r = curveVelocityWithin I γ s r :=
    curveVelocityWithin_subset hsub (huIcc r hr) (hγ.mdifferentiableOn r (hsub hr))
  have hK : IsCompact (γ '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (hγIcc.contMDiffOn.continuousOn)
  obtain ⟨C, _, hC⟩ := h.exists_norm_oneillT_le_of_isCompact hK
  -- Apply the two-sided Grönwall uniqueness estimate to `g r = ‖Q (γ r) (V r)‖ ^ 2`.
  let Q : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x ↦ (mfderiv I J f x).ker.starProjection
  let P : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x ↦ (mfderiv I J f x).kerᗮ.starProjection
  set V := curveVelocityWithin I γ (Icc a b)
  let g : ℝ → ℝ := fun r ↦ ‖Q (γ r) (V r)‖ ^ 2
  let g' : ℝ → ℝ := fun r ↦ 2 * ⟪P (γ r) (V r), h.oneillT (γ r) (Q (γ r) (V r)) (Q (γ r) (V r))⟫_ℝ
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have ht₀Icc : t₀ ∈ Icc a b := ⟨min_le_left t₀ t, le_max_left t₀ t⟩
  have htIcc : t ∈ Icc a b := ⟨min_le_right t₀ t, le_max_right t₀ t⟩
  have hgderiv (r : ℝ) (hr : r ∈ Icc a b) : HasDerivWithinAt g (g' r) (Icc a b) r :=
    h.hasDerivWithinAt_norm_starProjection_ker_curveVelocityWithin_sq hγIcc hr
  have hgbound (r : ℝ) (hr : r ∈ Icc a b) : ‖g' r‖ ≤ (2 * ‖V a‖ * C) * ‖g r‖ := by
    have hPV : ‖P (γ r) (V r)‖ ≤ ‖V a‖ :=
      (Submodule.norm_starProjection_apply_le _ _).trans
        (hγIcc.norm_curveVelocityWithin_eq isPreconnected_Icc hr ha).le
    have hTle : ‖h.oneillT (γ r) (Q (γ r) (V r)) (Q (γ r) (V r))‖ ≤ C * ‖Q (γ r) (V r)‖ ^ 2 := by
      simpa only [sq, mul_assoc] using hC (γ r) ⟨r, hr, rfl⟩ (Q (γ r) (V r)) (Q (γ r) (V r))
    calc ‖g' r‖
        = 2 * ‖⟪P (γ r) (V r), h.oneillT (γ r) (Q (γ r) (V r)) (Q (γ r) (V r))⟫_ℝ‖ := by
          simp only [g', norm_mul, Real.norm_ofNat]
      _ ≤ 2 * (‖P (γ r) (V r)‖ * ‖h.oneillT (γ r) (Q (γ r) (V r)) (Q (γ r) (V r))‖) := by
          gcongr
          exact norm_inner_le_norm _ _
      _ ≤ 2 * (‖V a‖ * (C * ‖Q (γ r) (V r)‖ ^ 2)) := by gcongr
      _ = (2 * ‖V a‖ * C) * ‖g r‖ := by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          ring
  have hgt₀ : g t₀ = 0 := by
    have hQ0 : Q (γ t₀) (V t₀) = 0 := by
      rw [hveq t₀ ht₀Icc]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hhor
    simp [g, hQ0]
  have hgt : g t = 0 :=
    eq_zero_of_norm_deriv_le_mul_norm_self_of_mem_Icc hgderiv hgbound ht₀Icc hgt₀ t htIcc
  have hQt : Q (γ t) (V t) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hgt)
  rw [← hveq t htIcc]
  exact (Submodule.starProjection_apply_eq_zero_iff _).mp hQt

/-- **Horizontal invariance of all-time geodesics.** An all-time geodesic in `M` whose velocity is
horizontal at one parameter `t₀` has horizontal velocity at every parameter `t`. -/
theorem mem_orthogonal_ker_curveVelocity_of_isGeodesicCurve
    {γ : ℝ → M} {t₀ : ℝ} (hγ : IsGeodesicCurve I γ)
    (hhor : curveVelocity I γ t₀ ∈ (mfderiv I J f (γ t₀)).kerᗮ) (t : ℝ) :
    curveVelocity I γ t ∈ (mfderiv I J f (γ t)).kerᗮ := by
  rw [← isGeodesicCurveOn_univ] at hγ
  rw [← curveVelocityWithin_univ] at hhor ⊢
  exact h.mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn hγ isPreconnected_univ
    (mem_univ t₀) hhor (mem_univ t)

/-- A geodesic on a preconnected parameter set `s` whose velocity is horizontal at one parameter
`t₀ ∈ s` projects to a geodesic in `N` on `s`. -/
theorem isGeodesicCurveOn_comp_of_mem_orthogonal_ker
    {γ : ℝ → M} {s : Set ℝ} {t₀ : ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    (ht₀ : t₀ ∈ s) (hhor : curveVelocityWithin I γ s t₀ ∈ (mfderiv I J f (γ t₀)).kerᗮ) :
    IsGeodesicCurveOn J (f ∘ γ) s :=
  (h.isGeodesicCurveOn_iff_comp hγ.contMDiffOn fun _ hr ↦
    h.mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn hγ hs ht₀ hhor hr).mp hγ

/-- An all-time geodesic in `M` whose velocity is horizontal at one parameter projects to an
all-time geodesic in `N`. -/
theorem isGeodesicCurve_comp_of_mem_orthogonal_ker
    {γ : ℝ → M} {t₀ : ℝ} (hγ : IsGeodesicCurve I γ)
    (hhor : curveVelocity I γ t₀ ∈ (mfderiv I J f (γ t₀)).kerᗮ) :
    IsGeodesicCurve J (f ∘ γ) :=
  (h.isGeodesicCurve_iff_comp
    (contMDiffOn_univ.mp (isGeodesicCurveOn_univ.mpr hγ).contMDiffOn) fun r ↦
      h.mem_orthogonal_ker_curveVelocity_of_isGeodesicCurve hγ hhor r).mp hγ

/-- If a geodesic `γ` on `[a, b]` has horizontal velocity at some `t₀ ∈ [a, b]`, its projection
`f ∘ γ` has the same `Manifold.pathELength` on `[a, b]` as `γ`. -/
theorem pathELength_comp_eq_of_isGeodesicCurveOn
    {γ : ℝ → M} {a b t₀ : ℝ} (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (ht₀ : t₀ ∈ Icc a b)
    (hhor : curveVelocityWithin I γ (Icc a b) t₀ ∈ (mfderiv I J f (γ t₀)).kerᗮ) :
    Manifold.pathELength J (f ∘ γ) a b = Manifold.pathELength I γ a b := by
  refine h.pathELength_comp_eq_of_mem_orthogonal_ker
    (hγ.mdifferentiableOn.mono Ioo_subset_Icc_self) fun r hr ↦ ?_
  rw [← curveVelocityWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)]
  exact h.mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn hγ isPreconnected_Icc
    ht₀ hhor (Ioo_subset_Icc_self hr)

/-- A geodesic from `(p, v)` on a preconnected parameter set `s` with horizontal initial velocity
`v` projects to a geodesic in `N` on `s` from `(f p, df_p v)`. -/
theorem isGeodesicCurveOnFrom_comp_of_mem_orthogonal_ker
    {γ : ℝ → M} {s : Set ℝ} {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicCurveOnFrom I γ s p v) (hs : IsPreconnected s)
    (hv : v ∈ (mfderiv I J f p).kerᗮ) :
    IsGeodesicCurveOnFrom J (f ∘ γ) s (f p) (mfderiv I J f p v) := by
  have hp : γ 0 = p := hγ.base_eq
  subst hp
  have hv0 : curveVelocityWithin I γ s 0 = v := TotalSpace.mk_inj.mp hγ.initial_eq
  refine ⟨h.isGeodesicCurveOn_comp_of_mem_orthogonal_ker hγ.isGeodesicCurveOn hs hγ.zero_mem
    (hv0.symm ▸ hv), hγ.zero_mem, ?_⟩
  rw [Function.comp_apply,
    curveVelocityWithin_map (h.isSubmersion.contMDiff.mdifferentiableAt (by simp))
      (hγ.isGeodesicCurveOn.uniqueDiffOn 0 hγ.zero_mem)
      (hγ.isGeodesicCurveOn.mdifferentiableOn 0 hγ.zero_mem),
    hv0]

/-- A geodesic from `(p, horizontalLift p w)` on a preconnected parameter set `s` projects to a
geodesic in `N` on `s` from `(f p, w)`. -/
theorem isGeodesicCurveOnFrom_comp_horizontalLift
    {γ : ℝ → M} {s : Set ℝ} {p : M} {w : TangentSpace J (f p)}
    (hγ : IsGeodesicCurveOnFrom I γ s p (h.horizontalLift p w)) (hs : IsPreconnected s) :
    IsGeodesicCurveOnFrom J (f ∘ γ) s (f p) w := by
  simpa only [h.mfderiv_horizontalLift] using
    h.isGeodesicCurveOnFrom_comp_of_mem_orthogonal_ker hγ hs
      (h.horizontalLift_mem_orthogonal_ker p w)

end HorizontalInvariance

/-! ### Maximal geodesic intervals, exponential map, and geodesic completeness -/

section MaximalAndExponential

include h

/-- For a horizontal vector `v ∈ T_p M`, a Riemannian submersion maps the maximal geodesic
interval at `(p, v)` into the maximal geodesic interval at `(f p, df_p v)`. -/
theorem geodesicInterval_subset_geodesicInterval_mfderiv {p : M} {v : TangentSpace I p}
    (hv : v ∈ (mfderiv I J f p).kerᗮ) :
    geodesicInterval I M p v ⊆ geodesicInterval J N (f p) (mfderiv I J f p v) := by
  intro t ht
  obtain ⟨γ, a, b, hγ, ht'⟩ := (mem_geodesicInterval_iff (I := I) (M := M)).mp ht
  exact (mem_geodesicInterval_iff (I := J) (M := N)).mpr
    ⟨f ∘ γ, a, b, h.isGeodesicCurveOnFrom_comp_of_mem_orthogonal_ker hγ isPreconnected_Ioo hv, ht'⟩

/-- Horizontal lifting at `p` maps the maximal geodesic interval at `(p, horizontalLift p w)` into
the maximal geodesic interval at `(f p, w)`. -/
theorem geodesicInterval_horizontalLift_subset (p : M) (w : TangentSpace J (f p)) :
    geodesicInterval I M p (h.horizontalLift p w) ⊆ geodesicInterval J N (f p) w := by
  simpa only [h.mfderiv_horizontalLift] using
    h.geodesicInterval_subset_geodesicInterval_mfderiv (h.horizontalLift_mem_orthogonal_ker p w)

/-- If a horizontal vector `v ∈ T_p M` lies in `expDomain I M p`, then `df_p v` lies in
`expDomain J N (f p)`. -/
theorem mfderiv_mem_expDomain {p : M} {v : TangentSpace I p}
    (hv : v ∈ expDomain I M p) (hhor : v ∈ (mfderiv I J f p).kerᗮ) :
    mfderiv I J f p v ∈ expDomain J N (f p) :=
  mem_expDomain_iff.mpr
    (h.geodesicInterval_subset_geodesicInterval_mfderiv hhor (mem_expDomain_iff.mp hv))

/-- If `horizontalLift p w` lies in the natural domain of `riemannianExp` at `p`, then `w` lies in
the natural domain of `riemannianExp` at `f p`. -/
theorem mem_expDomain_of_horizontalLift_mem {p : M} {w : TangentSpace J (f p)}
    (hw : h.horizontalLift p w ∈ expDomain I M p) :
    w ∈ expDomain J N (f p) := by
  simpa only [h.mfderiv_horizontalLift] using
    h.mfderiv_mem_expDomain hw (h.horizontalLift_mem_orthogonal_ker p w)

/-- If `M` is geodesically complete at `p`, then `N` is geodesically complete at `f p`. -/
theorem isGeodesicallyCompleteAt {p : M} (hp : IsGeodesicallyCompleteAt I M p) :
    IsGeodesicallyCompleteAt J N (f p) :=
  isGeodesicallyCompleteAt_iff_forall_one_mem_geodesicInterval.mpr fun w ↦
    h.geodesicInterval_horizontalLift_subset p w
      (hp.geodesicInterval_eq_univ (h.horizontalLift p w) ▸ mem_univ 1)

/-- A surjective Riemannian submersion from a geodesically complete manifold has a geodesically
complete base. -/
theorem forall_isGeodesicallyCompleteAt_of_surjective (hsurj : Function.Surjective f)
    (hM : ∀ p : M, IsGeodesicallyCompleteAt I M p) :
    ∀ q : N, IsGeodesicallyCompleteAt J N q := fun q ↦ by
  obtain ⟨p, rfl⟩ := hsurj q
  exact h.isGeodesicallyCompleteAt (hM p)

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] h in
/-- If the total space `M` of a Riemannian submersion is metrically complete for its Riemannian
distance, then the base `N` is geodesically complete at `f p` for every `p : M`. -/
theorem isGeodesicallyCompleteAt_of_completeSpace_source
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    {f : M → N} (h : IsRiemannianSubmersion I J f) (p : M) :
    IsGeodesicallyCompleteAt J N (f p) :=
  h.isGeodesicallyCompleteAt (isGeodesicallyCompleteAt_of_completeSpace p)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ F]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] h in
private theorem mem_orthogonal_ker_of_totalSpace_eq {x p : M}
    {u : TangentSpace I x} {v : TangentSpace I p}
    (heq : TotalSpace.mk' E x u = TotalSpace.mk' E p v)
    (hv : v ∈ (mfderiv I J f p).kerᗮ) :
    u ∈ (mfderiv I J f x).kerᗮ := by
  have hp : x = p := congrArg TotalSpace.proj heq
  subst hp
  rwa [TotalSpace.mk_inj.mp heq]

/-- On its maximal interval of definition, the maximal geodesic from `p` with horizontal initial
velocity `v` has horizontal velocity everywhere. -/
theorem mem_orthogonal_ker_curveVelocityWithin_maximalGeodesic
    [I.Boundaryless] [T2Space M] {p : M} {v : TangentSpace I p} {t : ℝ}
    (hv : v ∈ (mfderiv I J f p).kerᗮ) (ht : t ∈ geodesicInterval I M p v) :
    curveVelocityWithin I (maximalGeodesic I M p v) (geodesicInterval I M p v) t ∈
      (mfderiv I J f (maximalGeodesic I M p v t)).kerᗮ := by
  have hmax := isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v
  exact h.mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn hmax.isGeodesicCurveOn
    isPreconnected_geodesicInterval hmax.zero_mem
    (mem_orthogonal_ker_of_totalSpace_eq hmax.initial_eq hv) ht

/-- On its maximal interval of definition, the maximal geodesic from `p` with initial velocity
`horizontalLift p w` has horizontal velocity everywhere. -/
theorem mem_orthogonal_ker_curveVelocityWithin_maximalGeodesic_horizontalLift
    [I.Boundaryless] [T2Space M] {p : M} {w : TangentSpace J (f p)} {t : ℝ}
    (ht : t ∈ geodesicInterval I M p (h.horizontalLift p w)) :
    curveVelocityWithin I (maximalGeodesic I M p (h.horizontalLift p w))
      (geodesicInterval I M p (h.horizontalLift p w)) t ∈
      (mfderiv I J f (maximalGeodesic I M p (h.horizontalLift p w) t)).kerᗮ :=
  h.mem_orthogonal_ker_curveVelocityWithin_maximalGeodesic
    (h.horizontalLift_mem_orthogonal_ker p w) ht

/-- Projecting the maximal geodesic from `(p, horizontalLift p w)` gives a geodesic in `N` from
`(f p, w)` on the source maximal geodesic interval. -/
theorem isGeodesicCurveOnFrom_comp_maximalGeodesic_horizontalLift
    [I.Boundaryless] [T2Space M] (p : M) (w : TangentSpace J (f p)) :
    IsGeodesicCurveOnFrom J (f ∘ maximalGeodesic I M p (h.horizontalLift p w))
      (geodesicInterval I M p (h.horizontalLift p w)) (f p) w :=
  h.isGeodesicCurveOnFrom_comp_horizontalLift
    (isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p (h.horizontalLift p w))
    isPreconnected_geodesicInterval

/-- Any open-interval geodesic in `M` from `(p, v)` with horizontal initial velocity `v` projects
to the maximal geodesic in `N` from `(f p, df_p v)` on that interval. -/
theorem map_maximalGeodesic_eq_of_isGeodesicCurveOnFrom
    [J.Boundaryless] [T2Space N] {γ : ℝ → M} {a b t : ℝ} {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v) (hv : v ∈ (mfderiv I J f p).kerᗮ)
    (ht : t ∈ Ioo a b) :
    f (γ t) = maximalGeodesic J N (f p) (mfderiv I J f p v) t :=
  ((h.isGeodesicCurveOnFrom_comp_of_mem_orthogonal_ker hγ isPreconnected_Ioo hv)
    |>.eqOn_maximalGeodesic ht).symm

/-- Any open-interval geodesic in `M` from `(p, horizontalLift p w)` projects to the maximal
geodesic in `N` from `(f p, w)` on that interval. -/
theorem map_maximalGeodesic_eq_of_isGeodesicCurveOnFrom_horizontalLift
    [J.Boundaryless] [T2Space N] {γ : ℝ → M} {a b t : ℝ} {p : M} {w : TangentSpace J (f p)}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p (h.horizontalLift p w)) (ht : t ∈ Ioo a b) :
    f (γ t) = maximalGeodesic J N (f p) w t := by
  simpa only [h.mfderiv_horizontalLift] using
    h.map_maximalGeodesic_eq_of_isGeodesicCurveOnFrom hγ
      (h.horizontalLift_mem_orthogonal_ker p w) ht

/-- A Riemannian submersion intertwines maximal geodesics along any horizontal initial velocity at
every parameter in the source maximal geodesic interval. -/
theorem map_maximalGeodesic_of_mem [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {p : M} {v : TangentSpace I p} {t : ℝ} (hv : v ∈ (mfderiv I J f p).kerᗮ)
    (ht : t ∈ geodesicInterval I M p v) :
    f (maximalGeodesic I M p v t) = maximalGeodesic J N (f p) (mfderiv I J f p v) t := by
  rw [← maximalIntegralCurveInterval_geodesicSpray] at ht
  obtain ⟨z, a, b, hz, hz0, h0, ht', heq⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
  rw [maximalGeodesic_def (I := I), heq]
  exact h.map_maximalGeodesic_eq_of_isGeodesicCurveOnFrom
    (hz.isGeodesicCurveOnFrom_proj (uniqueDiffOn_Ioo a b) h0 hz0) hv ht'

/-- A Riemannian submersion intertwines maximal geodesics along horizontally lifted initial
velocities at every parameter in the source maximal geodesic interval. -/
theorem map_maximalGeodesic_horizontalLift_of_mem [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {p : M} {w : TangentSpace J (f p)} {t : ℝ}
    (ht : t ∈ geodesicInterval I M p (h.horizontalLift p w)) :
    f (maximalGeodesic I M p (h.horizontalLift p w) t) = maximalGeodesic J N (f p) w t := by
  simpa only [h.mfderiv_horizontalLift] using
    h.map_maximalGeodesic_of_mem (h.horizontalLift_mem_orthogonal_ker p w) ht

/-- If `M` is geodesically complete at `p`, then `f` intertwines the maximal geodesic from `(p, v)`
with the maximal geodesic from `(f p, df_p v)` at all times for every horizontal `v ∈ T_p M`. -/
theorem map_maximalGeodesic [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {p : M} (hp : IsGeodesicallyCompleteAt I M p) {v : TangentSpace I p}
    (hv : v ∈ (mfderiv I J f p).kerᗮ) (t : ℝ) :
    f (maximalGeodesic I M p v t) = maximalGeodesic J N (f p) (mfderiv I J f p v) t :=
  h.map_maximalGeodesic_of_mem hv (hp.geodesicInterval_eq_univ v ▸ mem_univ t)

/-- If `M` is geodesically complete at `p`, then `f` intertwines the maximal geodesic from
`(p, horizontalLift p w)` with the maximal geodesic from `(f p, w)` at all times. -/
theorem map_maximalGeodesic_horizontalLift [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {p : M} (hp : IsGeodesicallyCompleteAt I M p) (w : TangentSpace J (f p)) (t : ℝ) :
    f (maximalGeodesic I M p (h.horizontalLift p w) t) = maximalGeodesic J N (f p) w t := by
  simpa only [h.mfderiv_horizontalLift] using
    h.map_maximalGeodesic hp (h.horizontalLift_mem_orthogonal_ker p w) t

/-- **Naturality of the exponential map on horizontal vectors.** For a horizontal vector
`v ∈ expDomain I M p`, projecting `exp_p v` yields `exp_{f p} (df_p v)`. -/
theorem map_riemannianExp_of_mem [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {p : M} {v : TangentSpace I p} (hv : v ∈ expDomain I M p)
    (hhor : v ∈ (mfderiv I J f p).kerᗮ) :
    f (riemannianExp I M p v) = riemannianExp J N (f p) (mfderiv I J f p v) := by
  simpa only [riemannianExp_def] using
    h.map_maximalGeodesic_of_mem hhor (mem_expDomain_iff.mp hv)

/-- Whenever `horizontalLift p w` belongs to `expDomain I M p`, projecting
`exp_p (horizontalLift p w)` yields `exp_{f p} w`. -/
theorem map_riemannianExp_horizontalLift_of_mem [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {p : M} {w : TangentSpace J (f p)} (hw : h.horizontalLift p w ∈ expDomain I M p) :
    f (riemannianExp I M p (h.horizontalLift p w)) = riemannianExp J N (f p) w := by
  simpa only [h.mfderiv_horizontalLift] using
    h.map_riemannianExp_of_mem hw (h.horizontalLift_mem_orthogonal_ker p w)

/-- If `M` is geodesically complete at `p`, then `f (exp_p v) = exp_{f p} (df_p v)` for every
horizontal vector `v ∈ T_p M`. -/
theorem map_riemannianExp [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {p : M} (hp : IsGeodesicallyCompleteAt I M p) {v : TangentSpace I p}
    (hv : v ∈ (mfderiv I J f p).kerᗮ) :
    f (riemannianExp I M p v) = riemannianExp J N (f p) (mfderiv I J f p v) :=
  h.map_riemannianExp_of_mem
    (mem_expDomain_iff.mpr (hp.geodesicInterval_eq_univ v ▸ mem_univ 1)) hv

/-- If `M` is geodesically complete at `p`, then `f (exp_p (horizontalLift p w)) = exp_{f p} w`
for every `w ∈ T_{f p} N`. -/
theorem map_riemannianExp_horizontalLift [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {p : M} (hp : IsGeodesicallyCompleteAt I M p) (w : TangentSpace J (f p)) :
    f (riemannianExp I M p (h.horizontalLift p w)) = riemannianExp J N (f p) w := by
  simpa only [h.mfderiv_horizontalLift] using
    h.map_riemannianExp hp (h.horizontalLift_mem_orthogonal_ker p w)

end MaximalAndExponential

/-! ### Uniqueness and existence of horizontal geodesic lifts -/

section HorizontalLifting

include h

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
private theorem totalSpace_eq_of_tangentMap_eq {x₁ x₂ : M}
    {v₁ : TangentSpace I x₁} {v₂ : TangentSpace I x₂} (hx : x₁ = x₂)
    (hv₁ : v₁ ∈ (mfderiv I J f x₁).kerᗮ) (hv₂ : v₂ ∈ (mfderiv I J f x₂).kerᗮ)
    (htan : tangentMap I J f (TotalSpace.mk' E x₁ v₁) =
      tangentMap I J f (TotalSpace.mk' E x₂ v₂)) :
    TotalSpace.mk' E x₁ v₁ = TotalSpace.mk' E x₂ v₂ := by
  subst hx
  have hmf : mfderiv I J f x₁ v₁ = mfderiv I J f x₁ v₂ := TotalSpace.mk_inj.mp htan
  have hv : v₁ = v₂ := by
    rw [← Submodule.starProjection_eq_self_iff.mpr hv₁,
      ← Submodule.starProjection_eq_self_iff.mpr hv₂,
      ← h.horizontalLift_mfderiv, ← h.horizontalLift_mfderiv, hmf]
  exact congrArg (TotalSpace.mk' E x₁) hv

omit [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
/-- **Uniqueness of horizontal geodesic lifts.** Two geodesics in `M` on a preconnected parameter
set `s` that have the same projection in `N` on `s`, pass through the same point at some `t₀ ∈ s`,
and both have horizontal velocity at `t₀` agree throughout `s`. -/
theorem eqOn_of_isGeodesicCurveOn_horizontalLift [I.Boundaryless] [T2Space M]
    {γ₁ γ₂ : ℝ → M} {s : Set ℝ} {t₀ : ℝ}
    (hγ₁ : IsGeodesicCurveOn I γ₁ s) (hγ₂ : IsGeodesicCurveOn I γ₂ s)
    (hs : IsPreconnected s) (hfγ : EqOn (f ∘ γ₁) (f ∘ γ₂) s) (ht₀ : t₀ ∈ s)
    (hpt : γ₁ t₀ = γ₂ t₀)
    (hhor₁ : curveVelocityWithin I γ₁ s t₀ ∈ (mfderiv I J f (γ₁ t₀)).kerᗮ)
    (hhor₂ : curveVelocityWithin I γ₂ s t₀ ∈ (mfderiv I J f (γ₂ t₀)).kerᗮ) :
    EqOn γ₁ γ₂ s := by
  refine hγ₁.eqOn_of_curveVelocityLiftWithin_eq hγ₂ hs ht₀ ?_
  have hf₁ : MDifferentiableAt I J f (γ₁ t₀) :=
    h.isSubmersion.contMDiff.mdifferentiableAt (by simp)
  have hf₂ : MDifferentiableAt I J f (γ₂ t₀) :=
    h.isSubmersion.contMDiff.mdifferentiableAt (by simp)
  have htan : tangentMap I J f (curveVelocityLiftWithin I γ₁ s t₀) =
      tangentMap I J f (curveVelocityLiftWithin I γ₂ s t₀) := by
    rw [tangentMap_curveVelocityLiftWithin hf₁ (hγ₁.mdifferentiableOn t₀ ht₀)
        (hγ₁.uniqueDiffOn t₀ ht₀).uniqueMDiffWithinAt,
      tangentMap_curveVelocityLiftWithin hf₂ (hγ₂.mdifferentiableOn t₀ ht₀)
        (hγ₂.uniqueDiffOn t₀ ht₀).uniqueMDiffWithinAt]
    exact (hfγ.eventuallyEq_of_mem self_mem_nhdsWithin).curveVelocityLiftWithin_eq
      (congrArg f hpt)
  rw [curveVelocityLiftWithin_apply, curveVelocityLiftWithin_apply] at htan ⊢
  exact h.totalSpace_eq_of_tangentMap_eq hpt hhor₁ hhor₂ htan

private theorem exists_Ioo_horizontalLift_from [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {c₀ : ℝ → N} {δ : ℝ} {p : M} {q : N} {w : TangentSpace J q}
    (hδ : 0 < δ) (hq : f p = q) (hc₀ : IsGeodesicCurveOnFrom J c₀ (Ioo (-δ) δ) q w) :
    ∃ a₁ b₁ : ℝ, 0 ∈ Ioo a₁ b₁ ∧ Ioo a₁ b₁ ⊆ Ioo (-δ) δ ∧
      ∃ γ₀ : ℝ → M, IsGeodesicCurveOnFrom I γ₀ (Ioo a₁ b₁) p (h.horizontalLift p (hq ▸ w)) ∧
        EqOn (f ∘ γ₀) c₀ (Ioo a₁ b₁) ∧
        ∀ r ∈ Ioo a₁ b₁, curveVelocity I γ₀ r ∈ (mfderiv I J f (γ₀ r)).kerᗮ := by
  subst hq
  obtain ⟨a₀, b₀, _, h0, γ₀, hγ₀⟩ :=
    exists_geodesicCurveOnFrom_Ioo (I := I) (M := M) p (h.horizontalLift p w)
  let a₁ := max (-δ) a₀
  let b₁ := min δ b₀
  have h0u : (0 : ℝ) ∈ Ioo a₁ b₁ :=
    ⟨max_lt (neg_lt_zero.mpr hδ) h0.1, lt_min hδ h0.2⟩
  have hu₁ : Ioo a₁ b₁ ⊆ Ioo (-δ) δ :=
    fun r hr ↦ ⟨(le_max_left _ _).trans_lt hr.1, hr.2.trans_le (min_le_left _ _)⟩
  have hu₂ : Ioo a₁ b₁ ⊆ Ioo a₀ b₀ :=
    fun r hr ↦ ⟨(le_max_right _ _).trans_lt hr.1, hr.2.trans_le (min_le_right _ _)⟩
  have hγ₀u : IsGeodesicCurveOnFrom I γ₀ (Ioo a₁ b₁) p (h.horizontalLift p w) :=
    hγ₀.mono (uniqueDiffOn_Ioo _ _) hu₂ h0u
  have hc₀u : IsGeodesicCurveOnFrom J c₀ (Ioo a₁ b₁) (f p) w :=
    hc₀.mono (uniqueDiffOn_Ioo _ _) hu₁ h0u
  have hfγ₀u : IsGeodesicCurveOnFrom J (f ∘ γ₀) (Ioo a₁ b₁) (f p) w :=
    h.isGeodesicCurveOnFrom_comp_horizontalLift hγ₀u isPreconnected_Ioo
  have heq : EqOn (f ∘ γ₀) c₀ (Ioo a₁ b₁) := by
    simpa only [max_self, min_self] using hfγ₀u.eqOn_of_inter hc₀u
  refine ⟨a₁, b₁, h0u, hu₁, γ₀, hγ₀u, heq, fun r hr ↦ ?_⟩
  rw [← curveVelocityWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hr)]
  exact h.mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn hγ₀u.isGeodesicCurveOn
    isPreconnected_Ioo h0u
    (mem_orthogonal_ker_of_totalSpace_eq hγ₀u.initial_eq
      (h.horizontalLift_mem_orthogonal_ker p w)) hr

/-- **Local horizontal lifting of base geodesics.** Let `c` be a geodesic in `N` on a parameter set
`s` which is a neighbourhood of `t₀`, and let `p ∈ M` satisfy `f p = c t₀`. Then there exist an
open interval `(a, b) ⊆ s` containing `t₀` and a horizontal geodesic `γ` in `M` on `(a, b)` with
`γ t₀ = p` and `f ∘ γ = c` on `(a, b)`. -/
theorem exists_Ioo_isGeodesicCurveOn_horizontalLift [I.Boundaryless] [J.Boundaryless] [T2Space N]
    {c : ℝ → N} {s : Set ℝ} {t₀ : ℝ} {p : M}
    (hc : IsGeodesicCurveOn J c s) (hs : s ∈ 𝓝 t₀) (hp : f p = c t₀) :
    ∃ a b : ℝ, t₀ ∈ Ioo a b ∧ Ioo a b ⊆ s ∧
      ∃ γ : ℝ → M, IsGeodesicCurveOn I γ (Ioo a b) ∧ γ t₀ = p ∧
        EqOn (f ∘ γ) c (Ioo a b) ∧
        ∀ r ∈ Ioo a b, curveVelocity I γ r ∈ (mfderiv I J f (γ r)).kerᗮ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  rw [Real.ball_eq_Ioo] at hball
  have ht₀ : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hcIoo : IsGeodesicCurveOn J c (Ioo (t₀ - δ) (t₀ + δ)) :=
    hc.mono (uniqueDiffOn_Ioo _ _) hball
  have hc₀ : IsGeodesicCurveOnFrom J (c ∘ fun u : ℝ ↦ u + t₀) (Ioo (-δ) δ)
      (c t₀) (curveVelocity J c t₀) := by
    simpa only [sub_sub_cancel_left, add_sub_cancel_left] using
      hcIoo.isGeodesicCurveOnFrom_comp_add_const ht₀
  obtain ⟨a₁, b₁, h0u, hu₁, γ₀, hγ₀u, heq, hhor₀⟩ :=
    h.exists_Ioo_horizontalLift_from hδ hp hc₀
  let γ : ℝ → M := γ₀ ∘ fun r : ℝ ↦ 1 * r + (-t₀)
  have hmaps : MapsTo (fun r : ℝ ↦ 1 * r + (-t₀)) (Ioo (t₀ + a₁) (t₀ + b₁)) (Ioo a₁ b₁) :=
    fun r hr ↦ ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine ⟨t₀ + a₁, t₀ + b₁, ⟨by linarith [h0u.1], by linarith [h0u.2]⟩,
    fun r hr ↦ hball ⟨by linarith [(hu₁ (hmaps hr)).1], by linarith [(hu₁ (hmaps hr)).2]⟩,
    γ, hγ₀u.isGeodesicCurveOn.comp_affine 1 (-t₀) (uniqueDiffOn_Ioo _ _) hmaps,
    by simp [γ, hγ₀u.base_eq], fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · have heq := heq (hmaps hr)
    simp only [γ, Function.comp_apply, one_mul] at heq ⊢
    simpa only [neg_add_cancel_right] using heq
  · have hd : HasDerivAt (fun x : ℝ ↦ 1 * x + (-t₀)) 1 r :=
      (hasDerivAt_const_mul (1 : ℝ)).add_const (-t₀)
    have hγ₀r : MDifferentiableAt 𝓘(ℝ, ℝ) I γ₀ (1 * r + (-t₀)) :=
      (hγ₀u.isGeodesicCurveOn.contMDiffOn.contMDiffAt
        (isOpen_Ioo.mem_nhds (hmaps hr))).mdifferentiableAt two_ne_zero
    rw [curveVelocity_comp hd hγ₀r, one_smul]
    exact hhor₀ (1 * r + (-t₀)) (hmaps hr)

private theorem exists_global_horizontalLift_from
    [I.Boundaryless] [T2Space M] [J.Boundaryless] [T2Space N]
    {c₀ : ℝ → N} {p : M} {q : N} {w : TangentSpace J q}
    (hq : f p = q) (hcomp : IsGeodesicallyCompleteAt I M p)
    (hc₀ : IsGeodesicCurveOnFrom J c₀ univ q w) :
    ∃ γ₀ : ℝ → M, IsGeodesicCurveOnFrom I γ₀ univ p (h.horizontalLift p (hq ▸ w)) ∧
      (∀ r, f (γ₀ r) = c₀ r) ∧
      ∀ r, curveVelocity I γ₀ r ∈ (mfderiv I J f (γ₀ r)).kerᗮ := by
  subst hq
  let γ₀ := maximalGeodesic I M p (h.horizontalLift p w)
  have hdom : geodesicInterval I M p (h.horizontalLift p w) = univ :=
    hcomp.geodesicInterval_eq_univ (h.horizontalLift p w)
  have hγ₀ : IsGeodesicCurveOnFrom I γ₀ univ p (h.horizontalLift p w) := by
    simpa only [γ₀, hdom] using
      isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p (h.horizontalLift p w)
  have hfγ₀ : IsGeodesicCurveOnFrom J (f ∘ γ₀) univ (f p) w :=
    h.isGeodesicCurveOnFrom_comp_horizontalLift hγ₀ isPreconnected_univ
  have heq : EqOn (f ∘ γ₀) c₀ univ := by
    refine hfγ₀.isGeodesicCurveOn.eqOn_of_curveVelocityLiftWithin_eq hc₀.isGeodesicCurveOn
      isPreconnected_univ (mem_univ 0) ?_
    rw [curveVelocityLiftWithin_apply, curveVelocityLiftWithin_apply,
      hfγ₀.initial_eq, hc₀.initial_eq]
  refine ⟨γ₀, hγ₀, fun r ↦ heq (mem_univ r), fun r ↦ ?_⟩
  rw [← curveVelocityWithin_univ]
  exact h.mem_orthogonal_ker_curveVelocityWithin_of_isGeodesicCurveOn hγ₀.isGeodesicCurveOn
    isPreconnected_univ (mem_univ 0)
    (mem_orthogonal_ker_of_totalSpace_eq hγ₀.initial_eq
      (h.horizontalLift_mem_orthogonal_ker p w)) (mem_univ r)

/-- **Global horizontal lifting of base geodesics under geodesic completeness.** If `M` is
geodesically complete at `p` and `c` is an all-time geodesic in `N` with `f p = c t₀`, then there
exists an all-time horizontal geodesic `γ` in `M` with `γ t₀ = p` and `f ∘ γ = c`. -/
theorem exists_isGeodesicCurve_horizontalLift
    [I.Boundaryless] [T2Space M] [J.Boundaryless] [T2Space N]
    {c : ℝ → N} {t₀ : ℝ} {p : M} (hc : IsGeodesicCurve J c) (hp : f p = c t₀)
    (hcomp : IsGeodesicallyCompleteAt I M p) :
    ∃ γ : ℝ → M, IsGeodesicCurve I γ ∧ γ t₀ = p ∧ f ∘ γ = c ∧
      ∀ r, curveVelocity I γ r ∈ (mfderiv I J f (γ r)).kerᗮ := by
  have hc₀ : IsGeodesicCurveOnFrom J (c ∘ fun u : ℝ ↦ u + t₀) univ
      (c t₀) (curveVelocity J c t₀) := by
    refine ⟨?_, mem_univ 0, ?_⟩
    · rw [isGeodesicCurveOn_univ]
      simpa only [one_mul] using hc.comp_affine 1 t₀
    · have hd : HasDerivAt (fun u : ℝ ↦ u + t₀) 1 0 :=
        (hasDerivAt_id (0 : ℝ)).add_const t₀
      have hct₀ : MDifferentiableAt 𝓘(ℝ, ℝ) J c (0 + t₀) :=
        ((isGeodesicCurveOn_univ.mpr hc).mdifferentiableOn _ (mem_univ _)).mdifferentiableAt
          univ_mem
      rw [curveVelocityWithin_univ, curveVelocity_comp hd hct₀, one_smul, Function.comp_apply]
      exact congrArg (fun u : ℝ ↦ TotalSpace.mk' F (c u) (curveVelocity J c u)) (zero_add t₀)
  obtain ⟨γ₀, hγ₀, heq, hhor₀⟩ := h.exists_global_horizontalLift_from hp hcomp hc₀
  let γ : ℝ → M := γ₀ ∘ fun r : ℝ ↦ 1 * r + (-t₀)
  have hγgeo : IsGeodesicCurve I γ :=
    (isGeodesicCurveOn_univ.mp hγ₀.isGeodesicCurveOn).comp_affine 1 (-t₀)
  refine ⟨γ, hγgeo, by simp [γ, hγ₀.base_eq], funext fun r ↦ ?_, fun r ↦ ?_⟩
  · have hr := heq (1 * r + (-t₀))
    simp only [γ, Function.comp_apply, one_mul] at hr ⊢
    simpa only [neg_add_cancel_right] using hr
  · have hd : HasDerivAt (fun x : ℝ ↦ 1 * x + (-t₀)) 1 r :=
      (hasDerivAt_const_mul (1 : ℝ)).add_const (-t₀)
    have hγ₀r : MDifferentiableAt 𝓘(ℝ, ℝ) I γ₀ (1 * r + (-t₀)) :=
      (hγ₀.isGeodesicCurveOn.mdifferentiableOn _ (mem_univ _)).mdifferentiableAt univ_mem
    rw [curveVelocity_comp hd hγ₀r, one_smul]
    exact hhor₀ (1 * r + (-t₀))

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] h in
/-- **Global horizontal lifting of base geodesics for a complete total space.** If `M` is
metrically complete for its Riemannian distance and `c` is an all-time geodesic in `N` with
`f p = c t₀`, then `c` lifts to an all-time horizontal geodesic `γ` in `M` with `γ t₀ = p` and
`f ∘ γ = c`. -/
theorem exists_isGeodesicCurve_horizontalLift_of_completeSpace
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [I.Boundaryless] [J.Boundaryless] [T2Space N]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    {f : M → N} (h : IsRiemannianSubmersion I J f)
    {c : ℝ → N} {t₀ : ℝ} {p : M} (hc : IsGeodesicCurve J c) (hp : f p = c t₀) :
    ∃ γ : ℝ → M, IsGeodesicCurve I γ ∧ γ t₀ = p ∧ f ∘ γ = c ∧
      ∀ r, curveVelocity I γ r ∈ (mfderiv I J f (γ r)).kerᗮ :=
  h.exists_isGeodesicCurve_horizontalLift hc hp
    (isGeodesicallyCompleteAt_of_completeSpace p)

end HorizontalLifting

end TauCeti.IsRiemannianSubmersion

end
