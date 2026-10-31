/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.HalfSpaceChart
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Submersion

/-!
# Sublevels and bands at regular values are manifolds with boundary

Let `f : M → ℝ` be a `C¹` function on a boundaryless manifold modelled on a real space `E` of
dimension `n + 1`, and let `a` be a regular value of `f`. Then the sublevel `{x | f x ≤ a}` carries
the atlas `TauCeti.scalarRegularSublevelChartedSpace`, modelled on the half-space
`EuclideanHalfSpace (n + 1)`, and it is a `C^m` manifold with boundary when `f` is `C^m`, `m ≥ 1`
(`TauCeti.isManifold_scalarRegularSublevel`). Its manifold boundary is the level `f⁻¹(a)`
(`TauCeti.boundary_scalarRegularSublevel`).

The preferred charts `TauCeti.scalarRegularSublevelChartAt` are of two kinds.

* **Face charts.** At a point `x` of the level `f⁻¹(a)`, the chart is the submersion chart
  `TauCeti.scalarSubmersionChartAt` of `f` at `x`, read in `ℝⁿ⁺¹` with the inward coordinate
  `a - f` in slot `0` and the tangential coordinates in slots `1, …, n`, placed by
  `TauCeti.euclideanFinConsEquiv`. Writing `D` for the derivative of `f` in the preferred extended
  chart at `x`, `P` for the chosen projection onto `ker D` and
  `K : ker D ≃ (Fin (dim E - 1) → ℝ)` for the identification used by the level atlas, the
  tangential coordinates of `w` are `K (P (extChartAt I x w - extChartAt I x x))`, reindexed by
  `Fin.cast` along `dim E - 1 = n` (`TauCeti.scalarRegularSublevelChartAt_apply_zero_of_eq` and
  `TauCeti.scalarRegularSublevelChartAt_apply_succ_of_eq`). On the level these are the coordinates
  of the level chart `TauCeti.regularLevelChartAt`
  (`TauCeti.scalarRegularSublevelChartAt_apply_succ_eq_regularLevelChartAt`).
* **Interior charts.** At a point `x` with `f x < a`, the chart is the preferred chart of `M`,
  restricted to `{f < a}`, read in `ℝⁿ⁺¹` through a fixed linear equivalence and recentred at `x`.
  It is then restricted to a ball of radius `r` contained in its target and translated by `2 r`
  in the zeroth coordinate, so that its image lies in the open half-space
  (`TauCeti.exists_scalarRegularSublevelChartAt_of_lt`).

Both kinds are restrictions `OpenPartialHomeomorph.halfSpaceChart` of `ℝⁿ⁺¹`-valued charts
`OpenPartialHomeomorph.extendTrans` of `M` on whose sources `f ≤ a` exactly when the zeroth
coordinate is nonnegative. Their transition maps are therefore restrictions of transition maps of
`M`, composed with smooth maps of the model spaces. No compactness of the sublevel and no
assumption on the critical points of `f` away from the level are needed.

The same construction applies to the band `f⁻¹([a, b])` between regular values `a < b`, with atlas
`TauCeti.scalarRegularBandChartedSpace` (`TauCeti.isManifold_scalarRegularBand`). Its manifold
boundary is the union of the two levels `f⁻¹(a)` and `f⁻¹(b)`
(`TauCeti.boundary_scalarRegularBand`). At a point of the upper level `f⁻¹(b)` the preferred chart
`TauCeti.scalarRegularBandChartAt` is the face chart of the sublevel `{f ≤ b}`, restricted to
`{a < f}`, with inward coordinate `b - f`. At a point of the lower level `f⁻¹(a)` it is the
submersion chart of `f`, restricted to `{f < b}`, read through
`TauCeti.scalarRegularBandLowerFaceEquiv`: the inward coordinate is `f - a`, and the tangential
coordinates are again those of the level chart. At a point of `{a < f < b}` it is an interior chart
as above.

## Main declarations

* `TauCeti.scalarRegularSublevelChartAt` and `TauCeti.scalarRegularSublevelChartedSpace`: the
  preferred charts and the atlas of a sublevel at a regular value.
* `TauCeti.scalarRegularSublevelFaceEquiv`: the linear part of the face charts, with the source,
  target, apply and inverse laws `TauCeti.scalarRegularSublevelChartAt_source_of_eq`,
  `TauCeti.scalarRegularSublevelChartAt_apply_of_eq`,
  `TauCeti.mem_scalarRegularSublevelChartAt_target_iff_of_eq` and
  `TauCeti.coe_scalarRegularSublevelChartAt_symm_apply_of_eq`.
* `TauCeti.isManifold_scalarRegularSublevel`: the sublevel is a `C^m` manifold with boundary.
* `TauCeti.boundary_scalarRegularSublevel` and `TauCeti.interior_scalarRegularSublevel`: its
  manifold boundary is the level `f⁻¹(a)`, and its manifold interior is `{x | f x < a}`.
* `TauCeti.scalarRegularBandChartAt` and `TauCeti.scalarRegularBandChartedSpace`: the preferred
  charts and the atlas of a band between regular values, with the lower face equivalence
  `TauCeti.scalarRegularBandLowerFaceEquiv` and the face laws
  `TauCeti.scalarRegularBandChartAt_apply_zero_of_eq_left`,
  `TauCeti.scalarRegularBandChartAt_apply_zero_of_eq_right` and their tangential, source, target
  and inverse companions.
* `TauCeti.isManifold_scalarRegularBand`: the band is a `C^m` manifold with boundary.
* `TauCeti.boundary_scalarRegularBand` and `TauCeti.interior_scalarRegularBand`: its manifold
  boundary is `f⁻¹(a) ∪ f⁻¹(b)`, and its manifold interior is `f⁻¹((a, b))`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are regular domains).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3.
-/

public section

open Function Metric Module Set
open OpenPartialHomeomorph (contDiffOn_extendTrans_comp_symm contDiffOn_halfSpaceChart_symm_trans
  coe_halfSpaceChart_apply coe_halfSpaceChart_symm_apply halfSpaceChart_source
  halfSpaceChart_target)
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a : ℝ}
  {n : ℕ}

namespace ScalarSublevel

section Interior

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- The fixed linear identification of `E` with `ℝⁿ⁺¹` used by the interior charts. -/
private noncomputable abbrev modelEquiv (hn : finrank ℝ E = n + 1) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ContinuousLinearEquiv.ofFinrankEq (by rw [hn, finrank_euclideanSpace_fin])

variable (I) in
/-- The preferred chart of `M` at `x`, read in `ℝⁿ⁺¹` through `modelEquiv` and recentred at `x`. -/
private noncomputable abbrev centredChart (hn : finrank ℝ E = n + 1) (x : M) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  (chartAt H x).extendTrans I
    ((Homeomorph.subRight (extChartAt I x x)).trans (modelEquiv hn).toHomeomorph)

private theorem centredChart_apply (hn : finrank ℝ E = n + 1) (x w : M) :
    centredChart I hn x w = modelEquiv hn (extChartAt I x w - extChartAt I x x) := by
  simp [mfld_simps]

private theorem centredChart_source (hn : finrank ℝ E = n + 1) (x : M) :
    (centredChart I hn x).source = (chartAt H x).source := by
  simp [mfld_simps]

/-- The recentred chart at a point of an open set `U` maps the part of its source in `U` onto a
neighbourhood of `0`, which contains a ball about `0`. -/
private theorem exists_ball_subset_image {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) :
    ∃ r > 0, ball 0 r ⊆ centredChart I hn x '' ((chartAt H x).source ∩ U) := by
  refine Metric.isOpen_iff.1 ((centredChart I hn x).isOpen_image_of_subset_source
    ((chartAt H x).open_source.inter hU)
    (by rw [centredChart_source]; exact inter_subset_left)) 0
    ⟨x, ⟨mem_chart_source H x, hx⟩, ?_⟩
  rw [centredChart_apply, sub_self, map_zero]

variable (I) in
/-- The radius of the ball in the target of the recentred chart used by the interior chart. -/
private noncomputable def interiorRadius {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) : ℝ :=
  (exists_ball_subset_image (I := I) hU hn hx).choose

private theorem interiorRadius_pos {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1) {x : M}
    (hx : x ∈ U) : 0 < interiorRadius I hU hn hx :=
  (exists_ball_subset_image (I := I) hU hn hx).choose_spec.1

private theorem ball_interiorRadius_subset {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) :
    ball 0 (interiorRadius I hU hn hx) ⊆ centredChart I hn x '' ((chartAt H x).source ∩ U) :=
  (exists_ball_subset_image (I := I) hU hn hx).choose_spec.2

variable (I) in
/-- The domain of the interior chart at a point `x` of an open set `U`: the points of `U` which the
recentred chart at `x` sends into the ball of radius `interiorRadius`. -/
private noncomputable abbrev interiorDomain {U : Set M} (hU : IsOpen U)
    (hn : finrank ℝ E = n + 1) {x : M} (hx : x ∈ U) : Set M :=
  ((centredChart I hn x).source ∩ centredChart I hn x ⁻¹' ball 0 (interiorRadius I hU hn hx)) ∩ U

private theorem isOpen_interiorDomain {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) : IsOpen (interiorDomain I hU hn hx) :=
  ((centredChart I hn x).isOpen_inter_preimage isOpen_ball).inter hU

variable (I) in
/-- The interior chart at a point `x` of an open set `U`: the recentred chart at `x`, restricted to
the ball of radius `r = interiorRadius` and translated by `2 r` in the zeroth coordinate. -/
private noncomputable def interiorChart {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  ((chartAt H x).restr (interiorDomain I hU hn hx)).extendTrans I
    (((Homeomorph.subRight (extChartAt I x x)).trans (modelEquiv hn).toHomeomorph).trans
      (Homeomorph.addRight (EuclideanSpace.single 0 (2 * interiorRadius I hU hn hx))))

private theorem interiorChart_apply {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) (w : M) :
    interiorChart I hU hn hx w = centredChart I hn x w +
      EuclideanSpace.single 0 (2 * interiorRadius I hU hn hx) := by
  simp [interiorChart, mfld_simps]

private theorem interiorChart_source {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) : (interiorChart I hU hn hx).source = interiorDomain I hU hn hx := by
  simp only [interiorChart, OpenPartialHomeomorph.extendTrans_source, mfld_simps]
  rw [(isOpen_interiorDomain hU hn hx).interior_eq]
  refine inter_eq_right.2 fun w hw ↦ ?_
  have := hw.1.1
  rwa [centredChart_source] at this

/-- The zeroth coordinate of the interior chart is positive on its whole source. -/
private theorem interiorChart_apply_zero_pos {U : Set M} (hU : IsOpen U)
    (hn : finrank ℝ E = n + 1) {x : M} (hx : x ∈ U) {w : M}
    (hw : w ∈ (interiorChart I hU hn hx).source) :
    0 < interiorChart I hU hn hx w 0 := by
  rw [interiorChart_source] at hw
  have hlt : ‖centredChart I hn x w‖ < interiorRadius I hU hn hx := mem_ball_zero_iff.1 hw.1.2
  have h0 := (PiLp.norm_apply_le (centredChart I hn x w) 0).trans_lt hlt
  rw [interiorChart_apply]
  simp only [PiLp.add_apply, EuclideanSpace.single, PiLp.single_apply, ite_true]
  have h1 := neg_abs_le (centredChart I hn x w 0)
  rw [← Real.norm_eq_abs] at h1
  linarith [norm_nonneg (centredChart I hn x w 0)]

/-- An interior chart at a point of an open set `U` contained in `s` cuts out `s` by the sign of its
zeroth coordinate, which is positive on its whole source. -/
private theorem interiorChart_mem_iff {U s : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) (hUs : U ⊆ s) :
    ∀ w ∈ (interiorChart I hU hn hx).source, w ∈ s ↔ 0 ≤ interiorChart I hU hn hx w 0 := by
  intro w hw
  refine iff_of_true ?_ (interiorChart_apply_zero_pos hU hn hx hw).le
  rw [interiorChart_source] at hw
  exact hUs hw.2

end Interior

end ScalarSublevel

open ScalarSublevel

section FaceEquiv

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- The linear part `v ↦ (-D v, K (P v))` of the face chart of a sublevel at a regular point `x`
of `f`, with `-D v` in slot `0` and `K (P v)`, reindexed along `dim E - 1 = n`, in slots
`1, …, n` (`TauCeti.scalarRegularSublevelFaceEquiv_apply_zero`,
`TauCeti.scalarRegularSublevelFaceEquiv_apply_succ`). Here `D` is the derivative of `f` in the
preferred extended chart at `x`, `P` the chosen projection onto `ker D` and
`K : ker D ≃ (Fin (dim E - 1) → ℝ)` the identification used by the level atlas. -/
noncomputable def scalarRegularSublevelFaceEquiv (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
  (D.implicitCoordEquiv (LinearMap.range_eq_top.2 hx.surjective_fderiv_comp_extChartAt_symm)
      D.isFredholm_of_finiteDimensional.closedComplemented_ker).trans
    (((ContinuousLinearEquiv.neg ℝ).prodCongr
      (D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        hx.finrank_ker_fderiv_comp_extChartAt_symm)).trans (euclideanFinConsEquiv (by omega)))

/-- The zeroth coordinate of `TauCeti.scalarRegularSublevelFaceEquiv` is `-D v`, where `D` is the
derivative of `f` in the preferred extended chart at `x`. -/
theorem scalarRegularSublevelFaceEquiv_apply_zero (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) (v : E) :
    scalarRegularSublevelFaceEquiv hn hx v 0 =
      -fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v := by
  simp only [scalarRegularSublevelFaceEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.neg_apply,
    euclideanFinConsEquiv_apply_zero, ContinuousLinearMap.implicitCoordEquiv_apply]

/-- The coordinates of `TauCeti.scalarRegularSublevelFaceEquiv` in slots `1, …, n` are `K (P v)`,
reindexed along `dim E - 1 = n`, where `P` is the chosen projection onto the kernel of the
preferred-chart derivative `D` of `f` at `x` and `K` the identification of `ker D` used by the level
atlas. -/
theorem scalarRegularSublevelFaceEquiv_apply_succ (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) (v : E) (i : Fin n) :
    scalarRegularSublevelFaceEquiv hn hx v i.succ =
      let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
      D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        hx.finrank_ker_fderiv_comp_extChartAt_symm
        (Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker v)
        (Fin.cast (by omega) i) := by
  simp only [scalarRegularSublevelFaceEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, euclideanFinConsEquiv_apply_succ,
    ContinuousLinearMap.implicitCoordEquiv_apply]

/-- The linear part `v ↦ (D v, K (P v))` of the face chart of a band `f⁻¹([a, b])` at a regular
point `x` of its lower level `f⁻¹(a)`. It is `TauCeti.scalarRegularSublevelFaceEquiv` with the sign
of slot `0` reversed: slot `0` holds `D v`, the inward coordinate at the lower level
(`TauCeti.scalarRegularBandLowerFaceEquiv_apply_zero`), and slots `1, …, n` hold the same tangential
coordinates `K (P v)` (`TauCeti.scalarRegularBandLowerFaceEquiv_apply_succ`). -/
noncomputable def scalarRegularBandLowerFaceEquiv (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (scalarRegularSublevelFaceEquiv hn hx).trans <|
    ((euclideanFinConsEquiv (rfl : n = n)).symm.trans
      ((ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)))).trans
    (euclideanFinConsEquiv rfl)

/-- The zeroth coordinate of `TauCeti.scalarRegularBandLowerFaceEquiv` is `D v`, where `D` is the
derivative of `f` in the preferred extended chart at `x`. -/
theorem scalarRegularBandLowerFaceEquiv_apply_zero (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) (v : E) :
    scalarRegularBandLowerFaceEquiv hn hx v 0 =
      fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v := by
  simp [scalarRegularBandLowerFaceEquiv, scalarRegularSublevelFaceEquiv_apply_zero]

/-- The coordinates of `TauCeti.scalarRegularBandLowerFaceEquiv` in slots `1, …, n` are those of
`TauCeti.scalarRegularSublevelFaceEquiv`. -/
theorem scalarRegularBandLowerFaceEquiv_apply_succ (hn : finrank ℝ E = n + 1) {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) (v : E) (i : Fin n) :
    scalarRegularBandLowerFaceEquiv hn hx v i.succ =
      scalarRegularSublevelFaceEquiv hn hx v i.succ := by
  simp [scalarRegularBandLowerFaceEquiv]

end FaceEquiv

namespace ScalarSublevel

section Face

variable [I.Boundaryless] [FiniteDimensional ℝ E]

variable (I) in
/-- The face chart at a regular point `x`: the submersion chart of `f` at `x`, read in `ℝⁿ⁺¹`
through `TauCeti.scalarRegularSublevelFaceEquiv`. -/
private noncomputable def faceChart (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  (scalarSubmersionChartAt hf hx).extendTrans I (scalarRegularSublevelFaceEquiv hn hx).toHomeomorph

private theorem faceChart_source (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) :
    (faceChart I hn hf hx).source = (scalarSubmersionChartAt hf hx).source := by
  simp [faceChart, mfld_simps]

private theorem faceChart_apply (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) {w : M}
    (hw : w ∈ (chartAt H x).source) :
    faceChart I hn hf hx w =
      let D := fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
      euclideanFinConsEquiv (by omega) (f x - f w,
        D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
          hx.finrank_ker_fderiv_comp_extChartAt_symm
          (Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker
            (extChartAt I x w - extChartAt I x x))) := by
  have h := scalarSubmersionChartAt_extend_apply hf hx hw
  rw [OpenPartialHomeomorph.extend_coe, comp_apply] at h
  simp only [faceChart, OpenPartialHomeomorph.extendTrans_apply,
    ContinuousLinearEquiv.coe_toHomeomorph, h, scalarRegularSublevelFaceEquiv,
    ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.neg_apply, neg_sub]

private theorem faceChart_le_iff (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) (hxa : f x = a) :
    ∀ w ∈ (faceChart I hn hf hx).source, w ∈ {x | f x ≤ a} ↔ 0 ≤ faceChart I hn hf hx w 0 := by
  intro w hw
  rw [faceChart_source, scalarSubmersionChartAt_source] at hw
  rw [mem_ofPred_eq, faceChart_apply hn hf hx hw.1, euclideanFinConsEquiv_apply_zero, hxa,
    sub_nonneg]

end Face

section RestrFace

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- The face chart at a regular point `x` is `TauCeti.scalarRegularSublevelFaceEquiv` applied to the
extended submersion chart of `f` at `x`. -/
private theorem faceChart_apply_eq (hn : finrank ℝ E = n + 1) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) (w : M) :
    faceChart I hn hf hx w =
      scalarRegularSublevelFaceEquiv hn hx ((scalarSubmersionChartAt hf hx).extend I w) := by
  simp [faceChart, mfld_simps]

variable (I) in
/-- The submersion chart of `f` at a regular point `x`, restricted to a set `V` and read in `ℝⁿ⁺¹`
through a linear equivalence `Ψ`. The face charts of a band are of this form. -/
private noncomputable def restrFaceChart {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 1 f x)
    (hx : IsRegularPoint I 𝓘(ℝ) f x) (V : Set M) (Ψ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  ((scalarSubmersionChartAt hf hx).restr V).extendTrans I Ψ.toHomeomorph

variable {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : IsRegularPoint I 𝓘(ℝ) f x) {V : Set M}
  (Ψ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))

private theorem restrFaceChart_source (hV : IsOpen V) :
    (restrFaceChart I hf hx V Ψ).source = (scalarSubmersionChartAt hf hx).source ∩ V := by
  simp [restrFaceChart, hV.interior_eq, mfld_simps]

private theorem restrFaceChart_apply (w : M) :
    restrFaceChart I hf hx V Ψ w = Ψ ((scalarSubmersionChartAt hf hx).extend I w) := by
  simp [restrFaceChart, mfld_simps]

private theorem restrFaceChart_symm_apply (v : EuclideanSpace ℝ (Fin (n + 1))) :
    (restrFaceChart I hf hx V Ψ).symm v =
      ((scalarSubmersionChartAt hf hx).extend I).symm (Ψ.symm v) := by
  simp [restrFaceChart, mfld_simps]

end RestrFace

section Atlas

variable [I.Boundaryless] [FiniteDimensional ℝ E]

variable (I) in
/-- `e` is a chart of `M` from its maximal atlas for `C^m`, read in `ℝⁿ⁺¹` by a `C^m` homeomorphism
with `C^m` inverse. The preferred charts of sublevels and bands are half-space restrictions of such
charts. -/
private def IsExtendTransChart (m : ℕ∞ω)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1)))) : Prop :=
  ∃ (c : OpenPartialHomeomorph M H) (Ψ : E ≃ₜ EuclideanSpace ℝ (Fin (n + 1))),
    c ∈ IsManifold.maximalAtlas I m M ∧ ContDiff ℝ m Ψ ∧ ContDiff ℝ m Ψ.symm ∧
      e = c.extendTrans I Ψ

/-- The target of the interior chart is the ball of radius `r = interiorRadius` about the point
`2 r e₀` of `ℝⁿ⁺¹`. -/
private theorem interiorChart_target {U : Set M} (hU : IsOpen U) (hn : finrank ℝ E = n + 1)
    {x : M} (hx : x ∈ U) :
    (interiorChart I hU hn hx).target = ball (EuclideanSpace.single 0
      (2 * interiorRadius I hU hn hx)) (interiorRadius I hU hn hx) := by
  rw [← (interiorChart I hU hn hx).image_source_eq_target, interiorChart_source]
  ext v
  simp only [mem_image, interiorChart_apply, mem_ball, dist_eq_norm]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [add_sub_cancel_right]
    exact mem_ball_zero_iff.1 hw.1.2
  · intro hv
    obtain ⟨w, ⟨hw, hwa⟩, hwv⟩ := ball_interiorRadius_subset hU hn hx (mem_ball_zero_iff.2 hv)
    refine ⟨w, ⟨⟨by rwa [centredChart_source], ?_⟩, hwa⟩, by rw [hwv, sub_add_cancel]⟩
    rw [mem_preimage, hwv, mem_ball_zero_iff]
    exact hv

/-- An interior chart is a restriction of a chart of `M` from its maximal atlas, read in `ℝⁿ⁺¹` by a
smooth homeomorphism with smooth inverse. -/
private theorem exists_interiorChart_eq_extendTrans {m : ℕ∞ω} [IsManifold I m M] {U : Set M}
    (hU : IsOpen U) (hn : finrank ℝ E = n + 1) {x : M} (hx : x ∈ U) :
    IsExtendTransChart I m (interiorChart I hU hn hx) := by
  refine ⟨_, _, restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas _)
    (isOpen_interiorDomain hU hn hx), ?_, ?_, rfl⟩
  · exact ((modelEquiv hn).contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const
  · convert ((modelEquiv hn).symm.contDiff.comp (contDiff_id.sub (contDiff_const
      (c := EuclideanSpace.single 0 (2 * interiorRadius I hU hn hx))))).add
      (contDiff_const (c := extChartAt I x x)) using 1
    ext1 v
    simp [Homeomorph.addRight_symm, sub_eq_add_neg]

/-- A restricted face chart is a restriction of a chart of `M` from its maximal atlas, read in
`ℝⁿ⁺¹` by a smooth linear equivalence. -/
private theorem isExtendTransChart_restrFaceChart {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) {x : M} (hx : IsRegularPoint I 𝓘(ℝ) f x) {V : Set M}
    (hV : IsOpen V) (Ψ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    IsExtendTransChart I m (restrFaceChart I (hfm.of_le hm).contMDiffAt hx V Ψ) :=
  ⟨_, _, restr_mem_maximalAtlas _
    (scalarSubmersionChartAt_mem_maximalAtlas _ _ hm fun _ _ ↦ hfm.contMDiffAt) hV,
    Ψ.contDiff, Ψ.symm.contDiff, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- A charted space on a subset `s` of `M`, modelled on the half-space, all of whose charts are
half-space restrictions of charts satisfying `IsExtendTransChart`, is a `C^m` manifold with
boundary. -/
private theorem isManifold_of_forall_mem_atlas {m : ℕ∞ω} {s : Set M}
    [ChartedSpace (EuclideanHalfSpace (n + 1)) s]
    (h : ∀ e ∈ atlas (EuclideanHalfSpace (n + 1)) s,
      ∃ (e' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
        (he' : ∀ w ∈ e'.source, w ∈ s ↔ 0 ≤ e' w 0) (x : s),
        IsExtendTransChart I m e' ∧ e = e'.halfSpaceChart he' x) :
    IsManifold (𝓡∂ (n + 1)) m s := by
  refine isManifold_of_contDiffOn _ _ _ fun e₁ e₂ h₁ h₂ ↦ ?_
  obtain ⟨_, he₁, x₁, ⟨c₁, Ψ₁, hc₁, -, hΨ₁, rfl⟩, rfl⟩ := h e₁ h₁
  obtain ⟨_, he₂, x₂, ⟨c₂, Ψ₂, hc₂, hΨ₂, -, rfl⟩, rfl⟩ := h e₂ h₂
  exact contDiffOn_halfSpaceChart_symm_trans he₁ he₂ x₁ x₂
    (contDiffOn_extendTrans_comp_symm I hc₁ hc₂ hΨ₁ hΨ₂)

end Atlas

end ScalarSublevel

open ScalarSublevel

section Sublevel

omit [TopologicalSpace M] in
private theorem preimage_Iio_subset_setOf_le : f ⁻¹' Iio a ⊆ {x | f x ≤ a} :=
  fun _ hw ↦ mem_ofPred.2 (mem_Iio.1 (mem_preimage.1 hw)).le

variable [I.Boundaryless] [FiniteDimensional ℝ E] (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hreg : IsRegularValue I 𝓘(ℝ) f a) (hn : finrank ℝ E = n + 1)

/-- The preferred chart at a point `x` of the sublevel `{f ≤ a}` of a `C¹` function at a regular
value `a`, modelled on the half-space `EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`.

At a point of the level `f⁻¹(a)` it is the face chart: the submersion chart of `f` at `x`, with
the inward coordinate `a - f` in slot `0` and the tangential coordinates of the level chart in
slots `1, …, n` (`TauCeti.scalarRegularSublevelChartAt_apply_zero_of_eq`,
`TauCeti.scalarRegularSublevelChartAt_apply_succ_of_eq`). At a point of `{f < a}` it is an
interior chart, whose target is a ball in the open half-space
(`TauCeti.exists_scalarRegularSublevelChartAt_of_lt`). -/
noncomputable def scalarRegularSublevelChartAt (x : {x | f x ≤ a}) :
    OpenPartialHomeomorph {x | f x ≤ a} (EuclideanHalfSpace (n + 1)) :=
  if hx : f x < a then
    (interiorChart I (isOpen_Iio.preimage hf.continuous) hn (mem_Iio.2 hx)).halfSpaceChart
      (interiorChart_mem_iff _ hn _ preimage_Iio_subset_setOf_le) x
  else
    have hxa : f x = a := le_antisymm x.2 (not_lt.1 hx)
    (faceChart I hn hf.contMDiffAt (hreg.isRegularPoint hxa)).halfSpaceChart
      (faceChart_le_iff hn hf.contMDiffAt (hreg.isRegularPoint hxa) hxa) x

private theorem scalarRegularSublevelChartAt_of_lt {x : {x | f x ≤ a}} (hx : f x < a) :
    scalarRegularSublevelChartAt hf hreg hn x =
      (interiorChart I (isOpen_Iio.preimage hf.continuous) hn (mem_Iio.2 hx)).halfSpaceChart
        (interiorChart_mem_iff _ hn _ preimage_Iio_subset_setOf_le) x :=
  dite_eq_left hx

private theorem scalarRegularSublevelChartAt_of_eq {x : {x | f x ≤ a}} (hx : f x = a) :
    scalarRegularSublevelChartAt hf hreg hn x =
      (faceChart I hn hf.contMDiffAt (hreg.isRegularPoint hx)).halfSpaceChart
        (faceChart_le_iff hn hf.contMDiffAt (hreg.isRegularPoint hx) hx) x :=
  dite_eq_right hx.not_lt

/-- Every point of the sublevel lies in the source of its preferred chart. -/
theorem mem_scalarRegularSublevelChartAt_source (x : {x | f x ≤ a}) :
    x ∈ (scalarRegularSublevelChartAt hf hreg hn x).source := by
  have hxa : f x ≤ a := x.2
  rcases hxa.lt_or_eq with hx | hx
  · rw [scalarRegularSublevelChartAt_of_lt hf hreg hn hx, halfSpaceChart_source, mem_preimage,
      interiorChart_source]
    refine ⟨⟨by rw [centredChart_source]; exact mem_chart_source H _, ?_⟩, hx⟩
    rw [mem_preimage, centredChart_apply, sub_self, map_zero]
    exact mem_ball_self (interiorRadius_pos (isOpen_Iio.preimage hf.continuous) hn _)
  · rw [scalarRegularSublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_source, mem_preimage,
      faceChart_source]
    exact mem_scalarSubmersionChartAt_source _ _

/-- The atlas of the sublevel `{f ≤ a}` of a `C¹` function at a regular value `a`, modelled on the
half-space `EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`, with preferred charts
`TauCeti.scalarRegularSublevelChartAt`. -/
@[irreducible]
noncomputable def scalarRegularSublevelChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) {x | f x ≤ a} where
  atlas := range (scalarRegularSublevelChartAt hf hreg hn)
  chartAt := scalarRegularSublevelChartAt hf hreg hn
  mem_chart_source := mem_scalarRegularSublevelChartAt_source hf hreg hn
  chart_mem_atlas := mem_range_self

/-- The installed preferred charts are `TauCeti.scalarRegularSublevelChartAt`. -/
@[simp]
theorem scalarRegularSublevelChartedSpace_chartAt (x : {x | f x ≤ a}) :
    @chartAt (EuclideanHalfSpace (n + 1)) _ {x | f x ≤ a} _
        (scalarRegularSublevelChartedSpace hf hreg hn) x =
      scalarRegularSublevelChartAt hf hreg hn x := by
  unfold scalarRegularSublevelChartedSpace
  rfl

/-- The installed atlas consists exactly of the preferred charts. -/
@[simp]
theorem scalarRegularSublevelChartedSpace_atlas :
    @atlas (EuclideanHalfSpace (n + 1)) _ {x | f x ≤ a} _
        (scalarRegularSublevelChartedSpace hf hreg hn) =
      range (scalarRegularSublevelChartAt hf hreg hn) := by
  unfold atlas scalarRegularSublevelChartedSpace
  rfl

section Face

variable {x : {x | f x ≤ a}} (hx : f x = a)
include hx

/-- The source of the preferred chart at a point `x` of the level `f⁻¹(a)` is the part of the
sublevel in the source of the submersion chart of `f` at `x`. -/
theorem scalarRegularSublevelChartAt_source_of_eq :
    (scalarRegularSublevelChartAt hf hreg hn x).source =
      Subtype.val ⁻¹' (scalarSubmersionChartAt hf.contMDiffAt (hreg.isRegularPoint hx)).source := by
  rw [scalarRegularSublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_source, faceChart_source]

/-- At a point `x` of the level `f⁻¹(a)`, the preferred chart reads a point of its source in the
extended submersion chart of `f` at `x`, followed by `TauCeti.scalarRegularSublevelFaceEquiv`. -/
theorem scalarRegularSublevelChartAt_apply_of_eq {w : {x | f x ≤ a}}
    (hw : w ∈ (scalarRegularSublevelChartAt hf hreg hn x).source) :
    (scalarRegularSublevelChartAt hf hreg hn x w).1 =
      scalarRegularSublevelFaceEquiv hn (hreg.isRegularPoint hx)
        ((scalarSubmersionChartAt hf.contMDiffAt (hreg.isRegularPoint hx)).extend I w) := by
  rw [scalarRegularSublevelChartAt_source_of_eq hf hreg hn hx, mem_preimage] at hw
  rw [scalarRegularSublevelChartAt_of_eq hf hreg hn hx,
    coe_halfSpaceChart_apply _ _ (by rwa [faceChart_source])]
  simp [faceChart, mfld_simps]

/-- At a point `x` of the level `f⁻¹(a)`, a point `z` of the half-space lies in the target of the
preferred chart exactly when `TauCeti.scalarRegularSublevelFaceEquiv` sends it back into the target
of the extended submersion chart of `f` at `x`. -/
theorem mem_scalarRegularSublevelChartAt_target_iff_of_eq (z : EuclideanHalfSpace (n + 1)) :
    z ∈ (scalarRegularSublevelChartAt hf hreg hn x).target ↔
      (scalarRegularSublevelFaceEquiv hn (hreg.isRegularPoint hx)).symm z.1 ∈
        ((scalarSubmersionChartAt hf.contMDiffAt (hreg.isRegularPoint hx)).extend I).target := by
  rw [scalarRegularSublevelChartAt_of_eq hf hreg hn hx, halfSpaceChart_target, mem_preimage,
    OpenPartialHomeomorph.extend_target, I.range_eq_univ, inter_univ]
  simp [faceChart, mfld_simps]

/-- At a point `x` of the level `f⁻¹(a)`, the inverse of the preferred chart is the inverse of
`TauCeti.scalarRegularSublevelFaceEquiv` followed by the inverse extended submersion chart of `f`
at `x`. -/
theorem coe_scalarRegularSublevelChartAt_symm_apply_of_eq {z : EuclideanHalfSpace (n + 1)}
    (hz : z ∈ (scalarRegularSublevelChartAt hf hreg hn x).target) :
    ((scalarRegularSublevelChartAt hf hreg hn x).symm z : M) =
      ((scalarSubmersionChartAt hf.contMDiffAt (hreg.isRegularPoint hx)).extend I).symm
        ((scalarRegularSublevelFaceEquiv hn (hreg.isRegularPoint hx)).symm z.1) := by
  rw [scalarRegularSublevelChartAt_of_eq hf hreg hn hx] at hz ⊢
  rw [halfSpaceChart_target, mem_preimage, modelWithCornersEuclideanHalfSpace_toFun] at hz
  rw [coe_halfSpaceChart_symm_apply _ _ hz]
  simp [faceChart, mfld_simps]

/-- At a point `x` of the level `f⁻¹(a)`, the zeroth coordinate of the preferred chart is the
inward coordinate `a - f`. -/
theorem scalarRegularSublevelChartAt_apply_zero_of_eq {w : {x | f x ≤ a}}
    (hw : w ∈ (scalarRegularSublevelChartAt hf hreg hn x).source) :
    (scalarRegularSublevelChartAt hf hreg hn x w).1 0 = a - f w := by
  rw [scalarRegularSublevelChartAt_source_of_eq hf hreg hn hx, mem_preimage,
    scalarSubmersionChartAt_source] at hw
  rw [scalarRegularSublevelChartAt_of_eq hf hreg hn hx, coe_halfSpaceChart_apply _ _ (by
      rw [faceChart_source, scalarSubmersionChartAt_source]; exact hw),
    faceChart_apply hn _ _ hw.1, euclideanFinConsEquiv_apply_zero, hx]

/-- At a point `x` of the level `f⁻¹(a)`, the coordinates of the preferred chart in slots
`1, …, n` are the tangential coordinates `K (P (extChartAt I x w - extChartAt I x x))`, reindexed
along `dim E - 1 = n`. Here `D` is the derivative of `f` in the preferred extended chart at `x`,
`P` the chosen projection onto `ker D` and `K : ker D ≃ (Fin (dim E - 1) → ℝ)` the identification
used by the level atlas. -/
theorem scalarRegularSublevelChartAt_apply_succ_of_eq {w : {x | f x ≤ a}}
    (hw : w ∈ (scalarRegularSublevelChartAt hf hreg hn x).source) (i : Fin n) :
    (scalarRegularSublevelChartAt hf hreg hn x w).1 i.succ =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        (hreg.isRegularPoint hx).finrank_ker_fderiv_comp_extChartAt_symm
        (Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker
          (extChartAt I (x : M) w - extChartAt I (x : M) x)) (Fin.cast (by omega) i) := by
  rw [scalarRegularSublevelChartAt_source_of_eq hf hreg hn hx, mem_preimage,
    scalarSubmersionChartAt_source] at hw
  rw [scalarRegularSublevelChartAt_of_eq hf hreg hn hx, coe_halfSpaceChart_apply _ _ (by
      rw [faceChart_source, scalarSubmersionChartAt_source]; exact hw),
    faceChart_apply hn _ _ hw.1, euclideanFinConsEquiv_apply_succ]

/-- **On the level, the tangential coordinates are those of the level chart.** At a point `x` of
the level `f⁻¹(a)`, the coordinates in slots `1, …, n` of the preferred chart of the sublevel at a
point `w` of the level are the coordinates of the preferred level chart
`TauCeti.regularLevelChartAt` at `x`, reindexed along `dim E - 1 = n`. -/
theorem scalarRegularSublevelChartAt_apply_succ_eq_regularLevelChartAt {w : {x | f x ≤ a}}
    (hw : w ∈ (scalarRegularSublevelChartAt hf hreg hn x).source) (hwa : f w = a) (i : Fin n) :
    (scalarRegularSublevelChartAt hf hreg hn x w).1 i.succ =
      regularLevelChartAt (n := finrank ℝ E - 1) (fun y _ ↦ hf.contMDiffAt) hreg
        (by rw [finrank_self]) ⟨x, hx⟩ ⟨w, hwa⟩
        (Fin.cast (by omega) i) := by
  rw [scalarRegularSublevelChartAt_apply_succ_of_eq hf hreg hn hx hw,
    regularLevelChartAt_apply]

end Face

/-- At a point `x` of `{f < a}`, the preferred chart of the sublevel is an interior chart: for some
`r > 0` its target is the ball of radius `r` about the point `2 r e₀` of the open half-space, its
source lies in `{f < a}`, and it reads a point `w` as `T (extChartAt I x w - extChartAt I x x)`,
translated by `2 r e₀`, for a fixed linear equivalence `T : E ≃ ℝⁿ⁺¹`. -/
theorem exists_scalarRegularSublevelChartAt_of_lt {x : {x | f x ≤ a}} (hx : f x < a) :
    ∃ r > 0, (scalarRegularSublevelChartAt hf hreg hn x).target =
        (𝓡∂ (n + 1)) ⁻¹' ball (EuclideanSpace.single 0 (2 * r)) r ∧
      ∀ w ∈ (scalarRegularSublevelChartAt hf hreg hn x).source, f w < a ∧
        (scalarRegularSublevelChartAt hf hreg hn x w).1 =
          ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
              (F := EuclideanSpace ℝ (Fin (n + 1))) (by rw [hn, finrank_euclideanSpace_fin])
            (extChartAt I (x : M) w - extChartAt I (x : M) x) +
          EuclideanSpace.single 0 (2 * r) := by
  refine ⟨interiorRadius I (isOpen_Iio.preimage hf.continuous) hn (mem_Iio.2 hx),
    interiorRadius_pos _ hn _, ?_, fun w hw ↦ ?_⟩
  · rw [scalarRegularSublevelChartAt_of_lt hf hreg hn hx, halfSpaceChart_target,
      interiorChart_target]
  · rw [scalarRegularSublevelChartAt_of_lt hf hreg hn hx, halfSpaceChart_source, mem_preimage] at hw
    rw [scalarRegularSublevelChartAt_of_lt hf hreg hn hx, coe_halfSpaceChart_apply _ _ hw,
      interiorChart_apply, centredChart_apply]
    rw [interiorChart_source] at hw
    exact ⟨hw.2, rfl⟩

/-- Each preferred chart of the sublevel is the half-space restriction of a chart of `M` from its
maximal atlas, read in `ℝⁿ⁺¹` by a smooth homeomorphism with smooth inverse. -/
private theorem exists_scalarRegularSublevelChartAt_eq_halfSpaceChart {m : ℕ∞ω} [IsManifold I m M]
    (hm : 1 ≤ m) (hfm : ContMDiff I 𝓘(ℝ) m f) (x : {x | f x ≤ a}) :
    ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
      (he : ∀ w ∈ e.source, w ∈ {x | f x ≤ a} ↔ 0 ≤ e w 0) (y : {x | f x ≤ a}),
      IsExtendTransChart I m e ∧
        scalarRegularSublevelChartAt (hfm.of_le hm) hreg hn x = e.halfSpaceChart he y := by
  have hxa : f x ≤ a := x.2
  rcases hxa.lt_or_eq with hx | hx
  · exact ⟨_, _, x,
      exists_interiorChart_eq_extendTrans (isOpen_Iio.preimage (hfm.of_le hm).continuous) hn _,
      scalarRegularSublevelChartAt_of_lt _ hreg hn hx⟩
  · exact ⟨_, _, x, ⟨_, _, scalarSubmersionChartAt_mem_maximalAtlas _ _ hm fun _ _ ↦
        hfm.contMDiffAt,
      (scalarRegularSublevelFaceEquiv hn (hreg.isRegularPoint hx)).contDiff,
      (scalarRegularSublevelFaceEquiv hn (hreg.isRegularPoint hx)).symm.contDiff, rfl⟩,
      scalarRegularSublevelChartAt_of_eq _ hreg hn hx⟩

/-- **A sublevel at a regular value is a manifold with boundary.** If `f` is `C^m`, `m ≥ 1`, and
`a` is a regular value of `f`, then the sublevel `{x | f x ≤ a}` is a `C^m` manifold with boundary
for its preferred atlas `TauCeti.scalarRegularSublevelChartedSpace`, modelled on the half-space
`EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`. -/
theorem isManifold_scalarRegularSublevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    IsManifold (𝓡∂ (n + 1)) m {x | f x ≤ a} := by
  let := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
  refine isManifold_of_forall_mem_atlas (I := I) fun e he ↦ ?_
  rw [scalarRegularSublevelChartedSpace_atlas] at he
  obtain ⟨x, rfl⟩ := he
  exact exists_scalarRegularSublevelChartAt_eq_halfSpaceChart hreg hn hm hfm x

/-- **The boundary of a sublevel at a regular value is the level.** If `f` is `C^m`, `m ≥ 1`, and
`a` is a regular value of `f`, then the manifold boundary of the sublevel `{x | f x ≤ a}`, for its
preferred atlas, is the level `f⁻¹(a)`. -/
theorem boundary_scalarRegularSublevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    (𝓡∂ (n + 1)).boundary {x | f x ≤ a} = {x : {x | f x ≤ a} | f x = a} := by
  let := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn hm hfm
  ext x
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas
    (ENat.one_le_iff_ne_zero_withTop.1 hm) (chart_mem_atlas _ x) (mem_chart_source _ x),
    scalarRegularSublevelChartedSpace_chartAt, mem_ofPred_eq]
  have hxa : f x ≤ a := x.2
  rcases hxa.lt_or_eq with hx | hx
  · obtain ⟨r, hr, -, happly⟩ := exists_scalarRegularSublevelChartAt_of_lt (hfm.of_le hm) hreg hn hx
    rw [(happly x (mem_scalarRegularSublevelChartAt_source _ hreg hn x)).2, sub_self, map_zero,
      zero_add]
    simp only [EuclideanSpace.single, PiLp.single_apply, ite_true]
    exact iff_of_false (by positivity) hx.ne
  · rw [scalarRegularSublevelChartAt_apply_zero_of_eq _ hreg hn hx
      (mem_scalarRegularSublevelChartAt_source _ hreg hn x), hx, sub_self]
    exact iff_of_true rfl rfl

/-- The manifold interior of the sublevel `{x | f x ≤ a}` at a regular value `a` of a `C^m`
function, `m ≥ 1`, for its preferred atlas, is the strict sublevel `{x | f x < a}`. -/
theorem interior_scalarRegularSublevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) :
    letI := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
    (𝓡∂ (n + 1)).interior {x | f x ≤ a} = {x : {x | f x ≤ a} | f x < a} := by
  let := scalarRegularSublevelChartedSpace (hfm.of_le hm) hreg hn
  rw [← ModelWithCorners.compl_boundary, boundary_scalarRegularSublevel hreg hn hm hfm]
  ext x
  have hxa : f x ≤ a := x.2
  simp only [mem_compl_iff, mem_ofPred_eq]
  exact ⟨fun h ↦ hxa.lt_of_ne h, ne_of_lt⟩

end Sublevel

section Band

variable [I.Boundaryless] [FiniteDimensional ℝ E] {b : ℝ}

variable (I) in
/-- The face chart of the band `f⁻¹([a, b])` at a regular point `x` of the lower level `f⁻¹(a)`:
the submersion chart of `f` at `x`, restricted to `{f < b}` and read in `ℝⁿ⁺¹` through
`TauCeti.scalarRegularBandLowerFaceEquiv`. -/
private noncomputable abbrev lowerFaceChart (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hn : finrank ℝ E = n + 1) (b : ℝ) {x : M} (hx : IsRegularPoint I 𝓘(ℝ) f x) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  restrFaceChart I hf.contMDiffAt hx (f ⁻¹' Iio b) (scalarRegularBandLowerFaceEquiv hn hx)

variable (I) in
/-- The face chart of the band `f⁻¹([a, b])` at a regular point `x` of the upper level `f⁻¹(b)`:
the submersion chart of `f` at `x`, restricted to `{a < f}` and read in `ℝⁿ⁺¹` through
`TauCeti.scalarRegularSublevelFaceEquiv`. -/
private noncomputable abbrev upperFaceChart (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hn : finrank ℝ E = n + 1) (a : ℝ) {x : M} (hx : IsRegularPoint I 𝓘(ℝ) f x) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
  restrFaceChart I hf.contMDiffAt hx (f ⁻¹' Ioi a) (scalarRegularSublevelFaceEquiv hn hx)

variable (hf : ContMDiff I 𝓘(ℝ) 1 f) (hn : finrank ℝ E = n + 1)

/-- The zeroth coordinate of the lower face chart at `x` is `f - f x`. -/
private theorem lowerFaceChart_apply_zero {x : M} (hx : IsRegularPoint I 𝓘(ℝ) f x) {w : M}
    (hw : w ∈ (chartAt H x).source) : lowerFaceChart I hf hn b hx w 0 = f w - f x := by
  have h := scalarRegularSublevelFaceEquiv_apply_zero hn hx
    ((scalarSubmersionChartAt hf.contMDiffAt hx).extend I w)
  rw [← faceChart_apply_eq hn hf.contMDiffAt hx, faceChart_apply hn _ hx hw,
    euclideanFinConsEquiv_apply_zero] at h
  rw [restrFaceChart_apply, scalarRegularBandLowerFaceEquiv_apply_zero]
  linarith

/-- The zeroth coordinate of the upper face chart at `x` is `f x - f`. -/
private theorem upperFaceChart_apply_zero {x : M} (hx : IsRegularPoint I 𝓘(ℝ) f x) {w : M}
    (hw : w ∈ (chartAt H x).source) : upperFaceChart I hf hn a hx w 0 = f x - f w := by
  rw [restrFaceChart_apply, ← faceChart_apply_eq hn hf.contMDiffAt hx, faceChart_apply hn _ hx hw,
    euclideanFinConsEquiv_apply_zero]

/-- On the source of a face chart, the submersion chart at `x` is defined, hence so is the preferred
chart of `M` at `x`. -/
private theorem mem_chartAt_source_of_mem_restrFaceChart_source {x : M}
    (hx : IsRegularPoint I 𝓘(ℝ) f x) {V : Set M} (hV : IsOpen V)
    (Ψ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) {w : M}
    (hw : w ∈ (restrFaceChart I hf.contMDiffAt hx V Ψ).source) :
    w ∈ (chartAt H x).source ∧ w ∈ V := by
  rw [restrFaceChart_source _ _ _ hV, scalarSubmersionChartAt_source] at hw
  exact ⟨hw.1.1, hw.2⟩

private theorem lowerFaceChart_mem_iff {x : M} (hx : IsRegularPoint I 𝓘(ℝ) f x) (hxa : f x = a) :
    ∀ w ∈ (lowerFaceChart I hf hn b hx).source,
      w ∈ f ⁻¹' Icc a b ↔ 0 ≤ lowerFaceChart I hf hn b hx w 0 := by
  intro w hw
  obtain ⟨hw₁, hw₂⟩ := mem_chartAt_source_of_mem_restrFaceChart_source hf hx
    (isOpen_Iio.preimage hf.continuous) _ hw
  rw [lowerFaceChart_apply_zero hf hn hx hw₁, hxa, sub_nonneg, mem_preimage, mem_Icc]
  exact and_iff_left (mem_Iio.1 (mem_preimage.1 hw₂)).le

private theorem upperFaceChart_mem_iff {x : M} (hx : IsRegularPoint I 𝓘(ℝ) f x) (hxb : f x = b) :
    ∀ w ∈ (upperFaceChart I hf hn a hx).source,
      w ∈ f ⁻¹' Icc a b ↔ 0 ≤ upperFaceChart I hf hn a hx w 0 := by
  intro w hw
  obtain ⟨hw₁, hw₂⟩ := mem_chartAt_source_of_mem_restrFaceChart_source hf hx
    (isOpen_Ioi.preimage hf.continuous) _ hw
  rw [upperFaceChart_apply_zero hf hn hx hw₁, hxb, sub_nonneg, mem_preimage, mem_Icc]
  exact and_iff_right (mem_Ioi.1 (mem_preimage.1 hw₂)).le

omit [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless] [FiniteDimensional ℝ E] in
private theorem mem_preimage_Ioo_of_ne {x : M} (hx : x ∈ f ⁻¹' Icc a b) (hxa : f x ≠ a)
    (hxb : f x ≠ b) : x ∈ f ⁻¹' Ioo a b := by
  obtain ⟨h₁, h₂⟩ := mem_Icc.1 (mem_preimage.1 hx)
  exact mem_preimage.2 (mem_Ioo.2 ⟨h₁.lt_of_ne (Ne.symm hxa), h₂.lt_of_ne hxb⟩)

variable (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)

/-- The preferred chart at a point `x` of the band `f⁻¹([a, b])` of a `C¹` function between regular
values `a < b`, modelled on the half-space `EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`.

At a point of the lower level `f⁻¹(a)` it is the submersion chart of `f` at `x`, restricted to
`{f < b}`, with the inward coordinate `f - a` in slot `0` and the tangential coordinates of the
level chart in slots `1, …, n` (`TauCeti.scalarRegularBandChartAt_apply_zero_of_eq_left`,
`TauCeti.scalarRegularBandChartAt_apply_succ_eq_regularLevelChartAt_of_eq_left`). At a point of the
upper level `f⁻¹(b)` it is the face chart of the sublevel `{f ≤ b}`, restricted to `{a < f}`, with
the inward coordinate `b - f` in slot `0` and the same kind of tangential coordinates
(`TauCeti.scalarRegularBandChartAt_apply_zero_of_eq_right`,
`TauCeti.scalarRegularBandChartAt_apply_succ_eq_regularLevelChartAt_of_eq_right`). At a point of
`{a < f < b}` it is an interior chart, whose target is a ball in the open half-space
(`TauCeti.exists_scalarRegularBandChartAt_of_mem_Ioo`). -/
noncomputable def scalarRegularBandChartAt (x : f ⁻¹' Icc a b) :
    OpenPartialHomeomorph (f ⁻¹' Icc a b) (EuclideanHalfSpace (n + 1)) :=
  if hxa : f x = a then
    (lowerFaceChart I hf hn b (ha.isRegularPoint hxa)).halfSpaceChart
      (lowerFaceChart_mem_iff hf hn (ha.isRegularPoint hxa) hxa) x
  else if hxb : f x = b then
    (upperFaceChart I hf hn a (hb.isRegularPoint hxb)).halfSpaceChart
      (upperFaceChart_mem_iff hf hn (hb.isRegularPoint hxb) hxb) x
  else
    (interiorChart I (isOpen_Ioo.preimage hf.continuous) hn
        (mem_preimage_Ioo_of_ne x.2 hxa hxb)).halfSpaceChart
      (interiorChart_mem_iff _ hn _ (preimage_mono Ioo_subset_Icc_self)) x

private theorem scalarRegularBandChartAt_of_eq_left {x : f ⁻¹' Icc a b} (hx : f x = a) :
    scalarRegularBandChartAt hf hn ha hb x =
      (lowerFaceChart I hf hn b (ha.isRegularPoint hx)).halfSpaceChart
        (lowerFaceChart_mem_iff hf hn (ha.isRegularPoint hx) hx) x :=
  dite_eq_left hx

private theorem scalarRegularBandChartAt_of_eq_right (hab : a < b) {x : f ⁻¹' Icc a b}
    (hx : f x = b) :
    scalarRegularBandChartAt hf hn ha hb x =
      (upperFaceChart I hf hn a (hb.isRegularPoint hx)).halfSpaceChart
        (upperFaceChart_mem_iff hf hn (hb.isRegularPoint hx) hx) x :=
  (dite_eq_right (by rw [hx]; exact hab.ne')).trans (dite_eq_left hx)

private theorem scalarRegularBandChartAt_of_ne {x : f ⁻¹' Icc a b} (hxa : f x ≠ a)
    (hxb : f x ≠ b) :
    scalarRegularBandChartAt hf hn ha hb x =
      (interiorChart I (isOpen_Ioo.preimage hf.continuous) hn
          (mem_preimage_Ioo_of_ne x.2 hxa hxb)).halfSpaceChart
        (interiorChart_mem_iff _ hn _ (preimage_mono Ioo_subset_Icc_self)) x :=
  (dite_eq_right hxa).trans (dite_eq_right hxb)

variable (hab : a < b)
include hab in
/-- Every point of the band lies in the source of its preferred chart. -/
theorem mem_scalarRegularBandChartAt_source (x : f ⁻¹' Icc a b) :
    x ∈ (scalarRegularBandChartAt hf hn ha hb x).source := by
  by_cases hxa : f x = a
  · rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hxa, halfSpaceChart_source, mem_preimage,
      restrFaceChart_source _ _ _ (isOpen_Iio.preimage hf.continuous)]
    exact ⟨mem_scalarSubmersionChartAt_source _ _, mem_preimage.2 (mem_Iio.2 (by rwa [hxa]))⟩
  by_cases hxb : f x = b
  · rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hxb, halfSpaceChart_source,
      mem_preimage, restrFaceChart_source _ _ _ (isOpen_Ioi.preimage hf.continuous)]
    exact ⟨mem_scalarSubmersionChartAt_source _ _, mem_preimage.2 (mem_Ioi.2 (by rwa [hxb]))⟩
  rw [scalarRegularBandChartAt_of_ne hf hn ha hb hxa hxb, halfSpaceChart_source, mem_preimage,
    interiorChart_source]
  refine ⟨⟨by rw [centredChart_source]; exact mem_chart_source H _, ?_⟩,
    mem_preimage_Ioo_of_ne x.2 hxa hxb⟩
  rw [mem_preimage, centredChart_apply, sub_self, map_zero]
  exact mem_ball_self (interiorRadius_pos (isOpen_Ioo.preimage hf.continuous) hn _)

/-- The atlas of the band `f⁻¹([a, b])` of a `C¹` function between regular values `a < b`,
modelled on the half-space `EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`, with preferred
charts `TauCeti.scalarRegularBandChartAt`. -/
@[irreducible]
noncomputable def scalarRegularBandChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) (f ⁻¹' Icc a b) where
  atlas := range (scalarRegularBandChartAt hf hn ha hb)
  chartAt := scalarRegularBandChartAt hf hn ha hb
  mem_chart_source := mem_scalarRegularBandChartAt_source hf hn ha hb hab
  chart_mem_atlas := mem_range_self

/-- The installed preferred charts are `TauCeti.scalarRegularBandChartAt`. -/
@[simp]
theorem scalarRegularBandChartedSpace_chartAt (x : f ⁻¹' Icc a b) :
    @chartAt (EuclideanHalfSpace (n + 1)) _ (f ⁻¹' Icc a b) _
        (scalarRegularBandChartedSpace hf hn ha hb hab) x =
      scalarRegularBandChartAt hf hn ha hb x := by
  unfold scalarRegularBandChartedSpace
  rfl

/-- The installed atlas consists exactly of the preferred charts. -/
@[simp]
theorem scalarRegularBandChartedSpace_atlas :
    @atlas (EuclideanHalfSpace (n + 1)) _ (f ⁻¹' Icc a b) _
        (scalarRegularBandChartedSpace hf hn ha hb hab) =
      range (scalarRegularBandChartAt hf hn ha hb) := by
  unfold atlas scalarRegularBandChartedSpace
  rfl

omit hab

section LowerFace

variable {x : f ⁻¹' Icc a b} (hx : f x = a)
include hx

/-- The source of the preferred chart at a point `x` of the lower level `f⁻¹(a)` is the part of the
band in the source of the submersion chart of `f` at `x` where `f < b`. -/
theorem scalarRegularBandChartAt_source_of_eq_left :
    (scalarRegularBandChartAt hf hn ha hb x).source = Subtype.val ⁻¹'
      ((scalarSubmersionChartAt hf.contMDiffAt (ha.isRegularPoint hx)).source ∩
        f ⁻¹' Iio b) := by
  rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hx, halfSpaceChart_source,
    restrFaceChart_source _ _ _ (isOpen_Iio.preimage hf.continuous)]

/-- At a point `x` of the lower level `f⁻¹(a)`, the preferred chart reads a point of its source in
the extended submersion chart of `f` at `x`, followed by
`TauCeti.scalarRegularBandLowerFaceEquiv`. -/
theorem scalarRegularBandChartAt_apply_of_eq_left {w : f ⁻¹' Icc a b}
    (hw : w ∈ (scalarRegularBandChartAt hf hn ha hb x).source) :
    (scalarRegularBandChartAt hf hn ha hb x w).1 =
      scalarRegularBandLowerFaceEquiv hn (ha.isRegularPoint hx)
        ((scalarSubmersionChartAt hf.contMDiffAt (ha.isRegularPoint hx)).extend I w) := by
  rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hx, halfSpaceChart_source, mem_preimage] at hw
  rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hx, coe_halfSpaceChart_apply _ _ hw,
    restrFaceChart_apply]

/-- At a point `x` of the lower level `f⁻¹(a)`, a point `z` of the half-space lies in the target of
the preferred chart exactly when `TauCeti.scalarRegularBandLowerFaceEquiv` sends it back into the
target of the extended submersion chart of `f` at `x`, at a point where `f < b`. -/
theorem mem_scalarRegularBandChartAt_target_iff_of_eq_left (z : EuclideanHalfSpace (n + 1)) :
    z ∈ (scalarRegularBandChartAt hf hn ha hb x).target ↔
      (scalarRegularBandLowerFaceEquiv hn (ha.isRegularPoint hx)).symm z.1 ∈
          ((scalarSubmersionChartAt hf.contMDiffAt (ha.isRegularPoint hx)).extend I).target ∧
        f (((scalarSubmersionChartAt hf.contMDiffAt (ha.isRegularPoint hx)).extend I).symm
          ((scalarRegularBandLowerFaceEquiv hn (ha.isRegularPoint hx)).symm z.1)) < b := by
  rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hx, halfSpaceChart_target, mem_preimage,
    OpenPartialHomeomorph.extend_target, I.range_eq_univ, inter_univ]
  simp [restrFaceChart, (isOpen_Iio.preimage hf.continuous).interior_eq, mfld_simps]

/-- At a point `x` of the lower level `f⁻¹(a)`, the inverse of the preferred chart is the inverse of
`TauCeti.scalarRegularBandLowerFaceEquiv` followed by the inverse extended submersion chart of `f`
at `x`. -/
theorem coe_scalarRegularBandChartAt_symm_apply_of_eq_left {z : EuclideanHalfSpace (n + 1)}
    (hz : z ∈ (scalarRegularBandChartAt hf hn ha hb x).target) :
    ((scalarRegularBandChartAt hf hn ha hb x).symm z : M) =
      ((scalarSubmersionChartAt hf.contMDiffAt (ha.isRegularPoint hx)).extend I).symm
        ((scalarRegularBandLowerFaceEquiv hn (ha.isRegularPoint hx)).symm z.1) := by
  rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hx] at hz ⊢
  rw [halfSpaceChart_target, mem_preimage, modelWithCornersEuclideanHalfSpace_toFun] at hz
  rw [coe_halfSpaceChart_symm_apply _ _ hz, restrFaceChart_symm_apply]

/-- At a point `x` of the lower level `f⁻¹(a)`, the zeroth coordinate of the preferred chart is the
inward coordinate `f - a`. -/
theorem scalarRegularBandChartAt_apply_zero_of_eq_left {w : f ⁻¹' Icc a b}
    (hw : w ∈ (scalarRegularBandChartAt hf hn ha hb x).source) :
    (scalarRegularBandChartAt hf hn ha hb x w).1 0 = f w - a := by
  rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hx, halfSpaceChart_source, mem_preimage] at hw
  rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hx, coe_halfSpaceChart_apply _ _ hw,
    lowerFaceChart_apply_zero hf hn _
      (mem_chartAt_source_of_mem_restrFaceChart_source hf _
        (isOpen_Iio.preimage hf.continuous) _ hw).1, hx]

/-- **On the lower level, the tangential coordinates are those of the level chart.** At a point `x`
of the lower level `f⁻¹(a)`, the coordinates in slots `1, …, n` of the preferred chart of the
band at a point `w` of that level are the coordinates of the preferred level chart
`TauCeti.regularLevelChartAt` at `x`, reindexed along `dim E - 1 = n`. -/
theorem scalarRegularBandChartAt_apply_succ_eq_regularLevelChartAt_of_eq_left
    {w : f ⁻¹' Icc a b} (hw : w ∈ (scalarRegularBandChartAt hf hn ha hb x).source) (hwa : f w = a)
    (i : Fin n) :
    (scalarRegularBandChartAt hf hn ha hb x w).1 i.succ =
      regularLevelChartAt (n := finrank ℝ E - 1) (fun y _ ↦ hf.contMDiffAt) ha
        (by rw [finrank_self]) ⟨x, hx⟩ ⟨w, hwa⟩ (Fin.cast (by omega) i) := by
  have hw' := hw
  rw [scalarRegularBandChartAt_of_eq_left hf hn ha hb hx, halfSpaceChart_source,
    mem_preimage] at hw'
  rw [scalarRegularBandChartAt_apply_of_eq_left hf hn ha hb hx hw,
    scalarRegularBandLowerFaceEquiv_apply_succ, ← faceChart_apply_eq hn hf.contMDiffAt,
    faceChart_apply hn _ _ (mem_chartAt_source_of_mem_restrFaceChart_source hf _
      (isOpen_Iio.preimage hf.continuous) _ hw').1, euclideanFinConsEquiv_apply_succ,
    regularLevelChartAt_apply]

end LowerFace

section UpperFace

variable (hab : a < b) {x : f ⁻¹' Icc a b} (hx : f x = b)
include hab hx

/-- The source of the preferred chart at a point `x` of the upper level `f⁻¹(b)` is the part of the
band in the source of the submersion chart of `f` at `x` where `a < f`. -/
theorem scalarRegularBandChartAt_source_of_eq_right :
    (scalarRegularBandChartAt hf hn ha hb x).source = Subtype.val ⁻¹'
      ((scalarSubmersionChartAt hf.contMDiffAt (hb.isRegularPoint hx)).source ∩
        f ⁻¹' Ioi a) := by
  rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hx, halfSpaceChart_source,
    restrFaceChart_source _ _ _ (isOpen_Ioi.preimage hf.continuous)]

/-- At a point `x` of the upper level `f⁻¹(b)`, the preferred chart reads a point of its source in
the extended submersion chart of `f` at `x`, followed by `TauCeti.scalarRegularSublevelFaceEquiv`.
-/
theorem scalarRegularBandChartAt_apply_of_eq_right {w : f ⁻¹' Icc a b}
    (hw : w ∈ (scalarRegularBandChartAt hf hn ha hb x).source) :
    (scalarRegularBandChartAt hf hn ha hb x w).1 =
      scalarRegularSublevelFaceEquiv hn (hb.isRegularPoint hx)
        ((scalarSubmersionChartAt hf.contMDiffAt (hb.isRegularPoint hx)).extend I w) := by
  rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hx, halfSpaceChart_source,
    mem_preimage] at hw
  rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hx, coe_halfSpaceChart_apply _ _ hw,
    restrFaceChart_apply]

/-- At a point `x` of the upper level `f⁻¹(b)`, a point `z` of the half-space lies in the target of
the preferred chart exactly when `TauCeti.scalarRegularSublevelFaceEquiv` sends it back into the
target of the extended submersion chart of `f` at `x`, at a point where `a < f`. -/
theorem mem_scalarRegularBandChartAt_target_iff_of_eq_right (z : EuclideanHalfSpace (n + 1)) :
    z ∈ (scalarRegularBandChartAt hf hn ha hb x).target ↔
      (scalarRegularSublevelFaceEquiv hn (hb.isRegularPoint hx)).symm z.1 ∈
          ((scalarSubmersionChartAt hf.contMDiffAt (hb.isRegularPoint hx)).extend I).target ∧
        a < f (((scalarSubmersionChartAt hf.contMDiffAt (hb.isRegularPoint hx)).extend I).symm
          ((scalarRegularSublevelFaceEquiv hn (hb.isRegularPoint hx)).symm z.1)) := by
  rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hx, halfSpaceChart_target, mem_preimage,
    OpenPartialHomeomorph.extend_target, I.range_eq_univ, inter_univ]
  simp [restrFaceChart, (isOpen_Ioi.preimage hf.continuous).interior_eq, mfld_simps]

/-- At a point `x` of the upper level `f⁻¹(b)`, the inverse of the preferred chart is the inverse of
`TauCeti.scalarRegularSublevelFaceEquiv` followed by the inverse extended submersion chart of `f`
at `x`. -/
theorem coe_scalarRegularBandChartAt_symm_apply_of_eq_right {z : EuclideanHalfSpace (n + 1)}
    (hz : z ∈ (scalarRegularBandChartAt hf hn ha hb x).target) :
    ((scalarRegularBandChartAt hf hn ha hb x).symm z : M) =
      ((scalarSubmersionChartAt hf.contMDiffAt (hb.isRegularPoint hx)).extend I).symm
        ((scalarRegularSublevelFaceEquiv hn (hb.isRegularPoint hx)).symm z.1) := by
  rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hx] at hz ⊢
  rw [halfSpaceChart_target, mem_preimage, modelWithCornersEuclideanHalfSpace_toFun] at hz
  rw [coe_halfSpaceChart_symm_apply _ _ hz, restrFaceChart_symm_apply]

/-- At a point `x` of the upper level `f⁻¹(b)`, the zeroth coordinate of the preferred chart is the
inward coordinate `b - f`. -/
theorem scalarRegularBandChartAt_apply_zero_of_eq_right {w : f ⁻¹' Icc a b}
    (hw : w ∈ (scalarRegularBandChartAt hf hn ha hb x).source) :
    (scalarRegularBandChartAt hf hn ha hb x w).1 0 = b - f w := by
  rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hx, halfSpaceChart_source,
    mem_preimage] at hw
  rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hx, coe_halfSpaceChart_apply _ _ hw,
    upperFaceChart_apply_zero hf hn _
      (mem_chartAt_source_of_mem_restrFaceChart_source hf _
        (isOpen_Ioi.preimage hf.continuous) _ hw).1, hx]

/-- **On the upper level, the tangential coordinates are those of the level chart.** At a point `x`
of the upper level `f⁻¹(b)`, the coordinates in slots `1, …, n` of the preferred chart of the
band at a point `w` of that level are the coordinates of the preferred level chart
`TauCeti.regularLevelChartAt` at `x`, reindexed along `dim E - 1 = n`. -/
theorem scalarRegularBandChartAt_apply_succ_eq_regularLevelChartAt_of_eq_right
    {w : f ⁻¹' Icc a b} (hw : w ∈ (scalarRegularBandChartAt hf hn ha hb x).source) (hwb : f w = b)
    (i : Fin n) :
    (scalarRegularBandChartAt hf hn ha hb x w).1 i.succ =
      regularLevelChartAt (n := finrank ℝ E - 1) (fun y _ ↦ hf.contMDiffAt) hb
        (by rw [finrank_self]) ⟨x, hx⟩ ⟨w, hwb⟩ (Fin.cast (by omega) i) := by
  have hw' := hw
  rw [scalarRegularBandChartAt_of_eq_right hf hn ha hb hab hx, halfSpaceChart_source,
    mem_preimage] at hw'
  rw [scalarRegularBandChartAt_apply_of_eq_right hf hn ha hb hab hx hw,
    ← faceChart_apply_eq hn hf.contMDiffAt,
    faceChart_apply hn _ _ (mem_chartAt_source_of_mem_restrFaceChart_source hf _
      (isOpen_Ioi.preimage hf.continuous) _ hw').1, euclideanFinConsEquiv_apply_succ,
    regularLevelChartAt_apply]

end UpperFace

/-- At a point `x` of `{a < f < b}`, the preferred chart of the band is an interior chart: for some
`r > 0` its target is the ball of radius `r` about the point `2 r e₀` of the open half-space, its
source lies in `{a < f < b}`, and it reads a point `w` as `T (extChartAt I x w - extChartAt I x x)`,
translated by `2 r e₀`, for a fixed linear equivalence `T : E ≃ ℝⁿ⁺¹`. -/
theorem exists_scalarRegularBandChartAt_of_mem_Ioo {x : f ⁻¹' Icc a b} (hx : f x ∈ Ioo a b) :
    ∃ r > 0, (scalarRegularBandChartAt hf hn ha hb x).target =
        (𝓡∂ (n + 1)) ⁻¹' ball (EuclideanSpace.single 0 (2 * r)) r ∧
      ∀ w ∈ (scalarRegularBandChartAt hf hn ha hb x).source, f w ∈ Ioo a b ∧
        (scalarRegularBandChartAt hf hn ha hb x w).1 =
          ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
              (F := EuclideanSpace ℝ (Fin (n + 1))) (by rw [hn, finrank_euclideanSpace_fin])
            (extChartAt I (x : M) w - extChartAt I (x : M) x) +
          EuclideanSpace.single 0 (2 * r) := by
  have hxa : f x ≠ a := (mem_Ioo.1 hx).1.ne'
  have hxb : f x ≠ b := (mem_Ioo.1 hx).2.ne
  refine ⟨interiorRadius I (isOpen_Ioo.preimage hf.continuous) hn
      (mem_preimage_Ioo_of_ne x.2 hxa hxb), interiorRadius_pos _ hn _, ?_, fun w hw ↦ ?_⟩
  · rw [scalarRegularBandChartAt_of_ne hf hn ha hb hxa hxb, halfSpaceChart_target,
      interiorChart_target]
  · rw [scalarRegularBandChartAt_of_ne hf hn ha hb hxa hxb, halfSpaceChart_source,
      mem_preimage] at hw
    rw [scalarRegularBandChartAt_of_ne hf hn ha hb hxa hxb, coe_halfSpaceChart_apply _ _ hw,
      interiorChart_apply, centredChart_apply]
    rw [interiorChart_source] at hw
    exact ⟨mem_preimage.1 hw.2, rfl⟩

/-- Each preferred chart of the band is the half-space restriction of a chart of `M` from its
maximal atlas, read in `ℝⁿ⁺¹` by a smooth homeomorphism with smooth inverse. -/
private theorem exists_scalarRegularBandChartAt_eq_halfSpaceChart {m : ℕ∞ω} [IsManifold I m M]
    (hm : 1 ≤ m) (hfm : ContMDiff I 𝓘(ℝ) m f) (hab : a < b) (x : f ⁻¹' Icc a b) :
    ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
      (he : ∀ w ∈ e.source, w ∈ f ⁻¹' Icc a b ↔ 0 ≤ e w 0) (y : f ⁻¹' Icc a b),
      IsExtendTransChart I m e ∧
        scalarRegularBandChartAt (hfm.of_le hm) hn ha hb x = e.halfSpaceChart he y := by
  by_cases hxa : f x = a
  · exact ⟨_, _, x, isExtendTransChart_restrFaceChart hm hfm _
      (isOpen_Iio.preimage (hfm.of_le hm).continuous) _,
      scalarRegularBandChartAt_of_eq_left _ hn ha hb hxa⟩
  by_cases hxb : f x = b
  · exact ⟨_, _, x, isExtendTransChart_restrFaceChart hm hfm _
      (isOpen_Ioi.preimage (hfm.of_le hm).continuous) _,
      scalarRegularBandChartAt_of_eq_right _ hn ha hb hab hxb⟩
  · exact ⟨_, _, x,
      exists_interiorChart_eq_extendTrans (isOpen_Ioo.preimage (hfm.of_le hm).continuous) hn _,
      scalarRegularBandChartAt_of_ne _ hn ha hb hxa hxb⟩

/-- **A band between regular values is a manifold with boundary.** If `f` is `C^m`, `m ≥ 1`, and
`a < b` are regular values of `f`, then the band `f⁻¹([a, b])` is a `C^m` manifold with boundary
for its preferred atlas `TauCeti.scalarRegularBandChartedSpace`, modelled on the half-space
`EuclideanHalfSpace (n + 1)`, where `n + 1 = dim E`. -/
theorem isManifold_scalarRegularBand {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) (hab : a < b) :
    letI := scalarRegularBandChartedSpace (hfm.of_le hm) hn ha hb hab
    IsManifold (𝓡∂ (n + 1)) m (f ⁻¹' Icc a b) := by
  let := scalarRegularBandChartedSpace (hfm.of_le hm) hn ha hb hab
  refine isManifold_of_forall_mem_atlas (I := I) fun e he ↦ ?_
  rw [scalarRegularBandChartedSpace_atlas] at he
  obtain ⟨x, rfl⟩ := he
  exact exists_scalarRegularBandChartAt_eq_halfSpaceChart hn ha hb hm hfm hab x

/-- **The boundary of a band between regular values is the union of its two levels.** If `f` is
`C^m`, `m ≥ 1`, and `a < b` are regular values of `f`, then the manifold boundary of the band
`f⁻¹([a, b])`, for its preferred atlas, consists of the points where `f = a` or `f = b`. -/
theorem boundary_scalarRegularBand {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) (hab : a < b) :
    letI := scalarRegularBandChartedSpace (hfm.of_le hm) hn ha hb hab
    (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) = {x : f ⁻¹' Icc a b | f x = a ∨ f x = b} := by
  let := scalarRegularBandChartedSpace (hfm.of_le hm) hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb hm hfm hab
  ext x
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas
    (ENat.one_le_iff_ne_zero_withTop.1 hm) (chart_mem_atlas _ x) (mem_chart_source _ x),
    scalarRegularBandChartedSpace_chartAt, mem_ofPred_eq]
  have hsrc := mem_scalarRegularBandChartAt_source (hfm.of_le hm) hn ha hb hab x
  by_cases hxa : f x = a
  · rw [scalarRegularBandChartAt_apply_zero_of_eq_left _ hn ha hb hxa hsrc, hxa, sub_self]
    exact iff_of_true rfl (Or.inl rfl)
  by_cases hxb : f x = b
  · rw [scalarRegularBandChartAt_apply_zero_of_eq_right _ hn ha hb hab hxb hsrc, hxb, sub_self]
    exact iff_of_true rfl (Or.inr rfl)
  obtain ⟨r, hr, -, happly⟩ := exists_scalarRegularBandChartAt_of_mem_Ioo (hfm.of_le hm) hn ha hb
    (mem_preimage.1 (mem_preimage_Ioo_of_ne x.2 hxa hxb))
  rw [(happly x hsrc).2, sub_self, map_zero, zero_add]
  simp only [EuclideanSpace.single, PiLp.single_apply, ite_true]
  exact iff_of_false (by positivity) (by tauto)

/-- The manifold interior of the band `f⁻¹([a, b])` between regular values `a < b` of a `C^m`
function, `m ≥ 1`, for its preferred atlas, is the open band `f⁻¹((a, b))`. -/
theorem interior_scalarRegularBand {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ContMDiff I 𝓘(ℝ) m f) (hab : a < b) :
    letI := scalarRegularBandChartedSpace (hfm.of_le hm) hn ha hb hab
    (𝓡∂ (n + 1)).interior (f ⁻¹' Icc a b) = {x : f ⁻¹' Icc a b | f x ∈ Ioo a b} := by
  let := scalarRegularBandChartedSpace (hfm.of_le hm) hn ha hb hab
  rw [← ModelWithCorners.compl_boundary, boundary_scalarRegularBand hn ha hb hm hfm hab]
  ext x
  obtain ⟨h₁, h₂⟩ := mem_Icc.1 (mem_preimage.1 x.2)
  simp only [mem_compl_iff, mem_ofPred_eq, mem_Ioo, not_or]
  exact ⟨fun h ↦ ⟨h₁.lt_of_ne (Ne.symm h.1), h₂.lt_of_ne h.2⟩, fun h ↦ ⟨h.1.ne', h.2.ne⟩⟩

end Band

end TauCeti
