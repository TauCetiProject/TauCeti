/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Basic
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Quotient

/-!
# The q-coordinate chart at a cusp of the compactified quotient

Let `Γ ≤ PSL(2, ℝ)` be discrete and `D` a normalized cusp datum of `Γ` with scaling `σ` and width
`w`. For a height `A ≥ w` the horodisc of height `A` at `D` is precisely invariant under the cusp
stabilizer, so the q-coordinate `q(z) = exp (2 * π * I * σ(z) / w)` descends to the image of the
horodisc in the coarse quotient `Γ \ ℍ`, and it extends by `q = 0` to the cusp orbit adjoined in
the compactified quotient. This file packages this extension as an open partial homeomorphism
`Subgroup.CompactifiedQuotient.cuspChart D hA` from the compactified quotient to `ℂ`: its source
is the cusp neighbourhood `cuspNhd D A` and its target the disc of radius `cuspRadius D A`, the
exponential `exp (-2 * π * A / w)` of the height. On the target, the inverse sends `0` to the cusp
orbit and a nonzero `q` to the orbit of the logarithmic lift `σ⁻¹ • invQParam w q`.

Continuity at the cusp orbit is the fact that the q-coordinate tends to `0` along the cusp and,
conversely, that the logarithmic lift of a small `q` lies in a high horodisc. Continuity away from
the cusp orbit comes from the open quotient map `qCoordinate D` onto the punctured unit disc.
The compatibility of these charts with the atlas of the coarse quotient, and the resulting Riemann
surface structure on the compactified quotient, are not part of this file.

## Main declarations

* `Subgroup.CompactifiedQuotient.cuspRadius`: the radius `exp (-2 * π * A / w)` of the q-disc
  corresponding to the horodisc of height `A`.
* `Subgroup.CompactifiedQuotient.cuspChart`: the cusp chart, with
  `Subgroup.CompactifiedQuotient.cuspChart_ofCusp` and
  `Subgroup.CompactifiedQuotient.cuspChart_ofQuotient_mk` computing it on its source, and
  `Subgroup.CompactifiedQuotient.cuspChart_symm_zero`,
  `Subgroup.CompactifiedQuotient.cuspChart_symm_coordinate` and
  `Subgroup.CompactifiedQuotient.cuspChart_symm_of_ne_zero` computing its inverse on its target.

The underlying total maps of the chart and its inverse are implementation details: outside the
source and target their values are junk, so they are private.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §19.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.2.
-/

public noncomputable section

open Filter Function MulAction Set Topology TauCeti.Subgroup.CuspDatum TauCeti.UpperHalfPlane
  UpperHalfPlane
open scoped Complex.UnitDisc MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum) {A : ℝ}

/-! ### The radius of the q-disc -/

variable (A) in
/-- The radius `exp (-2 * π * A / w)` of the punctured q-disc onto which the horodisc of height `A`
is mapped by the q-coordinate of a cusp datum of width `w`. -/
def cuspRadius : ℝ := Real.exp (-2 * Real.pi * A / D.width)

variable (A) in
theorem cuspRadius_pos : 0 < cuspRadius D A := Real.exp_pos _

theorem cuspRadius_lt_one (hA : 0 < A) : cuspRadius D A < 1 := by
  rw [cuspRadius, Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) D.width_pos

theorem cuspRadius_antitone : Antitone (cuspRadius D) := fun _ _ h ↦
  Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) D.width_pos.le)

/-- The radius of the q-disc tends to zero as the height tends to infinity. -/
theorem tendsto_cuspRadius_atTop : Tendsto (cuspRadius D) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp ((tendsto_id.const_mul_atTop_of_neg
    (by nlinarith [Real.pi_pos] : -2 * Real.pi < 0)).atBot_div_const D.width_pos)

variable (A) in
/-- A horodisc is the inverse image of the q-disc of the corresponding radius. -/
theorem norm_coordinate_lt_cuspRadius_iff (z : ℍ) :
    ‖coordinate D z‖ < cuspRadius D A ↔ z ∈ horodisc D A := by
  rw [← coe_qCoordinate, cuspRadius]
  exact norm_qCoordinate_lt_iff_mem_horodisc D A z

/-! ### The forward map

The total map underlying the cusp chart. Its values off the cusp neighbourhood are junk, so it and
its lemmas are private. -/

variable (A) in
/-- The q-coordinate of a cusp datum, descended to the compactified quotient: on the image of the
horodisc of height `A` it is the `coordinate` of any representative, and it is `0` at the cusp
orbits and outside that image. -/
private def cuspChartFun : Γ.CompactifiedQuotient → ℂ :=
  Function.extend (fun z : horodisc D A ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) (z : ℍ)))
    (fun z ↦ coordinate D z) 0

variable (A) in
@[simp]
private theorem cuspChartFun_ofCusp (C : Γ.CuspOrbit) : cuspChartFun D A (ofCusp C) = 0 :=
  Function.extend_apply' _ _ _ (by rintro ⟨z, h⟩; cases h)

/-! ### The inverse map

The total map underlying the inverse of the cusp chart. Its values off the unit disc are junk, so
it and its lemmas are private. -/

/-- The inverse of the cusp chart: `0` goes to the cusp orbit, and a nonzero `q` of the unit disc to
the orbit of the logarithmic lift `σ⁻¹ • invQParam w q`. -/
private def cuspChartInv (q : ℂ) : Γ.CompactifiedQuotient :=
  if q = 0 then ofCusp D.cuspOrbit
  else ofQuotient (Quotient.mk _ (D.scaling⁻¹ • ofComplex (Periodic.invQParam D.width q)))

@[simp]
private theorem cuspChartInv_zero : cuspChartInv D 0 = ofCusp D.cuspOrbit := by
  simp [cuspChartInv]

private theorem cuspChartInv_of_ne_zero {q : ℂ} (hq : q ≠ 0) :
    cuspChartInv D q =
      ofQuotient (Quotient.mk _ (D.scaling⁻¹ • ofComplex (Periodic.invQParam D.width q))) := by
  simp [cuspChartInv, hq]

/-- On the punctured unit disc the inverse is the orbit of the scaled logarithmic lift. -/
private theorem cuspChartInv_coe (q : {q : 𝔻 // q ≠ 0}) :
    cuspChartInv D q =
      ofQuotient (Quotient.mk _ (D.scaling⁻¹ • invQParamUpperHalfPlane D.width D.width_pos q)) := by
  rw [cuspChartInv_of_ne_zero D (fun h ↦ q.2 (Complex.UnitDisc.coe_injective h)),
    ← coe_invQParamUpperHalfPlane D.width D.width_pos q, ofComplex_apply]

/-- The inverse of the cusp chart is a left inverse of the q-coordinate on orbits. -/
@[simp]
private theorem cuspChartInv_coordinate (z : ℍ) :
    cuspChartInv D (coordinate D z) = ofQuotient (Quotient.mk _ z) := by
  rw [← coe_qCoordinate, cuspChartInv_coe]
  obtain ⟨n, hn⟩ := (qCoordinate_eq_iff D _ z).mp (qCoordinate_smul_invQParamUpperHalfPlane D _)
  rw [hn]
  exact congrArg ofQuotient (Quotient.sound (orbitRel_apply.mpr (mem_orbit z _)))

/-- The inverse of the cusp chart sends the q-disc of the radius of a positive height into the
cusp neighbourhood of that height. -/
private theorem cuspChartInv_mem_cuspNhd {q : ℂ} (hA : 0 < A) (hq : ‖q‖ < cuspRadius D A) :
    cuspChartInv D q ∈ cuspNhd D A := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [cuspChartInv_zero]
    exact ofCusp_mem_cuspNhd D A
  · obtain ⟨q', rfl⟩ := TauCeti.Complex.UnitDisc.exists_coe_punctured_eq hq0
      (hq.trans (cuspRadius_lt_one D hA))
    rw [cuspChartInv_coe, ofQuotient_mem_cuspNhd_iff]
    refine ⟨_, ?_, rfl⟩
    rw [← norm_qCoordinate_lt_iff_mem_horodisc, qCoordinate_smul_invQParamUpperHalfPlane]
    exact hq

variable [DiscreteTopology Γ]

/-! ### Continuity -/

private theorem tendsto_cuspChartInv_zero :
    Tendsto (cuspChartInv D) (𝓝 0) (𝓝 (ofCusp D.cuspOrbit)) := by
  refine (nhds_basis_cuspNhd D D.width).tendsto_right_iff.mpr fun B hB ↦ ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (cuspRadius_pos D B)] with q hq
  exact cuspChartInv_mem_cuspNhd D (D.width_pos.trans_le hB) (mem_ball_zero_iff.mp hq)

private theorem continuousAt_cuspChartInv_of_ne_zero {q : ℂ} (hq : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ContinuousAt (cuspChartInv D) q := by
  obtain ⟨q', rfl⟩ := TauCeti.Complex.UnitDisc.exists_coe_punctured_eq hq hq1
  rw [← TauCeti.Complex.UnitDisc.isOpenEmbedding_coe_punctured.continuousAt_iff]
  refine Continuous.continuousAt ?_
  rw [← (isOpenQuotientMap_qCoordinate D).continuous_comp_iff]
  have : (cuspChartInv D ∘ fun q : {q : 𝔻 // q ≠ 0} ↦ ((q : 𝔻) : ℂ)) ∘ qCoordinate D =
      ofQuotient ∘ Quotient.mk _ := by
    funext z
    simp only [comp_apply, coe_qCoordinate, cuspChartInv_coordinate]
  rw [this]
  exact continuous_ofQuotient.comp continuous_quotient_mk'

/-- On the image of a high horodisc, the descended q-coordinate is the q-coordinate of any
representative. -/
@[simp]
private theorem cuspChartFun_ofQuotient_mk (hA : D.width ≤ A) {z : ℍ}
    (hz : z ∈ horodisc D A) :
    cuspChartFun D A (ofQuotient (Quotient.mk _ z)) = coordinate D z := by
  have hfac : (fun z : horodisc D A ↦ coordinate D z).FactorsThrough
      (fun z : horodisc D A ↦ ofQuotient (Quotient.mk (orbitRel Γ ℍ) (z : ℍ))) := fun z z' h ↦ by
    have := (quotientMk_eq_iff_qCoordinate_eq D hA z.2 z'.2).mp (ofQuotient_injective h)
    dsimp only
    rw [← coe_qCoordinate, ← coe_qCoordinate, this]
  exact hfac.extend_apply _ ⟨z, hz⟩

private theorem continuousAt_cuspChartFun_ofQuotient (hA : D.width ≤ A) {z : ℍ}
    (hz : z ∈ horodisc D A) :
    ContinuousAt (cuspChartFun D A) (ofQuotient (Quotient.mk _ z)) := by
  rw [← isOpenEmbedding_ofQuotient.continuousAt_iff,
    ← MulAction.isOpenQuotientMap_quotientMk.continuousAt_comp_iff]
  refine (mdifferentiable_coordinate D).continuous.continuousAt.congr ?_
  filter_upwards [(isOpen_horodisc D A).mem_nhds hz] with τ hτ
  exact (cuspChartFun_ofQuotient_mk D hA hτ).symm

private theorem tendsto_cuspChartFun_ofCusp (hA : D.width ≤ A) :
    Tendsto (cuspChartFun D A) (𝓝 (ofCusp D.cuspOrbit)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose a height `B ≥ A` at which the horodisc maps into the disc of radius `ε`
  obtain ⟨B, hAB, hB⟩ := ((eventually_ge_atTop A).and
    ((tendsto_cuspRadius_atTop D).eventually (gt_mem_nhds hε))).exists
  filter_upwards [cuspNhd_mem_nhds D B] with x hx
  rw [dist_zero_right]
  cases x with
  | ofCusp C => simpa using hε
  | ofQuotient p =>
    obtain ⟨z, hz, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D B).mp hx
    rw [cuspChartFun_ofQuotient_mk D hA (horodisc_antitone D hAB hz)]
    exact ((norm_coordinate_lt_cuspRadius_iff D B z).mpr hz).trans hB

/-! ### The chart -/

variable (hA : D.width ≤ A)

/-- **The cusp chart** of the compactified quotient at the cusp datum `D` and a height `A` at least
its width. Its source is the cusp neighbourhood `cuspNhd D A` and its target the disc of radius
`cuspRadius D A`; it sends the cusp orbit to `0` and the orbit of a point `z` of the horodisc to
its q-coordinate `coordinate D z`. -/
def cuspChart : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ where
  toFun := cuspChartFun D A
  invFun := cuspChartInv D
  source := cuspNhd D A
  target := Metric.ball 0 (cuspRadius D A)
  map_source' x hx := by
    cases x with
    | ofCusp C => simpa using cuspRadius_pos D A
    | ofQuotient p =>
      obtain ⟨z, hz, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D A).mp hx
      rw [cuspChartFun_ofQuotient_mk D hA hz, mem_ball_zero_iff,
        norm_coordinate_lt_cuspRadius_iff]
      exact hz
  map_target' _ hq :=
    cuspChartInv_mem_cuspNhd D (D.width_pos.trans_le hA) (mem_ball_zero_iff.mp hq)
  left_inv' x hx := by
    cases x with
    | ofCusp C =>
      rw [(ofCusp_mem_cuspNhd_iff D A).mp hx]
      simp
    | ofQuotient p =>
      obtain ⟨z, hz, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D A).mp hx
      rw [cuspChartFun_ofQuotient_mk D hA hz, cuspChartInv_coordinate]
  right_inv' q hq := by
    rw [mem_ball_zero_iff] at hq
    rcases eq_or_ne q 0 with rfl | hq0
    · simp
    · obtain ⟨q', rfl⟩ := TauCeti.Complex.UnitDisc.exists_coe_punctured_eq hq0
        (hq.trans (cuspRadius_lt_one D (D.width_pos.trans_le hA)))
      have hz : D.scaling⁻¹ • invQParamUpperHalfPlane D.width D.width_pos q' ∈ horodisc D A := by
        rw [← norm_qCoordinate_lt_iff_mem_horodisc, qCoordinate_smul_invQParamUpperHalfPlane]
        exact hq
      rw [cuspChartInv_coe, cuspChartFun_ofQuotient_mk D hA hz, ← coe_qCoordinate,
        qCoordinate_smul_invQParamUpperHalfPlane]
  open_source := isOpen_cuspNhd D A
  open_target := Metric.isOpen_ball
  continuousOn_toFun := continuousOn_of_forall_continuousAt fun x hx ↦ by
    cases x with
    | ofCusp C =>
      rw [(ofCusp_mem_cuspNhd_iff D A).mp hx, ContinuousAt, cuspChartFun_ofCusp]
      exact tendsto_cuspChartFun_ofCusp D hA
    | ofQuotient p =>
      obtain ⟨z, hz, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D A).mp hx
      exact continuousAt_cuspChartFun_ofQuotient D hA hz
  continuousOn_invFun := continuousOn_of_forall_continuousAt fun q hq ↦ by
    rcases eq_or_ne q 0 with rfl | hq0
    · rw [ContinuousAt, cuspChartInv_zero]
      exact tendsto_cuspChartInv_zero D
    · exact continuousAt_cuspChartInv_of_ne_zero D hq0 ((mem_ball_zero_iff.mp hq).trans
        (cuspRadius_lt_one D (D.width_pos.trans_le hA)))

@[simp]
theorem cuspChart_source : (cuspChart D hA).source = cuspNhd D A := (rfl)

@[simp]
theorem cuspChart_target : (cuspChart D hA).target = Metric.ball 0 (cuspRadius D A) := (rfl)

theorem ofCusp_mem_cuspChart_source : ofCusp D.cuspOrbit ∈ (cuspChart D hA).source :=
  ofCusp_mem_cuspNhd D A

/-- The cusp chart sends its cusp orbit to `0`. -/
@[simp]
theorem cuspChart_ofCusp : cuspChart D hA (ofCusp D.cuspOrbit) = 0 :=
  cuspChartFun_ofCusp D A _

/-- The cusp chart sends the orbit of a point of the horodisc to its q-coordinate. -/
@[simp]
theorem cuspChart_ofQuotient_mk {z : ℍ} (hz : z ∈ horodisc D A) :
    cuspChart D hA (ofQuotient (Quotient.mk _ z)) = coordinate D z :=
  cuspChartFun_ofQuotient_mk D hA hz

/-- The inverse of the cusp chart sends `0` to the cusp orbit. -/
@[simp]
theorem cuspChart_symm_zero : (cuspChart D hA).symm 0 = ofCusp D.cuspOrbit :=
  cuspChartInv_zero D

/-- The inverse of the cusp chart sends the q-coordinate of a point of the horodisc to its orbit. -/
@[simp]
theorem cuspChart_symm_coordinate {z : ℍ} (hz : z ∈ horodisc D A) :
    (cuspChart D hA).symm (coordinate D z) = ofQuotient (Quotient.mk _ z) := by
  rw [← cuspChart_ofQuotient_mk D hA hz]
  exact (cuspChart D hA).left_inv ((ofQuotient_mem_cuspNhd_iff D A).mpr ⟨z, hz, rfl⟩)

/-- The inverse of the cusp chart sends a nonzero point `q` of its target to the orbit of the
logarithmic lift `σ⁻¹ • invQParam w q`. -/
theorem cuspChart_symm_of_ne_zero {q : ℂ} (hq : q ∈ (cuspChart D hA).target) (hq0 : q ≠ 0) :
    (cuspChart D hA).symm q =
      ofQuotient (Quotient.mk _ (D.scaling⁻¹ • ofComplex (Periodic.invQParam D.width q))) := by
  rw [cuspChart_target, mem_ball_zero_iff] at hq
  obtain ⟨q', rfl⟩ := TauCeti.Complex.UnitDisc.exists_coe_punctured_eq hq0
    (hq.trans (cuspRadius_lt_one D (D.width_pos.trans_le hA)))
  have hz : D.scaling⁻¹ • invQParamUpperHalfPlane D.width D.width_pos q' ∈ horodisc D A := by
    rw [← norm_qCoordinate_lt_iff_mem_horodisc, qCoordinate_smul_invQParamUpperHalfPlane]
    exact hq
  rw [← coe_invQParamUpperHalfPlane D.width D.width_pos q', ofComplex_apply,
    ← cuspChart_symm_coordinate D hA hz, ← coe_qCoordinate,
    qCoordinate_smul_invQParamUpperHalfPlane]

end Subgroup.CompactifiedQuotient
