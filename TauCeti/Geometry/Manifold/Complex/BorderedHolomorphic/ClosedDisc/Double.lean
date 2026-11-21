/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.Basic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.Topology.Constructions.DoubleAlong.EulerCharacteristic

/-!
# The Schottky double of the closed disc is the Riemann sphere

The closed unit disc `𝕔𝔻`, with its Cayley charts, is a Riemann surface with boundary, and its
Schottky double `TauCeti.SchottkyDouble 𝕔𝔻` is a Riemann surface without boundary. This file
shows that this double is biholomorphic to the Riemann sphere `OnePoint ℂ`.

Topologically, the boundary of `𝕔𝔻` is the unit circle, so the Schottky double is the double
`TauCeti.DoubleAlong TauCeti.DoubleAlong.discBoundary` of the closed disc along its boundary
circle, which `TauCeti.DoubleAlong.discDoubleHomeomorph` identifies with the sphere: the first
sheet is sent identically to the closed disc and the second to the closed exterior by the
inversion `w ↦ (conj w)⁻¹` in the unit circle.

The homeomorphism is holomorphic with holomorphic inverse because in every doubled chart it is a
single Möbius transformation. The doubled Cayley chart at a point `ζ` of the unit circle has
inverse `w ↦ ζ (I - w) / (w + I)` on the closed upper half-plane, landing in the first sheet, and
`w ↦ ζ (I - conj w) / (conj w + I)` on the open lower half-plane, landing in the second sheet. The
inversion in the unit circle turns the second formula into the first, because `conj ζ = ζ⁻¹`. So
the inverse of the doubled chart, followed by the homeomorphism to the sphere, is the Möbius
transformation
`w ↦ ζ (I - w) / (w + I)` of the matrix `!![-ζ, ζ * I; 1, I]` on the whole plane, with
`-I ↦ ∞`, and Möbius transformations are biholomorphisms of the sphere.

Under the biholomorphism the sheet swap of the double, which is antiholomorphic
(`TauCeti.SchottkyDouble.writtenInExtChartAt_swap_eventuallyEq_conj`), becomes the inversion in
the unit circle, and its fixed set, the boundary, becomes the unit circle. The Euler
characteristic of the double is `2 = 2 · 1`, twice that of the disc.

## Main declarations

* `Complex.UnitClosedDisc.schottkyDoubleHomeomorphDiscDouble`: the Schottky double of `𝕔𝔻` is
  the topological double of the closed disc along its boundary circle.
* `Complex.UnitClosedDisc.schottkyDoubleDiffeomorph`: the Schottky double of `𝕔𝔻` is
  biholomorphic to the Riemann sphere.
* `Complex.UnitClosedDisc.schottkyDoubleDiffeomorph_doubleChart_symm`: in the doubled Cayley
  chart centred at `ζ`, the biholomorphism is the Möbius transformation of
  `Complex.UnitClosedDisc.cayleyMoebius ζ`, that is, `w ↦ ζ (I - w) / (w + I)`.
* `Complex.UnitClosedDisc.schottkyDoubleDiffeomorph_swap`: the sheet swap becomes the inversion
  `OnePoint.unitCircleInversion`.
* `Complex.UnitClosedDisc.schottkyDoubleDiffeomorph_image_fixed`: the fixed set of the sheet swap
  becomes the unit circle.
* `Complex.UnitClosedDisc.eulerChar_schottkyDouble` and
  `Complex.UnitClosedDisc.eulerChar_schottkyDouble_eq_two_mul`: `χ = 2 = 2 · χ(𝕔𝔻)`, where
  `χ(𝕔𝔻) = 1` (`Complex.UnitClosedDisc.eulerChar_eq_one`) since the disc is contractible.

## References

* L. V. Ahlfors and L. Sario, *Riemann Surfaces*, Princeton University Press, 1960, Ch. II, for
  the double of a bordered Riemann surface.
-/

public section

noncomputable section

open Set Metric Filter Function TauCeti OnePoint Matrix
open scoped Manifold ContDiff Topology Complex.UnitDisc ComplexConjugate

namespace Complex.UnitClosedDisc

/-! ### The topological double -/

/-- The Schottky double of the closed unit disc is the topological double of the closed disc
along its boundary circle `TauCeti.DoubleAlong.discBoundary`: the boundary of `𝕔𝔻` as a Riemann
surface with boundary is the unit circle. -/
def schottkyDoubleHomeomorphDiscDouble :
    SchottkyDouble 𝕔𝔻 ≃ₜ DoubleAlong DoubleAlong.discBoundary :=
  DoubleAlong.congr homeomorphClosedBall image_homeomorphClosedBall_compl_borderedInterior

@[simp]
theorem schottkyDoubleHomeomorphDiscDouble_inl (z : 𝕔𝔻) :
    schottkyDoubleHomeomorphDiscDouble (DoubleAlong.inl _ z) =
      DoubleAlong.inl _ (homeomorphClosedBall z) :=
  DoubleAlong.congr_inl _ _ z

@[simp]
theorem schottkyDoubleHomeomorphDiscDouble_inr (z : 𝕔𝔻) :
    schottkyDoubleHomeomorphDiscDouble (DoubleAlong.inr _ z) =
      DoubleAlong.inr _ (homeomorphClosedBall z) :=
  DoubleAlong.congr_inr _ _ z

@[simp]
theorem schottkyDoubleHomeomorphDiscDouble_symm_inl (z : closedBall (0 : ℂ) 1) :
    schottkyDoubleHomeomorphDiscDouble.symm (DoubleAlong.inl _ z) =
      DoubleAlong.inl _ (homeomorphClosedBall.symm z) := by
  rw [Homeomorph.symm_apply_eq, schottkyDoubleHomeomorphDiscDouble_inl,
    Homeomorph.apply_symm_apply]

@[simp]
theorem schottkyDoubleHomeomorphDiscDouble_symm_inr (z : closedBall (0 : ℂ) 1) :
    schottkyDoubleHomeomorphDiscDouble.symm (DoubleAlong.inr _ z) =
      DoubleAlong.inr _ (homeomorphClosedBall.symm z) := by
  rw [Homeomorph.symm_apply_eq, schottkyDoubleHomeomorphDiscDouble_inr,
    Homeomorph.apply_symm_apply]

/-- The homeomorphism of doubles intertwines the two sheet swaps. -/
@[simp]
theorem schottkyDoubleHomeomorphDiscDouble_swap (p : SchottkyDouble 𝕔𝔻) :
    schottkyDoubleHomeomorphDiscDouble (DoubleAlong.swap _ p) =
      DoubleAlong.swap _ (schottkyDoubleHomeomorphDiscDouble p) :=
  DoubleAlong.congr_swap _ _ p

/-- The homeomorphism of doubles carries the fixed set of the sheet swap of the Schottky double
onto that of the disc double. -/
theorem schottkyDoubleHomeomorphDiscDouble_image_fixed :
    schottkyDoubleHomeomorphDiscDouble ''
        {p | DoubleAlong.swap (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ p = p} =
      {p | DoubleAlong.swap DoubleAlong.discBoundary p = p} :=
  DoubleAlong.image_congr_fixed _ _

@[simp]
theorem schottkyDoubleHomeomorphDiscDouble_symm_swap (p : DoubleAlong DoubleAlong.discBoundary) :
    schottkyDoubleHomeomorphDiscDouble.symm (DoubleAlong.swap _ p) =
      DoubleAlong.swap _ (schottkyDoubleHomeomorphDiscDouble.symm p) := by
  rw [Homeomorph.symm_apply_eq, schottkyDoubleHomeomorphDiscDouble_swap,
    Homeomorph.apply_symm_apply]

/-! ### The Möbius transformation of a doubled Cayley chart -/

/-- The matrix `!![-ζ, ζ * I; 1, I]` of the Möbius transformation `w ↦ ζ (I - w) / (w + I)`, the
inverse of the Cayley chart centred at `ζ` extended to the whole sphere. Its determinant is
`-2 ζ I`, nonzero for `ζ ≠ 0`. -/
def cayleyMoebius (ζ : ℂ) (hζ : ζ ≠ 0) : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![-ζ, ζ * I; 1, I] (by
    rw [det_fin_two_of]
    have : -ζ * I - ζ * I * 1 = -2 * I * ζ := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hζ)

/-- The matrix of `cayleyMoebius ζ`. -/
@[simp]
theorem coe_cayleyMoebius (ζ : ℂ) (hζ : ζ ≠ 0) :
    (cayleyMoebius ζ hζ : Matrix (Fin 2) (Fin 2) ℂ) = !![-ζ, ζ * I; 1, I] :=
  (rfl)

/-- The Möbius transformation of `cayleyMoebius ζ` sends `-I` to `∞`. -/
@[simp]
theorem cayleyMoebius_smul_neg_I (ζ : ℂ) (hζ : ζ ≠ 0) :
    cayleyMoebius ζ hζ • ((-I : ℂ) : OnePoint ℂ) = (∞ : OnePoint ℂ) := by
  simp [smul_some_eq_ite, coe_cayleyMoebius]

/-- The Möbius transformation of `cayleyMoebius ζ` sends `∞` to `-ζ`. -/
@[simp]
theorem cayleyMoebius_smul_infty (ζ : ℂ) (hζ : ζ ≠ 0) :
    cayleyMoebius ζ hζ • (∞ : OnePoint ℂ) = ((-ζ : ℂ) : OnePoint ℂ) := by
  simp [smul_infty_eq_ite, coe_cayleyMoebius]

/-- Away from `-I`, the Möbius transformation of `cayleyMoebius ζ` is `w ↦ ζ (I - w) / (w + I)`. -/
theorem cayleyMoebius_smul_coe (ζ : ℂ) (hζ : ζ ≠ 0) {w : ℂ} (hw : w + I ≠ 0) :
    cayleyMoebius ζ hζ • (w : OnePoint ℂ) = ((ζ * (I - w) / (w + I) : ℂ) : OnePoint ℂ) := by
  simp [smul_some_eq_ite, hw]
  ring

/-- The biholomorphism of the Schottky double of the disc onto the sphere, as a homeomorphism. -/
private def toSphere : SchottkyDouble 𝕔𝔻 ≃ₜ OnePoint ℂ :=
  schottkyDoubleHomeomorphDiscDouble.trans DoubleAlong.discDoubleHomeomorph

private theorem toSphere_inl (z : 𝕔𝔻) :
    toSphere (DoubleAlong.inl _ z) = ((z : ℂ) : OnePoint ℂ) := by
  simp [toSphere]

private theorem toSphere_inr (z : 𝕔𝔻) :
    toSphere (DoubleAlong.inr _ z) = unitCircleInversion ((z : ℂ) : OnePoint ℂ) := by
  simp [toSphere]

/-- The inverse of a doubled Cayley chart followed by the homeomorphism to the sphere is the
Möbius transformation `w ↦ ζ (I - w) / (w + I)` on the whole plane. -/
private theorem toSphere_doubleChart_symm {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (he : cayleyChart ζ hζ ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 𝕔𝔻) (w : ℂ) :
    toSphere ((SchottkyDouble.doubleChart (cayleyChart ζ hζ) he).symm w) =
      cayleyMoebius ζ (ne_zero_of_norm_ne_zero (hζ ▸ one_ne_zero)) • (w : OnePoint ℂ) := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_norm_ne_zero (hζ ▸ one_ne_zero)
  rcases le_or_gt 0 w.im with hnn | hneg
  · have hw : w + I ≠ 0 := add_I_ne_zero_of_im_nonneg hnn
    rw [SchottkyDouble.doubleChart_symm_apply_of_im_nonneg he hnn, toSphere_inl,
      coe_cayleyChart_symm_apply, ClosedUpperHalfPlane.coe_fold_of_im_nonneg hnn,
      cayleyMoebius_smul_coe ζ hζ0 hw]
  · rw [SchottkyDouble.doubleChart_symm_apply_of_im_neg he hneg, toSphere_inr,
      coe_cayleyChart_symm_apply, ClosedUpperHalfPlane.coe_fold_of_im_nonpos hneg.le]
    rcases eq_or_ne w (-I) with rfl | hwI
    · rw [cayleyMoebius_smul_neg_I]
      simp
    · have hw : w + I ≠ 0 := fun h ↦ hwI (eq_neg_of_add_eq_zero_left h)
      have hcw : conj w + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simpa using hneg.le)
      have hcw' : I - conj w ≠ 0 := by
        intro h
        apply hwI
        rw [sub_eq_zero] at h
        rw [← conj_conj w, ← h, conj_I]
      rw [unitCircleInversion_coe (div_ne_zero (mul_ne_zero hζ0 hcw') hcw),
        cayleyMoebius_smul_coe ζ hζ0 hw, coe_eq_coe]
      have hw2 : -I - w ≠ 0 := by
        rw [← neg_add', neg_ne_zero, add_comm]
        exact hw
      simp only [map_div₀, map_mul, map_sub, map_add, conj_conj, conj_I, ← inv_eq_conj hζ]
      field_simp
      ring

/-- The Möbius transformation attached to the chart of the double at `p`. -/
private def chartMoebius (p : SchottkyDouble 𝕔𝔻) : GL (Fin 2) ℂ :=
  cayleyMoebius (chartCenter (DoubleAlong.fold _ p))
    (ne_zero_of_norm_ne_zero ((norm_chartCenter _).symm ▸ one_ne_zero))

/-- On the source of the chart of the double at `p`, the homeomorphism to the sphere is the chart
followed by a Möbius transformation. -/
private theorem toSphere_eq_smul_chartAt {p q : SchottkyDouble 𝕔𝔻}
    (hq : q ∈ (chartAt ℂ p).source) :
    toSphere q = chartMoebius p • ((chartAt ℂ p q : ℂ) : OnePoint ℂ) := by
  have he : cayleyChart (chartCenter (DoubleAlong.fold _ p)) (norm_chartCenter _) ∈
      IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 𝕔𝔻 := by
    rw [← chartAt_eq]
    exact IsManifold.chart_mem_maximalAtlas _
  have hc : chartAt ℂ p = SchottkyDouble.doubleChart _ he := by
    simp only [SchottkyDouble.chartAt_eq, chartAt_eq]
  rw [hc] at hq ⊢
  rw [chartMoebius, ← toSphere_doubleChart_symm (norm_chartCenter _) he,
    (SchottkyDouble.doubleChart _ he).left_inv hq]

private theorem contMDiff_toSphere : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω toSphere := by
  intro p
  have hev : toSphere =ᶠ[𝓝 p] (fun w : ℂ ↦ chartMoebius p • (w : OnePoint ℂ)) ∘ chartAt ℂ p := by
    filter_upwards [(chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)] with q hq
    exact toSphere_eq_smul_chartAt hq
  exact (((chartMoebius p).contMDiff_smul_coe _).comp p
    (contMDiffOn_chart.contMDiffAt
      ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)))).congr_of_eventuallyEq hev

private theorem contMDiff_toSphere_symm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω toSphere.symm := by
  intro x
  set p := toSphere.symm x
  set c := chartAt ℂ p
  set g := chartMoebius p
  have hinv {q : SchottkyDouble 𝕔𝔻} (hq : q ∈ c.source) :
      g⁻¹ • toSphere q = ((c q : ℂ) : OnePoint ℂ) := by
    rw [toSphere_eq_smul_chartAt hq, inv_smul_smul]
  have hx : g⁻¹ • x = ((c p : ℂ) : OnePoint ℂ) := by
    rw [← hinv (mem_chart_source ℂ p), Homeomorph.apply_symm_apply]
  have hev : toSphere.symm =ᶠ[𝓝 x] c.symm ∘ affineChart ∘ fun y ↦ g⁻¹ • y := by
    filter_upwards [toSphere.continuous_symm.continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds (mem_chart_source ℂ p))] with y hy
    have h := hinv hy
    rw [Homeomorph.apply_symm_apply] at h
    rw [Function.comp_apply, Function.comp_apply, h, affineChart_coe, c.left_inv hy]
  have hsmul : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun y : OnePoint ℂ ↦ g⁻¹ • y) x :=
    contMDiff_const_smul g⁻¹ x
  have haff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω affineChart (g⁻¹ • x) := by
    rw [hx]
    exact contMDiffAt_of_mem_maximalAtlas affineChart_mem_maximalAtlas (by simp)
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω c.symm (affineChart (g⁻¹ • x)) := by
    rw [hx, affineChart_coe]
    exact contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds (mem_chart_target ℂ p))
  exact (hc.comp x (haff.comp x hsmul)).congr_of_eventuallyEq hev

/-- **The Schottky double of the closed disc is the Riemann sphere.** The Schottky double of the
closed unit disc, with its Cayley charts, is biholomorphic to `OnePoint ℂ`: the first sheet goes
identically to the closed disc and the second to the closed exterior by `w ↦ (conj w)⁻¹`. -/
def schottkyDoubleDiffeomorph : SchottkyDouble 𝕔𝔻 ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ where
  toEquiv := toSphere.toEquiv
  contMDiff_toFun := contMDiff_toSphere
  contMDiff_invFun := contMDiff_toSphere_symm

@[simp]
theorem schottkyDoubleDiffeomorph_inl (z : 𝕔𝔻) :
    schottkyDoubleDiffeomorph (DoubleAlong.inl _ z) = ((z : ℂ) : OnePoint ℂ) :=
  toSphere_inl z

@[simp]
theorem schottkyDoubleDiffeomorph_inr (z : 𝕔𝔻) :
    schottkyDoubleDiffeomorph (DoubleAlong.inr _ z) =
      unitCircleInversion ((z : ℂ) : OnePoint ℂ) :=
  toSphere_inr z

/-- The underlying homeomorphism of the biholomorphism is
`Complex.UnitClosedDisc.schottkyDoubleHomeomorphDiscDouble` followed by
`TauCeti.DoubleAlong.discDoubleHomeomorph`. -/
theorem schottkyDoubleDiffeomorph_toHomeomorph :
    schottkyDoubleDiffeomorph.toHomeomorph =
      schottkyDoubleHomeomorphDiscDouble.trans DoubleAlong.discDoubleHomeomorph :=
  (rfl)

/-- **The biholomorphism in a doubled Cayley chart.** In the doubled Cayley chart centred at a
point `ζ` of the unit circle, the biholomorphism onto the sphere is the single Möbius
transformation `w ↦ ζ (I - w) / (w + I)` of the whole plane, with `-I ↦ ∞`. -/
@[simp]
theorem schottkyDoubleDiffeomorph_doubleChart_symm {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (he : cayleyChart ζ hζ ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 𝕔𝔻) (w : ℂ) :
    schottkyDoubleDiffeomorph ((SchottkyDouble.doubleChart (cayleyChart ζ hζ) he).symm w) =
      cayleyMoebius ζ (ne_zero_of_norm_ne_zero (hζ ▸ one_ne_zero)) • (w : OnePoint ℂ) :=
  toSphere_doubleChart_symm hζ he w

/-! ### The sheet swap and the Euler characteristic -/

/-- The biholomorphism carries the sheet swap of the Schottky double, an antiholomorphic
involution, to the inversion `w ↦ (conj w)⁻¹` of the sphere in the unit circle. -/
@[simp]
theorem schottkyDoubleDiffeomorph_swap (p : SchottkyDouble 𝕔𝔻) :
    schottkyDoubleDiffeomorph (DoubleAlong.swap _ p) =
      unitCircleInversion (schottkyDoubleDiffeomorph p) := by
  induction p using DoubleAlong.induction_on <;> simp

/-- The inverse of the biholomorphism carries the inversion in the unit circle to the sheet
swap. -/
@[simp]
theorem schottkyDoubleDiffeomorph_symm_unitCircleInversion (x : OnePoint ℂ) :
    schottkyDoubleDiffeomorph.symm (unitCircleInversion x) =
      DoubleAlong.swap _ (schottkyDoubleDiffeomorph.symm x) :=
  EquivLike.injective schottkyDoubleDiffeomorph <| by
    rw [Diffeomorph.apply_symm_apply, schottkyDoubleDiffeomorph_swap, Diffeomorph.apply_symm_apply]

/-- A point of the closed unit disc comes from the first sheet. -/
theorem schottkyDoubleDiffeomorph_symm_coe_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    schottkyDoubleDiffeomorph.symm (z : OnePoint ℂ) = DoubleAlong.inl _ (mk z hz) :=
  EquivLike.injective schottkyDoubleDiffeomorph <| by
    rw [Diffeomorph.apply_symm_apply, schottkyDoubleDiffeomorph_inl, coe_mk]

/-- A point of the closed exterior of the unit disc comes from the second sheet, at the inverse
of its conjugate. -/
theorem schottkyDoubleDiffeomorph_symm_coe_of_one_le_norm {z : ℂ} (hz : 1 ≤ ‖z‖) :
    schottkyDoubleDiffeomorph.symm (z : OnePoint ℂ) =
      DoubleAlong.inr _ (mk (conj z)⁻¹ (by simpa using inv_le_one_of_one_le₀ hz)) := by
  have hz0 : z ≠ 0 := norm_pos_iff.1 (one_pos.trans_le hz)
  refine EquivLike.injective schottkyDoubleDiffeomorph ?_
  rw [Diffeomorph.apply_symm_apply, schottkyDoubleDiffeomorph_inr, coe_mk,
    unitCircleInversion_coe (by simpa using hz0), map_inv₀, conj_conj, inv_inv]

/-- The point at infinity comes from the centre of the second sheet. -/
@[simp]
theorem schottkyDoubleDiffeomorph_symm_infty :
    schottkyDoubleDiffeomorph.symm ∞ = DoubleAlong.inr _ 0 :=
  EquivLike.injective schottkyDoubleDiffeomorph <| by
    rw [Diffeomorph.apply_symm_apply, schottkyDoubleDiffeomorph_inr, coe_zero,
      unitCircleInversion_zero]

/-- The biholomorphism carries the fixed set of the sheet swap, the boundary circle of the disc on
the first sheet, onto the unit circle of the sphere. -/
theorem schottkyDoubleDiffeomorph_image_fixed :
    schottkyDoubleDiffeomorph '' {p | DoubleAlong.swap (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ p = p} =
      (↑) '' sphere (0 : ℂ) 1 := by
  rw [← DoubleAlong.discDoubleHomeomorph_image_fixed_eq_sphere,
    ← schottkyDoubleHomeomorphDiscDouble_image_fixed, image_image,
    ← schottkyDoubleDiffeomorph.coe_toHomeomorph, schottkyDoubleDiffeomorph_toHomeomorph]
  exact congrArg (· '' _) (funext fun x ↦ Homeomorph.trans_apply _ _ x)

/-- The Schottky double of the closed unit disc has finite CW type, being the Riemann sphere. -/
instance finiteCWType_schottkyDouble : FiniteCWType (SchottkyDouble 𝕔𝔻) :=
  schottkyDoubleDiffeomorph.toHomeomorph.finiteCWType

/-- **Euler characteristic of the Schottky double of the disc.** It is the Riemann sphere, with
Euler characteristic `2`. -/
@[simp]
theorem eulerChar_schottkyDouble : eulerChar (SchottkyDouble 𝕔𝔻) = 2 := by
  rw [schottkyDoubleHomeomorphDiscDouble.eulerChar_eq, DoubleAlong.eulerChar_discDouble]

/-- The Euler characteristic of the Schottky double of the disc is twice that of the disc:
`2 = 2 · 1`. -/
theorem eulerChar_schottkyDouble_eq_two_mul :
    eulerChar (SchottkyDouble 𝕔𝔻) = 2 * eulerChar 𝕔𝔻 := by
  rw [eulerChar_schottkyDouble, eulerChar_eq_one, mul_one]

end Complex.UnitClosedDisc
