/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble
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
the doubled chart, followed by the homeomorphism to the sphere, is the Möbius transformation
`w ↦ ζ (I - w) / (w + I)` of the matrix `!![-ζ, ζ * I; 1, I]` on the whole plane, with
`-I ↦ ∞`, and Möbius transformations are biholomorphisms of the sphere.

Under the biholomorphism the sheet swap of the double, which is antiholomorphic
(`TauCeti.SchottkyDouble.writtenInExtChartAt_swap_eventuallyEq_conj`), becomes the inversion in
the unit circle, and its fixed set, the boundary, becomes the unit circle. The Euler
characteristic of the double is `2 = 2 · 1`, twice that of the disc.

## Main declarations

* `Complex.UnitClosedDisc.schottkyDoubleHomeomorph`: the Schottky double of `𝕔𝔻` is the
  topological double of the closed disc along its boundary circle.
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
  `Complex.UnitClosedDisc.eulerChar_schottkyDouble_eq_two_mul`: `χ = 2 = 2 · χ(𝕔𝔻)`.

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

/-- Two copies of a homeomorphism that carries `A` onto `B` glue to a homeomorphism of the
doubles. -/
private def doubleAlongCongr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (h : e '' A = B) : DoubleAlong A ≃ₜ DoubleAlong B where
  toFun := DoubleAlong.desc A ((DoubleAlong.inl B).comp e) ((DoubleAlong.inr B).comp e)
    fun x ↦ DoubleAlong.inl_coe_eq_inr B ⟨e x, h ▸ mem_image_of_mem e x.2⟩
  invFun := DoubleAlong.desc B ((DoubleAlong.inl A).comp e.symm)
    ((DoubleAlong.inr A).comp e.symm)
    fun y ↦ DoubleAlong.inl_coe_eq_inr A ⟨e.symm y, by
      have hy : (y : Y) ∈ e '' A := by rw [h]; exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      rwa [← hxy, e.symm_apply_apply]⟩
  left_inv p := by
    induction p using DoubleAlong.induction_on <;> simp
  right_inv p := by
    induction p using DoubleAlong.induction_on <;> simp
  continuous_toFun := ContinuousMap.continuous _
  continuous_invFun := ContinuousMap.continuous _

private theorem doubleAlongCongr_inl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {A : Set X} {B : Set Y} (h : e '' A = B) (x : X) :
    doubleAlongCongr e h (DoubleAlong.inl A x) = DoubleAlong.inl B (e x) :=
  DoubleAlong.desc_inl _ _ _ _ x

private theorem doubleAlongCongr_inr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {A : Set X} {B : Set Y} (h : e '' A = B) (x : X) :
    doubleAlongCongr e h (DoubleAlong.inr A x) = DoubleAlong.inr B (e x) :=
  DoubleAlong.desc_inr _ _ _ _ x

/-- The Schottky double of the closed unit disc is the topological double of the closed disc
along its boundary circle `TauCeti.DoubleAlong.discBoundary`: the boundary of `𝕔𝔻` as a Riemann
surface with boundary is the unit circle. -/
def schottkyDoubleHomeomorph : SchottkyDouble 𝕔𝔻 ≃ₜ DoubleAlong DoubleAlong.discBoundary :=
  doubleAlongCongr homeomorphClosedBall image_homeomorphClosedBall_compl_borderedInterior

@[simp]
theorem schottkyDoubleHomeomorph_inl (z : 𝕔𝔻) :
    schottkyDoubleHomeomorph (DoubleAlong.inl _ z) =
      DoubleAlong.inl _ (homeomorphClosedBall z) :=
  doubleAlongCongr_inl _ _ z

@[simp]
theorem schottkyDoubleHomeomorph_inr (z : 𝕔𝔻) :
    schottkyDoubleHomeomorph (DoubleAlong.inr _ z) =
      DoubleAlong.inr _ (homeomorphClosedBall z) :=
  doubleAlongCongr_inr _ _ z

/-- The homeomorphism of doubles intertwines the two sheet swaps. -/
@[simp]
theorem schottkyDoubleHomeomorph_swap (p : SchottkyDouble 𝕔𝔻) :
    schottkyDoubleHomeomorph (DoubleAlong.swap _ p) =
      DoubleAlong.swap _ (schottkyDoubleHomeomorph p) := by
  induction p using DoubleAlong.induction_on <;> simp

@[simp]
theorem schottkyDoubleHomeomorph_symm_swap (p : DoubleAlong DoubleAlong.discBoundary) :
    schottkyDoubleHomeomorph.symm (DoubleAlong.swap _ p) =
      DoubleAlong.swap _ (schottkyDoubleHomeomorph.symm p) := by
  rw [Homeomorph.symm_apply_eq, schottkyDoubleHomeomorph_swap, Homeomorph.apply_symm_apply]

/-! ### The Möbius transformation of a doubled Cayley chart -/

private theorem ne_zero_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) : ζ ≠ 0 :=
  ne_zero_of_norm_ne_zero (hζ ▸ one_ne_zero)

/-- The matrix `!![-ζ, ζ * I; 1, I]` of the Möbius transformation `w ↦ ζ (I - w) / (w + I)`, the
inverse of the Cayley chart centred at `ζ` extended to the whole sphere. Its determinant is
`-2 ζ I`, nonzero for `ζ` on the unit circle. -/
def cayleyMoebius (ζ : ℂ) (hζ : ‖ζ‖ = 1) : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![-ζ, ζ * I; 1, I] (by
    rw [det_fin_two_of]
    have : -ζ * I - ζ * I * 1 = -2 * I * ζ := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (ne_zero_of_norm_eq_one hζ))

/-- The matrix of `cayleyMoebius ζ`. -/
theorem coe_cayleyMoebius (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (cayleyMoebius ζ hζ : Matrix (Fin 2) (Fin 2) ℂ) = !![-ζ, ζ * I; 1, I] :=
  (rfl)

/-- The Möbius transformation of `cayleyMoebius ζ` sends `-I` to `∞`. -/
theorem cayleyMoebius_smul_neg_I (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    cayleyMoebius ζ hζ • ((-I : ℂ) : OnePoint ℂ) = (∞ : OnePoint ℂ) := by
  simp [smul_some_eq_ite, coe_cayleyMoebius]

/-- Away from `-I`, the Möbius transformation of `cayleyMoebius ζ` is `w ↦ ζ (I - w) / (w + I)`. -/
theorem cayleyMoebius_smul_coe (ζ : ℂ) (hζ : ‖ζ‖ = 1) {w : ℂ} (hw : w + I ≠ 0) :
    cayleyMoebius ζ hζ • (w : OnePoint ℂ) = ((ζ * (I - w) / (w + I) : ℂ) : OnePoint ℂ) := by
  simp only [smul_some_eq_ite, coe_cayleyMoebius, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, one_mul, hw, ↓reduceIte, coe_eq_coe]
  ring

/-- The biholomorphism of the Schottky double of the disc onto the sphere, as a homeomorphism. -/
private def toSphere : SchottkyDouble 𝕔𝔻 ≃ₜ OnePoint ℂ :=
  schottkyDoubleHomeomorph.trans DoubleAlong.discDoubleHomeomorph

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
      cayleyMoebius ζ hζ • (w : OnePoint ℂ) := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  rcases le_or_gt 0 w.im with hnn | hneg
  · have hw : w + I ≠ 0 := add_I_ne_zero_of_im_nonneg hnn
    rw [SchottkyDouble.doubleChart_symm_apply_of_im_nonneg he hnn, toSphere_inl,
      coe_cayleyChart_symm_apply, ClosedUpperHalfPlane.coe_fold_of_im_nonneg hnn,
      cayleyMoebius_smul_coe ζ hζ hw]
  · rw [SchottkyDouble.doubleChart_symm_apply_of_im_neg he hneg, toSphere_inr,
      coe_cayleyChart_symm_apply, ClosedUpperHalfPlane.coe_fold_of_im_nonpos hneg.le]
    have hconj : conj ζ * ζ = 1 := by
      rw [mul_comm, mul_conj', hζ]
      norm_num
    rcases eq_or_ne w (-I) with rfl | hwI
    · rw [cayleyMoebius_smul_neg_I]
      simp
    · have hw : w + I ≠ 0 := fun h ↦ hwI (eq_neg_of_add_eq_zero_left h)
      have hcw : conj w + I ≠ 0 := fun h ↦ by
        have := congrArg Complex.im h
        simp only [add_im, conj_im, I_im, zero_im] at this
        linarith
      have hcw' : I - conj w ≠ 0 := by
        intro h
        apply hwI
        rw [sub_eq_zero] at h
        rw [← conj_conj w, ← h, conj_I]
      rw [unitCircleInversion_coe (div_ne_zero (mul_ne_zero hζ0 hcw') hcw),
        cayleyMoebius_smul_coe ζ hζ hw, coe_eq_coe]
      have hw2 : -I - w ≠ 0 := by
        rw [← neg_add', neg_ne_zero, add_comm]
        exact hw
      have hζ' : conj ζ = ζ⁻¹ := eq_inv_of_mul_eq_one_left hconj
      simp only [map_div₀, map_mul, map_sub, map_add, conj_conj, conj_I, hζ']
      field_simp
      ring

/-- The Möbius transformation attached to the chart of the double at `p`. -/
private def chartMoebius (p : SchottkyDouble 𝕔𝔻) : GL (Fin 2) ℂ :=
  cayleyMoebius (chartCenter (DoubleAlong.fold _ p)) (norm_chartCenter _)

/-- On the source of the chart of the double at `p`, the homeomorphism to the sphere is the chart
followed by a Möbius transformation. -/
private theorem toSphere_eq_smul_chartAt {p q : SchottkyDouble 𝕔𝔻}
    (hq : q ∈ (chartAt ℂ p).source) :
    toSphere q = chartMoebius p • ((chartAt ℂ p q : ℂ) : OnePoint ℂ) := by
  rw [chartMoebius, ← toSphere_doubleChart_symm (norm_chartCenter _)
    (IsManifold.chart_mem_maximalAtlas _)]
  exact congrArg toSphere ((chartAt ℂ p).left_inv hq).symm

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

/-- The biholomorphism is the topological double of the disc, followed by
`TauCeti.DoubleAlong.discDoubleHomeomorph`. -/
theorem schottkyDoubleDiffeomorph_toHomeomorph :
    schottkyDoubleDiffeomorph.toHomeomorph =
      schottkyDoubleHomeomorph.trans DoubleAlong.discDoubleHomeomorph :=
  (rfl)

/-- **The biholomorphism in a doubled Cayley chart.** In the doubled Cayley chart centred at a
point `ζ` of the unit circle, the biholomorphism onto the sphere is the single Möbius
transformation `w ↦ ζ (I - w) / (w + I)` of the whole plane, with `-I ↦ ∞`. -/
theorem schottkyDoubleDiffeomorph_doubleChart_symm {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (he : cayleyChart ζ hζ ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 𝕔𝔻) (w : ℂ) :
    schottkyDoubleDiffeomorph ((SchottkyDouble.doubleChart (cayleyChart ζ hζ) he).symm w) =
      cayleyMoebius ζ hζ • (w : OnePoint ℂ) :=
  toSphere_doubleChart_symm hζ he w

/-! ### The sheet swap and the Euler characteristic -/

/-- The biholomorphism carries the sheet swap of the Schottky double, an antiholomorphic
involution, to the inversion `w ↦ (conj w)⁻¹` of the sphere in the unit circle. -/
@[simp]
theorem schottkyDoubleDiffeomorph_swap (p : SchottkyDouble 𝕔𝔻) :
    schottkyDoubleDiffeomorph (DoubleAlong.swap _ p) =
      unitCircleInversion (schottkyDoubleDiffeomorph p) := by
  change toSphere _ = unitCircleInversion (toSphere p)
  simp [toSphere]

/-- The biholomorphism carries the fixed set of the sheet swap, the boundary circle of the disc on
the first sheet, onto the unit circle of the sphere. -/
theorem schottkyDoubleDiffeomorph_image_fixed :
    schottkyDoubleDiffeomorph '' {p | DoubleAlong.swap (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ p = p} =
      (↑) '' sphere (0 : ℂ) 1 := by
  have h : schottkyDoubleHomeomorph '' {p | DoubleAlong.swap
      (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ p = p} =
      {p | DoubleAlong.swap DoubleAlong.discBoundary p = p} := by
    rw [schottkyDoubleHomeomorph.image_eq_preimage_symm]
    ext p
    change DoubleAlong.swap _ (schottkyDoubleHomeomorph.symm p) = schottkyDoubleHomeomorph.symm p ↔
      DoubleAlong.swap _ p = p
    rw [← schottkyDoubleHomeomorph_symm_swap, schottkyDoubleHomeomorph.symm.injective.eq_iff]
  rw [← DoubleAlong.discDoubleHomeomorph_image_fixed_eq_sphere, ← h, image_image]
  rfl

/-- The closed unit disc has finite CW type, being a closed ball. -/
instance instFiniteCWType : FiniteCWType 𝕔𝔻 :=
  homeomorphClosedBall.finiteCWType

/-- The Schottky double of the closed unit disc has finite CW type, being the Riemann sphere. -/
instance finiteCWType_schottkyDouble : FiniteCWType (SchottkyDouble 𝕔𝔻) :=
  schottkyDoubleDiffeomorph.toHomeomorph.finiteCWType

/-- **Euler characteristic of the Schottky double of the disc.** It is the Riemann sphere, with
Euler characteristic `2`. -/
theorem eulerChar_schottkyDouble : eulerChar (SchottkyDouble 𝕔𝔻) = 2 := by
  rw [schottkyDoubleHomeomorph.eulerChar_eq, DoubleAlong.eulerChar_discDouble]

/-- The Euler characteristic of the Schottky double of the disc is twice that of the disc:
`2 = 2 · 1`. -/
theorem eulerChar_schottkyDouble_eq_two_mul :
    eulerChar (SchottkyDouble 𝕔𝔻) = 2 * eulerChar 𝕔𝔻 := by
  rw [eulerChar_schottkyDouble, homeomorphClosedBall.eulerChar_eq,
    eulerChar_closedBall _ zero_le_one, mul_one]


end Complex.UnitClosedDisc
