/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.ComplexTorus
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedAnnulus
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Topology.Constructions.DoubleAlong.EulerCharacteristic

/-!
# The analytic double of a round annulus

For every `0 < r₁ < r₂`, the native analytic Schottky double of the closed annulus is
biholomorphic to the native complex quotient by the lattice `2π ℤ + 2i log(r₂/r₁) ℤ`.
The coordinate on the first sheet is `arg z - i log(|z|/r₁)` and on the second sheet its
conjugate. Across the inner seam these coincide; across the outer seam their difference is one
vertical period. Jumps of the principal argument are horizontal periods.

The construction uses the logarithmic charts of `ClosedAnnulus` and the doubled charts of
`SchottkyDouble`. In the inner doubled chart the quotient map has affine lift `arg ζ - w`, and
in the outer one the lift is `arg ζ + w - i log(r₂/r₁)`. These formulas prove analyticity at
both seams. The map is injective by the fundamental vertical strip and surjective because its
range is nonempty, open and compact in a connected quotient torus. No analytic classification or
additional gluing hypothesis is assumed.

## Main declarations

* `TauCeti.ClosedAnnulus.doubleTorusDiffeomorph`: the biholomorphism with explicit polar
  coordinate formulas on both sheets.
* `TauCeti.ClosedAnnulus.doubleTorusDiffeomorph_swap`: sheet exchange is quotient conjugation.
* `TauCeti.ClosedAnnulus.fixed_locus_doubleTorusConjugation`: the fixed locus consists of
  exactly the two disjoint embedded boundary circles.
* `TauCeti.ClosedAnnulus.eulerChar_schottkyDouble`: Euler characteristic zero from the existing
  topological comparison with `Circle × Circle`.
-/

public noncomputable section

namespace TauCeti.ClosedAnnulus

open Complex Filter Set Topology
open scoped ComplexConjugate ContDiff Manifold Real

variable {r₁ r₂ : ℝ}

/-! ### The period lattice of the analytic double -/

section Double

variable [hr₁ : Fact (0 < r₁)] [hr₁₂ : Fact (r₁ < r₂)]

private def doublePeriodBasis (r₁ r₂ : ℝ) [h₁ : Fact (0 < r₁)] [h₁₂ : Fact (r₁ < r₂)] :
    Module.Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.unitsSMul fun i ↦
    if i = 0 then Units.mk0 (2 * π) (by positivity)
    else Units.mk0 (2 * Real.log (r₂ / r₁))
      (mul_ne_zero (by norm_num) (Real.log_pos ((one_lt_div h₁.out).mpr h₁₂.out)).ne')

/-- The rectangular period lattice of the double of the annulus: horizontal period `2π` and
vertical period `2i log(r₂/r₁)`. -/
def doublePeriodLattice (r₁ r₂ : ℝ) [Fact (0 < r₁)] [Fact (r₁ < r₂)] : Submodule ℤ ℂ :=
  Submodule.span ℤ (range (doublePeriodBasis r₁ r₂))

/-- The period lattice of the doubled annulus is discrete. -/
instance instDiscreteTopologyDoublePeriodLattice :
    DiscreteTopology (doublePeriodLattice r₁ r₂) := by
  unfold doublePeriodLattice
  infer_instance

/-- The period lattice spans the real model plane. -/
instance instIsZLatticeDoublePeriodLattice : IsZLattice ℝ (doublePeriodLattice r₁ r₂) := by
  unfold doublePeriodLattice
  infer_instance

/-- Membership in the doubled annulus's period lattice is an integer linear combination of its
two explicit periods. -/
theorem mem_doublePeriodLattice_iff {w : ℂ} :
    w ∈ doublePeriodLattice r₁ r₂ ↔
      ∃ m n : ℤ, (m : ℂ) * (2 * π) + (n : ℂ) * (2 * Real.log (r₂ / r₁) * I) = w := by
  have hb : range (doublePeriodBasis r₁ r₂) =
      ({(2 * π : ℂ), (2 * Real.log (r₂ / r₁) : ℂ) * I} : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;>
        simp [doublePeriodBasis, Module.Basis.unitsSMul_apply, Complex.coe_basisOneI,
          Units.smul_def, Complex.real_smul]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [doublePeriodBasis, Module.Basis.unitsSMul_apply,
          Complex.coe_basisOneI, Units.smul_def, Complex.real_smul]⟩
      · exact ⟨1, by simp [doublePeriodBasis, Module.Basis.unitsSMul_apply,
          Complex.coe_basisOneI, Units.smul_def, Complex.real_smul]⟩
  rw [doublePeriodLattice, hb, Submodule.mem_span_pair]
  simp only [zsmul_eq_mul]

private theorem conj_mem_doublePeriodLattice {z : ℂ} (hz : z ∈ doublePeriodLattice r₁ r₂) :
    conj z ∈ doublePeriodLattice r₁ r₂ := by
  rw [mem_doublePeriodLattice_iff] at hz ⊢
  obtain ⟨m, n, rfl⟩ := hz
  refine ⟨m, -n, ?_⟩
  simp [map_add, map_mul, map_ofNat, mul_neg, neg_mul]

/-- Complex conjugation on the native quotient torus of the doubled annulus. -/
def doubleTorusConjugation (r₁ r₂ : ℝ) [Fact (0 < r₁)] [Fact (r₁ < r₂)] :
    C(AddAction.orbitRel.Quotient (doublePeriodLattice r₁ r₂) ℂ,
      AddAction.orbitRel.Quotient (doublePeriodLattice r₁ r₂) ℂ) := by
  let f : ℂ →ₗ[ℤ] ℂ := conjCLE.toLinearMap.restrictScalars ℤ
  have h : doublePeriodLattice r₁ r₂ ≤ (doublePeriodLattice r₁ r₂).comap f :=
    fun z hz ↦ conj_mem_doublePeriodLattice hz
  exact ⟨(doublePeriodLattice r₁ r₂).orbitRelQuotientMap _ f h,
    Submodule.continuous_orbitRelQuotientMap _ _ h continuous_conj⟩

/-- Quotient conjugation sends the class of `z` to the class of its complex conjugate. -/
@[simp]
theorem doubleTorusConjugation_mk (z : ℂ) :
    doubleTorusConjugation r₁ r₂ (Quotient.mk _ z) =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ) (conj z) :=
  (doublePeriodLattice r₁ r₂).orbitRelQuotientMap_mk _ _ _ z

/-- The conjugation of the doubled annulus's torus is an involution. -/
theorem doubleTorusConjugation_involutive : Function.Involutive (doubleTorusConjugation r₁ r₂) := by
  intro x
  refine Quotient.inductionOn x fun z ↦ ?_
  simp

private def doubleLog (z : closedAnnulus r₁ r₂) : ℂ :=
  -I * log ((z : ℂ) / r₁)

omit hr₁₂ in
private theorem exp_I_mul_doubleLog (z : closedAnnulus r₁ r₂) :
    exp (I * doubleLog z) = (z : ℂ) / r₁ := by
  -- Multiplication by `I` cancels the `-I` in the normalized logarithm, putting the argument
  -- into the form required by `exp_log`.
  rw [show I * doubleLog z = log ((z : ℂ) / r₁) by simp [doubleLog, ← mul_assoc]]
  exact exp_log (div_ne_zero
    (norm_pos_iff.mp (hr₁.out.trans_le (closedAnnulus.le_norm_coe z)))
    (ofReal_ne_zero.mpr hr₁.out.ne'))

/-- The first annulus sheet, mapped to the quotient by its logarithmic coordinate. -/
def doubleFirstSheet (r₁ r₂ : ℝ) [Fact (0 < r₁)] [Fact (r₁ < r₂)] :
    C(closedAnnulus r₁ r₂, AddAction.orbitRel.Quotient (doublePeriodLattice r₁ r₂) ℂ) where
  toFun z := Quotient.mk _ (doubleLog z)
  continuous_toFun := by
    have hperiod : (2 * π : ℂ) ∈ doublePeriodLattice r₁ r₂ := by
      rw [mem_doublePeriodLattice_iff]
      exact ⟨1, 0, by simp⟩
    have hc := (doublePeriodLattice r₁ r₂).continuousOn_orbitRelQuotient_mk_neg_I_mul_log hperiod
    have hf : Continuous (fun z : closedAnnulus r₁ r₂ ↦ (z : ℂ) / (r₁ : ℂ)) :=
      continuous_subtypeVal.div_const _
    exact hc.comp_continuous hf fun z ↦ by
      simpa using div_ne_zero
        (norm_pos_iff.mp ((Fact.out : 0 < r₁).trans_le (closedAnnulus.le_norm_coe z)))
        (ofReal_ne_zero.mpr (Fact.out : 0 < r₁).ne')

/-- The first-sheet map is the class of its normalized principal logarithm in the period torus. -/
@[simp]
theorem doubleFirstSheet_apply (z : closedAnnulus r₁ r₂) :
    doubleFirstSheet r₁ r₂ z = Quotient.mk _ (-I * log ((z : ℂ) / r₁)) := (rfl)

omit hr₁₂ in
private theorem doubleLog_im (z : closedAnnulus r₁ r₂) :
    (doubleLog z).im = -Real.log (‖(z : ℂ)‖ / r₁) := by
  simp [doubleLog, mul_im, log_re, Real.norm_eq_abs, abs_of_pos hr₁.out]

omit hr₁₂ in
private theorem doubleLog_im_bounds (z : closedAnnulus r₁ r₂) :
    -Real.log (r₂ / r₁) ≤ (doubleLog z).im ∧ (doubleLog z).im ≤ 0 := by
  rw [doubleLog_im]
  have hpos := div_pos (hr₁.out.trans_le (closedAnnulus.le_norm_coe z)) hr₁.out
  have hlo : 0 ≤ Real.log (‖(z : ℂ)‖ / r₁) :=
    Real.log_nonneg ((le_div_iff₀ hr₁.out).2 (by simpa using closedAnnulus.le_norm_coe z))
  have hhi : Real.log (‖(z : ℂ)‖ / r₁) ≤ Real.log (r₂ / r₁) :=
    Real.log_le_log hpos ((div_le_div_iff_of_pos_right hr₁.out).2 (closedAnnulus.norm_coe_le z))
  exact ⟨neg_le_neg hhi, neg_nonpos.mpr hlo⟩

omit hr₁₂ in
private theorem norm_eq_mul_exp_neg_doubleLog_im (z : closedAnnulus r₁ r₂) :
    ‖(z : ℂ)‖ = r₁ * Real.exp (-(doubleLog z).im) := by
  rw [doubleLog_im, neg_neg, Real.exp_log
    (div_pos (hr₁.out.trans_le (closedAnnulus.le_norm_coe z)) hr₁.out)]
  field_simp [hr₁.out.ne']

private theorem doubleFirstSheet_eq_conjugation_of_boundary (z : closedAnnulus r₁ r₂)
    (hz : z ∈ (borderedInterior (closedAnnulus r₁ r₂) : Set _)ᶜ) :
    doubleFirstSheet r₁ r₂ z = doubleTorusConjugation r₁ r₂ (doubleFirstSheet r₁ r₂ z) := by
  rw [compl_borderedInterior, DoubleAlong.mem_annulusBoundary] at hz
  simp only [doubleFirstSheet_apply, ← doubleLog.eq_1, doubleTorusConjugation_mk]
  apply (doublePeriodLattice r₁ r₂).orbitRelQuotient_mk_eq_mk_iff.mpr
  rw [mem_doublePeriodLattice_iff]
  rcases hz with hz | hz
  · have hi : (doubleLog z).im = 0 := by simp [doubleLog_im, hz, hr₁.out.ne']
    have hc : conj (doubleLog z) = doubleLog z := conj_eq_iff_im.mpr hi
    exact ⟨0, 0, by simp [hc]⟩
  · have hi : (doubleLog z).im = -Real.log (r₂ / r₁) := by rw [doubleLog_im, hz]
    refine ⟨0, -1, ?_⟩
    apply Complex.ext
    · simp
    · simp [hi]
      ring

private theorem doublePeriod_eq_im_cases {u v : ℂ}
    (hu : -Real.log (r₂ / r₁) ≤ u.im ∧ u.im ≤ Real.log (r₂ / r₁))
    (hv : -Real.log (r₂ / r₁) ≤ v.im ∧ v.im ≤ Real.log (r₂ / r₁))
    (h : Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ) u =
      Quotient.mk _ v) :
    ∃ m : ℤ, u.re - v.re = (m : ℝ) * (2 * π) ∧
      (u.im = v.im ∨ (u.im = Real.log (r₂ / r₁) ∧ v.im = -Real.log (r₂ / r₁)) ∨
        (u.im = -Real.log (r₂ / r₁) ∧ v.im = Real.log (r₂ / r₁))) := by
  have hL : 0 < Real.log (r₂ / r₁) := Real.log_pos ((one_lt_div hr₁.out).2 hr₁₂.out)
  obtain ⟨m, n, hn⟩ := mem_doublePeriodLattice_iff.mp
    ((doublePeriodLattice r₁ r₂).orbitRelQuotient_mk_eq_mk_iff.mp h)
  have hre := congrArg Complex.re hn
  have him := congrArg Complex.im hn
  norm_num [mul_re, mul_im] at hre him
  have hnlo : (-1 : ℝ) ≤ n := by nlinarith [hu.1, hv.2]
  have hnhi : (n : ℝ) ≤ 1 := by nlinarith [hu.2, hv.1]
  have hnlo' : -1 ≤ n := by exact_mod_cast hnlo
  have hnhi' : n ≤ 1 := by exact_mod_cast hnhi
  refine ⟨m, by nlinarith [hre], ?_⟩
  have hn' : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl | rfl
  · right; right; norm_num at him; constructor <;> nlinarith [hu.1, hv.2]
  · left; norm_num at him; linarith
  · right; left; norm_num at him; constructor <;> nlinarith [hu.2, hv.1]

omit hr₁₂ in
private theorem doubleLog_eq_of_re_im {x y : closedAnnulus r₁ r₂} {m : ℤ}
    (hre : (doubleLog x).re - (doubleLog y).re = (m : ℝ) * (2 * π))
    (him : (doubleLog x).im = (doubleLog y).im) : x = y := by
  have hd : doubleLog x = doubleLog y + (m : ℂ) * (2 * π) := by
    apply Complex.ext <;> simp <;> linarith
  have he : exp (I * doubleLog x) = exp (I * doubleLog y) := by
    apply exp_eq_exp_iff_exists_int.mpr
    refine ⟨m, ?_⟩
    rw [hd]
    ring
  rw [exp_I_mul_doubleLog, exp_I_mul_doubleLog] at he
  exact Subtype.ext ((div_left_inj₀ (ofReal_ne_zero.mpr hr₁.out.ne')).mp he)

private theorem doubleFirstSheet_injective : Function.Injective (doubleFirstSheet r₁ r₂) := by
  intro x y h
  simp only [doubleFirstSheet_apply, ← doubleLog.eq_1] at h
  have hL : 0 < Real.log (r₂ / r₁) := Real.log_pos ((one_lt_div hr₁.out).2 hr₁₂.out)
  obtain ⟨m, hre, him⟩ := doublePeriod_eq_im_cases
    ⟨(doubleLog_im_bounds x).1, (doubleLog_im_bounds x).2.trans hL.le⟩
    ⟨(doubleLog_im_bounds y).1, (doubleLog_im_bounds y).2.trans hL.le⟩ h
  apply doubleLog_eq_of_re_im hre
  rcases him with h | ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · linarith [(doubleLog_im_bounds x).2]
  · linarith [(doubleLog_im_bounds y).2]

private theorem doubleFirstSheet_eq_conjugation_iff {x y : closedAnnulus r₁ r₂} :
    doubleFirstSheet r₁ r₂ x = doubleTorusConjugation r₁ r₂ (doubleFirstSheet r₁ r₂ y) ↔
      x = y ∧ x ∈ (borderedInterior (closedAnnulus r₁ r₂) : Set _)ᶜ := by
  constructor
  · intro h
    have hL : 0 < Real.log (r₂ / r₁) := Real.log_pos ((one_lt_div hr₁.out).2 hr₁₂.out)
    simp only [doubleFirstSheet_apply, ← doubleLog.eq_1, doubleTorusConjugation_mk] at h
    have hv : -Real.log (r₂ / r₁) ≤ (conj (doubleLog y)).im ∧
        (conj (doubleLog y)).im ≤ Real.log (r₂ / r₁) := by
      simp only [conj_im]
      constructor <;> linarith [(doubleLog_im_bounds y).1, (doubleLog_im_bounds y).2]
    obtain ⟨m, hre, him⟩ := doublePeriod_eq_im_cases
      ⟨(doubleLog_im_bounds x).1, (doubleLog_im_bounds x).2.trans hL.le⟩ hv h
    simp only [conj_re, conj_im] at hre him
    have hi : (doubleLog x).im = (doubleLog y).im := by
      rcases him with h | ⟨h, _⟩ | ⟨h, h'⟩
      · linarith [(doubleLog_im_bounds x).2, (doubleLog_im_bounds y).2]
      · linarith [(doubleLog_im_bounds x).2]
      · linarith
    refine ⟨doubleLog_eq_of_re_im hre hi, ?_⟩
    rw [compl_borderedInterior, DoubleAlong.mem_annulusBoundary]
    rcases him with h | ⟨h, _⟩ | ⟨h, _⟩
    · left
      have hx : (doubleLog x).im = 0 := by linarith [(doubleLog_im_bounds x).2,
        (doubleLog_im_bounds y).2]
      rw [norm_eq_mul_exp_neg_doubleLog_im, hx]; simp
    · linarith [(doubleLog_im_bounds x).2]
    · right
      rw [norm_eq_mul_exp_neg_doubleLog_im, h, neg_neg, Real.exp_log
        (div_pos (hr₁.out.trans hr₁₂.out) hr₁.out)]
      field_simp [hr₁.out.ne']
  · rintro ⟨rfl, hx⟩
    exact doubleFirstSheet_eq_conjugation_of_boundary x hx

/-- The two-sheet logarithmic map from the native analytic Schottky double to its period torus.
It is well-defined on both seams: conjugation changes the outer-seam lift by one vertical period.
-/
def doubleTorusMap (r₁ r₂ : ℝ) [Fact (0 < r₁)] [Fact (r₁ < r₂)] :
    C(SchottkyDouble (closedAnnulus r₁ r₂),
      AddAction.orbitRel.Quotient (doublePeriodLattice r₁ r₂) ℂ) :=
  DoubleAlong.desc _ (doubleFirstSheet r₁ r₂)
    ((doubleTorusConjugation r₁ r₂).comp (doubleFirstSheet r₁ r₂)) fun z ↦ by
      rw [ContinuousMap.comp_apply]
      exact doubleFirstSheet_eq_conjugation_of_boundary (z : closedAnnulus r₁ r₂) z.property

/-- On the first sheet the map is the logarithmic coordinate modulo the period lattice. -/
@[simp]
theorem doubleTorusMap_inl (z : closedAnnulus r₁ r₂) :
    doubleTorusMap r₁ r₂ (DoubleAlong.inl _ z) =
      Quotient.mk _ (-I * log ((z : ℂ) / r₁)) := by
  rw [doubleTorusMap, DoubleAlong.desc_inl, doubleFirstSheet_apply]

/-- On the second sheet the map is the conjugate logarithmic coordinate modulo the lattice. -/
@[simp]
theorem doubleTorusMap_inr (z : closedAnnulus r₁ r₂) :
    doubleTorusMap r₁ r₂ (DoubleAlong.inr _ z) =
      Quotient.mk _ (conj (-I * log ((z : ℂ) / r₁))) := by
  rw [doubleTorusMap, DoubleAlong.desc_inr, ContinuousMap.comp_apply, doubleFirstSheet_apply,
    doubleTorusConjugation_mk]

/-- The sheet exchange is carried to the actual conjugation of the quotient torus. -/
theorem doubleTorusMap_swap (z : SchottkyDouble (closedAnnulus r₁ r₂)) :
    doubleTorusMap r₁ r₂ (DoubleAlong.swap _ z) =
      doubleTorusConjugation r₁ r₂ (doubleTorusMap r₁ r₂ z) := by
  refine DoubleAlong.induction_on _ z (fun x ↦ ?_) (fun x ↦ ?_)
  · simp only [DoubleAlong.swap_inl, doubleTorusMap_inr, doubleTorusMap_inl,
      doubleTorusConjugation_mk]
  · simp only [DoubleAlong.swap_inr, doubleTorusMap_inr, doubleTorusMap_inl,
      doubleTorusConjugation_mk, conj_conj]

/-- The logarithmic map of the double is injective; the only coincidences between the two
sheets are the points already identified at the two boundary circles. -/
theorem doubleTorusMap_injective : Function.Injective (doubleTorusMap r₁ r₂) := by
  intro x y
  refine DoubleAlong.induction_on _ x (fun a ↦ ?_) (fun a ↦ ?_)
  · refine DoubleAlong.induction_on _ y (fun b ↦ ?_) (fun b ↦ ?_)
    · intro h
      apply congrArg (DoubleAlong.inl _)
      exact doubleFirstSheet_injective (by simpa only [doubleTorusMap,
        DoubleAlong.desc_inl] using h)
    · intro h
      apply (DoubleAlong.inl_eq_inr_iff _).2
      exact doubleFirstSheet_eq_conjugation_iff.1 (by simpa only [doubleTorusMap,
        DoubleAlong.desc_inl, DoubleAlong.desc_inr, ContinuousMap.comp_apply] using h)
  · refine DoubleAlong.induction_on _ y (fun b ↦ ?_) (fun b ↦ ?_)
    · intro h
      apply Eq.symm
      apply (DoubleAlong.inl_eq_inr_iff _).2
      exact doubleFirstSheet_eq_conjugation_iff.1 (by simpa only [doubleTorusMap,
        DoubleAlong.desc_inl, DoubleAlong.desc_inr, ContinuousMap.comp_apply] using h.symm)
    · intro h
      apply congrArg (DoubleAlong.inr _)
      apply doubleFirstSheet_injective
      apply doubleTorusConjugation_involutive.injective
      simpa only [doubleTorusMap, DoubleAlong.desc_inr, ContinuousMap.comp_apply] using h

private theorem doubleFirstSheet_innerChart_symm (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    {w : ClosedUpperHalfPlane} (hw : w ∈ chartTarget r₁ r₂) :
    doubleFirstSheet r₁ r₂ ((innerChart ζ hζ).symm w) =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ) ((arg ζ : ℂ) - w) := by
  have hperiod : (2 * π : ℂ) ∈ doublePeriodLattice r₁ r₂ :=
    mem_doublePeriodLattice_iff.mpr ⟨1, 0, by simp⟩
  have heζ : exp (I * (arg ζ : ℂ)) = ζ := by
    simpa [hζ, mul_comm] using norm_mul_exp_arg_mul_I ζ
  rw [doubleFirstSheet_apply, ← doubleLog]
  apply (doublePeriodLattice r₁ r₂).orbitRelQuotient_mk_eq_of_exp_I_mul_eq hperiod
  rw [exp_I_mul_doubleLog, coe_innerChart_symm_apply hw, mul_sub, exp_sub, heζ,
    neg_mul, exp_neg]
  field_simp [hr₁.out.ne']

private theorem doubleFirstSheet_outerChart_symm (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    {w : ClosedUpperHalfPlane} (hw : w ∈ chartTarget r₁ r₂) :
    doubleFirstSheet r₁ r₂ ((outerChart ζ hζ).symm w) =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ)
        ((arg ζ : ℂ) + w - I * Real.log (r₂ / r₁)) := by
  have hperiod : (2 * π : ℂ) ∈ doublePeriodLattice r₁ r₂ :=
    mem_doublePeriodLattice_iff.mpr ⟨1, 0, by simp⟩
  have heζ : exp (I * (arg ζ : ℂ)) = ζ := by
    simpa [hζ, mul_comm] using norm_mul_exp_arg_mul_I ζ
  rw [doubleFirstSheet_apply, ← doubleLog]
  apply (doublePeriodLattice r₁ r₂).orbitRelQuotient_mk_eq_of_exp_I_mul_eq hperiod
  rw [exp_I_mul_doubleLog, coe_outerChart_symm_apply hw]
  -- Distribute `I` over the affine outer lift and use `I² = -1`; the resulting three terms
  -- exponentiate to the angular, chart and radial factors in the inverse-chart formula.
  rw [show I * ((arg ζ : ℂ) + w - I * Real.log (r₂ / r₁)) =
    I * (arg ζ : ℂ) + I * w + (Real.log (r₂ / r₁) : ℂ) by
      linear_combination -I_mul_I * (Real.log (r₂ / r₁) : ℂ)]
  rw [exp_add, exp_add, heζ, ← ofReal_exp, Real.exp_log
    (div_pos (hr₁.out.trans hr₁₂.out) hr₁.out)]
  push_cast
  field_simp [hr₁.out.ne']

/-- The doubled inner logarithmic chart gives the affine holomorphic lift `arg ζ - w` of the
map to the period torus, on both sheets and across the inner boundary. -/
theorem doubleTorusMap_comp_innerChart_symm (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (he : innerChart (r₁ := r₁) (r₂ := r₂) ζ hζ ∈
      IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 (closedAnnulus r₁ r₂))
    {w : ℂ} (hw : w ∈ (SchottkyDouble.doubleChart (innerChart ζ hζ) he).target) :
    doubleTorusMap r₁ r₂ ((SchottkyDouble.doubleChart (innerChart ζ hζ) he).symm w) =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ) ((arg ζ : ℂ) - w) := by
  have ht : ClosedUpperHalfPlane.fold w ∈ chartTarget r₁ r₂ := by
    simpa only [SchottkyDouble.doubleChart_target, innerChart_target, Set.mem_preimage] using hw
  by_cases hi : 0 ≤ w.im
  · rw [SchottkyDouble.doubleChart_symm_apply_of_im_nonneg he hi, doubleTorusMap,
      DoubleAlong.desc_inl, doubleFirstSheet_innerChart_symm ζ hζ ht,
      ClosedUpperHalfPlane.coe_fold_of_im_nonneg hi]
  · rw [SchottkyDouble.doubleChart_symm_apply_of_im_neg he (lt_of_not_ge hi),
      doubleTorusMap, DoubleAlong.desc_inr, ContinuousMap.comp_apply,
      doubleFirstSheet_innerChart_symm ζ hζ ht, doubleTorusConjugation_mk,
      ClosedUpperHalfPlane.coe_fold_of_im_nonpos (le_of_not_ge hi)]
    simp only [map_sub, conj_ofReal, conj_conj]

/-- The doubled outer logarithmic chart gives the affine holomorphic lift
`arg ζ + w - i log(r₂/r₁)`. The lower-sheet formula differs by the vertical lattice period. -/
theorem doubleTorusMap_comp_outerChart_symm (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (he : outerChart (r₁ := r₁) (r₂ := r₂) ζ hζ ∈
      IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 (closedAnnulus r₁ r₂))
    {w : ℂ} (hw : w ∈ (SchottkyDouble.doubleChart (outerChart ζ hζ) he).target) :
    doubleTorusMap r₁ r₂ ((SchottkyDouble.doubleChart (outerChart ζ hζ) he).symm w) =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ)
        ((arg ζ : ℂ) + w - I * Real.log (r₂ / r₁)) := by
  have ht : ClosedUpperHalfPlane.fold w ∈ chartTarget r₁ r₂ := by
    simpa only [SchottkyDouble.doubleChart_target, outerChart_target, Set.mem_preimage] using hw
  by_cases hi : 0 ≤ w.im
  · rw [SchottkyDouble.doubleChart_symm_apply_of_im_nonneg he hi, doubleTorusMap,
      DoubleAlong.desc_inl, doubleFirstSheet_outerChart_symm ζ hζ ht,
      ClosedUpperHalfPlane.coe_fold_of_im_nonneg hi]
  · rw [SchottkyDouble.doubleChart_symm_apply_of_im_neg he (lt_of_not_ge hi),
      doubleTorusMap, DoubleAlong.desc_inr, ContinuousMap.comp_apply,
      doubleFirstSheet_outerChart_symm ζ hζ ht, doubleTorusConjugation_mk,
      ClosedUpperHalfPlane.coe_fold_of_im_nonpos (le_of_not_ge hi)]
    apply (doublePeriodLattice r₁ r₂).orbitRelQuotient_mk_eq_mk_iff.mpr
    apply mem_doublePeriodLattice_iff.mpr
    refine ⟨0, 1, ?_⟩
    simp only [map_sub, map_add, map_mul, conj_ofReal, conj_I, conj_conj]
    ring

private theorem isLocalDiffeomorphAt_doubleTorusMap_of_lift
    (e : OpenPartialHomeomorph (SchottkyDouble (closedAnnulus r₁ r₂)) ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (SchottkyDouble (closedAnnulus r₁ r₂)))
    (a b : ℂ) (ha : a ≠ 0) {x : SchottkyDouble (closedAnnulus r₁ r₂)} (hx : x ∈ e.source)
    (hf : ∀ w ∈ e.target, doubleTorusMap r₁ r₂ (e.symm w) =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ) (a * w + b)) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (doubleTorusMap r₁ r₂) x := by
  have hc := e.isLocalDiffeomorphAt_of_mem_maximalAtlas he hx
  have haff := (Diffeomorph.smulAdd ω a b ha).isLocalDiffeomorph (e x)
  have hq := isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := ω)
    (G := doublePeriodLattice r₁ r₂) (M := ℂ) (Diffeomorph.smulAdd ω a b ha (e x))
  have hcomp := (hc.comp 𝓘(ℂ) ℂ haff).comp 𝓘(ℂ)
    (AddAction.orbitRel.Quotient (doublePeriodLattice r₁ r₂) ℂ) hq
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply]
  rw [Diffeomorph.smulAdd_apply, smul_eq_mul]
  exact (congrArg (doubleTorusMap r₁ r₂) (e.left_inv hy).symm).trans
    (hf (e y) (e.map_source hy))

/-- The logarithmic map to the period torus is an analytic local diffeomorphism, including at
both seams of the native Schottky double. -/
theorem isLocalDiffeomorph_doubleTorusMap :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (doubleTorusMap r₁ r₂) := by
  intro x
  let e := chartAt ClosedUpperHalfPlane (DoubleAlong.fold _ x)
  have he : e ∈ borderedHolomorphicGroupoid.maximalAtlas (closedAnnulus r₁ r₂) :=
    StructureGroupoid.subset_maximalAtlas _ (chart_mem_atlas _ _)
  have hreal : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1
      (closedAnnulus r₁ r₂) := StructureGroupoid.maximalAtlas_mono
    (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
      (contDiffGroupoid_le ENat.LEInfty.out)) he
  have hx : x ∈ (SchottkyDouble.doubleChart e hreal).source := by
    rw [SchottkyDouble.doubleChart_source]
    exact mem_chart_source ClosedUpperHalfPlane (DoubleAlong.fold _ x)
  have hmax := SchottkyDouble.doubleChart_mem_maximalAtlas (n := ω) he
  obtain ⟨ζ, hζ, hin | hout⟩ := mem_atlas_iff.mp (chart_mem_atlas _ (DoubleAlong.fold _ x))
  · have hlift := doubleTorusMap_comp_innerChart_symm (r₁ := r₁) (r₂ := r₂) ζ hζ
    subst e
    simp only [hin] at hreal hx hmax
    apply isLocalDiffeomorphAt_doubleTorusMap_of_lift _ hmax (-1) (arg ζ) (by norm_num) hx
    intro w hw
    -- The affine constructor writes `a * w + b`; the inner chart formula writes `arg ζ - w`.
    rw [show (-1 : ℂ) * w + (arg ζ : ℂ) = (arg ζ : ℂ) - w by ring]
    exact hlift hreal hw
  · have hlift := doubleTorusMap_comp_outerChart_symm (r₁ := r₁) (r₂ := r₂) ζ hζ
    subst e
    simp only [hout] at hreal hx hmax
    apply isLocalDiffeomorphAt_doubleTorusMap_of_lift _ hmax 1
      ((arg ζ : ℂ) - I * Real.log (r₂ / r₁)) one_ne_zero hx
    intro w hw
    -- Reassociate the affine constructor's constant term to match the outer chart formula.
    rw [show (1 : ℂ) * w + ((arg ζ : ℂ) - I * Real.log (r₂ / r₁)) =
      (arg ζ : ℂ) + w - I * Real.log (r₂ / r₁) by ring]
    exact hlift hreal hw

/-- The map covers the quotient torus. Its range is nonempty, open by the local lifts, and
closed by compactness of the native double. -/
theorem doubleTorusMap_surjective : Function.Surjective (doubleTorusMap r₁ r₂) := by
  have hopen := isLocalDiffeomorph_doubleTorusMap (r₁ := r₁) (r₂ := r₂) |>.isOpenMap.isOpen_range
  have hclosed := (isCompact_range (doubleTorusMap r₁ r₂).continuous).isClosed
  let z := (innerChart (r₁ := r₁) (r₂ := r₂) 1 (by norm_num)).symm ⟨0, by simp⟩
  have hn : (range (doubleTorusMap r₁ r₂)).Nonempty :=
    ⟨doubleTorusMap r₁ r₂ (DoubleAlong.inl _ z), mem_range_self _⟩
  exact range_eq_univ.mp (IsClopen.eq_univ ⟨hclosed, hopen⟩ hn)

/-- The analytic Schottky double of `r₁ ≤ |z| ≤ r₂`, for every `0 < r₁ < r₂`, is
biholomorphic to the native quotient by `2π ℤ + 2i log(r₂/r₁) ℤ`. The map on the first sheet is
`arg z - i log(|z|/r₁)` modulo this lattice and on the second sheet its conjugate. -/
def doubleTorusDiffeomorph (r₁ r₂ : ℝ) [Fact (0 < r₁)] [Fact (r₁ < r₂)] :
    SchottkyDouble (closedAnnulus r₁ r₂) ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯
      AddAction.orbitRel.Quotient (doublePeriodLattice r₁ r₂) ℂ :=
  isLocalDiffeomorph_doubleTorusMap.diffeomorphOfBijective
    ⟨doubleTorusMap_injective, doubleTorusMap_surjective⟩

/-- The biholomorphism evaluates as the seam-glued logarithmic map. -/
theorem doubleTorusDiffeomorph_apply (z : SchottkyDouble (closedAnnulus r₁ r₂)) :
    doubleTorusDiffeomorph r₁ r₂ z = doubleTorusMap r₁ r₂ z :=
  congrFun (IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _) z

omit hr₁₂ in
private theorem doubleLog_eq_arg_sub_log_norm (z : closedAnnulus r₁ r₂) :
    doubleLog z = (arg (z : ℂ) : ℂ) - I * Real.log (‖(z : ℂ)‖ / r₁) := by
  apply Complex.ext
  · simp [doubleLog, mul_re, log_im, div_eq_mul_inv, ← ofReal_inv,
      arg_mul_ofReal (z : ℂ) (inv_pos.mpr hr₁.out)]
  · simp [doubleLog_im, mul_im]

/-- The first-sheet formula with the usual polar argument and radial logarithm. -/
@[simp]
theorem doubleTorusDiffeomorph_inl (z : closedAnnulus r₁ r₂) :
    doubleTorusDiffeomorph r₁ r₂ (DoubleAlong.inl _ z) =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ)
        ((arg (z : ℂ) : ℂ) - I * Real.log (‖(z : ℂ)‖ / r₁)) := by
  rw [doubleTorusDiffeomorph_apply, doubleTorusMap_inl]
  simpa only [doubleLog] using congrArg (Quotient.mk _) (doubleLog_eq_arg_sub_log_norm z)

/-- The second-sheet formula is the conjugate polar logarithmic coordinate. -/
@[simp]
theorem doubleTorusDiffeomorph_inr (z : closedAnnulus r₁ r₂) :
    doubleTorusDiffeomorph r₁ r₂ (DoubleAlong.inr _ z) =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ)
        (conj ((arg (z : ℂ) : ℂ) - I * Real.log (‖(z : ℂ)‖ / r₁))) := by
  rw [doubleTorusDiffeomorph_apply, doubleTorusMap_inr]
  simpa only [doubleLog] using
    congrArg (fun w ↦ Quotient.mk _ (conj w)) (doubleLog_eq_arg_sub_log_norm z)

/-- The biholomorphism intertwines sheet exchange with complex conjugation on the torus. -/
theorem doubleTorusDiffeomorph_swap (z : SchottkyDouble (closedAnnulus r₁ r₂)) :
    doubleTorusDiffeomorph r₁ r₂ (DoubleAlong.swap _ z) =
      doubleTorusConjugation r₁ r₂ (doubleTorusDiffeomorph r₁ r₂ z) := by
  simp only [doubleTorusDiffeomorph_apply, doubleTorusMap_swap]

/-- A circle of fixed radius in the annulus, carried to its analytic double's quotient torus.
The endpoint radii give the two boundary circles fixed by quotient conjugation. -/
def doubleTorusCircle (ρ : Icc r₁ r₂) :
    C(Circle, AddAction.orbitRel.Quotient (doublePeriodLattice r₁ r₂) ℂ) where
  toFun ζ := doubleTorusDiffeomorph r₁ r₂ (DoubleAlong.inl _
    ((closedAnnulusHomeomorph hr₁.out).symm (ζ, ρ)))
  continuous_toFun := (doubleTorusDiffeomorph r₁ r₂).continuous.comp
    ((DoubleAlong.inl _).continuous.comp ((closedAnnulusHomeomorph hr₁.out).symm.continuous.comp
      (continuous_id.prodMk continuous_const)))

/-- Every fixed-radius circle is embedded in the quotient torus. -/
theorem isEmbedding_doubleTorusCircle (ρ : Icc r₁ r₂) :
    IsEmbedding (doubleTorusCircle (r₁ := r₁) (r₂ := r₂) ρ) :=
  (doubleTorusDiffeomorph r₁ r₂).toHomeomorph.isEmbedding.comp
    ((DoubleAlong.isEmbedding_inl _).comp
      ((closedAnnulusHomeomorph hr₁.out).symm.isEmbedding.comp (isEmbedding_prodMkLeft ρ)))

/-- The quotient coordinate of a circle at radius `ρ` is its argument with constant imaginary
part `-log(ρ/r₁)`. -/
theorem doubleTorusCircle_apply (ρ : Icc r₁ r₂) (ζ : Circle) :
    doubleTorusCircle (r₁ := r₁) (r₂ := r₂) ρ ζ =
      Quotient.mk (AddAction.orbitRel (doublePeriodLattice r₁ r₂) ℂ)
        ((arg (ζ : ℂ) : ℂ) - I * Real.log ((ρ : ℝ) / r₁)) := by
  simp only [doubleTorusCircle, ContinuousMap.coe_mk]
  rw [doubleTorusDiffeomorph_inl, coe_closedAnnulusHomeomorph_symm_apply]
  have hρ : 0 < (ρ : ℝ) := hr₁.out.trans_le ρ.property.1
  simp [Complex.real_smul, arg_ofReal_mul hρ (ζ : ℂ), Circle.norm_coe, abs_of_pos hρ]

private theorem range_doubleTorusCircle (ρ : Icc r₁ r₂) :
    range (doubleTorusCircle (r₁ := r₁) (r₂ := r₂) ρ) =
      (fun z : closedAnnulus r₁ r₂ ↦ doubleTorusDiffeomorph r₁ r₂ (DoubleAlong.inl _ z)) ''
        {z | ‖(z : ℂ)‖ = (ρ : ℝ)} := by
  ext q
  constructor
  · rintro ⟨ζ, rfl⟩
    refine ⟨(closedAnnulusHomeomorph hr₁.out).symm (ζ, ρ), ?_, ?_⟩
    · rw [mem_ofPred_eq, ← coe_closedAnnulusHomeomorph_apply_snd hr₁.out,
        (closedAnnulusHomeomorph hr₁.out).apply_symm_apply]
    · simp only [doubleTorusCircle, ContinuousMap.coe_mk]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(closedAnnulusHomeomorph hr₁.out z).1, ?_⟩
    have hs : (closedAnnulusHomeomorph hr₁.out z).2 = ρ :=
      Subtype.ext ((coe_closedAnnulusHomeomorph_apply_snd hr₁.out z).trans hz)
    simp only [doubleTorusCircle, ContinuousMap.coe_mk]
    rw [← hs, Prod.mk.eta, (closedAnnulusHomeomorph hr₁.out).symm_apply_apply]

/-- The fixed locus of quotient conjugation consists exactly of the two embedded circles
coming from the inner and outer boundaries of the annulus. -/
theorem fixed_locus_doubleTorusConjugation :
    {q | doubleTorusConjugation r₁ r₂ q = q} =
      range (doubleTorusCircle ⟨r₁, le_rfl, hr₁₂.out.le⟩) ∪
        range (doubleTorusCircle ⟨r₂, hr₁₂.out.le, le_rfl⟩) := by
  rw [range_doubleTorusCircle, range_doubleTorusCircle]
  ext q
  constructor
  · intro hq
    rw [mem_ofPred_eq] at hq
    obtain ⟨p, rfl⟩ := (doubleTorusDiffeomorph r₁ r₂).surjective q
    have hp : DoubleAlong.swap _ p = p := (doubleTorusDiffeomorph r₁ r₂).injective
      ((doubleTorusDiffeomorph_swap p).trans hq)
    have hm : p ∈ DoubleAlong.inl _ '' (borderedInterior (closedAnnulus r₁ r₂) : Set _)ᶜ := by
      rw [← DoubleAlong.fixed_locus, mem_ofPred_eq]
      exact hp
    obtain ⟨z, hz, rfl⟩ := hm
    rw [compl_borderedInterior, DoubleAlong.mem_annulusBoundary] at hz
    rcases hz with hz | hz
    · exact Or.inl ⟨z, hz, rfl⟩
    · exact Or.inr ⟨z, hz, rfl⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    all_goals
      have hb : z ∈ (borderedInterior (closedAnnulus r₁ r₂) : Set _)ᶜ := by
        rw [compl_borderedInterior, DoubleAlong.mem_annulusBoundary]
        first | exact Or.inl hz | exact Or.inr hz
      simp only [mem_ofPred_eq]
      rw [← doubleTorusDiffeomorph_swap, DoubleAlong.swap_inl,
        ← (DoubleAlong.inl_eq_inr_iff _).2 ⟨rfl, hb⟩]

/-- The two fixed boundary circles are disjoint. Strict separation of the radii is retained. -/
theorem disjoint_doubleTorus_boundary_circles :
    Disjoint (range (doubleTorusCircle (r₁ := r₁) (r₂ := r₂) ⟨r₁, le_rfl, hr₁₂.out.le⟩))
      (range (doubleTorusCircle ⟨r₂, hr₁₂.out.le, le_rfl⟩)) := by
  rw [range_doubleTorusCircle, range_doubleTorusCircle, Set.disjoint_left]
  rintro q ⟨x, hx, hq⟩ ⟨y, hy, hq'⟩
  have hxy : x = y := (DoubleAlong.isEmbedding_inl _).injective
    ((doubleTorusDiffeomorph r₁ r₂).injective (hq.trans hq'.symm))
  have he : r₁ = r₂ := hx.symm.trans (hxy ▸ hy)
  exact hr₁₂.out.ne he

/-- The analytic annulus double has finite CW type by the native topological double comparison. -/
instance instFiniteCWTypeSchottkyDouble :
    FiniteCWType (SchottkyDouble (closedAnnulus r₁ r₂)) := by
  -- The seam equality is propositional. Unfold the double so `rw` abstracts the seam in
  -- its type and quotient topology together; class congruence for `simp` holds the type fixed.
  unfold SchottkyDouble
  rw [compl_borderedInterior]
  exact DoubleAlong.finiteCWType_annulusDouble hr₁.out hr₁₂.out

/-- The native analytic double has Euler characteristic zero, by the existing topological
annulus-double comparison with `Circle × Circle`. -/
theorem eulerChar_schottkyDouble :
    eulerChar (SchottkyDouble (closedAnnulus r₁ r₂)) = 0 := by
  let := DoubleAlong.finiteCWType_annulusDouble hr₁.out hr₁₂.out
  -- Compare the quotient topologies along the same seam equality, then use the existing
  -- homeomorphism invariance of Euler characteristic.
  let e : SchottkyDouble (closedAnnulus r₁ r₂) ≃ₜ
      DoubleAlong (DoubleAlong.annulusBoundary r₁ r₂) := by
    unfold SchottkyDouble
    rw [compl_borderedInterior]
    exact Homeomorph.refl _
  rw [e.eulerChar_eq]
  exact DoubleAlong.eulerChar_annulusDouble hr₁.out hr₁₂.out

end Double

end TauCeti.ClosedAnnulus
