/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier

/-!
# Smooth winding reference fields on the plane

The affine Sobolev space of framed degree-`m` vortex fields is centered at a smooth pair
which equals `(-i m dθ, exp(i m θ))` outside a disc. Here `referenceConnection` and
`referenceSection` construct such a pair using a radial cutoff. Connections are actual
complex-valued real continuous-linear one-forms; their values are purely imaginary.
The cutoff removes the angular singularity on a neighborhood of the origin.

The end formulas, rotation laws and compact support of changes of cutoff are proved
explicitly. The latter allows different references to define the same affine Sobolev
space. These reference pairs are not asserted to solve the vortex equations.

Outside a disc the section is homogeneous of degree `0` and the connection of degree `-1`, so all
their derivatives are bounded (`exists_norm_iteratedFDeriv_referenceSection_le`,
`exists_norm_iteratedFDeriv_referenceConnection_le`), and they have temperate growth. Consequently,
for `1 < p < ∞`, multiplication by the reference section or by a coefficient of the reference
connection maps each integer-order Bessel-potential space `H^{k,p}(ℂ; F)` into itself
(`memSobolev_smulLeftCLM_referenceSection`, `memSobolev_smulLeftCLM_referenceConnection_apply`).
These are the products of reference coefficients with Sobolev increments in the vortex equations
and gauge action on the affine field space.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric
open scoped ContDiff Topology

private def cutoff (f : ContDiffBump (0 : ℝ)) (z : ℂ) : ℝ :=
  1 - f (‖z‖ ^ 2)

private theorem contDiff_cutoff (f : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ∞ (cutoff f) :=
  contDiff_const.sub (f.contDiff.comp (contDiff_norm_sq ℂ))

private theorem cutoff_eq_zero (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ f.rIn) : cutoff f z = 0 := by
  simp [cutoff, f.one_of_mem_closedBall (x := ‖z‖ ^ 2)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg] using hz)]

private theorem cutoff_eq_one (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hz : f.rOut ≤ ‖z‖ ^ 2) : cutoff f z = 1 := by
  simp [cutoff, f.zero_of_le_dist (x := ‖z‖ ^ 2)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg] using hz)]

private theorem cutoff_eventuallyEq_zero (f : ContDiffBump (0 : ℝ)) :
    cutoff f =ᶠ[𝓝 0] 0 := by
  have h := f.eventuallyEq_one.comp_tendsto
    (by simpa using (continuous_norm.pow 2).tendsto (0 : ℂ))
  filter_upwards [h] with z hz
  simp only [Function.comp_apply, Pi.one_apply, Pi.pow_apply] at hz
  simp [cutoff, hz]

/-- A globally smooth section equal to the winding phase `(z / ‖z‖)^m` outside a disc.
The bump is applied to the squared radius, so the construction is rotation-equivariant. -/
def referenceSection (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) : ℂ :=
  (cutoff f z : ℂ) * (z / (‖z‖ : ℂ)) ^ m

/-- A globally smooth imaginary connection one-form equal to `-i m dθ` outside a disc,
where `dθ_z(v) = Im(v / z)`. -/
def referenceConnection (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (-(m : ℂ) * I * (cutoff f z : ℂ)) •
    ((ofRealCLM.comp imCLM).comp (ContinuousLinearMap.mul ℝ ℂ z⁻¹))

/-- Evaluation of the reference section in the fixed complex coordinate. -/
@[simp]
theorem referenceSection_apply (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) :
    referenceSection f m z = (1 - f (‖z‖ ^ 2) : ℝ) * (z / (‖z‖ : ℂ)) ^ m := by
  simp [referenceSection, cutoff]

/-- Evaluation of the reference connection on a real tangent vector. -/
@[simp]
theorem referenceConnection_apply (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z v : ℂ) :
    referenceConnection f m z v =
      -(m : ℂ) * I * (1 - f (‖z‖ ^ 2) : ℝ) * ((v / z).im : ℂ) := by
  simp [referenceConnection, cutoff, div_eq_mul_inv, mul_comm]

/-- The reference section vanishes on the inner disc. -/
theorem referenceSection_eq_zero (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ f.rIn) : referenceSection f m z = 0 := by
  simp [referenceSection, cutoff_eq_zero f hz]

/-- The connection vanishes on the inner disc, removing the angular singularity. -/
theorem referenceConnection_eq_zero (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ f.rIn) : referenceConnection f m z = 0 := by
  simp [referenceConnection, cutoff_eq_zero f hz]

/-- The reference section has the exact prescribed winding tail. -/
theorem referenceSection_eq_phase (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : f.rOut ≤ ‖z‖ ^ 2) : referenceSection f m z = (z / (‖z‖ : ℂ)) ^ m := by
  simp [referenceSection, cutoff_eq_one f hz]

/-- The reference connection has the exact angular tail `-i m dθ`. -/
theorem referenceConnection_eq_angular (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : f.rOut ≤ ‖z‖ ^ 2) (v : ℂ) :
    referenceConnection f m z v = -(m : ℂ) * I * ((v / z).im : ℂ) := by
  simp [referenceConnection, cutoff_eq_one f hz, div_eq_mul_inv, mul_comm]

/-- The winding phase `(z / ‖z‖)^m` is smooth away from the origin. -/
private theorem contDiffOn_phase (m : ℕ) {N : WithTop ℕ∞} :
    ContDiffOn ℝ N (fun z : ℂ ↦ (z / (‖z‖ : ℂ)) ^ m) {0}ᶜ := by
  intro z hz
  have hz : z ≠ 0 := hz
  have hn : ContDiffAt ℝ N (fun w : ℂ ↦ (‖w‖ : ℂ)) z :=
    ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℂ hz)
  have hp : ContDiffAt ℝ N (fun w : ℂ ↦ w / (‖w‖ : ℂ)) z := by
    simpa only [div_eq_mul_inv, Pi.inv_apply, id_eq] using
      contDiffAt_id.mul (hn.inv (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)))
  exact (hp.pow m).contDiffWithinAt

/-- The section is smooth even at the origin. -/
theorem contDiff_referenceSection (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    ContDiff ℝ ∞ (referenceSection f m) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [cutoff_eventuallyEq_zero f] with z hz
    simp [referenceSection, hz]
  · exact (ofRealCLM.contDiff.comp (contDiff_cutoff f)).contDiffAt.mul
      ((contDiffOn_phase m).contDiffAt (isOpen_compl_singleton.mem_nhds hz))

/-- The connection is a smooth map into the space of one-forms, including at the origin. -/
theorem contDiff_referenceConnection (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    ContDiff ℝ ∞ (referenceConnection f m) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const (c := (0 : ℂ →L[ℝ] ℂ))).congr_of_eventuallyEq
    filter_upwards [cutoff_eventuallyEq_zero f] with z hz
    simp [referenceConnection, hz]
  · exact (contDiffAt_const.mul (ofRealCLM.contDiff.comp
        (contDiff_cutoff f)).contDiffAt).smul
      (contDiffAt_const.clm_comp ((ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp z
        (contDiffAt_id.inv hz)))

/-- The exact winding tail has unit norm. -/
theorem norm_referenceSection (f : ContDiffBump (0 : ℝ)) (m : ℕ) {z : ℂ}
    (hz : f.rOut ≤ ‖z‖ ^ 2) : ‖referenceSection f m z‖ = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
    linarith [f.rOut_pos]
  rw [referenceSection_eq_phase f m hz, norm_pow, norm_div]
  simp [norm_ne_zero_iff.2 hz0]

/-- The reference section has norm at most one everywhere. -/
theorem norm_referenceSection_le_one (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) :
    ‖referenceSection f m z‖ ≤ 1 := by
  rw [referenceSection_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h₁ : |1 - f (‖z‖ ^ 2)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [f.nonneg (x := ‖z‖ ^ 2), f.le_one (x := ‖z‖ ^ 2)]
  have h₂ : ‖z / (‖z‖ : ℂ)‖ ^ m ≤ 1 := by
    refine pow_le_one₀ (norm_nonneg _) ?_
    rw [norm_div, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  simpa using mul_le_mul h₁ h₂ (by positivity) zero_le_one

/-- The modulus defect `1 - ‖α_ref‖` of the reference section is compactly supported: it vanishes
outside the disc where the cutoff is active. -/
theorem hasCompactSupport_one_sub_norm_referenceSection (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    HasCompactSupport fun z ↦ 1 - ‖referenceSection f m z‖ := by
  refine HasCompactSupport.intro (isCompact_closedBall 0 (f.rOut + 1)) fun z hz ↦ ?_
  have hz' : f.rOut ≤ ‖z‖ ^ 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    nlinarith [f.rOut_pos]
  rw [norm_referenceSection f m hz', sub_self]

/-- Rotation of the coordinate multiplies the reference section by the degree-`m` phase. -/
theorem referenceSection_mul (f : ContDiffBump (0 : ℝ)) (m : ℕ) {u : ℂ}
    (hu : ‖u‖ = 1) (z : ℂ) :
    referenceSection f m (u * z) = u ^ m * referenceSection f m z := by
  simp only [referenceSection, cutoff, norm_mul, hu, one_mul]
  rw [mul_div_assoc, mul_pow]
  ring

/-- The reference connection is invariant under simultaneous rotation of point and vector. -/
theorem referenceConnection_mul (f : ContDiffBump (0 : ℝ)) (m : ℕ) {u : ℂ}
    (hu : ‖u‖ = 1) (z v : ℂ) :
    referenceConnection f m (u * z) (u * v) = referenceConnection f m z v := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  simp [referenceConnection_apply, hu, mul_div_mul_left _ _ hu0]

private theorem hasCompactSupport_cutoff_sub (f g : ContDiffBump (0 : ℝ)) :
    HasCompactSupport (cutoff f - cutoff g) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (max f.rOut g.rOut + 1))
  intro z hz
  have hnorm : max f.rOut g.rOut + 1 < ‖z‖ := by simpa using hz
  have hf : f.rOut ≤ ‖z‖ ^ 2 := by nlinarith [le_max_left f.rOut g.rOut, f.rOut_pos]
  have hg : g.rOut ≤ ‖z‖ ^ 2 := by nlinarith [le_max_right f.rOut g.rOut, g.rOut_pos]
  simp [cutoff_eq_one f hf, cutoff_eq_one g hg]

/-- Changing the radial cutoff changes the section by a compactly supported smooth field. -/
theorem hasCompactSupport_referenceSection_sub (f g : ContDiffBump (0 : ℝ)) (m : ℕ) :
    HasCompactSupport (referenceSection f m - referenceSection g m) := by
  apply (hasCompactSupport_cutoff_sub f g).mono
  intro z hz
  simp only [Function.mem_support, Pi.sub_apply, ne_eq, sub_eq_zero] at *
  exact fun h ↦ hz (by simp [referenceSection, h])

/-- Changing the radial cutoff changes the connection by a compactly supported smooth one-form. -/
theorem hasCompactSupport_referenceConnection_sub (f g : ContDiffBump (0 : ℝ)) (m : ℕ) :
    HasCompactSupport (referenceConnection f m - referenceConnection g m) := by
  apply (hasCompactSupport_cutoff_sub f g).mono
  intro z hz
  simp only [Function.mem_support, Pi.sub_apply, ne_eq, sub_eq_zero] at *
  exact fun h ↦ hz (by simp [referenceConnection, h])

/-! ### Bounded derivatives and Sobolev multiplication -/

/-- The winding phase is homogeneous of degree `0`. -/
private theorem phase_smul (m : ℕ) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (t • z / (‖t • z‖ : ℂ)) ^ m = (z / (‖z‖ : ℂ)) ^ m := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [norm_smul, Real.norm_of_nonneg ht.le, real_smul, ofReal_mul,
    mul_div_mul_left _ _ (ofReal_ne_zero.2 ht.ne')]

/-- The angular connection `-i m dθ` is smooth away from the origin. -/
private theorem contDiffOn_angular (m : ℕ) {N : WithTop ℕ∞} :
    ContDiffOn ℝ N (fun z : ℂ ↦ (-(m : ℂ) * I) •
      ((ofRealCLM.comp imCLM).comp (ContinuousLinearMap.mul ℝ ℂ z⁻¹))) {0}ᶜ := fun z hz ↦
  ((contDiffAt_const.clm_comp ((ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp z
    (contDiffAt_inv ℝ hz))).const_smul _).contDiffWithinAt

/-- The angular connection `-i m dθ` is homogeneous of degree `-1`. -/
private theorem angular_smul (m : ℕ) (t : ℝ) (z : ℂ) :
    (-(m : ℂ) * I) • ((ofRealCLM.comp imCLM).comp (ContinuousLinearMap.mul ℝ ℂ (t • z)⁻¹)) =
      t ^ (-1 : ℤ) • ((-(m : ℂ) * I) •
        ((ofRealCLM.comp imCLM).comp (ContinuousLinearMap.mul ℝ ℂ z⁻¹))) := by
  ext v
  simp [real_smul]
  ring

/-- Outside the disc of radius `max 1 f.rOut` the squared radius exceeds `f.rOut`. -/
private theorem rOut_le_norm_sq (f : ContDiffBump (0 : ℝ)) {z : ℂ} (hz : max 1 f.rOut < ‖z‖) :
    f.rOut ≤ ‖z‖ ^ 2 := by
  have h1 : 1 < ‖z‖ := (le_max_left _ _).trans_lt hz
  nlinarith [le_max_right 1 f.rOut]

/-- Every iterated derivative of the reference section is bounded. -/
theorem exists_norm_iteratedFDeriv_referenceSection_le (f : ContDiffBump (0 : ℝ)) (m n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (referenceSection f m) z‖ ≤ C :=
  exists_norm_iteratedFDeriv_le_of_eq_of_smul_eq (d := 0) le_rfl
    ((contDiff_referenceSection f m).of_le (by exact_mod_cast le_top)) (contDiffOn_phase m)
    (fun t ht z _ ↦ by rw [zpow_zero, one_smul, phase_smul m ht])
    (fun _ hz ↦ referenceSection_eq_phase f m (rOut_le_norm_sq f hz)) n le_rfl

/-- Every iterated derivative of the reference connection is bounded. -/
theorem exists_norm_iteratedFDeriv_referenceConnection_le (f : ContDiffBump (0 : ℝ)) (m n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (referenceConnection f m) z‖ ≤ C := by
  refine exists_norm_iteratedFDeriv_le_of_eq_of_smul_eq (d := -1) (by norm_num)
    ((contDiff_referenceConnection f m).of_le (by exact_mod_cast le_top))
    (contDiffOn_angular m) (fun t _ z _ ↦ angular_smul m t z) (R := max 1 f.rOut)
    (fun z hz ↦ ?_) n le_rfl
  ext v
  rw [referenceConnection_eq_angular f m (rOut_le_norm_sq f hz)]
  simp [div_eq_mul_inv, mul_comm]

/-- Every iterated derivative of a coefficient `z ↦ a_m(z) v` of the reference connection is
bounded. -/
theorem exists_norm_iteratedFDeriv_referenceConnection_apply_le (f : ContDiffBump (0 : ℝ))
    (m n : ℕ) (v : ℂ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ referenceConnection f m z v) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_referenceConnection_le f m n
  refine ⟨‖ContinuousLinearMap.apply ℝ ℂ v‖ * C, fun z ↦ ?_⟩
  refine ((ContinuousLinearMap.apply ℝ ℂ v).norm_iteratedFDeriv_comp_left
    (contDiff_referenceConnection f m).contDiffAt (by exact_mod_cast le_top)).trans ?_
  gcongr
  exact hC z

/-- The reference section has temperate growth. -/
theorem hasTemperateGrowth_referenceSection (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    (referenceSection f m).HasTemperateGrowth :=
  .of_norm_iteratedFDeriv_le (contDiff_referenceSection f m)
    (exists_norm_iteratedFDeriv_referenceSection_le f m)

/-- Each coefficient `z ↦ a_m(z) v` of the reference connection has temperate growth. -/
theorem hasTemperateGrowth_referenceConnection_apply (f : ContDiffBump (0 : ℝ)) (m : ℕ) (v : ℂ) :
    (fun z ↦ referenceConnection f m z v).HasTemperateGrowth :=
  .of_norm_iteratedFDeriv_le
    ((ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp (contDiff_referenceConnection f m))
    fun n ↦ exists_norm_iteratedFDeriv_referenceConnection_apply_le f m n v

section Sobolev

open TemperedDistribution
open scoped SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ENNReal} [Fact (1 ≤ p)]

/-- **Multiplication by the reference section preserves `H^{k,p}`**, for `1 < p < ∞` and every
natural order `k`. -/
theorem memSobolev_smulLeftCLM_referenceSection (hp : 1 < p) (hp_top : p ≠ ⊤)
    (f : ContDiffBump (0 : ℝ)) (m : ℕ) {k : ℕ} {u : 𝓢'(ℂ, F)} (hu : MemSobolev k p u) :
    MemSobolev k p (smulLeftCLM F (referenceSection f m) u) :=
  hu.smulLeftCLM_of_norm_iteratedFDeriv_le hp hp_top (hasTemperateGrowth_referenceSection f m)
    fun n _ ↦ exists_norm_iteratedFDeriv_referenceSection_le f m n

/-- **Multiplication by a coefficient `z ↦ a_m(z) v` of the reference connection preserves
`H^{k,p}`**, for `1 < p < ∞` and every natural order `k`. -/
theorem memSobolev_smulLeftCLM_referenceConnection_apply (hp : 1 < p) (hp_top : p ≠ ⊤)
    (f : ContDiffBump (0 : ℝ)) (m : ℕ) (v : ℂ) {k : ℕ} {u : 𝓢'(ℂ, F)} (hu : MemSobolev k p u) :
    MemSobolev k p (smulLeftCLM F (fun z ↦ referenceConnection f m z v) u) :=
  hu.smulLeftCLM_of_norm_iteratedFDeriv_le hp hp_top
    (hasTemperateGrowth_referenceConnection_apply f m v)
    fun n _ ↦ exists_norm_iteratedFDeriv_referenceConnection_apply_le f m n v

end Sobolev

end TauCeti.Vortex
