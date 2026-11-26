/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.RescaledNorm
public import TauCeti.Analysis.PDE.Vortex.Dilation.Basic
public import TauCeti.Analysis.PDE.Vortex.Graft
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.MeasureTheory.Function.LpSeminorm.Support

/-!
# The initial vortex graft at the scale of the large parameter

In Taubes's construction of Seiberg–Witten solutions from pseudoholomorphic curves, the leading
equations in a normal plane of the curve are the plane vortex equations with curvature coefficient
`r / 4`, that is `TauCeti.Vortex.coupledEquation c` with coupling `c = 2 r`, the equation
`*iF_a = c (1 - |α|²) / 8`. Writing `h = (2 r)^(-1/2)` for the length scale of the vortices,
the coupling is `c = h⁻²`. The gluing measures the defect of an approximate solution in the norm
`F_(r,s-1)` of `TauCeti.SeibergWitten.rescaledTargetNormSq s h`, after normalizing its rows as the
Seiberg–Witten section does: the curvature row is multiplied by `λ⁻² = h²` and the rows of
`∂bar_a α` by `λ⁻¹ = h`. This normalized defect is `TauCeti.Vortex.scaledCoupledEquation h x`.

A plane field `x` in the coordinate `w` in which vortices have unit size is moved to the coordinate
`z = h w` by `dilateField h⁻¹ x`, the pullback by `z ↦ h⁻¹ z`, which multiplies the connection by
`h⁻¹`. This file shows:

* **The normalized defect is the plane defect.** For `h ≠ 0`,
  `scaledCoupledEquation h x z = equation (dilateField h x) (h⁻¹ • z)`
  (`TauCeti.Vortex.scaledCoupledEquation_eq_equation_dilateField`, the flat scaling
  `TauCeti.Vortex.equation_dilateField_inv_sqrt` in terms of `h`), so the normalized defect of
  `dilateField h⁻¹ x` at `z` is the plane vortex defect of `x` at `w = h⁻¹ z`
  (`TauCeti.Vortex.scaledCoupledEquation_dilateField_inv`), and it vanishes exactly at the
  solutions of the coupled equation of coupling `h⁻²`
  (`TauCeti.Vortex.scaledCoupledEquation_eq_zero_iff`).
* **The norm of a moved defect.** For `h > 0` and `x` of class `Cˢ`, the `F_(r,s-1)` norm of the
  normalized defect of `dilateField h⁻¹ x` is `h²` times the unit-scale norm
  `∑_{j < s} ‖Dʲ equation x‖₂²` of the plane defect
  (`TauCeti.Vortex.rescaledTargetNormSq_scaledCoupledEquation_dilateField_inv`). The factor `h²`
  is the area element of the change of coordinates `w = h⁻¹ z`.
* **The initial vortex graft at unit scale.** The graft `TauCeti.Vortex.vortexGraft` of the
  normalized vortex `y_a` into the exterior vacuum with the dilated cutoff `w ↦ φ (w / R)` solves
  the plane vortex equation off the annulus `φ.rIn R ≤ |w| ≤ φ.rOut R`, and every derivative of its
  defect is `O(exp (-c' φ.rIn R))` there for every `c' < 1 / 2`. Integrating over the disc of
  radius `φ.rOut R` and absorbing its area `π (φ.rOut R)²` into a slightly faster rate gives, for
  every `c < 1 / 2`, `∑_{j < s} ‖Dʲ equation (graft)‖₂² ≤ K exp (-2 c φ.rIn R)`, uniformly over a
  bounded window of divisor coefficients
  (`TauCeti.Vortex.exists_rescaledTargetNormSq_one_equation_vortexGraft_le`).
* **The initial vortex graft at the scale `h`.** Hence the normalized defect of the graft moved to
  the scale `h` has squared `F_(r,s-1)` norm at most `K h² exp (-2 c φ.rIn R)`, with `K`
  independent of `h`, `R` and the coefficients
  (`TauCeti.Vortex.exists_rescaledTargetNormSq_scaledCoupledEquation_vortexGraft_le`). For a cutoff
  of fixed radius `ρ` in the coordinate `z`, that is `R = ρ / h`, this is
  `K h² exp (-2 c φ.rIn ρ / h)` for all small `h`
  (`TauCeti.Vortex.exists_rescaledTargetNormSq_scaledCoupledEquation_vortexGraft_div_le`): in terms
  of `r`, the squared residual of the initial approximate solution is
  `O(r⁻¹ exp (-2 c φ.rIn ρ √(2 r)))`.

These are statements about the flat plane model of one normal disc; the curvature of the normal
tube, the background connection and the clutching with the exterior solution on a four-manifold
are not treated here.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open MeasureTheory Metric Module TauCeti.SeibergWitten
open scoped ContDiff

namespace TauCeti.Vortex

/-! ### The normalized defect at coupling `h⁻²` -/

/-- **The normalized defect at coupling `h⁻²`.** The defect of the field `x` for the plane vortex
equation `*iF_a = (1 - |α|²) / (8 h²)` with coupling `h⁻²`, normalized as the Seiberg–Witten
section of Taubes's gluing at `h = (2 r)^(-1/2)`: its curvature row is multiplied by `h²` and the
two rows of `∂bar_a α` by `h`. -/
def scaledCoupledEquation (h : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[h ^ 2 * coupledEquation (h ^ 2)⁻¹ x z 0, h * coupledEquation (h ^ 2)⁻¹ x z 1,
    h * coupledEquation (h ^ 2)⁻¹ x z 2]

theorem scaledCoupledEquation_def (h : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    scaledCoupledEquation h x z =
      !₂[h ^ 2 * coupledEquation (h ^ 2)⁻¹ x z 0, h * coupledEquation (h ^ 2)⁻¹ x z 1,
        h * coupledEquation (h ^ 2)⁻¹ x z 2] :=
  (rfl)

@[simp]
theorem scaledCoupledEquation_apply_zero (h : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    scaledCoupledEquation h x z 0 = h ^ 2 * coupledEquation (h ^ 2)⁻¹ x z 0 :=
  (rfl)

@[simp]
theorem scaledCoupledEquation_apply_one (h : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    scaledCoupledEquation h x z 1 = h * coupledEquation (h ^ 2)⁻¹ x z 1 :=
  (rfl)

@[simp]
theorem scaledCoupledEquation_apply_two (h : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    scaledCoupledEquation h x z 2 = h * coupledEquation (h ^ 2)⁻¹ x z 2 :=
  (rfl)

/-- **The normalized defect is the plane defect in the unit-scale coordinate.** For `h ≠ 0`, the
normalized defect of `x` at `z` is the plane vortex defect of the dilated field `dilateField h x`
at `w = h⁻¹ z`. -/
theorem scaledCoupledEquation_eq_equation_dilateField {h : ℝ} (hh : h ≠ 0)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    scaledCoupledEquation h x z = equation (dilateField h x) (h⁻¹ • z) := by
  have h₁ := coupledEquation_dilateField (h ^ 2)⁻¹ h x (h⁻¹ • z)
  rw [mul_inv_cancel₀ (pow_ne_zero 2 hh), coupledEquation_one, smul_inv_smul₀ hh] at h₁
  rw [h₁, scaledCoupledEquation_def]

/-- **The normalized defect of a field moved to the scale `h`.** For `h ≠ 0`, the normalized
defect of `dilateField h⁻¹ x`, the field `x` moved from the coordinate `w` to `z = h w`, is the
plane vortex defect of `x` at `w = h⁻¹ z`. -/
@[simp]
theorem scaledCoupledEquation_dilateField_inv {h : ℝ} (hh : h ≠ 0)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    scaledCoupledEquation h (dilateField h⁻¹ x) z = equation x (h⁻¹ • z) := by
  rw [scaledCoupledEquation_eq_equation_dilateField hh, dilateField_dilateField,
    mul_inv_cancel₀ hh, dilateField_one]

/-- For `h ≠ 0`, the normalized defect vanishes exactly at the solutions of the plane vortex
equation of coupling `h⁻²`. -/
theorem scaledCoupledEquation_eq_zero_iff {h : ℝ} (hh : h ≠ 0)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    scaledCoupledEquation h x = 0 ↔ coupledEquation (h ^ 2)⁻¹ x = 0 := by
  rw [← coupledEquation_dilateField_eq_zero_iff (h ^ 2)⁻¹ hh x,
    mul_inv_cancel₀ (pow_ne_zero 2 hh), coupledEquation_one]
  simp only [funext_iff, Pi.zero_apply, scaledCoupledEquation_eq_equation_dilateField hh]
  refine ⟨fun H w ↦ ?_, fun H z ↦ H _⟩
  simpa [smul_smul, hh] using H (h • w)

/-- **The norm of a defect moved to the scale `h`.** For `h > 0` and a field `x` of class `Cˢ`,
the `F_(r,s-1)` norm at the scale `h` of the normalized defect of `dilateField h⁻¹ x` is `h²` times
the unit-scale norm of the plane vortex defect of `x`:
`‖·‖_(F_(r,s-1))² = h² ∑_{j < s} ‖Dʲ equation x‖₂²`. -/
theorem rescaledTargetNormSq_scaledCoupledEquation_dilateField_inv {s : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ s x) {h : ℝ} (hh : 0 < h) :
    rescaledTargetNormSq s h (scaledCoupledEquation h (dilateField h⁻¹ x)) =
      h ^ 2 * rescaledTargetNormSq s 1 (equation x) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [rescaledTargetNormSq_def]
  have hE : ContDiff ℝ (s - 1 : ℕ) fun z ↦ equation x (h⁻¹ • z) :=
    (contDiff_equation hx (by exact_mod_cast (by omega : s - 1 + 1 ≤ s))).comp
      (contDiff_const_smul _)
  rw [funext (scaledCoupledEquation_dilateField_inv hh.ne' x),
    rescaledTargetNormSq_eq_rpow_mul hE hh, Complex.finrank_real_complex]
  simp only [smul_smul, inv_mul_cancel₀ hh.ne', one_smul, Nat.cast_ofNat, Real.rpow_two]

/-! ### The initial vortex graft -/

variable {m : ℕ}

/-- The squared `L²` norm of a derivative of the defect of the graft with the dilated cutoff
`w ↦ φ (w / R)`, bounded pointwise by `C`, is at most `C² π (φ.rOut R)²`: the defect vanishes off
the disc of radius `φ.rOut R`. -/
private theorem lpNorm_iteratedFDeriv_equation_vortexGraft_sq_le (hm : 0 < m)
    (f : ContDiffBump (0 : ℝ)) (φ : ContDiffBump (0 : ℂ)) {R : ℝ} (hR : 0 < R)
    (hrOut : f.rOut < (φ.rIn * R) ^ 2) (a : Fin m → ℂ) (j : ℕ) {C : ℝ}
    (hC : ∀ z, ‖iteratedFDeriv ℝ j (equation (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a)) z‖ ≤ C) :
    lpNorm (iteratedFDeriv ℝ j (equation (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a))) 2 volume ^ 2 ≤
      C ^ 2 * (Real.pi * (φ.rOut * R) ^ 2) := by
  have hχ : ContDiff ℝ ∞ fun w ↦ φ (R⁻¹ • w) := φ.contDiff.comp (contDiff_const_smul _)
  have hE : ContDiff ℝ (j + 1 : ℕ) (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a) :=
    (contDiff_vortexGraft f hχ a).of_le (mod_cast le_top)
  have hρ : 0 ≤ φ.rOut * R := mul_nonneg φ.rOut_pos.le hR.le
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hsupp : Function.support
      (iteratedFDeriv ℝ j (equation (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a))) ⊆
        closedBall 0 (φ.rOut * R) := fun z hz ↦ by
    by_contra hz'
    refine hz ?_
    rw [((equation_vortexGraft_bump_comp_inv_smul_eventuallyEq_zero hm f φ hR hrOut a
      (Or.inr (by simpa using hz'))).iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_zero,
      Pi.zero_apply]
  have hL := eLpNorm_le_of_ae_bound_of_support_subset (μ := volume) (p := 2)
    ((contDiff_equation hE (by push_cast; exact le_rfl)).continuous_iteratedFDeriv
      le_rfl).aestronglyMeasurable hsupp (.of_forall hC)
  rw [Complex.volume_closedBall, ENNReal.toReal_ofNat] at hL
  replace hL := ENNReal.toReal_mono (by finiteness) hL
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀, ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ, ENNReal.coe_toReal, NNReal.coe_real_pi] at hL
  have hsq : (((φ.rOut * R) ^ 2 * Real.pi) ^ (2⁻¹ : ℝ)) ^ 2 = (φ.rOut * R) ^ 2 * Real.pi := by
    exact_mod_cast Real.rpow_inv_natCast_pow (n := 2) (by positivity) two_ne_zero
  rw [← toReal_eLpNorm]
  calc _ ≤ (((φ.rOut * R) ^ 2 * Real.pi) ^ (2⁻¹ : ℝ) * C) ^ 2 :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg hL 2
    _ = _ := by rw [mul_pow, hsq]; ring

/-- **The defect of the initial vortex graft at unit scale.** Let `m ≥ 1`, `S` a bounded set of
divisor coefficients, `φ` a bump function on `ℂ`, `s` an order and `c < 1 / 2` a rate. There is
`K` such that for every `R > 0` with `f.rOut < (φ.rIn R)²` and every `a ∈ S`, the vortex defect of
the graft of the normalized vortex `y_a` with the dilated cutoff `w ↦ φ (w / R)` satisfies
`∑_{j < s} ‖Dʲ equation (graft)‖₂² ≤ K exp (-2 c φ.rIn R)`. -/
theorem exists_rescaledTargetNormSq_one_equation_vortexGraft_le (hm : 0 < m)
    (f : ContDiffBump (0 : ℝ)) (φ : ContDiffBump (0 : ℂ)) {S : Set (Fin m → ℂ)}
    (hS : Bornology.IsBounded S) (s : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ R, 0 < R → f.rOut < (φ.rIn * R) ^ 2 → ∀ a ∈ S,
      rescaledTargetNormSq s 1 (equation (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a)) ≤
        K * Real.exp (-(2 * c * (φ.rIn * R))) := by
  -- A faster rate `c'`, whose surplus over `c` absorbs the area of the disc carrying the defect.
  obtain ⟨c', hcc', hc'⟩ := exists_between hc
  have hA : 0 < 2 * (c' - c) * φ.rIn := by have := φ.rIn_pos; nlinarith
  choose K hK using fun j : ℕ ↦
    exists_norm_iteratedFDeriv_equation_vortexGraft_bump_comp_inv_smul_le_mul_exp hm f φ hS j hc'
  refine ⟨∑ j ∈ Finset.range s, K j ^ 2 * (Real.pi * φ.rOut ^ 2) *
    (2 / (2 * (c' - c) * φ.rIn) ^ 2), fun R hR hrOut a ha ↦ ?_⟩
  rw [rescaledTargetNormSq_def, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [one_pow, one_mul]
  -- The area factor `R²` is absorbed by `exp (-2 (c' - c) φ.rIn R)`.
  have hR₂ := pow_mul_exp_neg_mul_le hA hR.le 2
  rw [Nat.factorial_two, Nat.cast_ofNat] at hR₂
  have hexp : Real.exp (-(c' * (φ.rIn * R))) ^ 2 =
      Real.exp (-(2 * c * (φ.rIn * R))) * Real.exp (-(2 * (c' - c) * φ.rIn) * R) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  calc lpNorm (iteratedFDeriv ℝ j (equation (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a))) 2
        volume ^ 2
      ≤ K j ^ 2 * (Real.pi * φ.rOut ^ 2) * Real.exp (-(2 * c * (φ.rIn * R))) *
          (R ^ 2 * Real.exp (-(2 * (c' - c) * φ.rIn) * R)) := by
        refine (lpNorm_iteratedFDeriv_equation_vortexGraft_sq_le hm f φ hR hrOut a j
          (hK j R hR hrOut a ha)).trans_eq ?_
        rw [mul_pow, hexp]
        ring
    _ ≤ K j ^ 2 * (Real.pi * φ.rOut ^ 2) * Real.exp (-(2 * c * (φ.rIn * R))) *
          (2 / (2 * (c' - c) * φ.rIn) ^ 2) := by gcongr
    _ = _ := by ring

/-- **The residual of the initial vortex graft at the scale `h`.** Let `m ≥ 1`, `S` a bounded set
of divisor coefficients, `φ` a bump function on `ℂ`, `s` an order and `c < 1 / 2` a rate. There
is `K` such that for every scale `h > 0`, every `R > 0` with `f.rOut < (φ.rIn R)²` and every
`a ∈ S`, the graft of the normalized vortex `y_a` with the dilated cutoff `w ↦ φ (w / R)`, moved
to the coordinate `z = h w`, has normalized defect at coupling `h⁻²` of `F_(r,s-1)` norm
`‖·‖_(F_(r,s-1))² ≤ K h² exp (-2 c φ.rIn R)`. -/
theorem exists_rescaledTargetNormSq_scaledCoupledEquation_vortexGraft_le (hm : 0 < m)
    (f : ContDiffBump (0 : ℝ)) (φ : ContDiffBump (0 : ℂ)) {S : Set (Fin m → ℂ)}
    (hS : Bornology.IsBounded S) (s : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ h, 0 < h → ∀ R, 0 < R → f.rOut < (φ.rIn * R) ^ 2 → ∀ a ∈ S,
      rescaledTargetNormSq s h (scaledCoupledEquation h
        (dilateField h⁻¹ (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a))) ≤
        K * h ^ 2 * Real.exp (-(2 * c * (φ.rIn * R))) := by
  obtain ⟨K, hK⟩ := exists_rescaledTargetNormSq_one_equation_vortexGraft_le hm f φ hS s hc
  refine ⟨K, fun h hh R hR hrOut a ha ↦ ?_⟩
  have hχ : ContDiff ℝ ∞ fun w ↦ φ (R⁻¹ • w) := φ.contDiff.comp (contDiff_const_smul _)
  rw [rescaledTargetNormSq_scaledCoupledEquation_dilateField_inv
    ((contDiff_vortexGraft f hχ a).of_le (mod_cast le_top)) hh]
  calc h ^ 2 * rescaledTargetNormSq s 1 (equation (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a))
      ≤ h ^ 2 * (K * Real.exp (-(2 * c * (φ.rIn * R)))) := by
        gcongr
        exact hK R hR hrOut a ha
    _ = _ := by ring

/-- **The residual of the initial vortex graft cut off at a fixed radius.** Let `m ≥ 1`, `S` a
bounded set of divisor coefficients, `φ` a bump function on `ℂ`, `ρ > 0` a radius, `s` an order
and `c < 1 / 2` a rate. There are `K` and `h₀ > 0` such that for every scale `0 < h < h₀` and
every `a ∈ S`, the graft of the normalized vortex `y_a` with the cutoff `w ↦ φ (h w / ρ)`, moved
to the coordinate `z = h w`, where its cutoff is `z ↦ φ (z / ρ)`, has normalized defect at
coupling `h⁻²` of `F_(r,s-1)` norm `‖·‖_(F_(r,s-1))² ≤ K h² exp (-2 c φ.rIn ρ / h)`. -/
theorem exists_rescaledTargetNormSq_scaledCoupledEquation_vortexGraft_div_le (hm : 0 < m)
    (f : ContDiffBump (0 : ℝ)) (φ : ContDiffBump (0 : ℂ)) {S : Set (Fin m → ℂ)}
    (hS : Bornology.IsBounded S) {ρ : ℝ} (hρ : 0 < ρ) (s : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∃ h₀, 0 < h₀ ∧ ∀ h, 0 < h → h < h₀ → ∀ a ∈ S,
      rescaledTargetNormSq s h (scaledCoupledEquation h
        (dilateField h⁻¹ (vortexGraft f (fun w ↦ φ ((ρ / h)⁻¹ • w)) a))) ≤
        K * h ^ 2 * Real.exp (-(2 * c * φ.rIn * ρ / h)) := by
  obtain ⟨K, hK⟩ := exists_rescaledTargetNormSq_scaledCoupledEquation_vortexGraft_le hm f φ hS s hc
  have hs : 0 < √f.rOut := Real.sqrt_pos.2 f.rOut_pos
  refine ⟨K, φ.rIn * ρ / √f.rOut, by have := φ.rIn_pos; positivity, fun h hh hh₀ a ha ↦ ?_⟩
  -- Below `h₀` the dilation `R = ρ / h` is admissible: `√f.rOut < φ.rIn ρ / h`.
  have hR : √f.rOut < φ.rIn * (ρ / h) := by
    rw [lt_div_iff₀ hs] at hh₀
    rw [← mul_div_assoc, lt_div_iff₀ hh]
    linarith
  have hrOut : f.rOut < (φ.rIn * (ρ / h)) ^ 2 := by
    rw [← Real.sq_sqrt f.rOut_pos.le]
    exact pow_lt_pow_left₀ hR hs.le two_ne_zero
  refine (hK h hh (ρ / h) (div_pos hρ hh) hrOut a ha).trans_eq ?_
  rw [mul_div_assoc]
  ring_nf

end TauCeti.Vortex
