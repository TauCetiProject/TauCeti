/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Schrodinger.Stationary
import TauCeti.Analysis.PDE.Vortex.Decay
import TauCeti.Analysis.PDE.Vortex.ScalarEquation
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Smooth framed vortices have representatives in every `A_m^s`

The framed degree-`m` plane vortex fields form the affine Sobolev space
`A_m^s = x_ref + H^s(ℂ; ℝ⁴)` (`TauCeti.Vortex.framedFieldSpace`), centered at a smooth reference
field equal to `(-i m dθ, (z / |z|)^m)` outside a disc. This file shows that every smooth framed
vortex has a representative in this model: a smooth plane vortex with the degree-`m` end framing
`α (z / |z|)^(-m) → 1` has a smooth framed gauge transform lying in `A_m^s` for every `s`
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`). With
`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`, which shows that two representatives
in `A_m^k` related by a smooth gauge differ by an element of the Sobolev gauge group `G_(k+1)`,
this compares the smooth framed vortex orbits with the vortex orbits of the Sobolev model.

The framed gauge is the one making the section `|α|` times the winding phase outside a disc
(`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`); such a gauge can have a phase with
a `1 / |z|` tail, which is not itself in any `H^s`. For a vortex normalized in this way, put
`ℓ = log |α|²`. Outside a disc where the reference field has its exact tail, the section of `x`
is `exp (ℓ / 2)` times the reference section, and the holomorphicity rows of the vortex equations
of `x` and of `x_ref` then determine the connection:

`x - x_ref = (-∂₂ℓ / 2, ∂₁ℓ / 2, (exp (ℓ / 2) - 1) x_ref)` (section coordinates of `x_ref`).

So it suffices to show that `ℓ`, cut off away from the zeros of `α`, lies in every `H^s`. The
truncation `u = χ ℓ` is smooth, nonpositive and decays exponentially
(`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`), hence is square integrable, and
`Δ ℓ = (exp ℓ - 1) / 4` (`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`) gives
`Δu = (exp u - 1) / 4 + h` with `h` smooth and compactly supported. Then `-Δu + u` is square
integrable, so `u ∈ H²` by elliptic regularity of `-Δ + 1`
(`TauCeti.mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq` with `P = 1`),
and whenever
`u ∈ H^s` with `s ≥ 2`, the function `exp u - 1` lies in `H^s`
(`TemperedDistribution.exp_mul_sub_one_mem_realSobolevFunctions`), so `-Δu + u ∈ H^s` and
`u ∈ H^(s+2)` (`TauCeti.Vortex.mem_realSobolevFunctions_of_laplacian_eq`). The derivatives of `u`
and the products of `exp (u / 2) - 1` with the reference coordinates, which have bounded
derivatives, then lie in every `H^s`.

## Main results

All in the namespace `TauCeti.Vortex`:

* `mem_realSobolevFunctions_of_laplacian_eq`: a `C²` square-integrable solution `u`, bounded
  above, of `Δu = c (exp u - 1) + h` with `h` smooth and compactly supported lies in every `H^s(ℂ)`.
* `mem_framedFieldSpace_of_sectionValue_eq`: a smooth vortex with `|α| → 1` whose section is `|α|`
  times the winding phase outside a compact set lies in `A_m^s` for every `s`.
* `exists_framedGaugeGroup_smul_mem_framedFieldSpace`: every smooth framed vortex has a smooth
  framed gauge transform in `A_m^s` for every `s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric Module TemperedDistribution
open scoped ContDiff Topology Laplacian Distributions

/-! ### Regularity of square-integrable solutions of `Δu = c (exp u - 1) + h` -/

/-- `|exp t - 1| ≤ exp (max M 0) |t|` for `t ≤ M`. -/
private theorem abs_exp_sub_one_le_mul_abs {t M : ℝ} (ht : t ≤ M) :
    |Real.exp t - 1| ≤ Real.exp (max M 0) * |t| := by
  have h1 : 1 ≤ Real.exp (max M 0) := Real.one_le_exp (le_max_right _ _)
  rcases le_total t 0 with h | h
  · have := Real.add_one_le_exp t
    have := Real.exp_le_one_iff.2 h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos h]
    nlinarith [abs_nonneg t]
  · -- `exp t - 1 ≤ t exp t`, from `1 - t ≤ exp (-t)`.
    have h2 := Real.add_one_le_exp (-t)
    have h3 : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h4 : Real.exp t ≤ Real.exp (max M 0) := Real.exp_le_exp.2 (ht.trans (le_max_left _ _))
    rw [abs_of_nonneg (by linarith [Real.add_one_le_exp t]), abs_of_nonneg h]
    nlinarith [Real.exp_pos t]

/-- **Sobolev regularity for the scalar vortex equation.** Let `u` be a `C²` square-integrable
function on the plane, bounded above, with `Δu = c (exp u - 1) + h` for a smooth compactly
supported `h`. Then `u` lies in every Sobolev space `H^s(ℂ)`. For `c = 1 / 4` and `h = 0` this is
the equation `Δ log |α|² = (|α|² - 1) / 4` of a plane vortex off the zeros of its section. -/
theorem mem_realSobolevFunctions_of_laplacian_eq {u h : ℂ → ℝ} {c M : ℝ} (hu : ContDiff ℝ 2 u)
    (hu2 : MemLp u 2 volume) (huM : ∀ z, u z ≤ M) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (heq : ∀ z, Δ u z = c * (Real.exp (u z) - 1) + h z) (s : ℝ) :
    u ∈ realSobolevFunctions ℂ s 2 := by
  set g : ℂ → ℝ := fun z ↦ u z - c * (Real.exp (u z) - 1) - h z with hg
  -- `-Δu + u = g` holds weakly, by Green's identity.
  have hweak (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
      ∫ z, u z * (-Δ (φ : ℂ → ℝ) z + φ z) = ∫ z, g z * φ z := by
    have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
    have hΔφ2 : MemLp (Δ φ) 2 volume :=
      (hφ.of_le (by simp)).continuous_laplacian.memLp_of_hasCompactSupport hφc.laplacian
    have hgreen : ∫ z, Δ φ z * u z = ∫ z, φ z * Δ u z := by
      -- The bundled test function has `φ` as its underlying function.
      exact hu.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian
        (μ := volume) (⟨φ, hφ, hφc, by simp⟩ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ))
    have hi₁ : Integrable (fun z ↦ Δ φ z * u z) volume := hΔφ2.integrable_mul hu2
    have hi₂ : Integrable (fun z ↦ u z * φ z) volume := hu2.integrable_mul hφ2
    have hi₃ : Integrable (fun z ↦ φ z * Δ u z) volume :=
      (hφ.continuous.mul hu.continuous_laplacian).integrable_of_hasCompactSupport
        hφc.mul_right
    calc ∫ z, u z * (-Δ φ z + φ z) = ∫ z, (-(Δ φ z * u z) + u z * φ z) := by
          congr 1
          ext z
          ring
      _ = -(∫ z, φ z * Δ u z) + ∫ z, u z * φ z := by
          rw [integral_add (f := fun z ↦ -(Δ φ z * u z)) hi₁.neg hi₂, integral_neg, hgreen]
      _ = ∫ z, (-(φ z * Δ u z) + u z * φ z) := by
          rw [integral_add (f := fun z ↦ -(φ z * Δ u z)) hi₃.neg hi₂, integral_neg]
      _ = ∫ z, g z * φ z := by
          congr 1
          ext z
          simp only [hg, heq z]
          ring
  -- The right side `g` is square integrable.
  have hh2 : MemLp h 2 volume := hh.continuous.memLp_of_hasCompactSupport hhc
  have hg2 : MemLp g 2 volume := by
    have hgc : Continuous g := by
      have := hu.continuous
      have := hh.continuous
      fun_prop
    refine MemLp.of_le ((hu2.norm.const_mul (1 + |c| * Real.exp (max M 0))).add hh2.norm)
      hgc.aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    have hK : 0 ≤ (1 + |c| * Real.exp (max M 0)) * ‖u z‖ + ‖h z‖ := by positivity
    rw [Pi.add_apply, Real.norm_of_nonneg hK]
    simp only [hg, Real.norm_eq_abs]
    have he := abs_exp_sub_one_le_mul_abs (huM z)
    have t₁ := abs_sub (u z) (c * (Real.exp (u z) - 1))
    have t₂ := abs_sub (u z - c * (Real.exp (u z) - 1)) (h z)
    rw [abs_mul] at t₁
    nlinarith [abs_nonneg c, abs_nonneg (u z)]
  -- The weak equation is that of the Schrödinger operator `-Δ + P` with `P = 1`.
  have hweak₁ (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
      ∫ z, u z * (-Δ (φ : ℂ → ℝ) z + (fun _ ↦ (1 : ℝ)) z * φ z) = ∫ z, g z * φ z := by
    simpa only [one_mul] using hweak φ hφ hφc
  -- Bootstrap: `u ∈ H^(2n+2)` for every `n`.
  have hboot (n : ℕ) : u ∈ realSobolevFunctions ℂ (2 * n + 2) 2 := by
    induction n with
    | zero =>
      simpa using mem_realSobolevFunctions_two_of_integral_mul_neg_laplacian_add_mul_eq
        (memLp_top_const 1) hu2 hg2 hweak₁
    | succ n ih =>
      have hs : finrank ℝ ℂ < 2 * (2 * (n : ℝ) + 2) :=
        finrank_real_complex_lt_two_mul (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      have hE := exp_mul_sub_one_mem_realSobolevFunctions hs ih 1
      have hgs : g ∈ realSobolevFunctions ℂ (2 * n + 2) 2 := by
        have := sub_mem (sub_mem ih (Submodule.smul_mem _ c hE))
          (mem_realSobolevFunctions_of_hasCompactSupport hh hhc (2 * n + 2))
        convert this using 1
        ext z
        simp [hg]
      have := mem_realSobolevFunctions_add_two_of_integral_mul_neg_laplacian_add_mul_eq ih
        (by simpa only [one_mul] using ih) hgs hweak₁
      convert this using 2
      push_cast
      ring
  exact realSobolevFunctions_mono (by norm_num) (by norm_num)
    (show s ≤ 2 * (⌈s⌉₊ : ℝ) + 2 by linarith [Nat.le_ceil s, (Nat.ceil s).cast_nonneg (α := ℝ)])
    (hboot ⌈s⌉₊)

/-! ### The field outside a disc in terms of `log |α|²` -/

/-- The field `(-∂₂u / 2, ∂₁u / 2, (exp (u / 2) - 1) x_ref)` built from a real function `u`, where
the section coordinates of the reference field `x_ref` multiply `exp (u / 2) - 1`. Outside a disc,
the difference between an end-normalized vortex and the reference field is this field for
`u = log |α|²` (`sub_referenceField_eq_logField`). -/
private def logField (f : ContDiffBump (0 : ℝ)) (m : ℕ) (u : ℂ → ℝ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[-fderiv ℝ u z I / 2, fderiv ℝ u z 1 / 2, (Real.exp (u z / 2) - 1) * referenceField f m z 2,
    (Real.exp (u z / 2) - 1) * referenceField f m z 3]

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-- **The difference from the reference field in terms of `log |α|²`.** At a point `z` outside the
cutoff disc of the reference field, where `x` solves the vortex equation, `α(z) ≠ 0`, and the
section of `x` is `|α|` times the winding phase near `z`, the difference `x - x_ref` is
`(-∂₂ℓ / 2, ∂₁ℓ / 2, (|α| - 1) x_ref)` with `ℓ = log |α|²`: the section is `|α|` times the reference
section, and the holomorphicity rows of the two vortex equations determine the connection. -/
private theorem sub_referenceField_eq_logField (f : ContDiffBump (0 : ℝ)) (hx : ContDiff ℝ ∞ x)
    {z : ℂ} (hsol : equation x z = 0) (hz : f.rOut < ‖z‖ ^ 2)
    (hpos : 0 < x z 2 ^ 2 + x z 3 ^ 2)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) :
    x z - referenceField f m z =
      logField f m (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z := by
  set ℓ : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) with hℓ
  set r := referenceField f m
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hri (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ r w i :=
    contDiff_euclidean.1 (contDiff_referenceField f m) i
  -- Near `z`, the section of `x` is `exp (ℓ / 2)` times the reference section.
  have hnear : ∀ᶠ w in 𝓝 z, x w 2 = Real.exp (ℓ w / 2) * r w 2 ∧
      x w 3 = Real.exp (ℓ w / 2) * r w 3 := by
    have hcont : Continuous fun w ↦ x w 2 ^ 2 + x w 3 ^ 2 :=
      ((hxi 2).continuous.pow 2).add ((hxi 3).continuous.pow 2)
    filter_upwards [hphase, (isOpen_lt continuous_const (continuous_norm.pow 2)).mem_nhds hz,
      (isOpen_lt continuous_const hcont).mem_nhds hpos] with w hw hwz hwpos
    have hw₀ := ne_zero_of_rOut_le_norm_sq f hwz.le
    -- `‖α‖ = exp (log ‖α‖² / 2)`.
    have hnorm : ‖sectionValue x w‖ = Real.exp (ℓ w / 2) := by
      have h4 : 0 < 4 * (x w 2 ^ 2 + x w 3 ^ 2) := by positivity
      have hsq : Real.exp (ℓ w / 2) ^ 2 = ‖sectionValue x w‖ ^ 2 := by
        rw [sq, ← Real.exp_add, add_halves, hℓ, Real.exp_log h4, sq_norm_sectionValue]
      rw [← Real.sqrt_sq (norm_nonneg (sectionValue x w)), ← hsq, Real.sqrt_sq (Real.exp_pos _).le]
    have hsec : sectionValue x w = Real.exp (ℓ w / 2) * sectionValue r w := by
      rw [hw, hnorm, sectionValue_referenceField, referenceSection_eq_phase f m hwz.le,
        coe_windingPhase m hw₀]
    have h2 := congrArg Complex.re hsec
    have h3 := congrArg Complex.im hsec
    simp only [sectionValue_apply, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re,
      I_im, re_ofNat, im_ofNat] at h2 h3
    constructor <;> linarith
  -- Derivatives of the section coordinates of `x` at `z`.
  have hℓd : DifferentiableAt ℝ ℓ z := by
    refine DifferentiableAt.log ?_ (mul_pos four_pos hpos).ne'
    exact (((hxi 2).differentiable (by simp) z).pow 2 |>.add
      (((hxi 3).differentiable (by simp) z).pow 2)).const_mul 4
  have hE : HasFDerivAt (fun w ↦ Real.exp (ℓ w / 2))
      (Real.exp (ℓ z / 2) • ((2 : ℝ)⁻¹ • fderiv ℝ ℓ z)) z := by
    have := (hℓd.hasFDerivAt.const_smul (2 : ℝ)⁻¹).exp
    simpa only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul] using this
  have hd (i : Fin 4) (hi : (fun w ↦ x w i) =ᶠ[𝓝 z] fun w ↦ Real.exp (ℓ w / 2) * r w i) (v : ℂ) :
      fderiv ℝ (fun w ↦ x w i) z v = Real.exp (ℓ z / 2) * (fderiv ℝ ℓ z v / 2) * r z i +
        Real.exp (ℓ z / 2) * fderiv ℝ (fun w ↦ r w i) z v := by
    rw [hi.fderiv_eq, (hE.fun_mul ((hri i).differentiable (by simp) z).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hd2 := hd 2 (hnear.mono fun _ h ↦ h.1)
  have hd3 := hd 3 (hnear.mono fun _ h ↦ h.2)
  have hx2 := hnear.self_of_nhds.1
  have hx3 := hnear.self_of_nhds.2
  -- The holomorphicity rows of the vortex equations of `x` and of `x_ref` at `z`.
  have hr := equation_referenceField_eq_zero f m hz
  have ex1 := equation_apply_one x z
  have ex2 := equation_apply_two x z
  have er1 := equation_apply_one r z
  have er2 := equation_apply_two r z
  rw [hsol, PiLp.zero_apply] at ex1 ex2
  rw [hr, PiLp.zero_apply] at er1 er2
  rw [hd2, hd3, hx2, hx3] at ex1 ex2
  -- The reference section has modulus one at `z`.
  have hPQ : r z 2 ^ 2 + r z 3 ^ 2 = 1 / 4 := by
    have h := sq_norm_sectionValue r z
    rw [sectionValue_referenceField, referenceSection_eq_phase f m hz.le,
      ← coe_windingPhase m (ne_zero_of_rOut_le_norm_sq f hz.le), Circle.norm_coe] at h
    linarith
  -- Dividing the rows of `x` by `exp (ℓ z / 2) > 0` and subtracting those of `x_ref`.
  set σ := Real.exp (ℓ z / 2)
  have hσ : σ ≠ 0 := (Real.exp_pos _).ne'
  have e1 : fderiv ℝ ℓ z 1 / 2 * r z 2 - fderiv ℝ ℓ z I / 2 * r z 3 - (x z 0 - r z 0) * r z 3 -
      (x z 1 - r z 1) * r z 2 = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left hσ
    linear_combination ex1.symm + σ * er1
  have e2 : fderiv ℝ ℓ z 1 / 2 * r z 3 + fderiv ℝ ℓ z I / 2 * r z 2 + (x z 0 - r z 0) * r z 2 -
      (x z 1 - r z 1) * r z 3 = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left hσ
    linear_combination ex2.symm + σ * er2
  have h0 : x z 0 - r z 0 = -fderiv ℝ ℓ z I / 2 := by
    linear_combination (-4 * r z 3) * e1 + (4 * r z 2) * e2 -
      4 * (x z 0 - r z 0 + fderiv ℝ ℓ z I / 2) * hPQ
  have h1 : x z 1 - r z 1 = fderiv ℝ ℓ z 1 / 2 := by
    linear_combination (-4 * r z 2) * e1 - (4 * r z 3) * e2 -
      4 * (x z 1 - r z 1 - fderiv ℝ ℓ z 1 / 2) * hPQ
  ext i
  fin_cases i <;> simp [logField, ← h0, ← h1, hx2, hx3, r, σ] <;> ring

/-- `|log s| ≤ 2 (1 - s)` for `1 / 2 ≤ s ≤ 1`. -/
private theorem abs_log_le_two_mul_one_sub {s : ℝ} (h₁ : 1 / 2 ≤ s) (h₂ : s ≤ 1) :
    |Real.log s| ≤ 2 * (1 - s) := by
  have hs : 0 < s := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv] at hlog
  rw [abs_of_nonpos (Real.log_nonpos hs.le h₂)]
  have : s⁻¹ - 1 ≤ 2 * (1 - s) := by
    rw [inv_eq_one_div, div_sub_one hs.ne', div_le_iff₀ hs]
    nlinarith
  linarith

/-- The smooth field `logField f m u` lies in every Sobolev space when `u` does. -/
private theorem logField_mem_sobolevFields (f : ContDiffBump (0 : ℝ)) (m : ℕ) {u : ℂ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hus : ∀ s, u ∈ realSobolevFunctions ℂ s 2) (s : ℝ) :
    logField f m u ∈ sobolevFields s := by
  set n := max 2 ⌈s⌉₊
  have hn : s ≤ n := (Nat.le_ceil s).trans (by exact_mod_cast le_max_right _ _)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_max_left _ _
  refine sobolevFields_mono hn (mem_sobolevFields.2 fun i ↦ ?_)
  -- The connection coordinates are derivatives of `u / 2`.
  have hd (v : ℂ) : (fun z ↦ fderiv ℝ u z v) ∈ realSobolevFunctions ℂ n 2 :=
    fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (by linarith)
      (hu.of_le (by simp)) (hus (n + 1)) v
  -- The section coordinates are products of `exp (u / 2) - 1` with reference coordinates.
  have he : (fun z ↦ Real.exp (2⁻¹ * u z) - 1) ∈ realSobolevFunctions ℂ n 2 :=
    exp_mul_sub_one_mem_realSobolevFunctions
      (finrank_real_complex_lt_two_mul (by linarith)) (hus n) 2⁻¹
  have hr (j : Fin 4) : (fun z ↦ referenceField f m z j * (Real.exp (2⁻¹ * u z) - 1)) ∈
      realSobolevFunctions ℂ (n : ℕ) 2 :=
    mul_mem_realSobolevFunctions_of_bounded_derivatives (by norm_num) (by norm_num) n
      (contDiff_euclidean.1 (contDiff_referenceField f m) j)
      (fun k _ ↦ exists_norm_iteratedFDeriv_referenceField_apply_le f m j k) he
  fin_cases i
  · convert Submodule.smul_mem _ (-2⁻¹ : ℝ) (hd I) using 1
    ext z
    simp [logField]
    ring
  · convert Submodule.smul_mem _ (2⁻¹ : ℝ) (hd 1) using 1
    ext z
    simp [logField]
    ring
  · simpa [logField, div_eq_inv_mul, mul_comm] using hr 2
  · simpa [logField, div_eq_inv_mul, mul_comm] using hr 3

/-- **End-normalized vortices lie in every `A_m^s`.** Let `x` be a smooth plane vortex with
`|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m` outside a compact
set. Then `x - x_ref` lies in every Sobolev space `H^s(ℂ; ℝ⁴)`, that is, `x ∈ A_m^s` for every
`s`. -/
theorem mem_framedFieldSpace_of_sectionValue_eq (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) (s : ℝ) : x ∈ framedFieldSpace f m s := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  set ℓ : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) with hℓ
  have hle (z : ℂ) := normSq_le_one_of_tendsto ((hxi 0).differentiable (by simp))
    ((hxi 1).differentiable (by simp)) ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol
    hlim z
  -- Outside a disc of radius `R`, the section is normalized, `|α|² ≥ 1 / 2`, and the reference
  -- field has its exact tail.
  have hev : ∀ᶠ z in cocompact ℂ,
      (sectionValue x z = ‖sectionValue x z‖ * windingPhase m z ∧
        1 / 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) ∧ f.rOut < ‖z‖ ^ 2 := by
    refine (hphase.and (hlim.eventually (le_mem_nhds (by norm_num)))).and ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (max 1 f.rOut)] with z hz
    have h1 : 1 < ‖z‖ := (le_max_left _ _).trans_lt hz
    have h2 : f.rOut < ‖z‖ := (le_max_right _ _).trans_lt hz
    nlinarith
  obtain ⟨R₀, -, hR₀⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hev)
  set R := max R₀ 0
  have hR (z : ℂ) (hz : R < ‖z‖) := hR₀ ((le_max_left _ _).trans hz.le : R₀ ≤ ‖z‖)
  have hRnhds {z : ℂ} (hz : R < ‖z‖) : ∀ᶠ w in 𝓝 z, R < ‖w‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  have hpos {z : ℂ} (hz : R < ‖z‖) : 0 < x z 2 ^ 2 + x z 3 ^ 2 := by linarith [(hR z hz).1.2]
  -- The cutoff `χ = 1 - b` vanishes on the disc of radius `R + 1` and is one outside `R + 2`.
  set b : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  set u : ℂ → ℝ := fun z ↦ (1 - b z) * ℓ z with hu_def
  have hu_in {z : ℂ} (hz : ‖z‖ < R + 1) : u =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    simp [hu_def, b.one_of_mem_closedBall (by simpa using hw.le)]
  have hu_out {z : ℂ} (hz : R + 2 < ‖z‖) : u =ᶠ[𝓝 z] ℓ := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    simp [hu_def, b.zero_of_le_dist (by simpa using hw.le)]
  have hℓ_at {z : ℂ} (hz : R < ‖z‖) : ContDiffAt ℝ ∞ ℓ z :=
    ((((hxi 2).pow 2).add ((hxi 3).pow 2)).const_smul (4 : ℝ)).contDiffAt.log
      (by simpa using (mul_pos four_pos (hpos hz)).ne')
  have hu : ContDiff ℝ ∞ u := by
    refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    rcases lt_or_ge ‖z‖ (R + 1) with hz | hz
    · exact contDiffAt_const.congr_of_eventuallyEq (hu_in hz)
    · exact (contDiffAt_const.sub b.contDiff.contDiffAt).mul (hℓ_at (by linarith))
  -- `u ≤ 0`, and `u` decays exponentially, so it is square integrable.
  have hu0 (z : ℂ) : u z ≤ 0 := by
    rcases lt_or_ge ‖z‖ (R + 1) with hz | -
    · simp [Filter.EventuallyEq.eq_of_nhds (hu_in hz)]
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith [b.le_one (x := z)])
        (Real.log_nonpos (by positivity) (hle z))
  have hu2 : MemLp u 2 volume := by
    obtain ⟨K, hK⟩ := exists_one_sub_normSq_le_mul_exp ((hxi 0).differentiable (by simp))
      ((hxi 1).differentiable (by simp)) ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol
      hlim (c := 1 / 4) (by norm_num)
    obtain ⟨K', hK'⟩ := exists_forall_le_mul_exp_of_eventually_le hu.continuous.abs
      (c := 1 / 4) (K := 2 * K) <| by
        filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
        have hb₀ := b.nonneg (x := z)
        have hb₁ := b.le_one (x := z)
        calc |u z| = (1 - b z) * |ℓ z| := by
              rw [hu_def, abs_mul, abs_of_nonneg (by linarith)]
          _ ≤ 1 * (2 * (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2))) := by
              gcongr
              · linarith
              · exact abs_log_le_two_mul_one_sub (hR z hz).1.2 (hle z)
          _ ≤ 2 * K * Real.exp (-(1 / 4 * ‖z‖)) := by linarith [hK z]
    have hg : MemLp (fun z : ℂ ↦ K' * Real.exp (-(1 / 4 * ‖z‖))) 2 volume := by
      refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
      refine ((integrable_exp_neg_mul_norm volume (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        (K' ^ 2)).congr (ae_of_all _ fun z ↦ ?_)
      simp only [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    refine hg.of_le hu.continuous.aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hK' z).trans (le_abs_self _)
  -- `Δu = (exp u - 1) / 4 + h` with `h` smooth and supported in the disc of radius `R + 2`.
  set h : ℂ → ℝ := fun z ↦ Δ u z - (Real.exp (u z) - 1) / 4 with hh_def
  have hh : ContDiff ℝ ∞ h :=
    (hu.laplacian (by simp)).sub ((Real.contDiff_exp.comp hu).sub contDiff_const |>.div_const 4)
  have hhc : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 2)) fun z hz ↦ ?_
    have hz' : R + 2 < ‖z‖ := by simpa using hz
    have hRz : R < ‖z‖ := by linarith
    have hΔ := laplacian_log_normSq_of_equation_eq_zero
      ((hxi 0).differentiable (by simp) z) ((hxi 1).differentiable (by simp) z)
      ((hxi 2).contDiffAt.of_le (by simp)) ((hxi 3).contDiffAt.of_le (by simp))
      (hpos hRz).ne' (Eventually.of_forall hsol)
    simp only [hh_def]
    rw [(InnerProductSpace.laplacian_congr_nhds (hu_out hz')).eq_of_nhds,
      (hu_out hz').eq_of_nhds, hℓ, hΔ, Real.exp_log (mul_pos four_pos (hpos hRz))]
    ring
  have hus := mem_realSobolevFunctions_of_laplacian_eq (hu.of_le (by simp)) hu2 hu0 hh hhc
    (c := 1 / 4) fun z ↦ by rw [hh_def]; ring
  -- `x - x_ref` agrees with `logField f m u` outside the disc of radius `R + 2`.
  have hY := logField_mem_sobolevFields f m hu hus
  have hYc : ContDiff ℝ ∞ (logField f m u) := by
    have hdu (v : ℂ) : ContDiff ℝ ∞ fun z ↦ fderiv ℝ u z v :=
      (hu.fderiv_right (by simp)).clm_apply contDiff_const
    have hr (j : Fin 4) := contDiff_euclidean.1 (contDiff_referenceField f m) j
    have he : ContDiff ℝ ∞ fun z ↦ Real.exp (u z / 2) - 1 :=
      (Real.contDiff_exp.comp (hu.div_const 2)).sub contDiff_const
    refine contDiff_euclidean.2 fun i ↦ ?_
    fin_cases i
    · simpa [logField] using ((hdu I).neg.div_const 2)
    · simpa [logField] using ((hdu 1).div_const 2)
    · simpa [logField] using he.mul (hr 2)
    · simpa [logField] using he.mul (hr 3)
  have hD : x - referenceField f m - logField f m u ∈ sobolevFields s := by
    refine mem_sobolevFields_of_hasCompactSupport
      ((hx.sub (contDiff_referenceField f m)).sub hYc) ?_ s
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 2)) fun z hz ↦ ?_
    have hz' : R + 2 < ‖z‖ := by simpa using hz
    have hRz : R < ‖z‖ := by linarith
    have hlog : logField f m u z = logField f m ℓ z := by
      simp only [logField, (hu_out hz').fderiv_eq, (hu_out hz').eq_of_nhds]
    rw [hlog,
      sub_referenceField_eq_logField f hx (hsol z) (hR z hRz).2 (hpos hRz)
        ((hRnhds hRz).mono fun w hw ↦ (hR w hw).1.1), sub_self]
  rw [mem_framedFieldSpace]
  simpa using add_mem (hY s) hD

/-- **Every smooth framed vortex has a representative in every `A_m^s`.** A smooth plane vortex
with the degree-`m` end framing `α (z / |z|)^(-m) → 1` has a smooth framed gauge transform lying in
the affine field space `A_m^s` for every `s`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (f : ContDiffBump (0 : ℝ)) : ∃ u : framedGaugeGroup, ∀ s, u • x ∈ framedFieldSpace f m s := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  have huc := ((mem_framedGaugeGroup _).1 u.property).1
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_gaugeTransform_eq_zero_iff ((huc.of_le (by norm_cast)).contDiffAt)
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  have hlim : Tendsto (fun z ↦ 4 * ((u • x) z 2 ^ 2 + (u • x) z 3 ^ 2)) (cocompact ℂ) (𝓝 1) := by
    refine (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe).congr fun z ↦ ?_
    rw [← sq_norm_sectionValue, ← sq_norm_sectionValue, framedGaugeGroup_smul,
      sectionValue_gaugeTransform, norm_mul, Circle.norm_coe, one_mul]
  exact ⟨u, mem_framedFieldSpace_of_sectionValue_eq (contDiff_gaugeTransform huc hx) hsol' hlim
    hu f⟩

end TauCeti.Vortex
