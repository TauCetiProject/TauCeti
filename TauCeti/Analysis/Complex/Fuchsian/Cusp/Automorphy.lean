/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Extension
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc
public import TauCeti.Analysis.Complex.RootsOfUnity.TwistedDescent
import TauCeti.Analysis.Complex.Periodic
import TauCeti.Analysis.Complex.RootsOfUnity.Quotient
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The weight-`k` automorphy sheaf in the width parameter at a cusp

Let `D` be a normalized cusp datum of `Γ ≤ PSL(2, ℝ)`, with scaling `σ`, generator `γ` and width
`w`, and let `s, g ∈ SL(2, ℝ)` lift `σ` and `γ`. Then `s * g * s⁻¹ = ε • [1, w; 0, 1]` for a sign
`ε = ±1`, the lower-right entry of `s * g * s⁻¹`. A function `f` holomorphic on the horodisc of
height `A ≥ 0` at the cusp which satisfies the weight-`k` transformation law
`f (g • τ) = denom g τ ^ k * f τ` there, and for which `f ∣[k] s⁻¹` is bounded at `i∞`, is a local
section of the weight-`k` automorphy sheaf at the cusp. This file computes these sections in the
width parameter. In the scaling coordinate `f ∣[k] s⁻¹` is periodic of period `w` up to the sign
`ε ^ k`, so it is periodic of period `2 * w` and is a function of the width parameter
`q₂(τ) = exp (2 * π * I * σ τ / (2 * w))` (`TauCeti.Subgroup.CuspDatum.sqrtCoordinate`), whose
square is the cusp coordinate
`q(τ) = exp (2 * π * I * σ τ / w)` (`TauCeti.Subgroup.CuspDatum.sqrtCoordinate_sq`). The local
sections are the multiples by holomorphic functions of `q` of the single frame

`automorphyFrame D s k r τ = denom s τ ^ (-k) * q₂(τ) ^ r`,

where `r ∈ {0, 1}` is fixed by `ε ^ k = (-1) ^ r`. Precisely:

* the frame is itself a local section: it is holomorphic and vanishes nowhere on `ℍ`
  (`TauCeti.Subgroup.CuspDatum.mdifferentiable_automorphyFrame`,
  `TauCeti.Subgroup.CuspDatum.automorphyFrame_ne_zero`), and satisfies the weight-`k`
  transformation law for `g` (`TauCeti.Subgroup.CuspDatum.automorphyFrame_smul`);
* every local section is the frame times a holomorphic function of `q`:
  `f τ = automorphyFrame D s k r τ * automorphyDescent D s k r f (q τ)` on the horodisc
  (`TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent`, which needs only the
  transformation law), where `automorphyDescent D s k r f` is holomorphic on the disc of
  `q`-values of the horodisc, including the cusp `q = 0`
  (`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent`), and is the unique continuous
  function with this property (`TauCeti.Subgroup.CuspDatum.eqOn_automorphyDescent`);
* the coefficient is the twisted descent through `q₂ ↦ q₂ ^ 2` of the sum
  `automorphyUntwist D s k f` of the `q₂`-expansion of `f ∣[k] s⁻¹`, which is holomorphic at the
  cusp (`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyUntwist`) and transforms by
  `(-1) ^ r` under `q₂ ↦ -q₂` (`TauCeti.Subgroup.CuspDatum.automorphyUntwist_neg`); so the order
  of the coefficient at the cusp is read off from that expansion as
  `ord₀ (automorphyUntwist D s k f) = r + ord₀ (automorphyDescent D s k r f) * 2`
  (`TauCeti.Subgroup.CuspDatum.analyticOrderAt_automorphyUntwist`).

At a regular cusp, or in even weight, `ε ^ k = 1`, so `r = 0`: the frame is `denom s τ ^ (-k)` and
the coefficient is the usual expansion of `f ∣[k] s⁻¹` in `q`. At an irregular cusp in odd weight
`ε ^ k = -1`, so `r = 1`: the `q₂`-expansion of `f ∣[k] s⁻¹` has only odd terms, the order of a
section in `q₂` is odd, and with the convention of the Diamond–Shurman errata, in which the order
at an irregular cusp is half the order in `q₂` whatever the weight, the order of a section at the
cusp is `1 / 2` plus the order of its coefficient. This half-integral correction is the
irregular-cusp contribution to the divisor of the automorphy sheaf in the odd-weight dimension
formulas of Diamond–Shurman §3.6. The analytic input is the twisted descent through `u ↦ u ^ 2`,
`TauCeti.pow_smul_descendPowTwist_pow`.

## Main declarations

* `TauCeti.Subgroup.CuspDatum.automorphyFrame`: the local frame of the weight-`k` automorphy
  sheaf at the cusp.
* `TauCeti.Subgroup.CuspDatum.automorphyUntwist`: the sum `q₂ ↦ (f ∣[k] s⁻¹)(τ)` of the
  `q₂`-expansion of a local section, with `TauCeti.Subgroup.CuspDatum.automorphyUntwist_neg`, its
  parity.
* `TauCeti.Subgroup.CuspDatum.automorphyDescent`: the coefficient of a local section with respect
  to the frame, as a function of the cusp coordinate.
* `TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent`,
  `TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent` and
  `TauCeti.Subgroup.CuspDatum.eqOn_automorphyDescent`: the local trivialization.
* `TauCeti.Subgroup.CuspDatum.analyticOrderAt_automorphyUntwist`: the order relation.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.4, 3.1 and 3.5–3.6, with the corrected irregular-cusp order
  convention of the errata to pp. 74–75.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §2.1.
-/

public section

noncomputable section

open Filter Function Matrix.ProjectiveSpecialLinearGroup Metric MulAction Set UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups ModularForm Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)} (D : Γ.CuspDatum)

/-- **The local frame of the weight-`k` automorphy sheaf at the cusp of `D`**, for a lift `s` of
the scaling and an exponent `r`: `τ ↦ denom s τ ^ (-k) * q₂(τ) ^ r` for the width parameter `q₂`.
When `ε ^ k = (-1) ^ r` for the sign `ε` of the conjugated lift `s * g * s⁻¹` of the generator, it
satisfies the weight-`k` transformation law for `g`
(`TauCeti.Subgroup.CuspDatum.automorphyFrame_smul`), and for `r < 2` every local section of
weight `k` at the cusp is the frame times a holomorphic function of the cusp coordinate
(`TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent`). -/
def automorphyFrame (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (τ : ℍ) : ℂ :=
  denom (Matrix.SpecialLinearGroup.mapGL ℝ s) τ ^ (-k) * sqrtCoordinate D τ ^ r

theorem automorphyFrame_def (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (τ : ℍ) :
    automorphyFrame D s k r τ =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ s) τ ^ (-k) * sqrtCoordinate D τ ^ r :=
  (rfl)

/-- The frame vanishes nowhere on the upper half-plane: the cusp itself is not a point of `ℍ`. -/
theorem automorphyFrame_ne_zero (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (τ : ℍ) :
    automorphyFrame D s k r τ ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (denom_ne_zero _ τ)) (pow_ne_zero _ (sqrtCoordinate_ne_zero D τ))

/-- **The frame is holomorphic** on the upper half-plane. -/
theorem mdifferentiable_automorphyFrame (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (automorphyFrame D s k r) :=
  (mdifferentiable_denom_zpow _ (-k)).mul ((mdifferentiable_sqrtCoordinate D).pow r)

variable {D} {s g : SL(2, ℝ)} {k : ℤ} {r : ℕ} {A : ℝ} {f : ℍ → ℂ}

/-- The conjugated lift `s * g * s⁻¹` of the generator lifts the translation by the width. -/
private theorem coe_conj_eq_upperRightHom (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) :
    ((s * g * s⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = upperRightHom D.width := by
  rw [← D.scaling_mul_generator_mul_inv, ← hs, ← hg]
  simp

/-- The automorphy factor of `g` relative to the frame: `denom s (g • τ) * denom g τ` is
`ε * denom s τ`, for the sign `ε` of `s * g * s⁻¹`. -/
private theorem denom_smul_mul_denom (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (τ : ℍ) :
    denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((g • τ : ℍ) : ℂ) *
        denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ =
      ((s * g * s⁻¹) 1 1 : ℝ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ s) τ := by
  have hsg : s * g = s * g * s⁻¹ * s := by group
  rw [← Matrix.SpecialLinearGroup.denom_mapGL_mul]
  conv_lhs => rw [hsg]
  rw [Matrix.SpecialLinearGroup.denom_mapGL_mul,
    TauCeti.UpperHalfPlane.denom_of_coe_eq_upperRightHom (coe_conj_eq_upperRightHom hs hg)]

/-- The sign condition, read in `ℂ`. -/
private theorem ofReal_zpow_eq (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r) :
    (((s * g * s⁻¹) 1 1 : ℝ) : ℂ) ^ k = (-1) ^ r := by
  rw [← Complex.ofReal_zpow, hk]
  push_cast
  rfl

/-- The sign `ε ^ k = (-1) ^ r` makes `ε ^ (-k)` equal to `(-1) ^ r` too. -/
private theorem zpow_neg_eq (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r) :
    (((s * g * s⁻¹) 1 1 : ℝ) : ℂ) ^ (-k) = (-1) ^ r := by
  rw [zpow_neg, ofReal_zpow_eq hk, ← inv_pow, inv_neg, inv_one]

/-- **The transformation law of the frame.** If `s` and `g` lift the scaling and the generator of
`D`, and `ε ^ k = (-1) ^ r` for the sign `ε = ±1` of `s * g * s⁻¹`, then the frame satisfies the
weight-`k` transformation law for `g` on all of `ℍ`: it is a local section of the weight-`k`
automorphy sheaf. -/
theorem automorphyFrame_smul (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (τ : ℍ) :
    automorphyFrame D s k r (g • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * automorphyFrame D s k r τ := by
  have hd := denom_smul_mul_denom hs hg τ
  have hg0 := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) τ
  have hsg : denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((g • τ : ℍ) : ℂ) =
      ((s * g * s⁻¹) 1 1 : ℝ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ s) τ /
        denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ := by
    rw [← hd, mul_div_cancel_right₀ _ hg0]
  have hq : sqrtCoordinate D (g • τ) = -sqrtCoordinate D τ := by
    rw [← pslMk_smul, hg, sqrtCoordinate_generator_smul]
  have h1 : ((-1 : ℂ) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [automorphyFrame_def, automorphyFrame_def, hsg, hq, div_zpow, mul_zpow, zpow_neg_eq hk,
    div_eq_mul_inv, ← zpow_neg, neg_neg, neg_pow]
  linear_combination (denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k *
    denom (Matrix.SpecialLinearGroup.mapGL ℝ s) τ ^ (-k) * sqrtCoordinate D τ ^ r) * h1

variable (D) in
/-- **The sum of the `q₂`-expansion of a local section** of weight `k` at the cusp of `D`: the
q-extension `q₂ ↦ (f ∣[k] s⁻¹) z`, for `q₂ = exp (2 * π * I * z / (2 * w))`, of the function
`f ∣[k] s⁻¹` in the scaling coordinate. At the width parameter of a point `τ` of the horodisc it
is `denom s τ ^ k * f τ` (`TauCeti.Subgroup.CuspDatum.automorphyUntwist_sqrtCoordinate`); it
transforms by the sign `(-1) ^ r` under `q₂ ↦ -q₂`, and its twisted descent through
`q₂ ↦ q₂ ^ 2` is `TauCeti.Subgroup.CuspDatum.automorphyDescent`. -/
def automorphyUntwist (s : SL(2, ℝ)) (k : ℤ) (f : ℍ → ℂ) : ℂ → ℂ :=
  UpperHalfPlane.cuspFunction (2 * D.width) (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹)

variable (D) in
theorem automorphyUntwist_def (s : SL(2, ℝ)) (k : ℤ) (f : ℍ → ℂ) :
    automorphyUntwist D s k f =
      UpperHalfPlane.cuspFunction (2 * D.width) (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) :=
  (rfl)

variable (D) in
/-- **The coefficient of a local section of the weight-`k` automorphy sheaf at the cusp with
respect to the frame** `TauCeti.Subgroup.CuspDatum.automorphyFrame D s k r`, as a function of the
cusp coordinate: for a local section `f` and `τ` in the horodisc,
`f τ = automorphyFrame D s k r τ * automorphyDescent D s k r f (coordinate D τ)`
(`TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent`). It is the twisted descent
`TauCeti.descendPowTwist` through `q₂ ↦ q₂ ^ 2` of
`TauCeti.Subgroup.CuspDatum.automorphyUntwist D s k f`. -/
def automorphyDescent (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (f : ℍ → ℂ) : ℂ → ℂ :=
  descendPowTwist 2 r (automorphyUntwist D s k f)

variable (D) in
theorem automorphyDescent_def (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (f : ℍ → ℂ) :
    automorphyDescent D s k r f = descendPowTwist 2 r (automorphyUntwist D s k f) :=
  (rfl)

variable (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
  (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
  (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
  (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (horodisc D A))
  (hbdd : IsBoundedAtImInfty (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹))

include hs in
/-- The point `s⁻¹ • z` lies in the horodisc of height `A` exactly when `A < z.im`. -/
private theorem inv_smul_mem_horodisc_iff {z : ℍ} : s⁻¹ • z ∈ horodisc D A ↔ A < z.im := by
  rw [mem_horodisc, ← hs, pslMk_smul, smul_inv_smul]

include hs hg hf in
/-- In the scaling coordinate, the translation by the width multiplies `f ∣[k] s⁻¹` by `ε ^ k`
above the height `A`. -/
private theorem slash_inv_vadd {z : ℍ} (hz : A < z.im) :
    (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) (D.width +ᵥ z) =
      (((s * g * s⁻¹) 1 1 : ℝ) : ℂ) ^ k * (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) z := by
  have hτ : s⁻¹ • z ∈ horodisc D A := (inv_smul_mem_horodisc_iff hs).mpr hz
  have hvadd : D.width +ᵥ z = s • g • s⁻¹ • z := by
    rw [← TauCeti.UpperHalfPlane.upperRightHom_smul, ← coe_conj_eq_upperRightHom hs hg,
      pslMk_smul, mul_smul, mul_smul]
  have hz' : z = s • s⁻¹ • z := (smul_inv_smul s z).symm
  rw [hvadd, Matrix.SpecialLinearGroup.slash_mapGL_inv_apply_smul, hf _ hτ, ← mul_assoc,
    ← mul_zpow, denom_smul_mul_denom hs hg, mul_zpow, mul_assoc,
    ← Matrix.SpecialLinearGroup.slash_mapGL_inv_apply_smul, ← hz']

include hs hg hf in
/-- Above the height `A`, `f ∣[k] s⁻¹` is periodic of period twice the width. -/
private theorem slash_inv_two_mul_vadd {z : ℍ} (hz : A < z.im) :
    (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) ((2 * D.width) +ᵥ z) =
      (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) z := by
  rw [two_mul, ← vadd_vadd, slash_inv_vadd hs hg hf (by rwa [vadd_im]), slash_inv_vadd hs hg hf hz,
    ← mul_assoc, ← mul_zpow, ← Complex.ofReal_mul,
    (TauCeti.UpperHalfPlane.entries_of_coe_eq_upperRightHom (coe_conj_eq_upperRightHom hs hg)).2,
    Complex.ofReal_one, one_zpow, one_mul]

include hs hfd in
/-- Above the height `A`, `f ∣[k] s⁻¹` is holomorphic. -/
private theorem mdifferentiableAt_slash_inv {z : ℍ} (hz : A < z.im) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) z := by
  have hτ : s⁻¹ • z ∈ horodisc D A := (inv_smul_mem_horodisc_iff hs).mpr hz
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ ↦ f (Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ • τ)) z := by
    refine MDifferentiableAt.comp z ?_ (mdifferentiable_smul (by simp) z)
    rw [Matrix.SpecialLinearGroup.mapGL_smul]
    exact (hfd _ hτ).mdifferentiableAt ((isOpen_horodisc D A).mem_nhds hτ)
  have hdet : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by simp
  rw [ModularForm.slash_def, σ_eq_refl_of_det_pos hdet]
  simp only [ContinuousAlgEquiv.refl_apply]
  exact (hcomp.mul mdifferentiableAt_const).mul (mdifferentiable_denom_zpow _ _ z)

variable (D) in
/-- The radius of the disc of cusp-coordinate values of the horodisc of height `A` is the square
of that of its width-parameter values. -/
private theorem sq_exp_radius (A : ℝ) :
    Real.exp (-2 * Real.pi * A / (2 * D.width)) ^ 2 = Real.exp (-2 * Real.pi * A / D.width) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [D.width_pos.ne']
  push_cast
  ring

include hs hg hf hfd hbdd in
/-- **The sum of the `q₂`-expansion of a local section is holomorphic** on the disc of
width-parameter values of the horodisc, including at the cusp `q₂ = 0`. -/
theorem differentiableOn_automorphyUntwist (hA : 0 ≤ A) :
    DifferentiableOn ℂ (automorphyUntwist D s k f)
      (ball 0 (Real.exp (-2 * Real.pi * A / (2 * D.width)))) := by
  rw [automorphyUntwist_def, UpperHalfPlane.cuspFunction]
  exact TauCeti.UpperHalfPlane.differentiableOn_cuspFunction_of_lt_im
    (by positivity [D.width_pos]) hA (fun z hz ↦ slash_inv_two_mul_vadd hs hg hf hz)
    (fun z hz ↦ mdifferentiableAt_slash_inv hs hfd hz) hbdd

include hs hg hf in
/-- **The sum of the `q₂`-expansion at the width parameter of a point of the horodisc** is the
untwisted value `denom s τ ^ k * f τ`. -/
theorem automorphyUntwist_sqrtCoordinate {τ : ℍ} (hτ : τ ∈ horodisc D A) :
    automorphyUntwist D s k f (sqrtCoordinate D τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ s) τ ^ k * f τ := by
  have hτ' : A < (s • τ).im := by rwa [mem_horodisc, ← hs, pslMk_smul] at hτ
  rw [automorphyUntwist_def, UpperHalfPlane.cuspFunction, sqrtCoordinate_def, ← hs, pslMk_smul,
    TauCeti.UpperHalfPlane.cuspFunction_qParam_of_lt_im (by positivity [D.width_pos])
      (fun z hz ↦ slash_inv_two_mul_vadd hs hg hf hz) hτ',
    Matrix.SpecialLinearGroup.slash_mapGL_inv_apply_smul]

include hs hg hk hf in
/-- At the width parameter of a point of the horodisc, `q₂ ↦ -q₂` multiplies the sum of the
`q₂`-expansion by `(-1) ^ r`. -/
private theorem automorphyUntwist_neg_sqrtCoordinate {τ : ℍ} (hτ : τ ∈ horodisc D A) :
    automorphyUntwist D s k f (-sqrtCoordinate D τ) =
      (-1) ^ r * automorphyUntwist D s k f (sqrtCoordinate D τ) := by
  have hw : 0 < 2 * D.width := by positivity [D.width_pos]
  have hper (z : ℍ) (hz : A < z.im) := slash_inv_two_mul_vadd hs hg hf hz
  have hz : A < (D.scaling • τ).im := (mem_horodisc D).mp hτ
  -- `-q₂` is the width parameter of the translate by the width in the scaling coordinate
  have hneg : -sqrtCoordinate D τ =
      Periodic.qParam (2 * D.width) ↑(D.width +ᵥ D.scaling • τ) := by
    have h := Periodic.qParam_add_half (h := 2 * D.width) hw.ne' ((D.scaling • τ : ℍ) : ℂ)
    have hhalf : ((2 * D.width : ℝ) : ℂ) / 2 = (D.width : ℂ) := by push_cast; ring
    rw [hhalf] at h
    rw [coe_vadd, add_comm, h, sqrtCoordinate_def]
  rw [hneg, sqrtCoordinate_def, automorphyUntwist_def, UpperHalfPlane.cuspFunction,
    TauCeti.UpperHalfPlane.cuspFunction_qParam_of_lt_im hw hper (by rwa [vadd_im] : A < _),
    TauCeti.UpperHalfPlane.cuspFunction_qParam_of_lt_im hw hper hz,
    slash_inv_vadd hs hg hf hz, ofReal_zpow_eq hk]

include hs hg hk hf hfd hbdd in
/-- **The parity of the `q₂`-expansion of a local section**: on the disc of width-parameter
values of the horodisc, `q₂ ↦ -q₂` multiplies the sum of the expansion by `(-1) ^ r`. For `r = 1`
the expansion has only odd terms. -/
theorem automorphyUntwist_neg (hA : 0 ≤ A) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (Real.exp (-2 * Real.pi * A / (2 * D.width)))) :
    automorphyUntwist D s k f (-u) = (-1) ^ r * automorphyUntwist D s k f u := by
  have hw : 0 < 2 * D.width := by positivity [D.width_pos]
  -- away from `0`, `u` is the width parameter of a point of the horodisc
  have hne {u : ℂ} (hu0 : u ≠ 0)
      (hu : ‖u‖ < Real.exp (-2 * Real.pi * A / (2 * D.width))) :
      automorphyUntwist D s k f (-u) = (-1) ^ r * automorphyUntwist D s k f u := by
    have him : A < (Periodic.invQParam (2 * D.width) u).im := by
      rwa [← Periodic.norm_qParam_lt_iff hw, Periodic.qParam_right_inv hw.ne' hu0]
    set z : ℍ := UpperHalfPlane.mk _ (hA.trans_lt him)
    have hτ : D.scaling⁻¹ • z ∈ horodisc D A := by
      rwa [mem_horodisc, smul_inv_smul, UpperHalfPlane.mk_im]
    have hqz : sqrtCoordinate D (D.scaling⁻¹ • z) = u := by
      rw [sqrtCoordinate_def, smul_inv_smul, UpperHalfPlane.coe_mk]
      exact Periodic.qParam_right_inv hw.ne' hu0
    rw [← hqz]
    exact automorphyUntwist_neg_sqrtCoordinate hs hg hk hf hτ
  rw [mem_ball_zero_iff] at hu
  rcases ne_or_eq u 0 with hu0 | rfl
  · exact hne hu0 hu
  -- at `0` both sides are continuous and agree on a punctured neighbourhood
  have hc : ContinuousAt (automorphyUntwist D s k f) 0 :=
    (differentiableOn_automorphyUntwist hs hg hf hfd hbdd hA).continuousOn.continuousAt
      (ball_mem_nhds _ (Real.exp_pos _))
  have h₁ : ContinuousAt (fun u ↦ automorphyUntwist D s k f (-u)) 0 :=
    hc.comp_of_eq continuous_neg.continuousAt neg_zero
  have heq : (fun u ↦ automorphyUntwist D s k f (-u)) =ᶠ[𝓝[≠] 0]
      fun u ↦ (-1) ^ r * automorphyUntwist D s k f u := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (Real.exp_pos _))] with v hv0 hv
    exact hne hv0 (mem_ball_zero_iff.mp hv)
  exact ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (continuousAt_const.mul hc)).mp heq).eq_of_nhds

include hs hg hk hf hfd hbdd in
/-- **The coefficient of a local section is holomorphic** on the disc of cusp-coordinate values
of the horodisc, including at the cusp `q = 0`. -/
theorem differentiableOn_automorphyDescent (hA : 0 ≤ A) (hr : r ≤ 2) :
    DifferentiableOn ℂ (automorphyDescent D s k r f)
      (ball 0 (Real.exp (-2 * Real.pi * A / D.width))) := by
  rw [← sq_exp_radius D A, ← image_pow_ball (Real.exp_pos _).le, automorphyDescent_def]
  exact differentiableOn_descendPowTwist isOpen_ball hr
    (differentiableOn_automorphyUntwist hs hg hf hfd hbdd hA)
    fun _ hu ↦ apply_rootsOfUnity_two_smul_of_apply_neg <| by
      rw [smul_eq_mul]
      exact automorphyUntwist_neg hs hg hk hf hfd hbdd hA hu

include hs hg hk hf in
/-- **The local trivialization of the weight-`k` automorphy sheaf at a cusp.** If `s` and `g`
lift the scaling and the generator of `D`, `ε ^ k = (-1) ^ r` with `r < 2` for the sign `ε` of
`s * g * s⁻¹`, and `f` satisfies the weight-`k` transformation law for `g` on the horodisc of
height `A`, then on the horodisc `f` is the frame times its coefficient, a function of the cusp
coordinate. If `f` is moreover holomorphic there and `f ∣[k] s⁻¹` is bounded at `i∞`, the
coefficient is holomorphic, including at the cusp
(`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent`). -/
theorem automorphyFrame_mul_automorphyDescent (hr : r < 2) {τ : ℍ} (hτ : τ ∈ horodisc D A) :
    automorphyFrame D s k r τ * automorphyDescent D s k r f (coordinate D τ) = f τ := by
  have h := pow_smul_descendPowTwist_pow_of_ne_zero hr (sqrtCoordinate_ne_zero D τ)
    (apply_rootsOfUnity_two_smul_of_apply_neg <| by
      rw [smul_eq_mul]
      exact automorphyUntwist_neg_sqrtCoordinate hs hg hk hf hτ)
  rw [automorphyUntwist_sqrtCoordinate hs hg hf hτ, sqrtCoordinate_sq, smul_eq_mul] at h
  rw [automorphyFrame_def, automorphyDescent_def, mul_assoc, h, ← mul_assoc,
    ← zpow_add₀ (denom_ne_zero _ _), neg_add_cancel, zpow_zero, one_mul]

include hs hg hk hf hfd hbdd in
/-- **Uniqueness of the local trivialization at a cusp.** Under the hypotheses of
`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent`, with `r < 2`, any function `G`
continuous on the disc of cusp-coordinate values of the horodisc with
`f τ = automorphyFrame D s k r τ * G (coordinate D τ)` on the horodisc is the coefficient of `f`
there. -/
theorem eqOn_automorphyDescent (hA : 0 ≤ A) (hr : r < 2) {G : ℂ → ℂ}
    (hG : ContinuousOn G (ball 0 (Real.exp (-2 * Real.pi * A / D.width))))
    (hfG : ∀ τ ∈ horodisc D A, f τ = automorphyFrame D s k r τ * G (coordinate D τ)) :
    EqOn G (automorphyDescent D s k r f) (ball 0 (Real.exp (-2 * Real.pi * A / D.width))) := by
  -- away from `0`, every value is the cusp coordinate of a point of the horodisc
  have hne {q : ℂ} (hq : ‖q‖ < Real.exp (-2 * Real.pi * A / D.width)) (hq0 : q ≠ 0) :
      G q = automorphyDescent D s k r f q := by
    have him : A < (Periodic.invQParam D.width q).im := by
      rwa [← Periodic.norm_qParam_lt_iff D.width_pos,
        Periodic.qParam_right_inv D.width_pos.ne' hq0]
    set z : ℍ := UpperHalfPlane.mk _ (hA.trans_lt him)
    have hτ : D.scaling⁻¹ • z ∈ horodisc D A := by
      rwa [mem_horodisc, smul_inv_smul, UpperHalfPlane.mk_im]
    have hqz : coordinate D (D.scaling⁻¹ • z) = q := by
      rw [coordinate_inv_smul, UpperHalfPlane.coe_mk]
      exact Periodic.qParam_right_inv D.width_pos.ne' hq0
    refine mul_left_cancel₀ (automorphyFrame_ne_zero D s k r (D.scaling⁻¹ • z)) ?_
    rw [← hqz, ← hfG _ hτ, automorphyFrame_mul_automorphyDescent hs hg hk hf hr hτ]
  intro q hq
  rw [mem_ball_zero_iff] at hq
  rcases ne_or_eq q 0 with hq0 | rfl
  · exact hne hq hq0
  -- at `0` both functions are continuous and agree on a punctured neighbourhood
  have hball := ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * Real.pi * A / D.width))
  have hD := (differentiableOn_automorphyDescent hs hg hk hf hfd hbdd hA hr.le).continuousOn
    |>.continuousAt hball
  have heq : G =ᶠ[𝓝[≠] 0] automorphyDescent D s k r f := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with v hv0 hv
    exact hne (mem_ball_zero_iff.mp hv) hv0
  exact (((hG.continuousAt hball).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hD).mp
    heq).eq_of_nhds

include hs hg hk hf hfd hbdd in
/-- **The order of the coefficient of a local section at a cusp.** Under the hypotheses of
`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent`, with `r < 2`, the order at
`q₂ = 0` of the sum of the `q₂`-expansion of `f ∣[k] s⁻¹` is `r` plus twice the order at `q = 0`
of the coefficient `automorphyDescent D s k r f`. -/
theorem analyticOrderAt_automorphyUntwist (hA : 0 ≤ A) (hr : r < 2) :
    analyticOrderAt (automorphyUntwist D s k f) 0 =
      r + analyticOrderAt (automorphyDescent D s k r f) 0 * 2 :=
  analyticOrderAt_eq_add_analyticOrderAt_descendPowTwist_mul isOpen_ball
    (mem_ball_self (Real.exp_pos _)) hr
    (differentiableOn_automorphyUntwist hs hg hf hfd hbdd hA)
    fun _ hu ↦ apply_rootsOfUnity_two_smul_of_apply_neg <| by
      rw [smul_eq_mul]
      exact automorphyUntwist_neg hs hg hk hf hfd hbdd hA hu

end TauCeti.Subgroup.CuspDatum
