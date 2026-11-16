/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Extension
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc
public import TauCeti.Analysis.Complex.RootsOfUnity.TwistedDescent
public import TauCeti.Analysis.Complex.UpperHalfPlane.AutomorphyExtension
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.Analysis.Complex.Fuchsian.Cusp.ChangeScaling
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
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
  (`TauCeti.Subgroup.CuspDatum.analyticOrderAt_automorphyUntwist`);
* in even weight `k = 2 * j` the frame is compared with the frame `(dq) ^ j` of the `j`-th power
  of the sheaf of differentials, whose weight-`k` function is
  `differentialFrame D j τ = (dq / dτ) ^ j`, a local section of weight `k`
  (`TauCeti.Subgroup.CuspDatum.differentialFrame_smul`,
  `TauCeti.Subgroup.CuspDatum.mdifferentiable_differentialFrame`): since
  `dq / dτ = (2 * π * I / w) * q / denom s τ ^ 2`, it is
  `automorphyFrame D s k 0 τ * ((2 * π * I / w) ^ j * q ^ j)`
  (`TauCeti.Subgroup.CuspDatum.differentialFrame_eq_automorphyFrame_mul`), so the transition
  function between the two frames is `q ↦ (2 * π * I / w) ^ j * q ^ j`
  (`TauCeti.Subgroup.CuspDatum.eqOn_automorphyDescent_differentialFrame`), of order `j = k / 2`
  at the cusp (`TauCeti.Subgroup.CuspDatum.analyticOrderAt_automorphyDescent_differentialFrame`).

The frames at two cusps of the same `Γ`-orbit, or at two cusp data at the same cusp, differ by
a nonzero constant after transport along `Γ`: if `γ ∈ Γ` carries the cusp of `D` to that of `D'`
and `h` lifts `γ`, then `automorphyFrame D' s' k r (h • τ)` is `denom h τ ^ k` times a nonzero
constant times `automorphyFrame D s k r τ`
(`TauCeti.Subgroup.CuspDatum.automorphyFrame_smul_of_smul_cusp_eq`). This is the transition
function between the trivializations of the automorphy sheaf in the charts at two cusp data
representing the same cusp of `X(Γ)`.

The transition functions to the chart at the cusp from any other chart are specified for
`Γ' ≤ SL(2, ℝ)` with image `Γ`, as for elliptic charts. The frame satisfies the weight-`k`
transformation law for every element of `Γ'` fixing the cusp as soon as every lift in `Γ'` of
the generator satisfies the sign condition
(`TauCeti.Subgroup.CuspDatum.automorphyFrame_smul_of_mem`), so on a precisely invariant horodisc
it is compatible with the weight-`k` action of `Γ'`
(`TauCeti.Subgroup.CuspDatum.automorphyFrame_compatible`; for a discrete `Γ` every horodisc of
height at least the width is precisely invariant,
`TauCeti.Subgroup.CuspDatum.smul_cusp_eq_of_mem_horodisc_of_smul_mem_horodisc`) and has an
automorphic extension (`Subgroup.automorphyExtension`). For a frame `F'` of another chart,
compatible with that action, the transition function is the coefficient of the automorphic
extension of `F'` with respect to the frame at the cusp:

* the coefficient of a function satisfying the transformation law for `g` on the horodisc is
  holomorphic at the cusp coordinate of every point of the horodisc at which the function is
  holomorphic (`TauCeti.Subgroup.CuspDatum.differentiableAt_automorphyDescent`), so the transition
  function is holomorphic on the overlap
  (`TauCeti.Subgroup.CuspDatum.differentiableAt_automorphyDescent_automorphyExtension`);
* the frame at the cusp times it is `F'` transported in weight `k`
  (`TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent_automorphyExtension`), and it
  vanishes nowhere `F'` does not vanish after transport
  (`TauCeti.Subgroup.CuspDatum.automorphyDescent_automorphyExtension_ne_zero`);
* the coefficients of every section in the two charts differ by it
  (`TauCeti.Subgroup.CuspDatum.automorphyDescent_eq_automorphyDescent_automorphyExtension_mul`);
  since the frame at the cusp vanishes nowhere on `ℍ`, this needs no continuity argument;
* for the chart at a second cusp, on a precisely invariant horodisc, this is the coefficient law
  `TauCeti.Subgroup.CuspDatum.automorphyDescent_eq_mul_automorphyDescent`, and the transition
  functions satisfy the cocycle law on triple overlaps
  (`TauCeti.Subgroup.CuspDatum.automorphyDescent_automorphyExtension_eq_mul`);
* the cusp `q = 0` lies only in the charts at cusps of its orbit. The exponent `r` depends only on
  that orbit (`TauCeti.Subgroup.CuspDatum.exponent_eq_of_smul_cusp_eq`), and the transition
  function between two such charts is, on the whole disc of cusp-coordinate values including
  `q = 0`, the nonzero constant of `TauCeti.Subgroup.CuspDatum.automorphyFrame_smul_of_smul_cusp_eq`
  (`TauCeti.Subgroup.CuspDatum.eqOn_automorphyDescent_automorphyExtension_automorphyFrame`).

At a regular cusp, or in even weight, `ε ^ k = 1`, so `r = 0`: the frame is `denom s τ ^ (-k)` and
the coefficient is the usual expansion of `f ∣[k] s⁻¹` in `q`. At an irregular cusp in odd weight
`ε ^ k = -1`, so `r = 1`: the `q₂`-expansion of `f ∣[k] s⁻¹` has only odd terms, the order of a
section in `q₂` is odd, and with the convention of the Diamond–Shurman errata, in which the order
at an irregular cusp is half the order in `q₂` whatever the weight, the order of a section at the
cusp is `1 / 2` plus the order of its coefficient. This half-integral correction is the
irregular-cusp contribution to the divisor of the automorphy sheaf in the odd-weight dimension
formulas of Diamond–Shurman §3.6. The analytic input is the twisted descent through `u ↦ u ^ 2`,
`TauCeti.pow_smul_descendPowTwist_pow`. In even weight the order `k / 2` of the transition
function to `(dq) ^ (k / 2)` is the cusp correction `(k / 2) * ε∞` of the even-weight dimension
formulas of Diamond–Shurman §3.5.

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
* `TauCeti.Subgroup.CuspDatum.differentialFrame`,
  `TauCeti.Subgroup.CuspDatum.differentialFrame_smul` and
  `TauCeti.Subgroup.CuspDatum.mdifferentiable_differentialFrame`: the weight-`2 * j` function of
  `(dq) ^ j`, a local section of weight `2 * j` holomorphic on all of `ℍ`.
* `TauCeti.Subgroup.CuspDatum.eqOn_automorphyDescent_differentialFrame` and
  `TauCeti.Subgroup.CuspDatum.analyticOrderAt_automorphyDescent_differentialFrame`: its
  coefficient `(2 * π * I / w) ^ j * q ^ j` with respect to the automorphy frame.
* `TauCeti.Subgroup.CuspDatum.automorphyFrame_smul_of_smul_cusp_eq`: the frames at two cusps of
  the same orbit differ by a nonzero constant after transport along `Γ`.
* `TauCeti.Subgroup.CuspDatum.differentiableAt_automorphyDescent`: holomorphy of the coefficient
  at the points of the horodisc.
* `TauCeti.Subgroup.CuspDatum.automorphyFrame_smul_of_mem` and
  `TauCeti.Subgroup.CuspDatum.automorphyFrame_compatible`: the transformation law of the frame
  for the whole cusp stabilizer in `Γ'`, and its compatibility on a precisely invariant horodisc.
* `TauCeti.Subgroup.CuspDatum.differentiableAt_automorphyDescent_automorphyExtension`,
  `TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent_automorphyExtension` and
  `TauCeti.Subgroup.CuspDatum.automorphyDescent_automorphyExtension_ne_zero`: the transition
  function from another chart.
* `TauCeti.Subgroup.CuspDatum.automorphyDescent_eq_automorphyDescent_automorphyExtension_mul`,
  `TauCeti.Subgroup.CuspDatum.automorphyDescent_eq_mul_automorphyDescent` and
  `TauCeti.Subgroup.CuspDatum.automorphyDescent_automorphyExtension_eq_mul`: the coefficients of a
  section in two charts differ by the transition function, and the cocycle law.
* `TauCeti.Subgroup.CuspDatum.exponent_eq_of_smul_cusp_eq` and
  `TauCeti.Subgroup.CuspDatum.eqOn_automorphyDescent_automorphyExtension_automorphyFrame`: the
  exponent is an invariant of the cusp orbit, and the transition function between the charts at
  two cusps of the same orbit is constant, also at the cusp.

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

section

variable {D} {s g : SL(2, ℝ)} {k : ℤ} {r : ℕ}

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

end

/-- **The sum of the `q₂`-expansion of a local section** of weight `k` at the cusp of `D`: the
q-extension `q₂ ↦ (f ∣[k] s⁻¹) z`, for `q₂ = exp (2 * π * I * z / (2 * w))`, of the function
`f ∣[k] s⁻¹` in the scaling coordinate. At the width parameter of a point `τ` of the horodisc it
is `denom s τ ^ k * f τ` (`TauCeti.Subgroup.CuspDatum.automorphyUntwist_sqrtCoordinate`); it
transforms by the sign `(-1) ^ r` under `q₂ ↦ -q₂`, and its twisted descent through
`q₂ ↦ q₂ ^ 2` is `TauCeti.Subgroup.CuspDatum.automorphyDescent`. -/
def automorphyUntwist (s : SL(2, ℝ)) (k : ℤ) (f : ℍ → ℂ) : ℂ → ℂ :=
  UpperHalfPlane.cuspFunction (2 * D.width) (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹)

theorem automorphyUntwist_def (s : SL(2, ℝ)) (k : ℤ) (f : ℍ → ℂ) :
    automorphyUntwist D s k f =
      UpperHalfPlane.cuspFunction (2 * D.width) (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) :=
  (rfl)

/-- **The coefficient of a local section of the weight-`k` automorphy sheaf at the cusp with
respect to the frame** `TauCeti.Subgroup.CuspDatum.automorphyFrame D s k r`, as a function of the
cusp coordinate: for a local section `f` and `τ` in the horodisc,
`f τ = automorphyFrame D s k r τ * automorphyDescent D s k r f (coordinate D τ)`
(`TauCeti.Subgroup.CuspDatum.automorphyFrame_mul_automorphyDescent`). It is the twisted descent
`TauCeti.descendPowTwist` through `q₂ ↦ q₂ ^ 2` of
`TauCeti.Subgroup.CuspDatum.automorphyUntwist D s k f`. -/
def automorphyDescent (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (f : ℍ → ℂ) : ℂ → ℂ :=
  descendPowTwist 2 r (automorphyUntwist D s k f)

theorem automorphyDescent_def (s : SL(2, ℝ)) (k : ℤ) (r : ℕ) (f : ℍ → ℂ) :
    automorphyDescent D s k r f = descendPowTwist 2 r (automorphyUntwist D s k f) :=
  (rfl)

section

variable {D} {s g : SL(2, ℝ)} {k : ℤ} {A : ℝ} {f : ℍ → ℂ}

/-- The point `s⁻¹ • z` lies in the horodisc of height `A` exactly when `A < z.im`. -/
private theorem inv_smul_mem_horodisc_iff (hs : (s : PSL(2, ℝ)) = D.scaling) {z : ℍ} :
    s⁻¹ • z ∈ horodisc D A ↔ A < z.im := by
  rw [mem_horodisc, ← hs, pslMk_smul, smul_inv_smul]

/-- In the scaling coordinate, the translation by the width multiplies `f ∣[k] s⁻¹` by `ε ^ k`
above the height `A`. -/
private theorem slash_inv_vadd (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    {z : ℍ} (hz : A < z.im) :
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

/-- Above the height `A`, `f ∣[k] s⁻¹` is periodic of period twice the width. -/
private theorem slash_inv_two_mul_vadd (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    {z : ℍ} (hz : A < z.im) :
    (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) ((2 * D.width) +ᵥ z) =
      (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) z := by
  rw [two_mul, ← vadd_vadd, slash_inv_vadd hs hg hf (by rwa [vadd_im]), slash_inv_vadd hs hg hf hz,
    ← mul_assoc, ← mul_zpow, ← Complex.ofReal_mul,
    (TauCeti.UpperHalfPlane.entries_of_coe_eq_upperRightHom (coe_conj_eq_upperRightHom hs hg)).2,
    Complex.ofReal_one, one_zpow, one_mul]

/-- Above the height `A`, `f ∣[k] s⁻¹` is holomorphic. -/
private theorem mdifferentiableAt_slash_inv (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (horodisc D A)) {z : ℍ} (hz : A < z.im) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) z := by
  have hτ : s⁻¹ • z ∈ horodisc D A := (inv_smul_mem_horodisc_iff hs).mpr hz
  refine MDifferentiableAt.slash ?_ k
  rw [Matrix.SpecialLinearGroup.mapGL_smul]
  exact (hfd _ hτ).mdifferentiableAt ((isOpen_horodisc D A).mem_nhds hτ)

end

/-- The radius of the disc of cusp-coordinate values of the horodisc of height `A` is the square
of that of its width-parameter values. -/
private theorem sq_exp_radius (A : ℝ) :
    Real.exp (-2 * Real.pi * A / (2 * D.width)) ^ 2 = Real.exp (-2 * Real.pi * A / D.width) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [D.width_pos.ne']
  push_cast
  ring

section

variable {D} {s g : SL(2, ℝ)} {k : ℤ} {r : ℕ} {A : ℝ} {f : ℍ → ℂ}

/-- **The sum of the `q₂`-expansion of a local section is holomorphic** on the disc of
width-parameter values of the horodisc, including at the cusp `q₂ = 0`. -/
theorem differentiableOn_automorphyUntwist (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (horodisc D A))
    (hbdd : IsBoundedAtImInfty (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹)) (hA : 0 ≤ A) :
    DifferentiableOn ℂ (automorphyUntwist D s k f)
      (ball 0 (Real.exp (-2 * Real.pi * A / (2 * D.width)))) := by
  rw [automorphyUntwist_def, UpperHalfPlane.cuspFunction]
  exact TauCeti.UpperHalfPlane.differentiableOn_cuspFunction_of_lt_im
    (by positivity [D.width_pos]) hA (fun z hz ↦ slash_inv_two_mul_vadd hs hg hf hz)
    (fun z hz ↦ mdifferentiableAt_slash_inv hs hfd hz) hbdd

/-- **The sum of the `q₂`-expansion at the width parameter of a point of the horodisc** is the
untwisted value `denom s τ ^ k * f τ`. -/
theorem automorphyUntwist_sqrtCoordinate (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    {τ : ℍ} (hτ : τ ∈ horodisc D A) :
    automorphyUntwist D s k f (sqrtCoordinate D τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ s) τ ^ k * f τ := by
  have hτ' : A < (s • τ).im := by rwa [mem_horodisc, ← hs, pslMk_smul] at hτ
  rw [automorphyUntwist_def, UpperHalfPlane.cuspFunction, sqrtCoordinate_def, ← hs, pslMk_smul,
    TauCeti.UpperHalfPlane.cuspFunction_qParam_of_lt_im (by positivity [D.width_pos])
      (fun z hz ↦ slash_inv_two_mul_vadd hs hg hf hz) hτ',
    Matrix.SpecialLinearGroup.slash_mapGL_inv_apply_smul]

/-- At the width parameter of a point of the horodisc, `q₂ ↦ -q₂` multiplies the sum of the
`q₂`-expansion by `(-1) ^ r`. -/
private theorem automorphyUntwist_neg_sqrtCoordinate (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    {τ : ℍ} (hτ : τ ∈ horodisc D A) :
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

/-- Away from `0`, on the disc of width-parameter values of the horodisc, `q₂ ↦ -q₂` multiplies
the sum of the `q₂`-expansion by `(-1) ^ r`: there `u` is the width parameter of a point of the
horodisc. -/
private theorem automorphyUntwist_neg_of_ne_zero (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hA : 0 ≤ A) {u : ℂ} (hu0 : u ≠ 0)
    (hu : ‖u‖ < Real.exp (-2 * Real.pi * A / (2 * D.width))) :
    automorphyUntwist D s k f (-u) = (-1) ^ r * automorphyUntwist D s k f u := by
  have hw : 0 < 2 * D.width := by positivity [D.width_pos]
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

/-- **The parity of the `q₂`-expansion of a local section**: on the disc of width-parameter
values of the horodisc, `q₂ ↦ -q₂` multiplies the sum of the expansion by `(-1) ^ r`. For `r = 1`
the expansion has only odd terms. -/
theorem automorphyUntwist_neg (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (horodisc D A))
    (hbdd : IsBoundedAtImInfty (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹)) (hA : 0 ≤ A) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (Real.exp (-2 * Real.pi * A / (2 * D.width)))) :
    automorphyUntwist D s k f (-u) = (-1) ^ r * automorphyUntwist D s k f u := by
  have hne {u : ℂ} (hu0 : u ≠ 0) (hu : ‖u‖ < Real.exp (-2 * Real.pi * A / (2 * D.width))) :=
    automorphyUntwist_neg_of_ne_zero hs hg hk hf hA hu0 hu
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

/-- **The coefficient of a local section is holomorphic** on the disc of cusp-coordinate values
of the horodisc, including at the cusp `q = 0`. -/
theorem differentiableOn_automorphyDescent (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (horodisc D A))
    (hbdd : IsBoundedAtImInfty (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹)) (hA : 0 ≤ A)
    (hr : r ≤ 2) :
    DifferentiableOn ℂ (automorphyDescent D s k r f)
      (ball 0 (Real.exp (-2 * Real.pi * A / D.width))) := by
  rw [← sq_exp_radius D A, ← image_pow_ball (Real.exp_pos _).le, automorphyDescent_def]
  exact differentiableOn_descendPowTwist isOpen_ball hr
    (differentiableOn_automorphyUntwist hs hg hf hfd hbdd hA)
    fun _ hu ↦ apply_rootsOfUnity_two_smul_of_apply_neg <| by
      rw [smul_eq_mul]
      exact automorphyUntwist_neg hs hg hk hf hfd hbdd hA hu

/-- **The local trivialization of the weight-`k` automorphy sheaf at a cusp.** If `s` and `g`
lift the scaling and the generator of `D`, `ε ^ k = (-1) ^ r` with `r < 2` for the sign `ε` of
`s * g * s⁻¹`, and `f` satisfies the weight-`k` transformation law for `g` on the horodisc of
height `A`, then on the horodisc `f` is the frame times its coefficient, a function of the cusp
coordinate. If `f` is moreover holomorphic there and `f ∣[k] s⁻¹` is bounded at `i∞`, the
coefficient is holomorphic, including at the cusp
(`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent`). -/
theorem automorphyFrame_mul_automorphyDescent (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hr : r < 2) {τ : ℍ} (hτ : τ ∈ horodisc D A) :
    automorphyFrame D s k r τ * automorphyDescent D s k r f (coordinate D τ) = f τ := by
  have h := pow_smul_descendPowTwist_pow_of_ne_zero hr (sqrtCoordinate_ne_zero D τ)
    (apply_rootsOfUnity_two_smul_of_apply_neg <| by
      rw [smul_eq_mul]
      exact automorphyUntwist_neg_sqrtCoordinate hs hg hk hf hτ)
  rw [automorphyUntwist_sqrtCoordinate hs hg hf hτ, sqrtCoordinate_sq, smul_eq_mul] at h
  rw [automorphyFrame_def, automorphyDescent_def, mul_assoc, h, ← mul_assoc,
    ← zpow_add₀ (denom_ne_zero _ _), neg_add_cancel, zpow_zero, one_mul]

/-- **Uniqueness of the local trivialization at a cusp.** Under the hypotheses of
`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent`, with `r < 2`, any function `G`
continuous on the disc of cusp-coordinate values of the horodisc with
`f τ = automorphyFrame D s k r τ * G (coordinate D τ)` on the horodisc is the coefficient of `f`
there. -/
theorem eqOn_automorphyDescent (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (horodisc D A))
    (hbdd : IsBoundedAtImInfty (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹)) (hA : 0 ≤ A)
    (hr : r < 2) {G : ℂ → ℂ}
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

/-- **The order of the coefficient of a local section at a cusp.** Under the hypotheses of
`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyDescent`, with `r < 2`, the order at
`q₂ = 0` of the sum of the `q₂`-expansion of `f ∣[k] s⁻¹` is `r` plus twice the order at `q = 0`
of the coefficient `automorphyDescent D s k r f`. -/
theorem analyticOrderAt_automorphyUntwist (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (horodisc D A))
    (hbdd : IsBoundedAtImInfty (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹)) (hA : 0 ≤ A)
    (hr : r < 2) :
    analyticOrderAt (automorphyUntwist D s k f) 0 =
      r + analyticOrderAt (automorphyDescent D s k r f) 0 * 2 :=
  analyticOrderAt_eq_add_analyticOrderAt_descendPowTwist_mul isOpen_ball
    (mem_ball_self (Real.exp_pos _)) hr
    (differentiableOn_automorphyUntwist hs hg hf hfd hbdd hA)
    fun _ hu ↦ apply_rootsOfUnity_two_smul_of_apply_neg <| by
      rw [smul_eq_mul]
      exact automorphyUntwist_neg hs hg hk hf hfd hbdd hA hu

end

/-! ### The powers of the differential of the cusp coordinate -/

/-- **The `j`-th power of the differential of the cusp coordinate**, as a function of weight
`2 * j` on the upper half-plane: `τ ↦ (dq / dτ) ^ j` for the cusp coordinate
`q(τ) = exp (2 * π * I * σ τ / w)`, read on `ℂ` through `UpperHalfPlane.ofComplex`. It is the
weight-`2 * j` function attached to the frame `(dq) ^ j` of the `j`-th power of the sheaf of
differentials in the chart at the cusp. It is the automorphy frame times
`(2 * π * I / w) ^ j * q ^ j`
(`TauCeti.Subgroup.CuspDatum.differentialFrame_eq_automorphyFrame_mul`), so its coefficient with
respect to the automorphy frame, the transition function between the two frames, vanishes to
order `j` at the cusp
(`TauCeti.Subgroup.CuspDatum.analyticOrderAt_automorphyDescent_differentialFrame`). -/
def differentialFrame (j : ℕ) (τ : ℍ) : ℂ :=
  deriv (fun t : ℂ ↦ coordinate D (ofComplex t)) τ ^ j

theorem differentialFrame_def (j : ℕ) (τ : ℍ) :
    differentialFrame D j τ = deriv (fun t : ℂ ↦ coordinate D (ofComplex t)) τ ^ j :=
  (rfl)

section

variable {D} {s g : SL(2, ℝ)}

/-- **The powers of the differential of the cusp coordinate in the automorphy frame.** For a lift
`s` of the scaling, `(dq / dτ) ^ j` is the automorphy frame of weight `2 * j` and exponent `0`
times `(2 * π * I / w) ^ j * q ^ j`. -/
theorem differentialFrame_eq_automorphyFrame_mul (hs : (s : PSL(2, ℝ)) = D.scaling) (j : ℕ)
    (τ : ℍ) :
    differentialFrame D j τ = automorphyFrame D s (2 * j) 0 τ *
      ((2 * Real.pi * Complex.I / D.width) ^ j * coordinate D τ ^ j) := by
  rw [differentialFrame_def, (hasDerivAt_coordinate D τ).deriv, ← hs,
    Matrix.SpecialLinearGroup.smulDeriv_coe, automorphyFrame_def]
  simp only [pow_zero, mul_one, zpow_neg, zpow_mul, zpow_ofNat, zpow_natCast]
  ring

/-- In even weight the sign of the conjugated lift `s * g * s⁻¹` of the generator disappears. -/
private theorem zpow_two_mul_conj (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (j : ℕ) :
    ((s * g * s⁻¹) 1 1 : ℝ) ^ (2 * (j : ℤ)) = (-1) ^ 0 := by
  rw [zpow_mul, zpow_two,
    (TauCeti.UpperHalfPlane.entries_of_coe_eq_upperRightHom (coe_conj_eq_upperRightHom hs hg)).2,
    one_zpow, pow_zero]

/-- **The transformation law of the powers of the differential of the cusp coordinate.** If `g`
lifts the generator of `D`, then `differentialFrame D j` satisfies the weight-`2 * j`
transformation law for `g` on all of `ℍ`: the cusp coordinate is invariant under `g`, and the
automorphy frame of weight `2 * j` and exponent `0` satisfies that law. -/
theorem differentialFrame_smul (hg : (g : PSL(2, ℝ)) = D.generator) (j : ℕ) (τ : ℍ) :
    differentialFrame D j (g • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ (2 * (j : ℤ)) * differentialFrame D j τ := by
  obtain ⟨s', hs'⟩ := QuotientGroup.mk_surjective (D.scaling : PSL(2, ℝ))
  have hq : coordinate D (g • τ) = coordinate D τ := by
    rw [← sqrtCoordinate_sq, ← sqrtCoordinate_sq, ← pslMk_smul, hg,
      sqrtCoordinate_generator_smul, neg_sq]
  rw [differentialFrame_eq_automorphyFrame_mul hs', differentialFrame_eq_automorphyFrame_mul hs',
    automorphyFrame_smul hs' hg (zpow_two_mul_conj hs' hg j), hq, mul_assoc]

end

/-- **The powers of the differential of the cusp coordinate are holomorphic** on the upper
half-plane. -/
theorem mdifferentiable_differentialFrame (j : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (differentialFrame D j) := by
  obtain ⟨s', hs'⟩ := QuotientGroup.mk_surjective (D.scaling : PSL(2, ℝ))
  rw [show differentialFrame D j = fun τ ↦ automorphyFrame D s' (2 * j) 0 τ *
      ((2 * Real.pi * Complex.I / D.width) ^ j * coordinate D τ ^ j) from
    funext (differentialFrame_eq_automorphyFrame_mul hs' j)]
  exact (mdifferentiable_automorphyFrame D s' _ _).mul
    (mdifferentiable_const.mul ((mdifferentiable_coordinate D).pow j))

section

variable {D} {s g : SL(2, ℝ)} {k : ℤ} {r : ℕ} {A : ℝ} {f : ℍ → ℂ}

/-- **The transition function from the automorphy frame to the powers of the differential at a
cusp.** For a lift `s` of the scaling, the coefficient of
`differentialFrame D j`, the weight-`2 * j` function of the frame `(dq) ^ j`, with respect to the
automorphy frame `automorphyFrame D s (2 * j) 0` is `q ↦ (2 * π * I / w) ^ j * q ^ j` on the open
unit disc. -/
theorem eqOn_automorphyDescent_differentialFrame (hs : (s : PSL(2, ℝ)) = D.scaling) (j : ℕ) :
    EqOn (automorphyDescent D s (2 * j) 0 (differentialFrame D j))
      (fun q ↦ (2 * Real.pi * Complex.I / D.width) ^ j * q ^ j) (ball 0 1) := by
  set c : ℂ := 2 * Real.pi * Complex.I / D.width
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (D.generator : PSL(2, ℝ))
  have hF (τ : ℍ) := differentialFrame_eq_automorphyFrame_mul (D := D) hs j τ
  -- in the scaling coordinate, `(dq / dτ) ^ j` is `c ^ j * q ^ j`, which is bounded
  have hslash (τ : ℍ) : (differentialFrame D j ∣[(2 * j : ℤ)]
      Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) (s • τ) = c ^ j * coordinate D τ ^ j := by
    rw [Matrix.SpecialLinearGroup.slash_mapGL_inv_apply_smul, hF, automorphyFrame_def]
    simp [c, zpow_ne_zero, denom_ne_zero]
  have hbdd : IsBoundedAtImInfty
      (differentialFrame D j ∣[(2 * j : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) := by
    refine isBoundedAtImInfty_iff.mpr ⟨‖c‖ ^ j, 0, fun τ _ ↦ ?_⟩
    rw [← smul_inv_smul s τ, hslash, norm_mul, norm_pow, norm_pow]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (norm_nonneg _) (norm_coordinate_lt_one D _).le)
  have h := eqOn_automorphyDescent hs hg (zpow_two_mul_conj hs hg j)
    (fun τ _ ↦ differentialFrame_smul hg j τ)
    (mdifferentiable_differentialFrame D j).mdifferentiableOn hbdd le_rfl two_pos
    (G := fun q ↦ c ^ j * q ^ j) (by fun_prop) fun τ _ ↦ hF τ
  rw [mul_zero, zero_div, Real.exp_zero] at h
  exact h.symm

/-- **The order of the transition function at a cusp.** The coefficient of the weight-`2 * j`
function of `(dq) ^ j` with respect to the automorphy frame vanishes to order exactly `j` at the
cusp. This is the correction `k / 2`, for `k = 2 * j`, of the divisor of the weight-`k` automorphy
sheaf at a cusp relative to the `j`-th power of the sheaf of differentials. -/
theorem analyticOrderAt_automorphyDescent_differentialFrame (hs : (s : PSL(2, ℝ)) = D.scaling)
    (j : ℕ) :
    analyticOrderAt (automorphyDescent D s (2 * j) 0 (differentialFrame D j)) 0 = j := by
  have hc : (2 * Real.pi * Complex.I / D.width : ℂ) ^ j ≠ 0 :=
    pow_ne_zero _ (div_ne_zero (by simp [Real.pi_ne_zero])
      (Complex.ofReal_ne_zero.mpr D.width_pos.ne'))
  have heq : automorphyDescent D s (2 * j) 0 (differentialFrame D j) =ᶠ[𝓝 0]
      (fun _ ↦ (2 * Real.pi * Complex.I / D.width : ℂ) ^ j) * (· - (0 : ℂ)) ^ j := by
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with q hq
    rw [eqOn_automorphyDescent_differentialFrame hs j hq]
    simp
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul analyticAt_const (by fun_prop),
    analyticAt_const.analyticOrderAt_eq_zero.mpr hc, analyticOrderAt_centeredMonomial, zero_add]

/-! ### Transport of the frame along `Γ` -/

section

variable {D' : Γ.CuspDatum} {s' h : SL(2, ℝ)} {γ : Γ}

/-- The lift `s' * h * s⁻¹` of `σ' γ σ⁻¹`. -/
private theorem coe_scaling_mul_mul_inv (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hs' : (s' : PSL(2, ℝ)) = D'.scaling) (hh : (h : PSL(2, ℝ)) = γ) :
    ((s' * h * s⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = D'.scaling * γ * D.scaling⁻¹ := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, hs', hh]

/-- If `γ` carries the cusp of `D` to that of `D'`, then `σ' γ σ⁻¹` fixes `∞`, so its lift
`s' * h * s⁻¹` is upper triangular. -/
private theorem scaling_mul_mul_inv_apply_one_zero (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hs' : (s' : PSL(2, ℝ)) = D'.scaling) (hh : (h : PSL(2, ℝ)) = γ)
    (hγ : γ • D.cusp = D'.cusp) : (s' * h * s⁻¹) 1 0 = 0 := by
  have hg : ((s' * h * s⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) • (OnePoint.infty : OnePoint ℝ) =
      OnePoint.infty := by
    rw [coe_scaling_mul_mul_inv hs hs' hh, mul_smul, mul_smul,
      inv_smul_eq_iff.mpr D.scaling_smul_cusp.symm, ← Subgroup.smul_def, hγ,
      D'.scaling_smul_cusp]
  rwa [OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hg

end

/-- **The transition function between the frames at two cusps of the same orbit is constant.**
Let `D` and `D'` be cusp data whose cusps are related by `γ ∈ Γ`, `γ • c = c'`, and let `s`, `s'`
and `h` lift their scalings `σ`, `σ'` and `γ`. Then `t = s' * h * s⁻¹` is upper triangular, and
the frame at the cusp of `D'`, read at `h • τ`, is the weight-`k` automorphy factor
`denom h τ ^ k` times the frame at the cusp of `D`, read at `τ`, times the nonzero constant
`t₁₁ ^ (-k) * exp (π * I * t₀₁ * t₁₁ / w) ^ r`, for the width `w` of `D`.

In the scaling coordinates `γ` is the affine map `x ↦ t₀₀ ^ 2 * x + t₀₀ * t₀₁`, the widths
satisfy `w' = t₀₀ ^ 2 * w`, and the width parameters satisfy
`q₂'(h • τ) = exp (π * I * t₀₁ * t₁₁ / w) * q₂(τ)`. For `γ = 1` this compares the frames of two
cusp data at the same cusp. For `D' = D`, `s' = s` and `h` a lift of the generator of `D`, the
constant is `ε ^ (-k) * (-1) ^ r` for the sign `ε` of `s * h * s⁻¹`, which is `1` exactly under
the sign condition of `TauCeti.Subgroup.CuspDatum.automorphyFrame_smul`. -/
theorem automorphyFrame_smul_of_smul_cusp_eq (hs : (s : PSL(2, ℝ)) = D.scaling)
    {D' : Γ.CuspDatum} {s' h : SL(2, ℝ)} {γ : Γ} (hs' : (s' : PSL(2, ℝ)) = D'.scaling)
    (hh : (h : PSL(2, ℝ)) = γ) (hγ : γ • D.cusp = D'.cusp) (τ : ℍ) :
    automorphyFrame D' s' k r (h • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ h) τ ^ k *
        ((((s' * h * s⁻¹) 1 1 : ℝ) : ℂ) ^ (-k) *
          Complex.exp (Real.pi * Complex.I * ((s' * h * s⁻¹) 0 1 * (s' * h * s⁻¹) 1 1) /
            D.width) ^ r) *
        automorphyFrame D s k r τ := by
  set t := s' * h * s⁻¹ with ht_def
  have ht : t 1 0 = 0 := scaling_mul_mul_inv_apply_one_zero hs hs' hh hγ
  have hdet : (t 0 0 : ℂ) * t 1 1 = 1 := by
    have h := t.det_coe
    rw [Matrix.det_fin_two, ht, mul_zero, sub_zero] at h
    exact_mod_cast h
  -- in the scaling coordinates `γ` is the affine map `x ↦ t₀₀ ^ 2 * x + t₀₀ * t₀₁`
  have hσ (x : ℍ) : ((D'.scaling • (γ : PSL(2, ℝ)) • x : ℍ) : ℂ) =
      (t 0 0 : ℂ) ^ 2 * (D.scaling • x : ℍ) + t 0 0 * t 0 1 := by
    rw [← coe_smul_of_apply_zero_one_eq_zero ht, ← UpperHalfPlane.pslMk_smul,
      coe_scaling_mul_mul_inv hs hs' hh, mul_smul, mul_smul, inv_smul_smul]
  -- hence the widths satisfy `w' = t₀₀ ^ 2 * w`, comparing `D'` with the transport of `D`
  have hw : D'.width = t 0 0 ^ 2 * D.width := by
    have hc := Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer γ.2)
    have h := TauCeti.cuspDatum_width_eq_mul (D := D.conj hc) (D' := D')
      (by rw [_root_.Subgroup.CuspDatum.conj_cusp, ← hγ, Subgroup.smul_def])
      (a := t 0 0 ^ 2) (b := t 0 0 * t 0 1) fun x ↦ by
        rw [_root_.Subgroup.CuspDatum.conj_scaling, mul_smul, Complex.ofReal_pow,
          Complex.ofReal_mul, ← hσ, smul_inv_smul]
    rwa [_root_.Subgroup.CuspDatum.conj_width] at h
  -- the automorphy factors: `denom s' (h • τ) * denom h τ = t₁₁ * denom s τ`
  have hden : denom (Matrix.SpecialLinearGroup.mapGL ℝ s') ((h • τ : ℍ) : ℂ) =
      (t 1 1 : ℂ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ s) τ /
        denom (Matrix.SpecialLinearGroup.mapGL ℝ h) τ := by
    have hts : s' * h = t * s := by rw [ht_def]; group
    rw [eq_div_iff (denom_ne_zero _ _), ← Matrix.SpecialLinearGroup.denom_mapGL_mul, hts,
      Matrix.SpecialLinearGroup.denom_mapGL_mul]
    simp [denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix, ht]
  -- the width parameters differ by the constant `exp (π * I * t₀₁ * t₁₁ / w)`
  have hq : sqrtCoordinate D' (h • τ) =
      Complex.exp (Real.pi * Complex.I * (t 0 1 * t 1 1) / D.width) * sqrtCoordinate D τ := by
    have hw0 : (D.width : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr D.width_pos.ne'
    have ha : (t 0 0 : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    rw [sqrtCoordinate_def, sqrtCoordinate_def, ← UpperHalfPlane.pslMk_smul, hh, hσ, hw,
      Periodic.qParam, Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    linear_combination (-(t 0 1 : ℂ)) * hdet
  rw [automorphyFrame_def, automorphyFrame_def, hq, hden, div_eq_mul_inv, mul_zpow, mul_zpow,
    inv_zpow', neg_neg, mul_pow]
  ring

/-! ### Holomorphy of the coefficient at the points of `ℍ` -/

/-- **The sum of the `q₂`-expansion is holomorphic at the width parameter of every point of the
horodisc at which the section is holomorphic.** Unlike
`TauCeti.Subgroup.CuspDatum.differentiableOn_automorphyUntwist`, this needs neither holomorphy on
the whole horodisc nor boundedness at `i∞`, so it applies to the automorphic extension of a local
section of another chart (`Subgroup.automorphyExtension`), holomorphic only on the saturation of
that chart. -/
theorem differentiableAt_automorphyUntwist_sqrtCoordinate (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    {τ : ℍ} (hτ : τ ∈ horodisc D A) (hfτ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ) :
    DifferentiableAt ℂ (automorphyUntwist D s k f) (sqrtCoordinate D τ) := by
  have hτ' : A < (s • τ).im := by rwa [mem_horodisc, ← hs, pslMk_smul] at hτ
  rw [automorphyUntwist_def, UpperHalfPlane.cuspFunction, sqrtCoordinate_def, ← hs, pslMk_smul]
  exact TauCeti.UpperHalfPlane.differentiableAt_cuspFunction_qParam_of_lt_im
    (by positivity [D.width_pos]) (fun z hz ↦ slash_inv_two_mul_vadd hs hg hf hz) hτ'
    (MDifferentiableAt.slash (by rwa [Matrix.SpecialLinearGroup.mapGL_smul, inv_smul_smul]) k)

/-- **The coefficient of a section is holomorphic at the cusp coordinate of every point of the
horodisc at which the section is holomorphic.** If `f` satisfies the weight-`k` transformation
law for `g` on the horodisc of height `A` and is holomorphic at a point `τ` of it, then
`automorphyDescent D s k r f` is holomorphic at the cusp coordinate of `τ`. -/
theorem differentiableAt_automorphyDescent (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hg : (g : PSL(2, ℝ)) = D.generator) (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hf : ∀ τ ∈ horodisc D A, f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hr : r ≤ 2) {τ : ℍ} (hτ : τ ∈ horodisc D A) (hfτ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ) :
    DifferentiableAt ℂ (automorphyDescent D s k r f) (coordinate D τ) := by
  -- the horodisc of height `max A 0` contains `τ` and lies in that of height `A`
  have hτ₀ : τ ∈ horodisc D (max A 0) :=
    (mem_horodisc D).mpr (max_lt ((mem_horodisc D).mp hτ) (D.scaling • τ).im_pos)
  have hf₀ : ∀ σ ∈ horodisc D (max A 0),
      f (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * f σ := fun σ hσ ↦
    hf σ ((mem_horodisc D).mpr ((le_max_left A 0).trans_lt ((mem_horodisc D).mp hσ)))
  -- near the width parameter of `τ`, every point is the width parameter of a point of the horodisc
  have hnhds : ∀ᶠ v in 𝓝 (sqrtCoordinate D τ),
      v ≠ 0 ∧ ‖v‖ < Real.exp (-2 * Real.pi * max A 0 / (2 * D.width)) :=
    (isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)).mem_nhds
      ⟨sqrtCoordinate_ne_zero D τ, (norm_sqrtCoordinate_lt_iff_mem_horodisc D _ τ).mpr hτ₀⟩
  rw [← sqrtCoordinate_sq, automorphyDescent_def]
  refine differentiableAt_descendPowTwist_pow hr ?_ (sqrtCoordinate_ne_zero D τ)
    (differentiableAt_automorphyUntwist_sqrtCoordinate hs hg hf hτ hfτ)
  filter_upwards [hnhds] with v hv
  exact apply_rootsOfUnity_two_smul_of_apply_neg <| by
    rw [smul_eq_mul]
    exact automorphyUntwist_neg_of_ne_zero hs hg hk hf₀ (le_max_right A 0) hv.1 hv.2

/-! ### Transition functions between the trivializations of two charts -/

section

variable {Γ' : _root_.Subgroup SL(2, ℝ)}

/-- **The transformation law of the frame for the whole cusp stabilizer.** Let `Γ' ≤ SL(2, ℝ)`
have image `Γ` in `PSL(2, ℝ)`, and let every lift `g ∈ Γ'` of the generator of `D` satisfy the
sign condition `ε ^ k = (-1) ^ r` of `TauCeti.Subgroup.CuspDatum.automorphyFrame_smul`. Then the
frame satisfies the weight-`k` transformation law for every element of `Γ'` fixing the cusp.

If `-1 ∈ Γ'` and `k` is odd, the two lifts `g` and `-g` of the generator have opposite signs, so the
hypothesis fails for every `r`: there is no frame, in accordance with the vanishing of the
weight-`k` forms by parity. -/
theorem automorphyFrame_smul_of_mem
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ)
    (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hk : ∀ g ∈ Γ', (g : PSL(2, ℝ)) = D.generator → ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {h : SL(2, ℝ)} (hh : h ∈ Γ') (hhc : (h : PSL(2, ℝ)) • D.cusp = D.cusp) (τ : ℍ) :
    automorphyFrame D s k r (h • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ h) τ ^ k * automorphyFrame D s k r τ := by
  -- a lift of the generator in `Γ'`
  obtain ⟨g₀, hg₀, hg₀gen⟩ := _root_.Subgroup.mem_map.mp (hΓ.symm ▸ D.generator.2 :
    (D.generator : PSL(2, ℝ)) ∈ Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))))
  -- the image of `h` is a power of the generator
  have hstab : (⟨(h : PSL(2, ℝ)), hΓ ▸ _root_.Subgroup.mem_map_of_mem _ hh⟩ : Γ) ∈
      stabilizer Γ D.cusp :=
    mem_stabilizer_iff.mpr hhc
  obtain ⟨n, hn⟩ := D.mem_stabilizer_iff.mp hstab
  have hn' : (h : PSL(2, ℝ)) = (D.generator : PSL(2, ℝ)) ^ n := by
    rw [← _root_.Subgroup.coe_zpow, hn]
  have hlift (g : SL(2, ℝ)) (hg : g ∈ Γ') (hgen : (g : PSL(2, ℝ)) = D.generator) :
      g ∈ TauCeti.UpperHalfPlane.transformationLawSubgroup k (automorphyFrame D s k r) :=
    TauCeti.UpperHalfPlane.mem_transformationLawSubgroup.mpr
      (automorphyFrame_smul hs hgen (hk g hg hgen))
  -- `h = h₁ * g₀ ^ (n - 1)` with `h₁ = h * g₀ ^ (1 - n)` another lift of the generator
  have hh₁ : ((h * g₀ ^ (1 - n) : SL(2, ℝ)) : PSL(2, ℝ)) = D.generator := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hn', ← QuotientGroup.mk'_apply, hg₀gen,
      ← zpow_add, add_sub_cancel, zpow_one]
  have hmem : h ∈ TauCeti.UpperHalfPlane.transformationLawSubgroup k (automorphyFrame D s k r) := by
    have hdecomp : h = h * g₀ ^ (1 - n) * g₀ ^ (n - 1) := by group
    rw [hdecomp]
    exact mul_mem (hlift _ (mul_mem hh (zpow_mem hg₀ _)) hh₁)
      (zpow_mem (hlift g₀ hg₀ hg₀gen) _)
  exact TauCeti.UpperHalfPlane.mem_transformationLawSubgroup.mp hmem τ

/-- **The frame is compatible on a precisely invariant horodisc.** Under the hypotheses of
`TauCeti.Subgroup.CuspDatum.automorphyFrame_smul_of_mem`, if the horodisc of height `A` is
precisely invariant under `Γ'`, in that an element of `Γ'` moving one of its points into it fixes
the cusp, then the frame is compatible with the weight-`k` action of `Γ'` on it, so that it has an
automorphic extension (`Subgroup.automorphyExtension`) and the transition-function lemmas apply to
it. For a discrete `Γ` and `A` at least the width the horodisc is precisely invariant
(`TauCeti.Subgroup.CuspDatum.smul_cusp_eq_of_mem_horodisc_of_smul_mem_horodisc`). -/
theorem automorphyFrame_compatible
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ)
    (hs : (s : PSL(2, ℝ)) = D.scaling)
    (hk : ∀ g ∈ Γ', (g : PSL(2, ℝ)) = D.generator → ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hprec : ∀ g ∈ Γ', ∀ σ ∈ horodisc D A, g • σ ∈ horodisc D A →
      (g : PSL(2, ℝ)) • D.cusp = D.cusp) :
    ∀ g ∈ Γ', ∀ σ ∈ horodisc D A, g • σ ∈ horodisc D A →
      automorphyFrame D s k r (g • σ) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * automorphyFrame D s k r σ :=
  fun g hg σ hσ hgσ ↦ automorphyFrame_smul_of_mem hΓ hs hk hg (hprec g hg σ hσ hgσ) σ

end

/-- **The transition function is holomorphic.** Let `F'` be a function on an open set `U'`,
holomorphic there and compatible with the weight-`k` action of `Γ'` (for instance the frame of
another chart). The coefficient with respect to the frame at the cusp of its automorphic extension
`Subgroup.automorphyExtension Γ' U' k F'` is the transition function from the trivialization of
the chart of `F'` to that at the cusp; it is holomorphic at the cusp coordinate of every point `τ`
moved into `U'` by an element of `Γ'`, that is, on the overlap of the two charts. -/
theorem differentiableAt_automorphyDescent_automorphyExtension
    (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {Γ' : _root_.Subgroup SL(2, ℝ)} {U' : Set ℍ} {F' : ℍ → ℂ} (hgΓ : g ∈ Γ')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hr : r ≤ 2) (hU' : IsOpen U') (hF'd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F' U') {τ : ℍ}
    {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • τ ∈ U') :
    DifferentiableAt ℂ (automorphyDescent D s k r (Γ'.automorphyExtension U' k F'))
      (coordinate D τ) :=
  differentiableAt_automorphyDescent hs hg hk (A := 0)
    (fun σ _ ↦ _root_.Subgroup.automorphyExtension_smul hF' hgΓ σ) hr
    ((mem_horodisc D).mpr (D.scaling • τ).im_pos)
    ((_root_.Subgroup.mdifferentiableOn_automorphyExtension hF' hU' hF'd).mdifferentiableAt
      (hU'.smul_left.mem_nhds
        (_root_.Subgroup.mem_smul_set_iff_exists_smul_mem.mpr ⟨h, hh, hτ⟩)))

/-- **The defining identity of the transition function.** Let `F'` be a function on `U'`
compatible with the weight-`k` action of `Γ'`, let `r < 2`, and let `h ∈ Γ'` move `τ` into `U'`.
Then the frame at the cusp at `τ` times the transition function at the cusp coordinate of `τ` is
the function `F'` at `h • τ`, transported back to `τ` in weight `k`. -/
theorem automorphyFrame_mul_automorphyDescent_automorphyExtension
    (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {Γ' : _root_.Subgroup SL(2, ℝ)} {U' : Set ℍ} {F' : ℍ → ℂ} (hgΓ : g ∈ Γ')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hr : r < 2) {τ : ℍ} {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • τ ∈ U') :
    automorphyFrame D s k r τ *
        automorphyDescent D s k r (Γ'.automorphyExtension U' k F') (coordinate D τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ h) τ ^ (-k) * F' (h • τ) := by
  rw [automorphyFrame_mul_automorphyDescent hs hg hk (A := 0)
    (fun σ _ ↦ _root_.Subgroup.automorphyExtension_smul hF' hgΓ σ) hr
    ((mem_horodisc D).mpr (D.scaling • τ).im_pos),
    _root_.Subgroup.automorphyExtension_eq hF' hh hτ]

/-- **The transition function does not vanish** at the cusp coordinate of a point `τ` of the
overlap with `F' (h • τ) ≠ 0`. -/
theorem automorphyDescent_automorphyExtension_ne_zero
    (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {Γ' : _root_.Subgroup SL(2, ℝ)} {U' : Set ℍ} {F' : ℍ → ℂ} (hgΓ : g ∈ Γ')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hr : r < 2) {τ : ℍ} {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • τ ∈ U')
    (hF'0 : F' (h • τ) ≠ 0) :
    automorphyDescent D s k r (Γ'.automorphyExtension U' k F') (coordinate D τ) ≠ 0 := by
  have h0 := automorphyFrame_mul_automorphyDescent_automorphyExtension hs hg hk hgΓ hF' hr hh hτ
  exact right_ne_zero_of_mul (h0 ▸ mul_ne_zero (zpow_ne_zero _ (denom_ne_zero _ _)) hF'0)

/-- **The transformation law of the coefficients of a section between the chart at the cusp and
another chart.** Let `f` satisfy the weight-`k` transformation law for `Γ'`, and let the second
chart have frame `F'` on `U'`, compatible with the weight-`k` action of `Γ'`. If `h ∈ Γ'` moves
`τ` into `U'` and `c` is the coefficient of `f` at `h • τ` in the second chart,
`F' (h • τ) * c = f (h • τ)`, then the coefficient of `f` at the cusp coordinate of `τ` is the
transition function times `c`. Since the frame at the cusp vanishes nowhere on `ℍ`, no holomorphy
is needed; the second chart may be a chart at a cusp
(`TauCeti.Subgroup.CuspDatum.automorphyDescent_eq_mul_automorphyDescent`) or at an elliptic or
free point. -/
theorem automorphyDescent_eq_automorphyDescent_automorphyExtension_mul
    (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {Γ' : _root_.Subgroup SL(2, ℝ)} {U' : Set ℍ} {F' : ℍ → ℂ} (hgΓ : g ∈ Γ')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hr : r < 2)
    (hlaw : ∀ g ∈ Γ', ∀ σ : ℍ, f (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * f σ)
    {τ : ℍ} {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • τ ∈ U') {c : ℂ}
    (hc : F' (h • τ) * c = f (h • τ)) :
    automorphyDescent D s k r f (coordinate D τ) =
      automorphyDescent D s k r (Γ'.automorphyExtension U' k F') (coordinate D τ) * c := by
  refine mul_left_cancel₀ (automorphyFrame_ne_zero D s k r τ) ?_
  rw [automorphyFrame_mul_automorphyDescent hs hg hk (A := 0) (fun σ _ ↦ hlaw g hgΓ σ) hr
    ((mem_horodisc D).mpr (D.scaling • τ).im_pos), ← mul_assoc,
    automorphyFrame_mul_automorphyDescent_automorphyExtension hs hg hk hgΓ hF' hr hh hτ,
    mul_assoc, hc, hlaw h hh τ, ← mul_assoc, zpow_neg_mul_zpow_self k (denom_ne_zero _ _),
    one_mul]

/-- **The transformation law of the coefficients of a section between the charts at two cusps.**
Let `Γ'` have image `Γ`, let `D'` be a second cusp datum with lift `s'` of its scaling, exponent
`r' < 2` and the sign condition for every lift in `Γ'` of its generator, and let the horodisc of
height `A'` at its cusp be precisely invariant: an element of `Γ'` moving one of its points into it
fixes the cusp; for a discrete `Γ` and `A'` at least the width this is
`TauCeti.Subgroup.CuspDatum.smul_cusp_eq_of_mem_horodisc_of_smul_mem_horodisc`. If `f` satisfies
the weight-`k` transformation law for `Γ'` and `h ∈ Γ'` moves `τ` into the horodisc, then the
coefficient of `f` at the cusp of `D` is the transition function, the coefficient of the
automorphic extension of the frame at the cusp of `D'`, times the coefficient of `f` at the cusp of
`D'` at `h • τ`. -/
theorem automorphyDescent_eq_mul_automorphyDescent
    (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {Γ' : _root_.Subgroup SL(2, ℝ)} (hgΓ : g ∈ Γ')
    {D' : Γ.CuspDatum} {s' : SL(2, ℝ)} {r' : ℕ} {A' : ℝ}
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ)
    (hr : r < 2)
    (hs' : (s' : PSL(2, ℝ)) = D'.scaling)
    (hk' : ∀ g ∈ Γ', (g : PSL(2, ℝ)) = D'.generator → ((s' * g * s'⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r')
    (hr' : r' < 2)
    (hprec' : ∀ g ∈ Γ', ∀ σ ∈ horodisc D' A', g • σ ∈ horodisc D' A' →
      (g : PSL(2, ℝ)) • D'.cusp = D'.cusp)
    (hlaw : ∀ g ∈ Γ', ∀ σ : ℍ, f (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * f σ)
    {τ : ℍ} {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • τ ∈ horodisc D' A') :
    automorphyDescent D s k r f (coordinate D τ) =
      automorphyDescent D s k r (Γ'.automorphyExtension (horodisc D' A') k
          (automorphyFrame D' s' k r')) (coordinate D τ) *
        automorphyDescent D' s' k r' f (coordinate D' (h • τ)) := by
  obtain ⟨g', hg'Γ, hg'⟩ := _root_.Subgroup.mem_map.mp (hΓ.symm ▸ D'.generator.2 :
    (D'.generator : PSL(2, ℝ)) ∈ Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))))
  refine automorphyDescent_eq_automorphyDescent_automorphyExtension_mul hs hg hk hgΓ
    (automorphyFrame_compatible hΓ hs' hk' hprec') hr hlaw hh hτ ?_
  exact automorphyFrame_mul_automorphyDescent hs' hg' (hk' g' hg'Γ hg') (A := 0)
    (fun σ _ ↦ hlaw g' hg'Γ σ) hr' ((mem_horodisc D').mpr (D'.scaling • h • τ).im_pos)

/-- **The cocycle law of the transition functions at two cusps.** Let `D'` be as in
`TauCeti.Subgroup.CuspDatum.automorphyDescent_eq_mul_automorphyDescent`, and let `F''` be a
function on `U''` compatible with the weight-`k` action of `Γ'`, the frame of a third chart. The
transition function from the chart of `F''` to that at the cusp of `D` is the product of the
transition function from the chart at the cusp of `D'` to that at the cusp of `D` and the
transition function from the chart of `F''` to that at the cusp of `D'`, read at the corresponding
point `h • τ`. -/
theorem automorphyDescent_automorphyExtension_eq_mul
    (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {Γ' : _root_.Subgroup SL(2, ℝ)} (hgΓ : g ∈ Γ')
    {D' : Γ.CuspDatum} {s' : SL(2, ℝ)} {r' : ℕ} {A' : ℝ}
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ)
    (hr : r < 2)
    (hs' : (s' : PSL(2, ℝ)) = D'.scaling)
    (hk' : ∀ g ∈ Γ', (g : PSL(2, ℝ)) = D'.generator → ((s' * g * s'⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r')
    (hr' : r' < 2)
    (hprec' : ∀ g ∈ Γ', ∀ σ ∈ horodisc D' A', g • σ ∈ horodisc D' A' →
      (g : PSL(2, ℝ)) • D'.cusp = D'.cusp)
    {U'' : Set ℍ} {F'' : ℍ → ℂ}
    (hF'' : ∀ g ∈ Γ', ∀ σ ∈ U'', g • σ ∈ U'' →
      F'' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F'' σ)
    {τ : ℍ} {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • τ ∈ horodisc D' A') :
    automorphyDescent D s k r (Γ'.automorphyExtension U'' k F'') (coordinate D τ) =
      automorphyDescent D s k r (Γ'.automorphyExtension (horodisc D' A') k
          (automorphyFrame D' s' k r')) (coordinate D τ) *
        automorphyDescent D' s' k r' (Γ'.automorphyExtension U'' k F'') (coordinate D' (h • τ)) :=
  automorphyDescent_eq_mul_automorphyDescent hs hg hk hgΓ hΓ hr hs' hk' hr' hprec'
    (fun _ hg σ ↦ _root_.Subgroup.automorphyExtension_smul hF'' hg σ) hh hτ

/-- **The exponent depends only on the cusp orbit.** Let `D'` be a cusp datum whose cusp is the
image `γ • c` of the cusp of `D` under `γ ∈ Γ`, with a lift `h ∈ Γ'` of `γ`, let `s'` lift its
scaling, and let `r' < 2` satisfy the sign condition for every lift in `Γ'` of its generator.
Then `r = r'`: the conjugate `h * g * h⁻¹ ∈ Γ'` lifts the generator of `D'`, and its conjugate by
`s'` has the same lower-right entry `ε` as `s * g * s⁻¹`, since `s' * h * s⁻¹` is upper
triangular. -/
theorem exponent_eq_of_smul_cusp_eq
    (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {Γ' : _root_.Subgroup SL(2, ℝ)} (hgΓ : g ∈ Γ')
    {D' : Γ.CuspDatum} {s' : SL(2, ℝ)} {r' : ℕ}
    (hr : r < 2) (hs' : (s' : PSL(2, ℝ)) = D'.scaling)
    (hk' : ∀ g ∈ Γ', (g : PSL(2, ℝ)) = D'.generator → ((s' * g * s'⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r')
    (hr' : r' < 2) {h : SL(2, ℝ)} {γ : Γ} (hhΓ : h ∈ Γ') (hh : (h : PSL(2, ℝ)) = γ)
    (hγ : γ • D.cusp = D'.cusp) : r = r' := by
  -- `h * g * h⁻¹` lifts the generator of `D'`
  have hc := Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer γ.2)
  have hgen : ((h * g * h⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = D'.generator := by
    rw [← cuspDatum_generator_eq (D := D.conj hc)
      (by rw [_root_.Subgroup.CuspDatum.conj_cusp, ← hγ, Subgroup.smul_def]),
      _root_.Subgroup.CuspDatum.coe_conj_generator, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hh, hg]
  -- conjugation by the upper triangular `t = s' * h * s⁻¹` keeps the lower-right entry
  have ht : (s' * h * s⁻¹) 1 0 = 0 := scaling_mul_mul_inv_apply_one_zero hs hs' hh hγ
  have hM : (s * g * s⁻¹) 1 0 = 0 :=
    (TauCeti.UpperHalfPlane.entries_of_coe_eq_upperRightHom (coe_conj_eq_upperRightHom hs hg)).1
  have hdet : (s' * h * s⁻¹) 0 0 * (s' * h * s⁻¹) 1 1 = 1 := by
    have h := (s' * h * s⁻¹).det_coe
    rwa [Matrix.det_fin_two, ht, mul_zero, sub_zero] at h
  have hconj : s' * (h * g * h⁻¹) * s'⁻¹ = (s' * h * s⁻¹) * (s * g * s⁻¹) * (s' * h * s⁻¹)⁻¹ := by
    group
  have hentry : (s' * (h * g * h⁻¹) * s'⁻¹) 1 1 = (s * g * s⁻¹) 1 1 := by
    rw [hconj, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, ht, hM]
    linear_combination (s * g * s⁻¹) 1 1 * hdet
  have hsign := hk' _ (Γ'.mul_mem (Γ'.mul_mem hhΓ hgΓ) (Γ'.inv_mem hhΓ)) hgen
  rw [hentry, hk] at hsign
  interval_cases r <;> interval_cases r' <;> first | rfl | norm_num at hsign

/-- **The transition function between the charts at two cusp data of the same cusp orbit is
constant, also at the cusp.** Let `D'` be as in
`TauCeti.Subgroup.CuspDatum.automorphyDescent_eq_mul_automorphyDescent`, and let `h ∈ Γ'` carry
the cusp of `D` to that of `D'` and the horodisc of height `A ≥ 0` at the cusp of `D` into the
horodisc of height `A'` at the cusp of `D'`. Then `r = r'`
(`TauCeti.Subgroup.CuspDatum.exponent_eq_of_smul_cusp_eq`), and on the disc of cusp-coordinate
values of the horodisc of height `A`, including the cusp `q = 0`, the transition function from the
chart at the cusp of `D'` to that at the cusp of `D` is the nonzero constant of
`TauCeti.Subgroup.CuspDatum.automorphyFrame_smul_of_smul_cusp_eq`. In particular it is holomorphic
and vanishes nowhere there, and for `D' = D`, `s' = s` and `h = 1` the constant is `1`. -/
theorem eqOn_automorphyDescent_automorphyExtension_automorphyFrame
    (hs : (s : PSL(2, ℝ)) = D.scaling) (hg : (g : PSL(2, ℝ)) = D.generator)
    (hk : ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    {Γ' : _root_.Subgroup SL(2, ℝ)} (hgΓ : g ∈ Γ')
    {D' : Γ.CuspDatum} {s' : SL(2, ℝ)} {r' : ℕ} {A' : ℝ}
    (hΓ : Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))) = Γ) (hr : r < 2)
    (hs' : (s' : PSL(2, ℝ)) = D'.scaling)
    (hk' : ∀ g ∈ Γ', (g : PSL(2, ℝ)) = D'.generator → ((s' * g * s'⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r')
    (hr' : r' < 2)
    (hprec' : ∀ g ∈ Γ', ∀ σ ∈ horodisc D' A', g • σ ∈ horodisc D' A' →
      (g : PSL(2, ℝ)) • D'.cusp = D'.cusp)
    (hA : 0 ≤ A) {h : SL(2, ℝ)} (hh : h ∈ Γ') (hhc : (h : PSL(2, ℝ)) • D.cusp = D'.cusp)
    (hhA : ∀ τ ∈ horodisc D A, h • τ ∈ horodisc D' A') :
    EqOn (automorphyDescent D s k r
        (Γ'.automorphyExtension (horodisc D' A') k (automorphyFrame D' s' k r')))
      (fun _ ↦ (((s' * h * s⁻¹) 1 1 : ℝ) : ℂ) ^ (-k) *
        Complex.exp (Real.pi * Complex.I * ((s' * h * s⁻¹) 0 1 * (s' * h * s⁻¹) 1 1) /
          D.width) ^ r)
      (ball 0 (Real.exp (-2 * Real.pi * A / D.width))) := by
  set γ : Γ := ⟨h, hΓ ▸ _root_.Subgroup.mem_map_of_mem _ hh⟩
  have hγ : γ • D.cusp = D'.cusp := by
    rw [Subgroup.smul_def]
    exact hhc
  obtain rfl := exponent_eq_of_smul_cusp_eq hs hg hk hgΓ hr hs' hk' hr' hh rfl hγ
  set C : ℂ := (((s' * h * s⁻¹) 1 1 : ℝ) : ℂ) ^ (-k) *
    Complex.exp (Real.pi * Complex.I * ((s' * h * s⁻¹) 0 1 * (s' * h * s⁻¹) 1 1) / D.width) ^ r
  set E := Γ'.automorphyExtension (horodisc D' A') k (automorphyFrame D' s' k r) with hE
  have hF' := automorphyFrame_compatible hΓ hs' hk' hprec'
  -- on the horodisc of height `A`, the extension is the frame at the cusp of `D` times `C`
  have hEF (τ : ℍ) (hτ : τ ∈ horodisc D A) : E τ = automorphyFrame D s k r τ * C := by
    rw [hE, _root_.Subgroup.automorphyExtension_eq hF' hh (hhA τ hτ),
      automorphyFrame_smul_of_smul_cusp_eq hs hs' rfl hγ τ, ← mul_assoc, ← mul_assoc,
      zpow_neg_mul_zpow_self k (denom_ne_zero _ _), one_mul]
    exact mul_comm _ _
  have hEd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) E (horodisc D A) :=
    (_root_.Subgroup.mdifferentiableOn_automorphyExtension hF' (isOpen_horodisc D' A')
      (mdifferentiable_automorphyFrame D' s' k r).mdifferentiableOn).mono fun τ hτ ↦
        _root_.Subgroup.mem_smul_set_iff_exists_smul_mem.mpr ⟨h, hh, hhA τ hτ⟩
  -- in the scaling coordinate the extension is `q₂ ^ r * C` above height `A`, so it is bounded
  have hbdd : IsBoundedAtImInfty (E ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) := by
    refine isBoundedAtImInfty_iff.mpr ⟨‖C‖, A + 1, fun z hz ↦ ?_⟩
    have hz' : s⁻¹ • z ∈ horodisc D A := (inv_smul_mem_horodisc_iff hs).mpr (by linarith)
    have hq : ‖sqrtCoordinate D (s⁻¹ • z)‖ < 1 := by
      simpa using (norm_sqrtCoordinate_lt_iff_mem_horodisc D 0 _).mpr
        ((mem_horodisc D).mpr (D.scaling • s⁻¹ • z).im_pos)
    have hden {a : ℂ} (ha : a ≠ 0) (b : ℂ) : a ^ k * (a ^ (-k) * b * C) = b * C := by
      linear_combination b * C * zpow_neg_mul_zpow_self k ha
    rw [← smul_inv_smul s z, Matrix.SpecialLinearGroup.slash_mapGL_inv_apply_smul, hEF _ hz',
      automorphyFrame_def, hden (denom_ne_zero _ _), norm_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  exact (eqOn_automorphyDescent hs hg hk
    (fun τ _ ↦ _root_.Subgroup.automorphyExtension_smul hF' hgΓ τ) hEd hbdd hA hr
    continuousOn_const hEF).symm

end

end TauCeti.Subgroup.CuspDatum
