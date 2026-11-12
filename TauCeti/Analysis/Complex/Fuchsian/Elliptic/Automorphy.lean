/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Linearizing
public import TauCeti.Analysis.Complex.RootsOfUnity.TwistedDescent
public import TauCeti.Analysis.Complex.UpperHalfPlane.AutomorphyExtension
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.Algebra.GroupWithZero.Units.Basic

/-!
# The weight-`k` automorphy sheaf in a local linearizing coordinate

Let `Γ ≤ PSL(2, ℝ)`, let `z ∈ ℍ` have finite stabilizer of order `m`, and let `Γ' ≤ SL(2, ℝ)`
contain lifts of the elements of `Γ`. A function `f` holomorphic on the invariant disc of radius
`ε` about `z` which satisfies the weight-`k` transformation law
`f (g • τ) = denom g τ ^ k * f τ` for the elements `g ∈ Γ'` fixing `z` is a local section of the
weight-`k` automorphy sheaf on the invariant disc modulo the stabilizer of `z`. When the disc is
precisely invariant (for instance when `Γ` is discrete and `ε` is small), this quotient is a
neighbourhood of the orbit of `z` in `Γ \ ℍ`, and these are the local sections there of the
weight-`k` automorphy sheaf on `Γ \ ℍ`. This file computes these sections in the chart given by a
local linearizing coordinate `ψ`, with local quotient coordinate `w = u ^ m` for the coordinate
`u` of `ψ`: they are the multiples of the single frame

`automorphyFrame ψ k r τ = (τ - conj z) ^ (-k) * u ^ r`,

where `0 ≤ r < m` is fixed by `λ ^ (2 * r + k) = 1` for the automorphy factors `λ = denom g z` of
the elements of `Γ'` fixing `z`. Precisely:

* the frame is itself a local section: it is holomorphic
  (`Subgroup.LinearizingCoordinate.mdifferentiableOn_automorphyFrame`), it satisfies the weight-`k`
  transformation law for the stabilizer (`Subgroup.LinearizingCoordinate.automorphyFrame_smul`),
  hence so do its multiples by functions of `w`, which is invariant
  (`Subgroup.LinearizingCoordinate.quotientCoordinate_smul`); it vanishes only at `z`, and there
  only for `r ≠ 0` (`Subgroup.LinearizingCoordinate.automorphyFrame_eq_zero_iff`);
* every local section is the frame times a holomorphic function of the quotient coordinate:
  `f τ = automorphyFrame ψ k r τ * automorphyDescent ψ k r f w`
  (`Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent`), where
  `automorphyDescent ψ k r f` is holomorphic on the set of quotient-coordinate values
  (`Subgroup.LinearizingCoordinate.differentiableOn_automorphyDescent`) and is the unique
  continuous function with this property
  (`Subgroup.LinearizingCoordinate.eqOn_automorphyDescent`);
* the order in `w` of the coefficient is read off from the order in `u` of the untwisted section
  `automorphyUntwist ψ k f`, the function `u ↦ (τ - conj z) ^ k * f τ` of the coordinate `u` of
  `τ`, as `ord₀ (automorphyUntwist ψ k f) = r + ord₀ (automorphyDescent ψ k r f) * m`
  (`Subgroup.LinearizingCoordinate.analyticOrderAt_automorphyUntwist`);
* the same holds for a section given only over an open subset `V` of the disc: its coefficient
  is holomorphic at the quotient coordinate of every point of the disc lying in `V`
  (`Subgroup.LinearizingCoordinate.differentiableAt_automorphyDescent`,
  `Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent_of_mem`);
* the transition function from the trivialization of another chart, with frame `F'` on an open
  set `U'`, to that of `ψ` is the coefficient of the automorphic extension of `F'`
  (`Subgroup.automorphyExtension`): it is holomorphic on the overlap of the two charts
  (`Subgroup.LinearizingCoordinate.differentiableAt_automorphyDescent_automorphyExtension`), the
  frame of `ψ` times it is `F'` transported in weight `k`
  (`Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent_automorphyExtension`),
  and it vanishes nowhere `F'` does not vanish after transport
  (`Subgroup.LinearizingCoordinate.automorphyDescent_automorphyExtension_ne_zero`); the
  coefficients of every section in the two charts differ by this transition function, also at
  the centre of `ψ`, for any second chart in which the coefficient of the section is continuous,
  such as a chart at a cusp
  (`Subgroup.LinearizingCoordinate.automorphyDescent_eq_automorphyDescent_automorphyExtension_mul`)
  or the chart of a local linearizing coordinate `ψ'` on a precisely invariant disc
  (`Subgroup.LinearizingCoordinate.automorphyDescent_eq_mul_automorphyDescent`); when the second
  chart is that of such a `ψ'`, the transition functions satisfy the cocycle law on triple
  overlaps (`Subgroup.LinearizingCoordinate.automorphyDescent_automorphyExtension_eq_mul`);
* the frames of the disc coordinates at `z` and at `h • z`, for `h ∈ SL(2, ℝ)`, differ by a
  nonzero constant after transport by `h` in weight `k`
  (`Subgroup.LinearizingCoordinate.automorphyFrame_discCoordinate_smul`): this is the transition
  function between the trivializations in the charts of `Γ \ ℍ` centred at two points of the same
  orbit, constant also at an elliptic orbit, where for `r ≠ 0` both frames vanish;
* in even weight `k = 2 * j` the frame is compared with the frame `(dw) ^ j` of the `j`-th power
  of the sheaf of differentials, whose weight-`k` function is
  `differentialFrame ψ j τ = (dw / dτ) ^ j`: this is a local section
  (`Subgroup.LinearizingCoordinate.differentialFrame_smul`,
  `Subgroup.LinearizingCoordinate.mdifferentiableOn_differentialFrame`), its untwisted section has
  order `j * (m - 1)` in `u`
  (`Subgroup.LinearizingCoordinate.analyticOrderAt_automorphyUntwist_differentialFrame`), and so
  the transition function between the two frames, the coefficient of `differentialFrame ψ j`, has
  order `j * (m - 1) / m` in `w`
  (`Subgroup.LinearizingCoordinate.analyticOrderAt_automorphyDescent_differentialFrame`).

The factor `(τ - conj z) ^ (-k)` absorbs the automorphy factor: for `g` fixing `z`,
`g • τ - conj z = (τ - conj z) / (denom g τ * conj λ)`, so `τ ↦ (τ - conj z) ^ k * f τ` is
multiplied by the constant `λ ^ k` under `g`, while `g` rotates `u` by `λ⁻²`. In the coordinate
`u` this function therefore transforms by the character `ζ ↦ ζ ^ r` of the rotation group, and
the factorization is `TauCeti.pow_smul_descendPowTwist_pow`. Since the order of the descended
function in `w` is the order of the untwisted function in `u` minus `r`, divided by `m`
(`Subgroup.LinearizingCoordinate.analyticOrderAt_automorphyUntwist`), the exponent `r` is the
correction by which the divisor of a section on the quotient differs from `1 / m` times its
divisor upstairs. For a lift `g` of an element of `Γ` fixing `z`, `denom g z ^ n = 1` as soon as
`2 * m ∣ n` (`Subgroup.denom_zpow_eq_one_of_dvd`). So for even `k`, when every element of `Γ'`
fixing `z` lifts an element of `Γ` (for instance when `Γ'.map (QuotientGroup.mk' _) ≤ Γ`), the
condition on `r` holds as soon as `2 * m ∣ 2 * r + k`, that is `r ≡ -k / 2` modulo `m`. Since
`dw / dτ` vanishes to order `m - 1` in `u`, the coefficient of `(dw / dτ) ^ j` then has order
`(j * (m - 1) - r) / m = ⌊(k / 2) * (1 - 1 / m)⌋` in `w`. This is the coefficient at the orbit
of `z` by which the divisor of a weight-`k` form, as a section of the automorphy sheaf, exceeds
that of the corresponding `j`-fold differential, and at elliptic points of orders two and three
it is the correction `⌊k / 4⌋`, respectively `⌊k / 3⌋`, in the dimension formulas of
Diamond–Shurman §3.5.

## Main declarations

* `Subgroup.LinearizingCoordinate.automorphyFrame`: the local frame of the weight-`k` automorphy
  sheaf in a local linearizing coordinate.
* `Subgroup.LinearizingCoordinate.automorphyFrame_smul` and
  `Subgroup.LinearizingCoordinate.mdifferentiableOn_automorphyFrame`: its transformation law and
  holomorphy.
* `Subgroup.LinearizingCoordinate.automorphyDescent`: the coefficient of a local section with
  respect to the frame, as a function of the quotient coordinate.
* `Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent`,
  `Subgroup.LinearizingCoordinate.differentiableOn_automorphyDescent` and
  `Subgroup.LinearizingCoordinate.eqOn_automorphyDescent`: the local trivialization.
* `Subgroup.LinearizingCoordinate.automorphyUntwist` and
  `Subgroup.LinearizingCoordinate.analyticOrderAt_automorphyUntwist`: the untwisted local section
  and the relation between its order and that of the coefficient.
* `Subgroup.LinearizingCoordinate.differentiableAt_automorphyDescent` and
  `Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent_of_mem`: the local
  trivialization over an open subset of the disc.
* `Subgroup.LinearizingCoordinate.differentiableAt_automorphyDescent_automorphyExtension`,
  `Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent_automorphyExtension` and
  `Subgroup.LinearizingCoordinate.automorphyDescent_automorphyExtension_ne_zero`: the transition
  function from another chart, the coefficient of the automorphic extension of its frame.
* `Subgroup.LinearizingCoordinate.automorphyFrame_compatible`: on a precisely invariant disc the
  frame is compatible with the weight-`k` action, so it is such a frame of another chart.
* `Subgroup.LinearizingCoordinate.automorphyDescent_eq_automorphyDescent_automorphyExtension_mul`,
  `Subgroup.LinearizingCoordinate.automorphyDescent_eq_mul_automorphyDescent` and
  `Subgroup.LinearizingCoordinate.automorphyDescent_automorphyExtension_eq_mul`: the coefficients
  of a section in two charts differ by the transition function, and the cocycle law.
* `Subgroup.LinearizingCoordinate.automorphyFrame_discCoordinate_smul`: the transport of the frame
  of the disc coordinate along `SL(2, ℝ)`.
* `Subgroup.LinearizingCoordinate.differentialFrame` and
  `Subgroup.LinearizingCoordinate.analyticOrderAt_automorphyDescent_differentialFrame`: the
  weight-`2 * j` function of `(dw) ^ j` and the order `j * (m - 1) / m` of its coefficient with
  respect to the automorphy frame.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3, 3.1 and 3.5–3.6.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §2.4.
-/

public section

noncomputable section

open Metric MulAction Set UpperHalfPlane TauCeti

open scoped ComplexConjugate Manifold MatrixGroups Pointwise Topology

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} {z : ℍ} {ε : ℝ}

namespace LinearizingCoordinate

variable [Finite (stabilizer Γ z)] (ψ : Γ.LinearizingCoordinate z ε)

/-- **The local frame of the weight-`k` automorphy sheaf** in a local linearizing coordinate `ψ`
at `z`, with exponent `r`: `τ ↦ (τ - conj z) ^ (-k) * u ^ r` for the coordinate `u` of `τ`. When
`r < m` and `denom g z ^ (2 * r + k) = 1` for the lifts `g` of the stabilizer, it satisfies the
weight-`k` transformation law (`Subgroup.LinearizingCoordinate.automorphyFrame_smul`) and every
local section of weight `k` is the frame times a holomorphic function of the quotient coordinate
(`Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent`). -/
def automorphyFrame (k : ℤ) (r : ℕ) (τ : stabilizerBall Γ z ε) : ℂ :=
  (((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ (-k) * ψ.coordinate τ ^ r

theorem automorphyFrame_def (k : ℤ) (r : ℕ) (τ : stabilizerBall Γ z ε) :
    ψ.automorphyFrame k r τ = (((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ (-k) * ψ.coordinate τ ^ r :=
  (rfl)

/-- The frame in terms of the ambient data: it is the restriction to the invariant disc of the
function `τ ↦ (τ - conj z) ^ (-k) * ψ.toEquiv (discCoordinate z τ) ^ r` on the upper half-plane,
whose holomorphy is `Subgroup.LinearizingCoordinate.mdifferentiableOn_automorphyFrame`. -/
theorem automorphyFrame_eq_toEquiv_discCoordinate (k : ℤ) (r : ℕ) (τ : stabilizerBall Γ z ε) :
    ψ.automorphyFrame k r τ = (((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ (-k) *
      ψ.toEquiv (UpperHalfPlane.discCoordinate z τ) ^ r := by
  rw [automorphyFrame_def, coordinate_def]

/-- Multiplying the frame by `(τ - conj z) ^ k` leaves the power `u ^ r` of the coordinate. -/
theorem zpow_mul_automorphyFrame (k : ℤ) (r : ℕ) (τ : stabilizerBall Γ z ε) :
    (((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ k * ψ.automorphyFrame k r τ = ψ.coordinate τ ^ r := by
  rw [automorphyFrame_def, ← mul_assoc, ← zpow_add₀ (coe_sub_conj_ne_zero z τ), add_neg_cancel,
    zpow_zero, one_mul]

/-- The frame vanishes exactly at the centre, and there only for a positive exponent. -/
@[simp]
theorem automorphyFrame_eq_zero_iff (k : ℤ) (r : ℕ) (τ : stabilizerBall Γ z ε) :
    ψ.automorphyFrame k r τ = 0 ↔ (τ : ℍ) = z ∧ r ≠ 0 := by
  rw [automorphyFrame_def, mul_eq_zero, pow_eq_zero_iff', coordinate_eq_zero_iff,
    or_iff_right (zpow_ne_zero _ (coe_sub_conj_ne_zero z τ))]

/-- **The frame is holomorphic** on the invariant disc: on the ambient upper half-plane it is
`τ ↦ (τ - conj z) ^ (-k) * u ^ r` with `u` the holomorphic coordinate
(`Subgroup.LinearizingCoordinate.mdifferentiableOn_coordinate`), and on
`Subgroup.stabilizerBall Γ z ε` this is `Subgroup.LinearizingCoordinate.automorphyFrame`
(`Subgroup.LinearizingCoordinate.automorphyFrame_eq_toEquiv_discCoordinate`). -/
theorem mdifferentiableOn_automorphyFrame (k : ℤ) (r : ℕ) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ ((τ : ℂ) - conj (z : ℂ)) ^ (-k) *
      ψ.toEquiv (UpperHalfPlane.discCoordinate z τ) ^ r) (ball z ε) := fun τ hτ ↦ by
  have h : MDiffAt (fun τ : ℍ ↦ ((τ : ℂ) - conj (z : ℂ)) ^ (-k)) τ :=
    (DifferentiableAt.comp_mdifferentiableAt (g := fun w : ℂ ↦ w ^ (-k))
      (differentiableAt_zpow.mpr (Or.inl (coe_sub_conj_ne_zero z τ)))
      ((mdifferentiable_coe τ).sub mdifferentiableAt_const))
  exact (h.mul (((ψ.mdifferentiableOn_coordinate τ hτ).mdifferentiableAt
    (isOpen_ball.mem_nhds hτ)).pow r)).mdifferentiableWithinAt

/-- **The transformation law of the frame.** If `g ∈ SL(2, ℝ)` lifts an element `q` of the
stabilizer of `z` and `denom g z ^ (2 * r + k) = 1`, then the frame satisfies the weight-`k`
transformation law for `g`: it is a local section of the weight-`k` automorphy sheaf. -/
theorem automorphyFrame_smul (k : ℤ) (r : ℕ) (q : stabilizer Γ z) {g : SL(2, ℝ)}
    (hg : (g : PSL(2, ℝ)) = ((q : Γ) : PSL(2, ℝ)))
    (hk : denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (τ : stabilizerBall Γ z ε) :
    ψ.automorphyFrame k r (q • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * ψ.automorphyFrame k r τ := by
  set c₀ := denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  -- the constant picked up by `(τ - conj z) ^ (-k)` cancels the rotation of `u ^ r`
  have hc₀ : c₀ ^ (-k) * (c₀ ^ (-2 : ℤ)) ^ r = 1 := by
    rw [zpow_neg_two_pow_eq_zpow₀ hk]
    exact zpow_neg_mul_zpow_self k (denom_ne_zero _ _)
  rw [automorphyFrame_def, automorphyFrame_def, coordinate_smul,
    coe_stabilizerRotation_eq_denom_zpow q hg, coe_smul_stabilizerBall_of_coe_eq q hg,
    coe_specialLinearGroup_smul_sub_conj_of_smul_eq_self (smul_eq_self_of_coe_eq q hg), mul_zpow,
    mul_zpow, inv_zpow',
    neg_neg, mul_pow]
  linear_combination
    (((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ (-k) * denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k *
      ψ.coordinate τ ^ r * hc₀

/-- The point of the upper half-plane, as a complex number, with coordinate `u` in `ψ`: the
inverse of the disc coordinate applied to the inverse reparametrization. -/
private def pointOf (u : ℂ) : ℂ :=
  ((z : ℂ) - conj (z : ℂ) * ψ.toEquiv.invFun u) / (1 - ψ.toEquiv.invFun u)

private theorem pointOf_coordinate (τ : stabilizerBall Γ z ε) :
    ψ.pointOf (ψ.coordinate τ) = ((τ : ℍ) : ℂ) := by
  have hτ : UpperHalfPlane.discCoordinate z (τ : ℍ) ∈ ψ.toEquiv.source := by
    rw [ψ.toEquiv_source, mem_ball_zero_iff]
    exact mem_ball_iff_norm_discCoordinate_lt.mp
      (mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2))
  have h := congrArg ((↑) : ℍ → ℂ) ((discCoordinateHomeomorph z).symm_apply_apply (τ : ℍ))
  rw [coe_discCoordinateHomeomorph_symm_apply, coe_discCoordinateHomeomorph_apply] at h
  rw [pointOf, coordinate_def, ψ.toEquiv.left_inv' hτ, h]

/-- The point with coordinate `u` depends holomorphically on `u`. -/
private theorem differentiableAt_pointOf {u : ℂ} (hu : u ∈ ψ.toEquiv.target) :
    DifferentiableAt ℂ ψ.pointOf u :=
  (analyticOnNhd_discCoordinateHomeomorph_symm z _
    (ball_subset_ball (Real.tanh_lt_one _).le (ψ.mem_ball_invFun hu))).differentiableAt.comp _
      (ψ.differentiableOn_invFun.differentiableAt (ψ.isOpen_target.mem_nhds hu))

/-- The centre `z` as a point of the invariant disc. -/
private def centre : stabilizerBall Γ z ε :=
  ⟨z, (mem_stabilizerBall Γ z ε).2 (by rw [dist_self]; exact ψ.ε_pos)⟩

private theorem coordinate_centre : ψ.coordinate ψ.centre = 0 :=
  (ψ.coordinate_eq_zero_iff _).mpr rfl

/-- The coordinate `0` of the centre lies in the image of the reparametrization. -/
private theorem zero_mem_target : (0 : ℂ) ∈ ψ.toEquiv.target :=
  (ψ.mem_target_iff 0).mpr ⟨ψ.centre, ψ.coordinate_centre.symm⟩

/-- The point with coordinate `0` is the centre. -/
private theorem pointOf_zero : ψ.pointOf 0 = z := by
  have h := pointOf_coordinate ψ ψ.centre
  rwa [coordinate_centre] at h

/-- **The untwisted local section**: a function `f` on the upper half-plane multiplied by the
weight-`k` factor `(τ - conj z) ^ k`, as a function of the coordinate `u` in `ψ`
(`Subgroup.LinearizingCoordinate.automorphyUntwist_coordinate`). For a local section `f` of
weight `k` it transforms under the rotations by a character
(`Subgroup.LinearizingCoordinate.automorphyUntwist_smul`), and its twisted descent is
`Subgroup.LinearizingCoordinate.automorphyDescent`. -/
def automorphyUntwist (k : ℤ) (f : ℍ → ℂ) (u : ℂ) : ℂ :=
  (ψ.pointOf u - conj (z : ℂ)) ^ k * f (ofComplex (ψ.pointOf u))

/-- At the coordinate `u` of a point `τ` of the invariant disc, the untwisted function is
`(τ - conj z) ^ k * f τ`. -/
@[simp]
theorem automorphyUntwist_coordinate (k : ℤ) (f : ℍ → ℂ) (τ : stabilizerBall Γ z ε) :
    ψ.automorphyUntwist k f (ψ.coordinate τ) = (((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ k * f τ := by
  rw [automorphyUntwist, pointOf_coordinate, ofComplex_apply]

/-- **The coefficient of a local section of the weight-`k` automorphy sheaf with respect to the
frame** `Subgroup.LinearizingCoordinate.automorphyFrame ψ k r`, as a function of the local
quotient coordinate of `ψ`: for a local section `f`,
`f τ = automorphyFrame ψ k r τ * automorphyDescent ψ k r f (quotientCoordinate ψ τ)`
(`Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent`). It is the twisted descent
`TauCeti.descendPowTwist` of the untwisted section
`Subgroup.LinearizingCoordinate.automorphyUntwist ψ k f`, which is `u ↦ (τ - conj z) ^ k * f τ`
for `τ` the point with coordinate `u`. -/
def automorphyDescent (k : ℤ) (r : ℕ) (f : ℍ → ℂ) : ℂ → ℂ :=
  letI : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  descendPowTwist (Nat.card (stabilizer Γ z)) r (ψ.automorphyUntwist k f)

theorem automorphyDescent_def (k : ℤ) (r : ℕ) (f : ℍ → ℂ) :
    letI : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
    ψ.automorphyDescent k r f =
      descendPowTwist (Nat.card (stabilizer Γ z)) r (ψ.automorphyUntwist k f) :=
  (rfl)

variable {Γ' : Subgroup SL(2, ℝ)} {k : ℤ} {r : ℕ} {f : ℍ → ℂ}

/-- The untwisted local section is holomorphic at the coordinate of every point of the invariant
disc at which the section is holomorphic. -/
theorem differentiableAt_automorphyUntwist_coordinate {τ : stabilizerBall Γ z ε}
    (hfd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ) :
    DifferentiableAt ℂ (ψ.automorphyUntwist k f) (ψ.coordinate τ) := by
  have hP := ψ.differentiableAt_pointOf ((ψ.mem_target_iff _).mpr ⟨τ, rfl⟩)
  have hF : DifferentiableAt ℂ (f ∘ ofComplex) (ψ.pointOf (ψ.coordinate τ)) := by
    rw [pointOf_coordinate]
    exact mdifferentiableAt_iff.mp hfd
  have hne : ψ.pointOf (ψ.coordinate τ) - conj (z : ℂ) ≠ 0 := by
    rw [pointOf_coordinate]
    exact coe_sub_conj_ne_zero z τ
  exact ((hP.sub_const _).zpow (Or.inl hne)).mul (hF.comp _ hP)

/-- The untwisted local section is holomorphic on the set of coordinate values. -/
theorem differentiableOn_automorphyUntwist (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε)) :
    DifferentiableOn ℂ (ψ.automorphyUntwist k f) ψ.toEquiv.target := by
  intro u hu
  obtain ⟨τ, rfl⟩ := (ψ.mem_target_iff u).mp hu
  have hτ : (τ : ℍ) ∈ ball z ε := mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2)
  exact (ψ.differentiableAt_automorphyUntwist_coordinate
    ((hfd τ hτ).mdifferentiableAt (isOpen_ball.mem_nhds hτ))).differentiableWithinAt

/-- The untwisted local section transforms by the character `ζ ↦ ζ ^ r` of the rotations at the
coordinate of a point `τ` of the invariant disc, when `denom g z ^ (2 * r + k) = 1` for the
elements `g ∈ Γ'` fixing `z` and the section satisfies the weight-`k` transformation law for them
at `τ`. -/
theorem automorphyUntwist_smul_coordinate
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (τ : stabilizerBall Γ z ε)
    (hf : ∀ g ∈ Γ', g • z = z →
      f (g • (τ : ℍ)) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    ψ.automorphyUntwist k f (ζ • ψ.coordinate τ) =
      ((ζ : ℂˣ) : ℂ) ^ r • ψ.automorphyUntwist k f (ψ.coordinate τ) := by
  set q := (stabilizerRotationEquiv Γ z).symm ζ
  have hq : stabilizerRotation Γ z q = ζ := by
    rw [← coe_stabilizerRotationEquiv]
    exact (stabilizerRotationEquiv Γ z).apply_symm_apply ζ
  obtain ⟨g, hgΓ', hgq⟩ := mem_map.mp (hΓ (q : Γ).2)
  rw [QuotientGroup.mk'_apply] at hgq
  have hgz := smul_eq_self_of_coe_eq q hgq
  have hζ : ζ • ψ.coordinate τ = ψ.coordinate (q • τ) := by
    rw [coordinate_smul, hq, rootsOfUnity.smul_eq_mul]
  set c₀ := denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  set D := denom (Matrix.SpecialLinearGroup.mapGL ℝ g) (τ : ℍ)
  have h₁ : c₀ ^ k = (c₀ ^ (-2 : ℤ)) ^ r :=
    (zpow_neg_two_pow_eq_zpow₀ (hk g hgΓ' hgz)).symm
  have h₂ : D ^ (-k) * D ^ k = 1 := zpow_neg_mul_zpow_self k (denom_ne_zero _ _)
  rw [hζ, automorphyUntwist_coordinate, automorphyUntwist_coordinate,
    coe_smul_stabilizerBall_of_coe_eq q hgq,
    coe_specialLinearGroup_smul_sub_conj_of_smul_eq_self hgz, mul_zpow, mul_zpow, inv_zpow',
    hf g hgΓ' hgz, ← hq, coe_stabilizerRotation_eq_denom_zpow q hgq, smul_eq_mul]
  linear_combination
    ((((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ k * f τ * c₀ ^ k) * h₂ +
      ((((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ k * f τ) * h₁

/-- The untwisted local section transforms by the character `ζ ↦ ζ ^ r` of the rotations, when
`denom g z ^ (2 * r + k) = 1` for the elements `g ∈ Γ'` fixing `z`. -/
theorem automorphyUntwist_smul (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    {u : ℂ} (hu : u ∈ ψ.toEquiv.target) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    ψ.automorphyUntwist k f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • ψ.automorphyUntwist k f u := by
  obtain ⟨τ, rfl⟩ := (ψ.mem_target_iff u).mp hu
  exact ψ.automorphyUntwist_smul_coordinate hΓ hk τ
    (fun g hg hgz ↦ hf g hg hgz τ (mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2))) ζ

/-- The coordinates of the points of the invariant disc lying in `V`. -/
private def coordinateSet (V : Set ℍ) : Set ℂ :=
  ψ.toEquiv.target ∩ ψ.pointOf ⁻¹' (((↑) : ℍ → ℂ) '' V)

private theorem coordinate_mem_coordinateSet {V : Set ℍ} {τ : stabilizerBall Γ z ε}
    (hτ : (τ : ℍ) ∈ V) : ψ.coordinate τ ∈ ψ.coordinateSet V :=
  ⟨(ψ.mem_target_iff _).mpr ⟨τ, rfl⟩, by
    rw [mem_preimage, pointOf_coordinate]
    exact mem_image_of_mem _ hτ⟩

private theorem exists_of_mem_coordinateSet {V : Set ℍ} {u : ℂ} (hu : u ∈ ψ.coordinateSet V) :
    ∃ τ : stabilizerBall Γ z ε, (τ : ℍ) ∈ V ∧ ψ.coordinate τ = u := by
  obtain ⟨τ, rfl⟩ := (ψ.mem_target_iff u).mp hu.1
  obtain ⟨σ, hσ, hστ⟩ := hu.2
  rw [pointOf_coordinate, coe_inj] at hστ
  exact ⟨τ, hστ ▸ hσ, rfl⟩

private theorem isOpen_coordinateSet {V : Set ℍ} (hV : IsOpen V) :
    IsOpen (ψ.coordinateSet V) :=
  ContinuousOn.isOpen_inter_preimage
    (fun _ hu ↦ (ψ.differentiableAt_pointOf hu).continuousAt.continuousWithinAt)
    ψ.isOpen_target (isOpenEmbedding_coe.isOpenMap _ hV)

variable {V : Set ℍ}

/-- On the coordinates of the points of `V`, the untwisted section of a function holomorphic and
satisfying the weight-`k` transformation law for the elements of `Γ'` fixing `z` on
`ball z ε ∩ V` is holomorphic and transforms by the character `ζ ↦ ζ ^ r`: the hypotheses of the
twisted descent `TauCeti.descendPowTwist`. -/
private theorem differentiableOn_automorphyUntwist_coordinateSet_and_smul
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hV : IsOpen V)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε ∩ V,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε ∩ V)) :
    DifferentiableOn ℂ (ψ.automorphyUntwist k f) (ψ.coordinateSet V) ∧
      ∀ u ∈ ψ.coordinateSet V, ∀ ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ,
        ψ.automorphyUntwist k f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • ψ.automorphyUntwist k f u := by
  have hball : ∀ σ : stabilizerBall Γ z ε, (σ : ℍ) ∈ V → (σ : ℍ) ∈ ball z ε ∩ V :=
    fun σ hσ ↦ ⟨mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 σ.2), hσ⟩
  refine ⟨fun u hu ↦ ?_, fun u hu ζ ↦ ?_⟩ <;>
    obtain ⟨σ, hσ, rfl⟩ := ψ.exists_of_mem_coordinateSet hu
  · exact (ψ.differentiableAt_automorphyUntwist_coordinate ((hfd _ (hball σ hσ)).mdifferentiableAt
      ((isOpen_ball.inter hV).mem_nhds (hball σ hσ)))).differentiableWithinAt
  · exact ψ.automorphyUntwist_smul_coordinate hΓ hk σ
      (fun g hg hgz ↦ hf g hg hgz σ (hball σ hσ)) ζ

/-- **The coefficient of a local section over an open subset of the disc is holomorphic.** If `f`
is holomorphic and satisfies the weight-`k` transformation law for the elements of `Γ'` fixing `z`
on `ball z ε ∩ V`, for an open set `V`, and `denom g z ^ (2 * r + k) = 1` for them, then
`automorphyDescent ψ k r f` is holomorphic at the quotient coordinate of every point of the
invariant disc lying in `V`. -/
theorem differentiableAt_automorphyDescent
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hV : IsOpen V)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε ∩ V,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε ∩ V)) (hr : r ≤ Nat.card (stabilizer Γ z))
    {τ : stabilizerBall Γ z ε} (hτ : (τ : ℍ) ∈ V) :
    DifferentiableAt ℂ (ψ.automorphyDescent k r f) (ψ.quotientCoordinate τ) := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨hd, hlaw⟩ := ψ.differentiableOn_automorphyUntwist_coordinateSet_and_smul hΓ hk hV hf hfd
  have hs := ψ.isOpen_coordinateSet hV
  have hmem : ψ.quotientCoordinate τ ∈ (· ^ Nat.card (stabilizer Γ z)) '' ψ.coordinateSet V :=
    ⟨_, ψ.coordinate_mem_coordinateSet hτ, (quotientCoordinate_def ψ τ).symm⟩
  rw [automorphyDescent_def]
  exact (differentiableOn_descendPowTwist hs hr hd hlaw _ hmem).differentiableAt
    (((Complex.isOpenQuotientMap_pow _).isOpenMap _ hs).mem_nhds hmem)

/-- **The local trivialization over an open subset of the disc.** Under the hypotheses of
`Subgroup.LinearizingCoordinate.differentiableAt_automorphyDescent`, and if `r < m`, then at every
point `τ` of the invariant disc lying in `V`, `f τ` is the frame times the coefficient at the
quotient coordinate of `τ`. -/
theorem automorphyFrame_mul_automorphyDescent_of_mem
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hV : IsOpen V)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε ∩ V,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε ∩ V)) (hr : r < Nat.card (stabilizer Γ z))
    {τ : stabilizerBall Γ z ε} (hτ : (τ : ℍ) ∈ V) :
    ψ.automorphyFrame k r τ * ψ.automorphyDescent k r f (ψ.quotientCoordinate τ) = f τ := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨hd, hlaw⟩ := ψ.differentiableOn_automorphyUntwist_coordinateSet_and_smul hΓ hk hV hf hfd
  have h := pow_smul_descendPowTwist_pow (ψ.isOpen_coordinateSet hV) hr hd hlaw
    (ψ.coordinate_mem_coordinateSet hτ)
  rw [automorphyUntwist_coordinate, smul_eq_mul] at h
  refine mul_left_cancel₀ (zpow_ne_zero k (coe_sub_conj_ne_zero z τ)) ?_
  rw [← mul_assoc, zpow_mul_automorphyFrame, automorphyDescent_def, quotientCoordinate_def, h]

/-- **The coefficient of a local section is holomorphic** on the set of local quotient-coordinate
values: if `f` is holomorphic on the invariant disc and satisfies the weight-`k` transformation
law for the elements of `Γ'` fixing `z`, and `denom g z ^ (2 * r + k) = 1` for them, then
`automorphyDescent ψ k r f` is holomorphic on `quotientImage ψ`. -/
theorem differentiableOn_automorphyDescent (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε)) (hr : r ≤ Nat.card (stabilizer Γ z)) :
    DifferentiableOn ℂ (ψ.automorphyDescent k r f) ψ.quotientImage := by
  intro w hw
  obtain ⟨τ, rfl⟩ := (ψ.mem_quotientImage_iff w).mp hw
  exact (ψ.differentiableAt_automorphyDescent hΓ hk isOpen_univ
    (fun g hg hgz τ hτ ↦ hf g hg hgz τ hτ.1) (hfd.mono inter_subset_left) hr
    (mem_univ _)).differentiableWithinAt

/-- **The local trivialization of the weight-`k` automorphy sheaf.** If `f` is holomorphic on the
invariant disc and satisfies the weight-`k` transformation law for the elements of `Γ'` fixing
`z`, and `r < m` with `denom g z ^ (2 * r + k) = 1` for them, then `f` is the frame times its
coefficient, a holomorphic function of the local quotient coordinate
(`Subgroup.LinearizingCoordinate.differentiableOn_automorphyDescent`). -/
theorem automorphyFrame_mul_automorphyDescent
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε)) (hr : r < Nat.card (stabilizer Γ z))
    (τ : stabilizerBall Γ z ε) :
    ψ.automorphyFrame k r τ * ψ.automorphyDescent k r f (ψ.quotientCoordinate τ) = f τ :=
  ψ.automorphyFrame_mul_automorphyDescent_of_mem hΓ hk isOpen_univ
    (fun g hg hgz τ hτ ↦ hf g hg hgz τ hτ.1) (hfd.mono inter_subset_left) hr (mem_univ _)

/-- **Uniqueness of the local trivialization.** Under the hypotheses of
`Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent`, any function `G`
continuous on the set of local quotient-coordinate values with
`f τ = automorphyFrame ψ k r τ * G (quotientCoordinate ψ τ)` is the coefficient of `f` there. -/
theorem eqOn_automorphyDescent (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε)) (hr : r < Nat.card (stabilizer Γ z))
    {G : ℂ → ℂ} (hG : ContinuousOn G ψ.quotientImage)
    (hfG : ∀ τ : stabilizerBall Γ z ε,
      f τ = ψ.automorphyFrame k r τ * G (ψ.quotientCoordinate τ)) :
    EqOn G (ψ.automorphyDescent k r f) ψ.quotientImage := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  rw [quotientImage_def] at hG ⊢
  refine eqOn_descendPowTwist ψ.isOpen_target hr (ψ.differentiableOn_automorphyUntwist hfd)
    (fun u hu ↦ ψ.automorphyUntwist_smul hΓ hk hf hu) hG fun u hu ↦ ?_
  obtain ⟨τ, rfl⟩ := (ψ.mem_target_iff u).mp hu
  rw [automorphyUntwist_coordinate, hfG τ, ← mul_assoc, zpow_mul_automorphyFrame,
    quotientCoordinate_def, smul_eq_mul]

/-- **The order of the coefficient of a local section.** Under the hypotheses of
`Subgroup.LinearizingCoordinate.automorphyFrame_mul_automorphyDescent`, the order at `u = 0` of the
untwisted section `u ↦ (τ - conj z) ^ k * f τ` is `r` plus `m` times the order at `w = 0` of the
coefficient `automorphyDescent ψ k r f`. -/
theorem analyticOrderAt_automorphyUntwist
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε)) (hr : r < Nat.card (stabilizer Γ z)) :
    analyticOrderAt (ψ.automorphyUntwist k f) 0 =
      r + analyticOrderAt (ψ.automorphyDescent k r f) 0 * Nat.card (stabilizer Γ z) := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  exact analyticOrderAt_eq_add_analyticOrderAt_descendPowTwist_mul ψ.isOpen_target
    ψ.zero_mem_target hr
    (ψ.differentiableOn_automorphyUntwist hfd) fun u hu ↦ ψ.automorphyUntwist_smul hΓ hk hf hu

/-! ### The powers of the differential of the local quotient coordinate -/

/-- The local quotient coordinate `w = u ^ m` of `ψ`, read on `ℂ` through
`UpperHalfPlane.ofComplex`. -/
private def quotientCoordinateOnComplex (t : ℂ) : ℂ :=
  ψ.toEquiv (UpperHalfPlane.discCoordinate z (ofComplex t)) ^ Nat.card (stabilizer Γ z)

private theorem quotientCoordinateOnComplex_def (t : ℂ) :
    ψ.quotientCoordinateOnComplex t =
      ψ.toEquiv (UpperHalfPlane.discCoordinate z (ofComplex t)) ^ Nat.card (stabilizer Γ z) :=
  (rfl)

/-- The local quotient coordinate, read on `ℂ`, at a point of the invariant disc. -/
private theorem quotientCoordinateOnComplex_coe (τ : stabilizerBall Γ z ε) :
    ψ.quotientCoordinateOnComplex ((τ : ℍ) : ℂ) = ψ.quotientCoordinate τ := by
  rw [quotientCoordinateOnComplex_def, ofComplex_apply, quotientCoordinate_def, coordinate_def]

/-- **The `j`-th power of the differential of the local quotient coordinate**, as a function of
weight `2 * j` on the upper half-plane: `τ ↦ (dw / dτ) ^ j` for the local quotient coordinate
`w = u ^ m` of `ψ`, read on `ℂ` through `UpperHalfPlane.ofComplex`. It is the weight-`2 * j`
function attached to the frame `(dw) ^ j` of the `j`-th power of the sheaf of differentials in the
chart of `ψ`: it is holomorphic on the invariant disc
(`Subgroup.LinearizingCoordinate.mdifferentiableOn_differentialFrame`) and satisfies the
weight-`2 * j` transformation law for the stabilizer
(`Subgroup.LinearizingCoordinate.differentialFrame_smul`), and its coefficient with respect to the
automorphy frame is the transition function between the two frames, of order `j * (m - 1) / m`
at the centre
(`Subgroup.LinearizingCoordinate.analyticOrderAt_automorphyDescent_differentialFrame`). -/
def differentialFrame (j : ℕ) (τ : ℍ) : ℂ :=
  deriv ψ.quotientCoordinateOnComplex τ ^ j

theorem differentialFrame_def (j : ℕ) (τ : ℍ) :
    ψ.differentialFrame j τ = deriv (fun t : ℂ ↦ ψ.toEquiv
      (UpperHalfPlane.discCoordinate z (ofComplex t)) ^ Nat.card (stabilizer Γ z)) τ ^ j :=
  (rfl)

private theorem differentialFrame_eq_deriv (j : ℕ) (τ : ℍ) :
    ψ.differentialFrame j τ = deriv ψ.quotientCoordinateOnComplex τ ^ j :=
  (rfl)

/-- The local quotient coordinate, read on `ℂ`, is holomorphic at the points of the invariant
disc. -/
private theorem differentiableAt_quotientCoordinateOnComplex {τ : ℍ} (hτ : τ ∈ ball z ε) :
    DifferentiableAt ℂ ψ.quotientCoordinateOnComplex τ :=
  mdifferentiableAt_iff.mp
    ((ψ.mdifferentiableOn_quotientCoordinate τ hτ).mdifferentiableAt (isOpen_ball.mem_nhds hτ))

/-- **The transformation law of the powers of the differential of the local quotient
coordinate.** If `g ∈ SL(2, ℝ)` lifts an element of the stabilizer of `z`, then
`differentialFrame ψ j` satisfies the weight-`2 * j` transformation law for `g` on the invariant
disc: the local quotient coordinate is invariant under `g`, and `g` has derivative
`(denom g τ ^ 2)⁻¹` at `τ`. -/
theorem differentialFrame_smul (j : ℕ) (q : stabilizer Γ z) {g : SL(2, ℝ)}
    (hg : (g : PSL(2, ℝ)) = ((q : Γ) : PSL(2, ℝ))) {τ : ℍ} (hτ : τ ∈ ball z ε) :
    ψ.differentialFrame j (g • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ (2 * (j : ℤ)) * ψ.differentialFrame j τ := by
  -- the local quotient coordinate is invariant under `g` near `τ`
  have hinv : (fun t : ℂ ↦ ψ.quotientCoordinateOnComplex
      (((g : PSL(2, ℝ)) • ofComplex t : ℍ) : ℂ)) =ᶠ[nhds (τ : ℂ)]
        ψ.quotientCoordinateOnComplex := by
    filter_upwards [(isOpenEmbedding_coe.isOpenMap _ isOpen_ball).mem_nhds
      (mem_image_of_mem _ hτ)] with t ht
    obtain ⟨σ, hσ, rfl⟩ := ht
    have hσ' : σ ∈ stabilizerBall Γ z ε := (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hσ)
    have h := ψ.quotientCoordinateOnComplex_coe (q • ⟨σ, hσ'⟩)
    rw [quotientCoordinate_smul, coe_smul_stabilizerBall_of_coe_eq q hg,
      ← ψ.quotientCoordinateOnComplex_coe ⟨σ, hσ'⟩] at h
    rw [ofComplex_apply, pslMk_smul]
    exact h
  have hderiv := Matrix.ProjectiveSpecialLinearGroup.deriv_smul_mul_smulDeriv_of_eventuallyEq _ hinv
  rw [pslMk_smul, Matrix.SpecialLinearGroup.smulDeriv_coe] at hderiv
  rw [differentialFrame_eq_deriv, differentialFrame_eq_deriv, ← hderiv, zpow_mul,
    zpow_ofNat, zpow_natCast, ← mul_pow, mul_left_comm,
    mul_inv_cancel₀ (pow_ne_zero 2 (denom_ne_zero _ _)), mul_one]

/-- **The powers of the differential of the local quotient coordinate are holomorphic** on the
invariant disc. -/
theorem mdifferentiableOn_differentialFrame (j : ℕ) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ψ.differentialFrame j) (ball z ε) := by
  have hU : IsOpen (((↑) : ℍ → ℂ) '' ball z ε) := isOpenEmbedding_coe.isOpenMap _ isOpen_ball
  have hWd : DifferentiableOn ℂ ψ.quotientCoordinateOnComplex (((↑) : ℍ → ℂ) '' ball z ε) := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact (ψ.differentiableAt_quotientCoordinateOnComplex hσ).differentiableWithinAt
  intro τ hτ
  refine (mdifferentiableAt_iff.mpr ?_).mdifferentiableWithinAt
  have hD : DifferentiableAt ℂ (fun t ↦ deriv ψ.quotientCoordinateOnComplex t ^ j) τ :=
    ((hWd.deriv hU).differentiableAt (hU.mem_nhds (mem_image_of_mem _ hτ))).pow j
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with t ht
  rw [Function.comp_apply, differentialFrame_eq_deriv, ofComplex_apply_of_im_pos ht,
    UpperHalfPlane.coe_mk]

/-- The derivative of the point with coordinate `u` does not vanish at the centre: the inverse
of the disc coordinate is a Möbius transformation, and the inverse reparametrization is
biholomorphic. -/
private theorem deriv_pointOf_zero_ne_zero : deriv ψ.pointOf 0 ≠ 0 := by
  have hr : 0 < Real.tanh (ε / 2) := by
    rw [← Real.tanh_zero]
    exact Real.tanh_strictMono (half_pos ψ.ε_pos)
  have h0s : (0 : ℂ) ∈ ψ.toEquiv.source := by rw [ψ.toEquiv_source]; exact mem_ball_self hr
  have h0t := ψ.zero_mem_target
  have hinv0 : ψ.toEquiv.invFun 0 = 0 := by
    have h := ψ.toEquiv.left_inv' h0s
    rwa [ψ.map_zero] at h
  have hd : DifferentiableAt ℂ ψ.toEquiv.invFun 0 :=
    ψ.differentiableOn_invFun.differentiableAt (ψ.isOpen_target.mem_nhds h0t)
  have hM := hasDerivAt_discCoordinateHomeomorph_symm z (zero_ne_one (α := ℂ))
  rw [sub_zero, one_pow, div_one, ← hinv0] at hM
  have hP : HasDerivAt ψ.pointOf (((z : ℂ) - conj (z : ℂ)) * deriv ψ.toEquiv.invFun 0) 0 :=
    hM.comp 0 hd.hasDerivAt
  rw [hP.deriv]
  exact mul_ne_zero (coe_sub_conj_ne_zero z z) (ψ.deriv_invFun_ne_zero h0t)

/-- The local quotient coordinate, read on `ℂ`, at the point with coordinate `u` is `u ^ m`. -/
private theorem quotientCoordinateOnComplex_pointOf {u : ℂ} (hu : u ∈ ψ.toEquiv.target) :
    ψ.quotientCoordinateOnComplex (ψ.pointOf u) = u ^ Nat.card (stabilizer Γ z) := by
  obtain ⟨σ, rfl⟩ := (ψ.mem_target_iff u).mp hu
  rw [pointOf_coordinate, quotientCoordinateOnComplex_coe, quotientCoordinate_def]

/-- The chain rule for `w = u ^ m` in the coordinate `u`: the untwisted powers of the
differential times `(dτ / du) ^ j` are `(τ - conj z) ^ (2 * j) * m ^ j * u ^ (j * (m - 1))`. -/
private theorem automorphyUntwist_differentialFrame_mul (j : ℕ) {u : ℂ}
    (hu : u ∈ ψ.toEquiv.target) :
    ψ.automorphyUntwist (2 * j) (ψ.differentialFrame j) u * deriv ψ.pointOf u ^ j =
      (ψ.pointOf u - conj (z : ℂ)) ^ (2 * j) * (Nat.card (stabilizer Γ z) : ℂ) ^ j *
        u ^ (j * (Nat.card (stabilizer Γ z) - 1)) := by
  set m := Nat.card (stabilizer Γ z)
  obtain ⟨τ, rfl⟩ := (ψ.mem_target_iff u).mp hu
  have hτ : (τ : ℍ) ∈ ball z ε := mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2)
  have hWP : ψ.quotientCoordinateOnComplex ∘ ψ.pointOf =ᶠ[nhds (ψ.coordinate τ)]
      fun u ↦ u ^ m := by
    filter_upwards [ψ.isOpen_target.mem_nhds hu] with v hv
    exact ψ.quotientCoordinateOnComplex_pointOf hv
  have hWd := ψ.differentiableAt_quotientCoordinateOnComplex hτ
  rw [← pointOf_coordinate ψ τ] at hWd
  have hchain := deriv_comp _ hWd (ψ.differentiableAt_pointOf hu)
  rw [hWP.deriv_eq, deriv_pow_field] at hchain
  have hU : ψ.automorphyUntwist (2 * j) (ψ.differentialFrame j) (ψ.coordinate τ) =
      (ψ.pointOf (ψ.coordinate τ) - conj (z : ℂ)) ^ (2 * j) *
        deriv ψ.quotientCoordinateOnComplex (ψ.pointOf (ψ.coordinate τ)) ^ j := by
    rw [automorphyUntwist_coordinate, differentialFrame_eq_deriv, pointOf_coordinate]
    norm_cast
  rw [hU, mul_assoc, ← mul_pow, ← hchain, mul_pow, ← pow_mul, mul_comm (m - 1)]
  ring

/-- **The order of the untwisted powers of the differential.** In the coordinate `u` of `ψ`, the
function `u ↦ (τ - conj z) ^ (2 * j) * (dw / dτ) ^ j` has order `j * (m - 1)` at the centre:
`w = u ^ m` and `u` is a local coordinate. -/
theorem analyticOrderAt_automorphyUntwist_differentialFrame (j : ℕ) :
    analyticOrderAt (ψ.automorphyUntwist (2 * j) (ψ.differentialFrame j)) 0 =
      (j * (Nat.card (stabilizer Γ z) - 1) : ℕ) := by
  set m := Nat.card (stabilizer Γ z)
  have hT := ψ.isOpen_target
  have h0 := ψ.zero_mem_target
  -- the factors other than the power of `u` are analytic and do not vanish at `0`
  have hPa : AnalyticAt ℂ ψ.pointOf 0 :=
    DifferentiableOn.analyticAt (fun u hu ↦ (ψ.differentiableAt_pointOf hu).differentiableWithinAt)
      (hT.mem_nhds h0)
  have hUa : AnalyticAt ℂ (ψ.automorphyUntwist (2 * j) (ψ.differentialFrame j)) 0 :=
    (ψ.differentiableOn_automorphyUntwist (ψ.mdifferentiableOn_differentialFrame j)).analyticAt
      (hT.mem_nhds h0)
  have hA : AnalyticAt ℂ (fun u ↦ (ψ.pointOf u - conj (z : ℂ)) ^ (2 * j) * (m : ℂ) ^ j) 0 := by
    fun_prop
  have hA0 :
      analyticOrderAt (fun u ↦ (ψ.pointOf u - conj (z : ℂ)) ^ (2 * j) * (m : ℂ) ^ j) 0 = 0 := by
    rw [hA.analyticOrderAt_eq_zero, ψ.pointOf_zero]
    exact mul_ne_zero (pow_ne_zero _ (coe_sub_conj_ne_zero z z))
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
  have hD0 : analyticOrderAt (deriv ψ.pointOf) 0 = 0 :=
    hPa.deriv.analyticOrderAt_eq_zero.mpr ψ.deriv_pointOf_zero_ne_zero
  have heq : ψ.automorphyUntwist (2 * j) (ψ.differentialFrame j) * deriv ψ.pointOf ^ j =ᶠ[nhds 0]
      (fun u ↦ (ψ.pointOf u - conj (z : ℂ)) ^ (2 * j) * (m : ℂ) ^ j) *
        (· - (0 : ℂ)) ^ (j * (m - 1)) := by
    filter_upwards [hT.mem_nhds h0] with u hu
    simpa only [Pi.mul_apply, Pi.pow_apply, sub_zero] using
      ψ.automorphyUntwist_differentialFrame_mul j hu
  have h := analyticOrderAt_congr heq
  rw [analyticOrderAt_mul hUa (hPa.deriv.pow j), analyticOrderAt_pow hPa.deriv, hD0,
    analyticOrderAt_mul hA (by fun_prop), hA0, analyticOrderAt_centeredMonomial] at h
  simpa using h

/-- **The transition function from the automorphy frame to the powers of the differential.**
Let `Γ'` be a group of lifts of exactly the elements of `Γ`, let `j : ℕ`, and let `r < m` with
`denom g z ^ (2 * r + 2 * j) = 1` for the elements `g ∈ Γ'` fixing `z`. Then the coefficient of
`differentialFrame ψ j`, the weight-`2 * j` function of the frame `(dw) ^ j`, with respect to the
automorphy frame `automorphyFrame ψ (2 * j) r` has order `j * (m - 1) / m` at the centre.

This is the correction at an elliptic point of the divisor of the weight-`2 * j` automorphy sheaf
relative to the `j`-th power of the sheaf of differentials: `⌊j * (1 - 1 / m)⌋`, which is
`⌊k / 4⌋` at a point of order two and `⌊k / 3⌋` at a point of order three, for `k = 2 * j`. -/
theorem analyticOrderAt_automorphyDescent_differentialFrame {j : ℕ}
    (hΓ : Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))) = Γ)
    (hk : ∀ g ∈ Γ', g • z = z →
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + 2 * (j : ℤ)) = 1)
    (hr : r < Nat.card (stabilizer Γ z)) :
    analyticOrderAt (ψ.automorphyDescent (2 * j) r (ψ.differentialFrame j)) 0 =
      (j * (Nat.card (stabilizer Γ z) - 1) / Nat.card (stabilizer Γ z) : ℕ) := by
  set m := Nat.card (stabilizer Γ z)
  have hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε, ψ.differentialFrame j (g • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ (2 * (j : ℤ)) * ψ.differentialFrame j τ := by
    intro g hg hgz τ hτ
    have hgΓ : (g : PSL(2, ℝ)) ∈ Γ := hΓ ▸ mem_map_of_mem _ hg
    exact ψ.differentialFrame_smul j ⟨⟨g, hgΓ⟩, by
      rw [mem_stabilizer_iff, Subgroup.mk_smul, pslMk_smul, hgz]⟩ rfl hτ
  have h := ψ.analyticOrderAt_automorphyUntwist hΓ.ge hk hf
    (ψ.mdifferentiableOn_differentialFrame j) hr
  rw [analyticOrderAt_automorphyUntwist_differentialFrame] at h
  generalize analyticOrderAt (ψ.automorphyDescent (2 * j) r (ψ.differentialFrame j)) 0 = n at h ⊢
  induction n using ENat.recTopCoe with
  | top =>
    rw [ENat.top_mul (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), add_top] at h
    exact absurd h (ENat.natCast_ne_top _)
  | coe n =>
    have h' : j * (m - 1) = r + n * m := by exact_mod_cast h
    rw [h', Nat.add_mul_div_right _ _ Nat.card_pos, Nat.div_eq_of_lt hr, zero_add]

/-! ### Transport of the frame of the disc coordinate along `SL(2, ℝ)` -/

/-- The frame of the disc coordinate, as a function on the upper half-plane:
`τ ↦ (τ - conj z) ^ (-k) * discCoordinate z τ ^ r`. -/
@[simp]
theorem automorphyFrame_discCoordinate (hε : 0 < ε) (k : ℤ) (r : ℕ) (τ : stabilizerBall Γ z ε) :
    automorphyFrame (discCoordinate hε) k r τ =
      (((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ (-k) * UpperHalfPlane.discCoordinate z τ ^ r := by
  rw [automorphyFrame_def, coordinate_discCoordinate]

/-- **The transition function between the frames of the disc coordinates at `z` and at `h • z`
is constant.** Let `h ∈ SL(2, ℝ)`, and let `τ` be a point of the invariant disc of radius `ε`
about `z` whose image `h • τ` is the point `τ'` of the invariant disc of radius `ε'` about
`h • z`.
Then the frame of the disc coordinate at `h • z`, read at `τ'`, is the weight-`k` automorphy factor
`denom h τ ^ k` times the frame of the disc coordinate at `z`, read at `τ`, times the nonzero
constant `conj (denom h z) ^ k * (conj (denom h z) / denom h z) ^ r`.

When `h` lifts an element of `Γ`, the charts `Subgroup.stabilizerBallQuotientChart` centred at
`z` and at `h • z` are charts about the same point of `Γ \ ℍ`, and this constant is the transition
function between the trivializations of the weight-`k` automorphy sheaf by their frames: the
quotient of the frame at `h • z`, transported by `h` in weight `k`, by the frame at `z`. -/
theorem automorphyFrame_discCoordinate_smul (hε : 0 < ε) {ε' : ℝ} (hε' : 0 < ε') (h : SL(2, ℝ))
    [Finite (stabilizer Γ (h • z))] (k : ℤ) (r : ℕ) (τ : stabilizerBall Γ z ε)
    (τ' : stabilizerBall Γ (h • z) ε') (hτ : (τ' : ℍ) = h • (τ : ℍ)) :
    automorphyFrame (discCoordinate hε') k r τ' =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ h) τ ^ k *
        (conj (denom (Matrix.SpecialLinearGroup.mapGL ℝ h) z) ^ k *
          (conj (denom (Matrix.SpecialLinearGroup.mapGL ℝ h) z) /
            denom (Matrix.SpecialLinearGroup.mapGL ℝ h) z) ^ r) *
        automorphyFrame (discCoordinate hε) k r τ := by
  set G := Matrix.SpecialLinearGroup.mapGL ℝ h
  have hdet : 0 < G.det.val := by simp [G]
  have hG : ∀ σ : ℍ, h • σ = G • σ := fun σ ↦ (Matrix.SpecialLinearGroup.mapGL_smul h σ).symm
  rw [automorphyFrame_discCoordinate, automorphyFrame_discCoordinate, hτ, hG, hG,
    UpperHalfPlane.discCoordinate_smul hdet, coe_smul_sub_conj_smul hdet]
  simp only [G, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one, Complex.ofReal_one, one_mul]
  rw [div_eq_mul_inv, mul_zpow, mul_inv, mul_zpow, inv_zpow', inv_zpow', neg_neg, mul_pow]
  ring

/-! ### Transition functions between the trivializations of two charts -/

/-- **The transformation law of the frame for the elements of `Γ'` fixing `z`.** If every element
of `Γ'` lifts an element of `Γ` and `denom g z ^ (2 * r + k) = 1` for the elements `g ∈ Γ'` fixing
`z`, then the frame satisfies the weight-`k` transformation law for each of them. -/
theorem automorphyFrame_smul_of_mem (hΓ : Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))) ≤ Γ)
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    {g : SL(2, ℝ)} (hg : g ∈ Γ') (hgz : g • z = z) (τ τ' : stabilizerBall Γ z ε)
    (hτ' : (τ' : ℍ) = g • (τ : ℍ)) :
    ψ.automorphyFrame k r τ' =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * ψ.automorphyFrame k r τ := by
  let q : stabilizer Γ z := ⟨⟨g, hΓ (mem_map_of_mem _ hg)⟩, by
    rw [mem_stabilizer_iff, Subgroup.mk_smul, pslMk_smul, hgz]⟩
  have hq : τ' = q • τ := Subtype.ext (by rw [hτ', coe_smul_stabilizerBall_of_coe_eq q rfl])
  rw [hq, ψ.automorphyFrame_smul k r q rfl (hk g hg hgz)]

variable {U' : Set ℍ} {F' : ℍ → ℂ}

/-- **The transition function is holomorphic.** Let `F'` be a function on an open set `U'`,
holomorphic there and compatible with the weight-`k` action of `Γ'` (for instance the frame of
another chart, on a precisely invariant disc or horodisc). The coefficient with respect to the
frame of `ψ` of its automorphic extension `Subgroup.automorphyExtension Γ' U' k F'` is the
transition function from the trivialization of the chart of `F'` to that of `ψ`; it is holomorphic
at the quotient coordinate of every point `τ` of the invariant disc moved into `U'` by an element
of `Γ'`, that is, on the overlap of the two charts. -/
theorem differentiableAt_automorphyDescent_automorphyExtension
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hU' : IsOpen U')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hF'd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F' U') (hr : r ≤ Nat.card (stabilizer Γ z))
    {τ : stabilizerBall Γ z ε} {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • (τ : ℍ) ∈ U') :
    DifferentiableAt ℂ (ψ.automorphyDescent k r (Γ'.automorphyExtension U' k F'))
      (ψ.quotientCoordinate τ) :=
  ψ.differentiableAt_automorphyDescent hΓ hk hU'.smul_left
    (fun _ hg _ σ _ ↦ automorphyExtension_smul hF' hg σ)
    ((mdifferentiableOn_automorphyExtension hF' hU' hF'd).mono inter_subset_right) hr
    (mem_smul_set_iff_exists_smul_mem.mpr ⟨h, hh, hτ⟩)

/-- **The defining identity of the transition function.** Under the hypotheses of
`Subgroup.LinearizingCoordinate.differentiableAt_automorphyDescent_automorphyExtension`, and if
`r < m`, the frame of `ψ` at `τ` times the transition function at the quotient coordinate of `τ`
is the function `F'` at `h • τ`, transported back to `τ` in weight `k`. -/
theorem automorphyFrame_mul_automorphyDescent_automorphyExtension
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hU' : IsOpen U')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hF'd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F' U') (hr : r < Nat.card (stabilizer Γ z))
    {τ : stabilizerBall Γ z ε} {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • (τ : ℍ) ∈ U') :
    ψ.automorphyFrame k r τ *
        ψ.automorphyDescent k r (Γ'.automorphyExtension U' k F') (ψ.quotientCoordinate τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ h) τ ^ (-k) * F' (h • τ) := by
  rw [ψ.automorphyFrame_mul_automorphyDescent_of_mem hΓ hk hU'.smul_left
    (fun _ hg _ σ _ ↦ automorphyExtension_smul hF' hg σ)
    ((mdifferentiableOn_automorphyExtension hF' hU' hF'd).mono inter_subset_right) hr
    (mem_smul_set_iff_exists_smul_mem.mpr ⟨h, hh, hτ⟩), automorphyExtension_eq hF' hh hτ]

/-- **The transition function does not vanish** at the quotient coordinate of a point `τ` of the
overlap with `F' (h • τ) ≠ 0`. When `F'` is the frame of a second local linearizing coordinate at
`z'`, which vanishes only at `z'` (`Subgroup.LinearizingCoordinate.automorphyFrame_eq_zero_iff`),
this is every point `τ` of the overlap with `h • τ ≠ z'`. -/
theorem automorphyDescent_automorphyExtension_ne_zero
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hU' : IsOpen U')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hF'd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F' U') (hr : r < Nat.card (stabilizer Γ z))
    {τ : stabilizerBall Γ z ε} {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ : h • (τ : ℍ) ∈ U')
    (hF'0 : F' (h • τ) ≠ 0) :
    ψ.automorphyDescent k r (Γ'.automorphyExtension U' k F') (ψ.quotientCoordinate τ) ≠ 0 := by
  have h0 := ψ.automorphyFrame_mul_automorphyDescent_automorphyExtension hΓ hk hU' hF' hF'd hr hh hτ
  exact right_ne_zero_of_mul (h0 ▸ mul_ne_zero (zpow_ne_zero _ (denom_ne_zero _ _)) hF'0)

/-- **The frame is compatible on a precisely invariant disc.** On a disc `ball z ε` that is
precisely invariant under `Γ'`, the frame, read on the upper half-plane, is compatible with the
weight-`k` action of `Γ'`, so that it has an automorphic extension
(`Subgroup.automorphyExtension`) and the transition-function lemmas above apply to it. -/
theorem automorphyFrame_compatible
    (hΓ : Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))) ≤ Γ)
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hprec : ∀ g ∈ Γ', ∀ σ ∈ ball z ε, g • σ ∈ ball z ε → g • z = z) :
    ∀ g ∈ Γ', ∀ σ ∈ ball z ε, g • σ ∈ ball z ε →
      (fun σ : ℍ ↦ ((σ : ℂ) - conj (z : ℂ)) ^ (-k) *
        ψ.toEquiv (UpperHalfPlane.discCoordinate z σ) ^ r) (g • σ) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k *
          (((σ : ℂ) - conj (z : ℂ)) ^ (-k) *
            ψ.toEquiv (UpperHalfPlane.discCoordinate z σ) ^ r) := fun g hg σ hσ hgσ ↦ by
  have h := ψ.automorphyFrame_smul_of_mem hΓ hk hg (hprec g hg σ hσ hgσ)
    ⟨σ, (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hσ)⟩
    ⟨g • σ, (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hgσ)⟩ rfl
  rwa [automorphyFrame_eq_toEquiv_discCoordinate, automorphyFrame_eq_toEquiv_discCoordinate] at h

variable {W : Set ℍ} {c' : ℍ → ℂ}

/-- The coefficient law away from the centre, where the frame of `ψ` does not vanish and can be
cancelled. -/
private theorem automorphyDescent_eq_mul_of_automorphyFrame_ne_zero
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hr : r < Nat.card (stabilizer Γ z)) (hU' : IsOpen U')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hF'd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F' U')
    (hW : IsOpen W) (hf : ∀ g ∈ Γ', ∀ σ : ℍ,
      f (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * f σ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W) {τ : stabilizerBall Γ z ε} (hτW : (τ : ℍ) ∈ W)
    {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ' : h • (τ : ℍ) ∈ U') {c : ℂ}
    (hc : F' (h • (τ : ℍ)) * c = f (h • (τ : ℍ))) (hF : ψ.automorphyFrame k r τ ≠ 0) :
    ψ.automorphyDescent k r f (ψ.quotientCoordinate τ) =
      ψ.automorphyDescent k r (Γ'.automorphyExtension U' k F') (ψ.quotientCoordinate τ) * c := by
  have h₁ := ψ.automorphyFrame_mul_automorphyDescent_of_mem hΓ hk hW
    (fun g hg _ σ _ ↦ hf g hg σ) (hfd.mono inter_subset_right) hr hτW
  have h₂ := ψ.automorphyFrame_mul_automorphyDescent_automorphyExtension hΓ hk hU' hF' hF'd hr hh
    hτ'
  have h₃ := hc
  rw [hf h hh] at h₃
  have hden := zpow_neg_mul_zpow_self k (denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ h) τ)
  refine mul_left_cancel₀ hF ?_
  rw [h₁, ← mul_assoc, h₂]
  linear_combination (-f τ) * hden - denom (Matrix.SpecialLinearGroup.mapGL ℝ h) τ ^ (-k) * h₃

/-- **The transformation law of the coefficients of a local section between the chart of `ψ` and
another chart.** Let `ψ` be a local linearizing coordinate at `z`, with exponent `r < m`
satisfying the frame condition, and let `f` satisfy the weight-`k` transformation law for `Γ'` and
be holomorphic on an open set `W`. Let the second chart have frame `F'` on an open set `U'`,
holomorphic there and compatible with the weight-`k` action of `Γ'`. If `τ` is a point of the
invariant disc lying in `W` and `h ∈ Γ'` moves it into `U'`, let `c'` be the coefficient of `f`
in the second chart near `h • τ`, read on the upper half-plane: `F' x * c' x = f x` for `x` near
`h • τ`. If `c'` is continuous at `h • τ`, then the coefficient of `f` in the chart of `ψ` at `τ`
is the transition function, the coefficient of the automorphic extension of `F'`, times
`c' (h • τ)`. This holds also at the centre `z`, where the frame of `ψ` may vanish; `W` need not
contain `h • τ`. The second chart may be that of another
local linearizing coordinate
(`Subgroup.LinearizingCoordinate.automorphyDescent_eq_mul_automorphyDescent`) or of a cusp. -/
theorem automorphyDescent_eq_automorphyDescent_automorphyExtension_mul
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hr : r < Nat.card (stabilizer Γ z)) (hU' : IsOpen U')
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ U', g • σ ∈ U' →
      F' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F' σ)
    (hF'd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F' U')
    (hW : IsOpen W) (hf : ∀ g ∈ Γ', ∀ σ : ℍ,
      f (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * f σ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W) {τ : stabilizerBall Γ z ε} (hτW : (τ : ℍ) ∈ W)
    {h : SL(2, ℝ)} (hh : h ∈ Γ') (hτ' : h • (τ : ℍ) ∈ U')
    (hc' : ∀ᶠ x in 𝓝 (h • (τ : ℍ)), F' x * c' x = f x) (hc'c : ContinuousAt c' (h • (τ : ℍ))) :
    ψ.automorphyDescent k r f (ψ.quotientCoordinate τ) =
      ψ.automorphyDescent k r (Γ'.automorphyExtension U' k F') (ψ.quotientCoordinate τ) *
        c' (h • τ) := by
  set E := Γ'.automorphyExtension U' k F'
  by_cases hF : ψ.automorphyFrame k r τ ≠ 0
  · exact ψ.automorphyDescent_eq_mul_of_automorphyFrame_ne_zero hΓ hk hr hU' hF' hF'd hW hf hfd
      hτW hh hτ' hc'.self_of_nhds hF
  -- At the centre both sides are continuous functions of the point, read on `ℂ` near `z`, which
  -- agree at every other point by the first case.
  have hz : (τ : ℍ) = z := ((ψ.automorphyFrame_eq_zero_iff k r τ).mp (not_not.mp hF)).1
  have hτb : (τ : ℍ) ∈ ball z ε := mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2)
  set M : ℂ → ℍ := fun t ↦ h • ofComplex t
  set L : ℂ → ℂ := fun t ↦ ψ.automorphyDescent k r f (ψ.quotientCoordinateOnComplex t)
  set R : ℂ → ℂ := fun t ↦ ψ.automorphyDescent k r E (ψ.quotientCoordinateOnComplex t) * c' (M t)
  have hM : M (τ : ℂ) = h • (τ : ℍ) := by simp only [M, ofComplex_apply]
  have hMc : ContinuousAt M (τ : ℂ) :=
    (continuous_const_smul h).continuousAt.comp
      (mdifferentiableAt_ofComplex (τ : ℍ).im_pos).continuousAt
  have hτq := ψ.quotientCoordinateOnComplex_coe τ
  have hLc : ContinuousAt L (τ : ℂ) := by
    refine ContinuousAt.comp (g := ψ.automorphyDescent k r f) ?_
      (ψ.differentiableAt_quotientCoordinateOnComplex hτb).continuousAt
    rw [hτq]
    exact (ψ.differentiableAt_automorphyDescent hΓ hk hW (fun g hg _ σ _ ↦ hf g hg σ)
      (hfd.mono inter_subset_right) hr.le hτW).continuousAt
  have hRc : ContinuousAt R (τ : ℂ) := by
    refine ContinuousAt.mul (ContinuousAt.comp (g := ψ.automorphyDescent k r E) ?_
      (ψ.differentiableAt_quotientCoordinateOnComplex hτb).continuousAt)
      (ContinuousAt.comp_of_eq hc'c hMc hM)
    rw [hτq]
    exact (ψ.differentiableAt_automorphyDescent_automorphyExtension hΓ hk hU' hF' hF'd hr.le hh
      hτ').continuousAt
  -- `L` and `R` agree near `τ` away from `τ`, where the frame of `ψ` does not vanish
  have hN : ((↑) : ℍ → ℂ) '' (ball z ε ∩ W ∩
      (fun x ↦ h • x) ⁻¹' {x | x ∈ U' ∧ F' x * c' x = f x}) ∈ 𝓝 (τ : ℂ) :=
    isOpenEmbedding_coe.isOpenMap.image_mem_nhds
      (Filter.inter_mem ((isOpen_ball.inter hW).mem_nhds ⟨hτb, hτW⟩)
        ((continuous_const_smul h).continuousAt.preimage_mem_nhds
          (Filter.inter_mem (hU'.mem_nhds hτ') hc')))
  have hev : L =ᶠ[𝓝[≠] (τ : ℂ)] R := by
    filter_upwards [nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with t ht htne
    obtain ⟨x, ⟨⟨hxb, hxW⟩, hxU', hxc⟩, rfl⟩ := ht
    let x₁ : stabilizerBall Γ z ε := ⟨x, (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hxb)⟩
    have hx₁ : ψ.automorphyFrame k r x₁ ≠ 0 := fun h0 ↦
      htne (congrArg ((↑) : ℍ → ℂ) (((ψ.automorphyFrame_eq_zero_iff k r x₁).mp h0).1.trans hz.symm))
    have e₁ : ψ.quotientCoordinateOnComplex (x : ℂ) = ψ.quotientCoordinate x₁ :=
      ψ.quotientCoordinateOnComplex_coe x₁
    have e₂ : M x = h • x := by simp only [M, ofComplex_apply]
    simp only [L, R]
    rw [e₁, e₂]
    exact ψ.automorphyDescent_eq_mul_of_automorphyFrame_ne_zero hΓ hk hr hU' hF' hF'd hW hf hfd
      (τ := x₁) hxW hh hxU' hxc hx₁
  have hLR : L (τ : ℂ) = R (τ : ℂ) :=
    tendsto_nhds_unique ((hLc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
      (hRc.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [L, R] at hLR
  rwa [hτq, hM] at hLR

variable {z' : ℍ} {ε' : ℝ} [Finite (stabilizer Γ z')] (ψ' : Γ.LinearizingCoordinate z' ε') {r' : ℕ}

/-- **The transformation law of the coefficients of a local section between two charts.** Let
`ψ` and `ψ'` be local linearizing coordinates at `z` and `z'`, with exponents `r < m` and
`r' < m'` satisfying the frame conditions, and let the disc of radius `ε'` about `z'` be precisely
invariant: an element of `Γ'` moving one of its points into it fixes `z'`; for a discrete `Γ'`
every small enough disc is (`TauCeti.eventually_smul_eq_self_of_image_smul_ball_inter_nonempty`).
Let `f` satisfy the weight-`k` transformation law for `Γ'` and be holomorphic on an open set `W`.
If `τ` is a point of the invariant disc about `z` lying in `W` and `σ = h • τ`, for `h ∈ Γ'`, is a
point of the invariant disc about `z'`, then the coefficient of `f` in the chart of `ψ` at `τ` is
the transition function, the coefficient of the automorphic extension of the frame of `ψ'`, times
the coefficient of `f` in the chart of `ψ'` at `σ`. This holds also at the centre `z`, where the
frame of `ψ` may vanish. -/
theorem automorphyDescent_eq_mul_automorphyDescent
    (hΓ : Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))) = Γ)
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hr : r < Nat.card (stabilizer Γ z))
    (hk' : ∀ g ∈ Γ', g • z' = z' →
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z' ^ (2 * r' + k) = 1)
    (hr' : r' < Nat.card (stabilizer Γ z'))
    (hprec' : ∀ g ∈ Γ', ∀ σ ∈ ball z' ε', g • σ ∈ ball z' ε' → g • z' = z')
    (hW : IsOpen W) (hf : ∀ g ∈ Γ', ∀ σ : ℍ,
      f (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * f σ)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W)
    {τ : stabilizerBall Γ z ε} (hτW : (τ : ℍ) ∈ W) {σ : stabilizerBall Γ z' ε'} {h : SL(2, ℝ)}
    (hh : h ∈ Γ') (hσ : (σ : ℍ) = h • (τ : ℍ)) :
    ψ.automorphyDescent k r f (ψ.quotientCoordinate τ) =
      ψ.automorphyDescent k r (Γ'.automorphyExtension (ball z' ε') k fun σ ↦
          ((σ : ℂ) - conj (z' : ℂ)) ^ (-k) * ψ'.toEquiv (UpperHalfPlane.discCoordinate z' σ) ^ r')
        (ψ.quotientCoordinate τ) * ψ'.automorphyDescent k r' f (ψ'.quotientCoordinate σ) := by
  have hσb : (σ : ℍ) ∈ ball z' ε' := mem_ball.mpr ((mem_stabilizerBall Γ z' ε').1 σ.2)
  -- by its transformation law, `f` is holomorphic on the saturation `Γ' • W`, which contains `σ`
  set W' := (Γ' : Set SL(2, ℝ)) • W
  have hW' : IsOpen W' := hW.smul_left
  have hfd' : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W' :=
    (mdifferentiableOn_automorphyExtension (fun g hg σ _ _ ↦ hf g hg σ) hW hfd).congr
      (eqOn_automorphyExtension hf fun _ _ ↦ rfl)
  have hτW' : (τ : ℍ) ∈ W' :=
    mem_smul_set_iff_exists_smul_mem.mpr ⟨1, Γ'.one_mem, by rwa [one_smul]⟩
  have hσW : (σ : ℍ) ∈ W' := mem_smul_set_iff_exists_smul_mem.mpr
    ⟨h⁻¹, Γ'.inv_mem hh, by rwa [hσ, inv_smul_smul]⟩
  -- the coefficient of `f` in the chart of `ψ'`, read on the upper half-plane
  have hc' (x : ℍ) (hx : x ∈ ball z' ε' ∩ W') :
      ((x : ℂ) - conj (z' : ℂ)) ^ (-k) * ψ'.toEquiv (UpperHalfPlane.discCoordinate z' x) ^ r' *
        ψ'.automorphyDescent k r' f (ψ'.quotientCoordinateOnComplex x) = f x := by
    have h := ψ'.automorphyFrame_mul_automorphyDescent_of_mem hΓ.ge hk' hW'
      (fun g hg _ σ _ ↦ hf g hg σ) (hfd'.mono inter_subset_right) hr'
      (τ := ⟨x, (mem_stabilizerBall Γ z' ε').2 (mem_ball.mp hx.1)⟩) hx.2
    rwa [automorphyFrame_eq_toEquiv_discCoordinate,
      ← ψ'.quotientCoordinateOnComplex_coe ⟨x, (mem_stabilizerBall Γ z' ε').2 (mem_ball.mp hx.1)⟩]
      at h
  have hc'c : ContinuousAt (fun x : ℍ ↦
      ψ'.automorphyDescent k r' f (ψ'.quotientCoordinateOnComplex x)) (σ : ℍ) := by
    refine ContinuousAt.comp (g := ψ'.automorphyDescent k r' f) ?_
      ((ψ'.differentiableAt_quotientCoordinateOnComplex hσb).continuousAt.comp
        continuous_coe.continuousAt)
    rw [ψ'.quotientCoordinateOnComplex_coe σ]
    exact (ψ'.differentiableAt_automorphyDescent hΓ.ge hk' hW' (fun g hg _ σ _ ↦ hf g hg σ)
      (hfd'.mono inter_subset_right) hr'.le hσW).continuousAt
  have h := ψ.automorphyDescent_eq_automorphyDescent_automorphyExtension_mul hΓ.ge hk hr
    isOpen_ball (ψ'.automorphyFrame_compatible hΓ.le hk' hprec')
    (ψ'.mdifferentiableOn_automorphyFrame k r') hW' hf hfd' hτW' hh (hσ ▸ hσb)
    (hσ ▸ Filter.mem_of_superset ((isOpen_ball.inter hW').mem_nhds ⟨hσb, hσW⟩) hc') (hσ ▸ hc'c)
  rwa [← hσ, ψ'.quotientCoordinateOnComplex_coe σ] at h

/-- **The cocycle law of the transition functions.** Let `ψ` and `ψ'` be as in
`Subgroup.LinearizingCoordinate.automorphyDescent_eq_mul_automorphyDescent`, and let `F''` be a
function on an open set `U''`, holomorphic there and compatible with the weight-`k` action of
`Γ'`, the frame of a third chart. On the triple overlap, the transition function from the chart of
`F''` to that of `ψ` is the product of the transition function from the chart of `ψ'` to that of
`ψ` and the transition function from the chart of `F''` to that of `ψ'`, read at the corresponding
point `σ = h • τ` of the chart of `ψ'`. -/
theorem automorphyDescent_automorphyExtension_eq_mul
    (hΓ : Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))) = Γ)
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hr : r < Nat.card (stabilizer Γ z))
    (hk' : ∀ g ∈ Γ', g • z' = z' →
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z' ^ (2 * r' + k) = 1)
    (hr' : r' < Nat.card (stabilizer Γ z'))
    (hprec' : ∀ g ∈ Γ', ∀ σ ∈ ball z' ε', g • σ ∈ ball z' ε' → g • z' = z')
    {U'' : Set ℍ} {F'' : ℍ → ℂ} (hU'' : IsOpen U'')
    (hF'' : ∀ g ∈ Γ', ∀ σ ∈ U'', g • σ ∈ U'' →
      F'' (g • σ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * F'' σ)
    (hF''d : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F'' U'')
    {τ : stabilizerBall Γ z ε} {σ : stabilizerBall Γ z' ε'} {h : SL(2, ℝ)} (hh : h ∈ Γ')
    (hσ : (σ : ℍ) = h • (τ : ℍ)) {h'' : SL(2, ℝ)} (hh'' : h'' ∈ Γ') (hτ : h'' • (τ : ℍ) ∈ U'') :
    ψ.automorphyDescent k r (Γ'.automorphyExtension U'' k F'') (ψ.quotientCoordinate τ) =
      ψ.automorphyDescent k r (Γ'.automorphyExtension (ball z' ε') k fun σ ↦
          ((σ : ℂ) - conj (z' : ℂ)) ^ (-k) * ψ'.toEquiv (UpperHalfPlane.discCoordinate z' σ) ^ r')
        (ψ.quotientCoordinate τ) *
        ψ'.automorphyDescent k r' (Γ'.automorphyExtension U'' k F'') (ψ'.quotientCoordinate σ) :=
  ψ.automorphyDescent_eq_mul_automorphyDescent ψ' hΓ hk hr hk' hr' hprec' hU''.smul_left
    (fun _ hg σ ↦ automorphyExtension_smul hF'' hg σ)
    (mdifferentiableOn_automorphyExtension hF'' hU'' hF''d)
    (mem_smul_set_iff_exists_smul_mem.mpr ⟨h'', hh'', hτ⟩) hh hσ

end LinearizingCoordinate

end Subgroup
