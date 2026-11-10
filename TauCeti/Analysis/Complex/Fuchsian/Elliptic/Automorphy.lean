/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Linearizing
public import TauCeti.Analysis.Complex.RootsOfUnity.TwistedDescent
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

open scoped ComplexConjugate Manifold MatrixGroups

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

/-- The untwisted local section is holomorphic on the set of coordinate values. -/
theorem differentiableOn_automorphyUntwist (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (ball z ε)) :
    DifferentiableOn ℂ (ψ.automorphyUntwist k f) ψ.toEquiv.target := by
  intro u hu
  obtain ⟨τ, rfl⟩ := (ψ.mem_target_iff u).mp hu
  have hτ : (τ : ℍ) ∈ ball z ε := mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2)
  have hP := ψ.differentiableAt_pointOf hu
  have hF : DifferentiableAt ℂ (f ∘ ofComplex) (ψ.pointOf (ψ.coordinate τ)) := by
    rw [pointOf_coordinate]
    exact mdifferentiableAt_iff.mp ((hfd τ hτ).mdifferentiableAt (isOpen_ball.mem_nhds hτ))
  have hne : ψ.pointOf (ψ.coordinate τ) - conj (z : ℂ) ≠ 0 := by
    rw [pointOf_coordinate]
    exact coe_sub_conj_ne_zero z τ
  exact (((hP.sub_const _).zpow (Or.inl hne)).mul (hF.comp _ hP)).differentiableWithinAt

/-- The untwisted local section transforms by the character `ζ ↦ ζ ^ r` of the rotations, when
`denom g z ^ (2 * r + k) = 1` for the elements `g ∈ Γ'` fixing `z`. -/
theorem automorphyUntwist_smul (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', g • z = z → denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ (2 * r + k) = 1)
    (hf : ∀ g ∈ Γ', g • z = z → ∀ τ ∈ ball z ε,
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
    {u : ℂ} (hu : u ∈ ψ.toEquiv.target) (ζ : rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ) :
    ψ.automorphyUntwist k f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • ψ.automorphyUntwist k f u := by
  obtain ⟨τ, rfl⟩ := (ψ.mem_target_iff u).mp hu
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
    hf g hgΓ' hgz τ (mem_ball.mpr ((mem_stabilizerBall Γ z ε).1 τ.2)), ← hq,
    coe_stabilizerRotation_eq_denom_zpow q hgq, smul_eq_mul]
  linear_combination
    ((((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ k * f τ * c₀ ^ k) * h₂ +
      ((((τ : ℍ) : ℂ) - conj (z : ℂ)) ^ k * f τ) * h₁

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
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  rw [quotientImage_def]
  exact differentiableOn_descendPowTwist ψ.isOpen_target hr
    (ψ.differentiableOn_automorphyUntwist hfd)
    fun u hu ↦ ψ.automorphyUntwist_smul hΓ hk hf hu

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
    ψ.automorphyFrame k r τ * ψ.automorphyDescent k r f (ψ.quotientCoordinate τ) = f τ := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  have h := pow_smul_descendPowTwist_pow ψ.isOpen_target hr
    (ψ.differentiableOn_automorphyUntwist hfd)
    (fun u hu ↦ ψ.automorphyUntwist_smul hΓ hk hf hu) ((ψ.mem_target_iff _).mpr ⟨τ, rfl⟩)
  rw [automorphyUntwist_coordinate, smul_eq_mul] at h
  refine mul_left_cancel₀ (zpow_ne_zero k (coe_sub_conj_ne_zero z τ)) ?_
  rw [← mul_assoc, zpow_mul_automorphyFrame, automorphyDescent_def, quotientCoordinate_def, h]

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
  have hτ' : τ ∈ stabilizerBall Γ z ε := (mem_stabilizerBall Γ z ε).2 (mem_ball.mp hτ)
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
  set m := Nat.card (stabilizer Γ z) with hm
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
  set m := Nat.card (stabilizer Γ z) with hm
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
  set m := Nat.card (stabilizer Γ z) with hm
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

end LinearizingCoordinate

end Subgroup
