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
`f (g • τ) = denom g τ ^ k * f τ` for the elements `g ∈ Γ'` fixing `z` is a local section, near
the orbit of `z`, of the weight-`k` automorphy sheaf on the quotient `Γ \ ℍ`. This file computes
that sheaf in the chart at the orbit of `z` given by a local linearizing coordinate `ψ`, with
local quotient coordinate `w = u ^ m` for the coordinate `u` of `ψ`: its local sections are the
multiples of the single frame

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
  (`Subgroup.LinearizingCoordinate.analyticOrderAt_automorphyUntwist`).

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
condition on `r` holds as soon as `2 * m ∣ 2 * r + k`, that is `r ≡ -k / 2` modulo `m`; at
elliptic points of orders two and three these exponents are the source of the corrections
`⌊k / 4⌋` and `⌊k / 3⌋` in the dimension formulas of Diamond–Shurman §3.5.

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
* `Subgroup.denom_zpow_eq_one_of_dvd`: for a lift `g` of an element of `Γ` fixing `z`,
  `denom g z ^ n = 1` whenever `2 * m ∣ n`.

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

/-- **The automorphy factor at a fixed point is a root of unity.** If the image of
`g ∈ SL(2, ℝ)` lies in the stabilizer of `z`, of order `m`, then `denom g z ^ (2 * m) = 1`, since
the image rotates the disc coordinate by `denom g z ^ (-2)`, an `m`-th root of unity. Hence
`denom g z ^ n = 1` whenever `2 * m ∣ n`. With `n = 2 * r + k` this is the condition on the
exponent `r` of the frame; for even `k` such an `r < m` exists, `r ≡ -k / 2` modulo `m`. -/
theorem denom_zpow_eq_one_of_dvd {g : SL(2, ℝ)}
    (hg : (g : PSL(2, ℝ)) ∈ Γ) (hgz : g • z = z) {n : ℤ}
    (hdvd : (2 * Nat.card (stabilizer Γ z) : ℤ) ∣ n) :
    denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z ^ n = 1 := by
  let q : stabilizer Γ z := ⟨⟨g, hg⟩, by rw [mem_stabilizer_iff, Subgroup.mk_smul, pslMk_smul, hgz]⟩
  have hroot : ((stabilizerRotation Γ z q : ℂˣ) : ℂ) ^ Nat.card (stabilizer Γ z) = 1 := by
    rw [← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity _ _).mp (stabilizerRotation Γ z q).2, Units.val_one]
  rw [coe_stabilizerRotation_eq_denom_zpow q rfl, ← zpow_natCast, ← zpow_mul] at hroot
  obtain ⟨t, ht⟩ := hdvd
  rw [ht, show (2 * Nat.card (stabilizer Γ z) : ℤ) * t = (-2 * Nat.card (stabilizer Γ z)) * -t by
    ring, zpow_mul, hroot, one_zpow]

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
    rw [zpow_neg_two_pow_eq_zpow₀ (denom_ne_zero _ _) hk]
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
  have hw : ψ.toEquiv.invFun (ψ.coordinate τ) ∈ ball (0 : ℂ) 1 :=
    ball_subset_ball (Real.tanh_lt_one _).le (ψ.mem_ball_invFun hu)
  have hP : DifferentiableAt ℂ ψ.pointOf (ψ.coordinate τ) :=
    (analyticOnNhd_discCoordinateHomeomorph_symm z _ hw).differentiableAt.comp _
      (ψ.differentiableOn_invFun.differentiableAt (ψ.isOpen_target.mem_nhds hu))
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
    (zpow_neg_two_pow_eq_zpow₀ (denom_ne_zero _ _) (hk g hgΓ' hgz)).symm
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
  have h0 : (0 : ℂ) ∈ ψ.toEquiv.target := (ψ.mem_target_iff 0).mpr
    ⟨⟨z, (mem_stabilizerBall Γ z ε).2 (by rw [dist_self]; exact ψ.ε_pos)⟩,
      ((ψ.coordinate_eq_zero_iff _).mpr rfl).symm⟩
  exact analyticOrderAt_eq_add_analyticOrderAt_descendPowTwist_mul ψ.isOpen_target h0 hr
    (ψ.differentiableOn_automorphyUntwist hfd) fun u hu ↦ ψ.automorphyUntwist_smul hΓ hk hf hu

end LinearizingCoordinate

end Subgroup
