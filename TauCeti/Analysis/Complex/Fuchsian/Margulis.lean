/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import TauCeti.Analysis.Complex.Fuchsian.Jorgensen
import TauCeti.Analysis.Complex.UpperHalfPlane.Displacement
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# The Margulis lemma for Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup. Two elements of `Γ` that both move some point
`z ∈ ℍ` a small distance cannot be in general position: if one of them, `g`, fixes no point of
`ℍ`, then the other, `h`, conjugates `g` to itself or to its inverse. Thus `h` fixes the fixed point
of `g` on the ideal boundary when `g` is parabolic, and preserves the pair of fixed points of `g`
when `g` is hyperbolic. This is the Margulis lemma for discrete subgroups of `PSL(2, ℝ)`, in the
pairwise form used to describe the thin part of a Fuchsian quotient: the points moved a small
distance by some nonidentity element.

The proof combines Jørgensen's inequality
`Subgroup.one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two`, which bounds
`|tr² A - 4| + |tr [A, B] - 2|` below by `1` outside these exceptional cases, with two upper bounds
in terms of the displacements `δ_A = dist (A • z) z` and `δ_B = dist (B • z) z`:

* `|tr [A, B] - 2| ≤ 4 (cosh δ_A cosh δ_B - 1)`
  (`Matrix.SpecialLinearGroup.abs_trace_commutatorElement_sub_two_le`), and
* `tr² A - 4 ≤ 2 (cosh δ_A - 1)` (`Matrix.SpecialLinearGroup.trace_sq_sub_four_le`).

The first bound holds for all `A` and `B`. The second controls `|tr² A - 4|` only when
`tr² A ≥ 4`, that is when `A` is not elliptic. An elliptic element rotating through a large angle
about a point near `z` moves `z` very little while `4 - tr² A` stays large, so the general
statement keeps `|tr² A - 4|` as a hypothesis, and the fixed-point-free statement uses the
explicit radius `1 / 4`.

## Main results

* `Subgroup.conj_eq_or_conj_eq_inv_of_cosh_dist`: if
  `|tr² A - 4| + 4 (cosh δ_A cosh δ_B - 1) < 1`, then `B A B⁻¹ = A` or `B A B⁻¹ = A⁻¹`.
* `Subgroup.conj_eq_or_conj_eq_inv_of_dist_le`: **the Margulis lemma.** If `g, h ∈ Γ` both move
  `z` a distance at most `1 / 4` and `g` fixes no point of `ℍ`, then `h g h⁻¹ = g` or
  `h g h⁻¹ = g⁻¹`.

## References

* Troels Jørgensen, *On discrete groups of Möbius transformations*, American Journal of
  Mathematics 98 (1976), 739–749.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §5.4 (Jørgensen's inequality and its consequences).
* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the Margulis lemma and the thick-thin decomposition).
-/

public section

open scoped MatrixGroups UpperHalfPlane

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- **Two elements moving a point a small distance, in trace form.** Let `Γ ≤ PSL(2, ℝ)` be a
discrete subgroup, let `A, B ∈ SL(2, ℝ)` lift elements of `Γ`, and let `z ∈ ℍ`. If
`|tr² A - 4| + 4 (cosh (dist (A • z) z) cosh (dist (B • z) z) - 1) < 1`, then `B` conjugates the
class of `A` to itself or to its inverse in `PSL(2, ℝ)`. -/
theorem conj_eq_or_conj_eq_inv_of_cosh_dist [DiscreteTopology Γ] {A B : SL(2, ℝ)}
    (hA : (A : PSL(2, ℝ)) ∈ Γ) (hB : (B : PSL(2, ℝ)) ∈ Γ) (z : ℍ)
    (h : |(A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 - 4| +
      4 * (Real.cosh (dist (A • z) z) * Real.cosh (dist (B • z) z) - 1) < 1) :
    (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ = A ∨
      (B : PSL(2, ℝ)) * A * (B : PSL(2, ℝ))⁻¹ = (A : PSL(2, ℝ))⁻¹ := by
  by_contra hne
  rw [not_or] at hne
  have hJ := one_le_abs_trace_sq_sub_four_add_abs_trace_commutatorElement_sub_two hA hB hne.1
    hne.2
  have hC := Matrix.SpecialLinearGroup.abs_trace_commutatorElement_sub_two_le A B z
  linarith

/-- **The Margulis lemma for Fuchsian groups.** Let `Γ ≤ PSL(2, ℝ)` be a discrete subgroup and let
`g, h ∈ Γ` both move a point `z ∈ ℍ` a distance at most `1 / 4`. If `g` fixes no point of `ℍ`, that
is, if `g` is parabolic or hyperbolic, then `h g h⁻¹ = g` or `h g h⁻¹ = g⁻¹`. -/
theorem conj_eq_or_conj_eq_inv_of_dist_le [DiscreteTopology Γ] {g h : PSL(2, ℝ)} (hg : g ∈ Γ)
    (hh : h ∈ Γ) (hfix : ∀ w : ℍ, g • w ≠ w) {z : ℍ} (hgz : dist (g • z) z ≤ 1 / 4)
    (hhz : dist (h • z) z ≤ 1 / 4) :
    h * g * h⁻¹ = g ∨ h * g * h⁻¹ = g⁻¹ := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective h
  rw [UpperHalfPlane.pslMk_smul] at hgz hhz
  -- `A` is not elliptic, since an elliptic element fixes a point of `ℍ`
  have htr : 4 ≤ (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 := by
    by_contra hlt
    have hell : |(A : Matrix (Fin 2) (Fin 2) ℝ).trace| < 2 := by
      rw [← abs_two, ← sq_lt_sq]
      norm_num
      linarith
    have hellA : (Matrix.SpecialLinearGroup.mapGL ℝ A).IsElliptic :=
      (Matrix.isElliptic_iff_abs_trace_lt_two A.det_coe).2 hell
    refine hfix (UpperHalfPlane.fixedPt _ hellA) ?_
    rw [UpperHalfPlane.pslMk_smul]
    exact (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt (by simp) hellA).2 rfl
  -- on `[0, 1 / 4]` the hyperbolic cosine is at most `cosh (1 / 4) ≤ exp (1 / 32) ≤ 32 / 31`
  have hcosh : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → Real.cosh δ ≤ 32 / 31 := fun δ h₀ h =>
    calc Real.cosh δ ≤ Real.cosh (1 / 4) := by
          rw [Real.cosh_le_cosh, abs_of_nonneg h₀, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
          exact h
      _ ≤ Real.exp ((1 / 4) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ ≤ 1 / (1 - (1 / 4) ^ 2 / 2) :=
          Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 32 / 31 := by norm_num
  have hcA := hcosh _ dist_nonneg hgz
  have hcB := hcosh _ dist_nonneg hhz
  have h1A := Real.one_le_cosh (dist (A • z) z)
  have h1B := Real.one_le_cosh (dist (B • z) z)
  have htrA := Matrix.SpecialLinearGroup.trace_sq_sub_four_le A z
  refine conj_eq_or_conj_eq_inv_of_cosh_dist hg hh z ?_
  rw [abs_of_nonneg (by linarith)]
  nlinarith

end Subgroup
