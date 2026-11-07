/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Wronskian
public import TauCeti.RingTheory.Valuation.LeadingTerm

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# The leading term of the `x`-coordinate of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `F`, with `x ∘ φ = N(x) / D(x)`
for `N / D = φ.xRatFunc` in lowest terms, `D` monic. The degree of `φ` is the degree of `N`, which
exceeds that of `D`. Suppose that `φ` pulls the invariant differential back as `φ^*ω₂ = c ω₁`
with `c ≠ 0`, that is, `φ` is separable, and that `2 ≠ 0` in `F`. Then

  `deg N = deg D + 1`  and  `leadingCoeff N · c² = 1`,

so that `x ∘ φ = c⁻² x + O(1)` near the point at infinity. In terms of the parameter `z = -x / y`
at infinity, `z ∘ φ = c z + O(z²)`, which is the expansion of `φ` on formal groups to first order
(Silverman IV.4); the statement here is about `x` alone and needs no formal group.

Both identities are read off the top coefficient of the Wronskian identity
`w² Ψ₂Sq₁ = c² D (4N³ + b₂'N²D + 2b₄'ND² + b₆'D³)` of
`TauCeti.Isogeny.wronskian_xRatFunc_sq_mul_Ψ₂Sq`, where `w = D N' - D' N`. Its right-hand side has
degree `3 deg N + deg D`, and its left-hand side has degree at most `2 (deg N + deg D - 1) + 3`,
which forces `deg N = deg D + 1`; the top coefficient of `w` is then `leadingCoeff N`.

Consequently, over a field with a valuation `v`, an isogeny scales the value of the
`x`-coordinate of a point close to the point at infinity by `v c⁻²`: there is a bound `R` such
that every affine point `P = (x₀, y₀)` of `W₁` with `R < v x₀` has an affine image with
`v (x(φ P)) · v c ² = v x₀`. Over a complete discretely valued field this says that `φ` carries
the points of `W₁` at depth `k` in the kernel of reduction, for `k` large, to points of `W₂` at
depth `k + v(c)`. This is the step at which the differential constant `|c|` enters the local
factor `[E₂(K_v) : φ E₁(K_v)] / #E₁(K_v)[φ]` of Cassels' isogeny invariance of the
Birch–Swinnerton-Dyer quotient at a place dividing `deg φ`.

## Main results

* `TauCeti.Isogeny.degree_eq_natDegree_num_xRatFunc`: `deg φ = deg N`.
* `TauCeti.Isogeny.natDegree_num_xRatFunc_eq_succ`: for separable `φ` and `2 ≠ 0`,
  `deg N = deg D + 1`.
* `TauCeti.Isogeny.leadingCoeff_num_xRatFunc_mul_sq`: under the same hypotheses,
  `leadingCoeff N · c² = 1`.
* `TauCeti.Isogeny.exists_valuation_xCoord_pointMap_mul_sq`: near the point at infinity, `φ`
  multiplies the value of the `x`-coordinate by `v c⁻²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, III.5 and IV.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), 79–114,
  Lemma 3.8.
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
  [W₂.IsElliptic]

/-- **The degree of an isogeny is the degree of the numerator of its `x`-coordinate**, since the
numerator of `φ.xRatFunc` has larger degree than its denominator. -/
theorem degree_eq_natDegree_num_xRatFunc (φ : Isogeny W₁ W₂) :
    φ.degree = φ.xRatFunc.num.natDegree := by
  rw [degree_eq_max_natDegree_xRatFunc,
    max_eq_left (natDegree_denom_lt_natDegree_num_xRatFunc φ).le]

omit [W₁.IsElliptic] [W₂.IsElliptic] in
private theorem four_ne_zero_of_two_ne_zero (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

section Separable

variable {φ : Isogeny W₁ W₂} {c : F}
  (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁)
  (hc0 : c ≠ 0) (h2 : (2 : F) ≠ 0)
include hc hc0 h2

omit hc in
/-- The right-hand side of the Wronskian identity has degree `deg D + 3 deg N` and leading
coefficient `4 c² · leadingCoeff N ³`: its term `4 c² D N³` dominates. -/
private theorem natDegree_and_leadingCoeff_rhs :
    (C (c ^ 2) * φ.xRatFunc.denom *
        (C 4 * φ.xRatFunc.num ^ 3 + C W₂.b₂ * φ.xRatFunc.num ^ 2 * φ.xRatFunc.denom +
          C (2 * W₂.b₄) * φ.xRatFunc.num * φ.xRatFunc.denom ^ 2 +
            C W₂.b₆ * φ.xRatFunc.denom ^ 3)).natDegree =
        φ.xRatFunc.denom.natDegree + 3 * φ.xRatFunc.num.natDegree ∧
      (C (c ^ 2) * φ.xRatFunc.denom *
        (C 4 * φ.xRatFunc.num ^ 3 + C W₂.b₂ * φ.xRatFunc.num ^ 2 * φ.xRatFunc.denom +
          C (2 * W₂.b₄) * φ.xRatFunc.num * φ.xRatFunc.denom ^ 2 +
            C W₂.b₆ * φ.xRatFunc.denom ^ 3)).leadingCoeff =
        c ^ 2 * 4 * φ.xRatFunc.num.leadingCoeff ^ 3 := by
  set N := φ.xRatFunc.num
  set D := φ.xRatFunc.denom
  have had : D.natDegree < N.natDegree := natDegree_denom_lt_natDegree_num_xRatFunc φ
  have hD : D.Monic := φ.xRatFunc.monic_denom
  have hN : N ≠ 0 := ne_zero_of_natDegree_gt had
  have hc4 : c ^ 2 * 4 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc0) (four_ne_zero_of_two_ne_zero h2)
  set P := C (c ^ 2 * 4) * (D * N ^ 3)
  set E := C (c ^ 2) * D * (C W₂.b₂ * N ^ 2 * D + C (2 * W₂.b₄) * N * D ^ 2 + C W₂.b₆ * D ^ 3)
  have hsplit : C (c ^ 2) * D * (C 4 * N ^ 3 + C W₂.b₂ * N ^ 2 * D +
      C (2 * W₂.b₄) * N * D ^ 2 + C W₂.b₆ * D ^ 3) = P + E := by
    simp only [P, E, C_mul]
    ring
  have hP : P.natDegree = D.natDegree + 3 * N.natDegree := by
    rw [natDegree_C_mul hc4, natDegree_mul hD.ne_zero (pow_ne_zero 3 hN), natDegree_pow]
  have hPlc : P.leadingCoeff = c ^ 2 * 4 * N.leadingCoeff ^ 3 := by
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hc4), leadingCoeff_mul,
      hD.leadingCoeff, leadingCoeff_pow, one_mul]
  have hE : E.natDegree < P.natDegree := by
    have hb₂ : (C W₂.b₂ * N ^ 2 * D).natDegree ≤ 2 * N.natDegree + D.natDegree :=
      natDegree_mul_le_of_le (natDegree_C_mul_le _ _ |>.trans (natDegree_pow_le_of_le 2 le_rfl))
        le_rfl
    have hb₄ : (C (2 * W₂.b₄) * N * D ^ 2).natDegree ≤ N.natDegree + 2 * D.natDegree :=
      natDegree_mul_le_of_le (natDegree_C_mul_le _ _) (natDegree_pow_le_of_le 2 le_rfl)
    have hb₆ : (C W₂.b₆ * D ^ 3).natDegree ≤ 3 * D.natDegree :=
      natDegree_C_mul_le _ _ |>.trans (natDegree_pow_le_of_le 3 le_rfl)
    have hS : (C W₂.b₂ * N ^ 2 * D + C (2 * W₂.b₄) * N * D ^ 2 + C W₂.b₆ * D ^ 3).natDegree ≤
        2 * N.natDegree + D.natDegree :=
      natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hb₂ (hb₄.trans (by omega)))
        (hb₆.trans (by omega))
    have : E.natDegree ≤ D.natDegree + (2 * N.natDegree + D.natDegree) :=
      natDegree_mul_le_of_le (natDegree_C_mul_le (c ^ 2) D) hS
    rw [hP]
    omega
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt hE, hP,
    leadingCoeff_add_of_degree_lt' (degree_lt_degree hE), hPlc]
  exact ⟨rfl, rfl⟩

/-- The numerator of `φ.xRatFunc` has degree one more than its denominator, when
`φ^*ω₂ = c ω₁` with `c ≠ 0` and `2 ≠ 0` in `F`. -/
private theorem natDegree_num_xRatFunc_eq_succ_of_eq_smul :
    φ.xRatFunc.num.natDegree = φ.xRatFunc.denom.natDegree + 1 := by
  have had : φ.xRatFunc.denom.natDegree < φ.xRatFunc.num.natDegree :=
    natDegree_denom_lt_natDegree_num_xRatFunc φ
  have hw := wronskian_xRatFunc_ne_zero hc hc0
  have hwdeg := natDegree_wronskian_lt_add hw
  have hlhs : (wronskian φ.xRatFunc.denom φ.xRatFunc.num ^ 2 * W₁.Ψ₂Sq).natDegree ≤
      2 * (wronskian φ.xRatFunc.denom φ.xRatFunc.num).natDegree + 3 :=
    natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 le_rfl) W₁.natDegree_Ψ₂Sq_le
  rw [wronskian_xRatFunc_sq_mul_Ψ₂Sq hc, (natDegree_and_leadingCoeff_rhs (φ := φ) hc0 h2).1] at hlhs
  omega

/-- The top coefficient of the Wronskian `D N' - D' N`, at degree `2 deg D`, is the leading
coefficient of `N`, when `D` is monic and `deg N = deg D + 1`. -/
private theorem coeff_wronskian_xRatFunc :
    (wronskian φ.xRatFunc.denom φ.xRatFunc.num).coeff (2 * φ.xRatFunc.denom.natDegree) =
      φ.xRatFunc.num.leadingCoeff := by
  set N := φ.xRatFunc.num
  set D := φ.xRatFunc.denom
  set d := D.natDegree with hd
  have hN : N.natDegree = d + 1 := natDegree_num_xRatFunc_eq_succ_of_eq_smul hc hc0 h2
  have hD : D.Monic := φ.xRatFunc.monic_denom
  have hDN' : (D * derivative N).coeff (d + d) = (d + 1) * N.leadingCoeff := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl (natDegree_derivative_le N |>.trans (by omega)),
      coeff_derivative, ← hd, hD.coeff_natDegree, leadingCoeff, hN]
    ring
  have hD'N : (derivative D * N).coeff (d + d) = d * N.leadingCoeff := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [derivative_of_natDegree_zero h0, zero_mul, coeff_zero, h0, Nat.cast_zero, zero_mul]
    · have hdd : d + d = (d - 1) + (d + 1) := by omega
      rw [hdd, coeff_mul_add_eq_of_natDegree_le (natDegree_derivative_le D |>.trans le_rfl) hN.le,
        coeff_derivative, Nat.sub_add_cancel h0, ← hd, hD.coeff_natDegree, leadingCoeff, hN,
        Nat.cast_sub h0]
      push_cast
      ring
  rw [two_mul, wronskian, coeff_sub, hDN', hD'N]
  ring

/-- **The leading coefficient of the `x`-coordinate of a separable isogeny is `c⁻²`**: if
`φ^*ω₂ = c ω₁` with `c ≠ 0` and `2 ≠ 0` in `F`, then the leading coefficient of the numerator of
`φ.xRatFunc`, whose denominator is monic, is `c⁻²`. So `x ∘ φ = c⁻² x + O(1)` near the point at
infinity, the first-order form of `z ∘ φ = c z + O(z²)` (Silverman IV.4). -/
theorem leadingCoeff_num_xRatFunc_mul_sq : φ.xRatFunc.num.leadingCoeff * c ^ 2 = 1 := by
  set N := φ.xRatFunc.num
  set D := φ.xRatFunc.denom
  set d := D.natDegree with hd
  have hN : N.natDegree = d + 1 := natDegree_num_xRatFunc_eq_succ_of_eq_smul hc hc0 h2
  have hN0 : N.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (n := d) (by omega))
  have hw : wronskian D N ≠ 0 := wronskian_xRatFunc_ne_zero hc hc0
  have hwdeg : (wronskian D N).natDegree ≤ 2 * d := by
    have : (wronskian D N).natDegree < d + N.natDegree := natDegree_wronskian_lt_add hw
    omega
  have h := congrArg (coeff · (2 * (2 * d) + 3)) (wronskian_xRatFunc_sq_mul_Ψ₂Sq hc)
  obtain ⟨hdeg, hlc⟩ := natDegree_and_leadingCoeff_rhs (φ := φ) hc0 h2
  rw [coeff_mul_add_eq_of_natDegree_le (natDegree_pow_le_of_le 2 hwdeg) W₁.natDegree_Ψ₂Sq_le,
    coeff_pow_of_natDegree_le hwdeg, coeff_wronskian_xRatFunc hc hc0 h2,
    WeierstrassCurve.coeff_Ψ₂Sq, show 2 * (2 * d) + 3 = d + 3 * N.natDegree by omega, ← hdeg,
    coeff_natDegree, hlc] at h
  have h4 : (4 : F) * N.leadingCoeff ^ 2 ≠ 0 :=
    mul_ne_zero (four_ne_zero_of_two_ne_zero h2) (pow_ne_zero 2 hN0)
  apply mul_left_cancel₀ h4
  linear_combination -h

/-- **Near the point at infinity, a separable isogeny divides the value of `x` by `v c ²`**: for a
valuation `v` on `F`, if `φ^*ω₂ = c ω₁` with `c ≠ 0` and `2 ≠ 0` in `F`, there is a bound `R` such
that every affine point `(x₀, y₀)` of `W₁` with `R < v x₀` is sent by `φ` to an affine point whose
`x`-coordinate `x₁` satisfies `v x₁ · v c ² = v x₀`. -/
theorem exists_valuation_xCoord_pointMap_mul_sq [DecidableEq F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) :
    ∃ R : Γ₀, ∀ (x y : F) (h : W₁.Nonsingular x y), R < v x →
      (Hom.ofIsogeny φ).pointMap (.some x y h) ≠ 0 ∧
        v (Point.xCoord ((Hom.ofIsogeny φ).pointMap (.some x y h))) * v c ^ 2 = v x := by
  set N := φ.xRatFunc.num
  set D := φ.xRatFunc.denom
  have hN : N.natDegree = D.natDegree + 1 := natDegree_num_xRatFunc_eq_succ_of_eq_smul hc hc0 h2
  have hD : D.Monic := φ.xRatFunc.monic_denom
  obtain ⟨RN, hRN⟩ := v.exists_map_eval_eq_leadingCoeff_mul_pow N
  obtain ⟨RD, hRD⟩ := v.exists_map_eval_eq_leadingCoeff_mul_pow D
  refine ⟨max RN RD, fun x y h hx ↦ ?_⟩
  have hx0 : v x ≠ 0 := ((zero_le (a := RN)).trans_lt ((le_max_left _ _).trans_lt hx)).ne'
  have hvD : v (D.eval x) = v x ^ D.natDegree := by
    rw [hRD x ((le_max_right _ _).trans_lt hx), hD.leadingCoeff, v.map_one, one_mul]
  have hDx : D.eval x ≠ 0 := by
    rw [← v.ne_zero_iff, hvD]
    exact pow_ne_zero _ hx0
  refine ⟨(pointMap_ofIsogeny_some_eq_zero_iff h).not.mpr hDx, ?_⟩
  rw [xCoord_pointMap_ofIsogeny_some h hDx, map_div₀, hvD, hRN x ((le_max_left _ _).trans_lt hx),
    hN, pow_succ]
  have hlc : v N.leadingCoeff * v c ^ 2 = 1 := by
    rw [← map_pow, ← map_mul, leadingCoeff_num_xRatFunc_mul_sq hc hc0 h2, v.map_one]
  rw [mul_comm (v x ^ D.natDegree) (v x), ← mul_assoc, mul_div_assoc,
    div_self (pow_ne_zero _ hx0), mul_one, mul_right_comm, hlc, one_mul]

end Separable

/-- **The `x`-coordinate of a separable isogeny has a simple pole at infinity**: when `2 ≠ 0` in
`F`, the numerator of `φ.xRatFunc` has degree one more than its denominator, so
`deg φ = deg D + 1` for the denominator `D`. -/
theorem natDegree_num_xRatFunc_eq_succ (φ : Isogeny W₁ W₂)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] (h2 : (2 : F) ≠ 0) :
    φ.xRatFunc.num.natDegree = φ.xRatFunc.denom.natDegree + 1 := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  exact natDegree_num_xRatFunc_eq_succ_of_eq_smul hc
    ((isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul φ hc).mp ‹_›) h2

end TauCeti.Isogeny
