/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.FormalPoint
public import TauCeti.RingTheory.PowerSeries.EulerDiffDerivation

/-!
# The canonical differential of the Tate curve

On the formal neighbourhood `R⟦u⟧⟦v⟧` of the node of the Tate curve, with `q = u v`, the formal
Tate point `(X, Y)` (`TauCeti.tateFormalX`, `TauCeti.tateFormalY`) is the expansion of the Tate
uniformisation `u ↦ (X(u), Y(u))`. The parameter `u` is multiplicative, so the natural
differential on the source is `du / u`, and the derivation dual to it at fixed `q` is
`u ∂/∂u - v ∂/∂v` (`PowerSeries.eulerDiffDerivation`): it sends `uᵃ vᵇ` to `(a - b) uᵃ vᵇ`, so it
kills every series in `q = u v`, in particular the coefficients `a₄(q)` and `a₆(q)` of the curve.

The main results say that the Weierstrass invariant differential
`ω = dx / (2y + a₁x + a₃) = -dy / (a₁y - 3x² - 2a₂x - a₄)` pulls back to `du / u`:

`(u ∂/∂u - v ∂/∂v) X = 2Y + X`  and  `(u ∂/∂u - v ∂/∂v) Y = 3X² + a₄(q) - Y`.

In terms of the partial derivatives `W_X` and `W_Y` of the Weierstrass polynomial, these are
`W_Y(X, Y) = D X` and `W_X(X, Y) = -D Y`. This is the canonical differential of the Tate curve,
the trivialisation of the Hodge line `ω` with respect to which the Tate curve's `q`-expansions are
taken. Over a complete non-archimedean field it is the identity `u X'(u) = 2Y(u) + X(u)` for the
analytic Tate coordinates; this file proves only the formal identity, for every commutative
coefficient ring, including residue characteristics `2` and `3`.

The derivation anticommutes with the exchange `u ↔ v` (`PowerSeries.swap_eulerDiffDerivation`),
which maps the formal Tate point to its negative: inversion `u ↦ u⁻¹` changes the sign of
`du / u`, as the automorphism `[-1]` changes the sign of `ω`.

## Main results

* `TauCeti.eulerDiffDerivation_tateParamHom`: it kills the substitution `q = u v`.
* `TauCeti.eulerDiffDerivation_tateFormalX`: `D X = 2Y + X`.
* `TauCeti.eulerDiffDerivation_tateFormalY`: `D Y = 3X² + a₄(q) - Y`.
* `TauCeti.evalEval_polynomialY_tateFormalX_tateFormalY` and
  `TauCeti.evalEval_polynomialX_tateFormalX_tateFormalY`: `W_Y(X, Y) = D X` and
  `W_X(X, Y) = -D Y`, so `ω = dx / W_Y = -dy / W_X` pulls back to `du / u`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.1.
* N. M. Katz, *p-adic properties of modular schemes and modular forms*, in *Modular functions of
  one variable III*, Lecture Notes in Math. 350, Springer (1973), Appendix 1.
-/

public section

open PowerSeries

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The derivation `u ∂/∂u - v ∂/∂v` kills every series in `q = u v`. -/
@[simp]
theorem eulerDiffDerivation_tateParamHom (g : ℤ⟦X⟧) :
    eulerDiffDerivation R (tateParamHom R g) = 0 := by
  ext b a
  rw [coeff_coeff_eulerDiffDerivation, coeff_coeff_tateParamHom]
  split_ifs with h
  · simp [h]
  · simp

/-- **The canonical differential, first coordinate**: `(u ∂/∂u - v ∂/∂v) X = 2Y + X` for the formal
Tate point `(X, Y)`. Since `a₁ = 1` and `a₃ = 0`, this says that `dx / (2y + a₁x + a₃)` pulls back
to `du / u`. -/
@[simp]
theorem eulerDiffDerivation_tateFormalX :
    eulerDiffDerivation R (tateFormalX R) = 2 * tateFormalY R + tateFormalX R := by
  -- Twice the coefficient `n (n - 1) / 2` of `y` is `n (n - 1)`.
  have hchoose (n : ℕ) : 2 * ((n.choose 2 : ℕ) : R) = n * (n - 1) := by
    rcases n with _ | n
    · simp
    · have h : (n + 1) * n = (n + 1).choose 2 * 2 := by
        simpa using Nat.add_one_mul_choose_eq n 1
      have h' := congrArg (Nat.cast : ℕ → R) h
      push_cast at h' ⊢
      linear_combination -h'
  ext b a
  rw [coeff_coeff_eulerDiffDerivation, map_add, map_add, coeff_coeff_tateFormalX,
    coeff_ofNat_mul, coeff_ofNat_mul, coeff_coeff_tateFormalY]
  rcases lt_trichotomy a b with h | rfl | h
  · have hd : ((a.dist b : ℕ) : R) = b - a := by
      rw [Nat.dist_eq_sub_of_le h.le, Nat.cast_sub h.le]
    simp only [h.ne, not_lt_of_gt h, ite_false]
    split_ifs
    · have hc := hchoose (a.dist b + 1)
      rw [show (a : R) - b = -(a.dist b : ℕ) by rw [hd]; ring]
      push_cast at hc ⊢
      linear_combination hc
    · ring
  · simp
  · have hd : ((a.dist b : ℕ) : R) = a - b := by
      rw [Nat.dist_eq_sub_of_le_right h.le, Nat.cast_sub h.le]
    simp only [h.ne', h, ite_false, ite_true]
    split_ifs
    · have hc := hchoose (a.dist b)
      rw [← hd]
      linear_combination -hc
    · ring

/-- The value `2Y + X` of `W_Y` at the formal Tate point is nonzero: its coefficient of `u` is
`1`. -/
private theorem two_mul_tateFormalY_add_tateFormalX_ne_zero [Nontrivial R] :
    2 * tateFormalY R + tateFormalX R ≠ 0 := by
  intro h
  have h1 := congrArg (fun F : R⟦X⟧⟦X⟧ ↦ coeff 1 (coeff 0 F)) h
  simp only [map_add, coeff_ofNat_mul, coeff_coeff_tateFormalY, coeff_coeff_tateFormalX,
    map_zero] at h1
  norm_num [Nat.dist] at h1

/-- **The invariant differential pulls back to `du / u`, in terms of `W_Y`**: at the formal Tate
point `(X, Y)` of the Tate curve with `q = u v`, the partial derivative `W_Y = 2y + a₁x + a₃` of
the Weierstrass polynomial is `(u ∂/∂u - v ∂/∂v) X`. -/
theorem evalEval_polynomialY_tateFormalX_tateFormalY :
    (tateCurve.map (tateParamHom R)).toAffine.polynomialY.evalEval (tateFormalX R)
      (tateFormalY R) = eulerDiffDerivation R (tateFormalX R) := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY, eulerDiffDerivation_tateFormalX]
  simp

/-- **The canonical differential, second coordinate**: `(u ∂/∂u - v ∂/∂v) Y = 3X² + a₄(q) - Y`
for the formal Tate point `(X, Y)`, where `a₄(q)` is substituted at `q = u v`. With
`a₁ = 1` and `a₂ = 0`, this says that `-dy / (a₁y - 3x² - 2a₂x - a₄)` pulls back to `du / u`. -/
@[simp]
theorem eulerDiffDerivation_tateFormalY :
    eulerDiffDerivation R (tateFormalY R) =
      3 * tateFormalX R ^ 2 + tateParamHom R tateCurve.a₄ - tateFormalY R := by
  -- Differentiating the Weierstrass equation gives `(2Y + X) (D Y - (3X² + a₄ - Y)) = 0` over
  -- the domain `ℤ⟦u⟧⟦v⟧`, where `2Y + X ≠ 0`; the identity then maps to every `R`. The general
  -- `Equation.evalEval_polynomialX_smul_add_evalEval_polynomialY_smul_eq_zero` does not apply
  -- directly: it needs `D` to be linear over a ring the curve is base changed from, while
  -- `ℤ⟦u⟧⟦v⟧` already carries the `ℤ⟦X⟧`-algebra structure by constants in `v`, not `q ↦ u v`.
  have hℤ : eulerDiffDerivation ℤ (tateFormalY ℤ) =
      3 * tateFormalX ℤ ^ 2 + tateParamHom ℤ tateCurve.a₄ - tateFormalY ℤ := by
    have h0 := congrArg (eulerDiffDerivation ℤ)
      (((tateCurve.map (tateParamHom ℤ)).toAffine.equation_iff' _ _).1
        (equation_tateFormalX_tateFormalY ℤ))
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, tateCurve_a₁,
      tateCurve_a₂, tateCurve_a₃, map_one, map_zero, sq, pow_three, map_sub, map_add,
      Derivation.leibniz, eulerDiffDerivation_tateParamHom, eulerDiffDerivation_tateFormalX,
      smul_eq_mul, mul_zero, zero_mul, add_zero, Derivation.map_one_eq_zero] at h0
    have h : (2 * tateFormalY ℤ + tateFormalX ℤ) * (eulerDiffDerivation ℤ (tateFormalY ℤ) -
        (3 * tateFormalX ℤ ^ 2 + tateParamHom ℤ tateCurve.a₄ - tateFormalY ℤ)) = 0 := by
      linear_combination h0
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left
      two_mul_tateFormalY_add_tateFormalX_ne_zero)
  have h := congrArg (map (map (Int.castRingHom R))) hℤ
  rwa [map_map_eulerDiffDerivation, map_map_tateFormalY, map_sub, map_add, map_mul, map_pow,
    map_map_tateFormalX, map_map_tateFormalY, map_ofNat, ← RingHom.comp_apply,
    map_map_comp_tateParamHom] at h

/-- **The invariant differential pulls back to `du / u`, in terms of `W_X`**: at the formal Tate
point `(X, Y)` of the Tate curve with `q = u v`, the partial derivative
`W_X = a₁y - 3x² - 2a₂x - a₄` of the Weierstrass polynomial is `-(u ∂/∂u - v ∂/∂v) Y`. -/
theorem evalEval_polynomialX_tateFormalX_tateFormalY :
    (tateCurve.map (tateParamHom R)).toAffine.polynomialX.evalEval (tateFormalX R)
      (tateFormalY R) = -eulerDiffDerivation R (tateFormalY R) := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialX, eulerDiffDerivation_tateFormalY]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
    tateCurve_a₁, tateCurve_a₂, map_one, map_zero]
  ring

end TauCeti
