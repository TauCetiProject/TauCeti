/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.MeanInequalities

/-!
# Gårding's theorem: concavity of `p^{1/m}` on the Gårding cone

Let `p` be a real polynomial, hyperbolic of degree `m ≥ 1` in the direction `a`
(`MvPolynomial.IsHyperbolic`), with Gårding cone `Γ = Γ(p, a)`. Then `p^{1/m}` is superadditive
on `Γ` (`MvPolynomial.IsHyperbolic.eval_rpow_add_le`):

`p(x)^{1/m} + p(y)^{1/m} ≤ p(x + y)^{1/m}` for `x, y ∈ Γ`,

and, being positively homogeneous of degree one (`MvPolynomial.IsHomogeneous.eval_smul_rpow`), it
is concave on the convex cone `Γ` (`MvPolynomial.IsHyperbolic.concaveOn_rpow`). This is the
concavity part of Gårding's theorem.

Its tangent form is **Gårding's inequality**
(`MvPolynomial.IsHyperbolic.mul_rpow_mul_rpow_le_eval_sum_smul_pderiv`): for `x ∈ Γ` and `y` in the
closure of `Γ`,

`m p(y)^{1/m} p(x)^{1 - 1/m} ≤ D_y p(x) = ∑ᵢ yᵢ ∂p/∂Xᵢ (x)`.

## Implementation notes

By Gårding's theorem on the directions (`MvPolynomial.IsHyperbolic.of_mem_gardingCone`), `p` is
hyperbolic in the direction `y`, with the same cone. So `t ↦ p(x + t • y)` splits with leading
coefficient `p(y)` and `m` roots `rᵢ`, all negative since `x ∈ Γ(p, y)`:
`p(x + t • y) = p(y) ∏ᵢ (t - rᵢ)`. At `t = 0` and `t = 1` this gives `p(x) = p(y) ∏ᵢ (-rᵢ)` and
`p(x + y) = p(y) ∏ᵢ (1 - rᵢ)`, and the inequality is the superadditivity of the geometric mean
(`Real.multiset_prod_map_rpow_inv_card_add_le`) for the families `-rᵢ` and `1`.

For Gårding's inequality with `y ∈ Γ`, the function `φ(t) = p(x + t • (y - x))^{1/m}` is concave
on `[0, 1]`, so `φ(1) - φ(0) ≤ φ'(0) = (1/m) p(x)^{1/m - 1} D_{y - x} p(x)`, and Euler's identity
`D_x p(x) = m p(x)` turns this into the inequality. Both sides are continuous in `y`, which
extends it to the closure of `Γ`.

## References

* L. Gårding, *An inequality for hyperbolic polynomials*, J. Math. Mech. 8 (1959), 957–965.
* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

open Set

variable {σ : Type*} {p : MvPolynomial σ ℝ} {m : ℕ} {a : σ → ℝ}

namespace MvPolynomial.IsHomogeneous

/-- For a homogeneous polynomial of degree `m ≥ 1` and `p(x) ≥ 0`, `p^{1/m}` is positively
homogeneous of degree one: `p(θ • x)^{1/m} = θ p(x)^{1/m}` for `θ ≥ 0`. -/
theorem eval_smul_rpow (hp : p.IsHomogeneous m) (hm : 1 ≤ m) {x : σ → ℝ}
    (hx : 0 ≤ eval x p) {θ : ℝ} (hθ : 0 ≤ θ) :
    eval (θ • x) p ^ (m : ℝ)⁻¹ = θ * eval x p ^ (m : ℝ)⁻¹ := by
  rw [hp.eval_smul, Real.mul_rpow (pow_nonneg hθ m) hx,
    Real.pow_rpow_inv_natCast hθ (by omega)]

end MvPolynomial.IsHomogeneous

namespace MvPolynomial.IsHyperbolic

/-- **Gårding's theorem, superadditivity.** For `p` hyperbolic of degree `m ≥ 1` in the direction
`a`, `p(x)^{1/m} + p(y)^{1/m} ≤ p(x + y)^{1/m}` for `x` and `y` in the Gårding cone `Γ(p, a)`. -/
theorem eval_rpow_add_le (hp : IsHyperbolic p m a) (hm : 1 ≤ m) {x y : σ → ℝ}
    (hx : x ∈ gardingCone p a) (hy : y ∈ gardingCone p a) :
    eval x p ^ (m : ℝ)⁻¹ + eval y p ^ (m : ℝ)⁻¹ ≤ eval (x + y) p ^ (m : ℝ)⁻¹ := by
  -- `p` is hyperbolic in the direction `y`, and `x` lies in its cone in that direction.
  have hy' := hp.of_mem_gardingCone hy
  have hx' : x ∈ gardingCone p y := (hp.gardingCone_eq_of_mem hy).symm ▸ hx
  set Q := aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X) p
  have hcard : Multiset.card Q.roots = m := hy'.card_roots x
  have hlc : Q.leadingCoeff = eval y p :=
    leadingCoeff_aeval_C_add_C_mul_X_of_isHomogeneous hy'.isHomogeneous x hy'.eval_pos.ne'
  have hroots := (mem_gardingCone_iff_forall_mem_roots hy'.isHomogeneous hy'.eval_pos.ne').1 hx'
  -- The values at `t = 0` and `t = 1` of `p(x + t • y) = p(y) ∏ᵢ (t - rᵢ)`.
  have h0 : eval x p = eval y p * (Q.roots.map fun r ↦ -r).prod := by
    have := (hy'.splits x).eval_eq_prod_roots 0
    rw [eval_aeval_C_add_C_mul_X, zero_smul, add_zero, hlc] at this
    simpa using this
  have h1 : eval (x + y) p = eval y p * (Q.roots.map fun r ↦ 1 - r).prod := by
    have := (hy'.splits x).eval_eq_prod_roots 1
    rwa [eval_aeval_C_add_C_mul_X, one_smul, hlc] at this
  have hpy := hy'.eval_pos.le
  have hA : 0 ≤ (Q.roots.map fun r ↦ -r).prod :=
    Multiset.prod_nonneg fun r hr ↦ by
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hr
      exact neg_nonneg.2 (hroots s hs).le
  have hB : 0 ≤ (Q.roots.map fun r ↦ 1 - r).prod :=
    Multiset.prod_nonneg fun r hr ↦ by
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hr
      linarith [hroots s hs]
  -- The superadditivity of the geometric mean for the families `-rᵢ` and `1`.
  have key := Real.multiset_prod_map_rpow_inv_card_add_le (s := Q.roots) (a := fun r ↦ -r)
    (b := fun _ ↦ 1) (fun h ↦ by simp [h] at hcard; omega)
    (fun r hr ↦ neg_nonneg.2 (hroots r hr).le) fun _ _ ↦ zero_le_one
  simp only [hcard, Multiset.map_const', Multiset.prod_replicate, one_pow, Real.one_rpow,
    neg_add_eq_sub] at key
  rw [h0, h1, Real.mul_rpow hpy hA, Real.mul_rpow hpy hB]
  nlinarith [Real.rpow_nonneg hpy (m : ℝ)⁻¹]

/-- **Gårding's theorem, concavity.** For `p` hyperbolic of degree `m` in the direction `a`,
`p^{1/m}` is concave on the Gårding cone `Γ(p, a)`. For `m = 0` the exponent `1/m` is the junk
value `0`, and the function is the constant `1`. -/
theorem concaveOn_rpow (hp : IsHyperbolic p m a) :
    ConcaveOn ℝ (gardingCone p a) fun x ↦ eval x p ^ (m : ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using concaveOn_const (1 : ℝ) hp.convex_gardingCone
  refine ⟨hp.convex_gardingCone, fun x hx y hy θ η hθ hη hθη ↦ ?_⟩
  have hpos {z : σ → ℝ} (hz : z ∈ gardingCone p a) : 0 ≤ eval z p :=
    (eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hz).le
  simp only [smul_eq_mul]
  rcases hθ.eq_or_lt with rfl | hθ'
  · simp [show η = 1 by linarith]
  rcases hη.eq_or_lt with rfl | hη'
  · simp [show θ = 1 by linarith]
  rw [← hp.isHomogeneous.eval_smul_rpow hm (hpos hx) hθ,
    ← hp.isHomogeneous.eval_smul_rpow hm (hpos hy) hη]
  exact hp.eval_rpow_add_le hm (smul_mem_gardingCone hp.isHomogeneous hx hθ')
    (smul_mem_gardingCone hp.isHomogeneous hy hη')

/-- **Gårding's inequality**, for `y` in the cone. -/
private theorem mul_rpow_mul_rpow_le_eval_sum_smul_pderiv_of_mem [Fintype σ]
    (hp : IsHyperbolic p m a) (hm : 1 ≤ m) {x y : σ → ℝ} (hx : x ∈ gardingCone p a)
    (hy : y ∈ gardingCone p a) :
    m * eval y p ^ (m : ℝ)⁻¹ * eval x p ^ (1 - (m : ℝ)⁻¹) ≤ eval x (∑ i, y i • pderiv i p) := by
  have hpos {z : σ → ℝ} (hz : z ∈ gardingCone p a) : 0 < eval z p :=
    eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hz
  -- The segment from `x` to `y` lies in the cone.
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ gardingCone p a := by
    convert hp.convex_gardingCone hx hy (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t) using 1
    module
  set q := aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C ((y - x) i) * Polynomial.X) p
  have hq (t : ℝ) : q.eval t = eval (x + t • (y - x)) p := eval_aeval_C_add_C_mul_X p x _ t
  -- `φ = q^{1/m}` is concave on `[0, 1]`.
  have hconc : ConcaveOn ℝ (Icc 0 1) fun t ↦ q.eval t ^ (m : ℝ)⁻¹ := by
    refine ⟨convex_Icc 0 1, fun s hs t ht c d hc hd hcd ↦ ?_⟩
    have h := hp.concaveOn_rpow.2 (hseg s hs) (hseg t ht) hc hd hcd
    simp only [hq, smul_eq_mul] at h ⊢
    convert h using 3
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hcd, one_smul, smul_smul, smul_smul,
      ← add_smul]
  have hx0 : q.eval 0 = eval x p := by simp [hq]
  have hderiv := (q.hasDerivAt 0).rpow_const (p := (m : ℝ)⁻¹) (Or.inl (hx0 ▸ (hpos hx).ne'))
  have hs := hconc.slope_le_of_hasDerivAt (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one) zero_lt_one hderiv
  -- `φ'(0) = (1/m) p(x)^{1/m - 1} (D_y p(x) - m p(x))`, by Euler's identity.
  have hq' : q.derivative.eval 0 = eval x (∑ i, y i • pderiv i p) - m * eval x p := by
    rw [derivative_aeval_C_add_C_mul_X, eval_aeval_C_add_C_mul_X, zero_smul, add_zero]
    have heuler := congrArg (eval x) hp.isHomogeneous.sum_X_mul_pderiv
    simp only [map_sum, eval_mul, eval_X, nsmul_eq_mul, map_natCast] at heuler
    simp only [map_sum, smul_eval, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, heuler]
  rw [slope_def_field, sub_zero, div_one, hq', hx0, hq, one_smul, add_sub_cancel] at hs
  -- Multiply by `m p(x)^{1 - 1/m}`.
  set P := eval x p
  have hP := hpos hx
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ m * P ^ (1 - (m : ℝ)⁻¹))
  have h1 : P ^ (m : ℝ)⁻¹ * P ^ (1 - (m : ℝ)⁻¹) = P := by
    rw [← Real.rpow_add hP, add_sub_cancel, Real.rpow_one]
  have h2 : P ^ ((m : ℝ)⁻¹ - 1) * P ^ (1 - (m : ℝ)⁻¹) = 1 := by
    rw [← Real.rpow_add hP, sub_add_sub_cancel, sub_self, Real.rpow_zero]
  have h3 : m * P ^ (1 - (m : ℝ)⁻¹) *
      ((eval x (∑ i, y i • pderiv i p) - m * P) * (m : ℝ)⁻¹ * P ^ ((m : ℝ)⁻¹ - 1)) =
        eval x (∑ i, y i • pderiv i p) - m * P := by
    rw [show m * P ^ (1 - (m : ℝ)⁻¹) *
        ((eval x (∑ i, y i • pderiv i p) - m * P) * (m : ℝ)⁻¹ * P ^ ((m : ℝ)⁻¹ - 1)) =
        (eval x (∑ i, y i • pderiv i p) - m * P) * (m * (m : ℝ)⁻¹) *
          (P ^ ((m : ℝ)⁻¹ - 1) * P ^ (1 - (m : ℝ)⁻¹)) by ring,
      h2, mul_inv_cancel₀ hm'.ne', mul_one, mul_one]
  rw [h3, mul_sub, show m * P ^ (1 - (m : ℝ)⁻¹) * P ^ (m : ℝ)⁻¹ = m * P by
    rw [mul_assoc, mul_comm (P ^ _), h1]] at hs'
  linarith

/-- **Gårding's inequality.** For `p` hyperbolic of degree `m` in the direction `a`, `x` in
the Gårding cone `Γ(p, a)` and `y` in its closure,
`m p(y)^{1/m} p(x)^{1 - 1/m} ≤ D_y p(x) = ∑ᵢ yᵢ ∂p/∂Xᵢ (x)`. This is the tangent inequality of
the concave function `p^{1/m}`, positively homogeneous of degree one, at `x`. In degree `m = 0`
both sides vanish. -/
theorem mul_rpow_mul_rpow_le_eval_sum_smul_pderiv [Fintype σ] (hp : IsHyperbolic p m a)
    {x y : σ → ℝ} (hx : x ∈ gardingCone p a) (hy : y ∈ closure (gardingCone p a)) :
    m * eval y p ^ (m : ℝ)⁻¹ * eval x p ^ (1 - (m : ℝ)⁻¹) ≤ eval x (∑ i, y i • pderiv i p) := by
  -- In degree `0`, `p` is a constant and both sides vanish.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.1
      (hp.isHomogeneous.totalDegree hp.ne_zero)⟩
    simp
  have hm' : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hm)
  -- Both sides are continuous in `y`; the left side through `t ↦ t^{1/m}` with `1/m > 0`.
  have hclosed : IsClosed {y : σ → ℝ |
      m * eval y p ^ (m : ℝ)⁻¹ * eval x p ^ (1 - (m : ℝ)⁻¹) ≤ eval x (∑ i, y i • pderiv i p)} := by
    refine isClosed_le ?_ ?_
    · exact ((continuous_const.mul ((continuous_eval p).rpow_const fun _ ↦ Or.inr hm'.le)).mul
        continuous_const)
    · simp only [map_sum, smul_eval]
      fun_prop
  exact closure_minimal (fun y hy ↦ hp.mul_rpow_mul_rpow_le_eval_sum_smul_pderiv_of_mem hm hx hy)
    hclosed hy

end MvPolynomial.IsHyperbolic
