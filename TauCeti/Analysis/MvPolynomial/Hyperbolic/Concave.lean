/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding
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

## Implementation notes

By Gårding's theorem on the directions (`MvPolynomial.IsHyperbolic.of_mem_gardingCone`), `p` is
hyperbolic in the direction `y`, with the same cone. So `t ↦ p(x + t • y)` splits with leading
coefficient `p(y)` and `m` roots `rᵢ`, all negative since `x ∈ Γ(p, y)`:
`p(x + t • y) = p(y) ∏ᵢ (t - rᵢ)`. At `t = 0` and `t = 1` this gives `p(x) = p(y) ∏ᵢ (-rᵢ)` and
`p(x + y) = p(y) ∏ᵢ (1 - rᵢ)`, and the inequality is the superadditivity of the geometric mean
(`Real.multiset_prod_map_rpow_inv_card_add_le`) for the families `-rᵢ` and `1`.

## References

* L. Gårding, *An inequality for hyperbolic polynomials*, J. Math. Mech. 8 (1959), 957–965.
* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

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

end MvPolynomial.IsHyperbolic
