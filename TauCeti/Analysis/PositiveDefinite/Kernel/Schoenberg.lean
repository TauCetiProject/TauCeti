/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.LinearAlgebra.Matrix.CondNegSemidef
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Bochner.Gaussian.Basic

/-!
# Schoenberg's theorem

A complex kernel `ψ` on an arbitrary index type is conditionally negative semidefinite if and only
if the kernels `(a, b) ↦ exp (-t ψ(a, b))` are positive semidefinite for every `t > 0`.

Conditionally negative semidefinite functions on a group produce, through this theorem, the
semigroups of positive-definite functions `exp (-t ψ)` that approximate the constant function `1`
as `t → 0`. When `ψ` vanishes at the identity these functions are normalized, and when the real
part of `ψ` is proper they vanish at infinity; this is how one proves the Haagerup property of a
group carrying a proper conditionally negative-definite function such as a tree length.

The forward direction reduces to the Schur product theorem. Entrywise exponentials of
positive-semidefinite kernels are positive semidefinite, being limits of sums of Schur powers with
nonnegative coefficients (`Matrix.PosSemidef.map_cexp`). For a base point `a₀`, the centred kernel
`L(a, b) = ψ(a, a₀) + ψ(a₀, b) - ψ(a, b) - ψ(a₀, a₀)` is positive semidefinite
(`Matrix.IsHermitian.condNegSemidef_iff_posSemidef_centered`), and
`exp (-t ψ(a, b)) = exp (t ψ(a₀, a₀)) · conj (g a) · g b · exp (t L(a, b))` with
`g b = exp (-t ψ(a₀, b))`. The converse differentiates at `t = 0`: on coefficients summing to
zero the quadratic form of `(exp (-t ψ) - 1) / t` is nonnegative and tends to that of `-ψ`.

## Main declarations

* `Matrix.PosSemidef.map_cexp`: the entrywise exponential of a positive-semidefinite kernel is
  positive semidefinite.
* `Matrix.CondNegSemidef.posSemidef_cexp_neg_mul`: the forward direction of Schoenberg's theorem.
* `Matrix.condNegSemidef_iff_forall_posSemidef_cexp_neg_mul`: **Schoenberg's theorem**.
* `Matrix.condNegSemidef_sq_norm_sub`: the squared distance `‖f a - f b‖²` along a map into a
  real inner product space is conditionally negative semidefinite.

## References

* I. J. Schoenberg, *Metric spaces and positive definite functions*, Trans. Amer. Math. Soc. 44
  (1938), 522–536.
* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3, §2.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Examples 16.1.2.
-/

public section

open Filter Topology
open scoped ComplexOrder Nat

namespace Matrix

variable {n : Type*}

/-- The entrywise exponential of a positive-semidefinite kernel is positive semidefinite: it is
the sum of the Schur powers `K ^ k / k!`. -/
theorem PosSemidef.map_cexp {K : Matrix n n ℂ} (hK : K.PosSemidef) :
    (K.map Complex.exp).PosSemidef := by
  have hsum : HasSum (fun k : ℕ ↦ (k ! : ℂ)⁻¹ • (of fun a b ↦ K a b ^ k)) (K.map Complex.exp) := by
    refine Pi.hasSum.mpr fun a ↦ Pi.hasSum.mpr fun b ↦ ?_
    simpa [Complex.exp_eq_exp_ℂ, div_eq_inv_mul] using
      NormedSpace.expSeries_div_hasSum_exp (K a b)
  refine PosSemidef.of_hasSum hsum fun k ↦ PosSemidef.smul ?_ (by positivity)
  exact hK.hadamard_pow k

/-- **Schoenberg's theorem**, forward direction. If `ψ` is conditionally negative semidefinite,
then `(a, b) ↦ exp (-t ψ(a, b))` is positive semidefinite for every `t ≥ 0`. -/
theorem CondNegSemidef.posSemidef_cexp_neg_mul {ψ : Matrix n n ℂ} (hψ : ψ.CondNegSemidef)
    {t : ℝ} (ht : 0 ≤ t) : PosSemidef (of fun a b ↦ Complex.exp (-(t * ψ a b))) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨a₀⟩⟩
  · exact ⟨IsHermitian.ext fun a ↦ isEmptyElim a, fun x ↦ by simp [Subsingleton.elim x 0]⟩
  have hsymm (a b : n) : star (ψ a b) = ψ b a := hψ.isHermitian.apply b a
  -- The centred kernel at `a₀` is positive semidefinite, hence so is its scaled exponential.
  have hL := ((hψ.isHermitian.condNegSemidef_iff_posSemidef_centered a₀).mp hψ).smul
    (by exact_mod_cast ht : (0 : ℂ) ≤ t)
  have hrank : PosSemidef (of fun a b ↦ star (Complex.exp (-(t * ψ a₀ a))) *
      Complex.exp (-(t * ψ a₀ b))) :=
    TauCeti.posSemidef_rankOne fun b ↦ Complex.exp (-(t * ψ a₀ b))
  -- The diagonal value `ψ(a₀, a₀)` is real, so `exp (t ψ(a₀, a₀))` is a nonnegative scalar.
  have hreal : ((ψ a₀ a₀).re : ℂ) = ψ a₀ a₀ := Complex.conj_eq_iff_re.mp (hsymm a₀ a₀)
  have hc : (0 : ℂ) ≤ Complex.exp (t * ψ a₀ a₀) := by
    rw [← hreal, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    exact_mod_cast (Real.exp_pos _).le
  refine (congrArg PosSemidef ?_).mp ((hL.map_cexp.hadamard hrank).smul hc)
  ext a b
  simp only [Matrix.smul_apply, Matrix.hadamard_apply, map_apply, of_apply, smul_eq_mul,
    RCLike.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, ← Complex.star_def,
    hsymm, ← Complex.exp_add]
  congr 1
  ring

/-- **Schoenberg's theorem.** A complex kernel `ψ` is conditionally negative semidefinite if and
only if `(a, b) ↦ exp (-t ψ(a, b))` is positive semidefinite for every `t > 0`. -/
theorem condNegSemidef_iff_forall_posSemidef_cexp_neg_mul {ψ : Matrix n n ℂ} :
    ψ.CondNegSemidef ↔
      ∀ t : ℝ, 0 < t → PosSemidef (of fun a b ↦ Complex.exp (-(t * ψ a b))) := by
  refine ⟨fun hψ t ht ↦ hψ.posSemidef_cexp_neg_mul ht.le, fun h ↦ ?_⟩
  -- The difference quotients `(exp (-t z) - 1) / t` tend to `-z` as `t → 0⁺`.
  have hlim (z : ℂ) : Tendsto (fun t : ℝ ↦ (t : ℂ)⁻¹ * (Complex.exp (-(t * z)) - 1))
      (𝓝[>] 0) (𝓝 (-z)) := by
    have hd : HasDerivAt (fun t : ℝ ↦ Complex.exp (-(t * z))) (-z) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const z).neg.cexp
    simpa [Complex.real_smul] using hd.tendsto_slope_zero_right
  have hsymm (t : ℝ) (ht : 0 < t) (a b : n) :
      star (Complex.exp (-(t * ψ a b))) = Complex.exp (-(t * ψ b a)) :=
    (h t ht).isHermitian.apply b a
  have hpos (t : ℝ) (ht : 0 < t) {ι : Type} [Fintype ι] (v : ι → n) (x : ι → ℂ) :
      0 ≤ ∑ i, ∑ j, star (x i) * Complex.exp (-(t * ψ (v i) (v j))) * x j :=
    (TauCeti.posSemidef_iff_finite_sum.mp (h t ht)).2 v x
  refine condNegSemidef_iff_finite_sum.mpr ⟨fun a b ↦ ?_, fun {ι : Type} _ v x hx ↦ ?_⟩
  · -- Conjugate symmetry of `exp (-t ψ)` for `t > 0` passes to the derivative at `0`.
    have hconj : (fun t : ℝ ↦ star ((t : ℂ)⁻¹ * (Complex.exp (-(t * ψ a b)) - 1))) =ᶠ[𝓝[>] 0]
        fun t ↦ (t : ℂ)⁻¹ * (Complex.exp (-(t * ψ b a)) - 1) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [star_mul, star_sub, star_one, hsymm t ht, star_inv₀, Complex.star_def,
        Complex.conj_ofReal, mul_comm]
    have := tendsto_nhds_unique (((hlim (ψ a b)).star).congr' hconj) (hlim (ψ b a))
    simpa using this
  · -- On coefficients summing to zero, the quadratic form of the difference quotient is
    -- nonnegative and tends to that of `-ψ`.
    have hzero : ∑ i, ∑ j, star (x i) * x j = 0 := by
      rw [← Finset.sum_mul_sum, hx, mul_zero]
    have hquot : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ ∑ i, ∑ j,
        star (x i) * ((t : ℂ)⁻¹ * (Complex.exp (-(t * ψ (v i) (v j))) - 1)) * x j := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have hrw : ∑ i, ∑ j,
          star (x i) * ((t : ℂ)⁻¹ * (Complex.exp (-(t * ψ (v i) (v j))) - 1)) * x j =
            (t : ℂ)⁻¹ * ∑ i, ∑ j, star (x i) * Complex.exp (-(t * ψ (v i) (v j))) * x j := by
        rw [← sub_zero (∑ i, ∑ j, star (x i) * Complex.exp (-(t * ψ (v i) (v j))) * x j),
          ← hzero]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      rw [hrw]
      exact mul_nonneg (by exact_mod_cast (inv_pos.mpr ht).le) (hpos t ht v x)
    have hlim' := tendsto_finsetSum Finset.univ fun i _ ↦ tendsto_finsetSum Finset.univ
      fun j _ ↦ ((hlim (ψ (v i) (v j))).const_mul (star (x i))).mul_const (x j)
    have := ge_of_tendsto hlim' hquot
    simpa [mul_neg, neg_mul, Finset.sum_neg_distrib] using this

/-- The squared distance `(a, b) ↦ ‖f a - f b‖²` along a map `f` into a real inner product space
is a conditionally negative semidefinite kernel. -/
theorem condNegSemidef_sq_norm_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : n → E) : CondNegSemidef (of fun a b ↦ ((‖f a - f b‖ ^ 2 : ℝ) : ℂ)) := by
  refine condNegSemidef_iff_forall_posSemidef_cexp_neg_mul.mpr fun t ht ↦ ?_
  have hG : PosSemidef (of fun x y : E ↦ Complex.exp (-(t * ‖x - y‖ ^ 2 : ℝ))) :=
    TauCeti.posSemidef_cexp_neg_mul_sq_norm ht.le
  refine (congrArg PosSemidef ?_).mp (hG.submatrix f)
  ext a b
  simp

end Matrix
