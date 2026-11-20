/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# The Newtonian kernel is a fundamental solution of `-Δ`

For `n = 1` and for `n ≥ 3`, the Newtonian kernel `Gₙ(x) = (n (n - 2) ωₙ)⁻¹ ‖x‖²⁻ⁿ` on `ℝⁿ`
(in dimension one, `G₁(x) = -|x| / 2`) satisfies the distributional identity `-Δ Gₙ = δ₀`: for
every `C²` function `f` with compact support,

`∫ x, Δ f x * Gₙ x = -f 0`,

and, with the pole moved to `a`, `∫ x, Δ f x * Gₙ (x - a) = -f a`.

The proof has two steps.

* **The weak gradient.** Integration by parts against `Gₙ` holds across the pole: for a `C¹`
  function `g` with compact support, `∫ Gₙ ∂ᵥg = -∫ (∂ᵥGₙ) g`, in every dimension.  For `n ≤ 2`
  the kernel is Lipschitz (it vanishes identically for `n = 0, 2`), so Mathlib's integration by
  parts for Lipschitz functions applies.  For `n ≥ 3` this is the exponent `2 - n` case of the
  integration by parts identity `TauCeti.integral_norm_rpow_mul_fderiv_eq_neg` for singular norm
  powers, proved by regularization and dominated convergence.  In particular `Gₙ` is weakly
  differentiable on every open set with weak derivative its classical one.
* **The flux.** Summing over an orthonormal basis turns `∫ Δ f Gₙ` into
  `-∫ ∇Gₙ · ∇f = (n ωₙ)⁻¹ ∫ ‖x‖⁻ⁿ f' x x`, and the radial fundamental theorem of calculus
  `TauCeti.integral_norm_rpow_neg_finrank_mul_fderiv_apply_self` evaluates the latter integral as
  `-(n ωₙ) f 0`.

The statement and the normalization follow Evans, *Partial Differential Equations*, Section 2.2.1,
Theorem 1, whose Green's-identity argument on the complement of a small ball is replaced here by
the two steps above.

## Main declarations

* `TauCeti.integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul`: integration by parts against
  the Newtonian kernel.
* `TauCeti.integral_fderiv_mul_newtonianKernel_sub`: the same identity with the pole at `a`.
* `TauCeti.hasWeakFDerivOn_newtonianKernel`: the classical derivative of the kernel is its weak
  derivative.
* `TauCeti.integral_laplacian_mul_newtonianKernel`: `-Δ Gₙ = δ₀`.
* `TauCeti.integral_laplacian_mul_newtonianKernel_sub`: the same identity with the pole at `a`.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Metric Set Topology TopologicalSpace

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- In dimensions at most two the Newtonian kernel is a multiple of the norm: it vanishes
identically in dimensions zero and two, where its normalizing constant is `0⁻¹ = 0`. -/
private lemma exists_newtonianKernel_eq_mul_norm (hn : n ≤ 2) :
    ∃ c : ℝ, newtonianKernel n = fun x ↦ c * ‖x‖ := by
  interval_cases n
  · exact ⟨0, by rw [newtonianKernel_dim_zero]; funext; simp⟩
  · exact ⟨-1 / 2, funext fun x ↦ by rw [newtonianKernel_one]; ring⟩
  · exact ⟨0, by rw [newtonianKernel_two]; funext; simp⟩

/-- Integration by parts against the Newtonian kernel in dimensions at most two, where the kernel
is Lipschitz. -/
private lemma integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul_of_le_two (hn : n ≤ 2)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, newtonianKernel n x * fderiv ℝ g x v =
      -∫ x, fderiv ℝ (newtonianKernel n) x v * g x := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [Subsingleton.elim v 0]
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨c, hcG⟩ := exists_newtonianKernel_eq_mul_norm hn
  have hG : LipschitzWith (‖c‖₊ * 1) (newtonianKernel n) :=
    hcG ▸ (lipschitzWith_smul c).comp lipschitzWith_one_norm
  obtain ⟨K, hgK⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  -- Away from the origin the line derivative of the kernel is its Fréchet derivative.
  have hlineG : (fun x ↦ lineDeriv ℝ (newtonianKernel n) x v * g x) =ᵐ[volume]
      fun x ↦ fderiv ℝ (newtonianKernel n) x v * g x := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : EuclideanSpace ℝ (Fin n)))]
      with x hx
    have hd : DifferentiableAt ℝ (newtonianKernel n) x := by
      rw [hcG]
      exact (differentiableAt_const c).mul
        ((contDiffAt_norm ℝ (n := 1) (Set.mem_compl_singleton_iff.1 hx)).differentiableAt
          one_ne_zero)
    rw [hd.lineDeriv_eq_fderiv]
  have hlineg : ∀ x, lineDeriv ℝ g x (-v) = -fderiv ℝ g x v := fun x ↦ by
    rw [((hg.differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
  rw [← integral_congr_ae hlineG, hG.integral_lineDeriv_mul_eq hgK hc v]
  simp_rw [hlineg, neg_mul, integral_neg, neg_neg, mul_comm (fderiv ℝ g _ v)]

/-- Integration by parts against the Newtonian kernel in dimensions at least three, where the
kernel is singular at the origin. This is the exponent `2 - n` case of
`TauCeti.integral_norm_rpow_mul_fderiv_eq_neg`. -/
private lemma integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul_of_three_le (hn : 3 ≤ n)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, newtonianKernel n x * fderiv ℝ g x v =
      -∫ x, fderiv ℝ (newtonianKernel n) x v * g x := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set C := ((n : ℝ) * ((n : ℝ) - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
  have hG : newtonianKernel n = fun x ↦ C * ‖x‖ ^ (2 - (n : ℝ)) := funext (newtonianKernel_def n)
  -- Away from the pole, `∂ᵥGₙ` is `C` times the derivative of the norm power.
  have hderiv : (fun x ↦ fderiv ℝ (newtonianKernel n) x v * g x) =ᵐ[volume]
      fun x ↦ C * ((((2 - (n : ℝ)) * ‖x‖ ^ (2 - (n : ℝ) - 2)) • innerSL ℝ x) v * g x) := by
    filter_upwards [volume.ae_ne 0] with x hx
    rw [hG, ((hasFDerivAt_norm_rpow_of_ne _ hx).const_mul C).fderiv]
    simp only [smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_congr_ae hderiv, hG]
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, integral_norm_rpow_mul_fderiv_eq_neg (μ := volume)
    (by linarith) (by rw [finrank_euclideanSpace_fin]; linarith) hg hc v, mul_neg]

/-- **Integration by parts against the Newtonian kernel.** In every dimension, for a `C¹`
function `g` with compact support, `∫ Gₙ ∂ᵥg = -∫ (∂ᵥGₙ) g`, although for `n ≥ 3` the kernel is
singular at the origin and for `n = 1` it is not differentiable there. -/
theorem integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, newtonianKernel n x * fderiv ℝ g x v =
      -∫ x, fderiv ℝ (newtonianKernel n) x v * g x := by
  rcases le_or_gt n 2 with hn | hn
  · exact integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul_of_le_two hn hg hc v
  · exact integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul_of_three_le (by omega) hg hc v

/-- **Integration by parts against the Newtonian kernel with pole `a`.** In every dimension, for
a `C¹` function `g` with compact support, `∫ ∂ᵥg (x) Gₙ(x - a) dx = -∫ g(x) ∂ᵥGₙ(x - a) dx`. -/
theorem integral_fderiv_mul_newtonianKernel_sub
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v a : EuclideanSpace ℝ (Fin n)) :
    ∫ x, fderiv ℝ g x v * newtonianKernel n (x - a) =
      -∫ x, g x * fderiv ℝ (newtonianKernel n) (x - a) v := by
  have h := integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul (g := fun y ↦ g (y + a))
    (hg.comp (contDiff_id.add contDiff_const)) (hc.comp_homeomorph (Homeomorph.addRight a)) v
  simp only [fderiv_comp_add_right] at h
  rw [← integral_add_right_eq_self (fun x ↦ fderiv ℝ g x v * newtonianKernel n (x - a)) a,
    ← integral_add_right_eq_self (fun x ↦ g x * fderiv ℝ (newtonianKernel n) (x - a) v) a]
  simp only [add_sub_cancel_right]
  simpa only [mul_comm] using h

/-- **The Newtonian kernel is weakly differentiable.** In every dimension, on every open set the
classical derivative of `Gₙ`, which exists away from the origin, is a weak derivative of `Gₙ`. -/
theorem hasWeakFDerivOn_newtonianKernel (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    HasWeakFDerivOn volume Ω (newtonianKernel n) (fderiv ℝ (newtonianKernel n)) :=
  hasWeakFDerivOn_of_forall_integral_fderiv_smul (locallyIntegrable_newtonianKernel n)
    (locallyIntegrable_fderiv_newtonianKernel n) (fun _ hg hc v ↦ by
      simpa only [smul_eq_mul, mul_comm] using
        integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul hg hc v) Ω

/-- Away from the pole, the gradient pairing `∇Gₙ · ∇f` is `-(n ωₙ)⁻¹ ‖x‖⁻ⁿ f' x x`. -/
private lemma sum_fderiv_newtonianKernel_mul_fderiv (hn : n ≠ 2)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, fderiv ℝ (newtonianKernel n) x (b i) * fderiv ℝ f x (b i) =
      -((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖x‖ ^ (-(n : ℝ)) * fderiv ℝ f x x) := by
  have hx' : fderiv ℝ f x x = ∑ i, ⟪b i, x⟫ * fderiv ℝ f x (b i) := by
    simpa using congrArg (fderiv ℝ f x) (b.sum_repr' x).symm
  simp_rw [fderiv_newtonianKernel_apply n hn, hx', Finset.mul_sum, real_inner_comm x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **The Newtonian kernel is a fundamental solution of `-Δ`.** For `n = 1` or `n ≥ 3` and
every `C²` function `f` with compact support on `ℝⁿ`, `∫ Δ f · Gₙ = -f 0`; that is, `-Δ Gₙ = δ₀`
in the sense of distributions. -/
theorem integral_laplacian_mul_newtonianKernel (hn : n ≠ 2) (hn0 : n ≠ 0)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∫ x, Δ f x * newtonianKernel n x = -f 0 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hvol := (volume_real_unitBall_pos n).ne'
  have hrad := integral_norm_rpow_neg_finrank_mul_fderiv_apply_self
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (hf.of_le (by norm_num)) hc
  rw [finrank_euclideanSpace_fin] at hrad
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hsum : (fun x ↦ ∑ i, fderiv ℝ (newtonianKernel n) x (b i) * fderiv ℝ f x (b i)) =ᵐ[volume]
      fun x ↦ -((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (‖x‖ ^ (-(n : ℝ)) * fderiv ℝ f x x) :=
    ae_of_all _ (sum_fderiv_newtonianKernel_mul_fderiv hn b f)
  rw [(locallyIntegrable_newtonianKernel n).integral_laplacian_mul_eq_neg_integral_sum
      (locallyIntegrable_fderiv_newtonianKernel n)
      (fun _ ↦ integral_newtonianKernel_mul_fderiv_eq_neg_fderiv_mul) hf hc b,
    integral_congr_ae hsum, integral_const_mul, hrad]
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  field_simp

/-- **The Newtonian kernel with pole `a` is a fundamental solution of `-Δ`.** For `n = 1` or
`n ≥ 3` and every `C²` function `f` with compact support on `ℝⁿ`, `∫ Δ f · Gₙ(· - a) = -f a`. -/
theorem integral_laplacian_mul_newtonianKernel_sub (hn : n ≠ 2) (hn0 : n ≠ 0)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (a : EuclideanSpace ℝ (Fin n)) :
    ∫ x, Δ f x * newtonianKernel n (x - a) = -f a := by
  have h := integral_laplacian_mul_newtonianKernel hn hn0 (f := fun y ↦ f (y + a))
    (hf.comp (contDiff_id.add contDiff_const)) (hc.comp_homeomorph (Homeomorph.addRight a))
  rw [laplacian_comp_add_right, zero_add] at h
  rw [← h, ← integral_add_right_eq_self _ a]
  simp

end TauCeti
