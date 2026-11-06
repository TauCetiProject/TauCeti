/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Bochner.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The Lichnerowicz eigenvalue estimate

On a closed Riemannian manifold of dimension `n ≥ 2` with `Ric ≥ (n - 1) k g`,
every nonzero smooth eigenfunction of the nonnegative scalar Laplacian with positive
eigenvalue `λ` satisfies `λ ≥ n k`. The sign convention here is
`laplaceBeltrami f = -λ f`.
The estimate applies to every positive eigenvalue, including the first one.

The proof integrates the Bochner inequality and uses Green's identity. The pointwise
Bochner inequality is also available without compactness.
Connectedness and a mean-zero hypothesis are unnecessary for this estimate.

The Bochner inequality combines two pointwise inequalities: the trace Cauchy–Schwarz inequality
`(Δ f)² ≤ n |Hess f|²` and the Ricci bound in the direction of `grad f`. At the eigenvalue `n k`
the integrated inequality is an equality, so both pointwise inequalities are equalities
everywhere. Equality in the first makes the Hessian pure trace, which together with the
eigen-equation is Obata's equation `Hess f = -k f g`; conversely, tracing Obata's equation gives
back `Δ f = -n k f`. This identifies the equality case of the estimate with Obata's equation.
The equality statements need no hypothesis on the dimension, on the sign of `k`, or on `f`.
No existence of eigenfunctions is asserted here, and Obata's theorem that a complete manifold
carrying a nonconstant solution of `Hess f = -k f g` with `k > 0` is a round sphere is not proved
here.

## Main results

* `TauCeti.Manifold.finrank_mul_le_of_laplaceBeltrami_eq_neg_mul`: the Lichnerowicz estimate
  `λ ≥ n k`.
* `TauCeti.Manifold.hessian_eq_neg_mul_mul_inner_of_laplaceBeltrami_eq_neg_finrank_mul`: the
  equality case `Δ f = -n k f` forces `Hess f = -k f g`.
* `TauCeti.Manifold.ricciTensor_mgradient_eq_of_laplaceBeltrami_eq_neg_finrank_mul`: in the
  equality case, `Ric(grad f, grad f) = (n - 1) k |grad f|²`.
* `TauCeti.Manifold.laplaceBeltrami_eq_neg_finrank_mul_iff_hessian_eq_neg_mul_mul_inner`: under
  the Ricci bound, `Δ f = -n k f` if and only if `Hess f = -k f g`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Chapter 9 (the Bochner technique
  and the Lichnerowicz estimate).
* M. Obata, *Certain conditions for a Riemannian manifold to be isometric with a sphere*,
  J. Math. Soc. Japan 14 (1962), 333–340.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {k lam : ℝ}

variable [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The dimension-weighted Bochner inequality under a Ricci lower bound. It is local,
requires no dimension restriction, and uses `Δ = div grad` rather than `Δ⁺`. -/
theorem le_finrank_mul_laplaceBeltrami_norm_sq_mgradient
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hRic : ∀ v : TangentSpace I x,
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) :
    2 * laplaceBeltrami I f x ^ 2 +
      2 * (Module.finrank ℝ E : ℝ) *
        mvfderiv I (laplaceBeltrami I f) x (mgradient I f x) +
      2 * (Module.finrank ℝ E : ℝ) * (((Module.finrank ℝ E : ℝ) - 1) * k) *
        ‖mgradient I f x‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x := by
  have htrace := laplaceBeltrami_sq_le_finrank_mul_sum_hessian_sq f x
    (stdOrthonormalBasis ℝ (TangentSpace I x))
  rw [laplaceBeltrami_norm_sq_mgradient hf x
    (stdOrthonormalBasis ℝ (TangentSpace I x))]
  have hcurv := mul_le_mul_of_nonneg_left (hRic (mgradient I f x))
    (show 0 ≤ 2 * (Module.finrank ℝ E : ℝ) by positivity)
  nlinarith

section Closed

variable [I.Boundaryless] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **The Lichnerowicz estimate.** On a closed manifold of dimension `n ≥ 2` with
`Ric ≥ (n - 1) k g`, every positive eigenvalue with a nonzero smooth eigenfunction
is at least `n k`. The eigen-equation is stated for the native `Δ = div grad`.
The real lower bound `k` need not be positive. -/
theorem finrank_mul_le_of_laplaceBeltrami_eq_neg_mul
    (hn : 2 ≤ Module.finrank ℝ E) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hlam : 0 < lam) (heig : ∀ x, laplaceBeltrami I f x = -lam * f x)
    (hne : ∃ x, f x ≠ 0)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) :
    (Module.finrank ℝ E : ℝ) * k ≤ lam := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  let n : ℝ := Module.finrank ℝ E
  let μ := riemannianVolume I M
  have hN : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ ‖mgradient I f x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using contMDiff_inner_mgradient (n := ∞) hf hf
  have hFint : Integrable (fun x ↦ f x ^ 2) μ :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNint : Integrable (fun x ↦ ‖mgradient I f x‖ ^ 2) μ :=
    hN.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hL := contMDiff_laplaceBeltrami (I := I) (n := 0) (m := ∞) (k := ∞)
    (by simp) (by simp) (hN.of_le (by simp))
  have hLint : Integrable (laplaceBeltrami I (fun x ↦ ‖mgradient I f x‖ ^ 2)) μ :=
    hL.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have henergy := integral_norm_sq_mgradient_eq_mul_integral_sq_of_laplaceBeltrami_eq_neg_mul
    (hf.of_le (by simp)) (HasCompactSupport.of_compactSpace f) heig
  have hzero := integral_laplaceBeltrami_eq_zero (hN.of_le (by simp))
    (HasCompactSupport.of_compactSpace _)
  have hderiv (x : M) : mvfderiv I (laplaceBeltrami I f) x (mgradient I f x) =
      -lam * ‖mgradient I f x‖ ^ 2 := by
    have heq : laplaceBeltrami I f = -lam • f := funext heig
    rw [heq, mvfderiv_const_smul_field, smul_apply, smul_eq_mul,
      ← inner_mgradient, real_inner_self_eq_norm_sq]
  have hpoint (x : M) : 2 * lam ^ 2 * f x ^ 2 +
      (2 * n * ((n - 1) * k - lam)) * ‖mgradient I f x‖ ^ 2 ≤
      n * laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x := by
    have h := le_finrank_mul_laplaceBeltrami_norm_sq_mgradient hf x (hRic x)
    rw [heig, hderiv] at h
    dsimp [n]
    nlinarith
  have hint := integral_mono
    ((hFint.const_mul (2 * lam ^ 2)).add (hNint.const_mul (2 * n * ((n - 1) * k - lam))))
    (hLint.const_mul n) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add (hFint.const_mul _) (hNint.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, hzero, mul_zero, henergy] at hint
  obtain ⟨x, hx⟩ := hne
  have hpos : 0 < ∫ x, f x ^ 2 ∂μ :=
    (hf.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (HasCompactSupport.of_compactSpace _) (fun _ ↦ sq_nonneg _) (pow_ne_zero 2 hx)
  have hn' : 1 < n := by dsimp [n]; exact_mod_cast (show 1 < Module.finrank ℝ E by omega)
  -- The integrated inequality factors as 2 * lam * (n - 1) * (∫ f²) * (n * k - lam) ≤ 0.
  have hfactor : 0 < 2 * lam * (n - 1) * ∫ x, f x ^ 2 ∂μ := by positivity
  by_contra hlt
  have hneg : 0 < n * k - lam := sub_pos.2 (lt_of_not_ge hlt)
  nlinarith [mul_pos hfactor hneg]

/-- The integral of the Bochner defect `n Δ|grad f|² + 2 n k |grad f|² - 2 n² k² f²` vanishes
for a smooth solution of `Δ f = -n k f` on a closed manifold. -/
private theorem integral_bochnerDefect_eq_zero
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (heig : ∀ x, laplaceBeltrami I f x = -((Module.finrank ℝ E : ℝ) * k) * f x) :
    ∫ y, ((Module.finrank ℝ E : ℝ) * laplaceBeltrami I (fun z ↦ ‖mgradient I f z‖ ^ 2) y +
      2 * (Module.finrank ℝ E : ℝ) * k * ‖mgradient I f y‖ ^ 2 -
      2 * (Module.finrank ℝ E : ℝ) ^ 2 * k ^ 2 * f y ^ 2) ∂riemannianVolume I M = 0 := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let N : M → ℝ := fun y ↦ ‖mgradient I f y‖ ^ 2
  have hN : ContMDiff I 𝓘(ℝ) ∞ N := by
    simpa only [N, real_inner_self_eq_norm_sq] using contMDiff_inner_mgradient (n := ∞) hf hf
  have hFint : Integrable (fun y ↦ f y ^ 2) (riemannianVolume I M) :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNint : Integrable N (riemannianVolume I M) :=
    hN.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLint : Integrable (laplaceBeltrami I N) (riemannianVolume I M) :=
    (contMDiff_laplaceBeltrami (I := I) (n := 0) (m := ∞) (k := ∞) (by simp) (by simp)
      (hN.of_le (by simp))).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have henergy := integral_norm_sq_mgradient_eq_mul_integral_sq_of_laplaceBeltrami_eq_neg_mul
    (hf.of_le (by simp)) (HasCompactSupport.of_compactSpace f) heig
  have hzero := integral_laplaceBeltrami_eq_zero (hN.of_le (by simp))
    (HasCompactSupport.of_compactSpace N)
  have hsum : Integrable (fun y ↦ (Module.finrank ℝ E : ℝ) * laplaceBeltrami I N y +
      2 * (Module.finrank ℝ E : ℝ) * k * N y) (riemannianVolume I M) :=
    (hLint.const_mul _).add (hNint.const_mul _)
  rw [integral_sub hsum (hFint.const_mul _), integral_add (hLint.const_mul _)
    (hNint.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul, hzero,
    henergy]
  ring

/-- At the eigenvalue `n k`, both inequalities in the Bochner argument are equalities at every
point: the trace Cauchy–Schwarz defect `n |Hess f|² - (Δ f)²` and the Ricci defect
`n (Ric(grad f, grad f) - (n - 1) k |grad f|²)` vanish. By the Bochner formula, twice their
sum is the continuous Bochner defect, whose integral is zero. -/
private theorem defects_eq_zero_of_laplaceBeltrami_eq_neg_finrank_mul
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (heig : ∀ x, laplaceBeltrami I f x = -((Module.finrank ℝ E : ℝ) * k) * f x)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) (x : M) :
    (Module.finrank ℝ E : ℝ) * ∑ i, ∑ j, hessian I f x
        (stdOrthonormalBasis ℝ (TangentSpace I x) i)
        (stdOrthonormalBasis ℝ (TangentSpace I x) j) ^ 2 - laplaceBeltrami I f x ^ 2 = 0 ∧
      (Module.finrank ℝ E : ℝ) *
        ((CovariantDerivative.leviCivitaConnection I M).ricciTensor x
          (mgradient I f x) (mgradient I f x) -
          ((Module.finrank ℝ E : ℝ) - 1) * k * ‖mgradient I f x‖ ^ 2) = 0 := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  let n : ℝ := Module.finrank ℝ E
  let N : M → ℝ := fun y ↦ ‖mgradient I f y‖ ^ 2
  have hN : ContMDiff I 𝓘(ℝ) ∞ N := by
    simpa only [N, real_inner_self_eq_norm_sq] using contMDiff_inner_mgradient (n := ∞) hf hf
  have hderiv (y : M) :
      mvfderiv I (laplaceBeltrami I f) y (mgradient I f y) = -(n * k) * N y := by
    have heq : laplaceBeltrami I f = -(n * k) • f := funext heig
    rw [heq, mvfderiv_const_smul_field, smul_apply, smul_eq_mul,
      ← inner_mgradient, real_inner_self_eq_norm_sq]
  -- By the Bochner formula, the defect is twice the sum of the two nonnegative defects.
  have hS (y : M) : n * laplaceBeltrami I N y + 2 * n * k * N y - 2 * n ^ 2 * k ^ 2 * f y ^ 2 =
      2 * (n * ∑ i, ∑ j, hessian I f y
        (stdOrthonormalBasis ℝ (TangentSpace I y) i)
        (stdOrthonormalBasis ℝ (TangentSpace I y) j) ^ 2 - laplaceBeltrami I f y ^ 2) +
      2 * (n * ((CovariantDerivative.leviCivitaConnection I M).ricciTensor y
        (mgradient I f y) (mgradient I f y) - (n - 1) * k * N y)) := by
    have hB := laplaceBeltrami_norm_sq_mgradient hf y (stdOrthonormalBasis ℝ (TangentSpace I y))
    simp only [N, hB, hderiv, heig]
    ring
  have hdefects (y : M) := And.intro
    (laplaceBeltrami_sq_le_finrank_mul_sum_hessian_sq f y
      (stdOrthonormalBasis ℝ (TangentSpace I y)))
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E))
      (sub_nonneg.2 (hRic y (mgradient I f y))))
  -- A continuous nonnegative function with zero integral vanishes everywhere.
  let F : M → ℝ := fun y ↦
    n * laplaceBeltrami I N y + 2 * n * k * N y - 2 * n ^ 2 * k ^ 2 * f y ^ 2
  have hF : Continuous F :=
    ((continuous_const.mul (contMDiff_laplaceBeltrami (I := I) (n := 0) (m := ∞) (k := ∞)
      (by simp) (by simp) (hN.of_le (by simp))).continuous).add
        (continuous_const.mul hN.continuous)).sub (continuous_const.mul (hf.continuous.pow 2))
  have hzero : F x = 0 := by
    by_contra hne
    refine (hF.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := riemannianVolume I M)
      (HasCompactSupport.of_compactSpace F) (fun y ↦ ?_) hne).ne'
        (integral_bochnerDefect_eq_zero hf heig)
    obtain ⟨hD, hR⟩ := hdefects y
    simp only [F, Pi.zero_apply, hS]
    linarith
  simp only [F] at hzero
  rw [hS] at hzero
  obtain ⟨hD, hR⟩ := hdefects x
  constructor <;> linarith

/-- **The equality case of the Lichnerowicz estimate.** On a closed manifold with
`Ric ≥ (n - 1) k g`, a smooth function with `Δ f = -n k f` satisfies Obata's Hessian equation
`Hess f = -k f g`. The eigen-equation is stated for the native `Δ = div grad`. No hypothesis on
the dimension, on the sign of `k`, or on `f` is needed. -/
theorem hessian_eq_neg_mul_mul_inner_of_laplaceBeltrami_eq_neg_finrank_mul
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (heig : ∀ x, laplaceBeltrami I f x = -((Module.finrank ℝ E : ℝ) * k) * f x)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)
    (x : M) (v w : TangentSpace I x) :
    hessian I f x v w = -k * f x * ⟪v, w⟫_ℝ := by
  have hD := (defects_eq_zero_of_laplaceBeltrami_eq_neg_finrank_mul hf heig hRic x).1
  rw [hessian_eq_laplaceBeltrami_div_finrank_mul_inner_of_finrank_mul_sum_hessian_sq_le
    (stdOrthonormalBasis ℝ (TangentSpace I x)) (sub_eq_zero.1 hD).le, heig]
  rcases eq_or_ne (Module.finrank ℝ E : ℝ) 0 with hn | hn
  · -- In dimension zero every tangent vector vanishes.
    have : Subsingleton (TangentSpace I x) :=
      Module.finrank_zero_iff.1 ((finrank_tangentSpace x).trans (by exact_mod_cast hn))
    simp [Subsingleton.elim w 0]
  · field_simp

/-- In the equality case of the Lichnerowicz estimate, the Ricci lower bound is attained in the
direction of the gradient: `Ric(grad f, grad f) = (n - 1) k |grad f|²` at every point. -/
theorem ricciTensor_mgradient_eq_of_laplaceBeltrami_eq_neg_finrank_mul
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (heig : ∀ x, laplaceBeltrami I f x = -((Module.finrank ℝ E : ℝ) * k) * f x)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)
    (x : M) :
    (CovariantDerivative.leviCivitaConnection I M).ricciTensor x
        (mgradient I f x) (mgradient I f x) =
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖mgradient I f x‖ ^ 2 := by
  have hR := (defects_eq_zero_of_laplaceBeltrami_eq_neg_finrank_mul hf heig hRic x).2
  rcases eq_or_ne (Module.finrank ℝ E : ℝ) 0 with hn | hn
  · -- In dimension zero every tangent vector vanishes.
    have : Subsingleton (TangentSpace I x) :=
      Module.finrank_zero_iff.1 ((finrank_tangentSpace x).trans (by exact_mod_cast hn))
    simp [Subsingleton.elim (mgradient I f x) 0]
  · exact sub_eq_zero.1 ((mul_eq_zero.1 hR).resolve_left hn)

/-- On a closed manifold with `Ric ≥ (n - 1) k g`, a smooth function solves `Δ f = -n k f`
exactly when it solves Obata's Hessian equation `Hess f = -k f g`. The reverse implication is
the trace of the Hessian equation and needs neither the Ricci bound nor compactness. -/
theorem laplaceBeltrami_eq_neg_finrank_mul_iff_hessian_eq_neg_mul_mul_inner
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) :
    (∀ x, laplaceBeltrami I f x = -((Module.finrank ℝ E : ℝ) * k) * f x) ↔
      ∀ (x : M) (v w : TangentSpace I x), hessian I f x v w = -k * f x * ⟪v, w⟫_ℝ := by
  refine ⟨fun heig ↦ hessian_eq_neg_mul_mul_inner_of_laplaceBeltrami_eq_neg_finrank_mul hf heig
    hRic, fun hH x ↦ ?_⟩
  rw [laplaceBeltrami_eq_finrank_mul_of_hessian_eq_mul_inner (hH x)]
  ring

end Closed

end TauCeti.Manifold
