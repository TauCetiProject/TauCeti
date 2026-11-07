/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Lichnerowicz.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Square
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# Equality in the Lichnerowicz estimate

On a closed Riemannian manifold of dimension `n` with `Ric ≥ (n - 1) k g`, a smooth
function satisfying `Δ f = -n k f` has `Hess f = -k f g`. Here `Δ = div grad` is the
native `laplaceBeltrami`. This Hessian equation is the input to Obata rigidity.

The result does not require connectedness, orientability, a nonzero function, or a
positive `k`. It includes dimensions zero and one: in dimension one the assumed
eigenvalue is exactly `k`; the vacuous Ricci bound does not impose an eigenvalue bound.

The proof uses the existing Bochner identity and Green energy identity. The scalar
Bochner defect is continuous, nonnegative and has zero integral against the canonical
Riemannian volume, so full support forces it to vanish at every point. Completing the
square in an arbitrary orthonormal basis then gives the Hessian equation without any
regularity assumption on a family of bases. The vanishing defect also forces the Ricci lower
bound to be attained in the direction of `grad f`. Conversely, tracing the Hessian equation
recovers `Δ f = -n k f`, so under the Ricci bound the two equations are equivalent.

## Main results

* `TauCeti.Manifold.hessian_eq_neg_mul_inner_of_laplaceBeltrami_eq_neg_mul`: the equality
  case `Δ f = -n k f` forces `Hess f = -k f g`.
* `TauCeti.Manifold.ricciTensor_mgradient_eq_of_laplaceBeltrami_eq_neg_mul`: in the equality
  case, `Ric(grad f, grad f) = (n - 1) k |grad f|²`.
* `TauCeti.Manifold.laplaceBeltrami_eq_neg_mul_iff_hessian_eq_neg_mul_inner`: under the Ricci
  bound, `Δ f = -n k f` if and only if `Hess f = -k f g`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016),
  Chapter 9 (equality in the Lichnerowicz estimate).
-/

public section

open Bundle MeasureTheory
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {k : ℝ}

private theorem lichnerowicz_defect_eq_zero (hn : 0 < Module.finrank ℝ E)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (heig : ∀ x, laplaceBeltrami I f x = -((Module.finrank ℝ E : ℝ) * k) * f x)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) (x : M) :
    (1 / 2 : ℝ) * laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x +
      k * ‖mgradient I f x‖ ^ 2 - (Module.finrank ℝ E : ℝ) * k ^ 2 * f x ^ 2 = 0 := by
  let _ := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  let n : ℝ := Module.finrank ℝ E
  let N := fun y ↦ ‖mgradient I f y‖ ^ 2
  let D := fun y ↦ (1 / 2 : ℝ) * laplaceBeltrami I N y + k * N y - n * k ^ 2 * f y ^ 2
  have hn' : 0 < n := by dsimp [n]; exact_mod_cast hn
  let _ : IsManifold I (2 + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hN := contMDiff_norm_sq_mgradient (n := 2) (hf.of_le (by simp))
  have hL := contMDiff_laplaceBeltrami (I := I) (n := 0) (m := ∞) (k := ∞)
    (by simp) (by simp) hN
  have he := integral_norm_sq_mgradient_eq_mul_integral_sq_of_laplaceBeltrami_eq_neg_mul
    (hf.of_le (by simp)) (HasCompactSupport.of_compactSpace f) heig
  have hz := integral_laplaceBeltrami_eq_zero hN (HasCompactSupport.of_compactSpace _)
  have hD : Continuous D := ((hL.continuous.const_mul _).add (hN.continuous.const_mul _)).sub
    ((hf.continuous.pow 2).const_mul _)
  -- The dimension-weighted Bochner inequality makes the scalar defect nonnegative.
  have hnonneg (y : M) : 0 ≤ D y := by
    have h := le_finrank_mul_laplaceBeltrami_norm_sq_mgradient hf y (hRic y)
    have hderiv :=
      mvfderiv_laplaceBeltrami_mgradient_of_laplaceBeltrami_eq_neg_mul heig y
    rw [heig, hderiv] at h
    have hnd : 0 ≤ n * D y := by dsimp only [D, N, n] at h ⊢; nlinarith
    exact nonneg_of_mul_nonneg_right hnd hn'
  have hDi := hD.integrable_of_hasCompactSupport
    (μ := riemannianVolume I M) (HasCompactSupport.of_compactSpace _)
  -- Green's energy identity cancels the remaining two integrals.
  have hzero : ∫ y, D y ∂riemannianVolume I M = 0 := by
    have hfi : Integrable (fun y ↦ f y ^ 2) (riemannianVolume I M) :=
      (hf.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hNi := hN.continuous.integrable_of_hasCompactSupport
      (μ := riemannianVolume I M) (HasCompactSupport.of_compactSpace _)
    have hLi := hL.continuous.integrable_of_hasCompactSupport
      (μ := riemannianVolume I M) (HasCompactSupport.of_compactSpace _)
    dsimp only [D]
    rw [integral_sub ((hLi.const_mul (1 / 2 : ℝ)).fun_add (hNi.const_mul k))
      (hfi.const_mul (n * k ^ 2)),
      integral_add (hLi.const_mul (1 / 2 : ℝ)) (hNi.const_mul k)]
    simp only [integral_const_mul, hz, mul_zero, zero_add]
    rw [he]
    ring
  -- Full support upgrades almost-everywhere vanishing to pointwise vanishing.
  exact congrFun (Measure.eq_of_ae_eq ((integral_eq_zero_iff_of_nonneg hnonneg hDi).1 hzero)
    hD continuous_zero) x

/-- **Equality in the Lichnerowicz estimate.** On a closed manifold with
`Ric ≥ (n - 1) k g`, an eigenfunction of `Δ⁺` with eigenvalue `n k` satisfies
`Hess f = -k f g`. No positivity or nonvanishing assumption is needed for this implication. -/
theorem hessian_eq_neg_mul_inner_of_laplaceBeltrami_eq_neg_mul
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (heig : ∀ x, laplaceBeltrami I f x = -(Module.finrank ℝ E : ℝ) * k * f x)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)
    (x : M) (u v : TangentSpace I x) :
    hessian I f x u v = -k * f x * ⟪u, v⟫_ℝ := by
  classical
  by_cases hn : Module.finrank ℝ E = 0
  · have : Subsingleton (TangentSpace I x) := (Module.finrank_zero_iff (R := ℝ)).1 (by
      rw [finrank_tangentSpace (I := I) x, hn])
    rw [Subsingleton.elim u 0]
    simp
  have heig' : ∀ y, laplaceBeltrami I f y = -((Module.finrank ℝ E : ℝ) * k) * f y := by
    simpa only [neg_mul] using heig
  have hD := lichnerowicz_defect_eq_zero (Nat.pos_of_ne_zero hn) hf heig' hRic x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let A : Matrix (Fin (Module.finrank ℝ (TangentSpace I x)))
      (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ := fun i j ↦ hessian I f x (b i) (b j)
  have hderiv :=
    mvfderiv_laplaceBeltrami_mgradient_of_laplaceBeltrami_eq_neg_mul heig' x
  have hb := laplaceBeltrami_norm_sq_mgradient hf x b
  rw [hderiv] at hb
  have hs : (∑ i, ∑ j, A i j ^ 2) ≤ (Module.finrank ℝ E : ℝ) * (-k * f x) ^ 2 := by
    have hr := hRic x (mgradient I f x)
    dsimp only [A]
    nlinarith
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ E := by simp
  have hscalar := Matrix.eq_scalar_of_trace_eq_of_sum_sq_le A (-k * f x)
    (by
      have htrace : A.trace = laplaceBeltrami I f x :=
        (laplaceBeltrami_eq_sum_hessian I f x b).symm
      rw [htrace, heig, hcard]
      ring)
    (by simpa only [hcard] using hs)
  have hentry (i j) : hessian I f x (b i) (b j) = -k * f x * ⟪b i, b j⟫_ℝ := by
    have h := congrFun (congrFun hscalar i) j
    simpa only [A, Matrix.scalar_apply, Matrix.diagonal_apply, b.inner_eq_ite,
      mul_ite, mul_one, mul_zero] using h
  -- A continuous linear map is determined by its pairings on an orthonormal basis.
  have hmap : CovariantDerivative.leviCivitaConnection I M (mgradient I f) x =
      (-k * f x) • ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    apply InnerProductSpace.ext_inner_right_basis b.toBasis
    intro j
    simpa only [hessian_def, ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis,
      smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left] using hentry i j
  rw [hessian_def, hmap, smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left]

/-- In the equality case of the Lichnerowicz estimate, the Ricci lower bound is attained in the
direction of the gradient: `Ric(grad f, grad f) = (n - 1) k |grad f|²` at every point. -/
theorem ricciTensor_mgradient_eq_of_laplaceBeltrami_eq_neg_mul
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (heig : ∀ x, laplaceBeltrami I f x = -(Module.finrank ℝ E : ℝ) * k * f x)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v)
    (x : M) :
    (CovariantDerivative.leviCivitaConnection I M).ricciTensor x
        (mgradient I f x) (mgradient I f x) =
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖mgradient I f x‖ ^ 2 := by
  by_cases hn : Module.finrank ℝ E = 0
  · have : Subsingleton (TangentSpace I x) := (Module.finrank_zero_iff (R := ℝ)).1 (by
      rw [finrank_tangentSpace (I := I) x, hn])
    rw [Subsingleton.elim (mgradient I f x) 0]
    simp
  have hn' : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Nat.pos_of_ne_zero hn
  have heig' : ∀ y, laplaceBeltrami I f y = -((Module.finrank ℝ E : ℝ) * k) * f y := by
    simpa only [neg_mul] using heig
  have hD := lichnerowicz_defect_eq_zero (Nat.pos_of_ne_zero hn) hf heig' hRic x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hb := laplaceBeltrami_norm_sq_mgradient hf x b
  rw [mvfderiv_laplaceBeltrami_mgradient_of_laplaceBeltrami_eq_neg_mul heig' x] at hb
  -- Trace Cauchy–Schwarz bounds the squared Hessian norm below by `n k² f²`.
  have hcs := laplaceBeltrami_sq_le_finrank_mul_sum_hessian_sq f x b
  rw [heig'] at hcs
  have hS : (Module.finrank ℝ E : ℝ) * k ^ 2 * f x ^ 2 ≤
      ∑ i, ∑ j, hessian I f x (b i) (b j) ^ 2 :=
    le_of_mul_le_mul_left (by linarith) hn'
  refine le_antisymm ?_ (hRic x _)
  linarith

/-- On a closed manifold with `Ric ≥ (n - 1) k g`, a smooth function solves `Δ f = -n k f`
exactly when it solves the Hessian equation `Hess f = -k f g`. The reverse implication is the
trace of the Hessian equation and needs neither the Ricci bound nor compactness. -/
theorem laplaceBeltrami_eq_neg_mul_iff_hessian_eq_neg_mul_inner
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) :
    (∀ x, laplaceBeltrami I f x = -(Module.finrank ℝ E : ℝ) * k * f x) ↔
      ∀ (x : M) (u v : TangentSpace I x), hessian I f x u v = -k * f x * ⟪u, v⟫_ℝ := by
  refine ⟨fun heig ↦ hessian_eq_neg_mul_inner_of_laplaceBeltrami_eq_neg_mul hf heig hRic,
    fun hH x ↦ ?_⟩
  rw [laplaceBeltrami_eq_finrank_mul_of_hessian_eq_mul_inner (hH x)]
  ring

end TauCeti.Manifold
