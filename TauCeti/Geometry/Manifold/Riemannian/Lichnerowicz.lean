/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Bochner
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The Lichnerowicz eigenvalue estimate

On a closed Riemannian manifold of dimension `n ≥ 2` with `Ric ≥ (n - 1) k g`,
every nonzero smooth eigenfunction of the nonnegative scalar Laplacian with positive
eigenvalue `λ` satisfies `λ ≥ n k`. The sign convention here is
`laplaceBeltrami f = -λ f`; no new Laplacian or spectral carrier is introduced.
The estimate applies to every positive eigenvalue, so in particular to the first one
once a compact spectral construction supplies its smooth eigenfunction.

The proof integrates the Bochner inequality and uses Green's identity. The pointwise
trace estimate and Bochner inequality are also available without compactness.
Connectedness and a mean-zero hypothesis are unnecessary for this estimate.
No existence of eigenfunctions or rigidity of the equality case is asserted here.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Chapter 9 (the Bochner technique
  and the Lichnerowicz estimate).
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

section Trace

variable [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The squared trace of the Hessian is at most the dimension times its squared norm,
expressed in any orthonormal basis. This includes dimension zero. -/
theorem laplaceBeltrami_sq_le_finrank_mul_sum_hessian_sq (f : M → ℝ) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    laplaceBeltrami I f x ^ 2 ≤ (Module.finrank ℝ E : ℝ) *
      ∑ i, ∑ j, hessian I f x (b i) (b j) ^ 2 := by
  classical
  have hcard : Fintype.card ι = Module.finrank ℝ E := by
    rw [← Module.finrank_eq_card_basis b.toBasis, finrank_tangentSpace]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι ↦ (1 : ℝ)) (fun i ↦ hessian I f x (b i) (b i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, hcard] at hcs
  rw [laplaceBeltrami_eq_sum_hessian I f x b]
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact Finset.sum_le_sum fun i _ ↦ Finset.single_le_sum
    (f := fun j ↦ hessian I f x (b i) (b j) ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)

end Trace

variable [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The dimension-weighted Bochner inequality under a Ricci lower bound. It is local,
requires no dimension restriction, and uses `Δ = div grad` rather than `Δ⁺`. -/
theorem bochner_inequality_of_ricci_lower_bound
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hRic : ∀ (x : M) (v : TangentSpace I x),
      ((Module.finrank ℝ E : ℝ) - 1) * k * ‖v‖ ^ 2 ≤
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v v) (x : M) :
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
  have hcurv := mul_le_mul_of_nonneg_left (hRic x (mgradient I f x))
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
  have hG : ContMDiff I I.tangent ∞ (T% (mgradient I f)) := contMDiff_mgradient hf
  have hN : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ ‖mgradient I f x‖ ^ 2) := by
    have hinner : ContMDiff I 𝓘(ℝ) ∞
        (fun x ↦ inner ℝ (mgradient I f x) (mgradient I f x)) :=
      ContMDiff.inner_bundle (IB := I) (F := E)
        (E := fun x : M ↦ TangentSpace I x) (b := id) hG hG
    simpa only [real_inner_self_eq_norm_sq] using hinner
  have hFint : Integrable (fun x ↦ f x ^ 2) μ :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNint : Integrable (fun x ↦ ‖mgradient I f x‖ ^ 2) μ :=
    hN.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hL := contMDiff_laplaceBeltrami (I := I) (n := 0) (m := ∞) (k := ∞)
    (by simp) (by simp) (hN.of_le (by simp))
  have hLint : Integrable (laplaceBeltrami I (fun x ↦ ‖mgradient I f x‖ ^ 2)) μ :=
    hL.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Green's identity gives the eigenfunction energy identity.
  have henergy : ∫ x, ‖mgradient I f x‖ ^ 2 ∂μ = lam * ∫ x, f x ^ 2 ∂μ := by
    have h := integral_mul_laplaceBeltrami (hf.of_le (by simp))
      (HasCompactSupport.of_compactSpace f) (hf.of_le (by simp))
    simp only [heig, real_inner_self_eq_norm_sq] at h
    have hfun : (fun x ↦ f x * (-lam * f x)) = fun x ↦ -lam * f x ^ 2 := by
      ext x
      ring
    rw [hfun, integral_const_mul] at h
    linarith
  -- The Laplacian of the squared gradient has integral zero.
  have hzero : ∫ x, laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x ∂μ = 0 := by
    have h := integral_mul_laplaceBeltrami (f := fun _ : M ↦ (1 : ℝ)) contMDiff_const
      (HasCompactSupport.of_compactSpace _) (hN.of_le (by simp))
    simpa [mgradient_const] using h
  have hderiv (x : M) : mvfderiv I (laplaceBeltrami I f) x (mgradient I f x) =
      -lam * ‖mgradient I f x‖ ^ 2 := by
    have heq : laplaceBeltrami I f = -lam • f := funext heig
    rw [heq, mvfderiv_const_smul_field, smul_apply, smul_eq_mul,
      ← inner_mgradient, real_inner_self_eq_norm_sq]
  have hpoint (x : M) : 2 * lam ^ 2 * f x ^ 2 +
      (2 * n * ((n - 1) * k - lam)) * ‖mgradient I f x‖ ^ 2 ≤
      n * laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x := by
    have h := bochner_inequality_of_ricci_lower_bound hf hRic x
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
    (hf.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun _ ↦ sq_nonneg _) (pow_ne_zero 2 hx)
  have hn' : 1 < n := by dsimp [n]; exact_mod_cast (show 1 < Module.finrank ℝ E by omega)
  have hfactor : 0 < 2 * lam * (n - 1) * ∫ x, f x ^ 2 ∂μ := by positivity
  by_contra hlt
  have hneg : 0 < n * k - lam := sub_pos.2 (lt_of_not_ge hlt)
  nlinarith [mul_pos hfactor hneg]

end Closed

end TauCeti.Manifold
