/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.Orientation

/-!
# Pairings of two-forms with pseudoholomorphic curves are bounded by area

Let `u : (C, j) → (X, J)` be a smooth pseudoholomorphic map from a surface, oriented so that the
frames `(e, j e)` are positive, and let `θ` and `σ` be two-forms on `X`. Pulled back along `u`, a
two-form is determined on each tangent plane of `C` by its value on one frame `(e, j e)`, and by
the Cauchy–Riemann equation `du (j e) = J (du e)` that value is `θ(du e, J (du e))`. Hence:

* if `θ(v, J v) ≥ 0` for every tangent vector `v` along `u`, then `u^* θ` is a nonnegative top
  form and `∫_C u^* θ ≥ 0` (`TauCeti.integralTopForm_mpullback_nonneg`, from the pointwise
  `TauCeti.SmoothTwoForm.apply_nonneg_of_eval₂_nonneg`);
* if `|θ(v, J v)| ≤ K σ(v, J v)` along `u`, then for compact `C`,
  `|∫_C u^* θ| ≤ K ∫_C u^* σ` (`TauCeti.abs_integralTopForm_mpullback_le`).

When `σ` is a symplectic form compatible with `J` and `g = σ(·, J ·)` is the associated metric,
the vectors `v` and `J v` are `g`-orthogonal of equal length, so `σ(v, J v) = |v|²` while
`|θ(v, J v)| ≤ ‖θ_x‖ |v| |J v| = ‖θ_x‖ |v|²` for the comass `‖θ_x‖` of `θ` at `x`
(`ContinuousAlternatingMap.le_opNorm`, with the operator norm identified with the comass by
`ContinuousAlternatingMap.opNorm_le_iff_le_mul_norm_ιMulti`). On a compact `X` the second hypothesis
therefore holds with `K` the maximal comass of `θ`: the integral `∫_C u^* θ` over a closed
pseudoholomorphic curve is bounded by the comass of `θ` times the symplectic area `∫_C u^* σ`.

The intended application bounds, for a basis of closed two-forms, every real pairing of the
homology class of a curve of bounded area, and then uses `TauCeti.finite_setOf_forall_abs_apply_le`
to leave only finitely many possible classes. That step depends on identifying `∫_C u^* θ` with
the pairing of `[θ]` with the class of the curve, a de Rham comparison not provided here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347, §1.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893, §2.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C]
  {J : SmoothAlmostComplexStructure I X} {j : SmoothAlmostComplexStructure I' C}
  {o : Manifold.Orientation I' C (Fin 2)} {u : C → X}

/-- **Nonnegativity of the pairing with a pseudoholomorphic curve.** Let `u` be a smooth
pseudoholomorphic map from a surface `C`, oriented so that the frames `(e, j e)` are positive. If
`θ(v, J v) ≥ 0` for every tangent vector `v` along `u`, then `∫_C u^* θ ≥ 0`. -/
theorem integralTopForm_mpullback_nonneg (hu : ContMDiff I' I ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {θ : SmoothTwoForm I X}
    (hθ : ∀ c (v : TangentSpace I (u c)), 0 ≤ SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)) :
    0 ≤ integralTopForm o (SmoothForm.mpullback u hu θ).1 :=
  integralTopForm_nonneg o fun c b hb ↦
    SmoothTwoForm.apply_nonneg_of_eval₂_nonneg (SmoothForm.mpullback u hu θ) (ho c) (fun e ↦ by
      rw [SmoothForm.eval₂_mpullback, (hhol c).mfderiv_apply_commute]
      exact hθ c _) b hb

/-- **Pairings with a pseudoholomorphic curve are bounded by area.** Let `u` be a smooth
pseudoholomorphic map from a compact surface `C`, oriented so that the frames `(e, j e)` are
positive. If `|θ(v, J v)| ≤ K σ(v, J v)` for every tangent vector `v` along `u`, then
`|∫_C u^* θ| ≤ K ∫_C u^* σ`. For a symplectic form `σ` compatible with `J`, the hypothesis holds
with `K` any bound for the comass of `θ` in the metric `σ(·, J ·)`. -/
theorem abs_integralTopForm_mpullback_le [CompactSpace C] (hu : ContMDiff I' I ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) {θ σ : SmoothTwoForm I X} {K : ℝ}
    (hK : ∀ c (v : TangentSpace I (u c)),
      |SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)| ≤
        K * SmoothBundleForm.eval₂ σ (u c) v (J (u c) v)) :
    |integralTopForm o (SmoothForm.mpullback u hu θ).1| ≤
      K * integralTopForm o (SmoothForm.mpullback u hu σ).1 := by
  -- `K • σ + s • θ` is nonnegative on the complex lines along `u` whenever `|s| ≤ 1`.
  have key (s : ℝ) (hs : |s| ≤ 1) :
      0 ≤ K * integralTopForm o (SmoothForm.mpullback u hu σ).1 +
        s * integralTopForm o (SmoothForm.mpullback u hu θ).1 := by
    have hpt (c : C) (v : TangentSpace I (u c)) :
        0 ≤ SmoothBundleForm.eval₂ (K • σ + s • θ) (u c) v (J (u c) v) := by
      have hs' : |s * SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)| ≤
          |SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)| := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) hs
      rw [SmoothBundleForm.eval₂_add, SmoothForm.eval₂_smul, SmoothForm.eval₂_smul, smul_eq_mul,
        smul_eq_mul]
      linarith [neg_abs_le (s * SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)), hK c v]
    have hσ : IsSmoothForm I' 0 (SmoothForm.mpullback u hu σ).1 :=
      (SmoothForm.isSmoothForm _).of_le (by simp)
    have hθ : IsSmoothForm I' 0 (SmoothForm.mpullback u hu θ).1 :=
      (SmoothForm.isSmoothForm _).of_le (by simp)
    simpa only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul,
      integralTopForm_add_of_compactSpace o (hσ.smul K) (hθ.smul s), integralTopForm_smul]
      using integralTopForm_mpullback_nonneg hu ho hhol hpt
  have h₁ := key 1 (by simp)
  have h₂ := key (-1) (by simp)
  rw [abs_le]
  constructor <;> linarith

end TauCeti
