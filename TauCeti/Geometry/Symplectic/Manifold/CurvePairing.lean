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

/-!
# Pairings of two-forms with pseudoholomorphic curves are bounded by area

Let `u : (C, j) → (X, J)` be a smooth pseudoholomorphic map from a surface, oriented so that the
frames `(e, j e)` are positive, and let `θ` and `σ` be two-forms on `X`. Pulled back along `u`, a
two-form is determined on each tangent plane of `C` by its value on one frame `(e, j e)`, and by
the Cauchy–Riemann equation `du (j e) = J (du e)` that value is `θ(du e, J (du e))`. Hence:

* if `θ(v, J v) ≥ 0` for every tangent vector `v` along `u`, then `u^* θ` is a nonnegative top
  form and `∫_C u^* θ ≥ 0` (`TauCeti.integralTopForm_mpullback_nonneg`);
* if `|θ(v, J v)| ≤ K σ(v, J v)` along `u`, then for compact `C`,
  `|∫_C u^* θ| ≤ K ∫_C u^* σ` (`TauCeti.abs_integralTopForm_mpullback_le`).

When `σ` is a symplectic form compatible with `J` and `g = σ(·, J ·)` is the associated metric,
the vectors `v` and `J v` are `g`-orthogonal of equal length, so `σ(v, J v) = |v|²` while
`|θ(v, J v)| ≤ ‖θ_x‖ |v| |J v| = ‖θ_x‖ |v|²` for the comass `‖θ_x‖` of `θ` at `x`
(`ContinuousAlternatingMap.le_opNorm`, with the operator norm identified with the comass by
`ContinuousAlternatingMap.opNorm_le_iff_le_mul_norm_ιMulti`). On a compact `X` the second hypothesis
therefore holds with `K` the maximal comass of `θ`: the pairing of a closed two-form with the
fundamental class of a closed pseudoholomorphic curve is bounded by the comass of the form times
the symplectic area of the curve. Applied to a basis of closed two-forms, this bounds every real
pairing of the homology class of a curve of bounded area, which by
`TauCeti.finite_setOf_forall_abs_apply_le` leaves only finitely many possible classes.

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

/-- A two-form on a surface that is nonnegative on the complex frames `(e, j e)` is nonnegative on
every positively oriented basis, when the frames `(e, j e)` are positively oriented. -/
theorem SmoothTwoForm.apply_nonneg_of_eval₂_nonneg (α : SmoothTwoForm I' C) {c : C}
    (ho : ∀ (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hα : ∀ e, 0 ≤ SmoothBundleForm.eval₂ α c e (j c e))
    (b : Basis (Fin 2) ℝ (TangentSpace I' c)) (hb : b.orientation = o.orientationAt c) :
    0 ≤ α.1 c b := by
  -- The complex frame `b₀ = (b 0, j (b 0))`.
  set b₀ := basisOfLinearIndependentOfCardEqFinrank
    ((j.almostComplexStructureAt c).linearIndependent_pair (b.ne_zero 0))
    (by simpa using (o.finrank_tangentSpace_eq c).symm)
  have hb₀ : ⇑b₀ = ![b 0, j c (b 0)] := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  -- A top form on the plane is its value on the frame `b₀` times `det_{b₀}`.
  have hα' : α.1 c b = α.1 c b₀ * b₀.det b := by
    simpa using congrArg (fun f ↦ f b) ((α.1 c).toAlternatingMap.eq_smul_basis_det b₀)
  rw [hα']
  refine mul_nonneg ?_ ((b₀.orientation_eq_iff_det_pos b).1 ?_).le
  · rw [hb₀, ← SmoothBundleForm.eval₂_apply]
    exact hα _
  · rw [hb, ho b₀ (by rw [hb₀]; simp)]

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

/-- The integral of the pullback of a combination `a • σ + b • θ` of two-forms along a smooth map
from a compact manifold is the same combination of the integrals. -/
private theorem integralTopForm_mpullback_smul_add_smul [CompactSpace C]
    (hu : ContMDiff I' I ∞ u) (σ θ : SmoothTwoForm I X) (a b : ℝ) :
    integralTopForm o (SmoothForm.mpullback u hu (a • σ + b • θ)).1 =
      a * integralTopForm o (SmoothForm.mpullback u hu σ).1 +
        b * integralTopForm o (SmoothForm.mpullback u hu θ).1 := by
  rw [map_add, map_smul, map_smul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    integralTopForm_add o (((SmoothForm.isSmoothForm _).of_le (by simp)).smul a)
      (((SmoothForm.isSmoothForm _).of_le (by simp)).smul b)
      (isClosed_tsupport _).isCompact (isClosed_tsupport _).isCompact,
    integralTopForm_smul, integralTopForm_smul]

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
    rw [← integralTopForm_mpullback_smul_add_smul]
    refine integralTopForm_mpullback_nonneg hu ho hhol fun c v ↦ ?_
    have h := hK c v
    have hs' : |s * SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)| ≤
        |SmoothBundleForm.eval₂ θ (u c) v (J (u c) v)| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hs
    simp only [SmoothBundleForm.eval₂_apply] at h hs' ⊢
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    linarith [neg_abs_le (s * θ.1 (u c) ![v, J (u c) v])]
  have h₁ := key 1 (by simp)
  have h₂ := key (-1) (by simp)
  rw [abs_le]
  constructor <;> linarith

end TauCeti
