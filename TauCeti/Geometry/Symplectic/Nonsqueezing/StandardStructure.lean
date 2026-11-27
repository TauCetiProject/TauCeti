/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pushforward
public import TauCeti.Geometry.Symplectic.Nonsqueezing.Monotonicity
import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic

/-!
# Extending the standard structure from an embedded ball

Let `φ` be a partial diffeomorphism from a finite-dimensional complex inner product space `E`,
such as `ℂⁿ`, into a Hausdorff σ-compact manifold `M` with a nondegenerate two-form `σ`, and
suppose that `φ` pulls `σ` back to the standard symplectic form `Im ⟪·, ·⟫_ℂ` on an open set
`W`. For every compact `K ⊆ W` this file constructs a smooth almost complex structure `J` on `M`,
compatible with `σ`, for which `φ` is pseudoholomorphic from multiplication by `i` at the points
of `K`: `dφ (i v) = J (dφ v)` (`PartialDiffeomorph.exists_compatible_mfderiv_I_smul`). It is the
standard structure of `E` pushed forward along `φ` and extended by the relative construction of
compatible structures.

In Gromov's proof of the nonsqueezing theorem, `φ` is a symplectic embedding of a ball `B(c, r)`
into `S²(a) × T²ⁿ⁻²`, and the structure is extended from the closed ball of each radius `r' < r`.
By the monotonicity of holomorphic curves in the standard ball
(`TauCeti.pi_mul_sq_le_integralTopForm_mpullback`), every nonconstant pseudoholomorphic sphere
through the centre `φ c` then has symplectic area at least `π r'²`
(`PartialDiffeomorph.exists_compatible_forall_pi_mul_sq_le_integralTopForm_mpullback`).

## Main results

* `PartialDiffeomorph.exists_compatible_mfderiv_I_smul`: a `σ`-compatible structure extending the
  pushed-forward standard structure from a compact set.
* `PartialDiffeomorph.exists_compatible_forall_pi_mul_sq_le_integralTopForm_mpullback`: for that
  structure, extended from the closed ball of radius `r'` about `c`, nonconstant pseudoholomorphic
  spheres through `φ c` have area at least `π r'²`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §0.3.A (the nonsqueezing theorem).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 9.3 (the almost complex structure extending the
  pushed-forward standard structure on an embedded ball).
-/

public section

noncomputable section

open Set Metric
open scoped Manifold ContDiff InnerProductSpace Real TauCeti.ComplexManifold

namespace PartialDiffeomorph

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {σ : SmoothTwoForm I M}

/-- **Extending the pushed-forward standard structure.** Let `φ` be a partial diffeomorphism from
a finite-dimensional complex inner product space `E` into a Hausdorff σ-compact manifold with a
nondegenerate two-form `σ`, pulling `σ` back to `Im ⟪·, ·⟫_ℂ` on an open subset `W` of its
source. For every compact `K ⊆ W` there is a smooth `σ`-compatible almost complex structure `J`
with `dφ_x (i v) = J (dφ_x v)` at every point `x` of `K`. -/
theorem exists_compatible_mfderiv_I_smul (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hσ : σ.IsNondegenerate) {W : Set E} (hW : IsOpen W) (hWs : W ⊆ φ.source)
    (hφ : ∀ x ∈ W, ∀ v w : E,
      σ.eval₂ (φ x) (mfderiv 𝓘(ℝ, E) I φ x v) (mfderiv 𝓘(ℝ, E) I φ x w) = (⟪v, w⟫_ℂ).im)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      ∀ x ∈ K, ∀ v : E,
        mfderiv 𝓘(ℝ, E) I φ x (Complex.I • v) = J (φ x) (mfderiv 𝓘(ℝ, E) I φ x v) := by
  -- Every tangent space of `E` is `E`, where the standard structure is multiplication by `i`.
  have hstd (x : E) : (SmoothAlmostComplexStructure.ofComplexManifold E E).almostComplexStructureAt
      x = (AlmostComplexStructure.ofComplexModule E : AlmostComplexStructure E) := by
    rw [SmoothAlmostComplexStructure.ofComplexManifold_self_eq_constSmooth,
      AlmostComplexStructure.constSmooth_almostComplexStructureAt]
  obtain ⟨J, hJ, hK'⟩ := φ.exists_compatible_mfderiv_apply_eq
    (SmoothAlmostComplexStructure.ofComplexManifold E E) hσ hW hWs
    (fun _ ↦ imInnerSymplecticForm E)
    (fun x _ ↦ hstd x ▸ imInnerSymplecticForm_compatible (E := E))
    (fun x hx v w ↦ (hφ x hx v w).trans (imInnerSymplecticForm_apply (E := E) v w).symm) hK hKW
  refine ⟨J, hJ, fun x hx v ↦ ?_⟩
  rw [← hK' x hx v, SmoothAlmostComplexStructure.ofComplexManifold_apply]

/-- **Area of spheres through the centre of an embedded ball.** Let `φ` be a partial
diffeomorphism from a finite-dimensional complex inner product space into a Hausdorff σ-compact
manifold with a nondegenerate two-form `σ`, defined on the ball `B(c, r)` and pulling `σ` back to
`Im ⟪·, ·⟫_ℂ` there, and let `0 ≤ r' < r`. There is a smooth `σ`-compatible almost complex
structure `J` for which every nonconstant smooth `J`-holomorphic sphere through `φ c` has
symplectic area at least `π r'²`. -/
theorem exists_compatible_forall_pi_mul_sq_le_integralTopForm_mpullback
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (hσ : σ.IsNondegenerate) {c : E} {r r' : ℝ}
    (hball : ball c r ⊆ φ.source)
    (hφ : ∀ x ∈ ball c r, ∀ v w : E,
      σ.eval₂ (φ x) (mfderiv 𝓘(ℝ, E) I φ x v) (mfderiv 𝓘(ℝ, E) I φ x w) = (⟪v, w⟫_ℂ).im)
    (hr' : 0 ≤ r') (hr'r : r' < r) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      ∀ (u : OnePoint ℂ → M) (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u),
        IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J u →
        (∃ z₀, u z₀ = φ c) → (∃ y, u y ≠ φ c) →
        π * r' ^ 2 ≤ integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
          (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
          (SmoothForm.mpullback u hu σ).val := by
  have hsub : closedBall c r' ⊆ ball c r := closedBall_subset_ball hr'r
  obtain ⟨J, hJ, hJK⟩ := φ.exists_compatible_mfderiv_I_smul hσ isOpen_ball hball hφ
    (isCompact_closedBall c r') hsub
  refine ⟨J, hJ, fun u hu hhol ⟨z₀, hz₀⟩ hnc ↦ ?_⟩
  have hin : ball c r' ⊆ ball c r := ball_subset_closedBall.trans hsub
  exact pi_mul_sq_le_integralTopForm_mpullback hJ.tames (hin.trans hball)
    (fun x hx ↦ hφ x (hin hx)) (fun x hx ↦ hJK x (ball_subset_closedBall hx)) hu hhol hr' hz₀ hnc

end PartialDiffeomorph
