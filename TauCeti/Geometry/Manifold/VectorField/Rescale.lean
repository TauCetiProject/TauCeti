/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.StrictInward
public import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Manifold.Exhaustion
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Slowing vector fields along an exhaustion

A smooth vector field can be multiplied by a strictly positive smooth function so that the
absolute value of its derivative of a prescribed smooth real function is at most any given
positive constant. Positive multiplication preserves strict inwardness, unlike a compactly
supported cutoff, which can vanish at boundary points.

Combining this rescaling with a proper exhaustion gives a smooth strictly inward field with
bounded exhaustion speed on every finite-dimensional Hausdorff sigma-compact manifold with
corners. The speed bound controls escape to infinity along finite-time integral curves; it
does not assert existence of integral curves at boundary points.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 8–9, for rescaling vector
  fields and inward-pointing flows. The rescaling here uses the explicit positive factor
  `2 * ε / (1 + df(X)^2)` and applies to arbitrary models with corners.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth vector field admits a strictly positive smooth multiplier that bounds its speed
along any prescribed smooth real function. No compactness or boundarylessness is needed. -/
theorem _root_.ContMDiff.exists_pos_contMDiffMap_abs_mvfderiv_smul_le [IsManifold I 1 M]
    {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < a x) ∧
      ∀ x, |mvfderiv I f x (a x • X x)| ≤ ε := by
  let g : M → ℝ := fun x ↦ mvfderiv I f x (X x)
  have hg : ContMDiff I 𝓘(ℝ) ∞ g :=
    (hf.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp hX
  have hden (x : M) : 0 < 1 + g x ^ 2 := by positivity
  let a : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x ↦ 2 * ε / (1 + g x ^ 2),
      contMDiff_const.div₀ (contMDiff_const.add (hg.pow 2)) (fun x ↦ (hden x).ne')⟩
  have ha (x : M) : 0 < a x := div_pos (mul_pos (by norm_num) hε) (hden x)
  refine ⟨a, ha, fun x ↦ ?_⟩
  rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (ha x)]
  dsimp [a]
  rw [div_mul_eq_mul_div, div_le_iff₀ (hden x)]
  have hsq := sq_nonneg (|g x| - 1)
  have habs : |g x| ^ 2 = g x ^ 2 := sq_abs _
  dsimp [g] at habs hsq ⊢
  nlinarith

/-- There are a nonnegative smooth proper exhaustion and a smooth strictly inward field whose
exhaustion speed is uniformly bounded by a prescribed positive constant. In particular, the
bound may be chosen to be `1 / 2`. -/
theorem exists_strictInward_isProperMap_abs_mvfderiv_le [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      IsProperMap f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x, X x ∈ strictInwardTangentCone I x) ∧
      ∀ x, |mvfderiv I f x (X x)| ≤ ε := by
  obtain ⟨f, hf, hf₀⟩ := exists_contMDiffMap_isProperMap_nonneg (M := M) I
  obtain ⟨Y, hY⟩ := exists_contMDiffSection_mem_strictInwardTangentCone (M := M) I
  obtain ⟨a, ha, hab⟩ := f.contMDiff.exists_pos_contMDiffMap_abs_mvfderiv_smul_le Y.contMDiff hε
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun x ↦ a x • Y x, a.contMDiff.smul_section Y.contMDiff⟩
  exact ⟨f, X, hf, hf₀, fun x ↦ (smul_mem_strictInwardTangentCone_iff (ha x)).2 (hY x), hab⟩

end TauCeti
