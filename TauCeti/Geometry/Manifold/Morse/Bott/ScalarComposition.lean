/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.Morse.ScalarComposition
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level

/-!
# Morse–Bott levels of a scalar reparametrization

Let `g` be a real function on a boundaryless finite-dimensional manifold `M` and `φ : ℝ → ℝ` a
change of values with a nondegenerate critical point at `c`: `φ'(c) = 0` and `φ''(c) ≠ 0`. A
hypersurface on which `g = c` and along which `g` has no critical points then consists of
critical points of `φ ∘ g`, and it is a nondegenerate (Morse–Bott) critical submanifold of
`φ ∘ g` (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_scalar_comp`).

The reason is the second-order chain rule: since `φ'(g x) = 0`, the critical Hessian of `φ ∘ g`
at a point `x` of the hypersurface is `φ''(c) dg ⊗ dg`
(`TauCeti.criticalHessian_scalar_comp_apply_of_deriv_eq_zero`). Its kernel is the kernel of the
nonzero covector `dg_x` (`TauCeti.ker_criticalHessian_scalar_comp_of_deriv_eq_zero`), which is
the tangent space of the hypersurface, a regular piece of a level of `g` of the right dimension
(`TauCeti.SmoothEmbedding.tangentRange_eq_ker_mfderiv`). The normal
space is a line on which the Hessian has the sign of `φ''(c)`, so the Morse index along the
hypersurface is `0` when `φ''(c) > 0`
(`TauCeti.manifoldMorseIndex_scalar_comp_eq_zero_of_iteratedDeriv_two_nonneg`) and `1` when
`φ''(c) < 0` (`TauCeti.manifoldMorseIndex_scalar_comp_eq_one_of_iteratedDeriv_two_neg`); both
hold pointwise.

This produces Morse–Bott functions with critical submanifolds of positive dimension from Morse
functions: for the height `h` on a round sphere, the critical latitudes of `φ ∘ h` are of this
kind (`TauCeti.Geometry.Manifold.Morse.Sphere.Bott`).

## Main results

* `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_scalar_comp`: a regular hypersurface
  in a level `g = c` is a Morse–Bott critical submanifold of `φ ∘ g` when `φ'(c) = 0` and
  `φ''(c) ≠ 0`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Function Module
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} {g : M → ℝ} {φ : ℝ → ℝ} {c : ℝ}

variable (hn : n ≠ 0) (hg : ∀ s, ContMDiffAt I 𝓘(ℝ) 2 g (i s)) (hgi : ∀ s, g (i s) = c)
  (hreg : ∀ s, IsRegularPoint I 𝓘(ℝ) g (i s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
  (hφ : ContDiffAt ℝ 2 φ c) (hφ' : deriv φ c = 0)
include hn hg hgi hreg hdim hφ hφ'

/-- **A regular hypersurface in a level is a critical submanifold of a scalar reparametrization
which is critical at that level.** If `i` embeds a hypersurface on which `g = c` and along which
`g` has no critical points, and `φ'(c) = 0`, then the kernel of the critical Hessian of `φ ∘ g`
at each point of the hypersurface contains no vector outside its tangent space as soon as
`φ''(c) ≠ 0`. -/
theorem isNondegenerateCriticalSubmanifold_scalar_comp (hφ'' : iteratedDeriv 2 φ c ≠ 0) :
    i.IsNondegenerateCriticalSubmanifold (φ ∘ g) := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  refine ⟨⟨fun s ↦ ?_, fun s ↦ ?_⟩, fun s v hv ↦ ?_⟩
  · rw [← hgi s] at hφ
    exact hφ.contMDiffAt.comp (i s) (hg s)
  · refine (mem_criticalPoints_scalar_comp_iff_or ((hg s).mdifferentiableAt two_ne_zero)
      ((hgi s ▸ hφ).differentiableAt two_ne_zero)).2 (.inl ?_)
    rwa [hgi s]
  · -- The kernel of the critical Hessian is `ker dg`, the tangent space of the hypersurface.
    rw [ker_criticalHessian_scalar_comp_of_deriv_eq_zero (hg s) (hreg s) (hgi s ▸ hφ)
      (by rwa [hgi s]) (by rwa [hgi s])] at hv
    rw [← i.tangentRange_eq_ker_mfderiv s hn (.of_forall hgi) (hreg s)
      (by rwa [finrank_self])] at hv
    exact hv

end TauCeti.SmoothEmbedding
