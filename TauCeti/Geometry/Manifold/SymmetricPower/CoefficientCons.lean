/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Analysis.Polynomial.SymmetricPower.Cons
import Mathlib.Analysis.Calculus.ContDiff.Defs
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Topology.Sym.Cons

/-!
# Fixed-root insertion is an analytic embedding in coefficient coordinates

Adjoining a fixed root `a` embeds complex coefficient `n`-space into coefficient `(n + 1)`-space.
The image consists of the monic polynomials vanishing at `a`, an affine hyperplane by
`TauCeti.Sym.mem_iff_pow_add_sum_coeffEquiv_mul_pow_eq_zero`. The map is a closed topological
embedding by `TauCeti.Sym.isClosedEmbedding_cons` and an analytic immersion by the coefficient
calculation in `TauCeti/Analysis/Polynomial/SymmetricPower/Cons.lean`. In particular, the
immersion does not fail when the tuple already contains `a`.

These coefficient embeddings are the local models for adjoining a basepoint to an unordered
tuple on a complex curve.
-/

public section

open Topology Manifold
open scoped ContDiff Manifold

namespace TauCeti.Sym

variable {n : ℕ}

/-- Adjoining a fixed point is a complex analytic smooth embedding in elementary-symmetric
coefficient coordinates, including along the repeated-root locus. -/
theorem isSmoothEmbedding_coeffEquiv_cons_coeffEquiv_symm (a : ℂ) :
    IsSmoothEmbedding 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (fun c => coeffEquiv ℂ (n + 1) (Sym.cons a ((coeffEquiv ℂ n).symm c))) := by
  have hf : ContDiff ℂ ω
      (fun c => coeffEquiv ℂ (n + 1) (Sym.cons a ((coeffEquiv ℂ n).symm c))) :=
    AnalyticOnNhd.contDiff (fun c _ => analyticAt_coeffEquiv_cons_coeffEquiv_symm a c)
  refine ⟨TauCeti.isImmersion_iff_forall_isImmersionAt.mpr (fun c => ?_), ?_⟩
  · exact (hf.contDiffOn.isImmersionAt_iff_injective_fderiv isOpen_univ (Set.mem_univ c)
      (by simp)).mpr (fderiv_coeffEquiv_cons_coeffEquiv_symm_injective a c)
  · have h := (coeffHomeomorph ℂ (n + 1)).isClosedEmbedding.comp
      ((isClosedEmbedding_cons (n := n) a).comp (coeffHomeomorph ℂ n).symm.isClosedEmbedding)
    simpa only [Function.comp_def, coeffHomeomorph_apply, coeffHomeomorph_symm_apply] using
      h.isEmbedding

end TauCeti.Sym
