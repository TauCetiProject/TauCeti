/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.RingTheory.Bialgebra.Convolution

/-!
# Analytic evaluation of convolution products

For families of algebra homomorphisms out of a bialgebra, analyticity of each coordinate
evaluation is preserved by pointwise convolution.
-/

public section

open Coalgebra WithConv

namespace TauCeti

/-- Convolution preserves analyticity of the coordinate evaluations of algebra homomorphisms. -/
theorem analyticAt_eval_convMul {K E A H : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E] [NormedCommRing A] [NormedAlgebra K A]
    [Semiring H] [Bialgebra K H] {x : E} {f g : E → WithConv (H →ₐ[K] A)}
    (hf : ∀ a : H, AnalyticAt K (fun z ↦ (f z).ofConv a) x)
    (hg : ∀ a : H, AnalyticAt K (fun z ↦ (g z).ofConv a) x) (a : H) :
    AnalyticAt K (fun z ↦ (f z * g z).ofConv a) x := by
  have heq (z : E) : (f z * g z).ofConv a =
      ∑ i ∈ (ℛ K a).index,
        (f z).ofConv ((ℛ K a).left i) * (g z).ofConv ((ℛ K a).right i) := by
    have h := (ℛ K a).convMul_apply
      (toConv (f z).ofConv.toLinearMap) (toConv (g z).ofConv.toLinearMap)
    rw [← AlgHom.toLinearMap_convMul] at h
    simpa only [ofConv_toConv, AlgHom.toLinearMap_apply] using h
  simp_rw [heq]
  exact Finset.analyticAt_fun_sum _ fun i _ ↦ (hf _).mul (hg _)

end TauCeti
