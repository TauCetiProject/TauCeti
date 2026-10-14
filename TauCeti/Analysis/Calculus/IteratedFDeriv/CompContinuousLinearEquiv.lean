/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Iterated derivatives under a linear change of variables

For a continuous linear equivalence `e`, the iterated derivative of `f ∘ e` at `y` is the iterated
derivative of `f` at `e y` precomposed with `e` in every slot. Hence the norm of the iterated
derivative of `f` at `e y` is at most `‖e⁻¹‖ ^ i` times the norm of the `i`-th derivative of
`f ∘ e` at `y`, and a Hölder bound for the `i`-th derivative of `f ∘ e` transfers to one for
the `i`-th derivative of `f`, at the cost of the factor `‖e⁻¹‖ ^ (i + r)`. No differentiability
of `f` is needed.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Iterated derivatives under a linear change of variables.** For a continuous linear
equivalence `e`, the `i`-th derivative of `f ∘ e` at `x` is the `i`-th derivative of `f` at `e x`
precomposed with `e` in every slot. Unlike `ContinuousLinearMap.iteratedFDeriv_comp_right`, no
differentiability of `f` is needed. -/
theorem iteratedFDeriv_comp_right (e : G ≃L[𝕜] E) (f : E → F) (x : G) (i : ℕ) :
    iteratedFDeriv 𝕜 i (f ∘ e) x =
      (iteratedFDeriv 𝕜 i f (e x)).compContinuousLinearMap fun _ => (e : G →L[𝕜] E) := by
  simpa only [← iteratedFDerivWithin_univ, Set.preimage_univ] using
    e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ _) i

/-- Under a linear change of variables `e`, the `i`-th derivative of `f` at `e y` is bounded by
`‖e⁻¹‖ ^ i` times the `i`-th derivative of `f ∘ e` at `y`. -/
theorem norm_iteratedFDeriv_le_pow_mul_norm_iteratedFDeriv_comp_right (e : G ≃L[𝕜] E)
    (f : E → F) (y : G) (i : ℕ) :
    ‖iteratedFDeriv 𝕜 i f (e y)‖ ≤
      ‖(e.symm : E →L[𝕜] G)‖ ^ i * ‖iteratedFDeriv 𝕜 i (f ∘ e) y‖ := by
  have hf : (f ∘ e) ∘ e.symm = f := by
    funext z
    simp
  have h : iteratedFDeriv 𝕜 i f (e y) =
      (iteratedFDeriv 𝕜 i (f ∘ e) y).compContinuousLinearMap fun _ => (e.symm : E →L[𝕜] G) := by
    simpa only [hf, symm_apply_apply] using e.symm.iteratedFDeriv_comp_right (f ∘ e) (e y) i
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

open scoped NNReal in
/-- **Hölder continuity of iterated derivatives under a linear change of variables.** If the
`i`-th derivative of `f ∘ e` is `r`-Hölder with constant `C` on `e ⁻¹' s`, then the `i`-th
derivative of `f` is `r`-Hölder on `s` with constant `C ‖e⁻¹‖ ^ i ‖e⁻¹‖ ^ r`. -/
theorem holderOnWith_iteratedFDeriv_of_comp_right (e : G ≃L[𝕜] E) {f : E → F} {s : Set E}
    {C r : ℝ≥0} {i : ℕ} (h : HolderOnWith C r (iteratedFDeriv 𝕜 i (f ∘ e)) (e ⁻¹' s)) :
    HolderOnWith (C * ‖(e.symm : E →L[𝕜] G)‖₊ ^ i * ‖(e.symm : E →L[𝕜] G)‖₊ ^ (r : ℝ)) r
      (iteratedFDeriv 𝕜 i f) s := by
  have hf : (f ∘ e) ∘ e.symm = f := by
    funext z
    simp
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hx' : e.symm x ∈ e ⁻¹' s := by simpa using hx
  have hy' : e.symm y ∈ e ⁻¹' s := by simpa using hy
  have hsub : ∀ A B : ContinuousMultilinearMap 𝕜 (fun _ : Fin i => G) F,
      A.compContinuousLinearMap (fun _ => (e.symm : E →L[𝕜] G)) -
        B.compContinuousLinearMap (fun _ => (e.symm : E →L[𝕜] G)) =
      (A - B).compContinuousLinearMap fun _ => (e.symm : E →L[𝕜] G) := fun A B => by
    ext
    simp
  rw [← hf, e.symm.iteratedFDeriv_comp_right, e.symm.iteratedFDeriv_comp_right, dist_eq_norm,
    hsub]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← dist_eq_norm]
  calc dist (iteratedFDeriv 𝕜 i (f ∘ e) (e.symm x)) (iteratedFDeriv 𝕜 i (f ∘ e) (e.symm y)) *
        ‖(e.symm : E →L[𝕜] G)‖ ^ i
      ≤ C * (‖(e.symm : E →L[𝕜] G)‖ * dist x y) ^ (r : ℝ) * ‖(e.symm : E →L[𝕜] G)‖ ^ i := by
        gcongr
        refine (h.dist_le hx' hy').trans ?_
        gcongr
        exact (e.symm : E →L[𝕜] G).lipschitzWith.dist_le_mul x y
    _ = _ := by
        rw [Real.mul_rpow (norm_nonneg _) dist_nonneg]
        push_cast
        ring

end ContinuousLinearEquiv
