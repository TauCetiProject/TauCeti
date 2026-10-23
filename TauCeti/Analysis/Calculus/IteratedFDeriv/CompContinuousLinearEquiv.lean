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
derivative of `f` at `e y` precomposed with `e` in every slot. Hence the norm of the `i`-th
derivative of `f ∘ e` at `y` is at most `‖e‖ ^ i` times that of `f` at `e y`, and the norm of the
`i`-th derivative of `f` at `e y` is at most `‖e⁻¹‖ ^ i` times that of `f ∘ e` at `y`. A Hölder
bound for the `i`-th derivative of `f ∘ e` transfers to one for the `i`-th derivative of `f`, at
the cost of the factor `‖e⁻¹‖ ^ (i + r)`. No differentiability
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

/-- Under a linear change of variables `e`, the `i`-th derivative of `f ∘ e` at `y` is bounded by
`‖e‖ ^ i` times the `i`-th derivative of `f` at `e y`. -/
theorem norm_iteratedFDeriv_comp_right_le (e : G ≃L[𝕜] E) (f : E → F) (y : G) (i : ℕ) :
    ‖iteratedFDeriv 𝕜 i (f ∘ e) y‖ ≤ ‖(e : G →L[𝕜] E)‖ ^ i * ‖iteratedFDeriv 𝕜 i f (e y)‖ := by
  rw [e.iteratedFDeriv_comp_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- Under a linear change of variables `e`, the `i`-th derivative of `f` at `e y` is bounded by
`‖e⁻¹‖ ^ i` times the `i`-th derivative of `f ∘ e` at `y`. -/
theorem norm_iteratedFDeriv_le_pow_mul_norm_iteratedFDeriv_comp_right (e : G ≃L[𝕜] E)
    (f : E → F) (y : G) (i : ℕ) :
    ‖iteratedFDeriv 𝕜 i f (e y)‖ ≤
      ‖(e.symm : E →L[𝕜] G)‖ ^ i * ‖iteratedFDeriv 𝕜 i (f ∘ e) y‖ := by
  have hf : (f ∘ e) ∘ e.symm = f := by
    funext z
    simp
  simpa only [hf, symm_apply_apply] using e.symm.norm_iteratedFDeriv_comp_right_le (f ∘ e) (e y) i

open scoped NNReal in
/-- **Hölder continuity of iterated derivatives under a linear change of variables.** If the
`i`-th derivative of `f ∘ e` is `r`-Hölder with constant `C` on `e ⁻¹' s`, then the `i`-th
derivative of `f` is `r`-Hölder on `s` with constant `C ‖e⁻¹‖ ^ i ‖e⁻¹‖ ^ r`. -/
theorem holderOnWith_iteratedFDeriv_of_comp_right (e : G ≃L[𝕜] E) {f : E → F} {s : Set E}
    {C r : ℝ≥0} {i : ℕ} (h : HolderOnWith C r (iteratedFDeriv 𝕜 i (f ∘ e)) (e ⁻¹' s)) :
    HolderOnWith (C * ‖(e.symm : E →L[𝕜] G)‖₊ ^ i * ‖(e.symm : E →L[𝕜] G)‖₊ ^ (r : ℝ)) r
      (iteratedFDeriv 𝕜 i f) s := by
  -- `Dⁱf = L ∘ Dⁱ(f ∘ e) ∘ e⁻¹`, where `L` precomposes with `e⁻¹` in every slot.
  set L := ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    fun _ : Fin i => (e.symm : E →L[𝕜] G)
  have hf : iteratedFDeriv 𝕜 i f = L ∘ iteratedFDeriv 𝕜 i (f ∘ e) ∘ (e.symm : E →L[𝕜] G) := by
    funext x
    have hfe : (f ∘ e) ∘ e.symm = f := by
      funext z
      simp
    simpa [L, hfe] using e.symm.iteratedFDeriv_comp_right (f ∘ e) x i
  have hL : ‖L‖₊ ≤ ‖(e.symm : E →L[𝕜] G)‖₊ ^ i := by
    rw [← NNReal.coe_le_coe]
    push_cast
    simpa using ContinuousMultilinearMap.norm_compContinuousLinearMapL_le F
      fun _ : Fin i => (e.symm : E →L[𝕜] G)
  have hmaps : Set.MapsTo (e.symm : E →L[𝕜] G) s (e ⁻¹' s) := fun x hx => by simpa using hx
  have hcomp := L.lipschitzWith.holderWith.comp_holderOnWith
    (h.comp ((e.symm : E →L[𝕜] G).lipschitzWith.holderWith.holderOnWith s) hmaps)
  rw [mul_one, one_mul, NNReal.coe_one, NNReal.rpow_one] at hcomp
  rw [hf]
  refine hcomp.mono_const ?_
  calc ‖L‖₊ * (C * ‖(e.symm : E →L[𝕜] G)‖₊ ^ (r : ℝ))
      ≤ ‖(e.symm : E →L[𝕜] G)‖₊ ^ i * (C * ‖(e.symm : E →L[𝕜] G)‖₊ ^ (r : ℝ)) := by gcongr
    _ = _ := by ring

end ContinuousLinearEquiv
