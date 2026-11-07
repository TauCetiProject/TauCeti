/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Iterated derivatives under a linear change of variables

For a continuous linear equivalence `e`, the iterated derivative of `f ∘ e` at `y` is the iterated
derivative of `f` at `e y` precomposed with `e` in every slot. Hence the norm of the `i`-th
derivative of `f ∘ e` at `y` is at most `‖e‖ ^ i` times that of `f` at `e y`, and the norm of the
`i`-th derivative of `f` at `e y` is at most `‖e⁻¹‖ ^ i` times that of `f ∘ e` at `y`. A Hölder
bound for the `i`-th derivative of `f ∘ e` transfers to one for the `i`-th derivative of `f`, at
the cost of the factor `‖e⁻¹‖ ^ (i + r)`. When `e` takes values in the scalar field, the second
derivative of `f ∘ e` applied to `v` and `w` is `e v * e w` times the second derivative of `f`.
No differentiability of `f` is needed.
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

/-- **Second derivatives along a one-dimensional linear change of variables.** For a continuous
linear equivalence `e` onto the scalar field and a function `f` of one variable, the second
derivative of `f ∘ e` at `z`, applied to `v` and `w`, is `e v * e w` times the second derivative
of `f` at `e z`. For instance, `e` may be the coordinate `PiLp.equivOfUnique p 𝕜 fun _ : ι ↦ 𝕜` of
a one-dimensional `L^p` space such as `EuclideanSpace ℝ (Fin 1)`. No differentiability of `f` is
needed. -/
theorem fderiv_fderiv_comp_right_apply (e : G ≃L[𝕜] 𝕜) (f : 𝕜 → F) (z v w : G) :
    fderiv 𝕜 (fderiv 𝕜 (f ∘ e)) z v w = (e v * e w) • deriv (deriv f) (e z) := by
  have h := iteratedFDeriv_two_apply (𝕜 := 𝕜) (f ∘ e) z ![v, w]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h, e.iteratedFDeriv_comp_right]
  simp [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_succ, Fin.prod_univ_two]

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

namespace LinearIsometryEquiv

/-- Linear isometries on either side preserve differences of iterated derivative fields,
without any differentiability assumption on the function. -/
theorem norm_iteratedFDeriv_sub_comp
    {𝕜 E E' F F' : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (e : E' ≃ₗᵢ[𝕜] E) (t : F ≃ₗᵢ[𝕜] F') (f : E → F) (j : ℕ) (x y : E') :
    ‖iteratedFDeriv 𝕜 j (t ∘ f ∘ e) x - iteratedFDeriv 𝕜 j (t ∘ f ∘ e) y‖ =
      ‖iteratedFDeriv 𝕜 j f (e x) - iteratedFDeriv 𝕜 j f (e y)‖ := by
  have hr (z : E') : iteratedFDeriv 𝕜 j (f ∘ e) z =
      (iteratedFDeriv 𝕜 j f (e z)).compContinuousLinearMap fun _ => (e : E' →L[𝕜] E) := by
    simpa only [← iteratedFDerivWithin_univ, Set.preimage_univ, LinearIsometryEquiv.coe_coe] using
      e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
        (Set.mem_univ z) j
  have htjet (z : E') : iteratedFDeriv 𝕜 j (t ∘ f ∘ e) z =
      (t : F →L[𝕜] F').compContinuousMultilinearMap (iteratedFDeriv 𝕜 j (f ∘ e) z) := by
    simpa only [LinearIsometryEquiv.coe_coe, Function.comp_assoc] using
      t.toContinuousLinearEquiv.iteratedFDeriv_comp_left (f := f ∘ e) (x := z) (i := j)
  rw [htjet, htjet]
  have ht : (t : F →L[𝕜] F').compContinuousMultilinearMap
      (iteratedFDeriv 𝕜 j (f ∘ e) x) -
      (t : F →L[𝕜] F').compContinuousMultilinearMap (iteratedFDeriv 𝕜 j (f ∘ e) y) =
      (t : F →L[𝕜] F').compContinuousMultilinearMap
        (iteratedFDeriv 𝕜 j (f ∘ e) x - iteratedFDeriv 𝕜 j (f ∘ e) y) := by ext; simp
  rw [ht, ← t.toContinuousLinearMap_toLinearIsometry,
    t.toLinearIsometry.norm_compContinuousMultilinearMap, hr, hr]
  have he : (iteratedFDeriv 𝕜 j f (e x)).compContinuousLinearMap (fun _ => (e : E' →L[𝕜] E)) -
      (iteratedFDeriv 𝕜 j f (e y)).compContinuousLinearMap (fun _ => (e : E' →L[𝕜] E)) =
      (iteratedFDeriv 𝕜 j f (e x) - iteratedFDeriv 𝕜 j f (e y)).compContinuousLinearMap
        (fun _ => (e : E' →L[𝕜] E)) := by ext; simp
  rw [he, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]


open scoped NNReal in
/-- Composing with linear isometries preserves a local Hölder bound on an actual derivative
field, including at points where the function need not be differentiable. -/
theorem holderOnWith_iteratedFDeriv_comp {E E' T Tu : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup Tu] [NormedSpace ℝ Tu]
    (e : E' ≃ₗᵢ[ℝ] E) (t : T ≃ₗᵢ[ℝ] Tu) (v : E → T)
    {C α : ℝ≥0} (j : ℕ) {S : Set E} (hv : HolderOnWith C α (iteratedFDeriv ℝ j v) S) :
    HolderOnWith C α (iteratedFDeriv ℝ j (t ∘ v ∘ e)) (e ⁻¹' S) := by
  rw [holderOnWith_iff_dist_le] at hv ⊢
  intro x hx y hy
  rw [dist_eq_norm, LinearIsometryEquiv.norm_iteratedFDeriv_sub_comp]
  have hxy := hv (e x) hx (e y) hy
  rw [e.dist_map] at hxy
  simpa only [dist_eq_norm] using hxy

end LinearIsometryEquiv
