/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic

/-!
# Symmetry of complex interpolation

Reversing the endpoints of a compatible couple and replacing `θ` by `1 - θ` gives the
same complex interpolation space, with equal norms. The isometry
`CompatibleCouple.ComplexMethodSpace.swap` lies over the canonical identification of
the sum spaces, so it preserves the element in the common ambient space.

Reflection of an admissible function is `z ↦ F (1 - z)`. Its boundary traces are the original
traces exchanged and precomposed with negation. This preserves their maximum norm and
therefore the quotient norm, without completeness or regularity assumptions.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976,
  §4.2 (symmetry of the complex method).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines TauCeti.Complex.HadamardThreeLines Set
open scoped ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : TauCeti.CompatibleCouple ℂ X₀ X₁ V}

/-- Reflection in the middle of the strip exchanges the boundary traces of an admissible
function and reverses their real parameters. -/
theorem IsStripFunction.reflect {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) :
    C.swap.IsStripFunction (fun z => C.sumSwap (F (1 - z)))
      (g.2.comp (Homeomorph.neg ℝ).toCocompactMap,
        g.1.comp (Homeomorph.neg ℝ).toCocompactMap) where
  diffContOnCl := by
    have hsub : Differentiable ℂ (fun z : ℂ => 1 - z) := by fun_prop
    exact C.sumSwap.toContinuousLinearEquiv.toContinuousLinearMap.differentiable.comp_diffContOnCl
      (hF.diffContOnCl.comp hsub.diffContOnCl fun _ hz =>
        one_sub_mem_verticalStrip_iff.2 hz)
  isBounded := by
    refine isBounded_iff_forall_norm_le.2 ⟨‖g‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [C.sumSwap.norm_map]
    apply hF.norm_le
    exact one_sub_mem_verticalClosedStrip_iff.2 hz
  apply_mul_I t := by
    have heq : (1 : ℂ) - t * I = 1 + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    rw [heq, hF.apply_one_add_mul_I, sumSwap_sndToSum]
    simp
  apply_one_add_mul_I t := by
    have heq : (1 : ℂ) - (1 + t * I) = ((-t : ℝ) : ℂ) * I := by push_cast; ring
    rw [heq, hF.apply_mul_I, sumSwap_fstToSum]
    simp

variable (C)

/-- The isometric reversal of admissible boundary traces: exchange the two traces and
precompose each with negation on `ℝ`. -/
def stripTracesSwap : C.stripTraces ≃ₗᵢ[ℂ] C.swap.stripTraces where
  toFun g := ⟨((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2.comp (Homeomorph.neg ℝ).toCocompactMap,
    (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1.comp (Homeomorph.neg ℝ).toCocompactMap),
      mem_stripTraces_iff.2 ⟨_, (C.isStripFunction_stripFunction g).reflect⟩⟩
  invFun g := ⟨((g : C₀(ℝ, X₁) × C₀(ℝ, X₀)).2.comp (Homeomorph.neg ℝ).toCocompactMap,
    (g : C₀(ℝ, X₁) × C₀(ℝ, X₀)).1.comp (Homeomorph.neg ℝ).toCocompactMap),
      mem_stripTraces_iff.2 ⟨_, (C.swap.isStripFunction_stripFunction g).reflect⟩⟩
  left_inv g := by apply Subtype.ext; ext t <;> simp
  right_inv g := by apply Subtype.ext; ext t <;> simp
  map_add' g h := by apply Subtype.ext; ext t <;> simp
  map_smul' c g := by apply Subtype.ext; ext t <;> simp
  norm_map' g := by
    dsimp
    simp only [Prod.norm_def, ZeroAtInftyContinuousMap.norm_comp_toCocompactMap]
    exact max_comm _ _

@[simp]
theorem stripTracesSwap_apply_fst (g : C.stripTraces) (t : ℝ) :
    (C.stripTracesSwap g : C₀(ℝ, X₁) × C₀(ℝ, X₀)).1 t =
      (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 (-t) := (rfl)

@[simp]
theorem stripTracesSwap_apply_snd (g : C.stripTraces) (t : ℝ) :
    (C.stripTracesSwap g : C₀(ℝ, X₁) × C₀(ℝ, X₀)).2 t =
      (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 (-t) := (rfl)

@[simp]
theorem stripTracesSwap_symm : C.stripTracesSwap.symm = C.swap.stripTracesSwap := (rfl)

/-- Evaluation of reversed traces at `z` is evaluation of the original function at `1 - z`,
under the canonical identification of sum spaces. -/
theorem stripEval_stripTracesSwap (z : ℂ) (g : C.stripTraces) :
    C.swap.stripEval z (C.stripTracesSwap g) = C.sumSwap (C.stripEval (1 - z) g) := by
  by_cases hz : z ∈ verticalClosedStrip 0 1
  · rw [stripEval_apply,
      stripFunction_eq (C.isStripFunction_stripFunction g).reflect hz, stripEval_apply]
  · have hz' : 1 - z ∉ verticalClosedStrip 0 1 :=
      mt one_sub_mem_verticalClosedStrip_iff.1 hz
    simp [C.swap.stripEval_eq_zero hz, C.stripEval_eq_zero hz']

/-- Evaluation of reversed traces at the complementary real parameter agrees with evaluation
of the original traces, under the canonical identification of sum spaces. -/
theorem stripEval_stripTracesSwap_of_add_eq_one {θ η : ℝ} (h : θ + η = 1)
    (g : C.stripTraces) :
    C.swap.stripEval η (C.stripTracesSwap g) = C.sumSwap (C.stripEval θ g) := by
  have hsub : (1 : ℂ) - η = θ := by
    exact_mod_cast sub_eq_of_eq_add h.symm
  rw [stripEval_stripTracesSwap, hsub]

namespace ComplexMethodSpace

variable {C} {θ η : ℝ}

/-- The quotient map induced by reflection, with two complementary real parameters. -/
private def reflectionMap (h : θ + η = 1) :
    C.ComplexMethodSpace θ →L[ℂ] C.swap.ComplexMethodSpace η :=
  lift ((mk η).comp C.stripTracesSwap.toContinuousLinearEquiv.toContinuousLinearMap)
    fun g hg => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      rw [← map_zero (mk (C := C.swap) η), mk_eq_mk_iff]
      rw [stripEval_stripTracesSwap_of_add_eq_one C h, hg]
      simp only [map_zero]

private theorem reflectionMap_mk (h : θ + η = 1) (g : C.stripTraces) :
    reflectionMap h (mk θ g) = mk η (C.stripTracesSwap g) := by
  rw [reflectionMap, lift_mk, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

private theorem toSum_reflectionMap (h : θ + η = 1) (u : C.ComplexMethodSpace θ) :
    toSum (reflectionMap h u) = C.sumSwap (toSum u) := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [reflectionMap_mk, toSum_mk, stripEval_stripTracesSwap_of_add_eq_one C h, toSum_mk]

private theorem reflectionMap_norm_le (h : θ + η = 1) (u : C.ComplexMethodSpace θ) :
    ‖reflectionMap h u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr
  rw [reflectionMap_mk]
  exact (norm_mk_le _).trans_lt ((C.stripTracesSwap.norm_map g).trans_lt hg)

private theorem reflectionMap_reflectionMap (h : θ + η = 1)
    (u : C.ComplexMethodSpace θ) :
    reflectionMap (by linarith : η + θ = 1) (reflectionMap h u) = u := by
  apply toSum_injective
  simp [toSum_reflectionMap, ← sumSwap_symm]

/-- **Symmetry of complex interpolation:** exchanging the endpoints and replacing `θ` by
`1 - θ` preserves the interpolation norm. The isometry identifies the same element of the
ambient space; no regularity or completeness hypothesis on the endpoints is needed. -/
def swap (C : TauCeti.CompatibleCouple ℂ X₀ X₁ V) (θ : ℝ) :
    C.ComplexMethodSpace θ ≃ₗᵢ[ℂ] C.swap.ComplexMethodSpace (1 - θ) :=
  LinearIsometryEquiv.ofBounds
    { toFun := reflectionMap (by ring : θ + (1 - θ) = 1)
      invFun := reflectionMap (by ring : (1 - θ) + θ = 1)
      left_inv := reflectionMap_reflectionMap _
      right_inv := reflectionMap_reflectionMap _
      map_add' := map_add _
      map_smul' := map_smul _ }
    (reflectionMap_norm_le _) (reflectionMap_norm_le _)

/-- On representatives, symmetry reflects the admissible boundary traces. -/
@[simp]
theorem swap_mk (g : C.stripTraces) :
    swap C θ (mk θ g) = mk (1 - θ) (C.stripTracesSwap g) :=
  reflectionMap_mk (by ring) g

/-- Symmetry lies over the canonical identification of the sum spaces. -/
@[simp]
theorem toSum_swap (u : C.ComplexMethodSpace θ) :
    toSum (swap C θ u) = C.sumSwap (toSum u) :=
  toSum_reflectionMap (by ring) u

/-- The inverse symmetry also lies over the inverse identification of the sum spaces. -/
@[simp]
theorem toSum_swap_symm (u : C.swap.ComplexMethodSpace (1 - θ)) :
    toSum ((swap C θ).symm u) = C.sumSwap.symm (toSum u) := by
  apply C.sumSwap.injective
  rw [← toSum_swap]
  simp only [LinearIsometryEquiv.apply_symm_apply]

end ComplexMethodSpace

end TauCeti.CompatibleCouple
