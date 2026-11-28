/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Winding
public import TauCeti.Analysis.Green.WindingWeight.FiniteSum
import TauCeti.Analysis.Contour.Cycle.Trace
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Reparam
import TauCeti.Analysis.Convex.Segment

/-!
# Integrability of contour-cycle winding weights

The trace-zero winding weight `C.windingWeight` of any contour cycle agrees almost everywhere with
the coefficient-weighted sum of the winding weights of its affine-normalized generators
(`TauCeti.Green.sum_windingWeight_comp_lineMap_ae`). Consequently `C.windingWeight` is globally
integrable on `ℂ` (`TauCeti.Contour.Cycle.integrable_windingWeight`), and its product with any map
continuous on `tsupport C.windingWeight` is globally integrable on `ℂ`
(`TauCeti.Contour.Cycle.integrable_windingWeight_smul`). When `C` lies in `U` (`C.IsIn U`) and is
null-homologous in `U` (`C.IsNullHomologous U`), `tsupport C.windingWeight ⊆ U`, so the product
with any map continuous on `U` is integrable on `U`
(`TauCeti.Contour.Cycle.integrableOn_windingWeight_smul`).
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The winding weights of the affine normalizations of the generators of a cycle add up, almost
everywhere, to the winding weight of the cycle. -/
theorem sum_windingWeight_comp_lineMap_ae (C : Contour.Cycle) :
    (fun z ↦ ∑ γ ∈ FreeAddCommGroup.support C, (FreeAddCommGroup.coeff γ C : ℝ) *
      windingWeight (γ ∘ AffineMap.lineMap γ.a γ.b) 0 1 z) =ᵐ[volume] C.windingWeight := by
  have hnot : ∀ᵐ z ∂volume, z ∉ Contour.Cycle.trace C :=
    compl_mem_ae_iff.mpr (Contour.Cycle.addHaar_trace_eq_zero C volume)
  filter_upwards [hnot] with z hz
  rw [Contour.Cycle.windingWeight_eq_of_notMem C hz,
    Contour.Cycle.windingNumber_eq_sum_support, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  have hzγ : z ∉ γ '' uIcc γ.a γ.b :=
    fun hm ↦ hz (Contour.Cycle.mem_trace_iff.mpr ⟨γ, hγ, hm⟩)
  rw [windingWeight_eq_of_notMem (by rwa [Set.image_comp_lineMap_uIcc_zero_one]),
    γ.absolutelyContinuousOnInterval.windingNumber_comp_lineMap hzγ]
  simp

/-- The trace-zero real winding weight of any contour cycle is integrable on `ℂ`. -/
theorem _root_.TauCeti.Contour.Cycle.integrable_windingWeight (C : Contour.Cycle) :
    Integrable C.windingWeight := by
  classical
  refine (integrable_sum_windingWeight (s := FreeAddCommGroup.support C)
    (γ := fun γ ↦ γ ∘ AffineMap.lineMap γ.a γ.b) (a := fun _ ↦ 0) (b := fun _ ↦ 1)
    (w := fun γ ↦ FreeAddCommGroup.coeff γ C)
    (fun γ _ ↦ absolutelyContinuousOnInterval_comp_lineMap_iff.2
      γ.absolutelyContinuousOnInterval)
    (fun γ _ ↦ by simp [γ.source_eq_target])).congr (sum_windingWeight_comp_lineMap_ae C)

/-- For any contour cycle `C` and any map `g : ℂ → E` continuous on `tsupport C.windingWeight`,
`z ↦ C.windingWeight z • g z` is integrable on `ℂ`. -/
theorem _root_.TauCeti.Contour.Cycle.integrable_windingWeight_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Contour.Cycle) {g : ℂ → E}
    (hg : ContinuousOn g (tsupport C.windingWeight)) :
    Integrable (fun z ↦ C.windingWeight z • g z) :=
  (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left _ _).trans (subset_tsupport _))).mp
    (C.integrable_windingWeight.integrableOn.smul_continuousOn hg C.hasCompactSupport_windingWeight)

/-- If `C` lies in `U` and is null-homologous in `U`, then `C.windingWeight • g` is integrable on
`U` for every map `g : ℂ → E` continuous on `U`. -/
theorem _root_.TauCeti.Contour.Cycle.integrableOn_windingWeight_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Contour.Cycle) {U : Set ℂ} {g : ℂ → E}
    (htrace : C.IsIn U) (hnull : C.IsNullHomologous U) (hg : ContinuousOn g U) :
    IntegrableOn (fun z ↦ C.windingWeight z • g z) U :=
  (C.integrable_windingWeight_smul
    (hg.mono (C.tsupport_windingWeight_subset htrace hnull))).integrableOn

end TauCeti.Green

end
