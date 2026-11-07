/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Distribution.Mass.Normal
public import TauCeti.Geometry.Convex.FullSimplex
import Mathlib.Analysis.Calculus.FDeriv.Affine
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Simplex

/-!
# The oriented current of the standard simplex

Let `Δᵖ = {x ∈ ℝᵖ | 0 ≤ xᵢ, ∑ xᵢ ≤ 1}` be the full-dimensional standard simplex
(`TauCeti.fullSimplex`), with the orientation of the standard basis `e₀, …, e_{p-1}` of
`ℝᵖ = EuclideanSpace ℝ (Fin p)`. Its *current* `[[Δᵖ]]` is the `p`-current

`[[Δᵖ]] ω = ∫_{Δᵖ} ω(x)(e₀, …, e_{p-1}) dx`

on test `p`-forms on any open set `Ω ⊆ ℝᵖ` (`TauCeti.simplexCurrent`). The simplex need not lie in
`Ω`: test forms on `Ω` vanish off `Ω`, and the support of `[[Δᵖ]]` lies in `Δᵖ`.

Let `Fᵢ = simplexMapAmbient i.succAbove : ℝᵖ → ℝᵖ⁺¹` be the affine face maps, sending the vertices
of `Δᵖ` to the vertices of `Δᵖ⁺¹` other than the `i`-th one. They are closed embeddings, so the
pushforward `(Fᵢ)_# [[Δᵖ]] = [[Δᵖ]] ∘ Fᵢ^*` along the pullback of test forms
`TestFunction.pullbackCLM` is defined. Stokes' theorem on the simplex
(`ContDiffOn.integral_extDerivWithin_fullSimplex`) is then the **boundary formula**

`∂ [[Δᵖ⁺¹]] = ∑ᵢ (-1)ⁱ (Fᵢ)_# [[Δᵖ]]`,

where `∂ T = T ∘ d`, with the face and sign conventions of the boundary of smooth singular chains.
In dimension zero `[[Δ⁰]]` is the Dirac current at the point, so that for instance
`∂ [[Δ¹]] = δ₁ - δ₀` on the line. The masses satisfy `M([[Δᵖ]]) ≤ vol(Δᵖ)`, so `[[Δᵖ]]` is a
normal current. The current of a smooth singular simplex `σ` is the pushforward of `[[Δᵖ]]` along
`σ`; this file treats the standard simplex itself.

## Main declarations

* `TauCeti.simplexCurrent p Ω`: the oriented current `[[Δᵖ]]` on test `p`-forms on `Ω`.
* `TauCeti.simplexCurrent_apply`: `[[Δᵖ]] ω = ∫_{Δᵖ} ω(x)(e₀, …, e_{p-1}) dx`.
* `TauCeti.simplexCurrent_zero_apply`: `[[Δ⁰]]` is the Dirac current at the point.
* `TauCeti.dsupport_simplexCurrent_subset`: the support of `[[Δᵖ]]` lies in `Δᵖ`.
* `TauCeti.simplexCurrent_extDerivCLM`, `TauCeti.simplexCurrent_comp_extDerivCLM`: the boundary
  formula `∂ [[Δᵖ⁺¹]] = ∑ᵢ (-1)ⁱ (Fᵢ)_# [[Δᵖ]]`.
* `TauCeti.simplexCurrent_one_extDerivCLM`: `∂ [[Δ¹]] = δ₁ - δ₀`.
* `TauCeti.mass_simplexCurrent_le`: `M([[Δᵖ]]) ≤ vol(Δᵖ)`.
* `TauCeti.isNormal_simplexCurrent`: `[[Δᵖ]]` is a normal current.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.8 (oriented simplexes as currents and their
  boundaries).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, with its conventions for the
  standard simplex, its faces and the signs of the boundary.
-/

public section

open MeasureTheory Set TopologicalSpace TestFunction Distribution
open scoped Distributions ENNReal

namespace TauCeti

variable {p : ℕ} {n : ℕ∞}

/-- The **oriented current of the standard simplex** `[[Δᵖ]]`: the continuous linear functional
`ω ↦ ∫_{Δᵖ} ω(x)(e₀, …, e_{p-1}) dx` on test `p`-forms on an open set `Ω ⊆ ℝᵖ`, where `eᵢ` is the
standard basis (`TauCeti.simplexCurrent_apply`). -/
noncomputable def simplexCurrent (p : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  integralAgainstBilinCLM
    (ContinuousLinearMap.mul ℝ ℝ ∘L
      ContinuousAlternatingMap.apply ℝ _ ℝ fun i ↦ EuclideanSpace.single i 1)
    (volume.restrict (fullSimplex p)) fun _ ↦ (1 : ℝ)

/-- The current `[[Δᵖ]]` integrates the coefficient of a test `p`-form on the standard basis over
the simplex. -/
theorem simplexCurrent_apply (Ω : Opens (EuclideanSpace ℝ (Fin p)))
    (ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ)) :
    simplexCurrent p Ω ω = ∫ x in fullSimplex p, ω x fun i ↦ EuclideanSpace.single i 1 := by
  have : IsFiniteMeasure (volume.restrict (fullSimplex p)) :=
    isFiniteMeasure_restrict.2 (isCompact_fullSimplex p).measure_ne_top
  rw [simplexCurrent,
    integralAgainstBilinCLM_eq_integral ((locallyIntegrable_const 1).locallyIntegrableOn _)]
  simp

/-- **Dimension zero**: `[[Δ⁰]]` is the Dirac current at the point of `ℝ⁰`. -/
theorem simplexCurrent_zero_apply (Ω : Opens (EuclideanSpace ℝ (Fin 0)))
    (ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin 0) [⋀^Fin 0]→L[ℝ] ℝ)) :
    simplexCurrent 0 Ω ω = ω 0 ![] := by
  have hs : fullSimplex 0 = univ := eq_univ_of_forall fun x ↦ by simp
  rw [simplexCurrent_apply, hs, Measure.restrict_univ, volume_euclideanSpace_eq_dirac,
    integral_dirac]
  exact congrArg (ω 0) (Subsingleton.elim _ _)

/-- The support of `[[Δᵖ]]` lies in the simplex `Δᵖ`. -/
theorem dsupport_simplexCurrent_subset (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    dsupport (simplexCurrent p Ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) → ℝ) ⊆
      fullSimplex p := by
  refine sInter_subset_of_mem ⟨fun ω hω ↦ ?_, isClosed_fullSimplex p⟩
  rw [simplexCurrent_apply]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
  simp [image_eq_zero_of_notMem_tsupport fun h ↦ hω h hx]

/-- **The boundary of the simplex on a test form**: `[[Δᵖ⁺¹]] (d ω)` is the alternating sum over
`i` of `[[Δᵖ]] (Fᵢ^* ω)`, where `Fᵢ = simplexMapAmbient i.succAbove` are the face maps. This is
Stokes' theorem on the simplex for test forms. -/
theorem simplexCurrent_extDerivCLM (Ω : Opens (EuclideanSpace ℝ (Fin (p + 1))))
    (ω : 𝓓(Ω, EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] ℝ)) :
    simplexCurrent (p + 1) Ω (extDerivCLM ω) =
      ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        simplexCurrent p ⊤ (pullbackCLM (simplexMapAmbient i.succAbove)
          (simplexMapAmbient _).contDiff.contDiffOn
          (fun _ hK _ ↦ isCompact_inter_preimage_simplexMapAmbient_succAbove i hK) ω) := by
  have hω : ContDiff ℝ 1 (ω : EuclideanSpace ℝ (Fin (p + 1)) → _) := ω.contDiff.of_le (by simp)
  -- On the simplex the exterior derivative of `ω` is its exterior derivative within the simplex,
  -- which is the one in Stokes' theorem.
  rw [simplexCurrent_apply, setIntegral_congr_fun (isClosed_fullSimplex _).measurableSet
    (g := fun x ↦ extDerivWithin ω (fullSimplex (p + 1)) x fun i ↦ EuclideanSpace.single i 1)
    fun x hx ↦ by simp only [extDerivCLM_apply, ((hω.differentiable one_ne_zero) x).extDerivWithin
      (uniqueDiffOn_fullSimplex _ x hx)],
    hω.contDiffOn.integral_extDerivWithin_fullSimplex]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [simplexCurrent_apply, ContinuousAffineMap.fderiv, Function.comp_def]

/-- **The boundary of the simplex**: `∂ [[Δᵖ⁺¹]] = ∑ᵢ (-1)ⁱ (Fᵢ)_# [[Δᵖ]]`, where `∂ T = T ∘ d` and
`(Fᵢ)_# T = T ∘ Fᵢ^*` is the pushforward along the face map `Fᵢ = simplexMapAmbient i.succAbove`.
-/
theorem simplexCurrent_comp_extDerivCLM (Ω : Opens (EuclideanSpace ℝ (Fin (p + 1)))) :
    simplexCurrent (p + 1) Ω ∘L extDerivCLM =
      ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        simplexCurrent p ⊤ ∘L pullbackCLM (simplexMapAmbient i.succAbove)
          (simplexMapAmbient _).contDiff.contDiffOn
          (fun _ hK _ ↦ isCompact_inter_preimage_simplexMapAmbient_succAbove i hK) := by
  ext ω
  simp [simplexCurrent_extDerivCLM]

/-- **The boundary of the unit interval**: `∂ [[Δ¹]] = δ₁ - δ₀` on the line `ℝ¹`, that is,
`[[Δ¹]] (d η) = η(1) - η(0)` for every test function `η`, read as a `0`-form. -/
theorem simplexCurrent_one_extDerivCLM (Ω : Opens (EuclideanSpace ℝ (Fin 1)))
    (η : 𝓓(Ω, EuclideanSpace ℝ (Fin 1) [⋀^Fin 0]→L[ℝ] ℝ)) :
    simplexCurrent 1 Ω (extDerivCLM η) = η (EuclideanSpace.single 0 1) ![] - η 0 ![] := by
  have h₀ : simplexMapAmbient (Fin.succ : Fin 1 → Fin 2) 0 = EuclideanSpace.single 0 1 := by
    rw [← Fin.succAbove_zero, simplexMapAmbient_succAbove_zero]
    ext k
    fin_cases k
    simp
  have h₁ : simplexMapAmbient (Fin.succAbove (1 : Fin 2)) 0 = 0 := by
    rw [← Fin.succ_zero_eq_one', simplexMapAmbient_succAbove_succ]
    ext k
    fin_cases k
    simp
  rw [simplexCurrent_extDerivCLM, Fin.sum_univ_two, simplexCurrent_zero_apply,
    simplexCurrent_zero_apply]
  simp [h₀, h₁, Subsingleton.elim (_ : Fin 0 → EuclideanSpace ℝ (Fin 1)) ![], sub_eq_add_neg]

/-- `[[Δᵖ]]` is compatible with restriction: on a test form extended by zero from a smaller open
set `Ω'`, the current `[[Δᵖ]]` on `Ω` is the current `[[Δᵖ]]` on `Ω'`. -/
@[simp]
theorem simplexCurrent_monoCLM {Ω Ω' : Opens (EuclideanSpace ℝ (Fin p))} (h : Ω' ≤ Ω)
    (ω : 𝓓^{n}(Ω', EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ)) :
    simplexCurrent p Ω (monoCLM ℝ ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ)) =
      simplexCurrent p Ω' ω := by
  simp [simplexCurrent_apply, monoCLM_apply, h]

/-- **The mass of the simplex**: `M([[Δᵖ]]) ≤ vol(Δᵖ)`. -/
theorem mass_simplexCurrent_le (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    mass (simplexCurrent p Ω : 𝓓^{n}(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) → ℝ) ≤
      volume (fullSimplex p) := by
  refine mass_le_iff.2 fun ω hω ↦ ?_
  rw [simplexCurrent_apply]
  calc ‖∫ x in fullSimplex p, ω x fun i ↦ EuclideanSpace.single i 1‖ₑ
      ≤ ∫⁻ x in fullSimplex p, ‖ω x fun i ↦ EuclideanSpace.single i 1‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ in fullSimplex p, 1 := lintegral_mono fun x ↦ by
        rw [← ofReal_norm, ENNReal.ofReal_le_one]
        exact ((ω x).le_opNorm _).trans (by simpa using hω x)
    _ = volume (fullSimplex p) := by simp

/-- **The simplex is a normal current**: `[[Δᵖ]]` and its boundary have finite mass. -/
theorem isNormal_simplexCurrent (p : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
    IsNormal (simplexCurrent p Ω : 𝓓(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) →L[ℝ] ℝ) := by
  have hT (p : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin p))) :
      mass (simplexCurrent p Ω : 𝓓(Ω, EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] ℝ) → ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_fullSimplex p).measure_ne_top (mass_simplexCurrent_le Ω)
  cases p with
  | zero => exact isNormal_finZero_iff.2 (hT 0 Ω)
  | succ p =>
    -- The boundary is a finite combination of pushforwards of `[[Δᵖ]]` along affine maps.
    refine isNormal_succ_iff.2 ⟨hT _ Ω, ?_⟩
    rw [simplexCurrent_comp_extDerivCLM, FunLike.coe_sum]
    refine ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ ↦ ?_) (mass_sum_le _ _)
    rw [FunLike.coe_smul, mass_smul, ContinuousLinearMap.coe_comp]
    refine ENNReal.mul_ne_top enorm_ne_top (ne_top_of_le_ne_top ?_
      (mass_comp_pullbackCLM_le _ (L := ‖(simplexMapAmbient (m := p) i.succAbove).contLinear‖₊)
        fun x _ ↦ by rw [ContinuousAffineMap.fderiv, coe_nnnorm]))
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) (hT p ⊤)

end TauCeti
