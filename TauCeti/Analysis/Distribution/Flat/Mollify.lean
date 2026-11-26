/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Flat.Basic
public import TauCeti.Analysis.Distribution.TestFunction.Mollify

/-!
# Flat approximation of normal currents by means of translates and by mollification

Let `ν` be a probability measure on a finite-dimensional real normed space `E`, concentrated on
`closedBall 0 r`, and let `U`, `Ω` be open sets with `U + closedBall 0 r ⊆ Ω`. The **mean of the
translates** of a current `T` on `Ω` against `ν` is the current `T ∘ M` on `U`, where
`M φ = x ↦ ∫ φ (x + v) dν(v)` (`TestFunction.translationMeanCLM`). For `ν` with a smooth density
`ρ` this is the regularization of `T` by convolution with `ρ`; for the Dirac mass at `h` it is the
translate of `T` by `h`.

The mean of translates of a normal current is normal, with `M(T ∘ M) ≤ M(T)`, and it is close to
`T` in the real flat norm: the homotopy formula `∂ (T ∘ K) + (∂ T) ∘ K = T ∘ M - T` for the averaged
homotopy operator `K` (`ContinuousLinearMap.comp_translationHomotopyCLM_comp_extDerivCLM`) writes
`T ∘ M - T = R + ∂ S` with `R = (∂ T) ∘ K` and `S = T ∘ K`, and `M(R) ≤ r M(∂ T)`, `M(S) ≤ r M(T)`.
Hence

`Flat(T ∘ M - T) ≤ r (M(T) + M(∂ T))`

(`ContinuousLinearMap.normalFlatMass_comp_translationMeanCLM_sub_le`), with `Flat(T ∘ M - T) ≤
r M(T)` in degree zero. In particular, as the measures concentrate at `0`, the means of translates
of a normal current converge to it in the flat norm
(`ContinuousLinearMap.tendsto_normalFlatMass_comp_translationMeanCLM_sub`). The statements are
proved for finite measures, with `T` replaced by `ν(E) T`.

The **mollification** of a current `T` on the whole space `E` by a normalized smooth bump
`ρ̂ = ρ.normed μ` is `T ∘ M` for the mollification `M = TestFunction.mollifyCLM` of test forms,
`(M ω) x = ∫ ρ̂ y ω (x + y) dμ(y)`. This is the mean of translates against the probability measure
with density `ρ̂`, concentrated on the closed ball of radius `r = ρ.rOut`, with `U = Ω = E`. So its
boundary is the mollification of `∂T = T ∘ d`, its mass is at most `M(T)`, and the flat estimate
`F(T - T ∘ M) ≤ r (M(T) + M(∂T))` holds for every real current of positive degree, with
`F(T - T ∘ M) ≤ r M(T)` in degree zero; the bounds are infinite unless `T` is normal. This is real
approximation: it does not preserve integer multiplicities.

## Main declarations

* `Distribution.IsNormal.comp_translationMeanCLM`: the mean of translates of a normal current is
  normal.
* `ContinuousLinearMap.normalFlatMass_comp_translationMeanCLM_sub_le`,
  `ContinuousLinearMap.normalFlatMass_comp_translationMeanCLM_sub_le_finZero`: the flat estimate.
* `ContinuousLinearMap.tendsto_normalFlatMass_comp_translationMeanCLM_sub`: flat convergence of
  the means of translates.
* `ContinuousLinearMap.comp_mollifyCLM_comp_extDerivCLM`: `∂(T ∘ M) = (∂T) ∘ M`.
* `ContinuousLinearMap.tendsto_comp_mollifyCLM`: `T ∘ M → T` on every test form as `r → 0`.
* `Distribution.mass_comp_mollifyCLM_le`: `M(T ∘ M) ≤ M(T)`.
* `Distribution.IsNormal.comp_mollifyCLM`: mollification preserves normal currents.
* `ContinuousLinearMap.normalFlatMass_sub_comp_mollifyCLM_le`: the flat estimate for
  mollification, and `ContinuousLinearMap.normalFlatMass_sub_comp_mollifyCLM_le_finZero` in degree
  zero.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.2 and §4.1.18 (the regularizations `T_ε` of a
  current and the flat estimate `F(T - T_ε) ≤ ε (M(T) + M(∂T))`).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter TestFunction Distribution
open scoped Pointwise Distributions ENNReal Topology

section TranslationMean

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {ν : Measure E} [IsFiniteMeasure ν] {r : ℝ}
  {U Ω : Opens E} {k : ℕ} {hν : ∀ᵐ v ∂ν, v ∈ closedBall (0 : E) r}
  {hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)}

namespace Distribution

/-- **The mean of the translates of a normal current is normal.** -/
theorem IsNormal.comp_translationMeanCLM {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsNormal T) : IsNormal (T ∘L translationMeanCLM ν hν hUΩ) := by
  have hM {j : ℕ} (S : 𝓓(Ω, E [⋀^Fin j]→L[ℝ] F) →L[ℝ] V) (hS : mass S ≠ ⊤) :
      mass (S ∘L translationMeanCLM ν hν hUΩ) ≠ ⊤ := by
    rw [ContinuousLinearMap.coe_comp]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (measure_ne_top ν univ) hS)
      (mass_comp_translationMeanCLM_le S)
  cases k with
  | zero => exact isNormal_finZero_iff.2 (hM T (isNormal_finZero_iff.1 hT))
  | succ k =>
    refine isNormal_succ_iff.2 ⟨hM T (isNormal_succ_iff.1 hT).1, ?_⟩
    rw [ContinuousLinearMap.comp_translationMeanCLM_comp_extDerivCLM]
    exact hM _ (isNormal_succ_iff.1 hT).2

end Distribution

namespace ContinuousLinearMap

/-- **The flat distance from a normal current to the mean of its translates**: for a normal
`(k + 1)`-current `T` on `Ω` and a finite measure `ν` concentrated on `closedBall 0 r`,
`Flat(T ∘ M - ν(E) T) ≤ r ν(E) (M(T) + M(∂ T))` on `U`. -/
theorem normalFlatMass_comp_translationMeanCLM_sub_le
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : IsNormal T) :
    (T ∘L translationMeanCLM ν hν hUΩ - ν.real univ • (T ∘L monoCLM ℝ)).normalFlatMass ≤
      ENNReal.ofReal r * ν univ * (mass T + mass (T ∘L extDerivCLM)) := by
  have hmR : mass ((T ∘L extDerivCLM) ∘L translationHomotopyCLM (k := k) ν hν hUΩ) ≤
      ENNReal.ofReal r * ν univ * mass (T ∘L extDerivCLM) := by
    rw [coe_comp]
    exact mass_comp_translationHomotopyCLM_le _
  have hmS : mass (T ∘L translationHomotopyCLM (k := k + 1) ν hν hUΩ) ≤
      ENNReal.ofReal r * ν univ * mass T := by
    rw [coe_comp]
    exact mass_comp_translationHomotopyCLM_le _
  have hfin (C : ℝ≥0∞) (hC : C ≠ ⊤) : ENNReal.ofReal r * ν univ * C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) hC
  -- The homotopy formula decomposes the difference as `(∂ T) ∘ K + ∂ (T ∘ K)`.
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM_of_mass_ne_top _
    (hT.comp_translationMeanCLM.sub (hT.comp_monoCLM.smul _))
    (ne_top_of_le_ne_top (hfin _ (isNormal_succ_iff.1 hT).2) hmR)
    (ne_top_of_le_ne_top (hfin _ (isNormal_succ_iff.1 hT).1) hmS)
    ((comp_translationHomotopyCLM_comp_extDerivCLM T).symm.trans (add_comm _ _))).trans ?_
  rw [mul_add, add_comm (_ * mass T)]
  exact add_le_add hmR hmS

/-- **The flat distance from a normal `0`-current to the mean of its translates**:
`Flat(T ∘ M - ν(E) T) ≤ r ν(E) M(T)`. -/
theorem normalFlatMass_comp_translationMeanCLM_sub_le_finZero
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : IsNormal T) :
    (T ∘L translationMeanCLM ν hν hUΩ - ν.real univ • (T ∘L monoCLM ℝ)).normalFlatMass ≤
      ENNReal.ofReal r * ν univ * mass T := by
  have hmS : mass (T ∘L translationHomotopyCLM (k := 0) ν hν hUΩ) ≤
      ENNReal.ofReal r * ν univ * mass T := by
    rw [coe_comp]
    exact mass_comp_translationHomotopyCLM_le _
  -- The homotopy formula writes the difference as the boundary `∂ (T ∘ K)`.
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM_of_mass_ne_top _
    (hT.comp_translationMeanCLM.sub (hT.comp_monoCLM.smul _)) isNormal_zero.mass_ne_top
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top ν univ)) (isNormal_finZero_iff.1 hT)) hmS)
    (by rw [zero_add, comp_translationHomotopyCLM_comp_extDerivCLM_finZero])).trans ?_
  simpa using hmS

/-- **Flat convergence of the means of translates**: if probability measures `νᵢ` are
concentrated on balls `closedBall 0 rᵢ` with `rᵢ → 0`, then the means of the translates of a
normal current `T` against `νᵢ` converge to `T` in the flat norm. -/
theorem tendsto_normalFlatMass_comp_translationMeanCLM_sub {ι : Type*} {l : Filter ι}
    {ν : ι → Measure E} [∀ i, IsProbabilityMeasure (ν i)] {r : ι → ℝ}
    (hr : Tendsto r l (𝓝 0)) (hν : ∀ i, ∀ᵐ v ∂ν i, v ∈ closedBall (0 : E) (r i))
    (hUΩ : ∀ i, (U : Set E) + closedBall (0 : E) (r i) ⊆ (Ω : Set E))
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : IsNormal T) :
    Tendsto (fun i ↦ (T ∘L translationMeanCLM (ν i) (hν i) (hUΩ i) -
      T ∘L monoCLM ℝ).normalFlatMass) l (𝓝 0) := by
  -- The flat masses are bounded by `rᵢ C` for a finite constant `C`.
  obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ i, (T ∘L translationMeanCLM (ν i) (hν i)
      (hUΩ i) - T ∘L monoCLM ℝ).normalFlatMass ≤ ENNReal.ofReal (r i) * C := by
    cases k with
    | zero =>
      refine ⟨mass T, isNormal_finZero_iff.1 hT, fun i ↦ ?_⟩
      simpa using normalFlatMass_comp_translationMeanCLM_sub_le_finZero (hν := hν i)
        (hUΩ := hUΩ i) hT
    | succ k =>
      refine ⟨mass T + mass (T ∘L extDerivCLM), ENNReal.add_ne_top.2 (isNormal_succ_iff.1 hT),
        fun i ↦ ?_⟩
      simpa using normalFlatMass_comp_translationMeanCLM_sub_le (hν := hν i) (hUΩ := hUΩ i) hT
  have hlim : Tendsto (fun i ↦ ENNReal.ofReal (r i) * C) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hr) (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
    hbound

end ContinuousLinearMap

end TranslationMean

section Mollify

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure E) [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E)) {k : ℕ}

namespace ContinuousLinearMap

/-- **Mollified currents converge on every test form**: as the bumps shrink,
`T (M φ) → T φ`. -/
theorem tendsto_comp_mollifyCLM [CompleteSpace F] (T : 𝓓((⊤ : Opens E), F) →L[ℝ] V)
    {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0)) (φ : 𝓓((⊤ : Opens E), F)) :
    Tendsto (fun i ↦ T (mollifyCLM μ (ρ i) φ)) l (𝓝 (T φ)) :=
  (T.continuous.tendsto φ).comp (tendsto_mollifyCLM μ hρ φ)

/-- **The boundary of a mollified current** is the mollified boundary: `∂(T ∘ M) = (∂T) ∘ M`. -/
theorem comp_mollifyCLM_comp_extDerivCLM [CompleteSpace F]
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) :
    (T ∘L mollifyCLM μ ρ) ∘L extDerivCLM = (T ∘L extDerivCLM) ∘L mollifyCLM μ ρ := by
  rw [ContinuousLinearMap.comp_assoc, ← extDerivCLM_comp_mollifyCLM,
    ContinuousLinearMap.comp_assoc]

end ContinuousLinearMap

namespace Distribution

/-- **Mollification does not increase mass**: `M(T ∘ M) ≤ M(T)`. -/
theorem mass_comp_mollifyCLM_le {𝓕 : Type*} [FunLike 𝓕 𝓓((⊤ : Opens E), F) V]
    [LinearMapClass 𝓕 ℝ 𝓓((⊤ : Opens E), F) V] (T : 𝓕) :
    mass (T ∘ mollifyCLM μ ρ) ≤ mass T := by
  simpa [mollifyCLM_eq_translationMeanCLM] using mass_comp_translationMeanCLM_le
    (ν := ρ.normedMeasure μ) (hν := ρ.ae_mem_closedBall_normedMeasure μ) (hUΩ := subset_univ _) T

/-- **Mollification preserves normal currents.** -/
theorem IsNormal.comp_mollifyCLM [CompleteSpace F]
    {T : 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V} (hT : IsNormal T) :
    IsNormal (T ∘L mollifyCLM μ ρ) := by
  rw [mollifyCLM_eq_translationMeanCLM]
  exact hT.comp_translationMeanCLM

end Distribution

namespace ContinuousLinearMap

/-- **The flat estimate for mollification**: for a current `T` of positive degree,
`F(T - T ∘ M) ≤ r (M(T) + M(∂T))`, where `F` is the real normal flat mass and `r = ρ.rOut`. This
is the flat estimate for the mean of translates against the probability measure with density
`ρ̂`. -/
theorem normalFlatMass_sub_comp_mollifyCLM_le
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    (T - T ∘L mollifyCLM μ ρ).normalFlatMass ≤
      ENNReal.ofReal ρ.rOut * (mass T + mass (T ∘L extDerivCLM)) := by
  by_cases hT : IsNormal T
  · rw [← normalFlatMass_neg, neg_sub, mollifyCLM_eq_translationMeanCLM]
    simpa using normalFlatMass_comp_translationMeanCLM_sub_le
      (U := ⊤) (hν := ρ.ae_mem_closedBall_normedMeasure μ) (hUΩ := subset_univ _) hT
  · have hr : ENNReal.ofReal ρ.rOut ≠ 0 := (ENNReal.ofReal_pos.2 ρ.rOut_pos).ne'
    rw [isNormal_succ_iff, not_and_or, not_ne_iff, not_ne_iff] at hT
    rcases hT with h | h <;> simp [h, hr]

/-- **The flat estimate for mollification in degree zero**: `F(T - T ∘ M) ≤ r M(T)`, where `F` is
the real normal flat mass and `r = ρ.rOut`. -/
theorem normalFlatMass_sub_comp_mollifyCLM_le_finZero
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    (T - T ∘L mollifyCLM μ ρ).normalFlatMass ≤ ENNReal.ofReal ρ.rOut * mass T := by
  by_cases hT : IsNormal T
  · rw [← normalFlatMass_neg, neg_sub, mollifyCLM_eq_translationMeanCLM]
    simpa using normalFlatMass_comp_translationMeanCLM_sub_le_finZero
      (U := ⊤) (hν := ρ.ae_mem_closedBall_normedMeasure μ) (hUΩ := subset_univ _) hT
  · have hr : ENNReal.ofReal ρ.rOut ≠ 0 := (ENNReal.ofReal_pos.2 ρ.rOut_pos).ne'
    simp [(not_ne_iff.1 (isNormal_finZero_iff.not.1 hT)), hr]

end ContinuousLinearMap

end Mollify
