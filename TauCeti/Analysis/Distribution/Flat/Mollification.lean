/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Flat.Basic
public import TauCeti.Analysis.Distribution.TestFunction.Average.Homotopy

/-!
# Flat approximation of normal currents by means of translates

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

## Main declarations

* `Distribution.IsNormal.comp_translationMeanCLM`: the mean of translates of a normal current is
  normal.
* `ContinuousLinearMap.normalFlatMass_comp_translationMeanCLM_sub_le`,
  `ContinuousLinearMap.normalFlatMass_comp_translationMeanCLM_sub_le_finZero`: the flat estimate.
* `ContinuousLinearMap.tendsto_normalFlatMass_comp_translationMeanCLM_sub`: flat convergence of
  the means of translates.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.18 (the regularizations `T_ε` of a current and the
  flat estimate `F(T - T_ε) ≤ ε (M(T) + M(∂T))`).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter TestFunction Distribution
open scoped Pointwise Distributions ENNReal Topology

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
  set X := T ∘L translationMeanCLM ν hν hUΩ - ν.real univ • (T ∘L monoCLM ℝ)
  set R := (T ∘L extDerivCLM) ∘L translationHomotopyCLM (k := k) ν hν hUΩ
  set S := T ∘L translationHomotopyCLM (k := k + 1) ν hν hUΩ
  have hX : IsNormal X := hT.comp_translationMeanCLM.sub (hT.comp_monoCLM.smul _)
  -- The homotopy formula decomposes `X` as `R + ∂ S`.
  have hdec : X = R + S ∘L extDerivCLM := by
    simp only [X, R, S]
    exact (comp_translationHomotopyCLM_comp_extDerivCLM T).symm.trans (add_comm _ _)
  have hmR : mass R ≤ ENNReal.ofReal r * ν univ * mass (T ∘L extDerivCLM) := by
    rw [coe_comp]
    exact mass_comp_translationHomotopyCLM_le _
  have hmS : mass S ≤ ENNReal.ofReal r * ν univ * mass T := by
    rw [coe_comp]
    exact mass_comp_translationHomotopyCLM_le _
  have hfin (C : ℝ≥0∞) (hC : C ≠ ⊤) : ENNReal.ofReal r * ν univ * C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) hC
  -- `R` is normal: its boundary is the boundary of `X`, since `∂ ∂ S = 0`.
  have hR : IsNormal R := by
    refine isNormal_succ_iff.2 ⟨ne_top_of_le_ne_top (hfin _ (isNormal_succ_iff.1 hT).2) hmR, ?_⟩
    have hRd : R ∘L extDerivCLM = X ∘L extDerivCLM := by
      rw [hdec, add_comp, comp_assoc S, extDerivCLM_comp_extDerivCLM, comp_zero, add_zero]
    rw [hRd]
    exact (isNormal_succ_iff.1 hX).2
  -- `S` is normal: its boundary is `X - R`.
  have hS : IsNormal S := by
    refine isNormal_succ_iff.2 ⟨ne_top_of_le_ne_top (hfin _ (isNormal_succ_iff.1 hT).1) hmS, ?_⟩
    have hSd : S ∘L extDerivCLM = X - R := by rw [hdec]; abel
    rw [hSd]
    exact (hX.sub hR).mass_ne_top
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM X hR hS hdec).trans ?_
  rw [mul_add, add_comm (_ * mass T)]
  exact add_le_add hmR hmS

/-- **The flat distance from a normal `0`-current to the mean of its translates**:
`Flat(T ∘ M - ν(E) T) ≤ r ν(E) M(T)`. -/
theorem normalFlatMass_comp_translationMeanCLM_sub_le_finZero
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ} (hT : IsNormal T) :
    (T ∘L translationMeanCLM ν hν hUΩ - ν.real univ • (T ∘L monoCLM ℝ)).normalFlatMass ≤
      ENNReal.ofReal r * ν univ * mass T := by
  set S := T ∘L translationHomotopyCLM (k := 0) ν hν hUΩ
  have hmS : mass S ≤ ENNReal.ofReal r * ν univ * mass T := by
    rw [coe_comp]
    exact mass_comp_translationHomotopyCLM_le _
  have hX : IsNormal (T ∘L translationMeanCLM ν hν hUΩ - ν.real univ • (T ∘L monoCLM ℝ)) :=
    hT.comp_translationMeanCLM.sub (hT.comp_monoCLM.smul _)
  have hdec : T ∘L translationMeanCLM ν hν hUΩ - ν.real univ • (T ∘L monoCLM ℝ) =
      0 + S ∘L extDerivCLM := by
    rw [zero_add, comp_translationHomotopyCLM_comp_extDerivCLM_finZero]
  have hS : IsNormal S := by
    refine isNormal_succ_iff.2 ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (measure_ne_top ν univ)) (isNormal_finZero_iff.1 hT)) hmS, ?_⟩
    rw [← zero_add (S ∘L extDerivCLM), ← hdec]
    exact isNormal_finZero_iff.1 hX
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM _ isNormal_zero hS hdec).trans ?_
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
