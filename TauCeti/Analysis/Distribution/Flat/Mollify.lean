/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Flat.Basic
public import TauCeti.Analysis.Distribution.TestFunction.Mollify

/-!
# Mollification of currents in Euclidean space

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let
`ρ` be a smooth bump function centred at `0`, normalized to `ρ̂ = ρ.normed μ` of integral one and
supported in the closed ball of radius `r = ρ.rOut`. The **mollification** of a current `T` on `E`
is `T ∘ M`, for the mollification `M = TestFunction.mollifyCLM` of test forms,
`(M ω) x = ∫ ρ̂ y ω (x + y) dμ(y)`. Its boundary is the mollification of `∂T = T ∘ d`, its mass is
at most `M(T)`, and it converges to `T` on every test form as the bump shrinks.

The averaged straight-line homotopy operator `K = TestFunction.mollifyHomotopyCLM` satisfies the
homotopy formula `K d + d K = M - id` on forms of positive degree and `K d = M - id` on functions.
Its sup bound `‖K ω‖ ≤ r ‖ω‖` gives the decomposition `T - T ∘ M = R + ∂S` with `S = -(T ∘ K)` and
`R = -(∂T ∘ K)`, of masses at most `r M(T)` and `r M(∂T)`. Hence the **flat estimate**: for every
real current `T` of positive degree,

`F(T - T ∘ M) ≤ r (M(T) + M(∂T))`,

for the real normal flat mass `F = ContinuousLinearMap.normalFlatMass`, and `F(T - T ∘ M) ≤ r M(T)`
in degree zero; the bounds are infinite unless `T` is normal. Mollification thus approximates
normal currents in flat mass as `r → 0`, keeping both mass and boundary mass bounded. This is real
approximation: it does not preserve integer multiplicities.

## Main declarations

* `ContinuousLinearMap.comp_mollifyCLM_comp_extDerivCLM`: `∂(T ∘ M) = (∂T) ∘ M`.
* `ContinuousLinearMap.tendsto_comp_mollifyCLM`: `T ∘ M → T` on every test form as `r → 0`.
* `Distribution.mass_comp_mollifyCLM_le`: `M(T ∘ M) ≤ M(T)`.
* `Distribution.mass_comp_mollifyHomotopyCLM_le`: `M(T ∘ K) ≤ r M(T)`.
* `Distribution.IsNormal.comp_mollifyCLM`: mollification preserves normal currents.
* `ContinuousLinearMap.normalFlatMass_sub_comp_mollifyCLM_le`: the flat estimate, and
  `ContinuousLinearMap.normalFlatMass_sub_comp_mollifyCLM_le_finZero` in degree zero.

## References

* H. Federer, *Geometric Measure Theory*, §4.1 (regularization of currents by convolution and
  its flat estimate).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula for
  translations).
-/

public section

noncomputable section

open Set Function MeasureTheory Metric TopologicalSpace Filter
open scoped Distributions Topology ENNReal NNReal

namespace ContinuousLinearMap

open TestFunction

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure E) [μ.IsAddHaarMeasure] {k : ℕ}

/-- **Mollified currents converge on every test form**: as the bumps shrink,
`T (M φ) → T φ`. -/
theorem tendsto_comp_mollifyCLM [CompleteSpace F] (T : 𝓓((⊤ : Opens E), F) →L[ℝ] V)
    {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0)) (φ : 𝓓((⊤ : Opens E), F)) :
    Tendsto (fun i ↦ T (mollifyCLM μ (ρ i) φ)) l (𝓝 (T φ)) :=
  (T.continuous.tendsto φ).comp (tendsto_mollifyCLM μ hρ φ)

variable (ρ : ContDiffBump (0 : E)) [CompleteSpace F]

/-- **The boundary of a mollified current** is the mollified boundary: `∂(T ∘ M) = (∂T) ∘ M`. -/
theorem comp_mollifyCLM_comp_extDerivCLM
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) :
    (T ∘L mollifyCLM μ ρ) ∘L extDerivCLM = (T ∘L extDerivCLM) ∘L mollifyCLM μ ρ := by
  rw [ContinuousLinearMap.comp_assoc, ← extDerivCLM_comp_mollifyCLM,
    ContinuousLinearMap.comp_assoc]

end ContinuousLinearMap

namespace Distribution

open TestFunction

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure E) [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E)) {k : ℕ}

/-- **Mollification does not increase mass**: `M(T ∘ M) ≤ M(T)`. -/
theorem mass_comp_mollifyCLM_le {𝓕 : Type*} [FunLike 𝓕 𝓓((⊤ : Opens E), F) V]
    [LinearMapClass 𝓕 ℝ 𝓓((⊤ : Opens E), F) V] (T : 𝓕) :
    mass (T ∘ mollifyCLM μ ρ) ≤ mass T := by
  simpa using mass_comp_le_of_norm_apply_le T zero_le_one fun φ hφ x ↦
    norm_mollifyCLM_apply_le μ ρ φ hφ x

/-- **Mass of the averaged homotopy current**: `M(T ∘ K) ≤ r M(T)` for a `k`-current `T`, with
`r = ρ.rOut`. -/
theorem mass_comp_mollifyHomotopyCLM_le {𝓕 : Type*}
    [FunLike 𝓕 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) V]
    [LinearMapClass 𝓕 ℝ 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) V] (T : 𝓕) :
    mass (T ∘ mollifyHomotopyCLM μ ρ) ≤ ENNReal.ofReal ρ.rOut * mass T :=
  mass_comp_le_of_norm_apply_le T ρ.rOut_pos.le fun φ hφ x ↦ by
    simpa using norm_mollifyHomotopyCLM_apply_le μ ρ φ hφ x

variable [CompleteSpace F]

/-- **Mollification preserves normal currents.** -/
theorem IsNormal.comp_mollifyCLM {T : 𝓓((⊤ : Opens E), E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsNormal T) : IsNormal (T ∘L mollifyCLM μ ρ) := by
  cases k with
  | zero =>
    rw [isNormal_finZero_iff] at hT ⊢
    exact ne_top_of_le_ne_top hT (mass_comp_mollifyCLM_le μ ρ T)
  | succ k =>
    rw [isNormal_succ_iff] at hT ⊢
    rw [ContinuousLinearMap.comp_mollifyCLM_comp_extDerivCLM]
    exact ⟨ne_top_of_le_ne_top hT.1 (mass_comp_mollifyCLM_le μ ρ T),
      ne_top_of_le_ne_top hT.2 (mass_comp_mollifyCLM_le μ ρ (T ∘L extDerivCLM))⟩

end Distribution

namespace ContinuousLinearMap

open TestFunction Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (ρ : ContDiffBump (0 : E)) {k : ℕ}

/-- **The flat estimate for mollification**: for a current `T` of positive degree,
`F(T - T ∘ M) ≤ r (M(T) + M(∂T))`, where `F` is the real normal flat mass and `r = ρ.rOut`. The
decomposition is `T - T ∘ M = -(∂T ∘ K) + ∂(-(T ∘ K))` for the averaged homotopy operator `K`. -/
theorem normalFlatMass_sub_comp_mollifyCLM_le
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    (T - T ∘L mollifyCLM μ ρ).normalFlatMass ≤
      ENNReal.ofReal ρ.rOut * (mass T + mass (T ∘L extDerivCLM)) := by
  have hr : ENNReal.ofReal ρ.rOut ≠ 0 := (ENNReal.ofReal_pos.2 ρ.rOut_pos).ne'
  by_cases hT : mass T = ⊤ ∨ mass (T ∘L extDerivCLM) = ⊤
  · rcases hT with h | h <;> simp [h, hr]
  push Not at hT
  set S := -(T ∘L mollifyHomotopyCLM μ ρ) with hS
  set R := -((T ∘L extDerivCLM) ∘L mollifyHomotopyCLM μ ρ) with hR
  have hSd : S ∘L extDerivCLM = T - T ∘L mollifyCLM μ ρ - R := by
    rw [hS, hR, neg_comp, comp_assoc, mollifyHomotopyCLM_comp_extDerivCLM, comp_sub, comp_sub,
      comp_id, comp_assoc]
    abel
  have hmS : mass S ≤ ENNReal.ofReal ρ.rOut * mass T := by
    rw [hS, FunLike.coe_neg, mass_neg]
    exact mass_comp_mollifyHomotopyCLM_le μ ρ T
  have hmR : mass R ≤ ENNReal.ofReal ρ.rOut * mass (T ∘L extDerivCLM) := by
    rw [hR, FunLike.coe_neg, mass_neg]
    exact mass_comp_mollifyHomotopyCLM_le μ ρ (T ∘L extDerivCLM)
  have hmS' : mass S ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.1) hmS
  have hmR' : mass R ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.2) hmR
  have hmM : mass (T ∘L mollifyCLM μ ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top hT.1 (mass_comp_mollifyCLM_le μ ρ T)
  have hnS : IsNormal S := by
    refine isNormal_succ_iff.2 ⟨hmS', ?_⟩
    rw [hSd]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hT.1, hmM⟩, hmR'⟩)
      (mass_sub_le.trans (add_le_add mass_sub_le le_rfl))
  have hnR : IsNormal R := by
    refine isNormal_succ_iff.2 ⟨hmR', ?_⟩
    have hRd : R ∘L extDerivCLM =
        T ∘L extDerivCLM - (T ∘L extDerivCLM) ∘L mollifyCLM μ ρ := by
      have h := congr($hSd ∘L extDerivCLM)
      rw [comp_assoc, extDerivCLM_comp_extDerivCLM, comp_zero, sub_comp, sub_comp,
        comp_mollifyCLM_comp_extDerivCLM] at h
      exact (sub_eq_zero.1 h.symm).symm
    rw [hRd]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hT.2, hT.2⟩)
      (mass_sub_le.trans (add_le_add le_rfl (mass_comp_mollifyCLM_le μ ρ (T ∘L extDerivCLM))))
  calc (T - T ∘L mollifyCLM μ ρ).normalFlatMass ≤ mass R + mass S :=
        normalFlatMass_le_of_eq_add_comp_extDerivCLM _ hnR hnS (by rw [hSd]; abel)
    _ ≤ ENNReal.ofReal ρ.rOut * mass (T ∘L extDerivCLM) + ENNReal.ofReal ρ.rOut * mass T :=
        add_le_add hmR hmS
    _ = ENNReal.ofReal ρ.rOut * (mass T + mass (T ∘L extDerivCLM)) := by ring

/-- **The flat estimate for mollification in degree zero**: `F(T - T ∘ M) ≤ r M(T)`, where `F` is
the real normal flat mass and `r = ρ.rOut`. The decomposition is `T - T ∘ M = ∂(-(T ∘ K))` for
the averaged homotopy operator `K`. -/
theorem normalFlatMass_sub_comp_mollifyCLM_le_finZero
    (T : 𝓓((⊤ : Opens E), E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    (T - T ∘L mollifyCLM μ ρ).normalFlatMass ≤ ENNReal.ofReal ρ.rOut * mass T := by
  have hr : ENNReal.ofReal ρ.rOut ≠ 0 := (ENNReal.ofReal_pos.2 ρ.rOut_pos).ne'
  by_cases hT : mass T = ⊤
  · simp [hT, hr]
  set S := -(T ∘L mollifyHomotopyCLM μ ρ) with hS
  have hSd : S ∘L extDerivCLM = T - T ∘L mollifyCLM μ ρ := by
    rw [hS, neg_comp, comp_assoc, mollifyHomotopyCLM_comp_extDerivCLM_finZero, comp_sub, comp_id]
    abel
  have hmS : mass S ≤ ENNReal.ofReal ρ.rOut * mass T := by
    rw [hS, FunLike.coe_neg, mass_neg]
    exact mass_comp_mollifyHomotopyCLM_le μ ρ T
  have hnS : IsNormal S := by
    refine isNormal_succ_iff.2
      ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT) hmS, ?_⟩
    rw [hSd]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hT, hT⟩)
      (mass_sub_le.trans (add_le_add le_rfl (mass_comp_mollifyCLM_le μ ρ T)))
  calc (T - T ∘L mollifyCLM μ ρ).normalFlatMass
      ≤ mass (0 : 𝓓((⊤ : Opens E), E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) + mass S :=
        normalFlatMass_le_of_eq_add_comp_extDerivCLM _ isNormal_zero hnS (by rw [hSd, zero_add])
    _ ≤ ENNReal.ofReal ρ.rOut * mass T := by simpa using hmS

end ContinuousLinearMap
