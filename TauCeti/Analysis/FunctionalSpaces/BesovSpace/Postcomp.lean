/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Normed.Lp.MapCLM
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Applying a continuous linear map to the values of Besov functions

A continuous linear map `L : F →L[ℂ] G` acts on `F`-valued tempered distributions by
`(L u) φ = L (u φ)`. The Littlewood–Paley blocks act on the test functions, so they commute with
`L` (`TemperedDistribution.littlewoodPaleyBlock_postcomp`), and `L` maps `Lᵖ(E, F)` to `Lᵖ(E, G)`
with norm at most `‖L‖`. Hence `L` maps `B^s_{p,q}(E; F)` to `B^s_{p,q}(E; G)` with norm at most
`‖L‖`, acting on the weighted blocks by `L`.

## Main declarations

* `TemperedDistribution.MemBesov.postcomp`: `B^s_{p,q}` is stable under applying `L` to the
  values.
* `TauCeti.BesovSpace.postcomp`: the bounded operator `B^s_{p,q}(E; F) →L[ℂ] B^s_{p,q}(E; G)`
  induced by `L`, of norm at most `‖L‖` (`TauCeti.BesovSpace.norm_postcomp_le`).
* `TauCeti.BesovSpace.postcomp_comp`, `TauCeti.BesovSpace.postcomp_id`: these operators compose as
  the maps `L` do.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

namespace TemperedDistribution

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Continuous linear maps on Besov spaces.** If `u ∈ B^s_{p,q}(E; F)` and `L : F →L[ℂ] G`, then
`L u ∈ B^s_{p,q}(E; G)`. -/
theorem MemBesov.postcomp {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (L : F →L[ℂ] G) :
    MemBesov φ s p q (PointwiseConvergenceCLM.postcomp _ L u) := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  refine memBesov_iff.2 ⟨fun j ↦ L.compLp (f j), fun j ↦ ?_,
    (hmem.const_mul ‖L‖).mono fun j ↦ ?_⟩
  · rw [littlewoodPaleyBlock_postcomp, hf j, Lp.toTemperedDistribution_compLp]
  · rw [Real.norm_of_nonneg (by positivity)]
    calc (2 : ℝ) ^ (s * j) * ‖L.compLp (f j)‖ ≤ (2 : ℝ) ^ (s * j) * (‖L‖ * ‖f j‖) := by
          gcongr
          exact L.norm_compLp_le (f j)
      _ = ‖L‖ * ((2 : ℝ) ^ (s * j) * ‖f j‖) := by ring

end TemperedDistribution

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The weighted blocks of `L u`: `L` applied to the weighted blocks of `u`. -/
private def postcompWeightedBlocks (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    lp (fun _ : ℕ ↦ Lp G p (volume : Measure E)) q :=
  lp.ampliation ℕ q (L.compLpL p (volume : Measure E)) u.weightedBlocks

private theorem coe_postcompWeightedBlocks_apply (L : F →L[ℂ] G) (u : BesovSpace F φ s p q)
    (j : ℕ) :
    (postcompWeightedBlocks L u j : 𝓢'(E, G)) = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) •
      littlewoodPaleyBlock G φ j (PointwiseConvergenceCLM.postcomp _ L u.toDistr) := by
  rw [postcompWeightedBlocks, lp.ampliation_apply_apply, ContinuousLinearMap.compLpL_apply,
    Lp.toTemperedDistribution_compLp, u.coe_weightedBlocks_apply, map_smul,
    littlewoodPaleyBlock_postcomp]

/-- `L u` as an element of `B^s_{p,q}(E; G)`. -/
private def postcompAux (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) : BesovSpace G φ s p q :=
  ⟨PointwiseConvergenceCLM.postcomp _ L u.toDistr, postcompWeightedBlocks L u,
    coe_postcompWeightedBlocks_apply L u⟩

private theorem weightedBlocks_postcompAux (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    (postcompAux L u).weightedBlocks = postcompWeightedBlocks L u :=
  (rfl)

private theorem norm_postcompAux_le (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    ‖postcompAux L u‖ ≤ ‖L‖ * ‖u‖ := by
  rw [← norm_weightedBlocks, ← norm_weightedBlocks, weightedBlocks_postcompAux,
    postcompWeightedBlocks]
  exact (lp.ampliation ℕ q (L.compLpL p (volume : Measure E))).le_of_opNorm_le
    ((lp.norm_ampliation_le _).trans L.norm_compLpL_le) u.weightedBlocks

variable (φ s p q) in
/-- **Continuous linear maps on Besov spaces.** A continuous linear map `L : F →L[ℂ] G`, applied to
the values, as a bounded operator `B^s_{p,q}(E; F) → B^s_{p,q}(E; G)`. It acts on the weighted
blocks by `L`, so its norm is at most `‖L‖` (`TauCeti.BesovSpace.norm_postcomp_le`). -/
def postcomp (L : F →L[ℂ] G) : BesovSpace F φ s p q →L[ℂ] BesovSpace G φ s p q :=
  LinearMap.mkContinuous
    { toFun := postcompAux L
      map_add' u v := ext (map_add (PointwiseConvergenceCLM.postcomp _ L) u.toDistr v.toDistr)
      map_smul' c u := ext (map_smul (PointwiseConvergenceCLM.postcomp _ L) c u.toDistr) }
    ‖L‖ (norm_postcompAux_le L)

@[simp]
theorem toDistr_postcomp (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    (postcomp φ s p q L u).toDistr = PointwiseConvergenceCLM.postcomp _ L u.toDistr :=
  (rfl)

/-- The norm of `TauCeti.BesovSpace.postcomp L` is at most `‖L‖`. -/
theorem norm_postcomp_le (L : F →L[ℂ] G) : ‖postcomp (E := E) φ s p q L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

/-- Applying `L` and then `M` to the values is applying `M ∘ L`. -/
theorem postcomp_comp (M : G →L[ℂ] H) (L : F →L[ℂ] G) :
    postcomp (E := E) φ s p q M ∘L postcomp φ s p q L = postcomp φ s p q (M.comp L) := by
  ext1 u
  ext1
  ext ψ
  simp only [ContinuousLinearMap.comp_apply, toDistr_postcomp, postcomp_apply_apply]

@[simp]
theorem postcomp_id : postcomp (E := E) φ s p q (ContinuousLinearMap.id ℂ F) = .id ℂ _ := by
  ext1 u
  ext1
  ext ψ
  simp only [toDistr_postcomp, postcomp_apply_apply, ContinuousLinearMap.id_apply]

end TauCeti.BesovSpace
