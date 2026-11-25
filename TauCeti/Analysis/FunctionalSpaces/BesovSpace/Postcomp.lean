/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Applying a continuous linear map to the values of Besov distributions

A continuous linear map `L : F →L[ℂ] G` acts on `F`-valued tempered distributions by
`(L u) ψ = L (u ψ)`. Every Littlewood–Paley block `Δⱼ` acts by precomposing the test function, so it
commutes with `L`, and `L` maps `Lᵖ(E, F)` to `Lᵖ(E, G)` with operator norm at most `‖L‖`. Hence `L`
induces a bounded linear map `B^s_{p,q}(E, F) →L[ℂ] B^s_{p,q}(E, G)` of norm at most `‖L‖`,
functorial in `L`; a continuous linear equivalence `F ≃L[ℂ] G` induces an isomorphism of Besov
spaces.

## Main declarations

* `TemperedDistribution.MemBesov.postcomp`: `L` maps `B^s_{p,q}(E, F)` into `B^s_{p,q}(E, G)` at the
  level of tempered distributions.
* `TauCeti.BesovSpace.postcomp`: the induced operator `B^s_{p,q}(E, F) →L[ℂ] B^s_{p,q}(E, G)`, of
  norm at most `‖L‖` (`TauCeti.BesovSpace.norm_postcomp_le`).
* `TauCeti.BesovSpace.postcompEquiv`: the isomorphism `B^s_{p,q}(E, F) ≃L[ℂ] B^s_{p,q}(E, G)`
  induced by `F ≃L[ℂ] G`.

## References

* H. Triebel, *Theory of Function Spaces*, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]

namespace TemperedDistribution

variable [CompleteSpace F] [CompleteSpace G]

/-- Applying a continuous linear map `L : F →L[ℂ] G` to the values of a tempered distribution in
`B^s_{p,q}(E, F)` produces a tempered distribution in `B^s_{p,q}(E, G)`. -/
theorem MemBesov.postcomp {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (L : F →L[ℂ] G) :
    MemBesov φ s p q (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L u : 𝓢'(E, G)) := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  refine memBesov_iff.2 ⟨fun j ↦ L.compLp (f j),
    fun j ↦ littlewoodPaleyBlock_postcomp_eq_compLp L (hf j),
    (hmem.const_mul ‖L‖).mono fun j ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity), mul_left_comm]
  gcongr
  exact L.norm_compLp_le (f j)

end TemperedDistribution

namespace TauCeti.BesovSpace

open TemperedDistribution

variable [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The Besov norm of `L ∘ u` is at most `‖L‖ ‖u‖`. -/
private theorem norm_postcomp_le_aux (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    ‖(u.memBesov_toDistr.postcomp L).toBesovSpace‖ ≤ ‖L‖ * ‖u‖ := by
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_and_norm_le_of_block
    (F' := G) (φ' := φ) (p' := p) (s' := s) (norm_nonneg L) u
    (w := (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L u.toDistr : 𝓢'(E, G)))
    (fun j ↦ L.compLp (u.block j))
    (fun j ↦ littlewoodPaleyBlock_postcomp_eq_compLp L (coe_block u j).symm)
    (fun j ↦ by rw [mul_left_comm]; gcongr; exact L.norm_compLp_le _)
  rwa [← ext (hv.trans (MemBesov.toDistr_toBesovSpace _).symm)]

variable (φ s p q) in
/-- The bounded operator `B^s_{p,q}(E, F) →L[ℂ] B^s_{p,q}(E, G)` induced by a continuous linear map
`L : F →L[ℂ] G` on the fiber. It sends `u` to the distribution `ψ ↦ L (u ψ)` and each block `Δⱼ u`
to `L ∘ Δⱼ u`, with operator norm at most `‖L‖`. -/
def postcomp (L : F →L[ℂ] G) : BesovSpace F φ s p q →L[ℂ] BesovSpace G φ s p q :=
  LinearMap.mkContinuous
    { toFun u := (u.memBesov_toDistr.postcomp L).toBesovSpace
      map_add' u v := ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, toDistr_add, map_add]
      map_smul' c u := ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, toDistr_smul, map_smul, RingHom.id_apply] }
    ‖L‖ (norm_postcomp_le_aux L)

@[simp]
theorem toDistr_postcomp (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    (postcomp φ s p q L u).toDistr =
      (PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L u.toDistr : 𝓢'(E, G)) :=
  MemBesov.toDistr_toBesovSpace _

theorem toDistr_postcomp_apply (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) (ψ : 𝓢(E, ℂ)) :
    (postcomp φ s p q L u).toDistr ψ = L (u.toDistr ψ) := by
  rw [toDistr_postcomp, PointwiseConvergenceCLM.postcomp_apply_apply]

@[simp]
theorem block_postcomp (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) (j : ℕ) :
    (postcomp φ s p q L u).block j = L.compLp (u.block j) :=
  Lp.toTemperedDistribution_injective <|
    (coe_block (postcomp φ s p q L u) j).trans <| by
      rw [toDistr_postcomp]
      exact littlewoodPaleyBlock_postcomp_eq_compLp L (coe_block u j).symm

theorem norm_postcomp_apply_le (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    ‖postcomp φ s p q L u‖ ≤ ‖L‖ * ‖u‖ :=
  norm_postcomp_le_aux L u

theorem norm_postcomp_le (L : F →L[ℂ] G) :
    ‖postcomp φ s p q L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) (norm_postcomp_apply_le L)

@[simp]
theorem postcomp_id :
    postcomp φ s p q (ContinuousLinearMap.id ℂ F) = ContinuousLinearMap.id ℂ _ := by
  ext u : 1
  refine ext ?_
  ext ψ
  simp only [toDistr_postcomp_apply, ContinuousLinearMap.id_apply]

@[simp]
theorem postcomp_zero :
    postcomp φ s p q (0 : F →L[ℂ] G) = 0 := by
  ext u : 1
  refine ext ?_
  ext ψ
  simp only [toDistr_postcomp_apply, zero_apply, toDistr_zero]

theorem postcomp_comp (L₁ : G →L[ℂ] H) (L₂ : F →L[ℂ] G) :
    postcomp φ s p q (L₁.comp L₂) = (postcomp φ s p q L₁).comp (postcomp φ s p q L₂) := by
  ext u : 1
  refine ext ?_
  ext ψ
  simp only [ContinuousLinearMap.comp_apply, toDistr_postcomp_apply]

@[simp]
theorem postcomp_postcomp (L₁ : G →L[ℂ] H) (L₂ : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    postcomp φ s p q L₁ (postcomp φ s p q L₂ u) = postcomp φ s p q (L₁.comp L₂) u := by
  rw [postcomp_comp, ContinuousLinearMap.comp_apply]

variable (φ s p q) in
/-- A continuous linear equivalence `e : F ≃L[ℂ] G` on the fiber induces an isomorphism of Besov
spaces `B^s_{p,q}(E, F) ≃L[ℂ] B^s_{p,q}(E, G)`. -/
def postcompEquiv (e : F ≃L[ℂ] G) : BesovSpace F φ s p q ≃L[ℂ] BesovSpace G φ s p q :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (postcomp φ s p q (e : F →L[ℂ] G))
    (postcomp φ s p q (e.symm : G →L[ℂ] F))
    (ContinuousLinearMap.ext fun v ↦ by simp [postcomp_postcomp])
    (ContinuousLinearMap.ext fun u ↦ by simp [postcomp_postcomp])

@[simp]
theorem coe_postcompEquiv (e : F ≃L[ℂ] G) :
    (postcompEquiv φ s p q e : BesovSpace F φ s p q →L[ℂ] BesovSpace G φ s p q) =
      postcomp φ s p q (e : F →L[ℂ] G) :=
  (rfl)

@[simp]
theorem postcompEquiv_apply (e : F ≃L[ℂ] G) (u : BesovSpace F φ s p q) :
    postcompEquiv φ s p q e u = postcomp φ s p q (e : F →L[ℂ] G) u :=
  (rfl)

@[simp]
theorem postcompEquiv_symm (e : F ≃L[ℂ] G) :
    (postcompEquiv φ s p q e).symm = postcompEquiv φ s p q e.symm :=
  (rfl)

end TauCeti.BesovSpace
