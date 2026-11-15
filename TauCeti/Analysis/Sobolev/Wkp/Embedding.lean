/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.Wkp.Basic

/-!
# Higher-order embeddings from a first-order embedding

Let `S : W^{1,p}(Ω) → L^{p⋆}(Ω)` be a bounded linear map representing the values, such as a
first-order Sobolev embedding. Every derivative of order at most `k` of a function in
`W^{k+1,p}(Ω)` lies in `W^{1,p}(Ω)`, so applying `S` to it lands in `L^{p⋆}(Ω)`. Keeping all the
weak derivatives, the inclusion is therefore a continuous linear map `W^{k+1,p}(Ω) → W^{k,p⋆}(Ω)`.
No hypothesis on `Ω` is needed beyond the existence of `S`.

The vector-valued derivative fields are embedded coordinatewise
(`TauCeti.WeakDerivStep.exists_lpEmbeddingL_of_ae_eq`). The higher-order space is then reassembled
one weak derivative at a time with `TauCeti.Wkp.mk`; its continuity follows from that of the
lower-order component and the highest derivative separately.

## Main declarations

* `TauCeti.Wkp.exists_sobolevEmbeddingL_succ_of_ae_eq`: the embedding
  `W^{k+2,p}(Ω) →L[ℝ] W^{k+1,p⋆}(Ω)`, preserving the value and the highest weak derivative.
* `TauCeti.Wkp.exists_sobolevEmbeddingL_of_ae_eq`: the embedding
  `W^{k+1,p}(Ω) →L[ℝ] W^{k,p⋆}(Ω)`, preserving the value.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.3, Theorem 6 (i).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p pstar : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ pstar)]

/-- The highest derivative of the order-`k + 1` part of `u ∈ W^{k+2,p}(Ω)` lies in
`L^{p⋆}(Ω)`, continuously in `u`. -/
private theorem exists_iteratedGradientL_of_ae_eq
    (S : W1p mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict Omega))
    (hS : ∀ u, S u =ᵐ[mu.restrict Omega] W1p.value u) (k : ℕ) :
    ∃ V : Wkp mu Omega p (k + 2) →L[ℝ] Lp (IteratedGradient E k) pstar (mu.restrict Omega),
      ∀ u, V u =ᵐ[mu.restrict Omega] iteratedGradient k (lowerOrder (k + 1) u) := by
  obtain ⟨V, hV⟩ := WeakDerivStep.exists_lpEmbeddingL_of_ae_eq S hS
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL
  refine ⟨V, fun u ↦ ?_⟩
  rw [iteratedGradient_eq_sobolevStage_iteratedGradientL, lowerOrder_succ]
  exact hV u

/-- The embedding `W^{2,p}(Ω) → W^{1,p⋆}(Ω)`, preserving the value and the gradient, built from
`S`. -/
private theorem exists_sobolevEmbeddingL_two_of_ae_eq
    (S : W1p mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict Omega))
    (hS : ∀ u, S u =ᵐ[mu.restrict Omega] W1p.value u) :
    ∃ T : Wkp mu Omega p 2 →L[ℝ] Wkp mu Omega pstar 1,
      ∀ u, value 1 (T u) =ᵐ[mu.restrict Omega] value 2 u ∧
        iteratedGradient 0 (T u) =ᵐ[mu.restrict Omega] iteratedGradient 0 (lowerOrder 1 u) := by
  obtain ⟨V, hV⟩ := exists_iteratedGradientL_of_ae_eq S hS 0
  let S₁ := S.comp (firstOrderL (mu := mu) (Omega := Omega) (p := p) 1)
  have hfirst (u : Wkp mu Omega p 2) : firstOrderL 1 u = lowerOrder 1 u := by
    rw [firstOrderL_apply, firstOrder_succ, firstOrder_zero]
  have hS₁ (u : Wkp mu Omega p 2) : S₁ u =ᵐ[mu.restrict Omega] value 2 u := by
    rw [value_succ, value_one, ← hfirst]
    exact hS _
  have hV' (u : Wkp mu Omega p 2) : V u =ᵐ[mu.restrict Omega]
      W1p.gradient (firstOrderL 1 u) := by
    rw [hfirst, ← iteratedGradient_zero]
    exact hV u
  have hmk (u : Wkp mu Omega p 2) : HasWeakFDerivOn mu Omega (S₁ u)
      (fun x ↦ innerSL ℝ (V u x)) :=
    ((W1p.hasWeakFDerivOn (firstOrderL 1 u)).congr_ae (hS _).symm).congr_ae_deriv
      (by filter_upwards [hV' u] with x hx; rw [hx])
  let F : Wkp mu Omega p 2 → W1p mu Omega pstar := fun u ↦ W1p.mk (S₁ u) (V u) (hmk u)
  have hF (u) : W1p.value (F u) = S₁ u := W1p.value_mk _ _ _
  have hG (u) : W1p.gradient (F u) = V u := W1p.gradient_mk _ _ _
  have hadd (a b : W1p mu Omega pstar) : W1p.value (a + b) = W1p.value a + W1p.value b := by
    simp only [← W1p.valueL_apply, map_add]
  have hsmul (c : ℝ) (a : W1p mu Omega pstar) : W1p.value (c • a) = c • W1p.value a := by
    simp only [← W1p.valueL_apply, map_smul]
  let T : Wkp mu Omega p 2 →ₗ[ℝ] W1p mu Omega pstar :=
    { toFun := F
      map_add' := fun u v ↦ W1p.ext_value (by rw [hadd, hF, hF, hF, map_add])
      map_smul' := fun c u ↦ W1p.ext_value (by
        rw [hsmul, hF, hF, map_smul, RingHom.id_apply]) }
  have hvalue : Continuous fun u ↦ W1p.value (T u) := by
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, hF]
    exact S₁.continuous
  have hgradient : Continuous fun u ↦ W1p.gradient (T u) := by
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, hG]
    exact V.continuous
  have hcont : Continuous T := continuous_iff_continuousAt.2 fun u ↦
    W1p.tendsto_iff_value_gradient.2 ⟨hvalue.continuousAt, hgradient.continuousAt⟩
  refine ⟨⟨T, hcont⟩, fun u ↦ ⟨?_, ?_⟩⟩
  · rw [value_one]
    exact (hF u).symm ▸ hS₁ u
  · rw [iteratedGradient_zero]
    exact (hG u).symm ▸ hV u

/-- One step of the reassembly: an embedding `W^{k+2,p}(Ω) → W^{k+1,p⋆}(Ω)` preserving the value
and the highest derivative extends to `W^{k+3,p}(Ω) → W^{k+2,p⋆}(Ω)` with the same properties. -/
private theorem exists_sobolevEmbeddingL_step_of_ae_eq
    (S : W1p mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict Omega))
    (hS : ∀ u, S u =ᵐ[mu.restrict Omega] W1p.value u) (k : ℕ)
    (T₀ : Wkp mu Omega p (k + 2) →L[ℝ] Wkp mu Omega pstar (k + 1))
    (hT₀ : ∀ u, value (k + 1) (T₀ u) =ᵐ[mu.restrict Omega] value (k + 2) u ∧
      iteratedGradient k (T₀ u) =ᵐ[mu.restrict Omega] iteratedGradient k (lowerOrder (k + 1) u)) :
    ∃ T : Wkp mu Omega p (k + 3) →L[ℝ] Wkp mu Omega pstar (k + 2),
      ∀ u, value (k + 2) (T u) =ᵐ[mu.restrict Omega] value (k + 3) u ∧
        iteratedGradient (k + 1) (T u) =ᵐ[mu.restrict Omega]
          iteratedGradient (k + 1) (lowerOrder (k + 2) u) := by
  obtain ⟨V, hV⟩ := exists_iteratedGradientL_of_ae_eq S hS (k + 1)
  let T₁ := T₀.comp (lowerOrderL (mu := mu) (Omega := Omega) (p := p) (k + 2))
  have hT₁ (u : Wkp mu Omega p (k + 3)) : T₁ u = T₀ (lowerOrder (k + 2) u) := by
    rw [ContinuousLinearMap.comp_apply, lowerOrderL_apply]
  have hmk (u : Wkp mu Omega p (k + 3)) : HasWeakFDerivOn mu Omega
      (iteratedGradient k (T₁ u)) (V u) := by
    rw [hT₁]
    exact ((hasWeakFDerivOn_iteratedGradient k (lowerOrder (k + 2) u)).congr_ae
      (hT₀ _).2.symm).congr_ae_deriv (hV u).symm
  let F : Wkp mu Omega p (k + 3) → Wkp mu Omega pstar (k + 2) := fun u ↦
    mk k (T₁ u) (V u) (hmk u)
  have hF (u) : lowerOrder (k + 1) (F u) = T₁ u := lowerOrder_mk _ _ _ _
  have hG (u) : iteratedGradient (k + 1) (F u) = V u := iteratedGradient_mk _ _ _ _
  have hadd (a b : Wkp mu Omega pstar (k + 2)) :
      lowerOrder (k + 1) (a + b) = lowerOrder (k + 1) a + lowerOrder (k + 1) b := by
    simp only [← lowerOrderL_apply, map_add]
  have hsmul (c : ℝ) (a : Wkp mu Omega pstar (k + 2)) :
      lowerOrder (k + 1) (c • a) = c • lowerOrder (k + 1) a := by
    simp only [← lowerOrderL_apply, map_smul]
  let T : Wkp mu Omega p (k + 3) →ₗ[ℝ] Wkp mu Omega pstar (k + 2) :=
    { toFun := F
      map_add' := fun u v ↦ ext_lowerOrder (k + 1) (by rw [hadd, hF, hF, hF, map_add])
      map_smul' := fun c u ↦ ext_lowerOrder (k + 1) (by
        rw [hsmul, hF, hF, map_smul, RingHom.id_apply]) }
  have hcont : Continuous T := by
    refine (continuous_iff_lowerOrder_iteratedGradient (k + 1)).2 ⟨?_, ?_⟩
    · simp only [T, LinearMap.coe_mk, AddHom.coe_mk, hF]
      exact T₁.continuous
    · simp only [T, LinearMap.coe_mk, AddHom.coe_mk, hG]
      exact V.continuous
  refine ⟨⟨T, hcont⟩, fun u ↦ ⟨?_, ?_⟩⟩
  · have h := (hT₀ (lowerOrder (k + 2) u)).1
    rw [← hT₁] at h
    rw [value_succ, value_succ (k + 2) u, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk, hF]
    exact h
  · rw [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, hG]
    exact hV u

/-- **Higher-order embedding from a first-order embedding.** If `S : W^{1,p}(Ω) → L^{p⋆}(Ω)` is a
bounded linear map representing the values, then for every `k` inclusion is a continuous linear
map `W^{k+2,p}(Ω) → W^{k+1,p⋆}(Ω)`. It preserves the value and the highest weak derivative of the
target, the order-`k + 1` derivative; by uniqueness of weak derivatives it therefore preserves
every weak derivative of order at most `k + 1`. -/
theorem exists_sobolevEmbeddingL_succ_of_ae_eq
    (S : W1p mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict Omega))
    (hS : ∀ u, S u =ᵐ[mu.restrict Omega] W1p.value u) (k : ℕ) :
    ∃ T : Wkp mu Omega p (k + 2) →L[ℝ] Wkp mu Omega pstar (k + 1),
      ∀ u, value (k + 1) (T u) =ᵐ[mu.restrict Omega] value (k + 2) u ∧
        iteratedGradient k (T u) =ᵐ[mu.restrict Omega]
          iteratedGradient k (lowerOrder (k + 1) u) := by
  induction k with
  | zero => exact exists_sobolevEmbeddingL_two_of_ae_eq S hS
  | succ k ih =>
    obtain ⟨T₀, hT₀⟩ := ih
    exact exists_sobolevEmbeddingL_step_of_ae_eq S hS k T₀ hT₀

/-- **Higher-order embedding from a first-order embedding.** If `S : W^{1,p}(Ω) → L^{p⋆}(Ω)` is a
bounded linear map representing the values, then for every `k` inclusion is a continuous linear
map `W^{k+1,p}(Ω) → W^{k,p⋆}(Ω)`, preserving the value. At positive target order the highest
derivative is preserved as well (`TauCeti.Wkp.exists_sobolevEmbeddingL_succ_of_ae_eq`). -/
theorem exists_sobolevEmbeddingL_of_ae_eq
    (S : W1p mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict Omega))
    (hS : ∀ u, S u =ᵐ[mu.restrict Omega] W1p.value u) (k : ℕ) :
    ∃ T : Wkp mu Omega p (k + 1) →L[ℝ] Wkp mu Omega pstar k,
      ∀ u, value k (T u) =ᵐ[mu.restrict Omega] value (k + 1) u := by
  cases k with
  | zero =>
    refine ⟨S, fun u ↦ ?_⟩
    rw [value_zero, value_one]
    exact hS u
  | succ k =>
    obtain ⟨T, hT⟩ := exists_sobolevEmbeddingL_succ_of_ae_eq S hS k
    exact ⟨T, fun u ↦ (hT u).1⟩

end Wkp

end TauCeti
