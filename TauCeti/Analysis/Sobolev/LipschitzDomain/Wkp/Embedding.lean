/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.LipschitzDomain.SobolevEmbedding
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Higher-order Sobolev embeddings on bounded Lipschitz domains

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain of dimension `n`, let `1 ≤ p` and let `p⋆` be the
Sobolev conjugate, `1/p⋆ = 1/p - 1/n`, with `p⋆ < ∞`, that is `p < n`. Every derivative of order
at most `k` of a function in `W^{k+1,p}(Ω)` lies in `W^{1,p}(Ω)`, so by the first-order embedding
`TauCeti.W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith` it lies in `L^{p⋆}(Ω)`. Keeping
all the weak derivatives, the inclusion is therefore a continuous linear map
`W^{k+1,p}(Ω) → W^{k,p⋆}(Ω)`. Iterating, `W^{k,p}(Ω) → L^q(Ω)` for `1/q = 1/p - k/n > 0`.

The vector-valued derivative fields are embedded coordinatewise: in a basis of the
finite-dimensional field space, each coordinate is a scalar Sobolev function
(`TauCeti.WeakDerivStep.toW1pL`), to which the scalar embedding applies. The higher-order space is
then reassembled one weak derivative at a time with `TauCeti.Wkp.mk`; its continuity follows from
that of the lower-order component and the highest derivative separately.

## Main declarations

* `TauCeti.Wkp.exists_sobolevEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{k+1,p}(Ω) →L[ℝ] W^{k,p⋆}(Ω)`, which preserves the value.
* `TauCeti.Wkp.exists_sobolevEmbeddingL_succ_of_isLipschitzDomainWith`: at positive target
  order, the embedding `W^{k+2,p}(Ω) →L[ℝ] W^{k+1,p⋆}(Ω)` also preserves the highest weak
  derivative.
* `TauCeti.Wkp.exists_lpEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{k,p}(Ω) →L[ℝ] L^q(Ω)` for `1/q + k/n = 1/p`, `q < ∞`.
* `TauCeti.Wkp.exists_eLpNorm_value_le_of_isLipschitzDomainWith`: the estimate
  `‖u‖_{L^r(Ω)} ≤ C ‖u‖_{W^{k,p}(Ω)}` for `r ≤ q`.
* `TauCeti.Wkp.memLp_value_of_isLipschitzDomainWith`: every `u ∈ W^{k,p}(Ω)` lies in `L^r(Ω)`
  for `r ≤ q`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.3, Theorem 6 (i).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part I, Case B.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p pstar : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinatewise first-order embedding of a weakly differentiable vector field: the field
selected by `base` lies in `L^{p⋆}(Ω)`, continuously in the graph norm. -/
private theorem exists_lipschitzWkpEmbedding_baseL {F X : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [Fact (1 ≤ pstar)]
    (S : W1p volume Ω p →L[ℝ] Lp ℝ pstar (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))))
    (hS : ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u)
    (base : X →L[ℝ] Lp F p (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))) :
    ∃ V : WeakDerivStep volume Ω p base →L[ℝ]
        Lp F pstar (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      ∀ u, V u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        base (WeakDerivStep.prev base u) := by
  classical
  let μ := volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))
  let b := Module.finBasis ℝ F
  let ℓ := fun i ↦ (b.coord i).toContinuousLinearMap
  refine ⟨∑ i, ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL pstar μ).comp
    (S.comp (WeakDerivStep.toW1pL base (ℓ i))), fun u ↦ ?_⟩
  have hcoord : ∀ i, ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL pstar μ)
      (S (WeakDerivStep.toW1pL base (ℓ i) u)) =ᵐ[μ]
        fun x ↦ (b.coord i) (base (WeakDerivStep.prev base u) x) • b i := fun i ↦ by
    filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL
      (S (WeakDerivStep.toW1pL base (ℓ i) u)), hS (WeakDerivStep.toW1pL base (ℓ i) u),
      (ℓ i).coeFn_compLpL (base (WeakDerivStep.prev base u))] with x h1 h2 h3
    rw [h1, ContinuousLinearMap.toSpanSingleton_apply, h2, WeakDerivStep.value_toW1pL, h3]
    rfl
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
      ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL pstar μ)
        (S (WeakDerivStep.toW1pL base (ℓ i) u))),
    ae_all_iff.mpr hcoord] with x hsum hcoords
  rw [sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hsum]
  simpa only [hcoords, Module.Basis.coord_apply] using
    b.sum_repr (base (WeakDerivStep.prev base u) x)

/-- The highest derivative of the order-`k + 1` part of `u ∈ W^{k+2,p}(Ω)` lies in
`L^{p⋆}(Ω)`, continuously in `u`. -/
private theorem exists_lipschitzWkpEmbedding_iteratedGradientL [Fact (1 ≤ pstar)]
    (S : W1p volume Ω p →L[ℝ] Lp ℝ pstar (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))))
    (hS : ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u) (k : ℕ) :
    ∃ V : Wkp volume Ω p (k + 2) →L[ℝ]
        Lp (IteratedGradient (WithLp 2 (ℝ × E)) k) pstar
          (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      ∀ u, V u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) := by
  obtain ⟨V, hV⟩ := exists_lipschitzWkpEmbedding_baseL S hS
    (sobolevStage (mu := volume) (Omega := Ω) (p := p) k).iteratedGradientL
  refine ⟨V, fun u ↦ ?_⟩
  rw [Wkp.iteratedGradient_eq_sobolevStage_iteratedGradientL, Wkp.lowerOrder_succ]
  exact hV u

/-- The embedding `W^{2,p}(Ω) → W^{1,p⋆}(Ω)`, preserving the value and the gradient, built from
the first-order embedding `S`. -/
private theorem exists_lipschitzWkpEmbedding_two [Fact (1 ≤ pstar)]
    (S : W1p volume Ω p →L[ℝ] Lp ℝ pstar (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))))
    (hS : ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u) :
    ∃ T : Wkp volume Ω p 2 →L[ℝ] Wkp volume Ω pstar 1,
      ∀ u, Wkp.value 1 (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value 2 u ∧
        Wkp.iteratedGradient 0 (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) := by
  obtain ⟨V, hV⟩ := exists_lipschitzWkpEmbedding_iteratedGradientL S hS 0
  let S₁ := S.comp (Wkp.firstOrderL (mu := volume) (Omega := Ω) (p := p) 1)
  have hfirst (u : Wkp volume Ω p 2) : Wkp.firstOrderL 1 u = Wkp.lowerOrder 1 u := by
    rw [Wkp.firstOrderL_apply, Wkp.firstOrder_succ, Wkp.firstOrder_zero]
  have hS₁ (u : Wkp volume Ω p 2) : S₁ u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
      Wkp.value 2 u := by
    rw [Wkp.value_succ, Wkp.value_one, ← hfirst]
    exact hS _
  have hV' (u : Wkp volume Ω p 2) : V u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
      W1p.gradient (Wkp.firstOrderL 1 u) := by
    rw [hfirst, ← Wkp.iteratedGradient_zero]
    exact hV u
  have hmk (u : Wkp volume Ω p 2) : HasWeakFDerivOn volume Ω (S₁ u)
      (fun x ↦ innerSL ℝ (V u x)) :=
    ((W1p.hasWeakFDerivOn (Wkp.firstOrderL 1 u)).congr_ae (hS _).symm).congr_ae_deriv
      (by filter_upwards [hV' u] with x hx; rw [hx])
  let F : Wkp volume Ω p 2 → W1p volume Ω pstar := fun u ↦ W1p.mk (S₁ u) (V u) (hmk u)
  have hF (u) : W1p.value (F u) = S₁ u := W1p.value_mk _ _ _
  have hG (u) : W1p.gradient (F u) = V u := W1p.gradient_mk _ _ _
  have hadd (a b : W1p volume Ω pstar) : W1p.value (a + b) = W1p.value a + W1p.value b := by
    simp only [← W1p.valueL_apply, map_add]
  have hsmul (c : ℝ) (a : W1p volume Ω pstar) : W1p.value (c • a) = c • W1p.value a := by
    simp only [← W1p.valueL_apply, map_smul]
  let T : Wkp volume Ω p 2 →ₗ[ℝ] W1p volume Ω pstar :=
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
  · rw [Wkp.value_one]
    exact (hF u).symm ▸ hS₁ u
  · rw [Wkp.iteratedGradient_zero]
    exact (hG u).symm ▸ hV u

/-- One step of the reassembly: an embedding `W^{k+2,p}(Ω) → W^{k+1,p⋆}(Ω)` preserving the value
and the highest derivative extends to `W^{k+3,p}(Ω) → W^{k+2,p⋆}(Ω)` with the same properties. -/
private theorem exists_lipschitzWkpEmbedding_step [Fact (1 ≤ pstar)]
    (S : W1p volume Ω p →L[ℝ] Lp ℝ pstar (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))))
    (hS : ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u) (k : ℕ)
    (T₀ : Wkp volume Ω p (k + 2) →L[ℝ] Wkp volume Ω pstar (k + 1))
    (hT₀ : ∀ u, Wkp.value (k + 1) (T₀ u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (k + 2) u ∧
        Wkp.iteratedGradient k (T₀ u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u)) :
    ∃ T : Wkp volume Ω p (k + 3) →L[ℝ] Wkp volume Ω pstar (k + 2),
      ∀ u, Wkp.value (k + 2) (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (k + 3) u ∧
        Wkp.iteratedGradient (k + 1) (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.iteratedGradient (k + 1) (Wkp.lowerOrder (k + 2) u) := by
  obtain ⟨V, hV⟩ := exists_lipschitzWkpEmbedding_iteratedGradientL S hS (k + 1)
  let T₁ := T₀.comp (Wkp.lowerOrderL (mu := volume) (Omega := Ω) (p := p) (k + 2))
  have hT₁ (u : Wkp volume Ω p (k + 3)) : T₁ u = T₀ (Wkp.lowerOrder (k + 2) u) := by
    rw [ContinuousLinearMap.comp_apply, Wkp.lowerOrderL_apply]
  have hmk (u : Wkp volume Ω p (k + 3)) : HasWeakFDerivOn volume Ω
      (Wkp.iteratedGradient k (T₁ u)) (V u) := by
    rw [hT₁]
    exact ((Wkp.hasWeakFDerivOn_iteratedGradient k (Wkp.lowerOrder (k + 2) u)).congr_ae
      (hT₀ _).2.symm).congr_ae_deriv (hV u).symm
  let F : Wkp volume Ω p (k + 3) → Wkp volume Ω pstar (k + 2) := fun u ↦
    Wkp.mk k (T₁ u) (V u) (hmk u)
  have hF (u) : Wkp.lowerOrder (k + 1) (F u) = T₁ u := Wkp.lowerOrder_mk _ _ _ _
  have hG (u) : Wkp.iteratedGradient (k + 1) (F u) = V u := Wkp.iteratedGradient_mk _ _ _ _
  have hadd (a b : Wkp volume Ω pstar (k + 2)) :
      Wkp.lowerOrder (k + 1) (a + b) = Wkp.lowerOrder (k + 1) a + Wkp.lowerOrder (k + 1) b := by
    simp only [← Wkp.lowerOrderL_apply, map_add]
  have hsmul (c : ℝ) (a : Wkp volume Ω pstar (k + 2)) :
      Wkp.lowerOrder (k + 1) (c • a) = c • Wkp.lowerOrder (k + 1) a := by
    simp only [← Wkp.lowerOrderL_apply, map_smul]
  let T : Wkp volume Ω p (k + 3) →ₗ[ℝ] Wkp volume Ω pstar (k + 2) :=
    { toFun := F
      map_add' := fun u v ↦ Wkp.ext_lowerOrder (k + 1) (by rw [hadd, hF, hF, hF, map_add])
      map_smul' := fun c u ↦ Wkp.ext_lowerOrder (k + 1) (by
        rw [hsmul, hF, hF, map_smul, RingHom.id_apply]) }
  have hcont : Continuous T := by
    refine (Wkp.continuous_iff_lowerOrder_iteratedGradient (k + 1)).2 ⟨?_, ?_⟩
    · simp only [T, LinearMap.coe_mk, AddHom.coe_mk, hF]
      exact T₁.continuous
    · simp only [T, LinearMap.coe_mk, AddHom.coe_mk, hG]
      exact V.continuous
  refine ⟨⟨T, hcont⟩, fun u ↦ ⟨?_, ?_⟩⟩
  · have h := (hT₀ (Wkp.lowerOrder (k + 2) u)).1
    rw [← hT₁] at h
    rw [Wkp.value_succ, Wkp.value_succ (k + 2) u]
    change Wkp.value (k + 1) (Wkp.lowerOrder (k + 1) (F u)) =ᵐ[_] _
    rw [hF]
    exact h
  · exact (hG u).symm ▸ hV u

/-- The embedding `W^{k+2,p}(Ω) → W^{k+1,p⋆}(Ω)`, with the value and the highest derivative
preserved, built one derivative at a time from the first-order embedding `S`. -/
private theorem exists_lipschitzWkpEmbedding_succ [Fact (1 ≤ pstar)]
    (S : W1p volume Ω p →L[ℝ] Lp ℝ pstar (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))))
    (hS : ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u) (k : ℕ) :
    ∃ T : Wkp volume Ω p (k + 2) →L[ℝ] Wkp volume Ω pstar (k + 1),
      ∀ u, Wkp.value (k + 1) (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (k + 2) u ∧
        Wkp.iteratedGradient k (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) := by
  induction k with
  | zero => exact exists_lipschitzWkpEmbedding_two S hS
  | succ k ih =>
    obtain ⟨T₀, hT₀⟩ := ih
    exact exists_lipschitzWkpEmbedding_step S hS k T₀ hT₀

/-- **Higher-order Sobolev embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then for every
`k` inclusion is a continuous linear map `W^{k+2,p}(Ω) → W^{k+1,p⋆}(Ω)`. It preserves the value
and the highest weak derivative of the target, the order-`k + 1` derivative; by uniqueness of weak
derivatives it therefore preserves every weak derivative of order at most `k + 1`. -/
theorem Wkp.exists_sobolevEmbeddingL_succ_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (k : ℕ) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : Wkp volume Ω p (k + 2) →L[ℝ] Wkp volume Ω pstar (k + 1),
      ∀ u, Wkp.value (k + 1) (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (k + 2) u ∧
        Wkp.iteratedGradient k (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hpstar hexp hΩ hb
  exact exists_lipschitzWkpEmbedding_succ S hS k

/-- **Higher-order Sobolev embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then for every
`k` inclusion is a continuous linear map `W^{k+1,p}(Ω) → W^{k,p⋆}(Ω)`, preserving the value.
At positive target order the highest derivative is preserved as well
(`TauCeti.Wkp.exists_sobolevEmbeddingL_succ_of_isLipschitzDomainWith`). -/
theorem Wkp.exists_sobolevEmbeddingL_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (k : ℕ) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] Wkp volume Ω pstar k,
      ∀ u, Wkp.value k (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        Wkp.value (k + 1) u := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  cases k with
  | zero =>
    obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hpstar hexp hΩ hb
    refine ⟨S, fun u ↦ ?_⟩
    rw [Wkp.value_zero, Wkp.value_one]
    exact hS u
  | succ k =>
    obtain ⟨T, hT⟩ := Wkp.exists_sobolevEmbeddingL_succ_of_isLipschitzDomainWith hpstar hexp hΩ hb k
    exact ⟨T, fun u ↦ (hT u).1⟩

/-- Iteration of the one-step embedding down to `L^q(Ω)`, with `1/q + k/n = 1/p`. -/
private theorem exists_lipschitzWkpLpEmbedding
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∀ (k : ℕ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], q ≠ ∞ →
      q⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹ →
      ∃ T : Wkp volume Ω p k →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
        ∀ u, T u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] Wkp.value k u
  | 0, p, q, _, _, _, hexp => by
    obtain rfl : q = p := by simpa using hexp
    exact ⟨ContinuousLinearMap.id ℝ _, fun u ↦ by simp⟩
  | k + 1, p, q, _, _, hq, hexp => by
    set n : ℝ≥0∞ := (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)
    set r : ℝ≥0∞ := (q⁻¹ + k * n⁻¹)⁻¹
    have hrinv : r⁻¹ = q⁻¹ + k * n⁻¹ := inv_inv _
    have hrexp : r⁻¹ + n⁻¹ = p⁻¹ := by
      rw [hrinv, ← hexp]
      push_cast
      ring
    have hr : r ≠ ∞ := by
      rw [← ENNReal.inv_ne_zero, hrinv]
      exact (add_pos_of_pos_of_nonneg (ENNReal.inv_pos.2 hq) zero_le).ne'
    have : Fact (1 ≤ r) := ⟨one_le_of_inv_add_eq_inv hrexp⟩
    obtain ⟨S, hS⟩ := Wkp.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hr hrexp hΩ hb k
    obtain ⟨T, hT⟩ := exists_lipschitzWkpLpEmbedding hΩ hb k (p := r) (q := q) hq hrinv.symm
    exact ⟨T.comp S, fun u ↦ (hT (S u)).trans (hS u)⟩

/-- **Higher-order Sobolev embedding into Lebesgue spaces on bounded Lipschitz domains.** If
`Ω ⊆ ℝ × E` is a bounded Lipschitz domain of dimension `n`, `1 ≤ p`, and
`1/q + k/n = 1/p` with `q < ∞`, that is `kp < n`, then inclusion is a continuous linear map
`W^{k,p}(Ω) → L^q(Ω)`. -/
theorem Wkp.exists_lpEmbeddingL_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hexp : q⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : Wkp volume Ω p k →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      ∀ u, T u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] Wkp.value k u :=
  letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  exists_lipschitzWkpLpEmbedding hΩ hb k hq hexp

/-- **The higher-order Sobolev inequality on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a
bounded Lipschitz domain of dimension `n`, `1 ≤ p`, and `1/q + k/n = 1/p` with `q < ∞`, then for
every `r ≤ q` there is a constant `C` with `‖u‖_{L^r(Ω)} ≤ C ‖u‖_{W^{k,p}(Ω)}`. -/
theorem Wkp.exists_eLpNorm_value_le_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hexp : q⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {r : ℝ≥0∞} (hr : r ≤ q) :
    ∃ C : ℝ≥0, ∀ u : Wkp volume Ω p k,
      eLpNorm (Wkp.value k u) r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) ≤ C * ‖u‖ₑ := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨T, hT⟩ := Wkp.exists_lpEmbeddingL_of_isLipschitzDomainWith k hq hexp hΩ hb
  have hμ : volume.restrict (Ω : Set (WithLp 2 (ℝ × E))) univ ≠ ∞ := by
    rw [Measure.restrict_apply_univ]
    exact hb.measure_lt_top.ne
  set M : ℝ≥0∞ := volume.restrict (Ω : Set (WithLp 2 (ℝ × E))) univ ^
    (1 / r.toReal - 1 / q.toReal)
  refine ⟨‖T‖₊ * M.toNNReal, fun u ↦ ?_⟩
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [eLpNorm_exponent_zero (Lp.aestronglyMeasurable _)]
    exact zero_le
  have he : 0 ≤ 1 / r.toReal - 1 / q.toReal := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (ENNReal.toReal_pos hr0 (ne_top_of_le_ne_top hq hr))
      (ENNReal.toReal_mono hq hr)
  have hM : M ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg he hμ
  have hTu : ‖T u‖ₑ ≤ ‖T‖₊ * ‖u‖ₑ := by
    simp only [enorm_eq_nnnorm]
    exact_mod_cast T.le_opNNNorm u
  calc eLpNorm (Wkp.value k u) r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))
        = eLpNorm (T u) r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
          eLpNorm_congr_ae (hT u).symm
    _ ≤ eLpNorm (T u) q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) * M :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hr (Lp.aestronglyMeasurable _)
    _ = ‖T u‖ₑ * M := by rw [Lp.enorm_def]
    _ ≤ ‖T‖₊ * ‖u‖ₑ * M := by gcongr
    _ = ↑(‖T‖₊ * M.toNNReal) * ‖u‖ₑ := by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hM]
      ring

/-- **Integrability on bounded Lipschitz domains at higher order.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, every `u ∈ W^{k,p}(Ω)` lies in `L^r(Ω)` for every `r ≤ q`,
where `1/q + k/n = 1/p` and `q < ∞`. -/
theorem Wkp.memLp_value_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hexp : q⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {r : ℝ≥0∞} (hr : r ≤ q)
    (u : Wkp volume Ω p k) :
    MemLp (Wkp.value k u) r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) := by
  obtain ⟨C, hC⟩ := Wkp.exists_eLpNorm_value_le_of_isLipschitzDomainWith k hq hexp hΩ hb hr
  have hfin : C * ‖u‖ₑ < ∞ := by finiteness
  exact (hC u).trans_lt hfin

end TauCeti

end
