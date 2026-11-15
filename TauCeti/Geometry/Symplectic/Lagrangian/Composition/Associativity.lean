/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Associativity
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Composition

/-!
# Associativity of transverse composition of Lagrangian correspondences

Let `f₁ : L₁ → M₁ × M₂`, `f₂ : L₂ → M₂ × M₃` and `f₃ : L₃ → M₃ × M₄` be Lagrangian immersions for
the twisted products `pr₁*σᵢ - pr₂*σᵢ₊₁`. There are two ways to compose them.

* **Left grouping.** If `x ↦ (f₁ x).2` and `y ↦ (f₂ y).1` are transverse, the composite of `f₁`
  and `f₂` is a Lagrangian immersion of the transverse fibre product `L₁ ×_{M₂} L₂`
  (`IsLagrangianImmersion.relComp_transverseFiberProduct`). If its second component
  `(x, y) ↦ (f₂ y).2` is transverse to `z ↦ (f₃ z).1`, composing again with `f₃` gives a
  Lagrangian immersion of `(L₁ ×_{M₂} L₂) ×_{M₃} L₃`.
* **Right grouping.** Symmetrically, if `y ↦ (f₂ y).2` and `z ↦ (f₃ z).1` are transverse and
  `x ↦ (f₁ x).2` is transverse to `(y, z) ↦ (f₂ y).1`, composing `f₁` with the composite of `f₂`
  and `f₃` gives a Lagrangian immersion of `L₁ ×_{M₂} (L₂ ×_{M₃} L₃)`.

Both triple composites send a matching triple `(x, y, z)` to `((f₁ x).1, (f₃ z).2)`. When both
first steps are transverse, the second step of one grouping is transverse exactly when that of
the other is (`TauCeti.transverse_comp_snd_transverseFiberProduct_iff`). So the hypotheses of the
left grouping already make the right grouping a transverse composition of Lagrangian immersions
(`IsLagrangianImmersion.relComp_relComp_transverseFiberProduct`). The smooth associator
`TauCeti.fiberProductAssocDiffeomorph` of the two iterated fibre products carries the left triple
composite to the right one, so one of them is a Lagrangian correspondence `M₁ ⇝ M₄` exactly when
the other is
(`IsLagrangianImmersion.isLagrangianEmbedding_relComp_assoc_transverseFiberProduct_iff`). This is
the associativity of transverse composition of Lagrangian correspondences, for compositions all of
whose intermediate fibre products are transverse; arbitrary correspondences have no associative
composition.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `IsLagrangianImmersion.relComp_relComp_transverseFiberProduct`: under the transversality
  hypotheses of the left grouping, the right triple composite is a Lagrangian immersion.
* `IsLagrangianImmersion.isLagrangianEmbedding_relComp_assoc_transverseFiberProduct_iff`: the left
  triple composite is a Lagrangian correspondence exactly when the right one is.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278 (composition
  of canonical relations is associative when the compositions involved are transverse).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ E₄ H₄ M₄ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃} [I₃.Boundaryless]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
  [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [FiniteDimensional ℝ E₄]
  [TopologicalSpace H₄] {I₄ : ModelWithCorners ℝ E₄ H₄} [I₄.Boundaryless]
  [TopologicalSpace M₄] [ChartedSpace H₄ M₄] [IsManifold I₄ ∞ M₄]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {σ₄ : SmoothTwoForm I₄ M₄} {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate}
  {hσ₃ : σ₃.IsNondegenerate} {hσ₄ : σ₄.IsNondegenerate}

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ EL₃ HL₃ L₃ : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [FiniteDimensional ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [K₁.Boundaryless] [TopologicalSpace L₁]
  [ChartedSpace HL₁ L₁] [IsManifold K₁ ∞ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [FiniteDimensional ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [K₂.Boundaryless] [TopologicalSpace L₂]
  [ChartedSpace HL₂ L₂] [IsManifold K₂ ∞ L₂]
  [NormedAddCommGroup EL₃] [NormedSpace ℝ EL₃] [FiniteDimensional ℝ EL₃] [TopologicalSpace HL₃]
  {K₃ : ModelWithCorners ℝ EL₃ HL₃} [K₃.Boundaryless] [TopologicalSpace L₃]
  [ChartedSpace HL₃ L₃] [IsManifold K₃ ∞ L₃]
  {f₁ : L₁ → M₁ × M₂} {f₂ : L₂ → M₂ × M₃} {f₃ : L₃ → M₃ × M₄}

/-- The model of `L₁ ×_{M₂} L₂`. -/
local notation "KF₁₂" => 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)

/-- The model of `L₂ ×_{M₃} L₃`. -/
local notation "KF₂₃" => 𝓘(ℝ, Fin (finrank ℝ EL₂ + finrank ℝ EL₃ - finrank ℝ E₃) → ℝ)

/-- The model of `(L₁ ×_{M₂} L₂) ×_{M₃} L₃`. -/
local notation "KFL" => 𝓘(ℝ, Fin (finrank ℝ (Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
  + finrank ℝ EL₃ - finrank ℝ E₃) → ℝ)

/-- The model of `L₁ ×_{M₂} (L₂ ×_{M₃} L₃)`. -/
local notation "KFR" => 𝓘(ℝ, Fin (finrank ℝ EL₁ +
  finrank ℝ (Fin (finrank ℝ EL₂ + finrank ℝ EL₃ - finrank ℝ E₃) → ℝ) - finrank ℝ E₂) → ℝ)

variable (h₁₂ : ∀ p : L₁ × L₂, (f₁ p.1).2 = (f₂ p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f₁ x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (f₂ p.2).1 (f₁ p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (f₂ y).1) p.2)).range = ⊤)
  (h₂₃ : ∀ p : L₂ × L₃, (f₂ p.1).2 = (f₃ p.2).1 →
    (mfderiv K₂ I₃ (fun y ↦ (f₂ y).2) p.1).range ⊔
      (((tangentSpaceCast I₃ (f₃ p.2).1 (f₂ p.1).2).toContinuousLinearMap).comp
        (mfderiv K₃ I₃ (fun z ↦ (f₃ z).1) p.2)).range = ⊤)

/-- **Transverse composition of Lagrangian correspondences, regrouped.** Let `f₁`, `f₂` and `f₃`
be Lagrangian immersions, with `f₁, f₂` transverse over `M₂` and `f₂, f₃` transverse over `M₃`.
If the left grouping `(f₁ ∘ f₂) ∘ f₃` is transverse at its second step, so is the right grouping
`f₁ ∘ (f₂ ∘ f₃)`, and the right triple composite `(x, (y, z)) ↦ ((f₁ x).1, (f₃ z).2)` on
`L₁ ×_{M₂} (L₂ ×_{M₃} L₃)` is a Lagrangian immersion for `pr₁*σ₁ - pr₂*σ₄`. -/
theorem IsLagrangianImmersion.relComp_relComp_transverseFiberProduct
    (hf₁ : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f₁)
    (hf₂ : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ f₂)
    (hf₃ : (hσ₃.twistedProd hσ₄).IsLagrangianImmersion K₃ f₃)
    (hL : letI := (transverseFiberProductChartedSpace (n := ∞) (by simp)
        hf₁.isImmersion.contMDiff.snd hf₂.isImmersion.contMDiff.fst h₁₂);
      ∀ p : {q : L₁ × L₂ // (f₁ q.1).2 = (f₂ q.2).1} × L₃, (f₂ p.1.1.2).2 = (f₃ p.2).1 →
        (mfderiv KF₁₂ I₃ (fun q : {q : L₁ × L₂ // (f₁ q.1).2 = (f₂ q.2).1} ↦ (f₂ q.1.2).2)
            p.1).range ⊔
          (((tangentSpaceCast I₃ (f₃ p.2).1 (f₂ p.1.1.2).2).toContinuousLinearMap).comp
            (mfderiv K₃ I₃ (fun z ↦ (f₃ z).1) p.2)).range = ⊤) :
    letI := transverseFiberProductChartedSpace (n := ∞) (by simp)
      hf₂.isImmersion.contMDiff.snd hf₃.isImmersion.contMDiff.fst h₂₃;
    haveI := isManifold_transverseFiberProduct (n := ∞) (by simp)
      hf₂.isImmersion.contMDiff.snd hf₃.isImmersion.contMDiff.fst h₂₃;
    letI := transverseFiberProductChartedSpace (n := ∞) (by simp) hf₁.isImmersion.contMDiff.snd
      (ContMDiff.fst (contMDiff_relComp_transverseFiberProduct hf₂.isImmersion.contMDiff
        hf₃.isImmersion.contMDiff h₂₃))
      ((transverse_comp_snd_transverseFiberProduct_iff (by simp) hf₁.isImmersion.contMDiff.snd
        hf₂.isImmersion.contMDiff.fst h₁₂ hf₂.isImmersion.contMDiff.snd
        hf₃.isImmersion.contMDiff.fst h₂₃).1 hL);
    (hσ₁.twistedProd hσ₄).IsLagrangianImmersion KFR
      (fun p : {p : L₁ × {q : L₂ × L₃ // (f₂ q.1).2 = (f₃ q.2).1} //
        (f₁ p.1).2 = (f₂ p.2.1.1).1} ↦ ((f₁ p.1.1).1, (f₃ p.1.2.1.2).2)) := by
  let := transverseFiberProductChartedSpace (n := ∞) (by simp)
    hf₂.isImmersion.contMDiff.snd hf₃.isImmersion.contMDiff.fst h₂₃
  have := isManifold_transverseFiberProduct (n := ∞) (by simp)
    hf₂.isImmersion.contMDiff.snd hf₃.isImmersion.contMDiff.fst h₂₃
  exact IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
    (hσ₃ := hσ₄) _ hf₁ (IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₂)
      (hσ₂ := hσ₃) (hσ₃ := hσ₄) h₂₃ hf₂ hf₃)

/-- **Associativity of transverse composition of Lagrangian correspondences.** Let `f₁`, `f₂` and
`f₃` be Lagrangian immersions, with `f₁, f₂` transverse over `M₂`, `f₂, f₃` transverse over `M₃`,
and the left grouping `(f₁ ∘ f₂) ∘ f₃` transverse at its second step, so that the right grouping
is transverse as well. Then the left triple composite `((x, y), z) ↦ ((f₁ x).1, (f₃ z).2)` on
`(L₁ ×_{M₂} L₂) ×_{M₃} L₃` is a Lagrangian correspondence `M₁ ⇝ M₄` exactly when the right triple
composite `(x, (y, z)) ↦ ((f₁ x).1, (f₃ z).2)` on `L₁ ×_{M₂} (L₂ ×_{M₃} L₃)` is. Both composites
are Lagrangian immersions, and the associator `TauCeti.fiberProductAssocDiffeomorph` of the two
iterated fibre products carries the left one to the right one, so this compares their topological
embeddedness. -/
theorem IsLagrangianImmersion.isLagrangianEmbedding_relComp_assoc_transverseFiberProduct_iff
    (hf₁ : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f₁)
    (hf₂ : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ f₂)
    (hf₃ : (hσ₃.twistedProd hσ₄).IsLagrangianImmersion K₃ f₃)
    (hL : letI := (transverseFiberProductChartedSpace (n := ∞) (by simp)
        hf₁.isImmersion.contMDiff.snd hf₂.isImmersion.contMDiff.fst h₁₂);
      ∀ p : {q : L₁ × L₂ // (f₁ q.1).2 = (f₂ q.2).1} × L₃, (f₂ p.1.1.2).2 = (f₃ p.2).1 →
        (mfderiv KF₁₂ I₃ (fun q : {q : L₁ × L₂ // (f₁ q.1).2 = (f₂ q.2).1} ↦ (f₂ q.1.2).2)
            p.1).range ⊔
          (((tangentSpaceCast I₃ (f₃ p.2).1 (f₂ p.1.1.2).2).toContinuousLinearMap).comp
            (mfderiv K₃ I₃ (fun z ↦ (f₃ z).1) p.2)).range = ⊤) :
    (letI := transverseFiberProductChartedSpace (n := ∞) (by simp)
        hf₁.isImmersion.contMDiff.snd hf₂.isImmersion.contMDiff.fst h₁₂;
      haveI := isManifold_transverseFiberProduct (n := ∞) (by simp)
        hf₁.isImmersion.contMDiff.snd hf₂.isImmersion.contMDiff.fst h₁₂;
      letI := transverseFiberProductChartedSpace (n := ∞) (by simp)
        (ContMDiff.snd (contMDiff_relComp_transverseFiberProduct hf₁.isImmersion.contMDiff
          hf₂.isImmersion.contMDiff h₁₂)) hf₃.isImmersion.contMDiff.fst hL;
      (hσ₁.twistedProd hσ₄).IsLagrangianEmbedding KFL
        (fun p : {p : {q : L₁ × L₂ // (f₁ q.1).2 = (f₂ q.2).1} × L₃ //
          (f₂ p.1.1.2).2 = (f₃ p.2).1} ↦ ((f₁ p.1.1.1.1).1, (f₃ p.1.2).2))) ↔
    (letI := transverseFiberProductChartedSpace (n := ∞) (by simp)
        hf₂.isImmersion.contMDiff.snd hf₃.isImmersion.contMDiff.fst h₂₃;
      haveI := isManifold_transverseFiberProduct (n := ∞) (by simp)
        hf₂.isImmersion.contMDiff.snd hf₃.isImmersion.contMDiff.fst h₂₃;
      letI := transverseFiberProductChartedSpace (n := ∞) (by simp)
        hf₁.isImmersion.contMDiff.snd
        (ContMDiff.fst (contMDiff_relComp_transverseFiberProduct hf₂.isImmersion.contMDiff
          hf₃.isImmersion.contMDiff h₂₃))
        ((transverse_comp_snd_transverseFiberProduct_iff (by simp) hf₁.isImmersion.contMDiff.snd
          hf₂.isImmersion.contMDiff.fst h₁₂ hf₂.isImmersion.contMDiff.snd
          hf₃.isImmersion.contMDiff.fst h₂₃).1 hL);
      (hσ₁.twistedProd hσ₄).IsLagrangianEmbedding KFR
        (fun p : {p : L₁ × {q : L₂ × L₃ // (f₂ q.1).2 = (f₃ q.2).1} //
          (f₁ p.1).2 = (f₂ p.2.1.1).1} ↦ ((f₁ p.1.1).1, (f₃ p.1.2.1.2).2))) := by
  have h₁ := hf₁.isImmersion.contMDiff
  have h₂ := hf₂.isImmersion.contMDiff
  have h₃ := hf₃.isImmersion.contMDiff
  have hR := (transverse_comp_snd_transverseFiberProduct_iff (by simp) h₁.snd h₂.fst h₁₂ h₂.snd
    h₃.fst h₂₃).1 hL
  let := transverseFiberProductChartedSpace (n := ∞) (by simp) h₁.snd h₂.fst h₁₂
  have := isManifold_transverseFiberProduct (n := ∞) (by simp) h₁.snd h₂.fst h₁₂
  let := transverseFiberProductChartedSpace (n := ∞) (by simp) h₂.snd h₃.fst h₂₃
  have := isManifold_transverseFiberProduct (n := ∞) (by simp) h₂.snd h₃.fst h₂₃
  have hc₁₂ := ContMDiff.snd (contMDiff_relComp_transverseFiberProduct h₁ h₂ h₁₂)
  have hc₂₃ := ContMDiff.fst (contMDiff_relComp_transverseFiberProduct h₂ h₃ h₂₃)
  let := transverseFiberProductChartedSpace (n := ∞) (by simp) hc₁₂ h₃.fst hL
  let := transverseFiberProductChartedSpace (n := ∞) (by simp) h₁.snd hc₂₃ hR
  -- Both triple composites are Lagrangian immersions, so each is a Lagrangian embedding exactly
  -- when it is a topological embedding.
  refine (IsLagrangianImmersion.isLagrangianEmbedding_relComp_transverseFiberProduct_iff
    (hσ₁ := hσ₁) (hσ₂ := hσ₃) (hσ₃ := hσ₄) hL
    (IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
      (hσ₃ := hσ₃) h₁₂ hf₁ hf₂) hf₃).trans
    (Iff.trans ?_ (IsLagrangianImmersion.isLagrangianEmbedding_relComp_transverseFiberProduct_iff
      (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₄) hR hf₁
      (IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₂) (hσ₂ := hσ₃)
        (hσ₃ := hσ₄) h₂₃ hf₂ hf₃)).symm)
  -- The left composite is the right one precomposed with the associator.
  have e₁₂ := isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp) h₁.snd h₂.fst h₁₂
  have e₂₃ := isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp) h₂.snd h₃.fst h₂₃
  have eL := isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp) hc₁₂ h₃.fst hL
  have eR := isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp) h₁.snd hc₂₃ hR
  let Φ := fiberProductAssocDiffeomorph (𝕜 := ℝ) (f := fun x ↦ (f₁ x).2) (g := fun y ↦ (f₂ y).1)
    (h := fun y ↦ (f₂ y).2) (k := fun z ↦ (f₃ z).1) e₁₂ e₂₃ eL eR
  convert Φ.toHomeomorph.isEmbedding_comp_iff (f := fun p : {p : L₁ × {q : L₂ × L₃ //
    (f₂ q.1).2 = (f₃ q.2).1} // (f₁ p.1).2 = (f₂ p.2.1.1).1} ↦ ((f₁ p.1.1).1, (f₃ p.1.2.1.2).2))
    using 2
  funext p
  simp [Φ]

end TauCeti.SmoothTwoForm.IsNondegenerate
