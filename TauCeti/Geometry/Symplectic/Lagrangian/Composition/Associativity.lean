/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Associativity
public import TauCeti.Geometry.Manifold.FiberProduct.Iterated
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Composition

/-!
# Associativity of transverse composition of Lagrangian correspondences

Let `f : L₁ → M₁ × M₂`, `g : L₂ → M₂ × M₃` and `k : L₃ → M₃ × M₄` be smooth Lagrangian maps for
the twisted products `pr₁*σᵢ - pr₂*σᵢ₊₁`, and suppose that both consecutive compositions are
transverse: `x ↦ (f x).2` is transverse to `y ↦ (g y).1`, and `y ↦ (g y).2` is transverse to
`z ↦ (k z).1`. The composite of the three correspondences can be formed in two ways.

* **Left grouping.** The transverse composite of `f` and `g` is the Lagrangian map
  `(x, y) ↦ ((f x).1, (g y).2)` on the fibre-product manifold `L₁ ×_{M₂} L₂`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.relComp_transverseFiberProduct`).
  Composing it with `k` needs `(x, y) ↦ (g y).2` on `L₁ ×_{M₂} L₂` to be transverse to
  `z ↦ (k z).1`, and gives `((x, y), z) ↦ ((f x).1, (k z).2)` on `(L₁ ×_{M₂} L₂) ×_{M₃} L₃`.
* **Right grouping.** Composing `f` with the transverse composite of `g` and `k` needs
  `x ↦ (f x).2` to be transverse to `(y, z) ↦ (g y).1` on `L₂ ×_{M₃} L₃`, and gives
  `(x, (y, z)) ↦ ((f x).1, (k z).2)` on `L₁ ×_{M₂} (L₂ ×_{M₃} L₃)`.

The outer transversality conditions of the two groupings are equivalent
(`TauCeti.transverse_fiberProduct_assoc_iff`). So whenever the left grouping is defined by
transverse compositions, so is the right one, and its composite is again a Lagrangian map
(`IsLagrangianMap.relComp_assoc_transverseFiberProduct`), a Lagrangian immersion when `f`, `g`
and `k` are (`IsLagrangianImmersion.relComp_assoc_transverseFiberProduct`). The two composites
are the same correspondence: the associator `TauCeti.fiberProductAssocDiffeomorph` of the iterated
fibre-product manifolds carries one parametrization to the other. In particular the left
composite is a Lagrangian correspondence `M₁ ⇝ M₄` exactly when the right one is
(`IsLagrangianImmersion.isLagrangianEmbedding_relComp_assoc_transverseFiberProduct_iff`).

All results are in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278
  (composition of canonical relations).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ E₄ H₄ M₄ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃} [I₃.Boundaryless]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
  [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [FiniteDimensional ℝ E₄]
  [TopologicalSpace H₄] {I₄ : ModelWithCorners ℝ E₄ H₄}
  [TopologicalSpace M₄] [ChartedSpace H₄ M₄] [IsManifold I₄ ∞ M₄]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {σ₄ : SmoothTwoForm I₄ M₄}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}
  {hσ₄ : σ₄.IsNondegenerate}

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
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃} {k : L₃ → M₃ × M₄}

/-- The model of the transverse fibre product `L₁ ×_{M₂} L₂`. -/
local notation "K₁₂" => 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)

/-- The model of the transverse fibre product `L₂ ×_{M₃} L₃`. -/
local notation "K₂₃" => 𝓘(ℝ, Fin (finrank ℝ EL₂ + finrank ℝ EL₃ - finrank ℝ E₃) → ℝ)

/-- The model of the iterated transverse fibre product `(L₁ ×_{M₂} L₂) ×_{M₃} L₃`. -/
local notation "KL" => 𝓘(ℝ, Fin (finrank ℝ (Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
  + finrank ℝ EL₃ - finrank ℝ E₃) → ℝ)

/-- The model of the iterated transverse fibre product `L₁ ×_{M₂} (L₂ ×_{M₃} L₃)`. -/
local notation "KR" => 𝓘(ℝ, Fin (finrank ℝ EL₁
  + finrank ℝ (Fin (finrank ℝ EL₂ + finrank ℝ EL₃ - finrank ℝ E₃) → ℝ) - finrank ℝ E₂) → ℝ)

variable (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
  (hk : ContMDiff K₃ (I₃.prod I₄) ∞ k)

variable
  (h₁₂ : ∀ p : L₁ × L₂, (f p.1).2 = (g p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (g p.2).1 (f p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) p.2)).range = ⊤)
  (h₂₃ : ∀ p : L₂ × L₃, (g p.1).2 = (k p.2).1 →
    (mfderiv K₂ I₃ (fun y ↦ (g y).2) p.1).range ⊔
      (((tangentSpaceCast I₃ (k p.2).1 (g p.1).2).toContinuousLinearMap).comp
        (mfderiv K₃ I₃ (fun z ↦ (k z).1) p.2)).range = ⊤)

section Smooth

include hf hg hk h₁₂ h₂₃

/-- **Associativity of transverse composition of Lagrangian correspondences.** Let
`f : L₁ → M₁ × M₂`, `g : L₂ → M₂ × M₃` and `k : L₃ → M₃ × M₄` be smooth Lagrangian maps for the
twisted products, such that both consecutive compositions are transverse and the composite of
`f` and `g` is transverse to `k`. Then the composite of `f` with the transverse composite of `g`
and `k` is again transverse, and on the fibre-product manifold `L₁ ×_{M₂} (L₂ ×_{M₃} L₃)` the map
`(x, (y, z)) ↦ ((f x).1, (k z).2)` is a Lagrangian map for `pr₁*σ₁ - pr₂*σ₄`. -/
theorem IsLagrangianMap.relComp_assoc_transverseFiberProduct
    (hL : letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst h₁₂
      ∀ p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} × L₃, (g p.1.val.2).2 = (k p.2).1 →
        (mfderiv K₁₂ I₃ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ (g q.val.2).2)
          p.1).range ⊔
        (((tangentSpaceCast I₃ (k p.2).1 (g p.1.val.2).2).toContinuousLinearMap).comp
          (mfderiv K₃ I₃ (fun z ↦ (k z).1) p.2)).range = ⊤)
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hkL : (hσ₃.twistedProd hσ₄).IsLagrangianMap K₃ k) :
    letI := transverseFiberProductChartedSpace (by simp) hg.snd hk.fst h₂₃
    haveI := isManifold_transverseFiberProduct (by simp) hg.snd hk.fst h₂₃
    letI := transverseFiberProductChartedSpace (by simp) hf.snd
      (contMDiff_relComp_transverseFiberProduct hg hk h₂₃).fst
      ((transverse_fiberProduct_assoc_iff (by simp) hf.snd hg.fst hg.snd hk.fst h₁₂ h₂₃).1 hL)
    (hσ₁.twistedProd hσ₄).IsLagrangianMap KR
      (fun p : {p : L₁ × {q : L₂ × L₃ // (g q.1).2 = (k q.2).1} // (f p.1).2 = (g p.2.val.1).1} ↦
        ((f p.val.1).1, (k p.val.2.val.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hg.snd hk.fst h₂₃
  have := isManifold_transverseFiberProduct (by simp) hg.snd hk.fst h₂₃
  exact IsLagrangianMap.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₄) hf
    (contMDiff_relComp_transverseFiberProduct hg hk h₂₃)
    ((transverse_fiberProduct_assoc_iff (by simp) hf.snd hg.fst hg.snd hk.fst h₁₂ h₂₃).1 hL) hfL
    (IsLagrangianMap.relComp_transverseFiberProduct (hσ₁ := hσ₂) (hσ₂ := hσ₃) (hσ₃ := hσ₄) hg hk
      h₂₃ hgL hkL)

end Smooth

section Immersion

variable [I₁.Boundaryless] [I₄.Boundaryless]

include h₁₂ h₂₃

/-- **Associativity of transverse composition of Lagrangian immersions.** Under the hypotheses of
`IsLagrangianMap.relComp_assoc_transverseFiberProduct`, if `f`, `g` and `k` are Lagrangian
immersions, then on the fibre-product manifold `L₁ ×_{M₂} (L₂ ×_{M₃} L₃)` the map
`(x, (y, z)) ↦ ((f x).1, (k z).2)` is a Lagrangian immersion for `pr₁*σ₁ - pr₂*σ₄`. -/
theorem IsLagrangianImmersion.relComp_assoc_transverseFiberProduct
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ g)
    (hkL : (hσ₃.twistedProd hσ₄).IsLagrangianImmersion K₃ k)
    (hL :
      letI := transverseFiberProductChartedSpace (by simp)
        hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst h₁₂
      ∀ p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} × L₃, (g p.1.val.2).2 = (k p.2).1 →
        (mfderiv K₁₂ I₃ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ (g q.val.2).2)
          p.1).range ⊔
        (((tangentSpaceCast I₃ (k p.2).1 (g p.1.val.2).2).toContinuousLinearMap).comp
          (mfderiv K₃ I₃ (fun z ↦ (k z).1) p.2)).range = ⊤) :
    letI := transverseFiberProductChartedSpace (by simp)
      hgL.isImmersion.contMDiff.snd hkL.isImmersion.contMDiff.fst h₂₃
    haveI := isManifold_transverseFiberProduct (by simp)
      hgL.isImmersion.contMDiff.snd hkL.isImmersion.contMDiff.fst h₂₃
    letI := transverseFiberProductChartedSpace (by simp) hfL.isImmersion.contMDiff.snd
      (contMDiff_relComp_transverseFiberProduct hgL.isImmersion.contMDiff
        hkL.isImmersion.contMDiff h₂₃).fst
      ((transverse_fiberProduct_assoc_iff (by simp) hfL.isImmersion.contMDiff.snd
        hgL.isImmersion.contMDiff.fst hgL.isImmersion.contMDiff.snd hkL.isImmersion.contMDiff.fst
        h₁₂ h₂₃).1 hL)
    (hσ₁.twistedProd hσ₄).IsLagrangianImmersion KR
      (fun p : {p : L₁ × {q : L₂ × L₃ // (g q.1).2 = (k q.2).1} // (f p.1).2 = (g p.2.val.1).1} ↦
        ((f p.val.1).1, (k p.val.2.val.2).2)) := by
  have hf := hfL.isImmersion.contMDiff
  have hg := hgL.isImmersion.contMDiff
  have hk := hkL.isImmersion.contMDiff
  let := transverseFiberProductChartedSpace (by simp) hg.snd hk.fst h₂₃
  have := isManifold_transverseFiberProduct (by simp) hg.snd hk.fst h₂₃
  exact IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
    (hσ₃ := hσ₄) ((transverse_fiberProduct_assoc_iff (by simp) hf.snd hg.fst hg.snd hk.fst h₁₂
      h₂₃).1 hL) hfL
    (IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₂) (hσ₂ := hσ₃) (hσ₃ := hσ₄)
      h₂₃ hgL hkL)

/-- **The two groupings of a transverse triple composite are the same correspondence.** Under the
hypotheses of `IsLagrangianImmersion.relComp_assoc_transverseFiberProduct`, the composite
`((x, y), z) ↦ ((f x).1, (k z).2)` on `(L₁ ×_{M₂} L₂) ×_{M₃} L₃` is a Lagrangian correspondence
`M₁ ⇝ M₄` exactly when the composite `(x, (y, z)) ↦ ((f x).1, (k z).2)` on
`L₁ ×_{M₂} (L₂ ×_{M₃} L₃)` is. The associator `TauCeti.fiberProductAssocDiffeomorph` of the two
fibre-product manifolds carries the second parametrization to the first. -/
theorem IsLagrangianImmersion.isLagrangianEmbedding_relComp_assoc_transverseFiberProduct_iff
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ g)
    (hkL : (hσ₃.twistedProd hσ₄).IsLagrangianImmersion K₃ k)
    (hL :
      letI := transverseFiberProductChartedSpace (by simp)
        hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst h₁₂
      ∀ p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} × L₃, (g p.1.val.2).2 = (k p.2).1 →
        (mfderiv K₁₂ I₃ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ (g q.val.2).2)
          p.1).range ⊔
        (((tangentSpaceCast I₃ (k p.2).1 (g p.1.val.2).2).toContinuousLinearMap).comp
          (mfderiv K₃ I₃ (fun z ↦ (k z).1) p.2)).range = ⊤) :
    letI := transverseFiberProductChartedSpace (by simp)
      hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst h₁₂
    haveI := isManifold_transverseFiberProduct (by simp)
      hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst h₁₂
    letI := transverseFiberProductChartedSpace (by simp)
      hgL.isImmersion.contMDiff.snd hkL.isImmersion.contMDiff.fst h₂₃
    haveI := isManifold_transverseFiberProduct (by simp)
      hgL.isImmersion.contMDiff.snd hkL.isImmersion.contMDiff.fst h₂₃
    letI := transverseFiberProductChartedSpace (by simp)
      (contMDiff_relComp_transverseFiberProduct hfL.isImmersion.contMDiff
        hgL.isImmersion.contMDiff h₁₂).snd hkL.isImmersion.contMDiff.fst hL
    letI := transverseFiberProductChartedSpace (by simp) hfL.isImmersion.contMDiff.snd
      (contMDiff_relComp_transverseFiberProduct hgL.isImmersion.contMDiff
        hkL.isImmersion.contMDiff h₂₃).fst
      ((transverse_fiberProduct_assoc_iff (by simp) hfL.isImmersion.contMDiff.snd
        hgL.isImmersion.contMDiff.fst hgL.isImmersion.contMDiff.snd hkL.isImmersion.contMDiff.fst
        h₁₂ h₂₃).1 hL)
    (hσ₁.twistedProd hσ₄).IsLagrangianEmbedding KL
        (fun p : {p : {q : L₁ × L₂ // (f q.1).2 = (g q.2).1} × L₃ // (g p.1.val.2).2 = (k p.2).1} ↦
          ((f p.val.1.val.1).1, (k p.val.2).2)) ↔
      (hσ₁.twistedProd hσ₄).IsLagrangianEmbedding KR
        (fun p : {p : L₁ × {q : L₂ × L₃ // (g q.1).2 = (k q.2).1} // (f p.1).2 = (g p.2.val.1).1} ↦
          ((f p.val.1).1, (k p.val.2.val.2).2)) := by
  have hf := hfL.isImmersion.contMDiff
  have hg := hgL.isImmersion.contMDiff
  have hk := hkL.isImmersion.contMDiff
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst h₁₂
  have := isManifold_transverseFiberProduct (by simp) hf.snd hg.fst h₁₂
  let := transverseFiberProductChartedSpace (by simp) hg.snd hk.fst h₂₃
  have := isManifold_transverseFiberProduct (by simp) hg.snd hk.fst h₂₃
  have hF := contMDiff_relComp_transverseFiberProduct hf hg h₁₂
  have hG := contMDiff_relComp_transverseFiberProduct hg hk h₂₃
  have hR := (transverse_fiberProduct_assoc_iff (by simp) hf.snd hg.fst hg.snd hk.fst h₁₂ h₂₃).1 hL
  let := transverseFiberProductChartedSpace (by simp) hF.snd hk.fst hL
  let := transverseFiberProductChartedSpace (by simp) hf.snd hG.fst hR
  -- Both composites are Lagrangian immersions, so each is a Lagrangian embedding exactly when it
  -- is a topological embedding.
  rw [IsLagrangianImmersion.isLagrangianEmbedding_relComp_transverseFiberProduct_iff
      (hσ₁ := hσ₁) (hσ₂ := hσ₃) (hσ₃ := hσ₄) hL
      (IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
        (hσ₃ := hσ₃) h₁₂ hfL hgL) hkL,
    IsLagrangianImmersion.isLagrangianEmbedding_relComp_transverseFiberProduct_iff
      (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₄) hR hfL
      (IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₂) (hσ₂ := hσ₃)
        (hσ₃ := hσ₄) h₂₃ hgL hkL)]
  -- The first composite is the second one composed with the associator.
  let e := fiberProductAssocDiffeomorph (f := fun x : L₁ ↦ (f x).2) (g := fun y : L₂ ↦ (g y).1)
    (h := fun y : L₂ ↦ (g y).2) (k := fun z : L₃ ↦ (k z).1)
    (isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst h₁₂)
    (isSmoothEmbedding_coe_transverseFiberProduct (by simp) hg.snd hk.fst h₂₃)
    (isSmoothEmbedding_coe_transverseFiberProduct (by simp) hF.snd hk.fst hL)
    (isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hG.fst hR)
  refine Iff.trans (iff_of_eq (congrArg _ (funext fun p ↦ ?_))) (e.toHomeomorph.isEmbedding_comp_iff
    (f := fun p : {p : L₁ × {q : L₂ × L₃ // (g q.1).2 = (k q.2).1} // (f p.1).2 = (g p.2.val.1).1} ↦
      ((f p.val.1).1, (k p.val.2.val.2).2)))
  simp [e]

end Immersion

end TauCeti.SmoothTwoForm.IsNondegenerate
