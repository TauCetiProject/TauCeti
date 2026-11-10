/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Composition
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic

/-!
# Composition of embedded Lagrangian correspondences

Let `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` be Lagrangian maps for the twisted products, and let
`a : C → L₁`, `b : C → L₂` present their fibre product as in
`TauCeti.Geometry.Symplectic.Lagrangian.Composition`. When the composite map
`h c = ((f (a c)).1, (g (b c)).2)` is a smooth embedding, it is a Lagrangian correspondence
`M₁ ⇝ M₃`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.isLagrangianEmbedding_relComp`).

When the middle components of `f` and `g` are transverse, the fibre product `L₁ ×_{M₂} L₂` is a
manifold and the composite on it is already an immersion, so for Lagrangian correspondences `f`
and `g` it is a Lagrangian correspondence `M₁ ⇝ M₃` as soon as it is a topological embedding
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding.relComp_transverseFiberProduct`).

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ EC HC C : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [TopologicalSpace L₁] [ChartedSpace HL₁ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [TopologicalSpace L₂] [ChartedSpace HL₂ L₂]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC]
  {KC : ModelWithCorners ℝ EC HC} [TopologicalSpace C] [ChartedSpace HC C]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃} {a : C → L₁} {b : C → L₂}

/-- **Composition of Lagrangian correspondences, embedded case.** Under the hypotheses of
`IsLagrangianMap.relComp`, if the composite `c ↦ ((f (a c)).1, (g (b c)).2)` is moreover a smooth
embedding, it is a Lagrangian correspondence `M₁ ⇝ M₃`. -/
theorem IsLagrangianMap.isLagrangianEmbedding_relComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) (hf : MDifferentiable K₁ (I₁.prod I₂) f)
    (hg : MDifferentiable K₂ (I₂.prod I₃) g) (ha : MDifferentiable KC K₁ a)
    (hb : MDifferentiable KC K₂ b) (hab : ∀ c, (f (a c)).2 = (g (b c)).1)
    (hfib : ∀ c u w, (mfderiv K₁ (I₁.prod I₂) f (a c) u).2 =
        (mfderiv K₂ (I₂.prod I₃) g (b c) w).1 →
      ∃ ξ, mfderiv KC K₁ a c ξ = u ∧ mfderiv KC K₂ b c ξ = w)
    (hemb : Manifold.IsSmoothEmbedding KC (I₁.prod I₃) ∞
      (fun c ↦ ((f (a c)).1, (g (b c)).2))) :
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KC (fun c ↦ ((f (a c)).1, (g (b c)).2)) :=
  (isLagrangianEmbedding_iff_of_isSmoothEmbedding hemb).mpr
    (hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL hf hg ha hb hab hfib)

section Transverse

variable [FiniteDimensional ℝ EL₁] [FiniteDimensional ℝ EL₂] [IsManifold K₁ ∞ L₁]
  [IsManifold K₂ ∞ L₂] [K₁.Boundaryless] [K₂.Boundaryless] [I₁.Boundaryless] [I₂.Boundaryless]
  [I₃.Boundaryless]
  (htrans : ∀ p : L₁ × L₂, (f p.1).2 = (g p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (g p.2).1 (f p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) p.2)).range = ⊤)

include htrans in
/-- **Transverse composition of Lagrangian correspondences, embedded case.** Let
`f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` be Lagrangian correspondences whose middle components
`pr₂ ∘ f` and `pr₁ ∘ g` are transverse. If the composite `(x, y) ↦ ((f x).1, (g y).2)` on the
transverse fibre product `L₁ ×_{M₂} L₂` is a topological embedding, it is a Lagrangian
correspondence `M₁ ⇝ M₃`. Transversality already makes the composite an immersion
(`IsIsotropicMap.isImmersion_relComp_transverseFiberProduct`), so only injectivity and the
topology of the image remain to be assumed. -/
theorem IsLagrangianEmbedding.relComp_transverseFiberProduct
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianEmbedding K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianEmbedding K₂ g)
    (hemb : Topology.IsEmbedding
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2))) :
    letI := transverseFiberProductChartedSpace (by simp) hfL.isImmersion.contMDiff.snd
      hgL.isImmersion.contMDiff.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  have hf := hfL.isImmersion.contMDiff
  have hg := hgL.isImmersion.contMDiff
  let _ := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  exact ⟨hfL.isLagrangianMap.isIsotropicMap.isImmersion_relComp_transverseFiberProduct
      (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hf hg htrans hgL.isLagrangianMap.isIsotropicMap
      (hfL.isImmersion.mfderiv_injective (by simp)) (hgL.isImmersion.mfderiv_injective (by simp)),
    hemb, hfL.isLagrangianMap.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
      (hσ₃ := hσ₃) hf hg htrans hgL.isLagrangianMap⟩

end Transverse

end TauCeti.SmoothTwoForm.IsNondegenerate
