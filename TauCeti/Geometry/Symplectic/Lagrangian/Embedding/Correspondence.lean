/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Rescale
public import TauCeti.Geometry.Symplectic.Manifold.TwistedProd

/-!
# Transposes and products of Lagrangian correspondences

A Lagrangian correspondence from `(M, σ)` to `(N, τ)` is a Lagrangian embedding
`f : L → M × N` for the twisted product `pr₁*σ - pr₂*τ`, that is, an embedded Lagrangian
submanifold of `M × N⁻`. Graphs of symplectomorphisms and the diagonal are the basic
examples (`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianEmbedding_graph_iff`). This file
constructs two operations on correspondences.

* **Transpose.** Exchanging the factors turns a correspondence `M ⇝ N` into a correspondence
  `N ⇝ M`. The exchange pulls `pr₁*τ - pr₂*σ` back to the negative of `pr₁*σ - pr₂*τ`, and a
  Lagrangian subspace stays Lagrangian when the form changes sign.
* **Product.** Correspondences `M₁ ⇝ N₁` and `M₂ ⇝ N₂` give a correspondence
  `M₁ × M₂ ⇝ N₁ × N₂`, after regrouping `(M₁ × N₁) × (M₂ × N₂)` as `(M₁ × M₂) × (N₁ × N₂)`.
  The regrouping pulls the twisted product of the product forms back to the product of the
  twisted products, for which products of Lagrangian embeddings are Lagrangian.

Both operations change the model of the ambient product, so the manifolds are finite
dimensional and boundaryless, as in symplectic geometry; this is what lets a diffeomorphism
between different models carry immersions to immersions.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianEmbedding_swap_comp_iff`: the transpose
  of a map into `M × N` is a Lagrangian correspondence `N ⇝ M` exactly when the map is a
  Lagrangian correspondence `M ⇝ N`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding.prodProdProdComm_comp_prodMap`:
  the regrouped product of two Lagrangian correspondences is a Lagrangian correspondence.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' N EL HL L : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [NormedAddCommGroup EL] [NormedSpace ℝ EL]
  [TopologicalSpace HL] {K : ModelWithCorners ℝ EL HL} [K.Boundaryless]
  [TopologicalSpace L] [ChartedSpace HL L] [IsManifold K ∞ L]
  {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
  (hσ : σ.IsNondegenerate) (hτ : τ.IsNondegenerate)

/-- **Transpose of a Lagrangian correspondence.** Exchanging the factors of a Lagrangian
correspondence `M ⇝ N` gives a Lagrangian correspondence `N ⇝ M`. -/
theorem IsLagrangianEmbedding.swap_comp {f : L → M × N}
    (h : (hσ.twistedProd hτ).IsLagrangianEmbedding K f) :
    (hτ.twistedProd hσ).IsLagrangianEmbedding K (Prod.swap ∘ f) := by
  rw [← Diffeomorph.coe_prodComm I J M N ∞]
  -- The exchange pulls the form of `N × M` back to `(-1) • (pr₁*σ - pr₂*τ)`.
  have hpull := mpullback_prodComm_twistedProd σ τ
  rw [← neg_one_smul ℝ (SmoothTwoForm.twistedProd σ τ)] at hpull
  refine (isLagrangianEmbedding_iff_of_isSmoothEmbedding
    ((Diffeomorph.prodComm I J M N ∞).isSmoothEmbedding_comp (by simp)
      h.isSmoothEmbedding)).mpr ?_
  exact (isLagrangianMap_diffeomorph_comp_iff _ hpull).mpr
    (((hσ.twistedProd hτ).isLagrangianMap_smul_iff (-1) (by norm_num)).mpr h.isLagrangianMap)

/-- **Transpose of a Lagrangian correspondence.** A map into `M × N` is a Lagrangian
correspondence `M ⇝ N` exactly when its transpose is a Lagrangian correspondence `N ⇝ M`. -/
@[simp]
theorem isLagrangianEmbedding_swap_comp_iff {f : L → M × N} :
    (hτ.twistedProd hσ).IsLagrangianEmbedding K (Prod.swap ∘ f) ↔
      (hσ.twistedProd hτ).IsLagrangianEmbedding K f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.swap_comp hσ hτ⟩
  simpa only [← Function.comp_assoc, Prod.swap_swap_eq, Function.id_comp] using h.swap_comp hτ hσ

section Product

variable {E₂ H₂ M₂ F₂ H₂' N₂ EL₂ HL₂ L₂ : Type*}
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  [TopologicalSpace H₂'] {J₂ : ModelWithCorners ℝ F₂ H₂'} [J₂.Boundaryless]
  [TopologicalSpace N₂] [ChartedSpace H₂' N₂] [IsManifold J₂ ∞ N₂]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂]
  [TopologicalSpace HL₂] {K₂ : ModelWithCorners ℝ EL₂ HL₂} [K₂.Boundaryless]
  [TopologicalSpace L₂] [ChartedSpace HL₂ L₂] [IsManifold K₂ ∞ L₂]
  {σ₂ : SmoothTwoForm I₂ M₂} {τ₂ : SmoothTwoForm J₂ N₂}
  (hσ₂ : σ₂.IsNondegenerate) (hτ₂ : τ₂.IsNondegenerate)

/-- **Product of Lagrangian correspondences.** Lagrangian correspondences `M ⇝ N` and
`M₂ ⇝ N₂` give a Lagrangian correspondence `M × M₂ ⇝ N × N₂`: the product embedding, with
`(M × N) × (M₂ × N₂)` regrouped as `(M × M₂) × (N × N₂)`. -/
theorem IsLagrangianEmbedding.prodProdProdComm_comp_prodMap {f : L → M × N} {g : L₂ → M₂ × N₂}
    (hf : (hσ.twistedProd hτ).IsLagrangianEmbedding K f)
    (hg : (hσ₂.twistedProd hτ₂).IsLagrangianEmbedding K₂ g) :
    ((hσ.prod hσ₂).twistedProd (hτ.prod hτ₂)).IsLagrangianEmbedding (K.prod K₂)
      (Equiv.prodProdProdComm M N M₂ N₂ ∘ Prod.map f g) := by
  rw [← Diffeomorph.coe_prodProdProdComm I J I₂ J₂ M N M₂ N₂ ∞]
  have h := hf.prodMap hg
  refine (isLagrangianEmbedding_iff_of_isSmoothEmbedding
    ((Diffeomorph.prodProdProdComm I J I₂ J₂ M N M₂ N₂ ∞).isSmoothEmbedding_comp (by simp)
      h.isSmoothEmbedding)).mpr ?_
  exact (isLagrangianMap_diffeomorph_comp_iff _
    (mpullback_prodProdProdComm_twistedProd_prod σ τ σ₂ τ₂)).mpr h.isLagrangianMap

end Product

end TauCeti.SmoothTwoForm.IsNondegenerate
