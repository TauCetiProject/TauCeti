/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Composition
public import TauCeti.Geometry.Symplectic.Lagrangian.Composition.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Transverse composition of Lagrangian correspondences

Let `f : L₁ → M₁ × M₂` be a smooth Lagrangian map for `pr₁*σ₁ - pr₂*σ₂` and `g : L₂ → M₂ × M₃` a
smooth Lagrangian map for `pr₁*σ₂ - pr₂*σ₃`. Their composite is parametrized by the fibre product

`L₁ ×_{M₂} L₂ = {(x, y) | (f x).2 = (g y).1}`

through the map `(x, y) ↦ ((f x).1, (g y).2)` into `M₁ × M₃`. The composition is **transverse**
when the two maps `x ↦ (f x).2` and `y ↦ (g y).1` into `M₂` are transverse: at every pair `(x, y)`
of the fibre product, the images of their differentials span `T M₂`. Then the fibre product is an
embedded submanifold of `L₁ × L₂`, of dimension `dim L₁ + dim L₂ - dim M₂`, with the atlas
`TauCeti.transverseFiberProductChartedSpace`, and its tangent vectors are exactly the pairs
`(u, w)` with `(df u).2 = (dg w).1`.

This is the tangent hypothesis of `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.relComp`,
so on this actual fibre-product manifold the composite is a Lagrangian map for `pr₁*σ₁ - pr₂*σ₃`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.relComp_transverseFiberProduct`).

The composite is smooth (`TauCeti.contMDiff_relComp_transverseFiberProduct`) but need not be an
immersion: its differential is injective exactly when the composition has no **excess**
(`TauCeti.injective_mfderiv_relComp_transverseFiberProduct_iff`). These general facts about
composites over transverse fibre products live in
`TauCeti.Geometry.Manifold.FiberProduct.Composition`.

For isotropic immersions, transversality itself removes the excess, so the composite is an
immersion (`IsIsotropicMap.isImmersion_relComp_transverseFiberProduct`). A tangent vector killed
by the differential gives `v ∈ T M₂` with `(0, v)` tangent to `f` and `(v, 0)` tangent to `g`.
Isotropy makes `v` orthogonal to the projections of both tangent images, which span `T M₂` by
transversality, so `v = 0`
(`TauCeti.SymplecticForm.IsIsotropic.eq_zero_of_map_snd_sup_map_fst_eq_top`). This
instantiates the pointwise statement `IsIsotropicMap.injective_mfderiv_relComp`. Hence the
transverse composite of Lagrangian immersions is a Lagrangian immersion
(`IsLagrangianImmersion.relComp_transverseFiberProduct`). Conversely, for linear canonical
relations the absence of excess directions already forces transversality
(`TauCeti.SymplecticForm.IsLagrangian.map_snd_sup_map_fst_eq_top_iff`), so at the tangent level
the immersion conclusion is equivalent to the transversality hypothesis.

A transverse composite without excess that is a topological embedding is therefore a Lagrangian
correspondence `M₁ ⇝ M₃`; this embedded case is in
`TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Composition`.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `IsLagrangianMap.relComp_transverseFiberProduct`: the transverse composite of Lagrangian maps
  is Lagrangian.
* `IsIsotropicMap.isImmersion_relComp_transverseFiberProduct`: the transverse composite of
  isotropic immersions is an immersion.
* `IsLagrangianImmersion.relComp_transverseFiberProduct`: the transverse composite of Lagrangian
  immersions is a Lagrangian immersion.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278
  (transversal composition of canonical relations).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [FiniteDimensional ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [K₁.Boundaryless] [TopologicalSpace L₁]
  [ChartedSpace HL₁ L₁] [IsManifold K₁ ∞ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [FiniteDimensional ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [K₂.Boundaryless] [TopologicalSpace L₂]
  [ChartedSpace HL₂ L₂] [IsManifold K₂ ∞ L₂]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃}

/-- The model of the transverse fibre product `L₁ ×_{M₂} L₂`, of dimension
`dim L₁ + dim L₂ - dim M₂`. -/
local notation "KF" => 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)

variable (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
  (htrans : ∀ p : L₁ × L₂, (f p.1).2 = (g p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (g p.2).1 (f p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) p.2)).range = ⊤)

namespace SmoothTwoForm.IsNondegenerate

variable [FiniteDimensional ℝ E₁] [IsManifold I₁ ∞ M₁] [FiniteDimensional ℝ E₃] [IsManifold I₃ ∞ M₃]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

section Smooth

include hf hg htrans

/-- **Transverse composition of Lagrangian correspondences.** Let `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` be smooth Lagrangian maps for the twisted products, such that `x ↦ (f x).2`
and `y ↦ (g y).1` are transverse. Then on the fibre product `L₁ ×_{M₂} L₂`, with its manifold
structure as a transverse fibre product, the composite `(x, y) ↦ ((f x).1, (g y).2)` is a
Lagrangian map for `pr₁*σ₁ - pr₂*σ₃`. It may have excess kernel; see
`injective_mfderiv_relComp_transverseFiberProduct_iff`. -/
theorem IsLagrangianMap.relComp_transverseFiberProduct
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianMap KF
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  have hval := (isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst
    htrans).contMDiff.mdifferentiable (by simp)
  exact hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL (hf.mdifferentiable (by simp))
    (hg.mdifferentiable (by simp)) hval.fst hval.snd (fun p ↦ p.2) fun p u w h ↦
      exists_mfderiv_eq_of_transverseFiberProduct (by simp) hf.snd hg.fst htrans p u w (by
        rwa [(hf.mdifferentiable (by simp) p.1.1).mfderiv_snd_apply,
          (hg.mdifferentiable (by simp) p.1.2).mfderiv_fst_apply])

end Smooth

/-- **Transverse composition has no excess.** If `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` are
isotropic immersions for the twisted products and `x ↦ (f x).2`, `y ↦ (g y).1` are transverse,
then on the transverse fibre-product manifold `L₁ ×_{M₂} L₂` the composite
`(x, y) ↦ ((f x).1, (g y).2)` is an immersion. -/
theorem IsIsotropicMap.isImmersion_relComp_transverseFiberProduct
    (hfL : (hσ₁.twistedProd hσ₂).IsIsotropicMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsIsotropicMap K₂ g)
    (hfi : Manifold.IsImmersion K₁ (I₁.prod I₂) ∞ f)
    (hgi : Manifold.IsImmersion K₂ (I₂.prod I₃) ∞ g) [I₁.Boundaryless] [I₃.Boundaryless] :
    letI := transverseFiberProductChartedSpace (by simp) hfi.contMDiff.snd hgi.contMDiff.fst htrans
    Manifold.IsImmersion KF (I₁.prod I₃) ∞
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  have hf := hfi.contMDiff
  have hg := hgi.contMDiff
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  have := isManifold_transverseFiberProduct (by simp) hf.snd hg.fst htrans
  have hi := isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst htrans
  refine (contMDiff_relComp_transverseFiberProduct hf hg htrans).isImmersion_of_injective_mfderiv
    (by simp) fun p ↦ ?_
  have hvd := hi.contMDiff.mdifferentiable (by simp) p
  -- The inclusion of the fibre product is an immersion, so `(da, db)` is injective.
  exact hfL.injective_mfderiv_relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL
    (hf.mdifferentiable (by simp) _) (hg.mdifferentiable (by simp) _) hvd.fst hvd.snd (fun q ↦ q.2)
    (hfi.mfderiv_injective (by simp) p.1.1) (hgi.mfderiv_injective (by simp) p.1.2)
    (eq_zero_of_mfderiv_transverseFiberProduct (by simp) hf.snd hg.fst htrans p) (htrans p.1 p.2)

/-- **Transverse composition of Lagrangian immersions.** If `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` are Lagrangian immersions for the twisted products and `x ↦ (f x).2`,
`y ↦ (g y).1` are transverse, then on the transverse fibre-product manifold `L₁ ×_{M₂} L₂` the
composite `(x, y) ↦ ((f x).1, (g y).2)` is a Lagrangian immersion for `pr₁*σ₁ - pr₂*σ₃`. -/
theorem IsLagrangianImmersion.relComp_transverseFiberProduct [I₁.Boundaryless] [I₃.Boundaryless]
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ g) :
    letI := transverseFiberProductChartedSpace (by simp)
      hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianImmersion KF
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp)
    hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst htrans
  refine ⟨IsIsotropicMap.isImmersion_relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
      (hσ₃ := hσ₃) htrans hfL.isLagrangianMap.isIsotropicMap hgL.isLagrangianMap.isIsotropicMap
      hfL.isImmersion hgL.isImmersion,
    (IsLagrangianMap.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃)
      hfL.isImmersion.contMDiff hgL.isImmersion.contMDiff htrans hfL.isLagrangianMap
      hgL.isLagrangianMap).isIsotropicMap, ?_⟩
  -- `dim L₁ + dim L₂ - dim M₂` is half of `dim M₁ + dim M₃`.
  have h₁ := hfL.two_mul_finrank
  have h₂ := hgL.two_mul_finrank
  simp only [finrank_prod, finrank_fin_fun] at h₁ h₂ ⊢
  omega

end SmoothTwoForm.IsNondegenerate

end TauCeti
