/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Composites over transverse fibre products

Let `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` be smooth maps, viewed as correspondences
`M₁ ⇝ M₂` and `M₂ ⇝ M₃`. Their relational composite is parametrized by the fibre product

`L₁ ×_{M₂} L₂ = {(x, y) | (f x).2 = (g y).1}`

through the map `(x, y) ↦ ((f x).1, (g y).2)` into `M₁ × M₃`. When `x ↦ (f x).2` and
`y ↦ (g y).1` are transverse, the fibre product carries the manifold structure
`TauCeti.transverseFiberProductChartedSpace`, and the composite is smooth on it.

The composite need not be an immersion. Its differential at `(x, y)` sends a tangent pair
`(u, w)` to `((df u).1, (dg w).2)`, so it is injective exactly when there is no **excess**: the
only matching pair `(u, w)` with `(df u).1 = 0` and `(dg w).2 = 0` is zero.
When `f` and `g` have injective differentials, the excess at `(x, y)` is the space of vectors
`v ∈ T M₂` with `(0, v)` tangent to `f` and `(v, 0)` tangent to `g`.

## Main results

* `TauCeti.contMDiff_relComp_transverseFiberProduct`: the composite is smooth on the transverse
  fibre product.
* `TauCeti.injective_mfderiv_relComp_transverseFiberProduct_iff`: the composite has injective
  differential exactly where the composition has no excess.
* `TauCeti.injective_mfderiv_relComp_transverseFiberProduct_iff_of_injective`: for maps with
  injective differentials, the excess is measured by vectors of `T M₂`.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
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

include hf hg htrans

/-- The composite `(x, y) ↦ ((f x).1, (g y).2)` is smooth on the transverse fibre product
`L₁ ×_{M₂} L₂`. -/
theorem contMDiff_relComp_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    ContMDiff KF (I₁.prod I₃) ∞
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  have hval := (isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst
    htrans).contMDiff
  exact (hf.comp hval.fst).fst.prodMk (hg.comp hval.snd).snd

/-- **The excess of a transverse composition.** The differential at `p = (x, y)` of the composite
`(x, y) ↦ ((f x).1, (g y).2)` on the transverse fibre product is injective exactly when the
composition has no excess at `p`: every tangent pair `(u, w)` with `(df u).2 = (dg w).1`,
`(df u).1 = 0` and `(dg w).2 = 0` is zero. No Lagrangian condition is needed. -/
theorem injective_mfderiv_relComp_transverseFiberProduct_iff
    (p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1}) :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    Function.Injective (mfderiv KF (I₁.prod I₃)
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) p) ↔
      ∀ u w, (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).2 = (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).1 →
        (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).1 = 0 → (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).2 = 0 →
          u = 0 ∧ w = 0 := by
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  have hval := ((isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst
    htrans).contMDiff p).mdifferentiableAt (by simp)
  have hf' := hf.mdifferentiable (by simp) p.1.1
  have hg' := hg.mdifferentiable (by simp) p.1.2
  -- The differential of the composite reads off the outer components of `df` and `dg`.
  have hd := hf'.mfderiv_prodMk_fst_snd_comp_apply
    (a := fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.1) (b := fun q ↦ q.1.2) hg'
    hval.fst hval.snd
  rw [injective_iff_map_eq_zero]
  constructor
  · intro hinj u w hfg hu hw
    obtain ⟨ξ, rfl, rfl⟩ := exists_mfderiv_eq_of_transverseFiberProduct (by simp) hf.snd hg.fst
      htrans p u w (by rwa [hf'.mfderiv_snd_apply, hg'.mfderiv_fst_apply])
    rw [hinj ξ (by rw [hd, hu, hw]; exact Prod.mk_zero_zero), map_zero, map_zero]
    exact ⟨rfl, rfl⟩
  · intro hexc ξ hξ0
    rw [hd] at hξ0
    obtain ⟨h₁, h₂⟩ := hexc _ _
      (hf'.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct_comp (a := fun q ↦ q.1.1)
        (b := fun q ↦ q.1.2) hg' hval.fst hval.snd (fun q ↦ q.2) ξ)
      (congrArg Prod.fst hξ0) (congrArg Prod.snd hξ0)
    exact eq_zero_of_mfderiv_transverseFiberProduct (by simp) hf.snd hg.fst htrans p ξ h₁ h₂

/-- **The excess of a transverse composition of immersions.** If `f` and `g` have injective
differentials at `x` and `y`, the composite `(x, y) ↦ ((f x).1, (g y).2)` on the transverse fibre
product has injective differential at `(x, y)` exactly when no nonzero `v ∈ T M₂` has `(0, v)`
tangent to `f` and `(v, 0)` tangent to `g`. -/
theorem injective_mfderiv_relComp_transverseFiberProduct_iff_of_injective
    (p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1})
    (hfi : Function.Injective (mfderiv K₁ (I₁.prod I₂) f p.1.1))
    (hgi : Function.Injective (mfderiv K₂ (I₂.prod I₃) g p.1.2)) :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    Function.Injective (mfderiv KF (I₁.prod I₃)
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) p) ↔
      ∀ u w, (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).1 = 0 →
        (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).2 = 0 →
        (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).2 = (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).1 →
          (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).2 = 0 := by
  rw [injective_mfderiv_relComp_transverseFiberProduct_iff hf hg htrans]
  refine forall₂_congr fun u w ↦ ⟨fun h hu hw hfg ↦ ?_, fun h hfg hu hw ↦ ?_⟩
  · rw [(h hfg hu hw).1, map_zero]
    exact Prod.snd_zero
  · have hu0 : mfderiv K₁ (I₁.prod I₂) f p.1.1 u = 0 := Prod.ext hu (h hu hw hfg)
    have hw0 : mfderiv K₂ (I₂.prod I₃) g p.1.2 w = 0 := Prod.ext (hfg ▸ h hu hw hfg) hw
    exact ⟨(injective_iff_map_eq_zero _).1 hfi u hu0, (injective_iff_map_eq_zero _).1 hgi w hw0⟩

end TauCeti
