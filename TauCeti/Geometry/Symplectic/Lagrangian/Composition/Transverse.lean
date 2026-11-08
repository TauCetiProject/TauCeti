/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Composition
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

The composite need not be an immersion. Its differential at `(x, y)` sends a tangent pair
`(u, w)` to `((df u).1, (dg w).2)`, so it is injective exactly when there is no **excess**: the
only matching pair `(u, w)` with `(df u).1 = 0` and `(dg w).2 = 0` is zero
(`TauCeti.injective_mfderiv_relComp_transverseFiberProduct_iff`).
When `f` and `g` have injective differentials, the excess at `(x, y)` is the space of vectors
`v ∈ T M₂` with `(0, v)` tangent to `f` and `(v, 0)` tangent to `g`
(`TauCeti.injective_mfderiv_relComp_transverseFiberProduct_iff_of_injective`).
A transverse composite without excess that is a topological embedding is therefore a Lagrangian
correspondence `M₁ ⇝ M₃`.

## Main results

In the namespace `TauCeti`:

* `contMDiff_relComp_transverseFiberProduct`: the composite is smooth on the transverse fibre
  product.
* `injective_mfderiv_relComp_transverseFiberProduct_iff`: the composite has injective
  differential exactly where the composition has no excess.

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `IsLagrangianMap.relComp_transverseFiberProduct`: the transverse composite of Lagrangian maps
  is Lagrangian.
* `IsLagrangianMap.isLagrangianEmbedding_relComp_transverseFiberProduct`: a transverse composite
  without excess which is a topological embedding is a Lagrangian correspondence.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
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

include hf hg htrans

/-- On the transverse fibre product, a tangent pair `(u, w)` at `p` is the image of a tangent
vector of the fibre product exactly when `(df u).2 = (dg w).1`; the two components of that tangent
vector are then `u` and `w`. -/
private theorem exists_mfderiv_eq_of_transverseFiberProduct
    (p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1}) (u : TangentSpace K₁ p.1.1)
    (w : TangentSpace K₂ p.1.2)
    (h : (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).2 = (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).1) :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    ∃ ξ, mfderiv KF K₁ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.1) p ξ = u ∧
      mfderiv KF K₂ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.2) p ξ = w := by
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  have hval := ((isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst
    htrans).contMDiff p).mdifferentiableAt (by simp)
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_transverseFiberProduct_iff (by simp) hf.snd hg.fst
    htrans p (u, w)).2 (by
      rw [(hf.mdifferentiable (by simp) p.1.1).mfderiv_snd_apply,
        (hg.mdifferentiable (by simp) p.1.2).mfderiv_fst_apply]
      exact h)
  exact ⟨ξ, by rw [hval.mfderiv_fst_apply]; exact congrArg Prod.fst hξ,
    by rw [hval.mfderiv_snd_apply]; exact congrArg Prod.snd hξ⟩

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
  have hi := isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst htrans
  have hval := (hi.contMDiff p).mdifferentiableAt (by simp)
  have hfa : MDifferentiableAt KF (I₁.prod I₂)
      (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ f q.1.1) p :=
    (hf.mdifferentiable (by simp) p.1.1).comp p hval.fst
  have hgb : MDifferentiableAt KF (I₂.prod I₃)
      (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ g q.1.2) p :=
    (hg.mdifferentiable (by simp) p.1.2).comp p hval.snd
  -- The differential of the composite reads off the outer components of `df` and `dg`.
  have hd (ξ) : mfderiv KF (I₁.prod I₃)
      (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f q.1.1).1, (g q.1.2).2)) p ξ =
      ((mfderiv K₁ (I₁.prod I₂) f p.1.1
          (mfderiv KF K₁ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.1) p ξ)).1,
        (mfderiv K₂ (I₂.prod I₃) g p.1.2
          (mfderiv KF K₂ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.2) p ξ)).2) := by
    have hh := hfa.fst.prodMk hgb.snd
    refine Prod.ext ?_ ?_
    · rw [← mfderiv_comp_apply p (hf.mdifferentiable (by simp) p.1.1) hval.fst]
      exact (hh.mfderiv_fst_apply ξ).symm.trans (hfa.mfderiv_fst_apply ξ)
    · rw [← mfderiv_comp_apply p (hg.mdifferentiable (by simp) p.1.2) hval.snd]
      exact (hh.mfderiv_snd_apply ξ).symm.trans (hgb.mfderiv_snd_apply ξ)
  -- The differential of the inclusion is injective, so a tangent vector of the fibre product is
  -- zero exactly when both of its components are.
  have hξ (ξ) (h₁ : mfderiv KF K₁
      (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.1) p ξ = 0)
      (h₂ : mfderiv KF K₂ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.2) p ξ = 0) :
      ξ = 0 := by
    refine (injective_iff_map_eq_zero _).1
      ((hi.isImmersion.isImmersionAt p).mfderiv_injective (by simp)) ξ ?_
    rw [hval.mfderiv_fst_apply] at h₁
    rw [hval.mfderiv_snd_apply] at h₂
    exact Prod.ext h₁ h₂
  rw [injective_iff_map_eq_zero]
  constructor
  · intro hinj u w hfg hu hw
    obtain ⟨ξ, rfl, rfl⟩ := exists_mfderiv_eq_of_transverseFiberProduct hf hg htrans p u w hfg
    rw [hinj ξ (by rw [hd, hu, hw]; rfl), map_zero, map_zero]
    exact ⟨rfl, rfl⟩
  · intro hexc ξ hξ0
    rw [hd] at hξ0
    have hmatch : (mfderiv K₁ (I₁.prod I₂) f p.1.1
        (mfderiv KF K₁ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.1) p ξ)).2 =
        (mfderiv K₂ (I₂.prod I₃) g p.1.2
          (mfderiv KF K₂ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.2) p ξ)).1 := by
      rw [← mfderiv_comp_apply p (hf.mdifferentiable (by simp) p.1.1) hval.fst,
        ← mfderiv_comp_apply p (hg.mdifferentiable (by simp) p.1.2) hval.snd]
      exact hfa.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct hgb (fun q ↦ q.2) ξ
    obtain ⟨h₁, h₂⟩ := hexc _ _ hmatch (congrArg Prod.fst hξ0) (congrArg Prod.snd hξ0)
    exact hξ ξ h₁ h₂

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
    rfl
  · have hu0 : mfderiv K₁ (I₁.prod I₂) f p.1.1 u = 0 := Prod.ext hu (h hu hw hfg)
    have hw0 : mfderiv K₂ (I₂.prod I₃) g p.1.2 w = 0 := Prod.ext (hfg ▸ h hu hw hfg) hw
    exact ⟨(injective_iff_map_eq_zero _).1 hfi u hu0, (injective_iff_map_eq_zero _).1 hgi w hw0⟩

namespace SmoothTwoForm.IsNondegenerate

variable [FiniteDimensional ℝ E₁] [IsManifold I₁ ∞ M₁] [FiniteDimensional ℝ E₃] [IsManifold I₃ ∞ M₃]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

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
      exists_mfderiv_eq_of_transverseFiberProduct hf hg htrans p u w h

/-- **Embedded transverse composition of Lagrangian correspondences.** Let `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` be smooth Lagrangian maps for the twisted products, such that `x ↦ (f x).2`
and `y ↦ (g y).1` are transverse, and suppose the composition has no excess: every tangent pair
`(u, w)` with `(df u).2 = (dg w).1`, `(df u).1 = 0` and `(dg w).2 = 0` is zero. If the composite
`(x, y) ↦ ((f x).1, (g y).2)` on the fibre product `L₁ ×_{M₂} L₂` is a topological embedding, it
is a Lagrangian correspondence `M₁ ⇝ M₃`. -/
theorem IsLagrangianMap.isLagrangianEmbedding_relComp_transverseFiberProduct
    [I₁.Boundaryless] [I₃.Boundaryless] (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hexc : ∀ (p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1}) u w,
      (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).2 = (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).1 →
        (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).1 = 0 → (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).2 = 0 →
          u = 0 ∧ w = 0)
    (hemb : Topology.IsEmbedding
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2))) :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KF
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  have := isManifold_transverseFiberProduct (by simp) hf.snd hg.fst htrans
  exact ⟨(contMDiff_relComp_transverseFiberProduct hf hg htrans).isImmersion_of_injective_mfderiv
      (by simp) fun p ↦
        (injective_mfderiv_relComp_transverseFiberProduct_iff hf hg htrans p).2 (hexc p),
    hemb, hfL.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hf hg htrans
      hgL⟩

end SmoothTwoForm.IsNondegenerate

end TauCeti
