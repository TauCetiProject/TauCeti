/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Composition
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Transverse composition of Lagrangian correspondences

Let `f : L₁ → M₁ × M₂` be Lagrangian for `pr₁*σ₁ - pr₂*σ₂` and `g : L₂ → M₂ × M₃` Lagrangian for
`pr₁*σ₂ - pr₂*σ₃`, and suppose that the maps `x ↦ (f x).2` and `y ↦ (g y).1` to `M₂` are
transverse. Then the fibre product

`L₁ ×_{M₂} L₂ = {(x, y) | (f x).2 = (g y).1}`

is a manifold of dimension `dim L₁ + dim L₂ - dim M₂`
(`TauCeti.transverseFiberProductChartedSpace`), and this file studies the composite

`h : L₁ ×_{M₂} L₂ → M₁ × M₃`, `(x, y) ↦ ((f x).1, (g y).2)`.

* `h` is a Lagrangian map for `pr₁*σ₁ - pr₂*σ₃`
  (`IsLagrangianMap.relComp_transverseFiberProduct`). This instantiates
  `IsLagrangianMap.relComp`, whose tangent hypothesis is the tangent description of the
  transverse fibre product.
* Transversality also removes the excess: when `f` and `g` are isotropic immersions, `h` is an
  immersion (`IsIsotropicMap.isImmersion_relComp_transverseFiberProduct`). A tangent vector
  killed by `dh` gives `v ∈ T M₂` with `(0, v)` tangent to `f` and `(v, 0)` tangent to `g`.
  Isotropy makes `v` orthogonal to the projections of both tangent images, which span `T M₂` by
  transversality, so `v = 0`
  (`TauCeti.SymplecticForm.IsIsotropic.eq_zero_of_map_snd_sup_map_fst_eq_top`).
* Hence the transverse composite of Lagrangian immersions is a Lagrangian immersion
  (`IsLagrangianImmersion.relComp_transverseFiberProduct`). It is a Lagrangian embedding, that
  is a Lagrangian correspondence `M₁ ⇝ M₃`, exactly when it is moreover a topological embedding
  (`IsLagrangianImmersion.isLagrangianEmbedding_relComp_transverseFiberProduct_iff`).

The declarations above without a namespace prefix are in
`TauCeti.SmoothTwoForm.IsNondegenerate`.

Conversely, for linear canonical relations the absence of excess directions already forces
transversality (`TauCeti.SymplecticForm.IsLagrangian.map_snd_sup_map_fst_eq_top_iff`), so at the
tangent level the immersion conclusion is equivalent to the transversality hypothesis. The
composite need not be injective, even for embedded `f` and `g`, so the embedding hypothesis is
kept separate.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278
  (transversal and strongly transversal composition of canonical relations).
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

/-- Linear form of the excess computation at tangent spaces of `M₂` at two points that are equal
but not syntactically so. If the projections of the ranges of `A` and `B` span the middle factor,
`A u = (0, v)` and `B w = (v, 0)`, then `v = 0`. -/
private theorem snd_eq_zero_of_isIsotropic_range {x₁ : M₁} {y y' : M₂} {x₃ : M₃} (hy : y = y')
    {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {A : X →ₗ[ℝ] TangentSpace I₁ x₁ × TangentSpace I₂ y}
    {B : Y →ₗ[ℝ] TangentSpace I₂ y' × TangentSpace I₃ x₃}
    (hA : ((hσ₁.symplecticFormAt x₁).twistedProd (hσ₂.symplecticFormAt y)).IsIsotropic
      (LinearMap.range A))
    (hB : ((hσ₂.symplecticFormAt y').twistedProd (hσ₃.symplecticFormAt x₃)).IsIsotropic
      (LinearMap.range B))
    (htr : ∀ v : TangentSpace I₂ y, ∃ u w, (B w).1 = v - (A u).2) {u : X} {w : Y}
    (hu : (A u).1 = 0) (hw : (B w).2 = 0) (huw : (A u).2 = (B w).1) : (A u).2 = 0 := by
  subst hy
  refine hA.eq_zero_of_map_snd_sup_map_fst_eq_top hB (eq_top_iff.mpr fun v _ ↦ ?_)
    ⟨u, Prod.ext hu rfl⟩ ⟨w, Prod.ext huw.symm hw⟩
  obtain ⟨u', w', h⟩ := htr v
  rw [← add_sub_cancel (A u').2 v, ← h]
  exact Submodule.add_mem_sup ⟨A u', ⟨u', rfl⟩, rfl⟩ ⟨B w', ⟨w', rfl⟩, rfl⟩

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ E₃]
  [I₂.Boundaryless]
  {EL₁ HL₁ L₁ EL₂ HL₂ L₂ : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [FiniteDimensional ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [K₁.Boundaryless]
  [TopologicalSpace L₁] [ChartedSpace HL₁ L₁] [IsManifold K₁ ∞ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [FiniteDimensional ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [K₂.Boundaryless]
  [TopologicalSpace L₂] [ChartedSpace HL₂ L₂] [IsManifold K₂ ∞ L₂]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃}
  (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
  (htrans : ∀ p : L₁ × L₂, (f p.1).2 = (g p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (g p.2).1 (f p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) p.2)).range = ⊤)

/-- **Transverse composition of Lagrangian correspondences.** If `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` are Lagrangian maps for the twisted products and `x ↦ (f x).2`,
`y ↦ (g y).1` are transverse, then on the transverse fibre-product manifold
`L₁ ×_{M₂} L₂` the composite `(x, y) ↦ ((f x).1, (g y).2)` is a Lagrangian map for
`pr₁*σ₁ - pr₂*σ₃`. -/
theorem IsLagrangianMap.relComp_transverseFiberProduct
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) :
    letI := transverseFiberProductChartedSpace (WithTop.coe_le_coe.2 le_top) hf.snd hg.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianMap
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (WithTop.coe_le_coe.2 le_top) hf.snd hg.fst htrans
  have hval := (isSmoothEmbedding_coe_transverseFiberProduct (WithTop.coe_le_coe.2 le_top)
    hf.snd hg.fst htrans).contMDiff
  refine hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL (hf.mdifferentiable (by simp))
    (hg.mdifferentiable (by simp)) (hval.fst.mdifferentiable (by simp))
    (hval.snd.mdifferentiable (by simp)) (fun p ↦ p.2) fun p u w huw ↦ ?_
  refine exists_mfderiv_fst_eq_and_mfderiv_snd_eq_transverseFiberProduct _ hf.snd hg.fst htrans
    p u w ?_
  rw [(hf.mdifferentiable (by simp) _).mfderiv_snd_apply,
    (hg.mdifferentiable (by simp) _).mfderiv_fst_apply]
  -- `tangentSpaceCast` is the identity of the underlying model space.
  exact huw

/-- **Transverse composition has no excess.** If `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` are
isotropic immersions for the twisted products and `x ↦ (f x).2`, `y ↦ (g y).1` are transverse,
then on the transverse fibre-product manifold `L₁ ×_{M₂} L₂` the composite
`(x, y) ↦ ((f x).1, (g y).2)` is an immersion. -/
theorem IsIsotropicMap.isImmersion_relComp_transverseFiberProduct
    (hfL : (hσ₁.twistedProd hσ₂).IsIsotropicMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsIsotropicMap K₂ g)
    (hfi : Manifold.IsImmersion K₁ (I₁.prod I₂) ∞ f)
    (hgi : Manifold.IsImmersion K₂ (I₂.prod I₃) ∞ g) [I₁.Boundaryless] [I₃.Boundaryless] :
    letI := transverseFiberProductChartedSpace (WithTop.coe_le_coe.2 le_top) hf.snd hg.fst htrans
    Manifold.IsImmersion 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (I₁.prod I₃) ∞
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (WithTop.coe_le_coe.2 le_top) hf.snd hg.fst htrans
  have := isManifold_transverseFiberProduct (WithTop.coe_le_coe.2 le_top) hf.snd hg.fst htrans
  have hi := isSmoothEmbedding_coe_transverseFiberProduct (WithTop.coe_le_coe.2 le_top)
    hf.snd hg.fst htrans
  have hval := hi.contMDiff
  refine ((hf.comp hval.fst).fst.prodMk (hg.comp hval.snd).snd).isImmersion_of_injective_mfderiv
    (WithTop.coe_le_coe.2 le_top) fun p ↦ (injective_iff_map_eq_zero _).mpr fun ξ hξ ↦ ?_
  -- Name the differentials of the two projections and of the maps they feed.
  have hvd := hval.mdifferentiable (by simp) p
  have had := hvd.fst
  have hbd := hvd.snd
  have hfd := hf.mdifferentiable (by simp) p.1.1
  have hgd := hg.mdifferentiable (by simp) p.1.2
  have hfa := hfd.comp p had
  have hgb := hgd.comp p hbd
  have hhd := hfa.fst.prodMk hgb.snd
  set u := mfderiv _ K₁ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.1) p ξ with hu
  set w := mfderiv _ K₂ (fun q : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ q.1.2) p ξ with hw
  -- The outer coordinates of `df u` and `dg w` are those of `dh ξ = 0`.
  have h₁ : (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).1 = 0 := by
    have h := hhd.mfderiv_fst_apply ξ
    rw [hξ] at h
    rw [hu, ← mfderiv_comp_apply p hfd had, ← hfa.mfderiv_fst_apply]
    -- `Prod.fst_zero` does not rewrite `h`: the zero of the tangent space of `M₁ × M₃` is the
    -- zero of `E₁ × E₃` only by definition.
    exact h
  have h₂ : (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).2 = 0 := by
    have h := hhd.mfderiv_snd_apply ξ
    rw [hξ] at h
    rw [hw, ← mfderiv_comp_apply p hgd hbd, ← hgb.mfderiv_snd_apply]
    -- As above, `Prod.snd_zero` only applies to `h` up to definitional unfolding.
    exact h
  -- The middle coordinates match, and transversality forces them to vanish.
  have h₃ : (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).2 = (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).1 := by
    rw [hu, hw, ← mfderiv_comp_apply p hfd had, ← mfderiv_comp_apply p hgd hbd]
    exact hfa.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct hgb (fun q ↦ q.2) ξ
  let A := (Manifold.tangentSpaceProdEquiv (f p.1.1)).toLinearEquiv.toLinearMap ∘ₗ
    (mfderiv K₁ (I₁.prod I₂) f p.1.1).toLinearMap
  let B := (Manifold.tangentSpaceProdEquiv (g p.1.2)).toLinearEquiv.toLinearMap ∘ₗ
    (mfderiv K₂ (I₂.prod I₃) g p.1.2).toLinearMap
  -- `A` and `B` only change the types of tangent vectors.
  have hA : ∀ u, A u = mfderiv K₁ (I₁.prod I₂) f p.1.1 u :=
    fun u ↦ Manifold.tangentSpaceProdEquiv_apply _ _
  have hB : ∀ w, B w = mfderiv K₂ (I₂.prod I₃) g p.1.2 w :=
    fun w ↦ Manifold.tangentSpaceProdEquiv_apply _ _
  have htr : ∀ v : TangentSpace I₂ (f p.1.1).2, ∃ u w, (B w).1 = v - (A u).2 := by
    intro v
    obtain ⟨_, ⟨u', rfl⟩, _, ⟨w', rfl⟩, hv⟩ :=
      Submodule.mem_sup.mp ((htrans p.1 p.2).symm ▸ Submodule.mem_top : v ∈ _)
    refine ⟨u', w', ?_⟩
    rw [← hv, hA, hB]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [(hf.mdifferentiable (by simp) _).mfderiv_snd_apply,
      (hg.mdifferentiable (by simp) _).mfderiv_fst_apply]
    -- `tangentSpaceCast` is the identity of the underlying model space.
    exact (add_sub_cancel_left _ _).symm
  have hv : (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).2 = 0 := by
    rw [← hA]
    exact snd_eq_zero_of_isIsotropic_range (hσ₂ := hσ₂) p.2
      ((isIsotropicMap_twistedProd_iff_forall hσ₁ hσ₂).mp hfL p.1.1)
      ((isIsotropicMap_twistedProd_iff_forall hσ₂ hσ₃).mp hgL p.1.2) htr
      ((congrArg Prod.fst (hA u)).trans h₁) ((congrArg Prod.snd (hB w)).trans h₂)
      ((congrArg Prod.snd (hA u)).trans (h₃.trans (congrArg Prod.fst (hB w)).symm))
  -- Both maps are immersions, so `u = 0` and `w = 0`, and the inclusion is an immersion.
  have hu₀ : u = 0 := hfi.mfderiv_injective (by simp) p.1.1 <| by
    rw [map_zero]
    exact Prod.ext h₁ hv
  have hw₀ : w = 0 := hgi.mfderiv_injective (by simp) p.1.2 <| by
    rw [map_zero]
    exact Prod.ext (h₃ ▸ hv) h₂
  refine hi.isImmersion.mfderiv_injective (by simp) p ?_
  rw [map_zero]
  exact Prod.ext ((hvd.mfderiv_fst_apply ξ).symm.trans hu₀)
    ((hvd.mfderiv_snd_apply ξ).symm.trans hw₀)

/-- **Transverse composition of Lagrangian immersions.** If `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` are Lagrangian immersions for the twisted products and `x ↦ (f x).2`,
`y ↦ (g y).1` are transverse, then on the transverse fibre-product manifold `L₁ ×_{M₂} L₂` the
composite `(x, y) ↦ ((f x).1, (g y).2)` is a Lagrangian immersion for `pr₁*σ₁ - pr₂*σ₃`. -/
theorem IsLagrangianImmersion.relComp_transverseFiberProduct [I₁.Boundaryless] [I₃.Boundaryless]
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ g) :
    letI := transverseFiberProductChartedSpace (WithTop.coe_le_coe.2 le_top)
      hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianImmersion
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (WithTop.coe_le_coe.2 le_top)
    hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst htrans
  refine ⟨IsIsotropicMap.isImmersion_relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
      (hσ₃ := hσ₃)
      hfL.isImmersion.contMDiff hgL.isImmersion.contMDiff htrans
      hfL.isLagrangianMap.isIsotropicMap hgL.isLagrangianMap.isIsotropicMap hfL.isImmersion
      hgL.isImmersion,
    (IsLagrangianMap.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃)
      hfL.isImmersion.contMDiff hgL.isImmersion.contMDiff htrans hfL.isLagrangianMap
      hgL.isLagrangianMap).isIsotropicMap, ?_⟩
  -- `dim L₁ + dim L₂ - dim M₂` is half of `dim M₁ + dim M₃`.
  have h₁ := hfL.two_mul_finrank
  have h₂ := hgL.two_mul_finrank
  simp only [finrank_prod, finrank_fin_fun] at h₁ h₂ ⊢
  omega

/-- **Transverse composition of Lagrangian correspondences, embedded case.** Under the hypotheses
of `IsLagrangianImmersion.relComp_transverseFiberProduct`, the composite
`(x, y) ↦ ((f x).1, (g y).2)` on the transverse fibre-product manifold is a Lagrangian
correspondence `M₁ ⇝ M₃` exactly when it is a topological embedding. -/
theorem IsLagrangianImmersion.isLagrangianEmbedding_relComp_transverseFiberProduct_iff
    [I₁.Boundaryless] [I₃.Boundaryless]
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ g) :
    letI := transverseFiberProductChartedSpace (WithTop.coe_le_coe.2 le_top)
      hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding
        𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
        (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) ↔
      Topology.IsEmbedding
        (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (WithTop.coe_le_coe.2 le_top)
    hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst htrans
  have h := IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
    (hσ₃ := hσ₃) htrans hfL hgL
  exact ⟨fun he ↦ he.isEmbedding, fun he ↦ ⟨h.isImmersion, he, h.isLagrangianMap⟩⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
