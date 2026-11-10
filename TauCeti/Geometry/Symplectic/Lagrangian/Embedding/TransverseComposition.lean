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

Let `f : L₁ → M₁ × M₂` be Lagrangian for `pr₁*σ₁ - pr₂*σ₂` and `g : L₂ → M₂ × M₃` Lagrangian for
`pr₁*σ₂ - pr₂*σ₃`, and suppose that the middle coordinates `x ↦ (f x).2` and `y ↦ (g y).1` are
transverse maps into `M₂`. Then the fibre product

`L₁ ×_{M₂} L₂ = {(x, y) | (f x).2 = (g y).1}`

is an embedded submanifold of `L₁ × L₂` (`TauCeti.transverseFiberProductChartedSpace`), and this
file studies the composite map

`h (x, y) = ((f x).1, (g y).2) : L₁ ×_{M₂} L₂ → M₁ × M₃`.

* `h` is a Lagrangian map for `pr₁*σ₁ - pr₂*σ₃`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.transverseComp`): the tangent spaces of
  the fibre product are the linear fibre products of tangent spaces, so the general composition
  theorem `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.relComp` applies.
* Transversality also rules out excess directions. A vector in the kernel of `dh` has the form
  `(u, w)` with `df u = (0, v)` and `dg w = (v, 0)`. Since the tangent images of `f` and `g` are
  canonical relations whose projections to `T M₂` span it, `v = 0`
  (`TauCeti.SymplecticForm.IsLagrangian.disjoint_comap_inr_comap_inl_iff`). So when `f` and `g`
  have injective differentials, so does `h`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.injective_mfderiv_transverseComp`), and
  when they are immersions, so is `h`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.isImmersion_transverseComp`).
  Hence the transverse composite of Lagrangian immersions is a Lagrangian immersion
  (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianImmersion.transverseComp`), and of
  Lagrangian embeddings it is a Lagrangian embedding as soon as `h` is a topological embedding
  (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding.transverseComp`). The last
  hypothesis cannot be dropped: transversality is a local condition and does not prevent `h` from
  being non-injective.

The symplectic manifolds `M₁` and `M₃` only need to be boundaryless for the immersion statements;
`L₁`, `L₂` and `M₂` are boundaryless and finite-dimensional, as in the transverse fibre-product
theorem.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* K. Wehrheim, C. Woodward, *Functoriality for Lagrangian correspondences in Floer theory*, Quantum
  Topology 1 (2010), 129–170, Section 2.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [FiniteDimensional ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [K₁.Boundaryless] [TopologicalSpace L₁]
  [ChartedSpace HL₁ L₁] [IsManifold K₁ ∞ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [FiniteDimensional ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [K₂.Boundaryless] [TopologicalSpace L₂]
  [ChartedSpace HL₂ L₂] [IsManifold K₂ ∞ L₂]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃}

omit [FiniteDimensional ℝ E₁] [I₂.Boundaryless] [FiniteDimensional ℝ E₃] in
/-- The no-excess statement at tangent spaces of `M₂` at two points that are equal but not
syntactically so. If the ranges of `A` and `B` are canonical relations whose projections to the
middle tangent space span it, then `A u = 0` and `B w = 0` whenever `A u = (0, v)` and
`B w = (v, 0)`. -/
private theorem eq_zero_of_transverse {x₁ : M₁} {y y' : M₂} {x₃ : M₃} (hy : y = y')
    {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {A : X →ₗ[ℝ] TangentSpace I₁ x₁ × TangentSpace I₂ y}
    {B : Y →ₗ[ℝ] TangentSpace I₂ y' × TangentSpace I₃ x₃}
    (hA : ((hσ₁.symplecticFormAt x₁).twistedProd (hσ₂.symplecticFormAt y)).IsLagrangian
      (LinearMap.range A))
    (hB : ((hσ₂.symplecticFormAt y').twistedProd (hσ₃.symplecticFormAt x₃)).IsLagrangian
      (LinearMap.range B))
    (htr : LinearMap.range (LinearMap.snd ℝ _ _ ∘ₗ A) ⊔
      LinearMap.range (((tangentSpaceCast I₂ y' y).toContinuousLinearMap :
        TangentSpace I₂ y' →ₗ[ℝ] TangentSpace I₂ y) ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ B) = ⊤)
    {u : X} {w : Y} (h₁ : (A u).1 = 0) (h₂ : (A u).2 = tangentSpaceCast I₂ y' y (B w).1)
    (h₃ : (B w).2 = 0) :
    A u = 0 ∧ B w = 0 := by
  subst hy
  -- `tangentSpaceCast I₂ y y` is the identity.
  have hcast : ((tangentSpaceCast I₂ y y).toContinuousLinearMap :
      TangentSpace I₂ y →ₗ[ℝ] TangentSpace I₂ y) = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  rw [hcast, LinearMap.id_comp, LinearMap.range_comp, LinearMap.range_comp] at htr
  have hdisj := (hA.disjoint_comap_inr_comap_inl_iff hB).mpr htr
  have hAu : A u = (0, (A u).2) := Prod.ext h₁ rfl
  have hBw : B w = ((A u).2, 0) := Prod.ext h₂.symm h₃
  have hv : (A u).2 = 0 := Submodule.disjoint_def.mp hdisj _
    (by rw [Submodule.mem_comap, LinearMap.inr_apply, ← hAu]; exact LinearMap.mem_range_self A u)
    (by rw [Submodule.mem_comap, LinearMap.inl_apply, ← hBw]; exact LinearMap.mem_range_self B w)
  exact ⟨by rw [hAu, hv, Prod.mk_zero_zero], by rw [hBw, hv, Prod.mk_zero_zero]⟩

section Composite

variable (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
  (htrans : ∀ p : L₁ × L₂, (f p.1).2 = (g p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (g p.2).1 (f p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) p.2)).range = ⊤)

include hf hg htrans

omit [FiniteDimensional ℝ E₁] [I₂.Boundaryless] [FiniteDimensional ℝ E₃] [FiniteDimensional ℝ EL₁]
  [K₁.Boundaryless] [IsManifold K₁ ∞ L₁] [FiniteDimensional ℝ EL₂] [K₂.Boundaryless]
  [IsManifold K₂ ∞ L₂] in
/-- At a point `(x, y)` of the transverse fibre product, if `df u = (0, v)` and `dg w = (v, 0)`
then `df u = 0` and `dg w = 0`. -/
private theorem mfderiv_eq_zero_of_transverse (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) (c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1})
    {u : TangentSpace K₁ c.1.1} {w : TangentSpace K₂ c.1.2}
    (h₁ : (mfderiv K₁ (I₁.prod I₂) f c.1.1 u).1 = 0)
    (h₂ : (mfderiv K₁ (I₁.prod I₂) f c.1.1 u).2 = (mfderiv K₂ (I₂.prod I₃) g c.1.2 w).1)
    (h₃ : (mfderiv K₂ (I₂.prod I₃) g c.1.2 w).2 = 0) :
    mfderiv K₁ (I₁.prod I₂) f c.1.1 u = 0 ∧ mfderiv K₂ (I₂.prod I₃) g c.1.2 w = 0 := by
  have hfx := hf.mdifferentiableAt (x := c.1.1) (by simp)
  have hgy := hg.mdifferentiableAt (x := c.1.2) (by simp)
  -- Reading `T (M₁ × M₂)` as `T M₁ × T M₂` only changes the types of tangent vectors.
  set A := (Manifold.tangentSpaceProdEquiv (f c.1.1)).toLinearEquiv.toLinearMap ∘ₗ
    (mfderiv K₁ (I₁.prod I₂) f c.1.1).toLinearMap
  set B := (Manifold.tangentSpaceProdEquiv (g c.1.2)).toLinearEquiv.toLinearMap ∘ₗ
    (mfderiv K₂ (I₂.prod I₃) g c.1.2).toLinearMap
  have hA (u) : A u = mfderiv K₁ (I₁.prod I₂) f c.1.1 u := Manifold.tangentSpaceProdEquiv_apply _ _
  have hB (w) : B w = mfderiv K₂ (I₂.prod I₃) g c.1.2 w := Manifold.tangentSpaceProdEquiv_apply _ _
  -- Transversality of the middle coordinates, read through `A` and `B`.
  have e₁ : ((mfderiv K₁ I₂ (fun x ↦ (f x).2) c.1.1 : _ →L[ℝ] _) : _ →ₗ[ℝ] _) =
      LinearMap.snd ℝ _ _ ∘ₗ A :=
    LinearMap.ext fun u ↦ by simpa [A] using hfx.mfderiv_snd_apply u
  have e₂ : ((((tangentSpaceCast I₂ (g c.1.2).1 (f c.1.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) c.1.2) : _ →L[ℝ] _) : _ →ₗ[ℝ] _) =
      ((tangentSpaceCast I₂ (g c.1.2).1 (f c.1.1).2).toContinuousLinearMap :
        TangentSpace I₂ (g c.1.2).1 →ₗ[ℝ] TangentSpace I₂ (f c.1.1).2) ∘ₗ
          LinearMap.fst ℝ _ _ ∘ₗ B :=
    LinearMap.ext fun w ↦ by simpa [B] using hgy.mfderiv_fst_apply w
  have htr := htrans c.1 c.2
  rw [e₁, e₂] at htr
  have h := eq_zero_of_transverse (hσ₂ := hσ₂) c.2
    ((isLagrangianMap_twistedProd_iff_forall hσ₁ hσ₂).mp hfL c.1.1)
    ((isLagrangianMap_twistedProd_iff_forall hσ₂ hσ₃).mp hgL c.1.2) htr (by rw [hA]; exact h₁)
    (by rw [hA, hB]; exact h₂) (by rw [hB]; exact h₃)
  rwa [hA, hB] at h

/-- **Transverse composition of Lagrangian correspondences.** If `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` are Lagrangian maps for the twisted products whose middle coordinates are
transverse, then `(x, y) ↦ ((f x).1, (g y).2)` is a Lagrangian map on the transverse fibre product
`L₁ ×_{M₂} L₂` for `pr₁*σ₁ - pr₂*σ₃`. -/
theorem IsLagrangianMap.transverseComp (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianMap
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f c.1.1).1, (g c.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  have hi := isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst htrans
  exact hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL (hf.mdifferentiable (by simp))
    (hg.mdifferentiable (by simp)) (hi.contMDiff.fst.mdifferentiable (by simp))
    (hi.contMDiff.snd.mdifferentiable (by simp)) (fun c ↦ c.2) fun c u w h ↦
      exists_mfderiv_fst_eq_and_mfderiv_snd_eq_transverseFiberProduct (by simp) hf.snd hg.fst
        htrans c u w (by
          rw [(hf.mdifferentiableAt (by simp)).mfderiv_snd_apply,
            (hg.mdifferentiableAt (by simp)).mfderiv_fst_apply]
          exact h)

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₃] in
/-- **Transverse composition has no excess kernel.** If `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` are Lagrangian maps for the twisted products with injective differentials
and transverse middle coordinates, then `(x, y) ↦ ((f x).1, (g y).2)` has injective differentials
on the transverse fibre product `L₁ ×_{M₂} L₂`. -/
theorem IsLagrangianMap.injective_mfderiv_transverseComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hfi : ∀ x, Injective (mfderiv K₁ (I₁.prod I₂) f x))
    (hgi : ∀ y, Injective (mfderiv K₂ (I₂.prod I₃) g y)) :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    ∀ c, Injective (mfderiv 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (I₁.prod I₃)
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f c.1.1).1, (g c.1.2).2)) c) := by
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  intro c
  have hi := isSmoothEmbedding_coe_transverseFiberProduct (by simp) hf.snd hg.fst htrans
  have hval := (hi.contMDiff c).mdifferentiableAt (by simp)
  have hfx := hf.mdifferentiableAt (x := c.1.1) (by simp)
  have hgy := hg.mdifferentiableAt (x := c.1.2) (by simp)
  have hfa : MDifferentiableAt _ (I₁.prod I₂)
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ f c.1.1) c := hfx.comp c hval.fst
  have hgb : MDifferentiableAt _ (I₂.prod I₃)
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ g c.1.2) c := hgy.comp c hval.snd
  have hh : MDifferentiableAt _ (I₁.prod I₃)
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f c.1.1).1, (g c.1.2).2)) c :=
    hfa.fst.prodMk hgb.snd
  refine (injective_iff_map_eq_zero _).mpr fun ξ hξ ↦ ?_
  set u := mfderiv _ K₁ (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ c.1.1) c ξ with hu
  set w := mfderiv _ K₂ (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ c.1.2) c ξ with hw
  have hdu : mfderiv _ (I₁.prod I₂) (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ f c.1.1)
      c ξ = mfderiv K₁ (I₁.prod I₂) f c.1.1 u := mfderiv_comp_apply c hfx hval.fst ξ
  have hdw : mfderiv _ (I₂.prod I₃) (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ g c.1.2)
      c ξ = mfderiv K₂ (I₂.prod I₃) g c.1.2 w := mfderiv_comp_apply c hgy hval.snd ξ
  -- The kernel vector `ξ` gives `df u = (0, v)` and `dg w = (v, 0)`.
  have h₁ : (mfderiv K₁ (I₁.prod I₂) f c.1.1 u).1 = 0 := by
    rw [← hdu, ← hfa.mfderiv_fst_apply, hh.mfderiv_fst_apply, hξ]
    exact Prod.fst_zero
  have h₃ : (mfderiv K₂ (I₂.prod I₃) g c.1.2 w).2 = 0 := by
    rw [← hdw, ← hgb.mfderiv_snd_apply, hh.mfderiv_snd_apply, hξ]
    exact Prod.snd_zero
  have h₂ : (mfderiv K₁ (I₁.prod I₂) f c.1.1 u).2 = (mfderiv K₂ (I₂.prod I₃) g c.1.2 w).1 := by
    rw [← hdu, ← hdw]
    exact hfa.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct hgb (fun c ↦ c.2) ξ
  obtain ⟨hfu, hgw⟩ := mfderiv_eq_zero_of_transverse (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃)
    hf hg htrans hfL hgL c h₁ h₂ h₃
  have hu0 : u = 0 := hfi _ (by rw [map_zero]; exact hfu)
  have hw0 : w = 0 := hgi _ (by rw [map_zero]; exact hgw)
  refine hi.isImmersion.mfderiv_injective (by simp) c ?_
  rw [map_zero]
  exact Prod.ext (by rw [← hval.mfderiv_fst_apply, ← hu, hu0]; exact Prod.fst_zero.symm)
    (by rw [← hval.mfderiv_snd_apply, ← hw, hw0]; exact Prod.snd_zero.symm)

end Composite

section Immersion

variable [I₁.Boundaryless] [I₃.Boundaryless]
  (htrans : ∀ p : L₁ × L₂, (f p.1).2 = (g p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (g p.2).1 (f p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) p.2)).range = ⊤)

/-- The transverse composite of two Lagrangian maps that are immersions is an immersion on the
transverse fibre product. -/
theorem IsLagrangianMap.isImmersion_transverseComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hfi : Manifold.IsImmersion K₁ (I₁.prod I₂) ∞ f)
    (hgi : Manifold.IsImmersion K₂ (I₂.prod I₃) ∞ g) :
    letI := transverseFiberProductChartedSpace (by simp) hfi.contMDiff.snd hgi.contMDiff.fst htrans
    Manifold.IsImmersion 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (I₁.prod I₃) ∞
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f c.1.1).1, (g c.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hfi.contMDiff.snd hgi.contMDiff.fst htrans
  have := isManifold_transverseFiberProduct (by simp) hfi.contMDiff.snd hgi.contMDiff.fst htrans
  have hi := isSmoothEmbedding_coe_transverseFiberProduct (by simp) hfi.contMDiff.snd
    hgi.contMDiff.fst htrans
  exact ((hfi.contMDiff.comp hi.contMDiff.fst).fst.prodMk
    (hgi.contMDiff.comp hi.contMDiff.snd).snd).isImmersion_of_injective_mfderiv (by simp)
    (hfL.injective_mfderiv_transverseComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hfi.contMDiff
      hgi.contMDiff htrans hgL (hfi.mfderiv_injective (by simp)) (hgi.mfderiv_injective (by simp)))

/-- **Transverse composition of Lagrangian immersions.** If `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` are Lagrangian immersions for the twisted products whose middle coordinates are
transverse, then `(x, y) ↦ ((f x).1, (g y).2)` is a Lagrangian immersion of the transverse fibre
product `L₁ ×_{M₂} L₂` for `pr₁*σ₁ - pr₂*σ₃`. -/
theorem IsLagrangianImmersion.transverseComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ g) :
    letI := transverseFiberProductChartedSpace (by simp) hfL.isImmersion.contMDiff.snd
      hgL.isImmersion.contMDiff.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianImmersion
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f c.1.1).1, (g c.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hfL.isImmersion.contMDiff.snd
    hgL.isImmersion.contMDiff.fst htrans
  have h₁ := hfL.two_mul_finrank
  have h₂ := hgL.two_mul_finrank
  rw [finrank_prod] at h₁ h₂
  refine ⟨hfL.isLagrangianMap.isImmersion_transverseComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃)
      htrans hgL.isLagrangianMap hfL.isImmersion hgL.isImmersion,
    (hfL.isLagrangianMap.transverseComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃)
      hfL.isImmersion.contMDiff hgL.isImmersion.contMDiff htrans
      hgL.isLagrangianMap).isIsotropicMap, ?_⟩
  rw [finrank_fin_fun, finrank_prod]
  omega

/-- **Transverse composition of Lagrangian correspondences, embedded case.** If
`f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` are Lagrangian embeddings for the twisted products whose
middle coordinates are transverse, and `(x, y) ↦ ((f x).1, (g y).2)` is a topological embedding of
the fibre product `L₁ ×_{M₂} L₂`, then it is a Lagrangian embedding of the transverse fibre product
for `pr₁*σ₁ - pr₂*σ₃`, that is, a Lagrangian correspondence `M₁ ⇝ M₃`. -/
theorem IsLagrangianEmbedding.transverseComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianEmbedding K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianEmbedding K₂ g)
    (hemb : Topology.IsEmbedding
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f c.1.1).1, (g c.1.2).2))) :
    letI := transverseFiberProductChartedSpace (by simp) hfL.isImmersion.contMDiff.snd
      hgL.isImmersion.contMDiff.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun c : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f c.1.1).1, (g c.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hfL.isImmersion.contMDiff.snd
    hgL.isImmersion.contMDiff.fst htrans
  exact ⟨hfL.isLagrangianMap.isImmersion_transverseComp (hσ₁ := hσ₁) (hσ₂ := hσ₂)
      (hσ₃ := hσ₃) htrans hgL.isLagrangianMap hfL.isImmersion hgL.isImmersion, hemb,
    hfL.isLagrangianMap.transverseComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃)
      hfL.isImmersion.contMDiff hgL.isImmersion.contMDiff htrans hgL.isLagrangianMap⟩

end Immersion

end TauCeti.SmoothTwoForm.IsNondegenerate
