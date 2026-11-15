/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.VectorBundle.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Complementary smooth subbundles

Let `V` and `W` be two families of subspaces of the fibres of a `C^n` vector bundle `E`, each with
`C^n` local frames near every point, so that with the subspace topology they are `C^n` subbundles
of `E` (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). Adding a vector of `V`
to a vector of `W` over the same point is a `C^n` map from the total space of the direct-sum bundle
`V ×ᵇ W` to that of `E` (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_add`).

When `V x` and `W x` are complementary in every fibre, this map is bijective on each fibre, and it
is a `C^n` diffeomorphism of total spaces
(`TauCeti.HasLocalContMDiffSubbundleFrames.exists_bundleDiffeomorph_prod_of_isCompl`): `E` is the
Whitney sum of `V` and `W`. Smoothness of the inverse is automatic
(`TauCeti.bundleDiffeomorph`), so the projections of `E` onto `V` along `W` and onto `W` along `V`
are `C^n` maps of total spaces
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_projectionOnto_of_isCompl`). No
metric is involved, and the subbundles need not be orthogonal for any metric.
-/

public section

open Bundle Set Module
open scoped Manifold ContDiff

namespace TauCeti.HasLocalContMDiffSubbundleFrames

section Add

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [IsRCLikeNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, IsScalarTower 𝕜 𝕜' (E x)] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜' F E] [VectorBundle 𝕜 F E]
  [ContMDiffVectorBundle n F E IB]
  {ι ι' : Type*} [Fintype ι] [Fintype ι'] {V W : Π x, Submodule 𝕜' (E x)}

/-- **Adding vectors of two smooth subbundles is smooth.** If the families of subspaces `V` and
`W` of the fibres of a `C^n` vector bundle `E` have `C^n` local frames near every point, then
`(x, v, w) ↦ (x, v + w)` is a `C^n` map from the total space of the direct-sum bundle `V ×ᵇ W`,
each summand carrying the subbundle structure of
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`, to the total space of `E`. -/
theorem contMDiff_totalSpace_add (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (hW : HasLocalContMDiffSubbundleFrames IB n F ι' W) :
    letI := subbundleTopology F (F' := ι → 𝕜') V
    letI := hV.fiberBundle
    letI := hV.vectorBundle
    letI := VectorBundle.restrictScalars 𝕜 𝕜' (ι → 𝕜') fun x ↦ V x
    letI := subbundleTopology F (F' := ι' → 𝕜') W
    letI := hW.fiberBundle
    letI := hW.vectorBundle
    letI := VectorBundle.restrictScalars 𝕜 𝕜' (ι' → 𝕜') fun x ↦ W x
    ContMDiff (IB.prod 𝓘(𝕜, (ι → 𝕜') × (ι' → 𝕜'))) (IB.prod 𝓘(𝕜, F)) n
      (fun v : TotalSpace ((ι → 𝕜') × (ι' → 𝕜')) ((fun x ↦ V x) ×ᵇ fun x ↦ W x) ↦
        (⟨v.proj, (v.2.1 : E v.proj) + v.2.2⟩ : TotalSpace F E)) := by
  let := subbundleTopology F (F' := ι → 𝕜') V
  let := hV.fiberBundle
  let := hV.vectorBundle
  let := VectorBundle.restrictScalars 𝕜 𝕜' (ι → 𝕜') fun x ↦ V x
  let := subbundleTopology F (F' := ι' → 𝕜') W
  let := hW.fiberBundle
  let := hW.vectorBundle
  let := VectorBundle.restrictScalars 𝕜 𝕜' (ι' → 𝕜') fun x ↦ W x
  exact (hV.contMDiff_totalSpace_inclusion.comp Bundle.Prod.contMDiff_fst).add_sectionAlong
    (hW.contMDiff_totalSpace_inclusion.comp Bundle.Prod.contMDiff_snd)

end Add

section IsCompl

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB]
  {ι ι' : Type*} [Fintype ι] {V W : Π x, Submodule 𝕜 (E x)}

/-- **Complementary smooth subbundles split a vector bundle.** Let `V` and `W` be families of
subspaces of the fibres of a `C^n` vector bundle `E`, each with `C^n` local frames near every point,
and complementary in every fibre. Then
`(x, v, w) ↦ (x, v + w)` is a `C^n` diffeomorphism from the total space of the direct-sum bundle
`V ×ᵇ W`, each summand carrying the subbundle structure of
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`, onto the total space of `E`. -/
theorem exists_bundleDiffeomorph_prod_of_isCompl [Fintype ι']
    (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (hW : HasLocalContMDiffSubbundleFrames IB n F ι' W) (hVW : ∀ x, IsCompl (V x) (W x)) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    letI := hV.fiberBundle
    letI := subbundleTopology F (F' := ι' → 𝕜) W
    letI := hW.fiberBundle
    ∃ Φ : TotalSpace ((ι → 𝕜) × (ι' → 𝕜)) ((fun x ↦ V x) ×ᵇ fun x ↦ W x)
        ≃ₘ^n⟮IB.prod 𝓘(𝕜, (ι → 𝕜) × (ι' → 𝕜)), IB.prod 𝓘(𝕜, F)⟯ TotalSpace F E,
      ∀ v, Φ v = ⟨v.proj, (v.2.1 : E v.proj) + v.2.2⟩ := by
  let := subbundleTopology F (F' := ι → 𝕜) V
  let := hV.fiberBundle
  have := hV.vectorBundle
  have := hV.contMDiffVectorBundle
  let := subbundleTopology F (F' := ι' → 𝕜) W
  let := hW.fiberBundle
  have := hW.vectorBundle
  have := hW.contMDiffVectorBundle
  have : CompleteSpace 𝕜 := by
    let := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  -- On each fibre, `(v, w) ↦ v + w` is a linear equivalence from a finite-dimensional space, whose
  -- summands are fibres of bundles with model `ι → 𝕜` and `ι' → 𝕜`, onto a Hausdorff space, a
  -- fibre of a bundle with model `F`; hence it is continuous.
  have hfib (x : B) : FiniteDimensional 𝕜 (V x × W x) ∧ T2Space (E x) := by
    have := VectorBundle.finiteDimensional 𝕜 (ι → 𝕜) (fun x ↦ V x) x
    have := VectorBundle.finiteDimensional 𝕜 (ι' → 𝕜) (fun x ↦ W x) x
    exact ⟨inferInstance, FiberBundle.t2Space F E x⟩
  refine ⟨bundleDiffeomorph (fun x ↦ have := (hfib x).1; have := (hfib x).2
    (Submodule.prodEquivOfIsCompl _ _ (hVW x)).toContinuousLinearEquiv) ?_, fun v ↦ ?_⟩
  · simpa only [LinearEquiv.coe_toContinuousLinearEquiv', Submodule.coe_prodEquivOfIsCompl']
      using hV.contMDiff_totalSpace_add hW
  · simp

/-- **Projecting onto a smooth subbundle along a complementary one is smooth.** Under the
hypotheses of `TauCeti.HasLocalContMDiffSubbundleFrames.exists_bundleDiffeomorph_prod_of_isCompl`,
the projection of `E` onto `V` along `W` is a `C^n` map from the total space of `E` to that of the
subbundle `V`. -/
theorem contMDiff_totalSpace_projectionOnto_of_isCompl [Finite ι']
    (hV : HasLocalContMDiffSubbundleFrames IB n F ι V)
    (hW : HasLocalContMDiffSubbundleFrames IB n F ι' W) (hVW : ∀ x, IsCompl (V x) (W x)) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    letI := hV.fiberBundle
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, ι → 𝕜)) n
      (fun w : TotalSpace F E ↦ (⟨w.proj, (V w.proj).projectionOnto (W w.proj) (hVW w.proj) w.2⟩ :
        TotalSpace (ι → 𝕜) fun x ↦ V x)) := by
  have := Fintype.ofFinite ι'
  let := subbundleTopology F (F' := ι → 𝕜) V
  let := hV.fiberBundle
  let := subbundleTopology F (F' := ι' → 𝕜) W
  let := hW.fiberBundle
  obtain ⟨Φ, hΦ⟩ := exists_bundleDiffeomorph_prod_of_isCompl hV hW hVW
  -- `Φ⁻¹` splits a vector of `E` into its components along `V` and `W`.
  have hΦs (w : TotalSpace F E) : Φ.symm w =
      ⟨w.proj, (Submodule.prodEquivOfIsCompl _ _ (hVW w.proj)).symm w.2⟩ := by
    refine Φ.toEquiv.symm_apply_eq.mpr ?_
    rw [Diffeomorph.coe_toEquiv, hΦ, ← Submodule.coe_prodEquivOfIsCompl' _ _ (hVW w.proj),
      LinearEquiv.apply_symm_apply]
  refine (Bundle.Prod.contMDiff_fst.comp Φ.symm.contMDiff).congr fun w ↦ ?_
  rw [Function.comp_apply, hΦs, Submodule.prodEquivOfIsCompl_symm_apply]

end IsCompl

end TauCeti.HasLocalContMDiffSubbundleFrames
