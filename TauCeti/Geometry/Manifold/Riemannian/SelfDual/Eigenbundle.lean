/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.AlternatingForm
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Manifold.Riemannian.Section
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# The self-dual and anti-self-dual eigenbundles of differential forms

On an oriented Riemannian manifold `M` of dimension `k + k` with `k` even, the fibrewise Hodge star
`TauCeti.formHodgeStarCLM` on middle-degree real `k`-forms is a self-adjoint involution on every
fibre `Λᵏ T*_x M`. Each fibre therefore splits orthogonally into its `+1`-eigenspace `Λ⁺_x` of
self-dual covectors (`TauCeti.selfDualSubspace`) and its `-1`-eigenspace `Λ⁻_x` of anti-self-dual
covectors (`TauCeti.antiSelfDualSubspace`), cut out by the complementary projections
`P⁺_x = (1 + ⋆) / 2` (`TauCeti.selfDualProjCLM`) and `P⁻_x = (1 - ⋆) / 2`
(`TauCeti.antiSelfDualProjCLM`). When `0 < k`, both subspaces have dimension
`(k + k).choose k / 2`; for two-forms on an oriented four-manifold (`k = 2`), both `Λ⁺_x` and
`Λ⁻_x` have dimension three.

For a `C^n` Riemannian metric on a `C^(n+1)` manifold (with corners), the projections `P⁺` and
`P⁻` are `C^n` sections of the endomorphism bundle of `Λᵏ T*M` (`TauCeti.contMDiff_selfDualProjCLM`
and `TauCeti.contMDiff_antiSelfDualProjCLM`). Because they have constant rank across each
trivialization of `Λᵏ T*M`, the operator-range frame criterion
`Bundle.Trivialization.exists_isSubbundleFrameOn_map_symmₗ` produces `C^n` local subbundle frames
for `Λ⁺` and `Λ⁻` near every point (`TauCeti.hasLocalContMDiffSubbundleFrames_selfDualSubspace` and
`TauCeti.hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace`, together with the rank-three
four-manifold specializations `TauCeti.hasLocalContMDiffSubbundleFrames_selfDualSubspace_two` and
`TauCeti.hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two`). Consequently:

* `Λ⁺` and `Λ⁻` are `C^n` real vector subbundles of `Λᵏ T*M`, with canonical inclusions that are
  `C^n` smooth embeddings of total spaces;
* `P⁺` and `P⁻` corestrict to `C^n` bundle retractions `Λᵏ T*M → Λ⁺` and `Λᵏ T*M → Λ⁻`, assembling
  into a `C^n` direct-sum diffeomorphism `Λ⁺ ⊕ Λ⁻ ≃ₘ^n Λᵏ T*M`
  (`TauCeti.selfDualProdAntiSelfDualDiffeomorph`);
* the pointwise Gram inner product `TauCeti.alternatingFormInner` restricts to `C^n` Riemannian
  bundle metrics on `Λ⁺` and `Λ⁻` (`TauCeti.selfDualRiemannianMetric` and
  `TauCeti.antiSelfDualRiemannianMetric`);
* smooth sections `ContMDiffSection` of `Λ⁺` and `Λ⁻` correspond `ℝ`-linearly to the submodules
  `TauCeti.SmoothForm.selfDualForms` and `TauCeti.SmoothForm.antiSelfDualForms` of smooth
  self-dual and anti-self-dual differential forms (`TauCeti.selfDualContMDiffSectionEquiv` and
  `TauCeti.antiSelfDualContMDiffSectionEquiv`).

## Main definitions

* `TauCeti.selfDualSubspace`, `TauCeti.antiSelfDualSubspace`: the fibrewise `+1` and `-1`
  eigenspaces `Λ⁺_x, Λ⁻_x ⊆ Λᵏ T*_x M` of the Hodge star.
* `TauCeti.selfDualProjCLM`, `TauCeti.antiSelfDualProjCLM`: the fibrewise continuous linear
  projections `(1 + ⋆) / 2` and `(1 - ⋆) / 2` on `Λᵏ T*_x M`.
* `TauCeti.selfDualBundleProj`, `TauCeti.antiSelfDualBundleProj`: the bundle projections
  `Λᵏ T*M → Λ⁺` and `Λᵏ T*M → Λ⁻` on total spaces.
* `TauCeti.selfDualProdAntiSelfDualDiffeomorph` and
  `TauCeti.selfDualProdAntiSelfDualDiffeomorphTwo`: the `C^n` direct-sum bundle diffeomorphism
  `Λ⁺ ⊕ Λ⁻ ≃ₘ^n Λᵏ T*M` and its rank-three four-manifold specialization.
* `TauCeti.selfDualRiemannianMetric`, `TauCeti.antiSelfDualRiemannianMetric`: the induced `C^n`
  Riemannian bundle metrics on `Λ⁺` and `Λ⁻`.
* `TauCeti.selfDualContMDiffSectionEquiv`, `TauCeti.antiSelfDualContMDiffSectionEquiv`,
  `TauCeti.selfDualContMDiffSectionEquivTwo`, `TauCeti.antiSelfDualContMDiffSectionEquivTwo`:
  the `ℝ`-linear equivalences between smooth subbundle sections of `Λ±` and smooth (anti-)self-dual
  differential forms.

## Main results

* `TauCeti.isCompl_selfDualSubspace_antiSelfDualSubspace`,
  `TauCeti.alternatingFormInner_eq_zero_of_mem_selfDualSubspace_of_mem_antiSelfDualSubspace`:
  each fibre `Λᵏ T*_x M` splits orthogonally as `Λ⁺_x ⊕ Λ⁻_x`.
* `TauCeti.finrank_selfDualSubspace`, `TauCeti.finrank_antiSelfDualSubspace`,
  `TauCeti.finrank_selfDualSubspace_two`, `TauCeti.finrank_antiSelfDualSubspace_two`: the fibre
  dimensions `(k + k).choose k / 2` for even `k > 0`, and `3` for `k = 2`.
* `TauCeti.contMDiff_selfDualProjCLM`, `TauCeti.contMDiff_antiSelfDualProjCLM`: `C^n` regularity
  of the projections as `Hom`-bundle sections.
* `TauCeti.hasLocalContMDiffSubbundleFrames_selfDualSubspace_of_finrank`,
  `TauCeti.hasLocalContMDiffSubbundleFrames_selfDualSubspace`,
  `TauCeti.hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace`,
  `TauCeti.hasLocalContMDiffSubbundleFrames_selfDualSubspace_two`,
  `TauCeti.hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two`: existence of `C^n` local
  subbundle frames for `Λ⁺` and `Λ⁻`.
* `TauCeti.isSmoothEmbedding_selfDualSubspace_inclusion`,
  `TauCeti.isSmoothEmbedding_antiSelfDualSubspace_inclusion`: the total spaces of `Λ⁺` and `Λ⁻`
  are `C^n`-smoothly embedded in `Λᵏ T*M`.
* `TauCeti.contMDiff_selfDualBundleProj`, `TauCeti.contMDiff_antiSelfDualBundleProj`: `C^n`
  regularity of the codomain-restricted bundle projections onto `Λ⁺` and `Λ⁻`.
* `TauCeti.contMDiff_section_selfDualSubspace_iff`,
  `TauCeti.contMDiff_section_antiSelfDualSubspace_iff`: a section of `Λ±` is `C^n` into the
  subbundle total space if and only if the underlying rough `k`-form satisfies `IsSmoothForm I n`.

## References

* M. F. Atiyah, N. J. Hitchin and I. M. Singer, *Self-duality in four-dimensional Riemannian
  geometry*, Proc. R. Soc. Lond. A 362 (1978), 425–461, §1.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University
  Press (1990), §1.1.
* J. W. Morgan, *The Seiberg–Witten Equations and Applications to the Topology of Smooth
  Four-Manifolds*, Mathematical Notes 44, Princeton University Press (1996), Chapter 4.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32.
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E]

section Fibrewise

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

/-! ### Fibrewise self-dual and anti-self-dual subspaces -/

/-- The subspace `Λ⁺_x` of self-dual real `k`-forms at `x`, defined as the `+1`-eigenspace of the
fibrewise Hodge star `formHodgeStarCLM o rfl x`. -/
def selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    Submodule ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  Module.End.eigenspace
    (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) 1

/-- The subspace `Λ⁻_x` of anti-self-dual real `k`-forms at `x`, defined as the `-1`-eigenspace of
the fibrewise Hodge star `formHodgeStarCLM o rfl x`. -/
def antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    Submodule ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  Module.End.eigenspace
    (formHodgeStarCLM o rfl x : Module.End ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) (-1)

/-- The total space of the self-dual subbundle `Λ⁺` carries the subspace topology induced from the
exterior `k`-form bundle (`TauCeti.subbundleTopology`). -/
instance instTopologicalSpaceTotalSpaceSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) {F' : Type*} :
    TopologicalSpace (TotalSpace F' fun x ↦ selfDualSubspace o x) :=
  subbundleTopology (E [⋀^Fin k]→L[ℝ] ℝ) (selfDualSubspace o)

/-- The total space of the anti-self-dual subbundle `Λ⁻` carries the subspace topology induced from
the exterior `k`-form bundle (`TauCeti.subbundleTopology`). -/
instance instTopologicalSpaceTotalSpaceAntiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) {F' : Type*} :
    TopologicalSpace (TotalSpace F' fun x ↦ antiSelfDualSubspace o x) :=
  subbundleTopology (E [⋀^Fin k]→L[ℝ] ℝ) (antiSelfDualSubspace o)

/-- A covector `α ∈ Λᵏ T*_x M` lies in `selfDualSubspace o x` if and only if `⋆α = α`. -/
@[simp]
theorem mem_selfDualSubspace_iff {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} :
    α ∈ selfDualSubspace o x ↔ formHodgeStarCLM o rfl x α = α := by
  rw [selfDualSubspace, Module.End.mem_eigenspace_iff, one_smul]
  rfl

/-- A covector `α ∈ Λᵏ T*_x M` lies in `antiSelfDualSubspace o x` if and only if `⋆α = -α`. -/
@[simp]
theorem mem_antiSelfDualSubspace_iff {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} :
    α ∈ antiSelfDualSubspace o x ↔ formHodgeStarCLM o rfl x α = -α := by
  rw [antiSelfDualSubspace, Module.End.mem_eigenspace_iff, neg_one_smul]
  rfl

/-- Reversing the manifold orientation exchanges the self-dual and anti-self-dual subspaces. -/
@[simp]
theorem selfDualSubspace_neg_orientation (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualSubspace (-o) x = antiSelfDualSubspace o x := by
  ext α
  rw [mem_selfDualSubspace_iff, mem_antiSelfDualSubspace_iff, formHodgeStarCLM_neg_orientation,
    neg_apply, neg_eq_iff_eq_neg]

/-- Reversing the manifold orientation exchanges the anti-self-dual and self-dual subspaces. -/
@[simp]
theorem antiSelfDualSubspace_neg_orientation (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    antiSelfDualSubspace (-o) x = selfDualSubspace o x := by
  rw [← selfDualSubspace_neg_orientation, neg_neg]

/-- A rough middle-degree form is self-dual if and only if its value at every point lies in
`selfDualSubspace o x`. -/
theorem RoughForm.mem_selfDualForms_iff_forall_mem_selfDualSubspace
    {o : Manifold.Orientation I M (Fin (k + k))} {φ : RoughForm I M ℝ k} :
    φ ∈ RoughForm.selfDualForms o ↔ ∀ x, φ x ∈ selfDualSubspace o x := by
  simp [funext_iff, formHodgeStarCLM_apply]

/-- A rough middle-degree form is anti-self-dual if and only if its value at every point lies in
`antiSelfDualSubspace o x`. -/
theorem RoughForm.mem_antiSelfDualForms_iff_forall_mem_antiSelfDualSubspace
    {o : Manifold.Orientation I M (Fin (k + k))} {φ : RoughForm I M ℝ k} :
    φ ∈ RoughForm.antiSelfDualForms o ↔ ∀ x, φ x ∈ antiSelfDualSubspace o x := by
  simp [funext_iff, formHodgeStarCLM_apply]

/-- Evaluating rough self-dual forms at `x` yields `selfDualSubspace o x`. -/
theorem RoughForm.map_proj_selfDualForms_eq_selfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (RoughForm.selfDualForms o).map (LinearMap.proj x) = selfDualSubspace o x := by
  rw [RoughForm.map_proj_selfDualForms]
  ext α
  simp [formHodgeStarCLM_apply]

/-- Evaluating rough anti-self-dual forms at `x` yields `antiSelfDualSubspace o x`. -/
theorem RoughForm.map_proj_antiSelfDualForms_eq_antiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (RoughForm.antiSelfDualForms o).map (LinearMap.proj x) = antiSelfDualSubspace o x := by
  rw [RoughForm.map_proj_antiSelfDualForms]
  ext α
  simp [formHodgeStarCLM_apply]

/-- Self-dual and anti-self-dual covectors at `x` meet trivially. -/
theorem disjoint_selfDualSubspace_antiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    Disjoint (selfDualSubspace o x) (antiSelfDualSubspace o x) := by
  rw [Submodule.disjoint_def]
  intro α hα₁ hα₂
  rw [mem_selfDualSubspace_iff] at hα₁
  rw [mem_antiSelfDualSubspace_iff, hα₁] at hα₂
  have h2 : (2 : ℝ) • α = 0 := by
    calc (2 : ℝ) • α = α + α := two_smul ℝ α
      _ = α + -α := congrArg (α + ·) hα₂
      _ = 0 := add_neg_cancel α
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- In an even middle degree, self-dual and anti-self-dual covectors at `x` are orthogonal for
`alternatingFormInner`. -/
theorem alternatingFormInner_eq_zero_of_mem_selfDualSubspace_of_mem_antiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) {x : M}
    {α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ}
    (hα : α ∈ selfDualSubspace o x) (hβ : β ∈ antiSelfDualSubspace o x) :
    alternatingFormInner (TangentSpace I x) k α β = 0 := by
  have h : alternatingFormInner (TangentSpace I x) k α β =
      -alternatingFormInner (TangentSpace I x) k α β := by
    calc
      alternatingFormInner (TangentSpace I x) k α β
        = alternatingFormInner (TangentSpace I x) k (formHodgeStarCLM o rfl x α) β := by
          rw [mem_selfDualSubspace_iff.mp hα]
      _ = alternatingFormInner (TangentSpace I x) k α (formHodgeStarCLM o rfl x β) :=
          alternatingFormInner_formHodgeStarCLM_left o hk x α β
      _ = alternatingFormInner (TangentSpace I x) k α (-β) := by
          rw [mem_antiSelfDualSubspace_iff.mp hβ]
      _ = -alternatingFormInner (TangentSpace I x) k α β := map_neg _ _
  linarith

/-! ### Fibrewise self-dual and anti-self-dual projections -/

/-- The fibrewise self-dual projection `P⁺_x = (1 + ⋆) / 2` on real `k`-forms at `x`. -/
def selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + formHodgeStarCLM o rfl x)

/-- The fibrewise anti-self-dual projection `P⁻_x = (1 - ⋆) / 2` on real `k`-forms at `x`. -/
def antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ - formHodgeStarCLM o rfl x)

/-- Explicit formula `(α + ⋆α) / 2` for `selfDualProjCLM`. -/
theorem selfDualProjCLM_apply (o : Manifold.Orientation I M (Fin (k + k))) (x : M)
    (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    selfDualProjCLM o x α = (2⁻¹ : ℝ) • (α + formHodgeStarCLM o rfl x α) :=
  (rfl)

/-- Explicit formula `(α - ⋆α) / 2` for `antiSelfDualProjCLM`. -/
theorem antiSelfDualProjCLM_apply (o : Manifold.Orientation I M (Fin (k + k))) (x : M)
    (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    antiSelfDualProjCLM o x α = (2⁻¹ : ℝ) • (α - formHodgeStarCLM o rfl x α) :=
  (rfl)

/-- `RoughForm.selfDualPart` at `x` applies `selfDualProjCLM` to `φ x`. -/
theorem RoughForm.selfDualPart_eq_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (φ : RoughForm I M ℝ k) (x : M) :
    RoughForm.selfDualPart o φ x = selfDualProjCLM o x (φ x) := by
  simp [RoughForm.selfDualPart_apply, selfDualProjCLM_apply, formHodgeStarCLM_apply]

/-- `RoughForm.antiSelfDualPart` at `x` applies `antiSelfDualProjCLM` to `φ x`. -/
theorem RoughForm.antiSelfDualPart_eq_antiSelfDualProjCLM
    (o : Manifold.Orientation I M (Fin (k + k))) (φ : RoughForm I M ℝ k) (x : M) :
    RoughForm.antiSelfDualPart o φ x = antiSelfDualProjCLM o x (φ x) := by
  simp [RoughForm.antiSelfDualPart_apply, antiSelfDualProjCLM_apply, formHodgeStarCLM_apply]

/-- Reversing the orientation exchanges `selfDualProjCLM` and `antiSelfDualProjCLM`. -/
@[simp]
theorem selfDualProjCLM_neg_orientation (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualProjCLM (-o) x = antiSelfDualProjCLM o x := by
  ext α v
  simp [selfDualProjCLM_apply, antiSelfDualProjCLM_apply, sub_eq_add_neg]

/-- Reversing the orientation exchanges `antiSelfDualProjCLM` and `selfDualProjCLM`. -/
@[simp]
theorem antiSelfDualProjCLM_neg_orientation (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    antiSelfDualProjCLM (-o) x = selfDualProjCLM o x := by
  rw [← selfDualProjCLM_neg_orientation, neg_neg]

/-- The self-dual and anti-self-dual projections sum to the identity on every fibre. -/
@[simp]
theorem add_selfDualProjCLM_antiSelfDualProjCLM
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualProjCLM o x + antiSelfDualProjCLM o x =
      ContinuousLinearMap.id ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) := by
  ext α v
  simp only [add_apply, ContinuousLinearMap.id_apply, selfDualProjCLM_apply,
    antiSelfDualProjCLM_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- Every middle-degree covector is the sum of its self-dual and anti-self-dual projections. -/
@[simp]
theorem selfDualProjCLM_add_antiSelfDualProjCLM_apply
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M)
    (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    selfDualProjCLM o x α + antiSelfDualProjCLM o x α = α :=
  congr($(add_selfDualProjCLM_antiSelfDualProjCLM o x) α)

/-- The difference `P⁺_x - P⁻_x` of the two projections is the Hodge star `⋆`. -/
@[simp]
theorem sub_selfDualProjCLM_antiSelfDualProjCLM
    (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    selfDualProjCLM o x - antiSelfDualProjCLM o x = formHodgeStarCLM o rfl x := by
  ext α v
  simp only [sub_apply, selfDualProjCLM_apply, antiSelfDualProjCLM_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- In an even middle degree, `selfDualProjCLM` maps every covector into `selfDualSubspace o x`. -/
theorem selfDualProjCLM_mem_selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    selfDualProjCLM o x α ∈ selfDualSubspace o x := by
  rw [mem_selfDualSubspace_iff, selfDualProjCLM_apply, map_smul, map_add]
  have hstar : formHodgeStarCLM o rfl x (formHodgeStarCLM o rfl x α) = α := by
    simpa using congr($(formHodgeStarCLM_comp_self_of_even o hk x) α)
  rw [hstar, add_comm]

/-- In an even middle degree, `antiSelfDualProjCLM` maps every covector into
`antiSelfDualSubspace o x`. -/
theorem antiSelfDualProjCLM_mem_antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    antiSelfDualProjCLM o x α ∈ antiSelfDualSubspace o x := by
  rw [← selfDualSubspace_neg_orientation, ← selfDualProjCLM_neg_orientation]
  exact selfDualProjCLM_mem_selfDualSubspace (-o) hk x α

/-- `selfDualProjCLM` fixes every self-dual covector. -/
theorem selfDualProjCLM_eq_self_of_mem {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} (hα : α ∈ selfDualSubspace o x) :
    selfDualProjCLM o x α = α := by
  rw [selfDualProjCLM_apply, mem_selfDualSubspace_iff.mp hα, ← two_smul ℝ α,
    inv_smul_smul₀ two_ne_zero]

/-- `antiSelfDualProjCLM` fixes every anti-self-dual covector. -/
theorem antiSelfDualProjCLM_eq_self_of_mem {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} (hα : α ∈ antiSelfDualSubspace o x) :
    antiSelfDualProjCLM o x α = α := by
  rw [← selfDualProjCLM_neg_orientation]
  exact selfDualProjCLM_eq_self_of_mem ((selfDualSubspace_neg_orientation o x).symm ▸ hα)

/-- `selfDualProjCLM` vanishes on `α` if and only if `α` is anti-self-dual. -/
theorem selfDualProjCLM_eq_zero_iff {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} :
    selfDualProjCLM o x α = 0 ↔ α ∈ antiSelfDualSubspace o x := by
  rw [selfDualProjCLM_apply, smul_eq_zero_iff_right (inv_ne_zero two_ne_zero),
    add_eq_zero_iff_neg_eq, mem_antiSelfDualSubspace_iff, eq_comm]

/-- `antiSelfDualProjCLM` vanishes on `α` if and only if `α` is self-dual. -/
theorem antiSelfDualProjCLM_eq_zero_iff {o : Manifold.Orientation I M (Fin (k + k))} {x : M}
    {α : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ} :
    antiSelfDualProjCLM o x α = 0 ↔ α ∈ selfDualSubspace o x := by
  rw [← selfDualProjCLM_neg_orientation, selfDualProjCLM_eq_zero_iff,
    antiSelfDualSubspace_neg_orientation]

/-- In an even middle degree, `selfDualProjCLM` is idempotent. -/
theorem isIdempotentElem_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    IsIdempotentElem (selfDualProjCLM o x) := by
  ext α v
  rw [mul_apply_eq_comp,
    selfDualProjCLM_eq_self_of_mem (selfDualProjCLM_mem_selfDualSubspace o hk x α)]

/-- In an even middle degree, `antiSelfDualProjCLM` is idempotent. -/
theorem isIdempotentElem_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    IsIdempotentElem (antiSelfDualProjCLM o x) := by
  rw [← selfDualProjCLM_neg_orientation]
  exact isIdempotentElem_selfDualProjCLM (-o) hk x

/-- In an even middle degree, `P⁺_x ∘ P⁻_x = 0`. -/
@[simp]
theorem selfDualProjCLM_comp_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    (selfDualProjCLM o x).comp (antiSelfDualProjCLM o x) = 0 := by
  ext α v
  rw [ContinuousLinearMap.comp_apply, zero_apply,
    selfDualProjCLM_eq_zero_iff.mpr (antiSelfDualProjCLM_mem_antiSelfDualSubspace o hk x α)]

/-- In an even middle degree, `P⁻_x ∘ P⁺_x = 0`. -/
@[simp]
theorem antiSelfDualProjCLM_comp_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) :
    (antiSelfDualProjCLM o x).comp (selfDualProjCLM o x) = 0 := by
  simpa using selfDualProjCLM_comp_antiSelfDualProjCLM (-o) hk x

/-- In an even middle degree, the range of `selfDualProjCLM` is `selfDualSubspace o x`. -/
@[simp]
theorem range_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) :
    (selfDualProjCLM o x).range = selfDualSubspace o x := by
  ext α
  refine ⟨?_, fun hα ↦ ⟨α, selfDualProjCLM_eq_self_of_mem hα⟩⟩
  rintro ⟨β, rfl⟩
  exact selfDualProjCLM_mem_selfDualSubspace o hk x β

/-- In an even middle degree, the range of `antiSelfDualProjCLM` is `antiSelfDualSubspace o x`. -/
@[simp]
theorem range_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (x : M) :
    (antiSelfDualProjCLM o x).range = antiSelfDualSubspace o x := by
  rw [← selfDualProjCLM_neg_orientation, range_selfDualProjCLM (-o) hk x,
    selfDualSubspace_neg_orientation]

/-- The kernel of `selfDualProjCLM` is `antiSelfDualSubspace o x`. -/
@[simp]
theorem ker_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (selfDualProjCLM o x).ker = antiSelfDualSubspace o x := by
  ext α
  exact selfDualProjCLM_eq_zero_iff

/-- The kernel of `antiSelfDualProjCLM` is `selfDualSubspace o x`. -/
@[simp]
theorem ker_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) (x : M) :
    (antiSelfDualProjCLM o x).ker = selfDualSubspace o x := by
  ext α
  exact antiSelfDualProjCLM_eq_zero_iff

/-- **Fibrewise direct-sum decomposition**: in an even middle degree, `Λ⁺_x` and `Λ⁻_x` are
complementary subspaces of `Λᵏ T*_x M`. -/
theorem isCompl_selfDualSubspace_antiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (x : M) :
    IsCompl (selfDualSubspace o x) (antiSelfDualSubspace o x) := by
  refine ⟨disjoint_selfDualSubspace_antiSelfDualSubspace o x, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro α _
  rw [← selfDualProjCLM_add_antiSelfDualProjCLM_apply o x α]
  exact Submodule.add_mem_sup (selfDualProjCLM_mem_selfDualSubspace o hk x α)
    (antiSelfDualProjCLM_mem_antiSelfDualSubspace o hk x α)

/-- In an even middle degree, `selfDualProjCLM` is self-adjoint for `alternatingFormInner`. -/
theorem alternatingFormInner_selfDualProjCLM_left (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) k (selfDualProjCLM o x α) β =
      alternatingFormInner (TangentSpace I x) k α (selfDualProjCLM o x β) := by
  simp only [selfDualProjCLM_apply, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
    alternatingFormInner_formHodgeStarCLM_left o hk x α β]

/-- In an even middle degree, `antiSelfDualProjCLM` is self-adjoint for `alternatingFormInner`. -/
theorem alternatingFormInner_antiSelfDualProjCLM_left (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (x : M) (α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) k (antiSelfDualProjCLM o x α) β =
      alternatingFormInner (TangentSpace I x) k α (antiSelfDualProjCLM o x β) := by
  rw [← selfDualProjCLM_neg_orientation]
  exact alternatingFormInner_selfDualProjCLM_left (-o) hk x α β

/-- **Orthogonal decomposition of the Gram pairing**: in an even middle degree,
`⟨α, β⟩ = ⟨P⁺ α, P⁺ β⟩ + ⟨P⁻ α, P⁻ β⟩` at every point. -/
theorem alternatingFormInner_eq_add_selfDualProjCLM_antiSelfDualProjCLM
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (x : M)
    (α β : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) k α β =
      alternatingFormInner (TangentSpace I x) k
          (selfDualProjCLM o x α) (selfDualProjCLM o x β) +
        alternatingFormInner (TangentSpace I x) k
          (antiSelfDualProjCLM o x α) (antiSelfDualProjCLM o x β) := by
  conv_lhs =>
    rw [← selfDualProjCLM_add_antiSelfDualProjCLM_apply o x α,
      ← selfDualProjCLM_add_antiSelfDualProjCLM_apply o x β]
  have h₁ := alternatingFormInner_eq_zero_of_mem_selfDualSubspace_of_mem_antiSelfDualSubspace o hk
    (selfDualProjCLM_mem_selfDualSubspace o hk x α)
    (antiSelfDualProjCLM_mem_antiSelfDualSubspace o hk x β)
  have h₂ : alternatingFormInner (TangentSpace I x) k
      (antiSelfDualProjCLM o x α) (selfDualProjCLM o x β) = 0 := by
    rw [alternatingFormInner_comm]
    exact alternatingFormInner_eq_zero_of_mem_selfDualSubspace_of_mem_antiSelfDualSubspace o hk
      (selfDualProjCLM_mem_selfDualSubspace o hk x β)
      (antiSelfDualProjCLM_mem_antiSelfDualSubspace o hk x α)
  simp only [map_add, LinearMap.add_apply, h₁, h₂, add_zero, zero_add]

/-! ### Fibre dimensions -/

/-- Twice the dimension of `selfDualSubspace o x` is `(k + k).choose k` in an even positive middle
degree. -/
theorem two_mul_finrank_selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (hk₀ : 0 < k) (x : M) :
    2 * finrank ℝ (selfDualSubspace o x) = (k + k).choose k := by
  rw [← RoughForm.map_proj_selfDualForms_eq_selfDualSubspace]
  exact RoughForm.two_mul_finrank_map_proj_selfDualForms o hk hk₀ x

/-- Twice the dimension of `antiSelfDualSubspace o x` is `(k + k).choose k` in an even positive
middle degree. -/
theorem two_mul_finrank_antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (hk₀ : 0 < k) (x : M) :
    2 * finrank ℝ (antiSelfDualSubspace o x) = (k + k).choose k := by
  rw [← selfDualSubspace_neg_orientation]
  exact two_mul_finrank_selfDualSubspace (-o) hk hk₀ x

/-- **Rank of `Λ⁺`**: in an even positive middle degree, each fibre `selfDualSubspace o x` has
dimension `(k + k).choose k / 2`. -/
theorem finrank_selfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (hk₀ : 0 < k) (x : M) :
    finrank ℝ (selfDualSubspace o x) = (k + k).choose k / 2 := by
  have h := two_mul_finrank_selfDualSubspace o hk hk₀ x
  omega

/-- **Rank of `Λ⁻`**: in an even positive middle degree, each fibre `antiSelfDualSubspace o x` has
dimension `(k + k).choose k / 2`. -/
theorem finrank_antiSelfDualSubspace (o : Manifold.Orientation I M (Fin (k + k)))
    (hk : Even k) (hk₀ : 0 < k) (x : M) :
    finrank ℝ (antiSelfDualSubspace o x) = (k + k).choose k / 2 := by
  rw [← selfDualSubspace_neg_orientation]
  exact finrank_selfDualSubspace (-o) hk hk₀ x

/-- **On an oriented Riemannian four-manifold, `Λ⁺` has rank three.** -/
@[simp]
theorem finrank_selfDualSubspace_two (o : Manifold.Orientation I M (Fin (2 + 2))) (x : M) :
    finrank ℝ (selfDualSubspace o x) = 3 := by
  rw [finrank_selfDualSubspace o even_two Nat.zero_lt_two x]
  decide

/-- **On an oriented Riemannian four-manifold, `Λ⁻` has rank three.** -/
@[simp]
theorem finrank_antiSelfDualSubspace_two (o : Manifold.Orientation I M (Fin (2 + 2))) (x : M) :
    finrank ℝ (antiSelfDualSubspace o x) = 3 := by
  rw [finrank_antiSelfDualSubspace o even_two Nat.zero_lt_two x]
  decide

end Fibrewise

/-! ### Smoothness of the projections and local subbundle frames -/

section SubbundleFrames

variable {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] {k : ℕ}

/-- **The self-dual projection `P⁺ = (1 + ⋆) / 2` is a `C^n` section of the endomorphism bundle**
of `Λᵏ T*M`, for a `C^n` metric on a `C^(n+1)` manifold. -/
theorem contMDiff_selfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) :
    ContMDiff I (I.prod 𝓘(ℝ, (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' ((E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
          TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ)
        x (selfDualProjCLM o x)) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  let F := E [⋀^Fin k]→L[ℝ] ℝ
  let V : M → Type _ := fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ
  have hid : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun y : M ↦ V y →L[ℝ] V y) x (.id ℝ (V x))) :=
    (contMDiff_hom_bundle_iff (F₁ := F) (F₂ := F) (E₁ := V) (E₂ := V)
      (fun x ↦ ContinuousLinearMap.id ℝ (V x))).2 contMDiff_id
  exact (contMDiff_const (c := (2⁻¹ : ℝ))).smul_section
    (hid.add_section (contMDiff_formHodgeStarCLM o rfl))

/-- **The anti-self-dual projection `P⁻ = (1 - ⋆) / 2` is a `C^n` section of the endomorphism
bundle** of `Λᵏ T*M`, for a `C^n` metric on a `C^(n+1)` manifold. -/
theorem contMDiff_antiSelfDualProjCLM (o : Manifold.Orientation I M (Fin (k + k))) :
    ContMDiff I (I.prod 𝓘(ℝ, (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' ((E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun y : M ↦ (TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
          TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ)
        x (antiSelfDualProjCLM o x)) := by
  simpa only [selfDualProjCLM_neg_orientation] using contMDiff_selfDualProjCLM (n := n) (-o)

/-- The fibrewise self-dual projection induces a `C^n` map on the total space of real `k`-forms. -/
theorem contMDiff_selfDualProj_totalSpace (o : Manifold.Orientation I M (Fin (k + k))) :
    ContMDiff (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) ↦
        TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
          p.proj (selfDualProjCLM o p.proj p.2)) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  exact (contMDiff_hom_bundle_iff (F₁ := E [⋀^Fin k]→L[ℝ] ℝ) (F₂ := E [⋀^Fin k]→L[ℝ] ℝ)
    (E₁ := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
    (E₂ := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) (selfDualProjCLM o)).1
    (contMDiff_selfDualProjCLM o)

/-- The fibrewise anti-self-dual projection induces a `C^n` map on the total space of real
`k`-forms. -/
theorem contMDiff_antiSelfDualProj_totalSpace (o : Manifold.Orientation I M (Fin (k + k))) :
    ContMDiff (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) ↦
        TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
          p.proj (antiSelfDualProjCLM o p.proj p.2)) := by
  simpa only [selfDualProjCLM_neg_orientation] using contMDiff_selfDualProj_totalSpace (n := n) (-o)

/-- **Local `C^n` subbundle frames for `Λ⁺` of prescribed constant rank `r`.** Whenever `k` is even
and every fibre `selfDualSubspace o x` has dimension `r`, `selfDualSubspace o` admits `C^n` local
subbundle frames indexed by `Fin r` near every point of `M`. -/
theorem hasLocalContMDiffSubbundleFrames_selfDualSubspace_of_finrank
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    {r : ℕ} (hr : ∀ x, finrank ℝ (selfDualSubspace o x) = r) :
    HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r) (selfDualSubspace o) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  let F := E [⋀^Fin k]→L[ℝ] ℝ
  let V : M → Type _ := fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ
  let e := trivializationAt F V x₀
  let A : M → F →L[ℝ] F := fun y ↦
    ContinuousLinearMap.inCoordinates F V F V x₀ y x₀ y (selfDualProjCLM o y)
  have hA : ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) n A e.baseSet := by
    intro y hy
    refine TauCeti.contMDiffWithinAt_clm_apply.2 fun u ↦ ?_
    have hsec : ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
        (fun z ↦ TotalSpace.mk' F (E := V) z (e.symm z u)) e.baseSet :=
      e.contMDiffOn_section_symm e.open_baseSet Subset.rfl contMDiffOn_const
    have hproj : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
        (fun z ↦ TotalSpace.mk' F (E := V) z (selfDualProjCLM o z (e.symm z u))) y :=
      (contMDiff_selfDualProj_totalSpace (n := n) o _).comp y
        (hsec.contMDiffAt (e.open_baseSet.mem_nhds hy))
    have he : (⟨y, selfDualProjCLM o y (e.symm y u)⟩ : TotalSpace F V) ∈ e.source :=
      e.mem_source.mpr hy
    have hcoord : ContMDiffAt I 𝓘(ℝ, F) n
        (fun z ↦ (e ⟨z, selfDualProjCLM o z (e.symm z u)⟩).2) y :=
      (((e.contMDiffOn (IB := I) (n := n)).contMDiffAt (e.open_source.mem_nhds he)).comp y
        hproj).snd
    have heq : (fun z ↦ (e ⟨z, selfDualProjCLM o z (e.symm z u)⟩).2) =ᶠ[𝓝 y] fun z ↦ A z u := by
      filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
      simp only [A, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
      rw [e.symmL_apply hz, Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hz]
    exact (hcoord.congr_of_eventuallyEq heq.symm).contMDiffWithinAt
  have hrank : ∀ y ∈ e.baseSet, finrank ℝ (A y).range = r := fun y hy ↦ by
    rw [ContinuousLinearMap.finrank_range_inCoordinates hy hy, range_selfDualProjCLM o hk y, hr y]
  obtain ⟨U, hUe, hU, hx₀U, X, hX, hXn⟩ :=
    e.exists_isSubbundleFrameOn_map_symmₗ e.open_baseSet Subset.rfl hA hrank
      (FiberBundle.mem_baseSet_trivializationAt F V x₀)
  refine ⟨U, hU, hx₀U, X, ⟨hX.continuousOn, hX.linearIndependent, fun {y} hy ↦ ?_⟩, hXn⟩
  have hy' : y ∈ e.baseSet := hUe hy
  rw [hX.span_eq hy, ContinuousLinearMap.range_inCoordinates hy' hy', range_selfDualProjCLM o hk y,
    ← Submodule.map_comp]
  have hid : (e.symmₗ ℝ y).comp
      ((e.continuousLinearEquivAt ℝ y hy').toLinearEquiv : V y →ₗ[ℝ] F) = LinearMap.id := by
    ext α
    simp [e.symmₗ_apply hy', Trivialization.continuousLinearEquivAt_apply,
      e.symm_apply_apply_mk hy' α]
  rw [hid, Submodule.map_id]

/-- **Local `C^n` subbundle frames for `Λ⁻` of prescribed constant rank `r`.** Whenever `k` is even
and every fibre `antiSelfDualSubspace o x` has dimension `r`, `antiSelfDualSubspace o` admits `C^n`
local subbundle frames indexed by `Fin r` near every point of `M`. -/
theorem hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_of_finrank
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    {r : ℕ} (hr : ∀ x, finrank ℝ (antiSelfDualSubspace o x) = r) :
    HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r) (antiSelfDualSubspace o) := by
  have hfun : antiSelfDualSubspace o = selfDualSubspace (-o) :=
    funext fun x ↦ (selfDualSubspace_neg_orientation o x).symm
  rw [hfun]
  exact hasLocalContMDiffSubbundleFrames_selfDualSubspace_of_finrank (-o) hk fun x ↦ by
    rw [selfDualSubspace_neg_orientation, hr x]

/-- **The self-dual eigenbundle `Λ⁺` is a `C^n` vector subbundle** of `Λᵏ T*M` of rank
`(k + k).choose k / 2`, in every even positive middle degree `k`. -/
theorem hasLocalContMDiffSubbundleFrames_selfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (hk₀ : 0 < k) :
    HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ)
      (Fin ((k + k).choose k / 2)) (selfDualSubspace o) :=
  hasLocalContMDiffSubbundleFrames_selfDualSubspace_of_finrank o hk
    (finrank_selfDualSubspace o hk hk₀)

/-- **The anti-self-dual eigenbundle `Λ⁻` is a `C^n` vector subbundle** of `Λᵏ T*M` of rank
`(k + k).choose k / 2`, in every even positive middle degree `k`. -/
theorem hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (hk₀ : 0 < k) :
    HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ)
      (Fin ((k + k).choose k / 2)) (antiSelfDualSubspace o) :=
  hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_of_finrank o hk
    (finrank_antiSelfDualSubspace o hk hk₀)

/-- **On an oriented Riemannian four-manifold, the self-dual two-form bundle `Λ⁺` has `C^n` local
frames of rank three** (model fibre `Fin 3 → ℝ`). -/
theorem hasLocalContMDiffSubbundleFrames_selfDualSubspace_two
    (o : Manifold.Orientation I M (Fin (2 + 2))) :
    HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin 2]→L[ℝ] ℝ) (Fin 3) (selfDualSubspace o) :=
  hasLocalContMDiffSubbundleFrames_selfDualSubspace_of_finrank o even_two
    (finrank_selfDualSubspace_two o)

/-- **On an oriented Riemannian four-manifold, the anti-self-dual two-form bundle `Λ⁻` has `C^n`
local frames of rank three** (model fibre `Fin 3 → ℝ`). -/
theorem hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two
    (o : Manifold.Orientation I M (Fin (2 + 2))) :
    HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin 2]→L[ℝ] ℝ) (Fin 3) (antiSelfDualSubspace o) :=
  hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_of_finrank o even_two
    (finrank_antiSelfDualSubspace_two o)

end SubbundleFrames

/-! ### Subbundle inclusions, smooth embeddings, retractions, and direct-sum splitting -/

section BundleSplitting

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

/-- The codomain-restricted bundle projection `Λᵏ T*M → Λ⁺` sending `(x, α)` to `(x, P⁺_x α)`. -/
@[expose]
def selfDualBundleProj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    TotalSpace (Fin r → ℝ) (fun x ↦ selfDualSubspace o x) :=
  ⟨p.proj, ⟨selfDualProjCLM o p.proj p.2, selfDualProjCLM_mem_selfDualSubspace o hk p.proj p.2⟩⟩

/-- The codomain-restricted bundle projection `Λᵏ T*M → Λ⁻` sending `(x, α)` to `(x, P⁻_x α)`. -/
@[expose]
def antiSelfDualBundleProj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    TotalSpace (Fin r → ℝ) (fun x ↦ antiSelfDualSubspace o x) :=
  ⟨p.proj, ⟨antiSelfDualProjCLM o p.proj p.2,
    antiSelfDualProjCLM_mem_antiSelfDualSubspace o hk p.proj p.2⟩⟩

/-- `selfDualBundleProj` preserves the base point. -/
@[simp]
theorem selfDualBundleProj_proj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    (selfDualBundleProj o hk r p).proj = p.proj :=
  (rfl)

/-- The fibre component of `selfDualBundleProj` coerces to `selfDualProjCLM`. -/
@[simp]
theorem selfDualBundleProj_coe_snd (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    ((selfDualBundleProj o hk r p).2 :
      TangentSpace I (selfDualBundleProj o hk r p).proj [⋀^Fin k]→L[ℝ] ℝ) =
      selfDualProjCLM o p.proj p.2 :=
  (rfl)

/-- `antiSelfDualBundleProj` preserves the base point. -/
@[simp]
theorem antiSelfDualBundleProj_proj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    (antiSelfDualBundleProj o hk r p).proj = p.proj :=
  (rfl)

/-- The fibre component of `antiSelfDualBundleProj` coerces to `antiSelfDualProjCLM`. -/
@[simp]
theorem antiSelfDualBundleProj_coe_snd (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    ((antiSelfDualBundleProj o hk r p).2 :
      TangentSpace I (antiSelfDualBundleProj o hk r p).proj [⋀^Fin k]→L[ℝ] ℝ) =
      antiSelfDualProjCLM o p.proj p.2 :=
  (rfl)

/-- `selfDualBundleProj` retracts the canonical inclusion `Λ⁺ → Λᵏ T*M` to the identity. -/
@[simp]
theorem selfDualBundleProj_inclusion (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ) (v : TotalSpace (Fin r → ℝ) (fun x ↦ selfDualSubspace o x)) :
    selfDualBundleProj o hk r ⟨v.proj, v.2⟩ = v := by
  rcases v with ⟨x, α, hα⟩
  exact congrArg (TotalSpace.mk x) (Subtype.ext (selfDualProjCLM_eq_self_of_mem hα))

/-- `antiSelfDualBundleProj` retracts the canonical inclusion `Λ⁻ → Λᵏ T*M` to the identity. -/
@[simp]
theorem antiSelfDualBundleProj_inclusion (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ) (v : TotalSpace (Fin r → ℝ) (fun x ↦ antiSelfDualSubspace o x)) :
    antiSelfDualBundleProj o hk r ⟨v.proj, v.2⟩ = v := by
  rcases v with ⟨x, α, hα⟩
  exact congrArg (TotalSpace.mk x) (Subtype.ext (antiSelfDualProjCLM_eq_self_of_mem hα))

section SmoothSplitting

variable {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

/-- The canonical inclusion `Λ⁺ → Λᵏ T*M` of total spaces is `C^n`. -/
theorem contMDiff_selfDualSubspace_inclusion (o : Manifold.Orientation I M (Fin (k + k)))
    {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o)) :
    letI := hsd.fiberBundle
    letI := hsd.vectorBundle
    ContMDiff (I.prod 𝓘(ℝ, Fin r → ℝ)) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun v : TotalSpace (Fin r → ℝ) (fun x ↦ selfDualSubspace o x) ↦
        (⟨v.proj, v.2⟩ :
          TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ))) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  exact hsd.contMDiff_totalSpace_inclusion

/-- The canonical inclusion `Λ⁻ → Λᵏ T*M` of total spaces is `C^n`. -/
theorem contMDiff_antiSelfDualSubspace_inclusion (o : Manifold.Orientation I M (Fin (k + k)))
    {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o)) :
    letI := hasd.fiberBundle
    letI := hasd.vectorBundle
    ContMDiff (I.prod 𝓘(ℝ, Fin r → ℝ)) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun v : TotalSpace (Fin r → ℝ) (fun x ↦ antiSelfDualSubspace o x) ↦
        (⟨v.proj, v.2⟩ :
          TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ))) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  exact hasd.contMDiff_totalSpace_inclusion

/-- **The total space of `Λ⁺` is `C^n`-smoothly embedded in `Λᵏ T*M`.** -/
theorem isSmoothEmbedding_selfDualSubspace_inclusion (o : Manifold.Orientation I M (Fin (k + k)))
    {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o)) :
    letI := hsd.fiberBundle
    Manifold.IsSmoothEmbedding (I.prod 𝓘(ℝ, Fin r → ℝ)) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun v : TotalSpace (Fin r → ℝ) (fun x ↦ selfDualSubspace o x) ↦
        (⟨v.proj, v.2⟩ :
          TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ))) := by
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  let := hsd.fiberBundle
  let := hsd.vectorBundle
  let := hsd.contMDiffVectorBundle
  exact isSmoothEmbedding_totalSpace_subbundle (contMDiff_selfDualSubspace_inclusion o hsd)

/-- **The total space of `Λ⁻` is `C^n`-smoothly embedded in `Λᵏ T*M`.** -/
theorem isSmoothEmbedding_antiSelfDualSubspace_inclusion
    (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o)) :
    letI := hasd.fiberBundle
    Manifold.IsSmoothEmbedding (I.prod 𝓘(ℝ, Fin r → ℝ)) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun v : TotalSpace (Fin r → ℝ) (fun x ↦ antiSelfDualSubspace o x) ↦
        (⟨v.proj, v.2⟩ :
          TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ))) := by
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  let := hasd.fiberBundle
  let := hasd.vectorBundle
  let := hasd.contMDiffVectorBundle
  exact isSmoothEmbedding_totalSpace_subbundle (contMDiff_antiSelfDualSubspace_inclusion o hasd)

variable [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- **The codomain-restricted bundle projection `Λᵏ T*M → Λ⁺` is `C^n`.** -/
theorem contMDiff_selfDualBundleProj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o)) :
    letI := hsd.fiberBundle
    letI := hsd.vectorBundle
    ContMDiff (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) (I.prod 𝓘(ℝ, Fin r → ℝ)) n
      (selfDualBundleProj o hk r) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  intro p
  exact hsd.contMDiffAt_totalSpace_mk (contMDiff_selfDualProj_totalSpace o p)
    fun q ↦ selfDualProjCLM_mem_selfDualSubspace o hk q.proj q.2

/-- **The codomain-restricted bundle projection `Λᵏ T*M → Λ⁻` is `C^n`.** -/
theorem contMDiff_antiSelfDualBundleProj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o)) :
    letI := hasd.fiberBundle
    letI := hasd.vectorBundle
    ContMDiff (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) (I.prod 𝓘(ℝ, Fin r → ℝ)) n
      (antiSelfDualBundleProj o hk r) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  intro p
  exact hasd.contMDiffAt_totalSpace_mk (contMDiff_antiSelfDualProj_totalSpace o p)
    fun q ↦ antiSelfDualProjCLM_mem_antiSelfDualSubspace o hk q.proj q.2

end SmoothSplitting

/-- **Smooth direct-sum decomposition `Λ⁺ ⊕ Λ⁻ ≃ₘ^n Λᵏ T*M` of total spaces.** On an oriented
`C^(n+1)` manifold with a `C^n` Riemannian metric, summing a self-dual and an anti-self-dual
`k`-form defines a `C^n` diffeomorphism from the direct-sum bundle `Λ⁺ ×ᵇ Λ⁻` onto `Λᵏ T*M`, with
inverse `(P⁺, P⁻)`. -/
def selfDualProdAntiSelfDualDiffeomorph (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) {r₁ r₂ : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r₁)
      (selfDualSubspace o))
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r₂)
      (antiSelfDualSubspace o)) :
    letI := hsd.fiberBundle
    letI := hasd.fiberBundle
    TotalSpace ((Fin r₁ → ℝ) × (Fin r₂ → ℝ))
      ((fun x ↦ selfDualSubspace o x) ×ᵇ fun x ↦ antiSelfDualSubspace o x)
      ≃ₘ^n⟮I.prod 𝓘(ℝ, (Fin r₁ → ℝ) × (Fin r₂ → ℝ)), I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)⟯
    TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  haveI := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  letI := hsd.fiberBundle
  letI := hasd.fiberBundle
  letI := hsd.vectorBundle
  letI := hasd.vectorBundle
  letI := hsd.contMDiffVectorBundle
  letI := hasd.contMDiffVectorBundle
  { toFun := fun v ↦
      ⟨v.proj, (v.2.1 : TangentSpace I v.proj [⋀^Fin k]→L[ℝ] ℝ) +
        (v.2.2 : TangentSpace I v.proj [⋀^Fin k]→L[ℝ] ℝ)⟩
    invFun := fun p ↦
      ⟨p.proj, ((selfDualBundleProj o hk r₁ p).2, (antiSelfDualBundleProj o hk r₂ p).2)⟩
    left_inv := by
      rintro ⟨x, α₁, α₂⟩
      have h₁ : selfDualProjCLM o x
          ((α₁ : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) + α₂) = α₁ := by
        rw [map_add, selfDualProjCLM_eq_self_of_mem α₁.2,
          selfDualProjCLM_eq_zero_iff.mpr α₂.2, add_zero]
      have h₂ : antiSelfDualProjCLM o x
          ((α₁ : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) + α₂) = α₂ := by
        rw [map_add, antiSelfDualProjCLM_eq_zero_iff.mpr α₁.2,
          antiSelfDualProjCLM_eq_self_of_mem α₂.2, zero_add]
      exact congrArg (TotalSpace.mk x) (Prod.ext (Subtype.ext h₁) (Subtype.ext h₂))
    right_inv := by
      rintro ⟨x, α⟩
      exact congrArg (TotalSpace.mk x) (selfDualProjCLM_add_antiSelfDualProjCLM_apply o x α)
    contMDiff_toFun := by
      intro v
      have hc := Bundle.contMDiffAt_totalSpace_prod_iff.mp
        (contMDiffAt_id (I := I.prod 𝓘(ℝ, (Fin r₁ → ℝ) × (Fin r₂ → ℝ))) (n := n) (x := v))
      have h₁ : ContMDiffAt (I.prod 𝓘(ℝ, (Fin r₁ → ℝ) × (Fin r₂ → ℝ)))
          (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
          (fun w ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
            (E := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
            w.proj (w.2.1 : TangentSpace I w.proj [⋀^Fin k]→L[ℝ] ℝ)) v :=
        (contMDiff_selfDualSubspace_inclusion o hsd ⟨v.proj, v.2.1⟩).comp v hc.1
      have h₂ : ContMDiffAt (I.prod 𝓘(ℝ, (Fin r₁ → ℝ) × (Fin r₂ → ℝ)))
          (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) n
          (fun w ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
            (E := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
            w.proj (w.2.2 : TangentSpace I w.proj [⋀^Fin k]→L[ℝ] ℝ)) v :=
        (contMDiff_antiSelfDualSubspace_inclusion o hasd ⟨v.proj, v.2.2⟩).comp v hc.2
      exact ContMDiffAt.add_sectionAlong (b := TotalSpace.proj) h₁ h₂
    contMDiff_invFun := by
      intro p
      exact Bundle.contMDiffAt_totalSpace_prod_iff.mpr
        ⟨contMDiff_selfDualBundleProj o hk hsd p,
          contMDiff_antiSelfDualBundleProj o hk hasd p⟩ }

/-- `selfDualProdAntiSelfDualDiffeomorph` sums the self-dual and anti-self-dual components in each
fibre. -/
@[simp]
theorem selfDualProdAntiSelfDualDiffeomorph_apply (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) {r₁ r₂ : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r₁)
      (selfDualSubspace o))
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r₂)
      (antiSelfDualSubspace o))
    (v : TotalSpace ((Fin r₁ → ℝ) × (Fin r₂ → ℝ))
      ((fun x ↦ selfDualSubspace o x) ×ᵇ fun x ↦ antiSelfDualSubspace o x)) :
    letI := hsd.fiberBundle
    letI := hasd.fiberBundle
    selfDualProdAntiSelfDualDiffeomorph n o hk hsd hasd v =
      ⟨v.proj, (v.2.1 : TangentSpace I v.proj [⋀^Fin k]→L[ℝ] ℝ) + v.2.2⟩ :=
  (rfl)

/-- The inverse of `selfDualProdAntiSelfDualDiffeomorph` splits a `k`-form into its self-dual and
anti-self-dual bundle projections. -/
@[simp]
theorem selfDualProdAntiSelfDualDiffeomorph_symm_apply (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) {r₁ r₂ : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r₁)
      (selfDualSubspace o))
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r₂)
      (antiSelfDualSubspace o))
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    letI := hsd.fiberBundle
    letI := hasd.fiberBundle
    (selfDualProdAntiSelfDualDiffeomorph n o hk hsd hasd).symm p =
      ⟨p.proj, ((selfDualBundleProj o hk r₁ p).2, (antiSelfDualBundleProj o hk r₂ p).2)⟩ :=
  (rfl)

/-- **Four-manifold bundle splitting `Λ⁺ ⊕ Λ⁻ ≃ₘ^n Λ² T*M`**, with rank-three model fibres
`Fin 3 → ℝ`. -/
def selfDualProdAntiSelfDualDiffeomorphTwo (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (2 + 2))) :
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := n) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := n) o).fiberBundle
    TotalSpace ((Fin 3 → ℝ) × (Fin 3 → ℝ))
      ((fun x ↦ selfDualSubspace o x) ×ᵇ fun x ↦ antiSelfDualSubspace o x)
      ≃ₘ^n⟮I.prod 𝓘(ℝ, (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)⟯
    TotalSpace (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  selfDualProdAntiSelfDualDiffeomorph n o even_two
    (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two o)
    (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two o)

end BundleSplitting

/-! ### Induced `C^n` Riemannian bundle metrics on `Λ⁺` and `Λ⁻` -/

section RiemannianMetric

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

/-- Restricting `alternatingFormInner` to any `C^n` subbundle of `Λᵏ T*M` given by local frames
yields a `C^n` Riemannian bundle metric on that subbundle. -/
private def alternatingFormSubbundleRiemannianMetric (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    {W : ∀ x : M, Submodule ℝ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)} {r : ℕ}
    (hW : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r) W) :
    letI := subbundleTopology (E [⋀^Fin k]→L[ℝ] ℝ) (F' := Fin r → ℝ) W
    letI := hW.fiberBundle
    letI := hW.vectorBundle
    ContMDiffRiemannianMetric I n (Fin r → ℝ) (fun x ↦ W x) :=
  haveI := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  letI := subbundleTopology (E [⋀^Fin k]→L[ℝ] ℝ) (F' := Fin r → ℝ) W
  letI := hW.fiberBundle
  letI := hW.vectorBundle
  letI := hW.contMDiffVectorBundle
  let g (x : M) :=
    IsBilinearMap.toContinuousBilinearMap (𝕜 := ℝ) (E := W x) (F := W x) (G := ℝ)
      (f := fun v w : W x ↦ alternatingFormInner (TangentSpace I x) k v.1 w.1)
      { add_left := fun _ _ _ ↦ by simp
        smul_left := fun _ _ _ ↦ by simp
        add_right := fun _ _ _ ↦ by simp
        smul_right := fun _ _ _ ↦ by simp }
  ContMDiffRiemannianMetric.ofPositiveDefiniteSection
    (⟨g, by
      have hg (x : M) (v w : W x) :
          g x v w = alternatingFormInner (TangentSpace I x) k v.1 w.1 := rfl
      intro x
      let F' := Fin r → ℝ
      let F := E [⋀^Fin k]→L[ℝ] ℝ
      let V : M → Type _ := fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ
      let eW := trivializationAt F' (fun y ↦ W y) x
      have hx : x ∈ eW.baseSet := FiberBundle.mem_baseSet_trivializationAt F' (fun y ↦ W y) x
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_clm_apply.2 fun u ↦
        TauCeti.contMDiffAt_clm_apply.2 fun w ↦ ?_⟩
      have hsec (c : F') : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
          (fun y ↦ TotalSpace.mk' F (E := V) y (eW.symm y c : V y)) x := by
        have hs : ContMDiffAt I (I.prod 𝓘(ℝ, F')) n
            (fun y ↦ TotalSpace.mk' F' (E := fun z ↦ W z) y (eW.symm y c)) x := by
          rw [contMDiffAt_section]
          refine (contMDiffAt_const (c := c)).congr_of_eventuallyEq ?_
          filter_upwards [eW.open_baseSet.mem_nhds hx] with y hy
          exact congr(Prod.snd $(eW.apply_mk_symm hy c))
        exact (hW.contMDiff_totalSpace_inclusion _).comp x hs
      have hinner := ContMDiffAt.alternatingFormInner_bundle (hsec u) (hsec w)
      refine hinner.congr_of_eventuallyEq ?_
      filter_upwards [eW.open_baseSet.mem_nhds hx] with y hy
      rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ) hy hy (by simp)]
      simp [hg, eW]⟩ :
      Manifold.BilinearSection I (Fin r → ℝ) (fun x ↦ W x) ℝ n)
    ((Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(Manifold.mem_symmetricBilinearSections _).2
        fun _ v w ↦ alternatingFormInner_comm v.1 w.1,
        fun _ v hv ↦ (alternatingFormInner_self_nonneg v.1).lt_of_ne'
          (mt (fun h0 ↦ Subtype.ext (alternatingFormInner_self_eq_zero.mp h0)) hv)⟩)

/-- **Induced `C^n` Riemannian bundle metric on `Λ⁺`**, obtained by restricting the Gram inner
product `alternatingFormInner` on exterior `k`-forms to each self-dual subspace. -/
def selfDualRiemannianMetric (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o)) :
    letI := hsd.fiberBundle
    letI := hsd.vectorBundle
    ContMDiffRiemannianMetric I n (Fin r → ℝ) (fun x ↦ selfDualSubspace o x) :=
  alternatingFormSubbundleRiemannianMetric n hsd

/-- `selfDualRiemannianMetric` evaluates on `v, w ∈ Λ⁺_x` as `alternatingFormInner`. -/
@[simp]
theorem selfDualRiemannianMetric_inner (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o))
    (x : M) (v w : selfDualSubspace o x) :
    letI := hsd.fiberBundle
    letI := hsd.vectorBundle
    (selfDualRiemannianMetric n o hsd).inner x v w =
      alternatingFormInner (TangentSpace I x) k
        (v : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
        (w : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) := by
  let := hsd.fiberBundle
  let := hsd.vectorBundle
  rw [selfDualRiemannianMetric, alternatingFormSubbundleRiemannianMetric,
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner]
  rfl

/-- **Induced `C^n` Riemannian bundle metric on `Λ⁻`**, obtained by restricting the Gram inner
product `alternatingFormInner` on exterior `k`-forms to each anti-self-dual subspace. -/
def antiSelfDualRiemannianMetric (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o)) :
    letI := hasd.fiberBundle
    letI := hasd.vectorBundle
    ContMDiffRiemannianMetric I n (Fin r → ℝ) (fun x ↦ antiSelfDualSubspace o x) :=
  alternatingFormSubbundleRiemannianMetric n hasd

/-- `antiSelfDualRiemannianMetric` evaluates on `v, w ∈ Λ⁻_x` as `alternatingFormInner`. -/
@[simp]
theorem antiSelfDualRiemannianMetric_inner (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o))
    (x : M) (v w : antiSelfDualSubspace o x) :
    letI := hasd.fiberBundle
    letI := hasd.vectorBundle
    (antiSelfDualRiemannianMetric n o hasd).inner x v w =
      alternatingFormInner (TangentSpace I x) k
        (v : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
        (w : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) := by
  let := hasd.fiberBundle
  let := hasd.vectorBundle
  rw [antiSelfDualRiemannianMetric, alternatingFormSubbundleRiemannianMetric,
    ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner]
  rfl

end RiemannianMetric

/-! ### Smooth sections of `Λ⁺` and `Λ⁻` vs. `SmoothForm.selfDualForms` -/

section Sections

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

/-- A section `s : ∀ x, selfDualSubspace o x` is `C^n` into the subbundle total space of `Λ⁺` if
and only if the underlying rough `k`-form `x ↦ (s x : Λᵏ T*_x M)` satisfies `IsSmoothForm I n`. -/
theorem contMDiff_section_selfDualSubspace_iff {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
    (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o))
    (s : ∀ x, selfDualSubspace o x) :
    letI := hsd.fiberBundle
    letI := hsd.vectorBundle
    ContMDiff I (I.prod 𝓘(ℝ, Fin r → ℝ)) n
        (fun x ↦ (⟨x, s x⟩ : TotalSpace (Fin r → ℝ) fun y ↦ selfDualSubspace o y)) ↔
      IsSmoothForm I n (fun x ↦ (s x : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (M := M) (I := I)
  let := hsd.fiberBundle
  let := hsd.vectorBundle
  rw [isSmoothForm_def]
  exact ⟨fun hs ↦ (contMDiff_selfDualSubspace_inclusion o hsd).comp hs,
    fun hφ x ↦ hsd.contMDiffAt_totalSpace_mk (hφ x) fun y ↦ (s y).2⟩

/-- A section `s : ∀ x, antiSelfDualSubspace o x` is `C^n` into the subbundle total space of `Λ⁻`
if and only if the underlying rough `k`-form `x ↦ (s x : Λᵏ T*_x M)` satisfies
`IsSmoothForm I n`. -/
theorem contMDiff_section_antiSelfDualSubspace_iff {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
    (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I n (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o))
    (s : ∀ x, antiSelfDualSubspace o x) :
    letI := hasd.fiberBundle
    letI := hasd.vectorBundle
    ContMDiff I (I.prod 𝓘(ℝ, Fin r → ℝ)) n
        (fun x ↦ (⟨x, s x⟩ : TotalSpace (Fin r → ℝ) fun y ↦ antiSelfDualSubspace o y)) ↔
      IsSmoothForm I n (fun x ↦ (s x : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (M := M) (I := I)
  let := hasd.fiberBundle
  let := hasd.vectorBundle
  rw [isSmoothForm_def]
  exact ⟨fun hs ↦ (contMDiff_antiSelfDualSubspace_inclusion o hasd).comp hs,
    fun hφ x ↦ hasd.contMDiffAt_totalSpace_mk (hφ x) fun y ↦ (s y).2⟩

section SmoothInfty

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Linear equivalence between smooth sections of `Λ⁺` and `SmoothForm.selfDualForms`.** -/
def selfDualContMDiffSectionEquiv (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I ∞ (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o)) :
    letI := hsd.fiberBundle
    letI := hsd.vectorBundle
    ContMDiffSection I (Fin r → ℝ) ∞ (fun x ↦ selfDualSubspace o x) ≃ₗ[ℝ]
      SmoothForm.selfDualForms o :=
  haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  letI := hsd.fiberBundle
  letI := hsd.vectorBundle
  { toFun := fun s ↦
      ⟨⟨fun x ↦ (s x : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ),
          ((contMDiff_section_selfDualSubspace_iff o hsd s).1 s.contMDiff).mem_smoothBundleForms⟩,
        SmoothForm.coe_mem_selfDualForms_iff.1
          (RoughForm.mem_selfDualForms_iff_forall_mem_selfDualSubspace.2 fun x ↦ (s x).2)⟩
    invFun := fun α ↦
      { toFun := fun x ↦
          ⟨((α : SmoothForm I M ℝ k) : RoughForm I M ℝ k) x,
            RoughForm.mem_selfDualForms_iff_forall_mem_selfDualSubspace.1
              (SmoothForm.coe_mem_selfDualForms_iff.2 α.2) x⟩
        contMDiff_toFun :=
          (contMDiff_section_selfDualSubspace_iff o hsd _).2 α.1.isSmoothForm }
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    left_inv := fun s ↦ by
      ext x
      rfl
    right_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl) }

/-- A smooth section of `Λ⁺` corresponds under `selfDualContMDiffSectionEquiv` to the smooth form
with the same fibrewise values. -/
@[simp]
theorem selfDualContMDiffSectionEquiv_apply_coe (o : Manifold.Orientation I M (Fin (k + k)))
    {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I ∞ (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o))
    (s : letI := hsd.fiberBundle; letI := hsd.vectorBundle
      ContMDiffSection I (Fin r → ℝ) ∞ (fun x ↦ selfDualSubspace o x))
    (x : M) :
    letI := hsd.fiberBundle
    letI := hsd.vectorBundle
    ((selfDualContMDiffSectionEquiv o hsd s : SmoothForm I M ℝ k) : RoughForm I M ℝ k) x =
      (s x : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  (rfl)

/-- `selfDualContMDiffSectionEquiv.symm` evaluates at `x` to the value of the smooth self-dual
form at `x`. -/
@[simp]
theorem selfDualContMDiffSectionEquiv_symm_apply_coe (o : Manifold.Orientation I M (Fin (k + k)))
    {r : ℕ}
    (hsd : HasLocalContMDiffSubbundleFrames I ∞ (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (selfDualSubspace o))
    (α : SmoothForm.selfDualForms o) (x : M) :
    letI := hsd.fiberBundle
    letI := hsd.vectorBundle
    (((selfDualContMDiffSectionEquiv o hsd).symm α) x :
      TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) =
      ((α : SmoothForm I M ℝ k) : RoughForm I M ℝ k) x :=
  (rfl)

/-- **Linear equivalence between smooth sections of `Λ⁻` and `SmoothForm.antiSelfDualForms`.** -/
def antiSelfDualContMDiffSectionEquiv (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I ∞ (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o)) :
    letI := hasd.fiberBundle
    letI := hasd.vectorBundle
    ContMDiffSection I (Fin r → ℝ) ∞ (fun x ↦ antiSelfDualSubspace o x) ≃ₗ[ℝ]
      SmoothForm.antiSelfDualForms o :=
  haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  letI := hasd.fiberBundle
  letI := hasd.vectorBundle
  { toFun := fun s ↦
      ⟨⟨fun x ↦ (s x : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ),
          ((contMDiff_section_antiSelfDualSubspace_iff o hasd s).1
            s.contMDiff).mem_smoothBundleForms⟩,
        SmoothForm.coe_mem_antiSelfDualForms_iff.1
          (RoughForm.mem_antiSelfDualForms_iff_forall_mem_antiSelfDualSubspace.2
            fun x ↦ (s x).2)⟩
    invFun := fun α ↦
      { toFun := fun x ↦
          ⟨((α : SmoothForm I M ℝ k) : RoughForm I M ℝ k) x,
            RoughForm.mem_antiSelfDualForms_iff_forall_mem_antiSelfDualSubspace.1
              (SmoothForm.coe_mem_antiSelfDualForms_iff.2 α.2) x⟩
        contMDiff_toFun :=
          (contMDiff_section_antiSelfDualSubspace_iff o hasd _).2 α.1.isSmoothForm }
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    left_inv := fun s ↦ by
      ext x
      rfl
    right_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl) }

/-- A smooth section of `Λ⁻` corresponds under `antiSelfDualContMDiffSectionEquiv` to the smooth
form with the same fibrewise values. -/
@[simp]
theorem antiSelfDualContMDiffSectionEquiv_apply_coe (o : Manifold.Orientation I M (Fin (k + k)))
    {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I ∞ (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o))
    (s : letI := hasd.fiberBundle; letI := hasd.vectorBundle
      ContMDiffSection I (Fin r → ℝ) ∞ (fun x ↦ antiSelfDualSubspace o x))
    (x : M) :
    letI := hasd.fiberBundle
    letI := hasd.vectorBundle
    ((antiSelfDualContMDiffSectionEquiv o hasd s : SmoothForm I M ℝ k) : RoughForm I M ℝ k) x =
      (s x : TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  (rfl)

/-- `antiSelfDualContMDiffSectionEquiv.symm` evaluates at `x` to the value of the smooth
anti-self-dual form at `x`. -/
@[simp]
theorem antiSelfDualContMDiffSectionEquiv_symm_apply_coe
    (o : Manifold.Orientation I M (Fin (k + k))) {r : ℕ}
    (hasd : HasLocalContMDiffSubbundleFrames I ∞ (E [⋀^Fin k]→L[ℝ] ℝ) (Fin r)
      (antiSelfDualSubspace o))
    (α : SmoothForm.antiSelfDualForms o) (x : M) :
    letI := hasd.fiberBundle
    letI := hasd.vectorBundle
    (((antiSelfDualContMDiffSectionEquiv o hasd).symm α) x :
      TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) =
      ((α : SmoothForm I M ℝ k) : RoughForm I M ℝ k) x :=
  (rfl)

/-- **Four-manifold smooth self-dual section equivalence**: on an oriented smooth Riemannian
four-manifold, smooth sections of the rank-three vector bundle `Λ⁺` (model fibre `Fin 3 → ℝ`) are
linearly equivalent to `SmoothForm.selfDualForms o`. -/
def selfDualContMDiffSectionEquivTwo (o : Manifold.Orientation I M (Fin (2 + 2))) :
    haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := ∞) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := ∞) o).vectorBundle
    ContMDiffSection I (Fin 3 → ℝ) ∞ (fun x ↦ selfDualSubspace o x) ≃ₗ[ℝ]
      SmoothForm.selfDualForms o :=
  haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  selfDualContMDiffSectionEquiv o (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two o)

/-- **Four-manifold smooth anti-self-dual section equivalence**: on an oriented smooth Riemannian
four-manifold, smooth sections of the rank-three vector bundle `Λ⁻` (model fibre `Fin 3 → ℝ`) are
linearly equivalent to `SmoothForm.antiSelfDualForms o`. -/
def antiSelfDualContMDiffSectionEquivTwo (o : Manifold.Orientation I M (Fin (2 + 2))) :
    haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := ∞) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := ∞) o).vectorBundle
    ContMDiffSection I (Fin 3 → ℝ) ∞ (fun x ↦ antiSelfDualSubspace o x) ≃ₗ[ℝ]
      SmoothForm.antiSelfDualForms o :=
  haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  antiSelfDualContMDiffSectionEquiv o (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two o)

end SmoothInfty

end Sections

end TauCeti
