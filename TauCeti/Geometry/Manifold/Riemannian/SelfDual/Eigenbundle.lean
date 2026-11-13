/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.AlternatingForm
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# The self-dual and anti-self-dual eigenbundles of differential forms

On an oriented Riemannian manifold `M` of dimension `k + k` with `k` even, the fibrewise Hodge star
`TauCeti.formHodgeStarCLM` on middle-degree real `k`-forms is a self-adjoint involution on every
fibre `Λᵏ T*_x M`. Each fibre splits orthogonally into its `+1`-eigenspace `Λ⁺_x` of self-dual
covectors (`TauCeti.selfDualSubspace`) and its `-1`-eigenspace `Λ⁻_x` of anti-self-dual covectors
(`TauCeti.antiSelfDualSubspace`), cut out by the complementary projections
`P⁺_x = (1 + ⋆) / 2` (`TauCeti.selfDualProjCLM`, `TauCeti.selfDualProj`) and `P⁻_x = (1 - ⋆) / 2`
(`TauCeti.antiSelfDualProjCLM`, `TauCeti.antiSelfDualProj`), both of dimension
`(k + k).choose k / 2` when `0 < k` (`3` when `k = 2`); see
`TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic` for this fibrewise theory.

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
* the pointwise Gram inner product `TauCeti.alternatingFormInner` restricts via
  `TauCeti.alternatingFormSubbundleRiemannianMetric` to `C^n` Riemannian bundle metrics on `Λ⁺` and
  `Λ⁻` (`TauCeti.selfDualRiemannianMetric` and `TauCeti.antiSelfDualRiemannianMetric`);
* smooth sections `ContMDiffSection` of `Λ⁺` and `Λ⁻` correspond `ℝ`-linearly to the submodules
  `TauCeti.SmoothForm.selfDualForms` and `TauCeti.SmoothForm.antiSelfDualForms` of smooth
  self-dual and anti-self-dual differential forms (`TauCeti.selfDualContMDiffSectionEquiv` and
  `TauCeti.antiSelfDualContMDiffSectionEquiv`).

## Main definitions

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

section SubbundleTopology

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

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

end SubbundleTopology

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
  simp_rw [selfDualProjCLM_def]
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
    have hsec := ((trivializationAt (F →L[ℝ] F) (fun y ↦ V y →L[ℝ] V y) x₀).contMDiffOn_section_iff
      e.open_baseSet (fun _ hy ↦ by rw [hom_trivializationAt_baseSet]; exact ⟨hy, hy⟩)).mp
      (contMDiff_selfDualProjCLM (n := n) o).contMDiffOn
    exact hsec.congr fun y _ ↦ by simp [A, hom_trivializationAt_apply]
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
def selfDualBundleProj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    TotalSpace (Fin r → ℝ) (fun x ↦ selfDualSubspace o x) :=
  ⟨p.proj, selfDualProj o hk p.proj p.2⟩

/-- The codomain-restricted bundle projection `Λᵏ T*M → Λ⁻` sending `(x, α)` to `(x, P⁻_x α)`. -/
def antiSelfDualBundleProj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    TotalSpace (Fin r → ℝ) (fun x ↦ antiSelfDualSubspace o x) :=
  ⟨p.proj, antiSelfDualProj o hk p.proj p.2⟩

/-- `selfDualBundleProj` acts on `(x, α)` by `selfDualProj` in the fibre over `x`. -/
@[simp]
theorem selfDualBundleProj_apply (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    selfDualBundleProj o hk r p = ⟨p.proj, selfDualProj o hk p.proj p.2⟩ :=
  (rfl)

/-- `antiSelfDualBundleProj` acts on `(x, α)` by `antiSelfDualProj` in the fibre over `x`. -/
@[simp]
theorem antiSelfDualBundleProj_apply (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    antiSelfDualBundleProj o hk r p = ⟨p.proj, antiSelfDualProj o hk p.proj p.2⟩ :=
  (rfl)

/-- `selfDualBundleProj` preserves the base point. -/
theorem selfDualBundleProj_proj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    (selfDualBundleProj o hk r p).proj = p.proj :=
  (rfl)

/-- `antiSelfDualBundleProj` preserves the base point. -/
theorem antiSelfDualBundleProj_proj (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ)
    (p : TotalSpace (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)) :
    (antiSelfDualBundleProj o hk r p).proj = p.proj :=
  (rfl)

/-- `selfDualBundleProj` retracts the canonical inclusion `Λ⁺ → Λᵏ T*M` to the identity. -/
theorem selfDualBundleProj_inclusion (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ) (v : TotalSpace (Fin r → ℝ) (fun x ↦ selfDualSubspace o x)) :
    selfDualBundleProj o hk r ⟨v.proj, v.2⟩ = v := by
  rcases v with ⟨x, α⟩
  simp

/-- `antiSelfDualBundleProj` retracts the canonical inclusion `Λ⁻ → Λᵏ T*M` to the identity. -/
theorem antiSelfDualBundleProj_inclusion (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k)
    (r : ℕ) (v : TotalSpace (Fin r → ℝ) (fun x ↦ antiSelfDualSubspace o x)) :
    antiSelfDualBundleProj o hk r ⟨v.proj, v.2⟩ = v := by
  rcases v with ⟨x, α⟩
  simp

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
  let := hsd.fiberBundle
  let := hsd.vectorBundle
  intro p
  refine (hsd.contMDiffAt_totalSpace_mk (contMDiff_selfDualProj_totalSpace o p)
    fun q ↦ selfDualProjCLM_mem_selfDualSubspace o hk q.proj q.2).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun q ↦
    congrArg (TotalSpace.mk q.proj) (Subtype.ext (coe_selfDualProj_apply o hk q.proj q.2))

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
  let := hasd.fiberBundle
  let := hasd.vectorBundle
  intro p
  refine (hasd.contMDiffAt_totalSpace_mk (contMDiff_antiSelfDualProj_totalSpace o p)
    fun q ↦ antiSelfDualProjCLM_mem_antiSelfDualSubspace o hk q.proj q.2).congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun q ↦
    congrArg (TotalSpace.mk q.proj) (Subtype.ext (coe_antiSelfDualProj_apply o hk q.proj q.2))

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
      ⟨p.proj, (selfDualProj o hk p.proj p.2, antiSelfDualProj o hk p.proj p.2)⟩
    left_inv := by
      rintro ⟨x, α₁, α₂⟩
      apply congrArg (TotalSpace.mk x)
      refine Prod.ext ?_ ?_ <;> simp
    right_inv := by
      rintro ⟨x, α⟩
      apply congrArg (TotalSpace.mk x)
      simp
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
anti-self-dual fibre projections. -/
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
      ⟨p.proj, (selfDualProj o hk p.proj p.2, antiSelfDualProj o hk p.proj p.2)⟩ :=
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

/-- `selfDualProdAntiSelfDualDiffeomorphTwo` sums the self-dual and anti-self-dual two-form
components in each fibre. -/
@[simp]
theorem selfDualProdAntiSelfDualDiffeomorphTwo_apply (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (2 + 2)))
    (v : TotalSpace ((Fin 3 → ℝ) × (Fin 3 → ℝ))
      ((fun x ↦ selfDualSubspace o x) ×ᵇ fun x ↦ antiSelfDualSubspace o x)) :
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := n) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := n) o).fiberBundle
    selfDualProdAntiSelfDualDiffeomorphTwo n o v =
      ⟨v.proj, (v.2.1 : TangentSpace I v.proj [⋀^Fin 2]→L[ℝ] ℝ) + v.2.2⟩ :=
  (rfl)

/-- The inverse of `selfDualProdAntiSelfDualDiffeomorphTwo` splits a two-form into its self-dual
and anti-self-dual fibre projections. -/
@[simp]
theorem selfDualProdAntiSelfDualDiffeomorphTwo_symm_apply (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (o : Manifold.Orientation I M (Fin (2 + 2)))
    (p : TotalSpace (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)) :
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := n) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := n) o).fiberBundle
    (selfDualProdAntiSelfDualDiffeomorphTwo n o).symm p =
      ⟨p.proj, (selfDualProj o even_two p.proj p.2, antiSelfDualProj o even_two p.proj p.2)⟩ :=
  (rfl)

end BundleSplitting

/-! ### Induced `C^n` Riemannian bundle metrics on `Λ⁺` and `Λ⁻` -/

section RiemannianMetric

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {k : ℕ}

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
  haveI := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  alternatingFormSubbundleRiemannianMetric hsd

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
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  exact alternatingFormSubbundleRiemannianMetric_inner hsd x v w

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
  haveI := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  alternatingFormSubbundleRiemannianMetric hasd

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
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  exact alternatingFormSubbundleRiemannianMetric_inner hasd x v w

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

/-- A smooth section of `Λ⁺` on a four-manifold corresponds under
`selfDualContMDiffSectionEquivTwo` to the smooth two-form with the same fibrewise values. -/
@[simp]
theorem selfDualContMDiffSectionEquivTwo_apply_coe (o : Manifold.Orientation I M (Fin (2 + 2)))
    (s : haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
      letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := ∞) o).fiberBundle
      letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := ∞) o).vectorBundle
      ContMDiffSection I (Fin 3 → ℝ) ∞ (fun x ↦ selfDualSubspace o x))
    (x : M) :
    haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := ∞) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := ∞) o).vectorBundle
    ((selfDualContMDiffSectionEquivTwo o s : SmoothForm I M ℝ 2) : RoughForm I M ℝ 2) x =
      (s x : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  (rfl)

/-- `selfDualContMDiffSectionEquivTwo.symm` evaluates at `x` to the value of the smooth self-dual
two-form at `x`. -/
@[simp]
theorem selfDualContMDiffSectionEquivTwo_symm_apply_coe
    (o : Manifold.Orientation I M (Fin (2 + 2)))
    (α : SmoothForm.selfDualForms o) (x : M) :
    haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := ∞) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_selfDualSubspace_two (n := ∞) o).vectorBundle
    (((selfDualContMDiffSectionEquivTwo o).symm α) x :
      TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) =
      ((α : SmoothForm I M ℝ 2) : RoughForm I M ℝ 2) x :=
  (rfl)

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

/-- A smooth section of `Λ⁻` on a four-manifold corresponds under
`antiSelfDualContMDiffSectionEquivTwo` to the smooth two-form with the same fibrewise values. -/
@[simp]
theorem antiSelfDualContMDiffSectionEquivTwo_apply_coe
    (o : Manifold.Orientation I M (Fin (2 + 2)))
    (s : haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
      letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := ∞) o).fiberBundle
      letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := ∞) o).vectorBundle
      ContMDiffSection I (Fin 3 → ℝ) ∞ (fun x ↦ antiSelfDualSubspace o x))
    (x : M) :
    haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := ∞) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := ∞) o).vectorBundle
    ((antiSelfDualContMDiffSectionEquivTwo o s : SmoothForm I M ℝ 2) : RoughForm I M ℝ 2) x =
      (s x : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  (rfl)

/-- `antiSelfDualContMDiffSectionEquivTwo.symm` evaluates at `x` to the value of the smooth
anti-self-dual two-form at `x`. -/
@[simp]
theorem antiSelfDualContMDiffSectionEquivTwo_symm_apply_coe
    (o : Manifold.Orientation I M (Fin (2 + 2)))
    (α : SmoothForm.antiSelfDualForms o) (x : M) :
    haveI : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := ∞) o).fiberBundle
    letI := (hasLocalContMDiffSubbundleFrames_antiSelfDualSubspace_two (n := ∞) o).vectorBundle
    (((antiSelfDualContMDiffSectionEquivTwo o).symm α) x :
      TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) =
      ((α : SmoothForm I M ℝ 2) : RoughForm I M ℝ 2) x :=
  (rfl)

end SmoothInfty

end Sections

end TauCeti
