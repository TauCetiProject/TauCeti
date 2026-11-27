/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import TauCeti.Analysis.LocallyConvex.Polar
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.ContMDiff.QuotientRange
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight

/-!
# The annihilator subbundle of a distribution

Let `D` be a distribution on a manifold `M`, assigning to every point `x` a subspace `D x` of the
tangent space. Its **annihilator** at `x` (`TauCeti.CotangentBundle.annihilatorSpace I D x`) is the
space `D⁰_x ⊆ T*_x M` of covectors vanishing on `D x`. For a contact structure `ξ` this is the
line `ξ⁰`, canonically the dual of the contact line `TM ⧸ ξ`; its nonzero elements are the values
of the local contact forms defining `ξ`, and the complement of its zero section is the
symplectization of `ξ`, which needs no coorientation.

This file shows that the annihilators of a `C^n` distribution of rank `k` on a manifold of
dimension `k + r` form a `C^n` vector subbundle of rank `r` of the cotangent bundle `T*M`.

* **Local annihilating coframes.** Near every point there are `r` covector fields of class `C^n`,
  linearly independent at every point of a neighbourhood, which span the annihilators there
  (`TauCeti.IsContMDiffDistribution.exists_annihilatorSpace_frame`); so `D` is locally the common
  kernel of `r` independent `C^n` covector fields
  (`TauCeti.IsContMDiffDistribution.exists_local_annihilating_coframe`). The coframe is built in one
  tangent-bundle trivialization: if `A y : 𝕜ᵏ → E` is the coordinate operator of a local frame of
  `D`, then for a fixed complement `Q ≅ 𝕜ʳ` of the range of `A x` the quotient coordinates
  `E → Q` along the range of `A y` are, near `x`, `r` independent covectors depending smoothly on
  `y` and vanishing on the frame
  (`ContMDiffOn.exists_contMDiffOn_linearIndependent_comp_eq_zero`). This adapts the chart
  construction of conormal frames (`chartConormalFrame` in
  `TauCeti/Geometry/Manifold/VectorBundle/Cotangent/Conormal/Subbundle.lean`). The corank-one case
  is `TauCeti.IsContMDiffDistribution.exists_local_annihilator`.
* **The annihilator bundle.** By the smooth local frame criterion
  `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`, the annihilators, with the
  subspace topology of `T*M`, are a `C^n` vector bundle with fibre `Fin r → 𝕜`
  (`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`,
  `TauCeti.IsContMDiffDistribution.annihilatorVectorBundle`,
  `TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle`), and their inclusion
  `TauCeti.CotangentBundle.annihilatorInclusion` into `T*M` is a `C^n` smooth embedding
  (`TauCeti.IsContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion`). In particular a
  covector field with values in the annihilators is a continuous section of `D⁰` exactly when it
  is a continuous section of `T*M`
  (`TauCeti.CotangentBundle.continuous_totalSpaceMk_annihilatorSpace_iff`).

Along the zero section, the differential of the inclusion is the identity in the splitting of
tangent spaces at zero vectors into base and fibre (`TauCeti.Bundle.zeroSectionTangentEquiv`): a
tangent vector of `D⁰` with horizontal part `v` and vertical part `a ∈ D⁰_x` goes to the tangent
vector of `T*M` with coordinates `(v, a)` in the preferred chart at the zero covector
(`TauCeti.CotangentBundle.mfderiv_annihilatorInclusion_zeroSection`).

Pointwise, `D x` and `D⁰_x` have complementary dimensions
(`TauCeti.CotangentBundle.finrank_add_finrank_annihilatorSpace`), `D x` is recovered as the common
kernel of `D⁰_x` (`TauCeti.CotangentBundle.mem_iff_forall_mem_annihilatorSpace`), and for a
hyperplane `D x = ker α` the annihilator is the line spanned by `α`
(`TauCeti.CotangentBundle.annihilatorSpace_eq_span_singleton`).

A vector field `V` on `M` determines the function `F_V(z) = z(V x)` on the annihilators
(`TauCeti.CotangentBundle.annihilatorPairing`). It is linear on each fibre
(`TauCeti.CotangentBundle.annihilatorPairing_mk_smul`), smooth for smooth `V` and `D`
(`TauCeti.CotangentBundle.contMDiff_annihilatorPairing`, pointwise
`TauCeti.CotangentBundle.contMDiffAt_annihilatorPairing`), and depends exactly on `V` modulo `D`:
`F_V = F_W` if and only if `V - W` is tangent to `D`
(`TauCeti.CotangentBundle.annihilatorPairing_eq_annihilatorPairing_iff`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 19.5
  (local annihilating coframes of a distribution).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1
  and Appendix B (the annihilator line of a contact structure and its symplectization).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

namespace CotangentBundle

/-! ### The annihilator spaces -/

variable (I) in
/-- The **annihilator** `D⁰_x ⊆ T*_x M` of a distribution `D` at `x`: the covectors vanishing on
`D x`. -/
def annihilatorSpace (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) (x : M) :
    Submodule 𝕜 (TangentSpace I x →L[𝕜] 𝕜) :=
  StrongDual.polarSubmodule 𝕜 (D x)

/-- The annihilator of `D` at `x` is the polar `StrongDual.polarSubmodule` of `D x`. -/
theorem annihilatorSpace_def (x : M) :
    annihilatorSpace I D x = StrongDual.polarSubmodule 𝕜 (D x) := (rfl)

/-- A covector lies in the annihilator of `D` at `x` when it vanishes on `D x`. -/
@[simp]
theorem mem_annihilatorSpace_iff {x : M} {p : TangentSpace I x →L[𝕜] 𝕜} :
    p ∈ annihilatorSpace I D x ↔ ∀ v ∈ D x, p v = 0 :=
  StrongDual.mem_polarSubmodule 𝕜 (D x) p

/-- A covector lies in the annihilator of `D` at `x` when its kernel contains `D x`. -/
theorem mem_annihilatorSpace_iff_le_ker {x : M} {p : TangentSpace I x →L[𝕜] 𝕜} :
    p ∈ annihilatorSpace I D x ↔ D x ≤ LinearMap.ker p.toLinearMap := by
  rw [mem_annihilatorSpace_iff]
  exact ⟨fun h v hv ↦ LinearMap.mem_ker.mpr (h v hv), fun h v hv ↦ LinearMap.mem_ker.mp (h hv)⟩

/-- **The annihilator of a hyperplane.** If a covector `α` at `x` has kernel `D x`, then the
annihilator of `D` at `x` is the line spanned by `α`. -/
theorem annihilatorSpace_eq_span_singleton {x : M} {α : TangentSpace I x →L[𝕜] 𝕜}
    (hker : LinearMap.ker α.toLinearMap = D x) :
    annihilatorSpace I D x = 𝕜 ∙ α := by
  rw [annihilatorSpace_def, ← hker]
  exact StrongDual.polarSubmodule_ker_eq_span_singleton α

section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- **The dimension of the annihilator.** On a finite-dimensional manifold, `D x` and its
annihilator have complementary dimensions: `dim D x + dim D⁰_x = dim M`. -/
theorem finrank_add_finrank_annihilatorSpace (x : M) :
    finrank 𝕜 (D x) + finrank 𝕜 (annihilatorSpace I D x) = finrank 𝕜 E := by
  rw [annihilatorSpace_def]
  exact StrongDual.finrank_add_finrank_polarSubmodule (𝕜 := 𝕜) (E := E) (D x)

/-- On a finite-dimensional manifold a tangent vector lies in `D x` exactly when every covector
of the annihilator `D⁰_x` vanishes on it: `D x` is the common kernel of its annihilator. -/
theorem mem_iff_forall_mem_annihilatorSpace {x : M} {v : TangentSpace I x} :
    v ∈ D x ↔ ∀ p ∈ annihilatorSpace I D x, p v = 0 := by
  rw [annihilatorSpace_def]
  exact StrongDual.mem_iff_forall_mem_polarSubmodule (E := E) (D x)

end FiniteDimensional

/-! ### The inclusion into the cotangent bundle -/

section Inclusion

variable (P : Type*) (I D)

/-- The canonical map from the total space of the annihilators of `D` into `T*M`, sending `(x, p)`
with `p ∈ D⁰_x` to `(x, p)`. The model-fibre parameter `P` of `Bundle.TotalSpace` plays no
role. -/
def annihilatorInclusion (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    CotangentBundle I M :=
  ⟨z.proj, z.snd⟩

@[simp]
theorem annihilatorInclusion_proj (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    (annihilatorInclusion I D P z).proj = z.proj := (rfl)

@[simp]
theorem annihilatorInclusion_snd (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    (annihilatorInclusion I D P z).snd = (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) := (rfl)

theorem annihilatorInclusion_apply (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    annihilatorInclusion I D P z = ⟨z.proj, z.snd⟩ := (rfl)

@[simp]
theorem annihilatorInclusion_mk' (x : M) (p : annihilatorSpace I D x) :
    annihilatorInclusion I D P (TotalSpace.mk' P x p) =
      TotalSpace.mk' (E →L[𝕜] 𝕜) x (p : TangentSpace I x →L[𝕜] 𝕜) := (rfl)

/-- `annihilatorInclusion` sends the zero covector in the annihilator over `x` to the zero covector
in `T*M` over `x`. -/
@[simp]
theorem annihilatorInclusion_zeroSection (x : M) :
    annihilatorInclusion I D P (zeroSection P (fun x ↦ annihilatorSpace I D x) x) =
      zeroSection (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x := (rfl)

/-- The image of the annihilator inclusion consists of the covectors annihilating `D` at their
base points. -/
@[simp]
theorem range_annihilatorInclusion :
    range (annihilatorInclusion I D P) = {w | w.snd ∈ annihilatorSpace I D w.proj} := by
  ext ⟨x, p⟩
  exact ⟨by rintro ⟨⟨y, q⟩, h⟩; cases h; exact q.property, fun hp ↦ ⟨⟨x, ⟨p, hp⟩⟩, rfl⟩⟩

/-- The annihilator inclusion is injective. -/
theorem annihilatorInclusion_injective : Injective (annihilatorInclusion I D P) :=
  injective_totalSpace_subbundle (E →L[𝕜] 𝕜) P (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)
    (annihilatorSpace I D)

variable {I D P} in
/-- Two covectors annihilating `D` are equal if they have the same base point and take the same
values. -/
theorem totalSpace_annihilatorSpace_ext {z w : TotalSpace P fun x ↦ annihilatorSpace I D x}
    (hproj : z.proj = w.proj)
    (h : ∀ v : TangentSpace I z.proj, (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) v =
      (w.snd : TangentSpace I w.proj →L[𝕜] 𝕜) v) : z = w :=
  annihilatorInclusion_injective I D P (CotangentBundle.ext hproj h)

variable [IsManifold I 1 M]

/-- The total space of the annihilators of `D` carries the subspace topology
(`TauCeti.subbundleTopology`) of the cotangent bundle. The model-fibre parameter `P` of
`Bundle.TotalSpace` plays no role. -/
instance instTopologicalSpaceTotalSpaceAnnihilatorSpace :
    TopologicalSpace (TotalSpace P fun x ↦ annihilatorSpace I D x) :=
  subbundleTopology (E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (annihilatorSpace I D)

/-- The annihilator inclusion is a topological embedding into `T*M`. -/
theorem isEmbedding_annihilatorInclusion : IsEmbedding (annihilatorInclusion I D P) :=
  isEmbedding_totalSpace_subbundle (E →L[𝕜] 𝕜) P
    (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (annihilatorSpace I D)

variable {I D P} in
/-- A covector field with values in the annihilators of `D` is a continuous section of the
annihilator bundle `D⁰` exactly when it is a continuous section of `T*M`. -/
theorem continuous_totalSpaceMk_annihilatorSpace_iff {σ : Π x : M, annihilatorSpace I D x} :
    Continuous (fun x ↦ TotalSpace.mk' P (E := fun x ↦ annihilatorSpace I D x) x (σ x)) ↔
      Continuous fun x ↦ TotalSpace.mk' (E →L[𝕜] 𝕜)
        (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x (σ x : TangentSpace I x →L[𝕜] 𝕜) := by
  rw [(isEmbedding_annihilatorInclusion I D P).continuous_iff]
  simp only [comp_def, annihilatorInclusion_mk']

end Inclusion

end CotangentBundle

open CotangentBundle

namespace IsContMDiffDistribution

variable {n : ℕ∞ω} {k r : ℕ}

/-! ### Local annihilating coframes -/

section Frame

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- **Local frames of the annihilator.** Let `D` be a `C^n` distribution of rank `k` on a
manifold of dimension `k + r`. Every point has an open neighbourhood `U` carrying `r` covector
fields of class `C^n` on `U` which, at every point `y` of `U`, are linearly independent and span
the annihilator of `D` at `y`. -/
theorem exists_annihilatorSpace_frame (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ α : Fin r → Π y : M, TangentSpace I y →L[𝕜] 𝕜,
      (∀ j, ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
        (fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) y (α j y)) U) ∧
      ∀ y ∈ U, LinearIndependent 𝕜 (α · y) ∧
        Submodule.span 𝕜 (range (α · y)) = annihilatorSpace I D y := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  -- Read a local frame of `D` in one fixed tangent-bundle trivialization.
  obtain ⟨V, hV, hxV, X, hX⟩ := isContMDiffDistribution_iff.mp hD x
  let e := trivializationAt E (TangentSpace I) x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  -- Smooth covectors `c j y` of the model space, independent and annihilating the frame.
  obtain ⟨U, hUS, hU, hxU, c, hc, hcU⟩ :=
    ContMDiffOn.exists_contMDiffOn_linearIndependent_comp_eq_zero
      (hX.contMDiffOn_trivOperator x) (hV.inter e.open_baseSet) ⟨hxV, hxe⟩
      (hX.isSubbundleFrameOn.injective_trivOperator hxV) hk
  -- Pull them back through the trivialization.
  let α : Fin r → Π y : M, TangentSpace I y →L[𝕜] 𝕜 :=
    fun j y ↦ c j y ∘L e.continuousLinearMapAt 𝕜 y
  have hαmem {y : M} (hy : y ∈ U) (j : Fin r) : α j y ∈ annihilatorSpace I D y :=
    mem_annihilatorSpace_iff.mpr fun _ hv ↦
      hX.isSubbundleFrameOn.apply_continuousLinearMapAt_eq_zero (hUS hy).1 (hUS hy).2
        ((hcU y hy).2 j) hv
  -- Pulling back through the trivialization is linear and injective.
  have hαind {y : M} (hy : y ∈ U) : LinearIndependent 𝕜 (α · y) :=
    Fintype.linearIndependent_iff.mpr fun μ hμ ↦ Fintype.linearIndependent_iff.mp (hcU y hy).1 μ
      (e.injective_comp_continuousLinearMapAt 𝕜 (hUS hy).2 (by
        simpa [α, ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.smul_comp] using hμ))
  refine ⟨U, hU, hxU, α, fun j ↦ contMDiffOn_mk_comp_continuousLinearMapAt x
    (fun _ hy ↦ (hUS hy).2) (hc j), fun y hy ↦ ⟨hαind hy, ?_⟩⟩
  -- `r` independent covectors of the `r`-dimensional annihilator span it.
  refine Submodule.eq_of_le_of_finrank_eq
    (Submodule.span_le.mpr (range_subset_iff.mpr fun j ↦ hαmem hy j)) ?_
  have h := finrank_add_finrank_annihilatorSpace (I := I) (D := D) y
  rw [hD.finrank_eq y] at h
  rw [finrank_span_eq_card (hαind hy), Fintype.card_fin]
  omega

/-- **Local annihilating coframes.** A `C^n` distribution of rank `k` on a manifold of dimension
`k + r` is, near every point, the common kernel of `r` covector fields of class `C^n` which are
linearly independent at every point of the neighbourhood. -/
theorem exists_local_annihilating_coframe (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ α : Fin r → Π y : M, TangentSpace I y →L[𝕜] 𝕜,
      (∀ j, ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
        (fun y ↦ TotalSpace.mk' (E →L[𝕜] 𝕜) y (α j y)) U) ∧
      ∀ y ∈ U, LinearIndependent 𝕜 (α · y) ∧
        ∀ v : TangentSpace I y, v ∈ D y ↔ ∀ j, α j y v = 0 := by
  obtain ⟨U, hU, hx, α, hα, hαU⟩ := hD.exists_annihilatorSpace_frame hk x
  refine ⟨U, hU, hx, α, hα, fun y hy ↦ ⟨(hαU y hy).1, fun v ↦ ?_⟩⟩
  rw [mem_iff_forall_mem_annihilatorSpace, ← (hαU y hy).2]
  refine ⟨fun h j ↦ h _ (Submodule.subset_span ⟨j, rfl⟩), fun h p hp ↦ ?_⟩
  induction hp using Submodule.span_induction with
  | mem _ hq => obtain ⟨j, rfl⟩ := hq; exact h j
  | zero => simp
  | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
  | smul _ _ _ h₁ => simp [h₁]

/-- The annihilators of a `C^n` distribution of rank `k` on a manifold of dimension `k + r` have
`C^n` local frames of size `r` near every point, as a family of subspaces of `T*M`. -/
theorem hasLocalContMDiffSubbundleFrames_annihilatorSpace (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    HasLocalContMDiffSubbundleFrames I n (E →L[𝕜] 𝕜) (Fin r)
      (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (annihilatorSpace I D) :=
  hasLocalContMDiffSubbundleFrames_iff.mpr fun x ↦ by
    obtain ⟨U, hU, hx, α, hα, hαU⟩ := hD.exists_annihilatorSpace_frame hk x
    exact ⟨U, hU, hx, α, ⟨fun j ↦ (hα j).continuousOn, fun hy ↦ (hαU _ hy).1,
      fun hy ↦ (hαU _ hy).2⟩, hα⟩

end Frame

/-! ### The annihilator bundle -/

section VectorBundle

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M]
  [IsManifold I (n + 1) M]

/-- **The annihilator bundle.** The annihilators of a `C^n` distribution of rank `k` on a manifold
of dimension `k + r` form a fibre bundle with fibre `Fin r → 𝕜`, with the topology of a subspace
of `T*M`. Its trivializations are those of the `C^n` local frames of the annihilators
(`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`). Use this definition as a local instance,
which chooses a local frame at every point. -/
@[instance_reducible]
def annihilatorFiberBundle (hD : IsContMDiffDistribution I n k D) (hk : k + r = finrank 𝕜 E) :
    FiberBundle (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x :=
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  (hD.hasLocalContMDiffSubbundleFrames_annihilatorSpace hk).fiberBundle

/-- **The annihilator bundle is a vector bundle**: its local frame trivializations are linear,
with continuous coordinate changes. -/
theorem annihilatorVectorBundle (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    letI := hD.annihilatorFiberBundle hk
    VectorBundle 𝕜 (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x :=
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  (hD.hasLocalContMDiffSubbundleFrames_annihilatorSpace hk).vectorBundle

/-- **The annihilator bundle is a `C^n` vector bundle**, a `C^n` subbundle of rank `r` of the
cotangent bundle. -/
theorem annihilatorContMDiffVectorBundle (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD.annihilatorVectorBundle hk
    ContMDiffVectorBundle n (Fin r → 𝕜) (fun x ↦ annihilatorSpace I D x) I :=
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  (hD.hasLocalContMDiffSubbundleFrames_annihilatorSpace hk).contMDiffVectorBundle

/-- The inclusion of the annihilator bundle into `T*M` is `C^n`. -/
theorem contMDiff_annihilatorInclusion (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    letI := hD.annihilatorFiberBundle hk
    ContMDiff (I.prod 𝓘(𝕜, Fin r → 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (annihilatorInclusion I D (Fin r → 𝕜)) :=
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  (hD.hasLocalContMDiffSubbundleFrames_annihilatorSpace hk).contMDiff_totalSpace_inclusion

/-- **The annihilator bundle is smoothly embedded in `T*M`.** The inclusion of the annihilators of
a `C^n` distribution of rank `k` on a manifold of dimension `k + r` into the cotangent bundle is a
`C^n` smooth embedding of a manifold of dimension `dim M + r`. The manifold `M` need not be
boundaryless. -/
theorem isSmoothEmbedding_annihilatorInclusion (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    letI := hD.annihilatorFiberBundle hk
    IsSmoothEmbedding (I.prod 𝓘(𝕜, Fin r → 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (annihilatorInclusion I D (Fin r → 𝕜)) := by
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  let := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  let := hD.annihilatorFiberBundle hk
  let := hD.annihilatorVectorBundle hk
  let := hD.annihilatorContMDiffVectorBundle hk
  exact isSmoothEmbedding_totalSpace_subbundle (F := E →L[𝕜] 𝕜) (F' := Fin r → 𝕜)
    (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (V := annihilatorSpace I D)
    (hD.contMDiff_annihilatorInclusion hk)

end VectorBundle


end IsContMDiffDistribution

namespace CotangentBundle

/-! ### The annihilator inclusion along the zero section -/

section ZeroSection

variable [IsManifold I 1 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiberBundle F fun x ↦ annihilatorSpace I D x] [VectorBundle 𝕜 F fun x ↦ annihilatorSpace I D x]

/-- **The differential of the annihilator inclusion along the zero section.** At the zero
covector over `q`, a tangent vector of `T*M` is read in the preferred chart there as a pair of a
tangent vector of `M` and a covector at `q`. For any vector bundle structure on the annihilators
of `D` for which the inclusion into `T*M` is differentiable at the zero covector, the inclusion
sends the tangent vector with horizontal part `v` and vertical part `a ∈ D⁰_q`
(`TauCeti.Bundle.zeroSectionTangentEquiv`) to `(v, a)`. -/
theorem mfderiv_annihilatorInclusion_zeroSection (q : M)
    (hι : MDifferentiableAt (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜))
      (annihilatorInclusion I D F) (zeroSection F (fun x ↦ annihilatorSpace I D x) q))
    (u : TangentSpace (I.prod 𝓘(𝕜, F)) (zeroSection F (fun x ↦ annihilatorSpace I D x) q)) :
    (mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (annihilatorInclusion I D F)
        (zeroSection F (fun x ↦ annihilatorSpace I D x) q) u : E × (E →L[𝕜] 𝕜)) =
      ((TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q u).1,
        ((TauCeti.Bundle.zeroSectionTangentEquiv (I := I) q u).2 : TangentSpace I q →L[𝕜] 𝕜)) := by
  set S := TauCeti.Bundle.zeroSectionTangentEquiv (I := I) (F := F)
    (V := fun x ↦ annihilatorSpace I D x) q
  -- Split `u` into its horizontal and vertical parts.
  obtain ⟨⟨v, a⟩, rfl⟩ := S.symm.surjective u
  rw [S.apply_symm_apply, TauCeti.Bundle.zeroSectionTangentEquiv_symm_eq, map_add]
  -- The inclusion maps the zero section to the zero section, whose differential is `v ↦ (v, 0)`.
  have h₁ : (mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (annihilatorInclusion I D F)
      (zeroSection F (fun x ↦ annihilatorSpace I D x) q)
      (mfderiv I (I.prod 𝓘(𝕜, F)) (zeroSection F fun x ↦ annihilatorSpace I D x) q v) :
        E × (E →L[𝕜] 𝕜)) = (v, 0) := by
    refine (mfderiv_comp_apply (f := zeroSection F fun x ↦ annihilatorSpace I D x) (x := q) hι
      (((contMDiff_zeroSection (n := 1) 𝕜 fun x ↦ annihilatorSpace I D x) q).mdifferentiableAt
        one_ne_zero) v).symm.trans ?_
    rw [show annihilatorInclusion I D F ∘ (zeroSection F fun x ↦ annihilatorSpace I D x) =
        zeroSection (E →L[𝕜] 𝕜) fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜 from
      funext fun x ↦ annihilatorInclusion_zeroSection I D F x, TauCeti.Bundle.mfderiv_zeroSection]
    -- The target tangent space is only definitionally `E × (E →L[𝕜] 𝕜)`, so
    -- `ContinuousLinearMap.inl_apply` does not rewrite here and is applied as a term.
    exact ContinuousLinearMap.inl_apply v
  -- The inclusion maps the line through `a` in the fibre to the line through `a` in `T*_q M`,
  -- whose velocity is `(0, a)`.
  have h₂ : (mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (annihilatorInclusion I D F)
      (zeroSection F (fun x ↦ annihilatorSpace I D x) q) (S.symm (0, a)) : E × (E →L[𝕜] 𝕜)) =
      (0, (a : TangentSpace I q →L[𝕜] 𝕜)) := by
    have hcurve : MDifferentiableAt 𝓘(𝕜) (I.prod 𝓘(𝕜, F))
        (fun t : 𝕜 ↦ (⟨q, t • a⟩ : TotalSpace F fun x ↦ annihilatorSpace I D x)) 0 := by
      simpa only [id] using (Bundle.TotalSpace.hasMFDerivAt_smul_curve
        (⟨q, a⟩ : TotalSpace F fun x ↦ annihilatorSpace I D x)
        (hasDerivAt_id' (0 : 𝕜))).mdifferentiableAt
    rw [TauCeti.Bundle.zeroSectionTangentEquiv_symm_inr]
    refine (mfderiv_comp_apply_of_eq
      (f := fun t : 𝕜 ↦ (⟨q, t • a⟩ : TotalSpace F fun x ↦ annihilatorSpace I D x))
      (x := (0 : 𝕜)) hι hcurve (by simp [zeroSection]) (1 : 𝕜)).symm.trans ?_
    rw [show annihilatorInclusion I D F ∘
          (fun t : 𝕜 ↦ (⟨q, t • a⟩ : TotalSpace F fun x ↦ annihilatorSpace I D x)) =
        fun t : 𝕜 ↦ (⟨q, t • (a : TangentSpace I q →L[𝕜] 𝕜)⟩ : CotangentBundle I M) from
      funext fun t ↦ annihilatorInclusion_mk' I D F q (t • a),
      (Bundle.TotalSpace.hasMFDerivAt_smul_curve
        (⟨q, (a : TangentSpace I q →L[𝕜] 𝕜)⟩ : CotangentBundle I M)
        (hasDerivAt_id' (0 : 𝕜))).mfderiv]
    -- The preferred trivialization of `T*M` at `q` gives `a` itself as its fibre coordinate.
    have ha : (trivializationAt (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) q
        ⟨q, (a : TangentSpace I q →L[𝕜] 𝕜)⟩).2 = (a : TangentSpace I q →L[𝕜] 𝕜) := by
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _
        (FiberBundle.mem_baseSet_trivializationAt (E →L[𝕜] 𝕜)
          (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) q),
        continuousLinearMapAt_trivializationAt_self]
    -- The velocity is `((1 : 𝕜 →L[𝕜] 𝕜).smulRight (0, 1 • ξ)) 1`, with `ξ` the fibre coordinate.
    -- Applying `smulRight` is `ContinuousLinearMap.smulRight_apply`, which holds by `rfl`; it
    -- cannot be rewritten because the tangent space is only definitionally a product, so the two
    -- `one_smul` steps are applied to the unfolded application.
    exact (one_smul 𝕜 _).trans (Prod.ext rfl ((one_smul 𝕜 _).trans ha))
  refine (congrArg₂ (· + ·) h₁ h₂).trans ?_
  exact Prod.ext (add_zero v) (zero_add _)

end ZeroSection

/-! ### Fibre-linear functions on the annihilator bundle -/

section Pairing

variable {P : Type*}

/-- The **fibre-linear function of a vector field** `V` on the annihilator bundle of a distribution
`D`: a covector `z` annihilating `D` over `x` is sent to `z(V x)`. It is linear on each fibre and
depends only on `V` modulo `D`
(`TauCeti.CotangentBundle.annihilatorPairing_eq_annihilatorPairing_iff`). -/
def annihilatorPairing (V : Π x : M, TangentSpace I x)
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) : 𝕜 :=
  (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) (V z.proj)

/-- The fibre-linear function of `V` evaluates the covector on `V` at its base point. -/
@[simp]
theorem annihilatorPairing_apply (V : Π x : M, TangentSpace I x)
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    annihilatorPairing V z = (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) (V z.proj) :=
  (rfl)

/-- The fibre-linear function of `V` is the value on `V` of the covector in `T*M`. -/
theorem annihilatorPairing_eq_snd_annihilatorInclusion (V : Π x : M, TangentSpace I x)
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    annihilatorPairing V z =
      (annihilatorInclusion I D P z).snd (V (annihilatorInclusion I D P z).proj) := by
  rw [annihilatorInclusion_apply]
  rfl

/-- **Fibre-linearity.** The function of `V` is linear on each fibre of the annihilator bundle. -/
theorem annihilatorPairing_mk_smul (V : Π x : M, TangentSpace I x) (x : M) (c : 𝕜)
    (q : annihilatorSpace I D x) :
    annihilatorPairing V (TotalSpace.mk' P x (c • q)) =
      c * annihilatorPairing V (TotalSpace.mk' P x q) := by
  simp

/-- The function of a sum of vector fields is the sum of their functions. -/
theorem annihilatorPairing_add (V W : Π x : M, TangentSpace I x) :
    annihilatorPairing (P := P) (D := D) (V + W) =
      annihilatorPairing V + annihilatorPairing W := by
  ext z
  simp

/-- The function of a constant multiple of a vector field is the multiple of its function. -/
theorem annihilatorPairing_smul (c : 𝕜) (V : Π x : M, TangentSpace I x) :
    annihilatorPairing (P := P) (D := D) (c • V) = c • annihilatorPairing V := by
  ext z
  simp

/-- **The function of `V` depends exactly on `V` modulo `D`.** On a finite-dimensional manifold, two
vector fields have the same function on the annihilator bundle of `D` exactly when their
difference is tangent to `D`. -/
theorem annihilatorPairing_eq_annihilatorPairing_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {V W : Π x : M, TangentSpace I x} :
    annihilatorPairing (P := P) (D := D) V = annihilatorPairing W ↔ ∀ x, V x - W x ∈ D x := by
  refine ⟨fun h x ↦ mem_iff_forall_mem_annihilatorSpace.2 fun q hq ↦ ?_, fun h ↦ ?_⟩
  · have hx := congrFun h (TotalSpace.mk' P x ⟨q, hq⟩)
    simp only [annihilatorPairing_apply] at hx
    rw [map_sub, hx, sub_self]
  · ext z
    rw [annihilatorPairing_apply, annihilatorPairing_apply, ← sub_eq_zero, ← map_sub]
    exact mem_annihilatorSpace_iff.1 z.snd.property _ (h z.proj)

end Pairing

section Smooth

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] {n : ℕ∞ω} {k r : ℕ}
  [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- **Pointwise smoothness of fibre-linear functions.** For a `C^n` distribution `D` of rank `k`
on a manifold of dimension `k + r`, the function on the annihilator bundle of `D` of a vector field
`V` that is `C^n` at the base point of `z` is `C^n` at `z`. -/
theorem contMDiffAt_annihilatorPairing (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = Module.finrank 𝕜 E) {V : Π x : M, TangentSpace I x}
    {z : TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x}
    (hV : ContMDiffAt I I.tangent n (T% V) z.proj) :
    letI := hD.annihilatorFiberBundle hk
    ContMDiffAt (I.prod 𝓘(𝕜, Fin r → 𝕜)) 𝓘(𝕜) n
      (annihilatorPairing (P := Fin r → 𝕜) (D := D) V) z :=
  letI := hD.annihilatorFiberBundle hk
  by
  have hj := hD.contMDiff_annihilatorInclusion hk
  -- The inclusion into `T*M` is the covector field `z ↦ z` along the bundle projection.
  rw [show annihilatorInclusion I D (Fin r → 𝕜) = fun z ↦ ⟨z.proj, z.snd⟩ from
    funext (annihilatorInclusion_apply I D _)] at hj
  exact ContMDiffAt.clm_bundle_apply_scalar (V := TangentSpace I)
    (b := fun w : TotalSpace (Fin r → 𝕜) (fun x ↦ annihilatorSpace I D x) ↦ w.proj)
    (hj z) (hV.comp z (Bundle.contMDiff_proj fun x ↦ annihilatorSpace I D x).contMDiffAt)

/-- **Smoothness of fibre-linear functions.** For a `C^n` distribution `D` of rank `k` on a
manifold of dimension `k + r`, the function of a `C^n` vector field `V` on the annihilator bundle
of `D` is `C^n`. -/
theorem contMDiff_annihilatorPairing (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = Module.finrank 𝕜 E) {V : Π x : M, TangentSpace I x}
    (hV : ContMDiff I I.tangent n (T% V)) :
    letI := hD.annihilatorFiberBundle hk
    ContMDiff (I.prod 𝓘(𝕜, Fin r → 𝕜)) 𝓘(𝕜) n
      (annihilatorPairing (P := Fin r → 𝕜) (D := D) V) :=
  fun _ ↦ contMDiffAt_annihilatorPairing hD hk (hV _)

end Smooth

end CotangentBundle

end TauCeti
