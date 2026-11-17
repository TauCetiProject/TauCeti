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
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.ContMDiff.QuotientRange
import TauCeti.Geometry.Manifold.IsManifold.Basic

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
  (`TauCeti.IsContMDiffDistribution.exists_local_coframe`). The coframe is built in one
  tangent-bundle trivialization: if `A y : 𝕜ᵏ → E` is the coordinate operator of a local frame of
  `D`, then for a fixed complement `Q ≅ 𝕜ʳ` of the range of `A x` the quotient coordinates
  `E → Q` along the range of `A y` are, near `x`, `r` independent covectors depending smoothly on
  `y` and vanishing on the frame
  (`ContMDiffOn.exists_contMDiffOn_linearIndependent_comp_eq_zero`). The corank-one case is
  `TauCeti.IsContMDiffDistribution.exists_local_annihilator`.
* **The annihilator bundle.** By the smooth local frame criterion
  `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`, the annihilators, with the
  subspace topology of `T*M`, are a `C^n` vector bundle with fibre `Fin r → 𝕜`
  (`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`,
  `TauCeti.IsContMDiffDistribution.annihilatorVectorBundle`,
  `TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle`), and their inclusion
  `TauCeti.CotangentBundle.annihilatorInclusion` into `T*M` is a `C^n` smooth embedding
  (`TauCeti.IsContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion`).

Pointwise, `D x` and `D⁰_x` have complementary dimensions
(`TauCeti.CotangentBundle.finrank_add_finrank_annihilatorSpace`), `D x` is recovered as the common
kernel of `D⁰_x` (`TauCeti.CotangentBundle.mem_iff_forall_mem_annihilatorSpace`), and for a
hyperplane `D x = ker α` the annihilator is the line spanned by `α`
(`TauCeti.CotangentBundle.annihilatorSpace_eq_span_singleton`).

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

/-- A covector lies in the annihilator of `D` at `x` when it vanishes on `D x`. -/
@[simp]
theorem mem_annihilatorSpace_iff {x : M} {p : TangentSpace I x →L[𝕜] 𝕜} :
    p ∈ annihilatorSpace I D x ↔ ∀ v ∈ D x, p v = 0 :=
  StrongDual.mem_polarSubmodule 𝕜 (D x) p

/-- A covector lies in the annihilator of `D` at `x` when its kernel contains `D x`. -/
theorem mem_annihilatorSpace_iff_le_ker {x : M} {p : TangentSpace I x →L[𝕜] 𝕜} :
    p ∈ annihilatorSpace I D x ↔ D x ≤ LinearMap.ker p.toLinearMap :=
  mem_annihilatorSpace_iff

section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- **The dimension of the annihilator.** On a finite-dimensional manifold, `D x` and its
annihilator have complementary dimensions: `dim D x + dim D⁰_x = dim M`. -/
theorem finrank_add_finrank_annihilatorSpace (x : M) :
    finrank 𝕜 (D x) + finrank 𝕜 (annihilatorSpace I D x) = finrank 𝕜 E :=
  StrongDual.finrank_add_finrank_polarSubmodule (𝕜 := 𝕜) (E := E) (D x)

/-- On a finite-dimensional manifold a tangent vector lies in `D x` exactly when every covector
of the annihilator `D⁰_x` vanishes on it: `D x` is the common kernel of its annihilator. -/
theorem mem_iff_forall_mem_annihilatorSpace {x : M} {v : TangentSpace I x} :
    v ∈ D x ↔ ∀ p ∈ annihilatorSpace I D x, p v = 0 := by
  refine ⟨fun hv p hp ↦ mem_annihilatorSpace_iff.mp hp v hv, fun h ↦ ?_⟩
  by_contra hv
  -- A linear functional separating `v` from `D x` is continuous in finite dimensions.
  obtain ⟨a, ha, haD⟩ := Submodule.exists_le_ker_of_notMem hv
  exact ha (h (LinearMap.toContinuousLinearMap a)
    (mem_annihilatorSpace_iff_le_ker.mpr haD))

/-- **The annihilator of a hyperplane.** If a nonzero covector `α` at `x` has kernel `D x`, then
the annihilator of `D` at `x` is the line spanned by `α`. -/
theorem annihilatorSpace_eq_span_singleton {x : M} {α : TangentSpace I x →L[𝕜] 𝕜} (hα : α ≠ 0)
    (hker : LinearMap.ker α.toLinearMap = D x) :
    annihilatorSpace I D x = 𝕜 ∙ α := by
  have hα' : α.toLinearMap ≠ 0 := fun h ↦ hα (ContinuousLinearMap.coe_injective h)
  -- `D x` is the kernel of a nonzero functional, so it has codimension one.
  have hD : finrank 𝕜 (D x) + 1 = finrank 𝕜 E := by
    have := LinearMap.finrank_range_add_finrank_ker α.toLinearMap
    rw [LinearMap.range_eq_top.mpr (α.toLinearMap.surjective_of_ne_zero hα'), finrank_top,
      finrank_self, hker, finrank_tangentSpace] at this
    omega
  refine (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr
    (mem_annihilatorSpace_iff_le_ker.mpr hker.ge)) ?_).symm
  have := finrank_add_finrank_annihilatorSpace (D := D) x
  rw [finrank_span_singleton hα]
  omega

end FiniteDimensional

/-! ### The inclusion into the cotangent bundle -/

section Inclusion

variable (P : Type*) (I D)

/-- The canonical map from the total space of the annihilators of `D` into `T*M`, sending `(x, p)`
with `p ∈ D⁰_x` to `(x, p)`. The model-fibre parameter `P` of `Bundle.TotalSpace` plays no
role. -/
def annihilatorInclusion (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    CotangentBundle I M :=
  ⟨z.proj, z.2⟩

@[simp]
theorem annihilatorInclusion_proj (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    (annihilatorInclusion I D P z).proj = z.proj := (rfl)

@[simp]
theorem annihilatorInclusion_snd (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    (annihilatorInclusion I D P z).2 = (z.2 : TangentSpace I z.proj →L[𝕜] 𝕜) := (rfl)

/-- The image of the annihilator inclusion consists of the covectors annihilating `D` at their
base points. -/
@[simp]
theorem range_annihilatorInclusion :
    range (annihilatorInclusion I D P) = {w | w.2 ∈ annihilatorSpace I D w.proj} := by
  ext ⟨x, p⟩
  exact ⟨by rintro ⟨⟨y, q⟩, h⟩; cases h; exact q.2, fun hp ↦ ⟨⟨x, ⟨p, hp⟩⟩, rfl⟩⟩

/-- The annihilator inclusion is injective. -/
theorem annihilatorInclusion_injective : Injective (annihilatorInclusion I D P) := by
  rintro ⟨x, p⟩ ⟨y, q⟩ h
  obtain rfl : x = y := congrArg TotalSpace.proj h
  exact congrArg (TotalSpace.mk x) (Subtype.ext
    ((TotalSpace.mk_inj (F := E →L[𝕜] 𝕜) (E := fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜)).mp h))

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
  let A := IsSubbundleFrameOn.trivOperator 𝕜 E X x
  -- Smooth covectors `c j y` of the model space, independent and annihilating the frame.
  obtain ⟨U, hUS, hU, hxU, c, hc, hcU⟩ :=
    ContMDiffOn.exists_contMDiffOn_linearIndependent_comp_eq_zero
      (hX.contMDiffOn_trivOperator x) (hV.inter e.open_baseSet) ⟨hxV, hxe⟩
      (hX.isSubbundleFrameOn.injective_trivOperator hxV) hk
  -- Pull them back through the trivialization.
  let α : Fin r → Π y : M, TangentSpace I y →L[𝕜] 𝕜 :=
    fun j y ↦ c j y ∘L e.continuousLinearMapAt 𝕜 y
  have hαmem {y : M} (hy : y ∈ U) (j : Fin r) : α j y ∈ annihilatorSpace I D y := by
    rw [mem_annihilatorSpace_iff_le_ker, ← hX.span_eq (hUS hy).1]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have hAi := IsSubbundleFrameOn.trivOperator_apply (𝕜 := 𝕜) (X := X) (hUS hy).2
      (Pi.single i (1 : 𝕜))
    have heval : α j y (X i y) = c j y (e ⟨y, X i y⟩).2 :=
      congrArg (c j y) (e.continuousLinearMapAt_apply_of_mem 𝕜 (hUS hy).2 (X i y))
    have hzero : α j y (X i y) = 0 := by
      rw [heval]
      simpa [A, hAi, e] using
        congrArg (fun f : (Fin k → 𝕜) →L[𝕜] 𝕜 ↦ f (Pi.single i 1)) ((hcU y hy).2 j)
    exact hzero
  have hαind {y : M} (hy : y ∈ U) : LinearIndependent 𝕜 (α · y) := by
    refine Fintype.linearIndependent_iff.mpr fun μ hμ ↦
      Fintype.linearIndependent_iff.mp (hcU y hy).1 μ ?_
    ext v
    simpa [α, e.continuousLinearMapAt_symmL (hUS hy).2] using
      DFunLike.congr_fun hμ (e.symmL 𝕜 y v)
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
theorem exists_local_coframe (hD : IsContMDiffDistribution I n k D) (hk : k + r = finrank 𝕜 E)
    (x : M) :
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

end Frame

/-! ### The annihilator bundle -/

section VectorBundle

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M]
  [IsManifold I (n + 1) M]

/-- The annihilators of a `C^n` distribution of rank `k` on a manifold of dimension `k + r` have
`C^n` local frames of size `r` near every point, as a family of subspaces of `T*M`. -/
theorem hasLocalContMDiffSubbundleFrames_annihilatorSpace (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    HasLocalContMDiffSubbundleFrames I n (E →L[𝕜] 𝕜) (Fin r)
      (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (annihilatorSpace I D) :=
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  hasLocalContMDiffSubbundleFrames_iff.mpr fun x ↦ by
    obtain ⟨U, hU, hx, α, hα, hαU⟩ := hD.exists_annihilatorSpace_frame hk x
    exact ⟨U, hU, hx, α, ⟨fun j ↦ (hα j).continuousOn, fun hy ↦ (hαU _ hy).1,
      fun hy ↦ (hαU _ hy).2⟩, hα⟩

/-- **The annihilator bundle.** The annihilators of a `C^n` distribution of rank `k` on a manifold
of dimension `k + r` form a fibre bundle with fibre `Fin r → 𝕜`, with the topology of a subspace
of `T*M`. Its trivializations are those of the `C^n` local frames of the annihilators
(`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`). Use this definition as a local instance,
which chooses a local frame at every point. -/
@[instance_reducible]
def annihilatorFiberBundle (hD : IsContMDiffDistribution I n k D) (hk : k + r = finrank 𝕜 E) :
    FiberBundle (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x :=
  (hD.hasLocalContMDiffSubbundleFrames_annihilatorSpace hk).fiberBundle

/-- **The annihilator bundle is a vector bundle**: its local frame trivializations are linear,
with continuous coordinate changes. -/
theorem annihilatorVectorBundle (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    letI := hD.annihilatorFiberBundle hk
    VectorBundle 𝕜 (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x :=
  (hD.hasLocalContMDiffSubbundleFrames_annihilatorSpace hk).vectorBundle

/-- **The annihilator bundle is a `C^n` vector bundle**, a `C^n` subbundle of rank `r` of the
cotangent bundle. -/
theorem annihilatorContMDiffVectorBundle (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD.annihilatorVectorBundle hk
    ContMDiffVectorBundle n (Fin r → 𝕜) (fun x ↦ annihilatorSpace I D x) I :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  (hD.hasLocalContMDiffSubbundleFrames_annihilatorSpace hk).contMDiffVectorBundle

/-- The inclusion of the annihilator bundle into `T*M` is `C^n`. -/
theorem contMDiff_annihilatorInclusion (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = finrank 𝕜 E) :
    letI := hD.annihilatorFiberBundle hk
    ContMDiff (I.prod 𝓘(𝕜, Fin r → 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (annihilatorInclusion I D (Fin r → 𝕜)) :=
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

end TauCeti
