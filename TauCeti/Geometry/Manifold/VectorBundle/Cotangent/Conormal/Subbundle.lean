/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Conormal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Analysis.Calculus.QuotientRange
import TauCeti.Geometry.Manifold.MFDeriv.Coordinates
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Topology.FiberBundle.Pullback

/-!
# The conormal vector subbundle of a map

For a map `i : Q → M` between manifolds, the conormal fibres
`TauCeti.CotangentBundle.conormalSpace J I i q ⊆ T*_{i q} M` form a family of subspaces of the
pulled-back cotangent bundle `i *ᵖ T*M`. Their total space carries the subspace topology
`TauCeti.CotangentBundle.instTopologicalSpaceTotalSpaceConormalSpace` from `i *ᵖ T*M`, and
`TauCeti.CotangentBundle.conormalInclusion` sends `(q, p)` to `(i q, p) ∈ T*M`, with image
`TauCeti.CotangentBundle.conormal J I i`; it is a topological embedding whenever `i` is
(`TauCeti.CotangentBundle.isEmbedding_conormalInclusion`).

Over `ℝ` or `ℂ`, when `M` has dimension `finrank 𝕜 F + k`, `i` is `C^m` (`n + 1 ≤ m`), and `di_q` is
injective at every `q : Q`, the conormal spaces admit `C^n` local frames
(`TauCeti.CotangentBundle.exists_isConormalFrameOn`): near `q₀ : Q`, for a fixed complement
`B : (Fin k → 𝕜) →L[𝕜] E` to the coordinate differential `A q₀`, the projections
`(A q).quotientRangeCoordinate B` vanish on `range (A q)` and pull back through the tangent chart at
`i q₀` to a `C^n` local basis of `conormalSpace J I i`. By the smooth local frame criterion
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`
(`hasLocalContMDiffSubbundleFrames_conormalSpace`), this makes `conormalSpace J I i` a `C^n` vector
bundle of rank `k` over `Q` (`conormalFiberBundle`, `conormalVectorBundle`,
`conormalContMDiffVectorBundle`) with `C^n` canonical inclusion into `T*M`
(`contMDiff_conormalInclusion`) and model dimension `dim M` (`finrank_conormalBundleModel`), without
assuming `Q` or `M` boundaryless. When `Q` is boundaryless and `i` is a `C^m` smooth embedding
(`n + 1 ≤ m`), `TauCeti.isSmoothEmbedding_lift_totalSpace_subbundle` shows `conormalInclusion` is a
`C^n` smooth embedding (`isSmoothEmbedding_conormalInclusion`). Point, full-manifold, product, and
slice examples are in `Conormal.Basic` and `Conormal.Prod`.

## Main definitions and results

* `TauCeti.CotangentBundle.conormalInclusion`, `range_conormalInclusion`,
  `isEmbedding_conormalInclusion`: canonical map `(q, p) ↦ (i q, p)` into `T*M`, with range
  `conormal J I i`, topological embedding when `i` is.
* `TauCeti.CotangentBundle.instTopologicalSpaceTotalSpaceConormalSpace`: subspace topology from
  `i *ᵖ T*M` on the total space of `conormalSpace J I i`.
* `TauCeti.CotangentBundle.IsConormalFrameOn`, `exists_isConormalFrameOn`: `C^n` local frames of
  `conormalSpace J I i`, their pointwise `basis` and `trivialization`, and local existence without
  shrinking across finite orders.
* `TauCeti.CotangentBundle.hasLocalContMDiffSubbundleFrames_conormalSpace`: the conormal spaces
  have `C^n` local frames of size `k` near every point.
* `TauCeti.CotangentBundle.conormalFiberBundle`, `conormalVectorBundle`,
  `conormalContMDiffVectorBundle`, `contMDiff_conormalInclusion`,
  `isSmoothEmbedding_conormalInclusion`: `C^n` vector subbundle structure and `C^n` smooth embedding
  into `T*M`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, LNM 1764, Springer, 2001, Section 3.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Lemma 10.32 and
  Proposition 11.27.
-/

public section

noncomputable section

open Bundle Function Manifold Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {P : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Canonical inclusion into the ambient cotangent bundle -/

section Inclusion

variable (P J I)

/-- The canonical map from the total space of the conormal spaces of `i : Q → M` into `T*M`,
sending `(q, p)` with `p ∈ conormalSpace J I i q` to `(i q, p)`. The model-fibre parameter `P` of
`Bundle.TotalSpace` plays no role. -/
def conormalInclusion (i : Q → M) (z : TotalSpace P fun q ↦ conormalSpace J I i q) :
    CotangentBundle I M :=
  ⟨i z.proj, z.2⟩

@[simp]
theorem conormalInclusion_proj (i : Q → M) (z : TotalSpace P fun q ↦ conormalSpace J I i q) :
    (conormalInclusion P J I i z).proj = i z.proj := (rfl)

@[simp]
theorem conormalInclusion_snd (i : Q → M) (z : TotalSpace P fun q ↦ conormalSpace J I i q) :
    (conormalInclusion P J I i z).2 = (z.2 : TangentSpace I (i z.proj) →L[𝕜] 𝕜) := (rfl)

theorem conormalInclusion_apply (i : Q → M) (z : TotalSpace P fun q ↦ conormalSpace J I i q) :
    conormalInclusion P J I i z = ⟨i z.proj, z.2⟩ := (rfl)

@[simp]
theorem conormalInclusion_mk' (i : Q → M) (q : Q) (p : conormalSpace J I i q) :
    conormalInclusion P J I i (TotalSpace.mk' P q p) =
      TotalSpace.mk' (E →L[𝕜] 𝕜) (i q) (p : TangentSpace I (i q) →L[𝕜] 𝕜) := (rfl)

/-- `conormalInclusion` sends the zero covector in the conormal space over `q` to the zero covector
in `T*M` over `i q`. -/
@[simp]
theorem conormalInclusion_zeroSection (i : Q → M) (q : Q) :
    conormalInclusion P J I i (zeroSection P (fun q ↦ conormalSpace J I i q) q) =
      zeroSection (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (i q) := (rfl)

/-- Every covector in the image of `conormalInclusion` annihilates the differential of `i` at its
base point in `Q`. -/
theorem conormalInclusion_snd_comp_mfderiv (i : Q → M)
    (z : TotalSpace P fun q ↦ conormalSpace J I i q) :
    (conormalInclusion P J I i z).2 ∘L mfderiv J I i z.proj = 0 :=
  mem_conormalSpace_iff.mp z.2.2

/-- The image of `conormalInclusion` in `T*M` is the conormal set `conormal J I i`. -/
@[simp]
theorem range_conormalInclusion (i : Q → M) :
    range (conormalInclusion P J I i) = conormal J I i := by
  ext w; rw [mem_range, mem_conormal_iff]
  refine ⟨?_, fun ⟨q, hq, hp⟩ ↦ ?_⟩
  · rintro ⟨⟨q, p', hp'⟩, rfl⟩; exact ⟨q, rfl, mem_conormalSpace_iff.mp hp'⟩
  · cases w; subst hq; exact ⟨⟨q, ⟨_, mem_conormalSpace_iff.mpr hp⟩⟩, rfl⟩

end Inclusion

variable (P) in
/-- When `i : Q → M` is injective, `conormalInclusion` is injective. -/
theorem conormalInclusion_injective {i : Q → M} (hi : Injective i) :
    Injective (conormalInclusion P J I i) := by
  rintro ⟨q₁, p₁⟩ ⟨q₂, p₂⟩ h
  obtain rfl : q₁ = q₂ := hi (congrArg TotalSpace.proj h)
  exact congrArg (TotalSpace.mk q₁) (Subtype.ext
    ((TotalSpace.mk_inj (F := E →L[𝕜] 𝕜) (E := fun y : M ↦ TangentSpace I y →L[𝕜] 𝕜)).mp h))

/-! ### Subbundle topology -/

section Topology

variable [IsManifold I 1 M]

variable (J I) in
/-- The total space of the conormal spaces of `i : Q → M` carries the subspace topology
(`TauCeti.subbundleTopology`) of the pulled-back cotangent bundle `i *ᵖ T*M`. The model-fibre
parameter `P` of `Bundle.TotalSpace` plays no role. -/
instance instTopologicalSpaceTotalSpaceConormalSpace (i : Q → M) :
    TopologicalSpace (TotalSpace P fun q ↦ conormalSpace J I i q) :=
  subbundleTopology (E →L[𝕜] 𝕜) (E := i *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)
    (conormalSpace J I i)

private theorem isEmbedding_toPullback (P : Type*) (i : Q → M) :
    IsEmbedding (fun z : TotalSpace P (fun q ↦ conormalSpace J I i q) ↦
      (⟨z.proj, (z.2 : TangentSpace I (i z.proj) →L[𝕜] 𝕜)⟩ :
        TotalSpace (E →L[𝕜] 𝕜) (i *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜))) :=
  isEmbedding_totalSpace_subbundle (E →L[𝕜] 𝕜) P
    (E := i *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (conormalSpace J I i)

variable (P J I) in
/-- The bundle projection of the conormal spaces is continuous. -/
theorem continuous_proj_conormalSpace (i : Q → M) :
    Continuous (π P fun q ↦ conormalSpace J I i q) :=
  (Pullback.continuous_proj (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) i).comp
    (isEmbedding_toPullback P i).continuous

variable (P J I) in
/-- The canonical map `conormalInclusion` into `T*M` is continuous. -/
theorem continuous_conormalInclusion (i : Q → M) :
    Continuous (conormalInclusion P J I i) :=
  (Pullback.continuous_lift (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) i).comp
    (isEmbedding_toPullback P i).continuous

variable (P) in
/-- Along a topological embedding `i : Q → M`, `conormalInclusion` is a topological embedding of the
total space of `conormalSpace J I i` into `T*M`. -/
theorem isEmbedding_conormalInclusion {i : Q → M} (hi : IsEmbedding i) :
    IsEmbedding (conormalInclusion P J I i) :=
  (Bundle.Pullback.isEmbedding_lift (F := E →L[𝕜] 𝕜)
    (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) hi).comp (isEmbedding_toPullback P i)

end Topology

/-! ### Local frames and `C^n` vector subbundle structure -/

section Frame

variable [IsManifold I 1 M] {ι : Type*} {n m : ℕ∞ω}

variable (J I) in
/-- A family of covectors `X j q ∈ T*_{i q} M` over `q : Q` is a `C^n` local frame of
`conormalSpace J I i` on `U ⊆ Q` when each lift `q ↦ (i q, X j q)` into `T*M` is `C^n` on `U` and,
at every `q ∈ U`, the covectors `X j q` form a basis of `conormalSpace J I i q`. -/
structure IsConormalFrameOn (n : ℕ∞ω) (i : Q → M)
    (X : ι → Π q : Q, TangentSpace I (i q) →L[𝕜] 𝕜) (U : Set Q) : Prop where
  /-- Each lifted covector section `q ↦ (i q, X j q)` is `C^n` on `U`. -/
  contMDiffOn_lift (j : ι) :
    ContMDiffOn J (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (fun q ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (i q) (X j q) : CotangentBundle I M)) U
  /-- At every point of `U`, the frame covectors are linearly independent. -/
  linearIndependent {q : Q} (hq : q ∈ U) : LinearIndependent 𝕜 (X · q)
  /-- At every point of `U`, the frame covectors span `conormalSpace J I i q`. -/
  span_eq {q : Q} (hq : q ∈ U) : Submodule.span 𝕜 (range (X · q)) = conormalSpace J I i q

namespace IsConormalFrameOn

section Basic

variable {i : Q → M} {X : ι → Π q : Q, TangentSpace I (i q) →L[𝕜] 𝕜} {U U' : Set Q}

/-- Restricting a `C^n` local conormal frame to a subset preserves the frame property. -/
theorem mono (hX : IsConormalFrameOn J I n i X U) (hU : U' ⊆ U) :
    IsConormalFrameOn J I n i X U' :=
  ⟨fun j ↦ (hX.contMDiffOn_lift j).mono hU, fun hq ↦ hX.linearIndependent (hU hq),
    fun hq ↦ hX.span_eq (hU hq)⟩

/-- Lowering the regularity order preserves a local conormal frame. -/
theorem of_le (hX : IsConormalFrameOn J I m i X U) (hnm : n ≤ m) :
    IsConormalFrameOn J I n i X U :=
  ⟨fun j ↦ (hX.contMDiffOn_lift j).of_le hnm, hX.linearIndependent, hX.span_eq⟩

/-- Every `C^n` local conormal frame is a continuous local subbundle frame of
`conormalSpace J I i` inside the pulled-back cotangent bundle `i *ᵖ T*M`. -/
theorem isSubbundleFrameOn (hX : IsConormalFrameOn J I n i X U) :
    IsSubbundleFrameOn (E →L[𝕜] 𝕜) (E := i *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)
      (conormalSpace J I i) X U :=
  ⟨fun j ↦ (inducing_pullbackTotalSpaceEmbedding (E →L[𝕜] 𝕜)
      (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) i).continuousOn_iff.mpr
      (continuousOn_id.prodMk (hX.contMDiffOn_lift j).continuousOn),
    hX.linearIndependent, hX.span_eq⟩

/-- At a point `q ∈ U`, a local conormal frame `X` on `U` forms a basis of
`conormalSpace J I i q`. -/
def basis (hX : IsConormalFrameOn J I n i X U) {q : Q} (hq : q ∈ U) :
    Basis ι 𝕜 (conormalSpace J I i q) :=
  hX.isSubbundleFrameOn.basis hq

/-- Coercing the `j`-th element of `hX.basis hq` into `T*_{i q} M` recovers `X j q`. -/
@[simp]
theorem coe_basis (hX : IsConormalFrameOn J I n i X U) {q : Q} (hq : q ∈ U) (j : ι) :
    (hX.basis hq j : TangentSpace I (i q) →L[𝕜] 𝕜) = X j q :=
  hX.isSubbundleFrameOn.coe_basis hq j

/-- At `q ∈ U`, the conormal covector with coordinates `c` in `hX.basis hq` is the linear
combination `∑ j, c j • X j q`. -/
theorem coe_basis_equivFun_symm [Fintype ι] (hX : IsConormalFrameOn J I n i X U) {q : Q}
    (hq : q ∈ U) (c : ι → 𝕜) :
    ((hX.basis hq).equivFun.symm c : TangentSpace I (i q) →L[𝕜] 𝕜) = ∑ j, c j • X j q := by simp

end Basic

section Pullback

variable (ic : C^n⟮J, Q; I, M⟯) {X : ι → Π q : Q, TangentSpace I (ic q) →L[𝕜] 𝕜} {U : Set Q}

/-- On an open set `U`, each member of a `C^n` local conormal frame along `ic : C^n⟮J, Q; I, M⟯` is
a `C^n` section of the pulled-back cotangent bundle `ic *ᵖ T*M`. -/
theorem contMDiffOn_pullback
    (hX : IsConormalFrameOn J I n (ic : Q → M) X U) (hU : IsOpen U) (j : ι) :
    ContMDiffOn J (J.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (fun q : Q ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) q (X j q) :
        TotalSpace (E →L[𝕜] 𝕜) ((ic : Q → M) *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜))) U :=
  fun _ hq ↦ ((Bundle.Pullback.contMDiffAt_iff ic ic.contMDiff.contMDiffAt).mpr
    ⟨contMDiffAt_id, (hX.contMDiffOn_lift j).contMDiffAt (hU.mem_nhds hq)⟩).contMDiffWithinAt

variable [Finite ι] [IsRCLikeNormedField 𝕜]

/-- The local trivialization of `conormalSpace J I ic` over `U` determined by a local conormal
frame `X` along `ic : C^n⟮J, Q; I, M⟯`. -/
def trivialization (hX : IsConormalFrameOn J I n (ic : Q → M) X U) (hU : IsOpen U) :
    Trivialization (ι → 𝕜) (π (ι → 𝕜) fun q ↦ conormalSpace J I (ic : Q → M) q) :=
  letI := FiberBundle.pullback (F := E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic
  letI := VectorBundle.pullback (𝕜 := 𝕜) (F := E →L[𝕜] 𝕜)
    (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic
  hX.isSubbundleFrameOn.trivialization hU

/-- `hX.trivialization ic hU` is the subbundle frame trivialization
`hX.isSubbundleFrameOn.trivialization hU` inside the pulled-back cotangent bundle `ic *ᵖ T*M`. -/
theorem trivialization_def (hX : IsConormalFrameOn J I n (ic : Q → M) X U) (hU : IsOpen U) :
    letI : FiberBundle (E →L[𝕜] 𝕜) ((ic : Q → M) *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) :=
      FiberBundle.pullback (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic
    letI : VectorBundle 𝕜 (E →L[𝕜] 𝕜) ((ic : Q → M) *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) :=
      VectorBundle.pullback (𝕜 := 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic
    hX.trivialization ic hU = hX.isSubbundleFrameOn.trivialization hU := (rfl)

private local instance :
    FiberBundle (E →L[𝕜] 𝕜) ((ic : Q → M) *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) :=
  FiberBundle.pullback (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic

private local instance :
    VectorBundle 𝕜 (E →L[𝕜] 𝕜) ((ic : Q → M) *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) :=
  VectorBundle.pullback (𝕜 := 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic

/-- The base set of `hX.trivialization ic hU` is `U`. -/
@[simp]
theorem trivialization_baseSet (hX : IsConormalFrameOn J I n (ic : Q → M) X U) (hU : IsOpen U) :
    (hX.trivialization ic hU).baseSet = U :=
  hX.isSubbundleFrameOn.trivialization_baseSet hU

/-- Over `U`, the conormal frame trivialization sends a covector to its coordinates in the basis
`hX.basis hp`. -/
@[simp]
theorem trivialization_apply (hX : IsConormalFrameOn J I n (ic : Q → M) X U) (hU : IsOpen U)
    {p : TotalSpace (ι → 𝕜) fun q ↦ conormalSpace J I (ic : Q → M) q} (hp : p.proj ∈ U) :
    hX.trivialization ic hU p = (p.proj, (hX.basis hp).equivFun p.2) :=
  hX.isSubbundleFrameOn.trivialization_apply hU hp

/-- Over `U`, the partial-homeomorphism inverse of the conormal frame trivialization sends
`(q, c)` to `(q, (hX.basis hz).equivFun.symm c)`. -/
@[simp]
theorem trivialization_toOpenPartialHomeomorph_symm_apply
    (hX : IsConormalFrameOn J I n (ic : Q → M) X U) (hU : IsOpen U)
    {z : Q × (ι → 𝕜)} (hz : z.1 ∈ U) :
    (hX.trivialization ic hU).toOpenPartialHomeomorph.symm z =
      TotalSpace.mk' (ι → 𝕜) (E := fun q ↦ conormalSpace J I (ic : Q → M) q)
        z.1 ((hX.basis hz).equivFun.symm z.2) :=
  hX.isSubbundleFrameOn.trivialization_symm_apply hU hz

/-- Over `U`, the fibrewise inverse of the conormal frame trivialization sends coordinates `c` to
`(hX.basis hq).equivFun.symm c`. -/
@[simp]
theorem trivialization_symm_apply (hX : IsConormalFrameOn J I n (ic : Q → M) X U) (hU : IsOpen U)
    {q : Q} (hq : q ∈ U) (c : ι → 𝕜) :
    (hX.trivialization ic hU).symm q c = (hX.basis hq).equivFun.symm c :=
  (TotalSpace.mk_inj (F := ι → 𝕜) (E := fun q ↦ conormalSpace J I (ic : Q → M) q) (b := q)).mp
    (((hX.trivialization ic hU).mk_symm (b := q) (by simpa using hq) c).trans
      (hX.trivialization_toOpenPartialHomeomorph_symm_apply ic hU (z := (q, c)) hq))

/-- The conormal frame trivialization is fibrewise linear. -/
instance isLinear_trivialization (hX : IsConormalFrameOn J I n (ic : Q → M) X U) (hU : IsOpen U) :
    (hX.trivialization ic hU).IsLinear 𝕜 :=
  hX.isSubbundleFrameOn.isLinear_trivialization hU

end Pullback

end IsConormalFrameOn

end Frame

section VectorBundle

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E]
  {m n : ℕ∞ω} [IsManifold I m M] [IsManifold J m Q] {k : ℕ}

omit [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I m M] [IsManifold J m Q] in
/-- Candidate local conormal frame near `q₀` associated with a continuous linear map
`B : (Fin k → 𝕜) →L[𝕜] E` complementary to the coordinate differential of `i`. -/
private def chartConormalFrame [IsManifold I 1 M] [IsManifold J 1 Q]
    (i : Q → M) (q₀ : Q) (B : (Fin k → 𝕜) →L[𝕜] E)
    (j : Fin k) (q : Q) : TangentSpace I (i q) →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin k ↦ 𝕜) j ∘L
    (inTangentCoordinates J I id i (mfderiv J I i) q₀ q).quotientRangeCoordinate B) ∘L
    (trivializationAt E (TangentSpace I) (i q₀)).continuousLinearMapAt 𝕜 (i q)

/-- When `U` lies in the overlap of the preferred charts at `q₀` and `i q₀` and `B` remains
complementary to the coordinate differential of `i` on `U`, each lifted covector section of
`chartConormalFrame` is `C^n` on `U`. -/
private theorem contMDiffOn_lift_chartConormalFrame [IsManifold I 1 M] [IsManifold J 1 Q]
    {i : Q → M} (hi : ContMDiff J I m i) (hmn : n + 1 ≤ m)
    (hinj : Injective (mfderiv J I i q₀)) {U : Set Q}
    (hUW₀ : U ⊆ (chartAt H' q₀).source ∩ i ⁻¹' (chartAt H (i q₀)).source)
    {B : (Fin k → 𝕜) →L[𝕜] E}
    (hB : ∀ q ∈ U, ((inTangentCoordinates J I id i (mfderiv J I i) q₀ q).coprod B).IsInvertible)
    (j : Fin k) :
    ContMDiffOn J (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (fun q ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (i q)
        (chartConormalFrame (J := J) i q₀ B j q) : CotangentBundle I M)) U := by
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold J (n + 1) Q := .of_le hmn
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have : FiniteDimensional 𝕜 F := .of_injective (mfderiv J I i q₀).toLinearMap hinj
  have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  have hAW₀ := (hi.of_le hmn).mfderiv_inTangentCoordinates le_rfl q₀
  have hT : ContMDiffOn J 𝓘(𝕜, E →L[𝕜] Fin k → 𝕜) n
      (fun q ↦ (inTangentCoordinates J I id i (mfderiv J I i) q₀ q).quotientRangeCoordinate B) U :=
    fun q hq ↦ (contDiffAt_id.quotientRangeCoordinate B (hB q hq)).contMDiffAt
      |>.comp_contMDiffWithinAt q (hAW₀.mono hUW₀ q hq)
  let eh := (trivializationAt E (TangentSpace I) (i q₀)).continuousLinearMap (RingHom.id 𝕜)
    (trivializationAt 𝕜 (Bundle.Trivial M 𝕜) (i q₀))
  refine (eh.contMDiffOn_iff fun q hq ↦ eh.mem_source.mpr
    (by simpa [eh, Trivial.eq_trivialization M 𝕜] using (hUW₀ hq).2)).mpr
    ⟨(hi.of_le (le_self_add.trans hmn)).contMDiffOn,
      ((contMDiffOn_const (c := ContinuousLinearMap.proj (R := 𝕜)
        (φ := fun _ : Fin k ↦ 𝕜) j)).clm_comp hT).congr fun q hq ↦ ?_⟩
  have hqM : i q ∈ (trivializationAt E (TangentSpace I) (i q₀)).baseSet := by
    simpa using (hUW₀ hq).2
  ext v; simp [eh, chartConormalFrame, Bundle.Trivialization.continuousLinearMap_apply,
    Trivial.eq_trivialization M 𝕜,
    (trivializationAt E (TangentSpace I) (i q₀)).continuousLinearMapAt_symmL hqM]

/-- Whenever `U` lies inside the overlap of the preferred charts at `q₀` and `i q₀` and `B`
remains complementary to the coordinate differential of `i` on `U`, `chartConormalFrame` is a
`C^n` local frame of `conormalSpace J I i` on `U`. -/
private theorem isConormalFrameOn_chartConormalFrame [IsManifold I 1 M] [IsManifold J 1 Q]
    {i : Q → M} (hi : ContMDiff J I m i) (hmn : n + 1 ≤ m)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank 𝕜 F + k = finrank 𝕜 E) {q₀ : Q}
    {U : Set Q} (hUW₀ : U ⊆ (chartAt H' q₀).source ∩ i ⁻¹' (chartAt H (i q₀)).source)
    {B : (Fin k → 𝕜) →L[𝕜] E}
    (hB : ∀ q ∈ U, ((inTangentCoordinates J I id i (mfderiv J I i) q₀ q).coprod B).IsInvertible) :
    IsConormalFrameOn J I n i (chartConormalFrame (J := J) i q₀ B) U := by
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  have hX_mem (j : Fin k) {q : Q} (hq : q ∈ U) :
      chartConormalFrame (J := J) i q₀ B j q ∈ conormalSpace J I i q := by
    have hqQ : q ∈ (trivializationAt F (TangentSpace J) q₀).baseSet := by simpa using (hUW₀ hq).1
    have hqM : i q ∈ (trivializationAt E (TangentSpace I) (i q₀)).baseSet := by
      simpa using (hUW₀ hq).2
    rw [mem_conormalSpace_iff]; ext u
    have hu : mfderiv J I i q u = (trivializationAt E (TangentSpace I) (i q₀)).symmL 𝕜 (i q)
        (inTangentCoordinates J I id i (mfderiv J I i) q₀ q
          ((trivializationAt F (TangentSpace J) q₀).continuousLinearMapAt 𝕜 q u)) := by
      rw [inTangentCoordinates]; dsimp only [id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hqQ hqM]
      simp only [ContinuousLinearMap.comp_apply, Trivialization.coe_continuousLinearEquivAt_eq',
        Trivialization.symm_continuousLinearEquivAt_eq',
        (trivializationAt F (TangentSpace J) q₀).symmL_continuousLinearMapAt hqQ,
        (trivializationAt E (TangentSpace I) (i q₀)).symmL_continuousLinearMapAt hqM]
    simp only [chartConormalFrame, ContinuousLinearMap.comp_apply, zero_apply, hu,
      (trivializationAt E (TangentSpace I) (i q₀)).continuousLinearMapAt_symmL hqM,
      ContinuousLinearMap.quotientRangeCoordinate_apply_left, map_zero]
  have hX_lin {q : Q} (hq : q ∈ U) :
      LinearIndependent 𝕜 (chartConormalFrame (J := J) (I := I) i q₀ B · q) := by
    have hqM : i q ∈ (trivializationAt E (TangentSpace I) (i q₀)).baseSet := by
      simpa using (hUW₀ hq).2
    refine Fintype.linearIndependent_iff.mpr fun μ hμ j ↦ ?_
    simpa [chartConormalFrame,
      (trivializationAt E (TangentSpace I) (i q₀)).continuousLinearMapAt_symmL hqM,
      ContinuousLinearMap.quotientRangeCoordinate_apply_right (hB q hq), Pi.single_apply] using
      DFunLike.congr_fun hμ
        ((trivializationAt E (TangentSpace I) (i q₀)).symmL 𝕜 (i q) (B (Pi.single j 1)))
  exact ⟨contMDiffOn_lift_chartConormalFrame hi hmn (hinj q₀) hUW₀ hB,
    fun hq ↦ hX_lin hq, fun {q} hq ↦ Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (range_subset_iff.mpr fun j ↦ hX_mem j hq))
      (by have := finrank_add_finrank_conormalSpace (hinj q)
          rw [finrank_span_eq_card (hX_lin hq), Fintype.card_fin]; omega)⟩

/-- **Existence of `C^n` local conormal frames.** When `M` has dimension `finrank 𝕜 F + k`, `i` is
`C^m` with `n + 1 ≤ m`, and `mfderiv J I i q` is injective at every `q : Q`, every point `q₀ : Q`
has an open neighbourhood `U` carrying a `C^n` local frame of `conormalSpace J I i` indexed by
`Fin k`. Smooth and analytic orders (`∞`, `ω`) are included without shrinking per finite order. -/
theorem exists_isConormalFrameOn {i : Q → M} (hi : ContMDiff J I m i) (hmn : n + 1 ≤ m)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank 𝕜 F + k = finrank 𝕜 E) (q₀ : Q) :
    haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
    ∃ U : Set Q, IsOpen U ∧ q₀ ∈ U ∧
      ∃ X : Fin k → Π q : Q, TangentSpace I (i q) →L[𝕜] 𝕜,
        IsConormalFrameOn J I n i X U := by
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold J (n + 1) Q := .of_le hmn
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : IsManifold J 1 Q := .of_le (n := n + 1) le_add_self
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have : FiniteDimensional 𝕜 F := .of_injective (mfderiv J I i q₀).toLinearMap (hinj q₀)
  -- Read `mfderiv J I i` in fixed tangent charts at `q₀` and `i q₀`; it is `C^n` on their overlap.
  let W₀ : Set Q := (chartAt H' q₀).source ∩ i ⁻¹' (chartAt H (i q₀)).source
  have hW₀_open : IsOpen W₀ :=
    (chartAt H' q₀).open_source.inter ((chartAt H (i q₀)).open_source.preimage hi.continuous)
  have hq₀W₀ : q₀ ∈ W₀ := ⟨mem_chart_source H' q₀, mem_chart_source H (i q₀)⟩
  have hAW₀ := (hi.of_le hmn).mfderiv_inTangentCoordinates le_rfl q₀
  have hAq₀_inj : Injective (inTangentCoordinates J I id i (mfderiv J I i) q₀ q₀) := by
    rw [inTangentCoordinates]; dsimp only [id_eq]
    have hq₀Q := mem_baseSet_trivializationAt F (TangentSpace J) q₀
    have hq₀M := mem_baseSet_trivializationAt E (TangentSpace I) (i q₀)
    rw [ContinuousLinearMap.inCoordinates_eq hq₀Q hq₀M]
    exact ((trivializationAt E (TangentSpace I) (i q₀)).continuousLinearEquivAt 𝕜 (i q₀)
      hq₀M).injective.comp ((hinj q₀).comp
        ((trivializationAt F (TangentSpace J) q₀).continuousLinearEquivAt 𝕜 q₀ hq₀Q).symm.injective)
  -- Choose a closed complement `C` remaining complementary on an open `V ∋ q₀`, and identify `C`
  -- with `Fin k → 𝕜` by dimension counting.
  obtain ⟨C, _, V, hV_open, hq₀V, hInv⟩ :=
    (hAW₀.continuousOn.continuousAt (hW₀_open.mem_nhds hq₀W₀)).exists_isInvertible_coprod_subtypeL
      (.of_injective_of_finiteDimensional_domain hAq₀_inj)
  obtain ⟨e₀, -⟩ := hInv q₀ hq₀V
  have hC_rank : finrank 𝕜 (Fin k → 𝕜) = finrank 𝕜 C := by
    have he₀ := e₀.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at he₀; rw [Module.finrank_pi, Fintype.card_fin]; omega
  let cEquiv : (Fin k → 𝕜) ≃L[𝕜] C := ContinuousLinearEquiv.ofFinrankEq hC_rank
  let B : (Fin k → 𝕜) →L[𝕜] E := C.subtypeL ∘L cEquiv.toContinuousLinearMap
  refine ⟨V ∩ W₀, hV_open.inter hW₀_open, ⟨hq₀V, hq₀W₀⟩,
    chartConormalFrame (J := J) i q₀ B,
    isConormalFrameOn_chartConormalFrame hi hmn hinj hk inter_subset_right fun q hq ↦ ?_⟩
  obtain ⟨eq, heq⟩ := hInv q hq.1
  exact ⟨((ContinuousLinearEquiv.refl 𝕜 F).prodCongr cEquiv).trans eq,
    ContinuousLinearMap.ext fun ⟨u, w⟩ ↦ by
      simpa [ContinuousLinearEquiv.trans_apply, B] using DFunLike.congr_fun heq (u, cEquiv w)⟩

/-- For a `C^m` map `i : Q → M` with `n + 1 ≤ m`, injective differentials, and ambient dimension
`finrank 𝕜 F + k = finrank 𝕜 E`, the conormal spaces `conormalSpace J I i` have `C^n` local frames
of size `k` near every point, as a family of subspaces of the pulled-back cotangent bundle
`i *ᵖ T*M`. -/
theorem hasLocalContMDiffSubbundleFrames_conormalSpace {i : Q → M} (hi : ContMDiff J I m i)
    (hmn : n + 1 ≤ m) (hinj : ∀ q, Injective (mfderiv J I i q))
    (hk : finrank 𝕜 F + k = finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
    let ic : C^n⟮J, Q; I, M⟯ := ⟨i, hi.of_le (le_self_add.trans hmn)⟩
    letI := FiberBundle.pullback (F := E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic
    HasLocalContMDiffSubbundleFrames J n (E →L[𝕜] 𝕜) (Fin k)
      (E := (ic : Q → M) *ᵖ fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)
      (conormalSpace J I (ic : Q → M)) :=
  haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
  let ic : C^n⟮J, Q; I, M⟯ := ⟨i, hi.of_le (le_self_add.trans hmn)⟩
  letI := FiberBundle.pullback (F := E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic
  hasLocalContMDiffSubbundleFrames_iff.mpr fun q ↦ by
    obtain ⟨U, hU, hq, X, hX⟩ := exists_isConormalFrameOn hi hmn hinj hk q
    exact ⟨U, hU, hq, X, hX.isSubbundleFrameOn, hX.contMDiffOn_pullback ic hU⟩

/-- For a `C^m` map `i : Q → M` with `n + 1 ≤ m`, injective differentials, and ambient dimension
`finrank 𝕜 F + k = finrank 𝕜 E`, the conormal spaces `conormalSpace J I i` form a fibre bundle over
`Q` with model fibre `Fin k → 𝕜`, carrying the subspace topology from `i *ᵖ T*M`
(`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`). Install this definition locally with
`letI`. -/
@[instance_reducible]
def conormalFiberBundle {i : Q → M} (hi : ContMDiff J I m i) (hmn : n + 1 ≤ m)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank 𝕜 F + k = finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
    FiberBundle (Fin k → 𝕜) fun q ↦ conormalSpace J I i q :=
  haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
  let ic : C^n⟮J, Q; I, M⟯ := ⟨i, hi.of_le (le_self_add.trans hmn)⟩
  letI := FiberBundle.pullback (F := E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic
  letI := VectorBundle.pullback (𝕜 := 𝕜) (F := E →L[𝕜] 𝕜)
    (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ic
  (hasLocalContMDiffSubbundleFrames_conormalSpace hi hmn hinj hk).fiberBundle

/-- The trivializations of `conormalFiberBundle` are the trivializations associated with `C^n` local
conormal frames on open subsets of `Q`. -/
theorem mem_trivializationAtlas_conormalFiberBundle_iff {i : Q → M} (hi : ContMDiff J I m i)
    (hmn : n + 1 ≤ m) (hinj : ∀ q, Injective (mfderiv J I i q))
    (hk : finrank 𝕜 F + k = finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
    letI := conormalFiberBundle hi hmn hinj hk
    ∀ e : Trivialization (Fin k → 𝕜) (π (Fin k → 𝕜) fun q ↦ conormalSpace J I i q),
      e ∈ trivializationAtlas (Fin k → 𝕜) (fun q ↦ conormalSpace J I i q) ↔
        ∃ (V : Set Q) (hV : IsOpen V) (Y : Fin k → Π q : Q, TangentSpace I (i q) →L[𝕜] 𝕜)
          (hY : IsConormalFrameOn J I n i Y V),
            hY.trivialization ⟨i, hi.of_le (le_self_add.trans hmn)⟩ hV = e := fun e ↦ by
  have : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
  let ic : C^n⟮J, Q; I, M⟯ := ⟨i, hi.of_le (le_self_add.trans hmn)⟩
  let T' : M → Type _ := fun x ↦ TangentSpace I x →L[𝕜] 𝕜
  let := FiberBundle.pullback (F := E →L[𝕜] 𝕜) (E := T') ic
  let := VectorBundle.pullback (𝕜 := 𝕜) (F := E →L[𝕜] 𝕜) (E := T') ic
  refine ((hasLocalContMDiffSubbundleFrames_conormalSpace hi hmn hinj hk
    ).mem_trivializationAtlas_fiberBundle_iff e).trans
      ⟨fun ⟨V, hV, Y, hY, hYn, he⟩ ↦
        ⟨V, hV, Y, ⟨fun j ↦ ?_, hY.linearIndependent, hY.span_eq⟩, he⟩,
        fun ⟨V, hV, Y, hY, he⟩ ↦
          ⟨V, hV, Y, hY.isSubbundleFrameOn, hY.contMDiffOn_pullback ic hV, he⟩⟩
  exact fun q hq ↦ (((Bundle.Pullback.contMDiffAt_iff ic ic.contMDiff.contMDiffAt).mp
    ((hYn j).contMDiffAt (hV.mem_nhds hq))).2).contMDiffWithinAt

/-- **The conormal bundle is a topological vector bundle.** Its local frame trivializations are
linear with continuous coordinate changes. -/
theorem conormalVectorBundle {i : Q → M} (hi : ContMDiff J I m i) (hmn : n + 1 ≤ m)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank 𝕜 F + k = finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
    letI := conormalFiberBundle hi hmn hinj hk
    VectorBundle 𝕜 (Fin k → 𝕜) fun q ↦ conormalSpace J I i q := by
  have : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
  let ic : C^n⟮J, Q; I, M⟯ := ⟨i, hi.of_le (le_self_add.trans hmn)⟩
  let T' : M → Type _ := fun x ↦ TangentSpace I x →L[𝕜] 𝕜
  let := FiberBundle.pullback (F := E →L[𝕜] 𝕜) (E := T') ic
  let := VectorBundle.pullback (𝕜 := 𝕜) (F := E →L[𝕜] 𝕜) (E := T') ic
  exact (hasLocalContMDiffSubbundleFrames_conormalSpace hi hmn hinj hk).vectorBundle

/-- **The conormal bundle is a `C^n` vector bundle.** On `C^m` manifolds with `n + 1 ≤ m`, the
conormal spaces have `C^n` local frames, so the smooth local frame criterion
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` applies. -/
theorem conormalContMDiffVectorBundle {i : Q → M} (hi : ContMDiff J I m i) (hmn : n + 1 ≤ m)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank 𝕜 F + k = finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
    letI := conormalFiberBundle hi hmn hinj hk
    letI := conormalVectorBundle hi hmn hinj hk
    ContMDiffVectorBundle n (Fin k → 𝕜) (fun q ↦ conormalSpace J I i q) J := by
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold J (n + 1) Q := .of_le hmn
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let ic : C^n⟮J, Q; I, M⟯ := ⟨i, hi.of_le (le_self_add.trans hmn)⟩
  let T' : M → Type _ := fun x ↦ TangentSpace I x →L[𝕜] 𝕜
  let := FiberBundle.pullback (F := E →L[𝕜] 𝕜) (E := T') ic
  let := VectorBundle.pullback (𝕜 := 𝕜) (F := E →L[𝕜] 𝕜) (E := T') ic
  let := ContMDiffVectorBundle.pullback (E →L[𝕜] 𝕜) T' J ic
  exact (hasLocalContMDiffSubbundleFrames_conormalSpace hi hmn hinj hk).contMDiffVectorBundle

/-- **The canonical inclusion `conormalInclusion` of the conormal bundle into `T*M` is `C^n`.** -/
theorem contMDiff_conormalInclusion {i : Q → M} (hi : ContMDiff J I m i) (hmn : n + 1 ≤ m)
    (hinj : ∀ q, Injective (mfderiv J I i q)) (hk : finrank 𝕜 F + k = finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
    letI := conormalFiberBundle hi hmn hinj hk
    ContMDiff (J.prod 𝓘(𝕜, Fin k → 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (conormalInclusion (Fin k → 𝕜) J I i) := by
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold J (n + 1) Q := .of_le hmn
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let ic : C^n⟮J, Q; I, M⟯ := ⟨i, hi.of_le (le_self_add.trans hmn)⟩
  let T' : M → Type _ := fun x ↦ TangentSpace I x →L[𝕜] 𝕜
  let := FiberBundle.pullback (F := E →L[𝕜] 𝕜) (E := T') ic
  let := VectorBundle.pullback (𝕜 := 𝕜) (F := E →L[𝕜] 𝕜) (E := T') ic
  let := ContMDiffVectorBundle.pullback (E →L[𝕜] 𝕜) T' J ic
  let := conormalFiberBundle hi hmn hinj hk
  let := conormalVectorBundle hi hmn hinj hk
  let := conormalContMDiffVectorBundle hi hmn hinj hk
  have hlift : ContMDiff (J.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (Pullback.lift (F := E →L[𝕜] 𝕜) (E := T') ic) :=
    ((Bundle.Pullback.contMDiff_iff ic ic.contMDiff (E := T')).mp contMDiff_id).2
  refine hlift.comp (f := fun z : TotalSpace (Fin k → 𝕜) (fun q ↦ conormalSpace J I i q) ↦
    (⟨z.proj, (z.2 : TangentSpace I (i z.proj) →L[𝕜] 𝕜)⟩ : TotalSpace (E →L[𝕜] 𝕜) (i *ᵖ T')))
    fun z ↦ ?_
  have he := FiberBundle.trivialization_mem_atlas (Fin k → 𝕜) (fun q ↦ conormalSpace J I i q) z.proj
  have ⟨U, hU, X, hX, htriv⟩ :=
    (mem_trivializationAtlas_conormalFiberBundle_iff hi hmn hinj hk _).mp he
  have hzU : z.proj ∈ U := by
    have hz := mem_baseSet_trivializationAt (Fin k → 𝕜) (fun q ↦ conormalSpace J I i q) z.proj
    rwa [← htriv, hX.trivialization_baseSet ic hU] at hz
  let Vp : Π q : Q, Submodule 𝕜 ((i *ᵖ T') q) := conormalSpace J I i
  let : TopologicalSpace (TotalSpace (Fin k → 𝕜) fun q ↦ Vp q) :=
    subbundleTopology (E →L[𝕜] 𝕜) (F' := Fin k → 𝕜) Vp
  let : FiberBundle (Fin k → 𝕜) (fun q ↦ Vp q) := conormalFiberBundle hi hmn hinj hk
  let : VectorBundle 𝕜 (Fin k → 𝕜) (fun q ↦ Vp q) := conormalVectorBundle hi hmn hinj hk
  let : ContMDiffVectorBundle n (Fin k → 𝕜) (fun q ↦ Vp q) J :=
    conormalContMDiffVectorBundle hi hmn hinj hk
  have : MemTrivializationAtlas (hX.isSubbundleFrameOn.trivialization hU) :=
    ⟨(htriv ▸ he : hX.trivialization ic hU ∈ _)⟩
  have : ∀ q, IsScalarTower 𝕜 𝕜 ((i *ᵖ T') q) := fun _ ↦ ⟨mul_smul⟩
  exact hX.isSubbundleFrameOn.contMDiffAt_totalSpace_subbundle hU (hX.contMDiffOn_pullback ic hU)
    (p := ⟨z.proj, z.2⟩) hzU

omit [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] in
/-- **Dimension of the conormal bundle model.** When `finrank 𝕜 F + k = finrank 𝕜 E`, the model
space `F × (Fin k → 𝕜)` of the conormal bundle has the same dimension as `M`. -/
theorem finrank_conormalBundleModel [FiniteDimensional 𝕜 F]
    (hk : finrank 𝕜 F + k = finrank 𝕜 E) :
    finrank 𝕜 (F × (Fin k → 𝕜)) = finrank 𝕜 E := by
  rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin, hk]

/-- **The conormal bundle of an embedded submanifold is smoothly embedded in `T*M`.** For a `C^m`
smooth embedding `i : Q → M` (`n + 1 ≤ m`) of a boundaryless manifold `Q` into a finite-dimensional
manifold `M` with `finrank 𝕜 F + k = finrank 𝕜 E`, the canonical inclusion `conormalInclusion` is a
`C^n` smooth embedding of `TotalSpace (Fin k → 𝕜) (fun q ↦ conormalSpace J I i q)` into
`CotangentBundle I M`. The ambient manifold `M` need not be boundaryless. -/
theorem isSmoothEmbedding_conormalInclusion [J.Boundaryless] {i : Q → M}
    (hi : IsSmoothEmbedding J I m i) (hmn : n + 1 ≤ m) (hk : finrank 𝕜 F + k = finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le ((le_add_left le_rfl).trans hmn)
    letI := conormalFiberBundle hi.contMDiff hmn
      (hi.isImmersion.mfderiv_injective
        (ENat.one_le_iff_ne_zero_withTop.mp ((le_add_left le_rfl).trans hmn))) hk
    IsSmoothEmbedding (J.prod 𝓘(𝕜, Fin k → 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
      (conormalInclusion (Fin k → 𝕜) J I i) := by
  have hinj := hi.isImmersion.mfderiv_injective
    (ENat.one_le_iff_ne_zero_withTop.mp ((le_add_left le_rfl).trans hmn))
  have : IsManifold I (n + 1) M := .of_le hmn
  have : IsManifold J (n + 1) Q := .of_le hmn
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  have : IsManifold J n Q := .of_le (n := n + 1) le_self_add
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let := conormalFiberBundle hi.contMDiff hmn hinj hk
  let := conormalVectorBundle hi.contMDiff hmn hinj hk
  let := conormalContMDiffVectorBundle hi.contMDiff hmn hinj hk
  exact isSmoothEmbedding_lift_totalSpace_subbundle
    (F := E →L[𝕜] 𝕜) (F' := Fin k → 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)
    (V := conormalSpace J I i) (hi.of_le (le_self_add.trans hmn))
    (isEmbedding_conormalInclusion (Fin k → 𝕜) hi.isEmbedding)
    (contMDiff_conormalInclusion hi.contMDiff hmn hinj hk)

end VectorBundle

end TauCeti.CotangentBundle
