/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Projection

/-!
# `C^n` bilinear fields

Pairing two `C^n` sections with a `C^n` bilinear field gives a `C^n` function
(`ContMDiffWithinAt.clm_bundle_apply₂_trivial` and its variant on a set). Interchanging the two
inputs of a `C^n` family of bilinear bundle maps, over any base map and within a set, preserves
its regularity (`ContMDiffWithinAt.clm_bundle_flip`, with the variants `ContMDiffAt.clm_bundle_flip`
and `ContMDiff.clm_bundle_flip`); this permits contraction of a smooth tensor
in any input slot. Precomposing both inputs of a `C^n` bilinear field with a `C^n` field of
continuous linear maps gives a `C^n` bilinear field (`ContMDiff.bilinearComp_bundle`).

In particular the transpose of a `C^n` bilinear field is `C^n`. When two is nonzero in the
scalar field, averaging a field with its transpose defines a linear projection onto the symmetric
`C^n` sections. Over the reals this provides a linear ambient space for `C^n` Riemannian metrics,
without choosing an inner product on the original bundle fibres.

The construction uses Mathlib's `ContMDiffSection` of the iterated hom bundle. In bundle
coordinates transposition is the fixed continuous linear isometry
`ContinuousLinearMap.flipₗᵢ`; in particular preservation of regularity is valid in boundary
charts as well.
No compactness or finite-dimensionality is needed. The fibres are topological vector spaces
isomorphic to the normed model fibre and need not carry chosen norms.
-/

public section

noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]

section BaseMap

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {V₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞ω} {b : M → B} {s : Set M} {x : M}

/-- Pairing two `C^n` sections with a `C^n` bilinear field, over a base map `b`, gives a `C^n`
function, within a set at a point. -/
theorem ContMDiffWithinAt.clm_bundle_apply₂_trivial
    {β : ∀ x : M, V₁ (b x) →L[𝕜] V₂ (b x) →L[𝕜] G} {U : ∀ x : M, V₁ (b x)}
    {W : ∀ x : M, V₂ (b x)}
    (hβ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] G)
        (E := fun z ↦ V₁ z →L[𝕜] V₂ z →L[𝕜] G) (b y) (β y)) s x)
    (hU : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun y ↦ TotalSpace.mk' F₁ (b y) (U y)) s x)
    (hW : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂)) n (fun y ↦ TotalSpace.mk' F₂ (b y) (W y)) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜, G) n (fun y ↦ β y (U y) (W y)) s x :=
  (contMDiffWithinAt_totalSpace_iff.mp (hβ.clm_bundle_apply₂ (F₃ := G)
    (E₃ := Bundle.Trivial B G) hU hW)).2

/-- Pairing two `C^n` sections with a `C^n` bilinear field, over a base map `b`, gives a `C^n`
function on a set. -/
theorem ContMDiffOn.clm_bundle_apply₂_trivial
    {β : ∀ x : M, V₁ (b x) →L[𝕜] V₂ (b x) →L[𝕜] G} {U : ∀ x : M, V₁ (b x)}
    {W : ∀ x : M, V₂ (b x)}
    (hβ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] G)
        (E := fun z ↦ V₁ z →L[𝕜] V₂ z →L[𝕜] G) (b y) (β y)) s)
    (hU : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁)) n (fun y ↦ TotalSpace.mk' F₁ (b y) (U y)) s)
    (hW : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂)) n (fun y ↦ TotalSpace.mk' F₂ (b y) (W y)) s) :
    ContMDiffOn IM 𝓘(𝕜, G) n (fun y ↦ β y (U y) (W y)) s :=
  fun y hy ↦ (hβ y hy).clm_bundle_apply₂_trivial (hU y hy) (hW y hy)

section Flip

variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {V₃ : B → Type*} [TopologicalSpace (TotalSpace F₃ V₃)]
  [∀ x, TopologicalSpace (V₃ x)] [∀ x, AddCommGroup (V₃ x)] [∀ x, Module 𝕜 (V₃ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul 𝕜 (V₃ x)]
  [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]
  [∀ x, IsNormableSpace 𝕜 (V₁ x)] [∀ x, IsNormableSpace 𝕜 (V₂ x)]
  [∀ x, IsNormableSpace 𝕜 (V₃ x)]
  {A : ∀ x, V₁ (b x) →L[𝕜] V₂ (b x) →L[𝕜] V₃ (b x)}

/-- Interchanging the two inputs of a family of bilinear bundle maps over a base map `b` preserves
`C^n` regularity within a set at a point. -/
theorem ContMDiffWithinAt.clm_bundle_flip
    (hA : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (E := fun z ↦ V₁ z →L[𝕜] V₂ z →L[𝕜] V₃ z) (b y) (A y)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (E := fun z ↦ V₂ z →L[𝕜] V₁ z →L[𝕜] V₃ z) (b y) (A y).flip) s x := by
  rw [contMDiffWithinAt_hom_bundle] at hA ⊢
  refine ⟨hA.1, ?_⟩
  have hnear : ∀ᶠ y in 𝓝[insert x s] x, b y ∈
      (trivializationAt F₁ V₁ (b x)).baseSet ∩
      (trivializationAt F₂ V₂ (b x)).baseSet ∩
      (trivializationAt F₃ V₃ (b x)).baseSet :=
    hA.1.insert.continuousWithinAt.preimage_mem_nhdsWithin
      (((trivializationAt F₁ V₁ (b x)).open_baseSet.inter
        (trivializationAt F₂ V₂ (b x)).open_baseSet).inter
        (trivializationAt F₃ V₃ (b x)).open_baseSet |>.mem_nhds
          ⟨⟨mem_baseSet_trivializationAt' (b x), mem_baseSet_trivializationAt' (b x)⟩,
            mem_baseSet_trivializationAt' (b x)⟩)
  let _ : NormedAddCommGroup (F₁ →L[𝕜] F₂ →L[𝕜] F₃) := inferInstance
  let _ : NormedSpace 𝕜 (F₁ →L[𝕜] F₂ →L[𝕜] F₃) := inferInstance
  let _ : NormedAddCommGroup (F₂ →L[𝕜] F₁ →L[𝕜] F₃) := inferInstance
  let _ : NormedSpace 𝕜 (F₂ →L[𝕜] F₁ →L[𝕜] F₃) := inferInstance
  have hf : ContDiff 𝕜 n (ContinuousLinearMap.flip :
      (F₁ →L[𝕜] F₂ →L[𝕜] F₃) → F₂ →L[𝕜] F₁ →L[𝕜] F₃) := by
    -- The normed and topological versions of flip agree on both arguments.
    convert (ContinuousLinearMap.flipₗᵢ 𝕜 F₁ F₂ F₃).toContinuousLinearEquiv.contDiff
      (𝕜 := 𝕜) (n := n) using 1
    ext A u v
    rfl
  have hflip := hf.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hA.2
  have heq : (fun y ↦ ContinuousLinearMap.inCoordinates F₂ V₂ (F₁ →L[𝕜] F₃)
      (fun z ↦ V₁ z →L[𝕜] V₃ z) (b x) (b y) (b x) (b y) (A y).flip) =ᶠ[𝓝[insert x s] x]
      (fun y ↦ (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[𝕜] F₃)
        (fun z ↦ V₂ z →L[𝕜] V₃ z) (b x) (b y) (b x) (b y) (A y)).flip) := by
    filter_upwards [hnear] with y hy
    ext u v
    simp only [ContinuousLinearMap.flip_apply]
    rw [inCoordinates_apply_eq₂ hy.1.2 hy.1.1 hy.2,
      inCoordinates_apply_eq₂ hy.1.1 hy.1.2 hy.2, ContinuousLinearMap.flip_apply]
  exact hflip.congr_of_eventuallyEq (heq.filter_mono (nhdsWithin_mono _ (Set.subset_insert x s)))
    (heq.self_of_nhdsWithin (Set.mem_insert x s))

/-- Interchanging the two inputs of a family of bilinear bundle maps over a base map `b` preserves
`C^n` regularity at a point. -/
theorem ContMDiffAt.clm_bundle_flip
    (hA : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (E := fun z ↦ V₁ z →L[𝕜] V₂ z →L[𝕜] V₃ z) (b y) (A y)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (E := fun z ↦ V₂ z →L[𝕜] V₁ z →L[𝕜] V₃ z) (b y) (A y).flip) x :=
  ContMDiffWithinAt.clm_bundle_flip hA

/-- Interchanging the two inputs of a family of bilinear bundle maps over a base map `b` preserves
`C^n` regularity. -/
theorem ContMDiff.clm_bundle_flip
    (hA : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
        (E := fun z ↦ V₁ z →L[𝕜] V₂ z →L[𝕜] V₃ z) (b y) (A y))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁ →L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁ →L[𝕜] F₃)
        (E := fun z ↦ V₂ z →L[𝕜] V₁ z →L[𝕜] V₃ z) (b y) (A y).flip) :=
  fun x ↦ (hA x).clm_bundle_flip

end Flip

end BaseMap

section SingleBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞ω}

namespace TauCeti.Manifold

variable (IB F V G n) in
/-- `C^n` bilinear fields with values in a normed space on a vector bundle. -/
abbrev BilinearSection :=
  Cₛ^n⟮IB; F →L[𝕜] F →L[𝕜] G, fun x : B ↦ V x →L[𝕜] V x →L[𝕜] G⟯

/-- Transposition as a linear involution on `C^n` bilinear fields. -/
def transposeBilinearSection :
    BilinearSection IB F V G n →ₗ[𝕜]
      BilinearSection IB F V G n :=
  -- Transfer normability without changing the topology or choosing fibre norms.
  letI : ∀ x, IsNormableSpace 𝕜 (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).isNormableSpace
  { toFun b := ⟨fun x ↦ (b x).flip, contMDiffOn_univ.1 fun x _ ↦
      (b.contMDiff x).contMDiffWithinAt.clm_bundle_flip⟩
    map_add' b c := by ext x v w; simp
    map_smul' a b := by ext x v w; simp }

@[simp]
theorem transposeBilinearSection_apply
    (b : BilinearSection IB F V G n)
    (x : B) (v w : V x) : transposeBilinearSection b x v w = b x w v := by
  -- The term-mode definition evaluates to the fibrewise flip.
  rfl

/-- Transposing a `C^n` bilinear field twice recovers the original field. -/
@[simp]
theorem transposeBilinearSection_transposeBilinearSection
    (b : BilinearSection IB F V G n) :
    transposeBilinearSection (transposeBilinearSection b) = b := by
  ext x v w
  simp

/-- The linear subspace of symmetric `C^n` bilinear fields. -/
def symmetricBilinearSections :
    Submodule 𝕜 (BilinearSection IB F V G n) :=
  LinearMap.ker (transposeBilinearSection - LinearMap.id)

@[simp]
theorem mem_symmetricBilinearSections
    (b : BilinearSection IB F V G n) :
    b ∈ symmetricBilinearSections ↔ ∀ x v w, b x v w = b x w v := by
  simp only [symmetricBilinearSections, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h x v w
    simpa using congrArg (fun c ↦ c x w v) h
  · intro h
    ext x v w
    simpa using h x w v

/-- Transposition fixes every symmetric section. -/
@[simp]
theorem transposeBilinearSection_of_mem
    {b : BilinearSection IB F V G n}
    (hb : b ∈ symmetricBilinearSections) : transposeBilinearSection b = b := by
  simpa only [symmetricBilinearSections, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] using hb

/-- The symmetrization projection `b ↦ (b + bᵀ) / 2` on `C^n` bilinear fields. -/
def symmetrizeBilinearSection :
    BilinearSection IB F V G n →ₗ[𝕜]
      BilinearSection IB F V G n :=
  (2 : 𝕜)⁻¹ • (LinearMap.id + transposeBilinearSection)

@[simp]
theorem symmetrizeBilinearSection_apply
    (b : BilinearSection IB F V G n)
    (x : B) (v w : V x) :
    symmetrizeBilinearSection b x v w = (2 : 𝕜)⁻¹ • (b x v w + b x w v) := by
  simp [symmetrizeBilinearSection]

/-- Symmetrization takes values in the symmetric sections. -/
@[simp↓]
theorem symmetrizeBilinearSection_mem
    (b : BilinearSection IB F V G n) :
    symmetrizeBilinearSection b ∈ symmetricBilinearSections := by
  simp [add_comm]

variable [NeZero (2 : 𝕜)]

/-- Symmetrization fixes every symmetric section. -/
@[simp]
theorem symmetrizeBilinearSection_of_mem
    {b : BilinearSection IB F V G n}
    (hb : b ∈ symmetricBilinearSections) : symmetrizeBilinearSection b = b := by
  ext x v w
  rw [symmetrizeBilinearSection_apply, (mem_symmetricBilinearSections b).mp hb x v w,
    ← two_smul 𝕜, inv_smul_smul₀ (NeZero.ne (2 : 𝕜))]

/-- Symmetrization is a projection onto the submodule of symmetric sections. -/
theorem isProj_symmetrizeBilinearSection :
    LinearMap.IsProj symmetricBilinearSections
      (symmetrizeBilinearSection (IB := IB) (F := F) (V := V) (G := G) (n := n)) where
  map_mem := symmetrizeBilinearSection_mem
  map_id _ := symmetrizeBilinearSection_of_mem

/-- The fixed points of symmetrization are exactly the symmetric sections. -/
@[simp]
theorem symmetrizeBilinearSection_eq_self_iff
    (b : BilinearSection IB F V G n) :
    symmetrizeBilinearSection b = b ↔ b ∈ symmetricBilinearSections :=
  isProj_symmetrizeBilinearSection.mem_iff_map_id.symm

/-- Every symmetric `C^n` field is the symmetrization of a `C^n` bilinear field. -/
theorem range_symmetrizeBilinearSection :
    LinearMap.range (symmetrizeBilinearSection (IB := IB) (F := F) (V := V) (G := G) (n := n)) =
      symmetricBilinearSections :=
  isProj_symmetrizeBilinearSection.range

end TauCeti.Manifold

section BilinearComp

variable [∀ x, IsNormableSpace 𝕜 (V x)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {W : B → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, TopologicalSpace (W x)] [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  [FiberBundle F' W] [VectorBundle 𝕜 F' W] [∀ x, IsNormableSpace 𝕜 (W x)]

/-- Precomposing both arguments of a bilinear field on `W` that is `C^n` at `x` with a field of
continuous linear maps `V x → W x` that is `C^n` at `x` gives a bilinear field on `V` that is
`C^n` at `x`. -/
theorem ContMDiffAt.bilinearComp_bundle {x : B}
    {β : ∀ x, W x →L[𝕜] W x →L[𝕜] G}
    (hβ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F' →L[𝕜] F' →L[𝕜] G)) n (fun x ↦
      TotalSpace.mk' (F' →L[𝕜] F' →L[𝕜] G) (E := fun y ↦ W y →L[𝕜] W y →L[𝕜] G) x (β x)) x)
    {A : ∀ x, V x →L[𝕜] W x}
    (hA : ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n (fun x ↦
      TotalSpace.mk' (F →L[𝕜] F') (E := fun y ↦ V y →L[𝕜] W y) x (A x)) x) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n (fun x ↦
      TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] V y →L[𝕜] G) x
        ((β x).bilinearComp (A x) (A x))) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let a (y : B) := ContinuousLinearMap.inCoordinates F V F' W x y x y (A y)
  let q (y : B) := ContinuousLinearMap.inCoordinates F' W (F' →L[𝕜] G)
    (fun z ↦ W z →L[𝕜] G) x y x y (β y)
  have ha : ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] F') n a x :=
    ((contMDiffAt_hom_bundle _).mp hA).2
  have hq : ContMDiffAt IB 𝓘(𝕜, F' →L[𝕜] F' →L[𝕜] G) n q x :=
    ((contMDiffAt_hom_bundle _).mp hβ).2
  have hc := (ha.clm_precomp (F₃ := G)).clm_comp (hq.clm_comp ha)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V x),
    (trivializationAt F' W x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F' W x)] with y hyV hyW
  dsimp only [a, q]
  ext v w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  rw [inCoordinates_apply_eq₂ hyV hyV (by simp), inCoordinates_apply_eq₂ hyW hyW (by simp)]
  simp [ContinuousLinearMap.inCoordinates, hyV, hyW]

/-- Precomposing both arguments of a `C^n` bilinear field on `W` with a `C^n` field of
continuous linear maps `V x → W x` gives a `C^n` bilinear field on `V`. -/
theorem ContMDiff.bilinearComp_bundle
    {β : ∀ x, W x →L[𝕜] W x →L[𝕜] G}
    (hβ : ContMDiff IB (IB.prod 𝓘(𝕜, F' →L[𝕜] F' →L[𝕜] G)) n (fun x ↦
      TotalSpace.mk' (F' →L[𝕜] F' →L[𝕜] G) (E := fun y ↦ W y →L[𝕜] W y →L[𝕜] G) x (β x)))
    {A : ∀ x, V x →L[𝕜] W x}
    (hA : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n (fun x ↦
      TotalSpace.mk' (F →L[𝕜] F') (E := fun y ↦ V y →L[𝕜] W y) x (A x))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n (fun x ↦
      TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) (E := fun y ↦ V y →L[𝕜] V y →L[𝕜] G) x
        ((β x).bilinearComp (A x) (A x))) :=
  fun x ↦ (hβ x).bilinearComp_bundle (hA x)

end BilinearComp

end SingleBundle
