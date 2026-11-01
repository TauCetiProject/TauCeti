/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Topology.VectorBundle.Coordinates
public import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Topology.VectorBundle.Hom

/-!
# Testing smooth bundle homomorphisms on sections

A section of a hom bundle with finite-dimensional source fibres is smooth if and only if
it sends every globally smooth section to a smooth section. This turns smoothness of
tensorial operations on sections into smoothness of the associated tensor field, by
applying the criterion once for each argument.

The criterion applies over arbitrary smooth finite-dimensional manifolds, including
noncompact manifolds and manifolds with boundary, and places no finite-dimensionality
assumption on the target fibres.

The file also records that pulling back a fixed continuous bilinear form on the model fibre
along a trivialization gives a `C^n` field of bilinear forms over its base set
(`TauCeti.Manifold.contMDiffOn_trivializationAt_pullbackForm`), and that fibrewise inversion
preserves smoothness of a hom-bundle section at every point where the section is invertible
(`ContMDiffWithinAt.clm_bundle_inverse` and its variants). The latter is the bundle form of the
smoothness of inversion of continuous linear maps between Banach spaces. A constant bilinear
pairing between trivial bundles is a smooth hom-bundle section
(`TauCeti.contMDiff_const_bundlePairing`).

Over a complete nontrivially normed field, a fibrewise continuous linear map with
finite-dimensional model source is `C^n` on total spaces exactly when it is a `C^n` hom-bundle
section (`TauCeti.contMDiff_hom_bundle_iff`), the `C^n` counterpart of
`TauCeti.continuous_hom_bundle_iff`. Fibrewise continuous linear equivalences forming a `C^n`
hom-bundle section induce a `C^n` diffeomorphism of total spaces
(`TauCeti.bundleDiffeomorph`), the counterpart of `TauCeti.bundleHomeomorph`. With
finite-dimensional model source, a fibrewise continuous linear map is realized by a `C^n`
diffeomorphism of total spaces exactly when it is a `C^n` hom-bundle section with invertible
fibre maps (`TauCeti.exists_bundleDiffeomorph_iff`).

For two vector bundle cores with `C^n` transition functions (`VectorBundleCore.IsContMDiff`), a
section of the Hom bundle between them is `C^n` exactly when it is `C^n` in every pair of a source
chart and a target chart, on their common domain, with chart expressions
`VectorBundleCore.inChartCoordinates`
(`VectorBundleCore.contMDiff_hom_bundle_iff_forall_contMDiffOn`). This is the `C^n` counterpart
of `VectorBundleCore.continuous_hom_bundle_iff_forall_continuousOn`.
-/

public section

open Bundle FiberBundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] {n : WithTop ℕ∞}

/-- A constant bilinear pairing is a smooth section of the hom bundle between trivial
coefficient bundles. -/
theorem contMDiff_const_bundlePairing (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃)
        (E := fun z ↦ Trivial M F₁ z →L[ℝ] Trivial M F₂ z →L[ℝ] Trivial M F₃ z) y μ) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have heq : (fun y ↦ ContinuousLinearMap.inCoordinates F₁ (Trivial M F₁)
      (F₂ →L[ℝ] F₃) (fun z ↦ Trivial M F₂ z →L[ℝ] Trivial M F₃ z) x y x y μ) =
      fun _ ↦ μ := by
    funext y
    ext v w
    rw [inCoordinates_apply_eq₂ (by simp [Trivial.eq_trivialization M F₁])
      (by simp [Trivial.eq_trivialization M F₂])
      (by simp [Trivial.eq_trivialization M F₃])]
    simp [Trivial.eq_trivialization M F₁, Trivial.eq_trivialization M F₂,
      Trivial.eq_trivialization M F₃]
  rw [heq]
  exact contMDiffAt_const

end TauCeti

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]

/-- A hom-bundle section with finite-dimensional source fibres is smooth exactly when
its evaluation on every globally smooth section is smooth. The target fibres need not
be finite-dimensional, and the base need not be compact or boundaryless. -/
theorem contMDiff_hom_iff (A : Π x : M, V x →L[ℝ] W x) :
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) x (A x)) ↔
      ∀ s : Π x : M, V x, CMDiff ∞ (T% s) →
        ContMDiff I (I.prod 𝓘(ℝ, G)) ∞ (fun x ↦ TotalSpace.mk' G x (A x (s x))) := by
  constructor
  · intro hA s hs
    exact hA.clm_bundle_apply hs
  · intro hA x
    let e := trivializationAt F V x
    let e' := trivializationAt G W x
    have hx : x ∈ e.baseSet ∩ e'.baseSet :=
      ⟨mem_baseSet_trivializationAt F V x, mem_baseSet_trivializationAt G W x⟩
    have hopen := e.open_baseSet.inter e'.open_baseSet
    obtain ⟨ρ, hρ, -⟩ :=
      (SmoothBumpFunction.nhds_basis_support (I := I) (hopen.mem_nhds hx)).mem_iff.mp
        (hopen.mem_nhds hx)
    obtain ⟨u, hu, huopen, hxu⟩ := mem_nhds_iff.mp
      (ρ.eventuallyEq_one.and (hopen.mem_nhds hx))
    let b := Module.Basis.ofVectorSpace ℝ F
    have htest (j) : CMDiff ∞ (T% ((ρ : M → ℝ) • e.localFrame b j)) :=
      ρ.contMDiff.contMDiffOn.smul_section_of_tsupport e.open_baseSet
        (hρ.trans inter_subset_left) (e.contMDiffOn_localFrame_baseSet ∞ b j)
    have hlocal := contMDiffOn_hom_of_localFrame (I := I) (e := e) (e' := e') b
      (f := fun y ↦ y) contMDiffOn_id (fun y hy ↦ (hu hy).2) (A := A) (fun j ↦
        ((hA _ (htest j)).contMDiffOn).congr (fun y hy ↦ by
          dsimp only [Pi.smul_apply']
          simp only [(hu hy).1, Pi.one_apply, one_smul]))
    exact hlocal.contMDiffAt (huopen.mem_nhds hxu)

section PullbackForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The field of bilinear forms `b ↦ φ (e b ·) (e b ·)` obtained by pulling back a fixed bilinear
form `φ` on the model fibre along the preferred trivialization `e` at `x` is `C^n` on the base set
of `e`. -/
theorem contMDiffOn_trivializationAt_pullbackForm [ContMDiffVectorBundle n F E IB]
    (φ : F →L[ℝ] F →L[ℝ] ℝ) (x : B) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b
        ((ContinuousLinearMap.precomp ℝ ((trivializationAt F E x).continuousLinearMapAt ℝ b)).comp
          (φ.comp ((trivializationAt F E x).continuousLinearMapAt ℝ b))))
      (trivializationAt F E x).baseSet := by
  -- Recording this instance locally keeps the instance search for the vector bundle structure on
  -- the bundle of bilinear forms within the default budget.
  have : ∀ b, ContinuousAdd (E b →L[ℝ] ℝ) := fun b ↦ inferInstance
  rw [Trivialization.contMDiffOn_section_iff (F := F →L[ℝ] F →L[ℝ] ℝ)
    (E := fun b ↦ E b →L[ℝ] E b →L[ℝ] ℝ) (trivializationAt _ _ x)
    (trivializationAt F E x).open_baseSet (by simp [hom_trivializationAt_baseSet])]
  -- Read in the corresponding trivialization of the bundle of bilinear forms, the field is the
  -- constant `φ`.
  refine (contMDiffOn_const (c := φ)).congr fun b hb ↦ ?_
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, hb]

end PullbackForm

end TauCeti.Manifold

section Inverse

variable {𝕜 B F₁ F₂ M : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [CompleteSpace F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b : M → B} {ϕ : ∀ m, E₁ (b m) →L[𝕜] E₂ (b m)} {s : Set M} {x : M}

/-- Consider linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending `C^n` on `m`, over a base map
`b : M → B`, with `ϕ x` invertible. Then the fibrewise inverses `(ϕ m).inverse` depend `C^n` on
`m` at `x`.

We give here a version of this statement within a set at a point. -/
theorem ContMDiffWithinAt.clm_bundle_inverse
    (hϕ : CMDiffAt[s] n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hx : (ϕ x).IsInvertible) :
    CMDiffAt[s] n
      (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m)
        (ϕ m).inverse) x := by
  simp only [contMDiffWithinAt_hom_bundle] at hϕ ⊢
  refine ⟨hϕ.1, ?_⟩
  have h₁ := mem_baseSet_trivializationAt F₁ E₁ (b x)
  have h₂ := mem_baseSet_trivializationAt F₂ E₂ (b x)
  -- In coordinates centred at `b x`, the coordinate expression of `ϕ x` is invertible.
  have hinv : (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ (b x) (b x) (b x) (b x)
      (ϕ x)).IsInvertible := by
    rw [ContinuousLinearMap.inCoordinates_eq h₁ h₂]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (hx.comp ContinuousLinearMap.isInvertible_equiv)
  -- Near `x`, the inverse in coordinates is the inverse of the coordinate expression, and
  -- inversion is smooth at an invertible map.
  have hev : ∀ᶠ m in 𝓝[s] x, b m ∈ (trivializationAt F₁ E₁ (b x)).baseSet ∧
      b m ∈ (trivializationAt F₂ E₂ (b x)).baseSet :=
    hϕ.1.continuousWithinAt.preimage_mem_nhdsWithin <| Filter.inter_mem
      ((trivializationAt F₁ E₁ (b x)).open_baseSet.mem_nhds h₁)
      ((trivializationAt F₂ E₂ (b x)).open_baseSet.mem_nhds h₂)
  have hcomp := (hinv.contDiffAt_map_inverse (n := n)).contMDiffAt.comp_contMDiffWithinAt x hϕ.2
  refine hcomp.congr_of_eventuallyEq ?_ (ContinuousLinearMap.inCoordinates_inverse (ϕ x) h₁ h₂)
  filter_upwards [hev] with m hm
  exact ContinuousLinearMap.inCoordinates_inverse (ϕ m) hm.1 hm.2

/-- Consider linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending `C^n` on `m`, over a base map
`b : M → B`, with `ϕ x` invertible. Then the fibrewise inverses `(ϕ m).inverse` depend `C^n` on
`m` at `x`.

We give here a version of this statement at a point. -/
theorem ContMDiffAt.clm_bundle_inverse
    (hϕ : CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hx : (ϕ x).IsInvertible) :
    CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m)
        (ϕ m).inverse) x :=
  ContMDiffWithinAt.clm_bundle_inverse hϕ hx

/-- Consider linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending `C^n` on `m`, over a base map
`b : M → B`, and invertible on `s`. Then the fibrewise inverses `(ϕ m).inverse` depend `C^n` on
`m` on `s`. -/
theorem ContMDiffOn.clm_bundle_inverse
    (hϕ : CMDiff[s] n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hs : ∀ x ∈ s, (ϕ x).IsInvertible) :
    CMDiff[s] n
      (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m)
        (ϕ m).inverse) :=
  fun x hx ↦ (hϕ x hx).clm_bundle_inverse (hs x hx)

/-- Consider linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending `C^n` on `m`, over a base map
`b : M → B`, and all invertible. Then the fibrewise inverses `(ϕ m).inverse` depend `C^n` on
`m`. -/
theorem ContMDiff.clm_bundle_inverse
    (hϕ : CMDiff n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hinv : ∀ x, (ϕ x).IsInvertible) :
    CMDiff n
      (fun m ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun (x : B) ↦ (E₂ x →L[𝕜] E₁ x)) (b m)
        (ϕ m).inverse) :=
  fun x ↦ (hϕ x).clm_bundle_inverse (hinv x)

end Inverse

section BundleMap

variable {𝕜 B F₁ F₂ EB HB : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

namespace TauCeti

/-- For a finite-dimensional model source, a fibrewise continuous linear map is `C^n` on total
spaces exactly when it is a `C^n` section of the Hom bundle. The target need not have finite
rank, and the base may be any manifold, possibly with boundary. -/
theorem contMDiff_hom_bundle_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    (ϕ : ∀ x, E₁ x →L[𝕜] E₂ x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
        (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ϕ x)) ↔
      ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
        (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)) := by
  refine ⟨fun hϕ ↦ (hϕ.comp (contMDiff_proj E₁)).clm_bundle_apply contMDiff_id, fun hϕ x ↦ ?_⟩
  let e₁ := trivializationAt F₁ E₁ x
  let e₂ := trivializationAt F₂ E₂ x
  let b := Module.Basis.ofVectorSpace 𝕜 F₁
  -- Test the section on the local frame of `E₁` given by `e₁` and a basis of `F₁`.
  have h := Manifold.contMDiffOn_hom_of_localFrame (e := e₁) (e' := e₂) b (f := fun y ↦ y)
    contMDiffOn_id (fun _ hy ↦ hy) (A := ϕ) fun j ↦
      (hϕ.comp_contMDiffOn (e₁.contMDiffOn_localFrame_baseSet n b j)).mono inter_subset_left
  exact h.contMDiffAt ((e₁.open_baseSet.inter e₂.open_baseSet).mem_nhds
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩)

variable [CompleteSpace F₁] [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]

/-- The `C^n` diffeomorphism of total spaces induced by fibrewise continuous linear equivalences
forming a `C^n` section of the Hom bundle. The inverse is `C^n` because fibrewise inversion
preserves smoothness of Hom-bundle sections; no finite-dimensionality is needed. -/
def bundleDiffeomorph (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x
        (e x : E₁ x →L[𝕜] E₂ x))) :
    TotalSpace F₁ E₁ ≃ₘ^n⟮IB.prod 𝓘(𝕜, F₁), IB.prod 𝓘(𝕜, F₂)⟯ TotalSpace F₂ E₂ where
  toFun p := ⟨p.proj, e p.proj p.2⟩
  invFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := (he.comp (contMDiff_proj E₁)).clm_bundle_apply contMDiff_id
  contMDiff_invFun := by
    have hi := he.clm_bundle_inverse fun x ↦ ContinuousLinearMap.isInvertible_equiv
    have h := (hi.comp (contMDiff_proj E₂)).clm_bundle_apply contMDiff_id
    simp only [ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe] at h
    exact h

@[simp]
theorem bundleDiffeomorph_apply (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x
        (e x : E₁ x →L[𝕜] E₂ x)))
    (p : TotalSpace F₁ E₁) : bundleDiffeomorph e he p = ⟨p.proj, e p.proj p.2⟩ :=
  (rfl)

@[simp]
theorem bundleDiffeomorph_symm_apply (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x
        (e x : E₁ x →L[𝕜] E₂ x)))
    (p : TotalSpace F₂ E₂) : (bundleDiffeomorph e he).symm p = ⟨p.proj, (e p.proj).symm p.2⟩ :=
  (rfl)

omit [CompleteSpace F₁] in
/-- For a finite-dimensional model source, a fibrewise continuous linear map is realized by a
`C^n` diffeomorphism of total spaces exactly when it is a `C^n` section of the Hom bundle and
every fibre map is invertible. -/
theorem exists_bundleDiffeomorph_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    (ϕ : ∀ x, E₁ x →L[𝕜] E₂ x) :
    (∃ Φ : TotalSpace F₁ E₁ ≃ₘ^n⟮IB.prod 𝓘(𝕜, F₁), IB.prod 𝓘(𝕜, F₂)⟯ TotalSpace F₂ E₂,
        ⇑Φ = fun p ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)) ↔
      ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
          (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ϕ x)) ∧
        ∀ x, (ϕ x).IsInvertible := by
  have := FiniteDimensional.complete 𝕜 F₁
  constructor
  · rintro ⟨Φ, hΦ⟩
    refine ⟨(contMDiff_hom_bundle_iff ϕ).2 (hΦ ▸ Φ.contMDiff), fun x ↦ ?_⟩
    -- A bijective fibre map is an isomorphism in finite dimension.
    let := FiberBundle.t2Space F₁ E₁ x
    let := FiberBundle.t2Space F₂ E₂ x
    let := VectorBundle.finiteDimensional 𝕜 F₁ E₁ x
    have hx : Function.Bijective (ϕ x) :=
      (bijective_totalSpace_map_iff (ϕ := fun x ↦ ϕ x)).1 (hΦ ▸ Φ.bijective) x
    exact ⟨(LinearEquiv.ofBijective (ϕ x).toLinearMap hx).toContinuousLinearEquiv, rfl⟩
  · rintro ⟨hϕ, hinv⟩
    choose e he using hinv
    refine ⟨bundleDiffeomorph e ?_, ?_⟩
    · convert hϕ using 3
      exact he _
    · funext p
      exact congrArg (TotalSpace.mk' F₂ p.proj) (DFunLike.congr_fun (he p.proj) p.2)

end TauCeti

end BundleMap

namespace VectorBundleCore

variable {𝕜 B F G EB HB ι κ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞} {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}
  [Z.IsContMDiff IB n] [W.IsContMDiff IB n]

/-- On the common domain of a source chart and a target chart, a section of the Hom bundle
between two cores is `C^n` exactly when its expression in those charts is. -/
theorem contMDiffOn_hom_bundle_iff_inChartCoordinates {f : B → F →L[𝕜] G} (i : ι) (j : κ) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x))
        (Z.baseSet i ∩ W.baseSet j) ↔
      ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n (fun x ↦ Z.inChartCoordinates W i j x (f x))
        (Z.baseSet i ∩ W.baseSet j) := by
  have : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
  have : MemTrivializationAtlas (W.localTriv j) := ⟨⟨j, rfl⟩⟩
  -- Read the section in the Hom-bundle trivialization built from the two fixed charts.
  let e := (Z.localTriv i).continuousLinearMap (RingHom.id 𝕜) (W.localTriv j)
  exact e.contMDiffOn_section_baseSet_iff.trans (contMDiffOn_congr fun x hx ↦
    (inChartCoordinates_eq_localTriv_comp hx.1 hx.2 (f x)).symm)

/-- A section of the Hom bundle between two cores is `C^n` exactly when it is `C^n` in every pair
of charts, on their common domain. -/
theorem contMDiff_hom_bundle_iff_forall_contMDiffOn {f : B → F →L[𝕜] G} :
    ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun y ↦ Z.Fiber y →L[𝕜] W.Fiber y) x (f x)) ↔
      ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] G) n (fun x ↦ Z.inChartCoordinates W i j x (f x))
        (Z.baseSet i ∩ W.baseSet j) := by
  refine ⟨fun hf i j ↦ (contMDiffOn_hom_bundle_iff_inChartCoordinates i j).1 hf.contMDiffOn,
    fun h x ↦ ?_⟩
  have hU := (Z.isOpen_baseSet (Z.indexAt x)).inter (W.isOpen_baseSet (W.indexAt x))
  exact ((contMDiffOn_hom_bundle_iff_inChartCoordinates _ _).2 (h _ _)).contMDiffAt
    (hU.mem_nhds ⟨Z.mem_baseSet_at x, W.mem_baseSet_at x⟩)

end VectorBundleCore
