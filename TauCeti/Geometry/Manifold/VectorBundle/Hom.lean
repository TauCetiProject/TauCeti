/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Topology.VectorBundle.Coordinates

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
      (fun y hy ↦ (hu hy).2) (A := A) (fun j ↦
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
