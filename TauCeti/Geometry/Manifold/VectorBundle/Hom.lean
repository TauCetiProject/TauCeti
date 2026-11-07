/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Topology.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Topology.VectorBundle.Coordinates
import TauCeti.Data.Bundle
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension

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
(`TauCeti.contMDiff_const_bundlePairing`). A hom-bundle section whose coordinate expressions are
constant on the common frame domains is smooth
(`TauCeti.contMDiff_hom_bundle_of_inCoordinates_eq_const`).

Negation of a hom-bundle section along any base map preserves its regularity
(`ContMDiff.clm_bundle_neg`). Interchanging the inputs of a smooth bilinear bundle map preserves
smoothness
(`ContMDiffWithinAt.clm_bundle_flip`), without a choice of fibre norms. This permits
contraction of a smooth tensor in any input slot.

Finally, a family of fibrewise linear maps with finite-dimensional model source is a `C^n`
section of the hom bundle exactly when the map of total spaces it induces is `C^n`
(`TauCeti.contMDiff_hom_bundle_iff`, with a pointwise version
`TauCeti.contMDiffAt_hom_bundle_iff`); this needs neither bundle to be a `C^n` vector bundle.
The same holds for families depending on a parameter in a manifold `P`, as sections along the
projection `P × B → B` and maps `P × TotalSpace F₁ E₁ → TotalSpace F₂ E₂`
(`TauCeti.contMDiff_hom_bundle_prod_iff`, `TauCeti.contMDiffAt_hom_bundle_prod_iff`).
Combined with fibrewise inversion, a `C^n` family of fibrewise linear equivalences therefore
induces a `C^n` diffeomorphism of total spaces, `TauCeti.bundleDiffeomorph`, whose inverse is
automatically `C^n`. Over the model `𝓘(ℂ, EB)` with `n = ∞`, these are the holomorphic bundle
morphisms and equivalences of holomorphic vector bundles. They are the `C^n` counterparts of
`TauCeti.continuous_hom_bundle_iff` and `TauCeti.bundleHomeomorph`. A family of fibrewise linear
maps is realized by a `C^n` diffeomorphism of total spaces exactly when its total-space map is
`C^n` and its fibre maps are bijective (`TauCeti.exists_bundleDiffeomorph_iff`).
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

namespace TauCeti

section ConstantCoordinates

variable {𝕜 M F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace M] {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V : M → Type*} {W : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  [TopologicalSpace (TotalSpace F₁ V)] [FiberBundle F₁ V] [VectorBundle 𝕜 F₁ V]
  [TopologicalSpace (TotalSpace F₂ W)] [FiberBundle F₂ W] [VectorBundle 𝕜 F₂ W]
  {n : WithTop ℕ∞}

/-- A hom-bundle section is smooth if its expression in the preferred frames at each point
is constant on their common base set. The constant may depend on the centre of the frames;
no smoothness assumption on either vector bundle is needed. -/
theorem contMDiff_hom_bundle_of_inCoordinates_eq_const
    {ϕ : ∀ x, V x →L[𝕜] W x} {c : M → F₁ →L[𝕜] F₂}
    (hϕ : ∀ a x, x ∈ (trivializationAt F₁ V a).baseSet →
      x ∈ (trivializationAt F₂ W a).baseSet →
      ContinuousLinearMap.inCoordinates F₁ V F₂ W a x a x (ϕ x) = c a) :
    ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (ϕ x)) := by
  intro a
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, (contMDiffAt_const (c := c a)).congr_of_eventuallyEq ?_⟩
  filter_upwards [(trivializationAt F₁ V a).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F₁ V a), (trivializationAt F₂ W a).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F₂ W a)] with x hx₁ hx₂
  exact hϕ a x hx₁ hx₂

end ConstantCoordinates

end TauCeti

section Neg

variable {𝕜 B M F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  {EB HB EM HM : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M]
  [ChartedSpace HM M] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {V : B → Type*} {W : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, AddCommGroup (W b)] [∀ b, Module 𝕜 (W b)] [∀ b, TopologicalSpace (W b)]
  [∀ b, IsTopologicalAddGroup (W b)] [∀ b, ContinuousSMul 𝕜 (W b)]
  [TopologicalSpace (TotalSpace F₁ V)] [FiberBundle F₁ V] [VectorBundle 𝕜 F₁ V]
  [TopologicalSpace (TotalSpace F₂ W)] [FiberBundle F₂ W] [VectorBundle 𝕜 F₂ W]
  {n : WithTop ℕ∞} {b : M → B} {A : ∀ y, V (b y) →L[𝕜] W (b y)}

/-- Negating a hom-bundle section along any base map preserves its regularity. -/
theorem ContMDiff.clm_bundle_neg
    (hA : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
        (E := fun x ↦ V x →L[𝕜] W x) (b y) (A y))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
        (E := fun x ↦ V x →L[𝕜] W x) (b y) (-A y)) := by
  intro x
  have h := hA x
  rw [contMDiffAt_hom_bundle] at h ⊢
  refine ⟨h.1, ?_⟩
  simpa only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.neg_comp] using h.2.neg

end Neg

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

namespace TauCeti

section BundleMap

variable {𝕜 B F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP] {HP : Type*} [TopologicalSpace HP]
  {IP : ModelWithCorners 𝕜 EP HP} {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

/-- For a finite-dimensional model source, a family of fibrewise linear maps depending on a
parameter in a manifold `P`, that is a Hom-bundle section along the projection `P × B → B`, is
`C^n` at `(p, x)` exactly when the induced map `P × TotalSpace F₁ E₁ → TotalSpace F₂ E₂` is `C^n`
at every point `(p, v)` with `v` in the fibre over `x`. The target need not have finite rank. -/
theorem contMDiffAt_hom_bundle_prod_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
    (ϕ : ∀ q : P × B, E₁ q.2 →L[𝕜] E₂ q.2) (q : P × B) :
    ContMDiffAt (IP.prod IB) (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
        (fun y : P × B ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) y.2
          (ϕ y)) q ↔
      ∀ v : E₁ q.2, ContMDiffAt (IP.prod (IB.prod 𝓘(𝕜, F₁))) (IB.prod 𝓘(𝕜, F₂)) n
        (fun p : P × TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.2.proj (ϕ (p.1, p.2.proj) p.2.2))
        (q.1, ⟨q.2, v⟩) := by
  constructor
  · intro hϕ v
    have h : ContMDiffAt (IP.prod (IB.prod 𝓘(𝕜, F₁))) (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
        (fun p : P × TotalSpace F₁ E₁ ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
          (E := fun y ↦ E₁ y →L[𝕜] E₂ y) p.2.proj (ϕ (p.1, p.2.proj))) (q.1, ⟨q.2, v⟩) :=
      hϕ.comp (x := (q.1, (⟨q.2, v⟩ : TotalSpace F₁ E₁)))
        (contMDiffAt_fst.prodMk ((contMDiffAt_proj E₁).comp _ contMDiffAt_snd))
    exact h.clm_bundle_apply contMDiffAt_snd
  · intro hϕ
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_snd, contMDiffAt_clm_apply.2 fun w ↦ ?_⟩
    let e₁ := trivializationAt F₁ E₁ q.2
    let e₂ := trivializationAt F₂ E₂ q.2
    have h₁ : q.2 ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ q.2
    have h₂ : q.2 ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ q.2
    -- The section `y ↦ e₁.symm y w` is `C^n` near `q.2`: read in `e₁`, it is constant.
    have hs : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) n
        (fun y ↦ TotalSpace.mk' F₁ y (e₁.symm y w)) q.2 := by
      rw [contMDiffAt_section]
      refine (contMDiffAt_const (c := w)).congr_of_eventuallyEq ?_
      filter_upwards [e₁.open_baseSet.mem_nhds h₁] with y hy
      exact congr(Prod.snd $(e₁.apply_mk_symm hy w))
    -- Applying the total-space map to this section, with the parameter, and reading the result
    -- in `e₂` gives the coordinate expression of `ϕ` applied to `w`.
    have ht := (contMDiffAt_totalSpace.1 ((hϕ (e₁.symm q.2 w)).comp q
      (contMDiffAt_fst.prodMk (hs.comp q contMDiffAt_snd)))).2
    refine ht.congr_of_eventuallyEq ?_
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (e₁.open_baseSet.mem_nhds h₁), continuous_snd.continuousAt.preimage_mem_nhds
      (e₂.open_baseSet.mem_nhds h₂)] with y hy₁ hy₂
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [e₁.symmL_apply hy₁, Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ hy₂]
    -- `TotalSpace.mk'` is the total-space constructor; the second component of
    -- `e₂` applied to this point is precisely its fibre coordinate.
    rfl

/-- For a finite-dimensional model source, a family of fibrewise linear maps depending on a
parameter in a manifold `P` is a `C^n` Hom-bundle section along the projection `P × B → B`
exactly when the induced map `P × TotalSpace F₁ E₁ → TotalSpace F₂ E₂` is `C^n`. -/
theorem contMDiff_hom_bundle_prod_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
    (ϕ : ∀ q : P × B, E₁ q.2 →L[𝕜] E₂ q.2) :
    ContMDiff (IP.prod IB) (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
        (fun y : P × B ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) y.2
          (ϕ y)) ↔
      ContMDiff (IP.prod (IB.prod 𝓘(𝕜, F₁))) (IB.prod 𝓘(𝕜, F₂)) n
        (fun p : P × TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.2.proj (ϕ (p.1, p.2.proj) p.2.2)) :=
  ⟨fun hϕ p ↦ (contMDiffAt_hom_bundle_prod_iff ϕ (p.1, p.2.proj)).1 (hϕ _) p.2.2,
    fun hϕ q ↦ (contMDiffAt_hom_bundle_prod_iff ϕ q).2 fun v ↦ hϕ (q.1, ⟨q.2, v⟩)⟩

/-- For a finite-dimensional model source, a family of fibrewise linear maps is a Hom-bundle
section which is `C^n` at `x` exactly when the induced map of total spaces is `C^n` at every
point of the fibre over `x`. The target need not have finite rank. -/
theorem contMDiffAt_hom_bundle_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
    (ϕ : ∀ x, E₁ x →L[𝕜] E₂ x) (x : B) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) y (ϕ y)) x ↔
      ∀ v : E₁ x, ContMDiffAt (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
        (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)) ⟨x, v⟩ := by
  -- This is the case of a family that does not depend on its parameter, taken in `B` itself.
  have h := contMDiffAt_hom_bundle_prod_iff (IB := IB) (IP := IB) (n := n) (F₁ := F₁) (F₂ := F₂)
    (fun q : B × B ↦ ϕ q.2) (x, x)
  refine ⟨fun hϕ v ↦ ?_, fun hϕ ↦ ?_⟩
  · exact (h.1 (hϕ.comp (x, x) contMDiffAt_snd) v).comp (x := (⟨x, v⟩ : TotalSpace F₁ E₁))
      (contMDiffAt_const.prodMk contMDiffAt_id)
  · exact (h.2 fun v ↦ (hϕ v).comp (x := ((x, ⟨x, v⟩) : B × TotalSpace F₁ E₁)) contMDiffAt_snd).comp
      x (contMDiffAt_const.prodMk contMDiffAt_id)

/-- For a finite-dimensional model source, a family of fibrewise linear maps is a `C^n` section
of the Hom bundle exactly when the induced map of total spaces is `C^n`. This is the `C^n`
counterpart of `TauCeti.continuous_hom_bundle_iff`; the target need not have finite rank. -/
theorem contMDiff_hom_bundle_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
    (ϕ : ∀ x, E₁ x →L[𝕜] E₂ x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
        (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ϕ x)) ↔
      ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
        (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)) :=
  ⟨fun hϕ p ↦ (contMDiffAt_hom_bundle_iff ϕ p.proj).1 (hϕ p.proj) p.2,
    fun hϕ x ↦ (contMDiffAt_hom_bundle_iff ϕ x).2 fun v ↦ hϕ ⟨x, v⟩⟩

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]

/-- A `C^n` fibrewise linear equivalence with finite-dimensional model source has a `C^n`
inverse on total spaces. -/
theorem contMDiff_bundle_symm (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.2))) :
    ContMDiff (IB.prod 𝓘(𝕜, F₂)) (IB.prod 𝓘(𝕜, F₁)) n
      (fun p : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₁ p.proj ((e p.proj).symm p.2)) := by
  let := FiniteDimensional.complete 𝕜 F₁
  have h := (contMDiff_hom_bundle_iff (fun x ↦ (e x).toContinuousLinearMap)).2 he
  have hi := h.clm_bundle_inverse fun x ↦ ContinuousLinearMap.isInvertible_equiv
  have ha := (hi.comp (contMDiff_proj E₂)).clm_bundle_apply contMDiff_id
  simpa only [ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe] using ha

/-- The `C^n` diffeomorphism of total spaces induced by a `C^n` family of fibrewise linear
equivalences, with finite-dimensional model source. Smoothness of the inverse is automatic. -/
def bundleDiffeomorph (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
    (he : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.2))) :
    TotalSpace F₁ E₁ ≃ₘ^n⟮IB.prod 𝓘(𝕜, F₁), IB.prod 𝓘(𝕜, F₂)⟯ TotalSpace F₂ E₂ where
  toFun p := ⟨p.proj, e p.proj p.2⟩
  invFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := he
  contMDiff_invFun := contMDiff_bundle_symm e he

variable (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
  (he : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
    (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.2)))

@[simp]
theorem bundleDiffeomorph_apply (p : TotalSpace F₁ E₁) :
    bundleDiffeomorph e he p = ⟨p.proj, e p.proj p.2⟩ :=
  (rfl)

@[simp]
theorem bundleDiffeomorph_symm_apply (p : TotalSpace F₂ E₂) :
    (bundleDiffeomorph e he).symm p = ⟨p.proj, (e p.proj).symm p.2⟩ :=
  (rfl)

/-- The underlying homeomorphism of `bundleDiffeomorph` is `bundleHomeomorph`. -/
@[simp]
theorem toHomeomorph_bundleDiffeomorph :
    (bundleDiffeomorph e he).toHomeomorph = bundleHomeomorph e he.continuous :=
  Homeomorph.ext fun p ↦ by simp

/-- For a finite-dimensional model source, a family of fibrewise linear maps is realized by a
`C^n` diffeomorphism of total spaces exactly when the induced map of total spaces is `C^n` and
every fibre map is bijective. -/
theorem exists_bundleDiffeomorph_iff (ϕ : ∀ x, E₁ x →L[𝕜] E₂ x) :
    (∃ Φ : TotalSpace F₁ E₁ ≃ₘ^n⟮IB.prod 𝓘(𝕜, F₁), IB.prod 𝓘(𝕜, F₂)⟯ TotalSpace F₂ E₂,
        ⇑Φ = fun p ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)) ↔
      ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
          (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (ϕ p.proj p.2)) ∧
        ∀ x, Function.Bijective (ϕ x) := by
  refine ⟨fun ⟨Φ, hΦ⟩ ↦ ⟨hΦ ▸ Φ.contMDiff, bijective_totalSpace_map_iff.1 (hΦ ▸ Φ.bijective)⟩,
    fun ⟨hϕ, hbij⟩ ↦ ?_⟩
  -- A bijective fibre map is an isomorphism, since the fibres are finite-dimensional.
  have h (x : B) : ∃ e : E₁ x ≃L[𝕜] E₂ x, ⇑e = ϕ x := by
    let := FiberBundle.t2Space F₁ E₁ x
    let := FiberBundle.t2Space F₂ E₂ x
    let := VectorBundle.finiteDimensional 𝕜 F₁ E₁ x
    exact ⟨(LinearEquiv.ofBijective (ϕ x).toLinearMap (hbij x)).toContinuousLinearEquiv, rfl⟩
  choose e he using h
  exact ⟨bundleDiffeomorph e (hϕ.congr fun p ↦ by simp [he]), funext fun p ↦ by simp [he]⟩

end BundleMap

end TauCeti

section Flip

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB EM : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HB HM : Type*} [TopologicalSpace HB] [TopologicalSpace HM]
  {IB : ModelWithCorners 𝕜 EB HB} {IM : ModelWithCorners 𝕜 EM HM}
  {B M : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace M] [ChartedSpace HM M]
  {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {V₁ V₂ V₃ : B → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module 𝕜 (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [∀ x, IsNormableSpace 𝕜 (V₁ x)] [∀ x, IsNormableSpace 𝕜 (V₂ x)]
  [∀ x, IsNormableSpace 𝕜 (V₃ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul 𝕜 (V₃ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [TopologicalSpace (TotalSpace F₃ V₃)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]
  {b : M → B} {s : Set M} {x : M} {n : ℕ∞ω}
  {A : ∀ x, V₁ (b x) →L[𝕜] V₂ (b x) →L[𝕜] V₃ (b x)}

/-- Interchanging the two inputs of a smooth family of bilinear bundle maps preserves
smoothness, also within a parameter set. -/
theorem _root_.ContMDiffWithinAt.clm_bundle_flip
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

end Flip
