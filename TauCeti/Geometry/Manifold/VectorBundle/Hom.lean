/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

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
(`TauCeti.Manifold.contMDiffOn_trivializationAt_pullbackForm`).
-/

public section

open Bundle FiberBundle Set
open scoped ContDiff Manifold Topology

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
