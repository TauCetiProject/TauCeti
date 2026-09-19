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

The reverse implication uses `TauCeti.Manifold.contMDiffOn_hom_of_localFrame`, cutting
off its local frame with a smooth bump function that equals one near the point, as in
`TauCeti.Manifold.eq_of_contMDiff_tensorial`.
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
      huopen (fun y hy ↦ (hu hy).2) (A := A) (fun j ↦
        ((hA _ (htest j)).contMDiffOn).congr (fun y hy ↦ by
          dsimp only [Pi.smul_apply']
          simp only [(hu hy).1, Pi.one_apply, one_smul]))
    exact hlocal.contMDiffAt (huopen.mem_nhds hxu)

end TauCeti.Manifold
