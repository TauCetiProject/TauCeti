/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smoothly varying left inverses

Let `𝕜 → 𝕜'` be a normed field extension. Let `A x` be a continuous `𝕜'`-linear map from a Banach
space `G` to a normed space `F`, depending `C^n` over `𝕜` on a point `x` of a manifold. If `A x₀`
has a continuous left inverse `P`, then the compression `P ∘ A x` is the identity at `x₀`, hence
invertible near `x₀`, and `(P ∘ A x)⁻¹ ∘ P` is a left inverse of `A x` for `x` near `x₀`. Operator
inversion is analytic over the ground field on the invertible operators, so this left inverse is
again `C^n` over `𝕜` at `x₀`, while retaining its `𝕜'`-linearity. The supplied ground-field scalar
structures are preserved. This is the smooth counterpart of
`ContinuousAt.exists_continuousAt_leftInverse`.

For `G = (𝕜')ᵏ` and `A x` the operator `c ↦ ∑ i, c i • X i x` of a family of linearly independent
vectors depending smoothly on `x`, the left inverse sends a vector of the span of the `X i x` to
its coordinates. So coordinates in a smoothly moving basis depend smoothly on the base point,
which is what makes the local trivializations of a subbundle spanned by smooth local frames
smoothly compatible.

## Main results

* `ContMDiffAt.exists_contMDiffAt_leftInverse`: `C^n` varying left inverses of a `C^n` family of
  operators whose member at `x₀` has a continuous left inverse.
* `ContMDiffAt.of_clm_apply`: regularity can be tested after a smoothly varying split injection.
* `ContMDiffOn.exists_isOpen_contMDiffOn_sub_comp_inverse_comp`: near a point where a left
  inverse compresses a smooth family of operators to the identity, the projections of a fixed
  covector annihilating the central member are smooth and nonzero, and the compression stays
  invertible, on an open neighborhood.
-/

public section

noncomputable section

open Filter Function Topology
open scoped Manifold ContDiff

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G]
  [IsScalarTower 𝕜 𝕜' G] [CompleteSpace G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {n : ℕ∞ω}

/-- **Left inverses vary smoothly.** Let `A x` be a continuous linear map into a normed space from
a Banach space, linear over the extension field `𝕜'` and depending `C^n` over the ground field
`𝕜` on a manifold point `x` at `x₀`. If `A x₀` has a continuous `𝕜'`-linear left inverse, then
there are continuous `𝕜'`-linear maps `L x`, depending `C^n` over `𝕜` on `x` at `x₀`, such that
`L x` is a left inverse of `A x` for all `x` near `x₀`. -/
theorem ContMDiffAt.exists_contMDiffAt_leftInverse {A : M → G →L[𝕜'] F} {x₀ : M}
    (hA : ContMDiffAt I 𝓘(𝕜, G →L[𝕜'] F) n A x₀) (h : (A x₀).HasLeftInverse) :
    ∃ L : M → F →L[𝕜'] G, ContMDiffAt I 𝓘(𝕜, F →L[𝕜'] G) n L x₀ ∧
      ∀ᶠ x in 𝓝 x₀, LeftInverse (L x) (A x) := by
  -- Retain the original ground-field module on extension-linear endomorphisms.
  let : NormedAlgebra 𝕜 (G →L[𝕜'] G) :=
    { Algebra.ofModule smul_mul_assoc mul_smul_comm with norm_smul_le := norm_smul_le }
  obtain ⟨P, hP⟩ := h
  -- The compression `P ∘ A x` is the identity at `x₀`, hence invertible near `x₀`.
  have hQ : ContMDiffAt I 𝓘(𝕜, G →L[𝕜'] G) n (fun x ↦ P ∘L A x) x₀ :=
    ((ContinuousLinearMap.compL 𝕜' G F G P).restrictScalars 𝕜).contDiff.comp_contMDiffAt hA
  have hQ₀ : P ∘L A x₀ = ((1 : (G →L[𝕜'] G)ˣ) : G →L[𝕜'] G) := ContinuousLinearMap.ext hP
  have hinv : ContDiffAt 𝕜 n Ring.inverse (P ∘L A x₀) := by
    rw [hQ₀]
    exact contDiffAt_ringInverse 𝕜 1
  refine ⟨fun x ↦ Ring.inverse (P ∘L A x) ∘L P,
    (((ContinuousLinearMap.compL 𝕜' F G G).flip P).restrictScalars 𝕜).contDiff.comp_contMDiffAt
      (hinv.comp_contMDiffAt (f := fun x ↦ P ∘L A x) hQ), ?_⟩
  filter_upwards [hQ.continuousAt.preimage_mem_nhds (hQ₀ ▸ Units.nhds 1)] with x hx v
  have := congrArg (fun T : G →L[𝕜'] G ↦ T v) (Ring.inverse_mul_cancel _ hx)
  simpa using this

/-- Ground-field smoothness can be tested after a smoothly varying extension-linear split
injection. No regularity of `v` is assumed in advance. -/
theorem ContMDiffAt.of_clm_apply {A : M → G →L[𝕜'] F} {v : M → G} {x₀ : M}
    (hAv : ContMDiffAt I 𝓘(𝕜, F) n (fun x ↦ A x (v x)) x₀)
    (hA : ContMDiffAt I 𝓘(𝕜, G →L[𝕜'] F) n A x₀) (h : (A x₀).HasLeftInverse) :
    ContMDiffAt I 𝓘(𝕜, G) n v x₀ := by
  obtain ⟨L, hL, hLA⟩ := hA.exists_contMDiffAt_leftInverse h
  have hL' := (ContinuousLinearMap.restrictScalarsL 𝕜' F G 𝕜 𝕜).contDiff.comp_contMDiffAt hL
  exact (hL'.clm_apply hAv).congr_of_eventuallyEq
    (hLA.mono fun x hx ↦ (hx (v x)).symm)

/-- Near a point where a smooth family of operators `A y : G → F` is compressed by a left inverse
`P` to the identity and `a` is a covector killing `A x`, the covectors
`a - a (A y) (P (A y))⁻¹ P` are smooth and nonzero, and the compression `P (A y)` is invertible,
on an open neighborhood of `x` inside the domain of smoothness. They annihilate `A y` by
`ContinuousLinearMap.sub_comp_inverse_comp_comp_eq_zero`. -/
theorem ContMDiffOn.exists_isOpen_contMDiffOn_sub_comp_inverse_comp
    {A : M → G →L[𝕜] F} {S : Set M}
    (hA : ContMDiffOn I 𝓘(𝕜, G →L[𝕜] F) n A S) (hS : IsOpen S) {x : M} (hxS : x ∈ S)
    {P : F →L[𝕜] G} (hP : LeftInverse P (A x)) {a : F →L[𝕜] 𝕜} (ha : a ≠ 0)
    (haA : a ∘L A x = 0) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ S ∧
      ContMDiffOn I 𝓘(𝕜, F →L[𝕜] 𝕜) n
        (fun y ↦ a - a ∘L A y ∘L (P ∘L A y).inverse ∘L P) W ∧
      ∀ y ∈ W, (P ∘L A y).IsInvertible ∧ a - a ∘L A y ∘L (P ∘L A y).inverse ∘L P ≠ 0 := by
  -- The compressed frame is the identity at x, hence invertible on a neighborhood.
  let Q : M → G →L[𝕜] G := fun y ↦ P ∘L A y
  have hQ : ContMDiffOn I 𝓘(𝕜, G →L[𝕜] G) n Q S :=
    contMDiffOn_const.clm_comp hA
  have hQx : Q x = 1 := ContinuousLinearMap.ext hP
  -- Project the annihilator at x to the annihilators of the nearby frame images.
  let c : M → F →L[𝕜] 𝕜 := fun y ↦ a - a ∘L A y ∘L (Q y).inverse ∘L P
  have hcx : c x = a := by
    dsimp only [c]
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, haA]
    simp
  have hQunit : ∀ᶠ y in 𝓝 x, (Q y).IsInvertible := by
    have hi : (Q x).IsInvertible := by
      rw [hQx]
      exact ⟨ContinuousLinearEquiv.refl 𝕜 _, rfl⟩
    exact (hQ.continuousOn.continuousAt (hS.mem_nhds hxS)).tendsto.eventually hi.eventually_nhds
  obtain ⟨W, hWQ, hW, hxW⟩ := eventually_nhds_iff.mp hQunit
  have hc : ContMDiffOn I 𝓘(𝕜, F →L[𝕜] 𝕜) n c (S ∩ W) := by
    apply contMDiffOn_const.sub
    exact ((contMDiffOn_const.clm_comp (hA.mono Set.inter_subset_left)).clm_comp
      (fun y hy ↦ (hWQ y hy.2).contDiffAt_map_inverse.comp_contMDiffWithinAt
        ((hQ y hy.1).mono Set.inter_subset_left))).clm_comp contMDiffOn_const
  have hcn : ∀ᶠ y in 𝓝 x, c y ≠ 0 :=
    (hc.continuousOn.continuousAt ((hS.inter hW).mem_nhds ⟨hxS, hxW⟩)).eventually_ne
      (by rwa [hcx])
  obtain ⟨Z, hZc, hZ, hxZ⟩ := eventually_nhds_iff.mp hcn
  exact ⟨S ∩ W ∩ Z, (hS.inter hW).inter hZ, ⟨⟨hxS, hxW⟩, hxZ⟩,
    Set.inter_subset_left.trans Set.inter_subset_left,
    hc.mono Set.inter_subset_left, fun y hy ↦ ⟨hWQ y hy.1.2, hZc y hy.2⟩⟩
