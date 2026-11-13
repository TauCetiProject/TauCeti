/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Associated.Prod

/-!
# Smooth families in products of associated bundles

A family in `P ×_G (F₁ × F₂)` is smooth exactly when its two associated components are smooth.
Together with `AssociatedBundle.prodHomeomorph`, this identifies association of a product with
the native fibrewise product, both topologically and on smooth families. In particular, smooth
operations on two associated inputs can be checked in a common principal frame.

The statements use the existing charts through the fibre. They do not require linear actions,
finite-dimensional fibres, or smoothness of the principal transition functions: they compare the
specified charts, even before those charts are known to form smooth bundles. Smoothness of the
bundles themselves follows separately from smooth principal transitions and smooth actions.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer, 1993, §§10.7 and 10.9.
-/

public section

noncomputable section

open Bundle Filter Set TauCeti
open scoped Manifold Topology ContDiff

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {𝕜 B G F₁ F₂ M : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [Group G] [TopologicalSpace G]
  {EF₁ : Type*} [NormedAddCommGroup EF₁] [NormedSpace 𝕜 EF₁]
  {HF₁ : Type*} [TopologicalSpace HF₁] {IF₁ : ModelWithCorners 𝕜 EF₁ HF₁}
  [TopologicalSpace F₁] [ChartedSpace HF₁ F₁] [MulAction G F₁] [ContinuousSMul G F₁]
  {EF₂ : Type*} [NormedAddCommGroup EF₂] [NormedSpace 𝕜 EF₂]
  {HF₂ : Type*} [TopologicalSpace HF₂] {IF₂ : ModelWithCorners 𝕜 EF₂ HF₂}
  [TopologicalSpace F₂] [ChartedSpace HF₂ F₂] [MulAction G F₂] [ContinuousSMul G F₂]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {f : M → B} {v : ∀ x, AssociatedBundle G P (F₁ × F₂) (f x)} {s : Set M} {x₀ : M}

/-- In the associated product, a family is `C^n` within a set at a point exactly when both
associated component families are `C^n` there. -/
theorem contMDiffWithinAt_prodEquiv_iff :
    ContMDiffWithinAt IM (IB.prod (IF₁.prod IF₂)) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂))
        ⟨f x, v x⟩) s x₀ ↔
      ContMDiffWithinAt IM (IB.prod IF₁) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F₁ (AssociatedBundle G P F₁)
          ⟨f x, (prodEquiv (f x) (v x)).1⟩) s x₀ ∧
      ContMDiffWithinAt IM (IB.prod IF₂) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F₂ (AssociatedBundle G P F₂)
          ⟨f x, (prodEquiv (f x) (v x)).2⟩) s x₀ := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff, ManifoldTotalSpace.contMDiffWithinAt_iff,
    ManifoldTotalSpace.contMDiffWithinAt_iff]
  have hcoord (hf : ContMDiffWithinAt IM IB n f s x₀) :
      (fun x ↦
        ((trivializationAt F₁ (AssociatedBundle G P F₁) (f x₀)
          ⟨f x, (prodEquiv (f x) (v x)).1⟩).2,
        (trivializationAt F₂ (AssociatedBundle G P F₂) (f x₀)
          ⟨f x, (prodEquiv (f x) (v x)).2⟩).2)) =ᶠ[𝓝[s] x₀]
      (fun x ↦ (trivializationAt (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂))
        (f x₀) ⟨f x, v x⟩).2) := by
    filter_upwards [hf.continuousWithinAt ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt G P (f x₀)))] with x hx
    exact trivializationAt_prodEquiv hx (v x)
  have h₀ := trivializationAt_prodEquiv (mem_baseSet_trivializationAt G P (f x₀)) (v x₀)
  constructor
  · rintro ⟨hf, hv⟩
    have h := hv.congr_of_eventuallyEq (hcoord hf) h₀
    exact ⟨⟨hf, h.fst⟩, ⟨hf, h.snd⟩⟩
  · rintro ⟨⟨hf, hv⟩, ⟨_, hw⟩⟩
    exact ⟨hf, (hv.prodMk hw).congr_of_eventuallyEq (hcoord hf).symm h₀.symm⟩

/-- A family in the associated product is `C^n` at a point exactly when both component
families are `C^n` there. -/
theorem contMDiffAt_prodEquiv_iff :
    ContMDiffAt IM (IB.prod (IF₁.prod IF₂)) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂))
        ⟨f x, v x⟩) x₀ ↔
      ContMDiffAt IM (IB.prod IF₁) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F₁ (AssociatedBundle G P F₁)
          ⟨f x, (prodEquiv (f x) (v x)).1⟩) x₀ ∧
      ContMDiffAt IM (IB.prod IF₂) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F₂ (AssociatedBundle G P F₂)
          ⟨f x, (prodEquiv (f x) (v x)).2⟩) x₀ :=
  contMDiffWithinAt_prodEquiv_iff

/-- A family in the associated product is `C^n` on a set exactly when both component
families are `C^n` on that set. -/
theorem contMDiffOn_prodEquiv_iff :
    ContMDiffOn IM (IB.prod (IF₁.prod IF₂)) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂))
        ⟨f x, v x⟩) s ↔
      ContMDiffOn IM (IB.prod IF₁) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F₁ (AssociatedBundle G P F₁)
          ⟨f x, (prodEquiv (f x) (v x)).1⟩) s ∧
      ContMDiffOn IM (IB.prod IF₂) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F₂ (AssociatedBundle G P F₂)
          ⟨f x, (prodEquiv (f x) (v x)).2⟩) s := by
  simp only [ContMDiffOn, contMDiffWithinAt_prodEquiv_iff, forall_and]

/-- A family in the associated product is `C^n` exactly when both associated components
are `C^n`. -/
theorem contMDiff_prodEquiv_iff :
    ContMDiff IM (IB.prod (IF₁.prod IF₂)) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (F₁ × F₂) (AssociatedBundle G P (F₁ × F₂))
        ⟨f x, v x⟩) ↔
      ContMDiff IM (IB.prod IF₁) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F₁ (AssociatedBundle G P F₁)
          ⟨f x, (prodEquiv (f x) (v x)).1⟩) ∧
      ContMDiff IM (IB.prod IF₂) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F₂ (AssociatedBundle G P F₂)
          ⟨f x, (prodEquiv (f x) (v x)).2⟩) := by
  simp only [ContMDiff, contMDiffAt_prodEquiv_iff, forall_and]

end TauCeti.AssociatedBundle
