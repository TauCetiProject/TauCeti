/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Variational.DirectMethod
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace

/-!
# The direct method under compact constraints and compact perturbations

In infinite dimensions, level constraints such as `{u | ‖J u‖ = 1}` under a compact operator
`J : V →L[𝕜] F` are generally not weakly closed. However, because `J` is weak-to-norm continuous
on every norm-bounded set (`IsCompactOperator.continuousOn_toWeakSpace_symm_of_isBounded`), the
intersection of `J ⁻¹' C` (for a closed `C ⊆ F`) with any bounded weakly closed set is weakly
closed. Consequently, for an energy with bounded sublevels on `S₀ ∩ J ⁻¹' C` that is weakly lower
semicontinuous on each bounded slice `closedBall 0 R ∩ (S₀ ∩ J ⁻¹' C)`, every bounded sublevel is
weakly compact and the direct method yields a minimizer without global weak closedness of the
admissible set.

In particular:

* Adding a compact perturbation `g ∘ J` (with `g` lower semicontinuous on `J '' B`) to a lower
  semicontinuous real-quasiconvex function preserves weak lower semicontinuity on every
  norm-bounded set `B` (`TauCeti.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_isBounded`).
* In a reflexive seminormed space over `ℝ` or `ℂ`, bounded sublevels and bounded sets of minimizers
  on `S₀ ∩ J ⁻¹' C` are weakly compact
  (`TauCeti.isCompact_toWeakSpace_sublevel_of_compact_constraint`,
  `TauCeti.isCompact_toWeakSpace_minimizers_of_compact_constraint`), and the energy attains its
  minimum (`TauCeti.exists_isMinOn_of_compact_constraint_of_isBounded_sublevel`,
  `TauCeti.exists_isMinOn_of_compact_constraint`).
* Specialized to additive energies `u ↦ f u + g (J u)` with `f` weakly lower semicontinuous on `S₀`
  and `g` lower semicontinuous on `C`, `TauCeti.exists_isMinOn_add_comp_of_compact_constraint`
  directly handles compactly perturbed and sphere-constrained variational problems.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
-/

public section

open Bornology Metric NormedSpace Set

namespace TauCeti

section AdditivePerturbation

variable {𝕜 V F β : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousConstSMul 𝕜 F] [T2Space (WeakSpace 𝕜 F)]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]

/-- Adding a compact lower semicontinuous perturbation `g ∘ J` to a lower semicontinuous
real-quasiconvex energy yields a weakly lower semicontinuous energy on every norm-bounded set. -/
theorem lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_isBounded
    {f : V → β} (hf : QuasiconvexOn ℝ univ f) (hlsc : LowerSemicontinuous f)
    {J : V →L[𝕜] F} (hJ : IsCompactOperator J) {B : Set V} (hB : IsBounded B)
    {g : F → β} (hg : LowerSemicontinuousOn g (J '' B)) :
    LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ f ((toWeakSpace 𝕜 V).symm w) + g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' B) := by
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace' 𝕜
  exact ((hf.lowerSemicontinuous_comp_toWeakSpace_symm (𝕜 := 𝕜) hlsc).lowerSemicontinuousOn _).add
    (hJ.lowerSemicontinuousOn_comp_toWeakSpace_symm_of_isBounded hB hg)

end AdditivePerturbation

section CompactConstraint

variable {𝕜 V F β : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousConstSMul 𝕜 F] [T2Space (WeakSpace 𝕜 F)]
  [LinearOrder β]
  {J : V →L[𝕜] F} {S₀ : Set V} {C : Set F} {E : V → β}

/-- On a compactly constrained set `S₀ ∩ J ⁻¹' C` in a reflexive seminormed space, any bounded
sublevel of an energy that is weakly lower semicontinuous on bounded slices is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_compact_constraint
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J)
    (hS₀ : IsClosed (toWeakSpace 𝕜 V '' S₀)) (hC : IsClosed C)
    (hE : ∀ R : ℝ, LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C))))
    (b : β) (hb : IsBounded {u ∈ S₀ ∩ J ⁻¹' C | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S₀ ∩ J ⁻¹' C | E u ≤ b}) := by
  let : NormedSpace ℝ V := .restrictScalars ℝ 𝕜 V
  let : IsScalarTower ℝ 𝕜 V := .of_algebraMap_smul fun _ _ ↦ rfl
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace' 𝕜
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
  have hball_closed : IsClosed (toWeakSpace 𝕜 V '' closedBall (0 : V) R) := by
    rw [← isClosed_closedBall.closure_eq, (convex_closedBall (0 : V) R).toWeakSpace_closure 𝕜]
    exact isClosed_closure
  have hslice_closed : IsClosed (toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ S₀)) := by
    rw [image_inter (toWeakSpace 𝕜 V).injective]
    exact hball_closed.inter hS₀
  have hK_closed : IsClosed (toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C))) := by
    rw [← inter_assoc]
    exact hJ.isClosed_toWeakSpace_inter_preimage (isBounded_closedBall.subset inter_subset_left)
      hslice_closed hC
  have hsub_eq : {u ∈ S₀ ∩ J ⁻¹' C | E u ≤ b} =
      {u ∈ closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C) | E u ≤ b} := by
    ext u
    exact ⟨fun hu ↦ ⟨⟨mem_closedBall_zero_iff.2 (hR u hu), hu.1⟩, hu.2⟩,
      fun hu ↦ ⟨hu.1.2, hu.2⟩⟩
  rw [hsub_eq] at hb ⊢
  exact isCompact_toWeakSpace_sublevel hV hK_closed (hE R) b hb

/-- A single nonempty bounded sublevel suffices for the direct method on a compactly constrained
set `S₀ ∩ J ⁻¹' C` in a reflexive seminormed space. -/
theorem exists_isMinOn_of_compact_constraint_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J)
    (hS₀ : IsClosed (toWeakSpace 𝕜 V '' S₀)) (hC : IsClosed C)
    (hE : ∀ R : ℝ, LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C))))
    {b : β} (hne : {u ∈ S₀ ∩ J ⁻¹' C | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S₀ ∩ J ⁻¹' C | E u ≤ b}) :
    ∃ u ∈ S₀ ∩ J ⁻¹' C, IsMinOn E (S₀ ∩ J ⁻¹' C) u := by
  have hcompact := isCompact_toWeakSpace_sublevel_of_compact_constraint hV hJ hS₀ hC hE b hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
  have hsubset : toWeakSpace 𝕜 V '' {u ∈ S₀ ∩ J ⁻¹' C | E u ≤ b} ⊆
      toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C)) :=
    image_mono fun u hu ↦ ⟨mem_closedBall_zero_iff.2 (hR u hu), hu.1⟩
  obtain ⟨w, hw, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact ((hE R).mono hsubset)
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The direct method under compact constraints.** On a nonempty set `S₀ ∩ J ⁻¹' C` with `S₀`
weakly closed, `C` closed, and `J` compact in a reflexive seminormed space, an energy with bounded
sublevels that is weakly lower semicontinuous on bounded slices attains its minimum. -/
theorem exists_isMinOn_of_compact_constraint
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J)
    (hne : (S₀ ∩ J ⁻¹' C).Nonempty)
    (hS₀ : IsClosed (toWeakSpace 𝕜 V '' S₀)) (hC : IsClosed C)
    (hE : ∀ R : ℝ, LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C))))
    (hb : HasBoundedSublevelsOn E (S₀ ∩ J ⁻¹' C)) :
    ∃ u ∈ S₀ ∩ J ⁻¹' C, IsMinOn E (S₀ ∩ J ⁻¹' C) u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_compact_constraint_of_isBounded_sublevel hV hJ hS₀ hC hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the full set of minimizers on a compactly constrained set `S₀ ∩ J ⁻¹' C` is bounded, then
it is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_compact_constraint_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J)
    (hS₀ : IsClosed (toWeakSpace 𝕜 V '' S₀)) (hC : IsClosed C)
    (hE : ∀ R : ℝ, LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C))))
    (hb : IsBounded {u ∈ S₀ ∩ J ⁻¹' C | IsMinOn E (S₀ ∩ J ⁻¹' C) u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S₀ ∩ J ⁻¹' C | IsMinOn E (S₀ ∩ J ⁻¹' C) u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ :=
      {u ∈ S₀ ∩ J ⁻¹' C | IsMinOn E (S₀ ∩ J ⁻¹' C) u}.eq_empty_or_nonempty
  · rw [hempty, image_empty]
    exact isCompact_empty
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel_of_compact_constraint hV hJ hS₀ hC hE (E u) hb

/-- For an energy with bounded sublevels on a compactly constrained set `S₀ ∩ J ⁻¹' C` in a
reflexive seminormed space, the set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_compact_constraint
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J)
    (hS₀ : IsClosed (toWeakSpace 𝕜 V '' S₀)) (hC : IsClosed C)
    (hE : ∀ R : ℝ, LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C))))
    (hb : HasBoundedSublevelsOn E (S₀ ∩ J ⁻¹' C)) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S₀ ∩ J ⁻¹' C | IsMinOn E (S₀ ∩ J ⁻¹' C) u}) :=
  isCompact_toWeakSpace_minimizers_of_compact_constraint_of_isBounded hV hJ hS₀ hC hE
    hb.isBounded_minimizers

end CompactConstraint

section AdditiveCompactConstraint

variable {𝕜 V F β : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousConstSMul 𝕜 F] [T2Space (WeakSpace 𝕜 F)]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]

/-- **Minimizing a compactly perturbed energy under a compact constraint.** In a reflexive
seminormed space over `ℝ` or `ℂ`, an additive energy `u ↦ f u + g (J u)` with `f` weakly lower
semicontinuous on `S₀`, `g` lower semicontinuous on `C`, and bounded sublevels on `S₀ ∩ J ⁻¹' C`
attains its minimum on `S₀ ∩ J ⁻¹' C`. -/
theorem exists_isMinOn_add_comp_of_compact_constraint
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {J : V →L[𝕜] F} (hJ : IsCompactOperator J)
    {S₀ : Set V} {C : Set F}
    (hne : (S₀ ∩ J ⁻¹' C).Nonempty)
    (hS₀ : IsClosed (toWeakSpace 𝕜 V '' S₀)) (hC : IsClosed C)
    {f : V → β}
    (hf : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ f ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S₀))
    {g : F → β} (hg : LowerSemicontinuousOn g C)
    (hb : HasBoundedSublevelsOn (fun u ↦ f u + g (J u)) (S₀ ∩ J ⁻¹' C)) :
    ∃ u ∈ S₀ ∩ J ⁻¹' C, IsMinOn (fun u ↦ f u + g (J u)) (S₀ ∩ J ⁻¹' C) u := by
  refine exists_isMinOn_of_compact_constraint hV hJ hne hS₀ hC (fun R ↦ ?_) hb
  have hsubS₀ : toWeakSpace 𝕜 V '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C)) ⊆
      toWeakSpace 𝕜 V '' S₀ :=
    image_mono fun _ hu ↦ hu.2.1
  have hsubC : J '' (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C)) ⊆ C := by
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2.2
  have hbd : IsBounded (closedBall (0 : V) R ∩ (S₀ ∩ J ⁻¹' C)) :=
    isBounded_closedBall.subset inter_subset_left
  exact (hf.mono hsubS₀).add
    (hJ.lowerSemicontinuousOn_comp_toWeakSpace_symm_of_isBounded hbd (hg.mono hsubC))

end AdditiveCompactConstraint

end TauCeti
