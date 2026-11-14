/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.WeakSpace
public import TauCeti.Analysis.Variational.DirectMethod
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded

/-!
# Compact operators and perturbations in the direct method

In infinite dimensions, neither compact operators nor nonlinear lower-order terms `g ∘ J` are
globally weakly continuous, and compactly defined constraint sets such as `{u ∈ S | J u ∈ C}` (for
example, Rayleigh or Nehari-type spheres `{u | ‖J u‖ = 1}`) are not weakly closed. Nevertheless,
once an energy controls norm sublevels (`TauCeti.HasBoundedSublevelsOn`), every variational argument
localizes to closed norm balls, which are weakly closed over `ℝ` or `ℂ`
(`TauCeti.isClosed_toWeakSpace_closedBall`) and on which a compact operator `J` is weak-to-norm
continuous (`IsCompactOperator.continuousOn_toWeakSpace_symm`).

This file formalizes the two main variational consequences of that localization principle:

1. **Compact perturbations of weakly lower semicontinuous energies.** Any energy with bounded
   sublevels on `S` that is weakly lower semicontinuous on norm-bounded subsets of `S` is globally
   weakly lower semicontinuous on `S`
   (`TauCeti.lowerSemicontinuousOn_toWeakSpace_of_hasBoundedSublevelsOn`). In particular, if `E₀` is
   weakly lower semicontinuous on `S`, `J : V →L[𝕜] F` is compact, and `g : F → β` is lower
   semicontinuous on `J '' S`, then the nonconvex perturbed functional `u ↦ E₀ u + g (J u)` is
   weakly lower semicontinuous on every bounded subset of `S`
   (`IsCompactOperator.lowerSemicontinuousOn_add_comp_toWeakSpace_symm`), globally weakly lower
   semicontinuous on `S` whenever it has bounded sublevels
   (`IsCompactOperator.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn`),
   and attains its minimum on any nonempty weakly closed `S` in a reflexive space
   (`IsCompactOperator.exists_isMinOn_add_comp`).

2. **The direct method under non-weakly-closed compact constraints.** For a weakly closed set `S`, a
   compact operator `J : V →L[𝕜] F`, and a closed set `C ⊆ F`, the constrained set `S ∩ J ⁻¹' C`
   need not be weakly closed, yet every norm-bounded sublevel `{u ∈ S ∩ J ⁻¹' C | E u ≤ b}` of an
   energy `E` that is weakly lower semicontinuous on `S ∩ J ⁻¹' C` is weakly closed
   (`IsCompactOperator.isClosed_toWeakSpace_sublevel_inter_preimage`) and, in a reflexive space,
   weakly compact (`IsCompactOperator.isCompact_toWeakSpace_sublevel_inter_preimage`). Consequently,
   `E` attains its minimum on `S ∩ J ⁻¹' C`, and its set of minimizers is weakly compact, assuming
   bounded sublevels and weak lower semicontinuity only on the constrained set `S ∩ J ⁻¹' C`
   (`IsCompactOperator.exists_isMinOn_inter_preimage`,
   `IsCompactOperator.isCompact_toWeakSpace_minimizers_inter_preimage`).

## References

* M. Struwe, *Variational Methods*, 4th ed., Springer, 2008, Theorem I.1.2 and Section I.2.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications, III: Variational Methods and
  Optimization*, Springer, 1985, §38.3 and §38.7.
-/

public section

open Bornology Filter Function Metric NormedSpace Set Topology

namespace TauCeti

/-- **Sublevel localization of weak lower semicontinuity.** Over `ℝ` or `ℂ`, an energy `E` with
norm-bounded sublevels on `S` is globally weakly lower semicontinuous on `S` as soon as it is
weakly lower semicontinuous on every norm-bounded subset of `S`. No weak closedness assumption on
`S` is needed. -/
theorem lowerSemicontinuousOn_toWeakSpace_of_hasBoundedSublevelsOn {𝕜 V β : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [LinearOrder β] {E : V → β} {S : Set V}
    (hb : HasBoundedSublevelsOn E S)
    (hloc : ∀ ⦃B : Set V⦄, B ⊆ S → IsBounded B →
      LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' B)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) := by
  let f : WeakSpace 𝕜 V → β := fun w ↦ E ((toWeakSpace 𝕜 V).symm w)
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro b
  -- Every point of `S` with `E u ≤ b` lies in a closed norm ball `closedBall 0 R`, which is weakly
  -- closed by Hahn–Banach.
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : V)).1 (hb.isBounded_sublevel b)
  let B : Set V := S ∩ closedBall 0 R
  have hB_lsc : LowerSemicontinuousOn f (toWeakSpace 𝕜 V '' B) :=
    hloc inter_subset_left (isBounded_closedBall.subset inter_subset_right)
  obtain ⟨v₀, hv₀, hBv₀⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hB_lsc b
  refine ⟨(toWeakSpace 𝕜 V '' closedBall 0 R) ∩ v₀,
    (isClosed_toWeakSpace_closedBall (0 : V) R).inter hv₀, ?_⟩
  have hinter : (toWeakSpace 𝕜 V '' S) ∩ ((toWeakSpace 𝕜 V '' closedBall 0 R) ∩ v₀) =
      (toWeakSpace 𝕜 V '' B) ∩ v₀ := by
    rw [← inter_assoc, ← image_inter (toWeakSpace 𝕜 V).injective]
  rw [hinter, ← hBv₀]
  ext w
  constructor
  · rintro ⟨⟨u, huS, rfl⟩, hfb⟩
    have hu_le : E u ≤ b := by simpa only [f, mem_preimage, mem_Iic,
      LinearEquiv.symm_apply_apply] using hfb
    exact ⟨mem_image_of_mem _ ⟨huS, hR ⟨huS, hu_le⟩⟩, hfb⟩
  · rintro ⟨⟨u, huB, rfl⟩, hfb⟩
    exact ⟨mem_image_of_mem _ huB.1, hfb⟩

end TauCeti

namespace IsCompactOperator

section BoundedPerturbation

variable {𝕜 V F β : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
  {J : V →L[𝕜] F}

/-- On any norm-bounded set `B ⊆ V`, adding `g ∘ J` (with `J` compact and `g` lower semicontinuous
on `J '' B`) to a weakly lower semicontinuous functional `E₀` preserves weak lower semicontinuity.
-/
theorem lowerSemicontinuousOn_add_comp_toWeakSpace_symm (hJ : IsCompactOperator J)
    {B : Set V} (hB : IsBounded B) {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' B))
    (hg : LowerSemicontinuousOn g (J '' B)) :
    LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦
        E₀ ((toWeakSpace 𝕜 V).symm w) + g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' B) :=
  hE₀.add (hJ.lowerSemicontinuousOn_comp_toWeakSpace_symm hB hg)

end BoundedPerturbation

section CompactPerturbation

variable {𝕜 V F β : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [TopologicalSpace β] [OrderTopology β] [ContinuousAdd β]
  {J : V →L[𝕜] F}

/-- **Sequential weak lower semicontinuity of a compact perturbation.** If `u n → a` weakly in `V`
along a sequence in `S`, `E₀` is weakly lower semicontinuous within `S` at `a`, `J` is compact, and
`g` is lower semicontinuous at `J a`, then every limit `l` of `E₀ (u n) + g (J (u n))` satisfies
`E₀ a + g (J a) ≤ l`. -/
theorem le_of_tendsto_add_comp_of_tendsto_toWeakSpace (hJ : IsCompactOperator J)
    {E₀ : V → β} {g : F → β} {S : Set V} {u : ℕ → V} {a : V}
    (huS : ∀ n, u n ∈ S)
    (hE₀ : LowerSemicontinuousWithinAt
      (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) (toWeakSpace 𝕜 V a))
    (hg : LowerSemicontinuousAt g (J a))
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V a)))
    {l : β} (hl : Tendsto (fun n ↦ E₀ (u n) + g (J (u n))) atTop (𝓝 l)) :
    E₀ a + g (J a) ≤ l := by
  -- The weakly convergent sequence has norm-bounded range `B = S ∩ range u`, on which `J` is
  -- weak-to-norm continuous and `LowerSemicontinuousWithinAt.add` applies.
  let B : Set V := S ∩ range u
  have hB : IsBounded B := hu.isBounded_range_of_toWeakSpace.subset inter_subset_right
  have hE₀' : LowerSemicontinuousWithinAt
      (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' B) (toWeakSpace 𝕜 V a) :=
    hE₀.mono (image_mono inter_subset_left)
  have hg_at : LowerSemicontinuousWithinAt g univ
      (J ((toWeakSpace 𝕜 V).symm (toWeakSpace 𝕜 V a))) := by
    simpa only [LinearEquiv.symm_apply_apply] using hg.lowerSemicontinuousWithinAt (s := univ)
  have hg' : LowerSemicontinuousWithinAt
      (fun w : WeakSpace 𝕜 V ↦ g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' B) (toWeakSpace 𝕜 V a) :=
    hg_at.comp (g := fun z : WeakSpace 𝕜 V ↦ J ((toWeakSpace 𝕜 V).symm z))
      (hJ.continuousWithinAt_toWeakSpace_symm hB (toWeakSpace 𝕜 V a)) (mapsTo_univ _ _)
  have hsum := hE₀'.add hg'
  have hu_B : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop
      (𝓝[toWeakSpace 𝕜 V '' B] (toWeakSpace 𝕜 V a)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu
      (Eventually.of_forall fun n ↦ mem_image_of_mem _ ⟨huS n, mem_range_self n⟩)
  by_contra! hlt
  by_cases hc : ∃ c, l < c ∧ c < E₀ a + g (J a)
  · obtain ⟨c, hlc, hcM⟩ := hc
    have hcM' : c < E₀ ((toWeakSpace 𝕜 V).symm (toWeakSpace 𝕜 V a)) +
        g (J ((toWeakSpace 𝕜 V).symm (toWeakSpace 𝕜 V a))) := by
      simpa only [LinearEquiv.symm_apply_apply] using hcM
    have ev : ∀ᶠ n in atTop, c ≤ E₀ (u n) + g (J (u n)) := by
      filter_upwards [hu_B.eventually (hsum c hcM')] with n hn
      exact (by simpa only [LinearEquiv.symm_apply_apply] using hn : c < _).le
    exact hlc.not_ge (ge_of_tendsto hl ev)
  · have hIic : Iic l ∈ 𝓝 l := mem_of_superset (gt_mem_nhds hlt) fun y hy ↦
      le_of_not_gt fun hly ↦ hc ⟨y, hly, hy⟩
    have hlt' : l < E₀ ((toWeakSpace 𝕜 V).symm (toWeakSpace 𝕜 V a)) +
        g (J ((toWeakSpace 𝕜 V).symm (toWeakSpace 𝕜 V a))) := by
      simpa only [LinearEquiv.symm_apply_apply] using hlt
    have ev_gt : ∀ᶠ n in atTop, l < E₀ (u n) + g (J (u n)) := by
      simpa only [LinearEquiv.symm_apply_apply] using hu_B.eventually (hsum l hlt')
    obtain ⟨n, hn_gt, hn_le⟩ := (ev_gt.and (hl.eventually hIic)).exists
    exact hn_gt.not_ge hn_le

/-- **Global weak lower semicontinuity of a compact perturbation under bounded sublevels.** If `E₀`
is weakly lower semicontinuous on `S`, `J : V →L[𝕜] F` is compact, `g : F → β` is lower
semicontinuous on `J '' S`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on `S`, then
`u ↦ E₀ u + g (J u)` is globally weakly lower semicontinuous on `S`. -/
theorem lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn
    (hJ : IsCompactOperator J) {S : Set V} {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦
        E₀ ((toWeakSpace 𝕜 V).symm w) + g (J ((toWeakSpace 𝕜 V).symm w)))
      (toWeakSpace 𝕜 V '' S) :=
  TauCeti.lowerSemicontinuousOn_toWeakSpace_of_hasBoundedSublevelsOn hb fun _ hBS hB ↦
    hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm hB
      (hE₀.mono (image_mono hBS)) (hg.mono (image_mono hBS))

/-- **Direct method for compactly perturbed energies.** In a reflexive seminormed space over `ℝ` or
`ℂ`, if `S` is nonempty and weakly closed, `E₀` is weakly lower semicontinuous on `S`, `J` is
compact, `g` is lower semicontinuous on `J '' S`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on
`S`, then `u ↦ E₀ u + g (J u)` attains its minimum on `S`. -/
theorem exists_isMinOn_add_comp (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J) {S : Set V} (hne : S.Nonempty)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    ∃ u ∈ S, IsMinOn (fun v ↦ E₀ v + g (J v)) S u := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.exists_isMinOn_of_weak_closed hV hne hS
    (hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hE₀ hg hb) hb

/-- Under the hypotheses of `IsCompactOperator.exists_isMinOn_add_comp` (without requiring `S` to be
nonempty), the set of minimizers of `u ↦ E₀ u + g (J u)` on `S` is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_add_comp (hV : Surjective (inclusionInDoubleDual 𝕜 V))
    (hJ : IsCompactOperator J) {S : Set V} (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    {E₀ : V → β} {g : F → β}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hg : LowerSemicontinuousOn g (J '' S))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn (fun v ↦ E₀ v + g (J v)) S u}) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact TauCeti.isCompact_toWeakSpace_minimizers hV hS
    (hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hE₀ hg hb) hb

end CompactPerturbation

section CompactConstraint

variable {𝕜 V F β : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
  [T2Space (WeakSpace 𝕜 F)]
  [LinearOrder β] {J : V →L[𝕜] F} {S : Set V} {C : Set F} {E : V → β}

/-- **Weak closedness of bounded sublevels on compactly constrained sets.** Even though
`S ∩ J ⁻¹' C` need not be weakly closed, if `S` is weakly closed, `J` is compact, `C ⊆ F` is closed,
and `E` is weakly lower semicontinuous on `S ∩ J ⁻¹' C`, then every norm-bounded sublevel
`{u ∈ S ∩ J ⁻¹' C | E u ≤ b}` is closed in the weak topology. -/
theorem isClosed_toWeakSpace_sublevel_inter_preimage (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (b : β) (hb : IsBounded {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) :
    IsClosed (toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) := by
  -- Cut off by a closed norm ball containing the bounded sublevel: `(S ∩ closedBall 0 R) ∩ J ⁻¹' C`
  -- is weakly closed because `J` is weak-to-norm continuous on `S ∩ closedBall 0 R`.
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : V)).1 hb
  let K₀ : Set V := (S ∩ closedBall 0 R) ∩ J ⁻¹' C
  have hSR_closed : IsClosed (toWeakSpace 𝕜 V '' (S ∩ closedBall 0 R)) := by
    rw [image_inter (toWeakSpace 𝕜 V).injective]
    exact hS.inter (TauCeti.isClosed_toWeakSpace_closedBall (0 : V) R)
  have hK₀_closed : IsClosed (toWeakSpace 𝕜 V '' K₀) :=
    hJ.isClosed_toWeakSpace_inter_preimage
      (isBounded_closedBall.subset inter_subset_right) hSR_closed hC
  have hK₀_sub : K₀ ⊆ S ∩ J ⁻¹' C := fun _ hu ↦ ⟨hu.1.1, hu.2⟩
  obtain ⟨v, hv, hEv⟩ :=
    lowerSemicontinuousOn_iff_preimage_Iic.1 (hE.mono (image_mono hK₀_sub)) b
  have heq : toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | E u ≤ b} =
      (toWeakSpace 𝕜 V '' K₀) ∩
        (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ⁻¹' Iic b := by
    ext w
    constructor
    · rintro ⟨u, ⟨huSC, huE⟩, rfl⟩
      exact ⟨mem_image_of_mem _ ⟨⟨huSC.1, hR ⟨huSC, huE⟩⟩, huSC.2⟩,
        by simpa only [mem_preimage, mem_Iic, LinearEquiv.symm_apply_apply] using huE⟩
    · rintro ⟨⟨u, huK₀, rfl⟩, huE⟩
      exact ⟨u, ⟨hK₀_sub huK₀,
        by simpa only [mem_preimage, mem_Iic, LinearEquiv.symm_apply_apply] using huE⟩, rfl⟩
  rw [heq, hEv]
  exact hK₀_closed.inter hv

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, every norm-bounded sublevel of a weakly lower
semicontinuous energy `E` on a compactly constrained set `S ∩ J ⁻¹' C` is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_inter_preimage
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (b : β) (hb : IsBounded {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have hclosed := hJ.isClosed_toWeakSpace_sublevel_inter_preimage hS hC hE b hb
  simpa only [hclosed.closure_eq] using TauCeti.isCompact_closure_toWeakSpace hV hb

/-- **Single-sublevel direct method under a compact constraint.** A single nonempty norm-bounded
sublevel `{u ∈ S ∩ J ⁻¹' C | E u ≤ b}` suffices for `E` to attain its minimum on `S ∩ J ⁻¹' C`,
without requiring `S ∩ J ⁻¹' C` itself to be weakly closed. -/
theorem exists_isMinOn_inter_preimage_of_isBounded_sublevel
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    {b : β} (hne : {u ∈ S ∩ J ⁻¹' C | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S ∩ J ⁻¹' C | E u ≤ b}) :
    ∃ u ∈ S ∩ J ⁻¹' C, IsMinOn E (S ∩ J ⁻¹' C) u := by
  have hcompact := hJ.isCompact_toWeakSpace_sublevel_inter_preimage hV hS hC hE b hb
  have hsub : toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | E u ≤ b} ⊆
      toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C) :=
    image_mono fun _ hu ↦ hu.1
  obtain ⟨w, hw, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact (hE.mono hsub)
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (TauCeti.isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The direct method under a compact constraint.** In a reflexive seminormed space over `ℝ` or
`ℂ`, if `S` is weakly closed, `J` is compact, `C ⊆ F` is closed, `S ∩ J ⁻¹' C` is nonempty, and `E`
is weakly lower semicontinuous with norm-bounded sublevels on `S ∩ J ⁻¹' C`, then `E` attains its
minimum on `S ∩ J ⁻¹' C`. -/
theorem exists_isMinOn_inter_preimage
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hne : (S ∩ J ⁻¹' C).Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (hb : TauCeti.HasBoundedSublevelsOn E (S ∩ J ⁻¹' C)) :
    ∃ u ∈ S ∩ J ⁻¹' C, IsMinOn E (S ∩ J ⁻¹' C) u := by
  obtain ⟨v, hv⟩ := hne
  exact hJ.exists_isMinOn_inter_preimage_of_isBounded_sublevel hV hS hC hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the set of minimizers of `E` on a compactly constrained set `S ∩ J ⁻¹' C` is norm-bounded,
then it is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_inter_preimage_of_isBounded
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (hb : IsBounded {u ∈ S ∩ J ⁻¹' C | IsMinOn E (S ∩ J ⁻¹' C) u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | IsMinOn E (S ∩ J ⁻¹' C) u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ :=
    {u ∈ S ∩ J ⁻¹' C | IsMinOn E (S ∩ J ⁻¹' C) u}.eq_empty_or_nonempty
  · rw [hempty]
    simp
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact hJ.isCompact_toWeakSpace_sublevel_inter_preimage hV hS hC hE (E u) hb

/-- For an energy `E` that is weakly lower semicontinuous and has norm-bounded sublevels on
`S ∩ J ⁻¹' C` (with `S` weakly closed, `J` compact, and `C` closed), the set of minimizers of `E`
on `S ∩ J ⁻¹' C` is weakly compact, including when `S ∩ J ⁻¹' C` is empty. -/
theorem isCompact_toWeakSpace_minimizers_inter_preimage
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (hb : TauCeti.HasBoundedSublevelsOn E (S ∩ J ⁻¹' C)) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S ∩ J ⁻¹' C | IsMinOn E (S ∩ J ⁻¹' C) u}) :=
  hJ.isCompact_toWeakSpace_minimizers_inter_preimage_of_isBounded hV hS hC hE
    hb.isBounded_minimizers

/-- **Direct method for compactly perturbed energies under a compact constraint.** Combining compact
perturbations and compact constraints, if `S` is weakly closed, `J` is compact, `C ⊆ F` is closed,
`S ∩ J ⁻¹' C` is nonempty, `E₀` is weakly lower semicontinuous on `S ∩ J ⁻¹' C`, `g` is lower
semicontinuous on `J '' (S ∩ J ⁻¹' C)`, and `u ↦ E₀ u + g (J u)` has bounded sublevels on
`S ∩ J ⁻¹' C`, then `u ↦ E₀ u + g (J u)` attains its minimum on `S ∩ J ⁻¹' C`. -/
theorem exists_isMinOn_add_comp_inter_preimage
    {γ : Type*} [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
    [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ]
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hne : (S ∩ J ⁻¹' C).Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    {E₀ : V → γ} {g : F → γ}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (hg : LowerSemicontinuousOn g (J '' (S ∩ J ⁻¹' C)))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) (S ∩ J ⁻¹' C)) :
    ∃ u ∈ S ∩ J ⁻¹' C, IsMinOn (fun v ↦ E₀ v + g (J v)) (S ∩ J ⁻¹' C) u :=
  hJ.exists_isMinOn_inter_preimage hV hne hS hC
    (hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hE₀ hg hb) hb

/-- Under the hypotheses of `IsCompactOperator.exists_isMinOn_add_comp_inter_preimage` (without
requiring `S ∩ J ⁻¹' C` to be nonempty), the set of minimizers of `u ↦ E₀ u + g (J u)` on
`S ∩ J ⁻¹' C` is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_add_comp_inter_preimage
    {γ : Type*} [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
    [TopologicalSpace γ] [OrderTopology γ] [ContinuousAdd γ]
    (hV : Surjective (inclusionInDoubleDual 𝕜 V)) (hJ : IsCompactOperator J)
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) (hC : IsClosed C)
    {E₀ : V → γ} {g : F → γ}
    (hE₀ : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E₀ ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' (S ∩ J ⁻¹' C)))
    (hg : LowerSemicontinuousOn g (J '' (S ∩ J ⁻¹' C)))
    (hb : TauCeti.HasBoundedSublevelsOn (fun u ↦ E₀ u + g (J u)) (S ∩ J ⁻¹' C)) :
    IsCompact (toWeakSpace 𝕜 V ''
      {u ∈ S ∩ J ⁻¹' C | IsMinOn (fun v ↦ E₀ v + g (J v)) (S ∩ J ⁻¹' C) u}) :=
  hJ.isCompact_toWeakSpace_minimizers_inter_preimage hV hS hC
    (hJ.lowerSemicontinuousOn_add_comp_toWeakSpace_symm_of_hasBoundedSublevelsOn hE₀ hg hb) hb

end CompactConstraint

end IsCompactOperator
