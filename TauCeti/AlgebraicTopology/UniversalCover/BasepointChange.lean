/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action

/-!
# Basepoint change for the universal cover

A path `γ : Path x₀ x₁` identifies the universal covers based at its endpoints. In the
based-path model, the identification removes the initial path `γ`: it sends the class of a path
`α` starting at `x₀` to the class of `γ.symm.trans α`, now regarded as a path starting at `x₁`.

The construction uses `TauCeti.Path.prependUniversalCover`, which prepends a fixed path to every
representative and is continuous for the quotient topology on the universal cover. Prepending a
path and its reverse gives inverse continuous maps, producing
`TauCeti.Path.basepointChangeHomeomorph`.

The resulting homeomorphism lies over the identity of the base, sends the point represented by
`γ` to the constant-path point over `x₁`, depends only on the endpoint-preserving homotopy class
of `γ`, and respects reflexivity, reversal, and concatenation. These properties make explicit the
basepoint-change coherence of the based-path universal-cover construction.

## Main declarations

* `TauCeti.Path.basepointChangeHomeomorph`: the homeomorphism between universal covers
  based at the endpoints of a path.
* `TauCeti.Path.basepointChangeHomeomorph_trans`: basepoint change respects path
  concatenation.

## References

This is the standard change-of-basepoint map in the based-path construction of the universal
cover; compare Hatcher, *Algebraic Topology*, Section 1.3. The quotient model used here is adapted
from Kim Morrison's [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292)
and is credited in `TauCeti.AlgebraicTopology.UniversalCover.Basic`. The continuity argument
generalizes the fixed-loop argument in `TauCeti.AlgebraicTopology.UniversalCover.Action`, also
adapted from that pull request.
-/

public section
noncomputable section

open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]

namespace TauCeti.Path

open UniversalCover

variable {x₀ x₁ x₂ : X}

/-- **A path identifies the universal covers based at its endpoints.** The forward map removes
the chosen initial path by prepending its reverse; the inverse map prepends the path itself. -/
def basepointChangeHomeomorph (gamma : Path x₀ x₁) :
    UniversalCover x₀ ≃ₜ UniversalCover x₁ where
  toFun := TauCeti.Path.prependUniversalCover gamma.symm
  invFun := TauCeti.Path.prependUniversalCover gamma
  left_inv p := by
    rcases p with ⟨x, q⟩
    rw [TauCeti.Path.prependUniversalCover_mk, TauCeti.Path.prependUniversalCover_mk]
    congr 1
    rw [Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
  right_inv p := by
    rcases p with ⟨x, q⟩
    rw [TauCeti.Path.prependUniversalCover_mk, TauCeti.Path.prependUniversalCover_mk]
    congr 1
    rw [Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  continuous_toFun := TauCeti.Path.continuous_prependUniversalCover gamma.symm
  continuous_invFun := TauCeti.Path.continuous_prependUniversalCover gamma

/-- Basepoint change prepends the reverse path class to a representative. -/
@[simp]
theorem basepointChangeHomeomorph_apply_mk (gamma : Path x₀ x₁) (x : X)
    (q : Path.Homotopic.Quotient x₀ x) :
    basepointChangeHomeomorph gamma (mk x q) =
      mk x ((Path.Homotopic.Quotient.mk gamma).symm.trans q) := by
  change TauCeti.Path.prependUniversalCover gamma.symm (mk x q) = _
  rw [TauCeti.Path.prependUniversalCover_mk, Path.Homotopic.Quotient.mk_symm]

/-- The inverse basepoint change prepends the original path class to a representative. -/
@[simp]
theorem basepointChangeHomeomorph_symm_apply_mk (gamma : Path x₀ x₁) (x : X)
    (q : Path.Homotopic.Quotient x₁ x) :
    (basepointChangeHomeomorph gamma).symm (mk x q) =
      mk x ((Path.Homotopic.Quotient.mk gamma).trans q) := by
  exact TauCeti.Path.prependUniversalCover_mk gamma x q

/-- Basepoint change lies over the identity map of the base. -/
@[simp]
theorem proj_basepointChangeHomeomorph (gamma : Path x₀ x₁) (p : UniversalCover x₀) :
    proj (basepointChangeHomeomorph gamma p) = proj p := by
  exact TauCeti.Path.proj_prependUniversalCover gamma.symm p

/-- The inverse basepoint change also lies over the identity map of the base. -/
@[simp]
theorem proj_basepointChangeHomeomorph_symm (gamma : Path x₀ x₁) (p : UniversalCover x₁) :
    proj ((basepointChangeHomeomorph gamma).symm p) = proj p := by
  exact TauCeti.Path.proj_prependUniversalCover gamma p

/-- On a based-path representative, basepoint change prepends the reverse of the changing path. -/
@[simp]
theorem basepointChangeHomeomorph_apply_ofBasedPath (gamma : Path x₀ x₁)
    (beta : BasedPath x₀) :
    basepointChangeHomeomorph gamma (ofBasedPath x₀ beta) =
      ofBasedPath x₁ (BasedPath.ofPath (gamma.symm.trans beta.toPath)) :=
  TauCeti.Path.prependUniversalCover_ofBasedPath gamma.symm beta

/-- On a based-path representative, inverse basepoint change prepends the changing path. -/
@[simp]
theorem basepointChangeHomeomorph_symm_apply_ofBasedPath (gamma : Path x₀ x₁)
    (beta : BasedPath x₁) :
    (basepointChangeHomeomorph gamma).symm (ofBasedPath x₁ beta) =
      ofBasedPath x₀ (BasedPath.ofPath (gamma.trans beta.toPath)) :=
  TauCeti.Path.prependUniversalCover_ofBasedPath gamma beta

private theorem mem_own_sheet {x : X} {U : Set X} (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) : mk x q ∈ sheet U hxU q := by
  induction q using Quotient.inductionOn with
  | h gamma =>
      change mk x (Path.Homotopic.Quotient.mk gamma) ∈
        sheet U hxU (Path.Homotopic.Quotient.mk gamma)
      rw [← ofBasedPath_ofPath gamma]
      exact mem_sheet_self hxU gamma

private theorem isLocallyInjective_proj [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    IsLocallyInjective (proj : UniversalCover x₀ → X) := by
  rintro ⟨x, q⟩
  obtain ⟨U, hU_open, hxU, _hU_pathConn, hU_slsc⟩ :=
    exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial x
  exact ⟨sheet U hxU q, isOpen_sheet U hU_open hxU q, mem_own_sheet hxU q,
    proj_injOn_sheet hU_slsc hxU q⟩

private theorem isSeparatedMap_proj [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    IsSeparatedMap (proj : UniversalCover x₀ → X) := by
  rintro ⟨x, q₁⟩ ⟨y, q₂⟩ hxy hne
  change x = y at hxy
  subst y
  obtain ⟨U, hU_open, hxU, _hU_pathConn, hU_slsc⟩ :=
    exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial x
  have hq : q₁ ≠ q₂ := by
    intro h
    apply hne
    subst h
    rfl
  exact ⟨sheet U hxU q₁, sheet U hxU q₂,
    isOpen_sheet U hU_open hxU q₁, isOpen_sheet U hU_open hxU q₂,
    mem_own_sheet hxU q₁, mem_own_sheet hxU q₂,
    pairwise_disjoint_sheet hU_slsc hxU hq⟩

/-- The basepoint-change homeomorphism is the unique continuous map over `X` that sends the point
represented by the changing path to the constant-path point. -/
theorem eq_basepointChangeHomeomorph (gamma : Path x₀ x₁)
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {f : C(UniversalCover x₀, UniversalCover x₁)}
    (hgamma : f (ofBasedPath x₀ (BasedPath.ofPath gamma)) = basepointLift x₁)
    (hproj : proj ∘ f = proj) :
    f = (basepointChangeHomeomorph gamma : C(UniversalCover x₀, UniversalCover x₁)) := by
  have hbase :
      basepointChangeHomeomorph gamma (ofBasedPath x₀ (BasedPath.ofPath gamma)) =
        basepointLift x₁ := by
    rw [ofBasedPath_ofPath, basepointChangeHomeomorph_apply_mk, basepointLift_coe,
      Path.Homotopic.Quotient.symm_trans]
  have hproj' : proj ∘ f = proj ∘ (basepointChangeHomeomorph gamma :
      UniversalCover x₀ → UniversalCover x₁) := by
    rw [hproj]
    funext p
    exact (proj_basepointChangeHomeomorph gamma p).symm
  apply ContinuousMap.ext
  exact congrFun ((isSeparatedMap_proj x₁).eq_of_comp_eq (isLocallyInjective_proj x₁)
    f.continuous
    (basepointChangeHomeomorph gamma).continuous hproj'
    (ofBasedPath x₀ (BasedPath.ofPath gamma)) (hgamma.trans hbase.symm))

/-- Homotopic basepoint-change paths induce the same homeomorphism. -/
theorem basepointChangeHomeomorph_eq_of_homotopic {gamma delta : Path x₀ x₁}
    (h : gamma.Homotopic delta) :
    basepointChangeHomeomorph gamma = basepointChangeHomeomorph delta := by
  apply Homeomorph.ext
  rintro ⟨x, q⟩
  simp only [basepointChangeHomeomorph_apply_mk]
  congr 1
  exact congrArg (fun r => r.trans q)
    (congrArg Path.Homotopic.Quotient.symm (Quotient.sound h))

/-- Changing basepoint along a constant path gives the identity homeomorphism. -/
@[simp]
theorem basepointChangeHomeomorph_refl (x : X) :
    basepointChangeHomeomorph (Path.refl x) = Homeomorph.refl (UniversalCover x) := by
  apply Homeomorph.ext
  intro p
  exact TauCeti.Path.prependUniversalCover_refl p

/-- Reversing the changing path reverses the basepoint-change homeomorphism. -/
@[simp]
theorem basepointChangeHomeomorph_symm (gamma : Path x₀ x₁) :
    basepointChangeHomeomorph gamma.symm = (basepointChangeHomeomorph gamma).symm := by
  apply Homeomorph.ext
  rintro ⟨x, q⟩
  simp only [basepointChangeHomeomorph_apply_mk,
    basepointChangeHomeomorph_symm_apply_mk]
  congr 1
  congr 1
  exact (Path.Homotopic.Quotient.mk_symm gamma.symm).symm.trans
    (congrArg Path.Homotopic.Quotient.mk (Path.symm_symm gamma))

/-- Changing basepoint along a concatenation is the composite of the two basepoint changes. -/
@[simp]
theorem basepointChangeHomeomorph_trans (gamma : Path x₀ x₁) (delta : Path x₁ x₂) :
    basepointChangeHomeomorph (gamma.trans delta) =
      (basepointChangeHomeomorph gamma).trans (basepointChangeHomeomorph delta) := by
  apply Homeomorph.ext
  rintro ⟨x, q⟩
  simp only [Homeomorph.trans_apply, basepointChangeHomeomorph_apply_mk,
    Path.Homotopic.Quotient.mk_trans]
  congr 1
  have hsymm : ((Path.Homotopic.Quotient.mk gamma).trans
      (Path.Homotopic.Quotient.mk delta)).symm =
      (Path.Homotopic.Quotient.mk delta).symm.trans
        (Path.Homotopic.Quotient.mk gamma).symm := by
    rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm,
      Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_symm]
  rw [hsymm, Path.Homotopic.Quotient.trans_assoc]

end TauCeti.Path
