/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import TauCeti.AlgebraicTopology.UniversalCover.Action

/-!
# Basepoint change for the universal cover

A path `γ : Path x₀ x₁` identifies the universal covers based at its endpoints. In the
based-path model, the identification removes the initial path `γ`: it sends the class of a path
`α` starting at `x₀` to the class of `γ.symm.trans α`, now regarded as a path starting at `x₁`.

The construction uses `TauCeti.Path.prependUniversalCover`, which prepends a fixed path
to every representative and is continuous for the quotient topology on the universal cover.
Prepending a path and its reverse gives inverse continuous maps, producing
`TauCeti.Path.basepointChangeHomeomorph`.

The resulting homeomorphism lies over the identity of the base, sends the point represented by
`γ` to the constant-path point over `x₁`, depends only on the endpoint-preserving homotopy class
of `γ`, intertwines the fundamental-group actions at its endpoints, and respects reflexivity,
reversal, and concatenation. These properties make explicit the basepoint-change coherence of the
based-path universal-cover construction.

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
generalizes the fixed-loop argument from that pull request;
`TauCeti.AlgebraicTopology.UniversalCover.Action` now reuses the generalized theorem.
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
def basepointChangeHomeomorph (gamma : _root_.Path x₀ x₁) :
    UniversalCover x₀ ≃ₜ UniversalCover x₁ where
  toFun := prependUniversalCover gamma.symm
  invFun := prependUniversalCover gamma
  left_inv p := by
    rcases p with ⟨x, q⟩
    rw [prependUniversalCover_mk, prependUniversalCover_mk]
    congr 1
    rw [Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
  right_inv p := by
    rcases p with ⟨x, q⟩
    rw [prependUniversalCover_mk, prependUniversalCover_mk]
    congr 1
    rw [Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  continuous_toFun := continuous_prependUniversalCover gamma.symm
  continuous_invFun := continuous_prependUniversalCover gamma

/-- Basepoint change prepends the reverse path class to a representative. -/
@[simp]
theorem basepointChangeHomeomorph_apply_mk (gamma : _root_.Path x₀ x₁) (x : X)
    (q : Path.Homotopic.Quotient x₀ x) :
    basepointChangeHomeomorph gamma (mk x q) =
      mk x ((Path.Homotopic.Quotient.mk gamma).symm.trans q) := by
  -- Applying the bundled homeomorphism exposes its `toFun`, which is definitionally the
  -- prepending map; there is no separate projection lemma for this structure wrapper.
  change prependUniversalCover gamma.symm (mk x q) = _
  rw [prependUniversalCover_mk, Path.Homotopic.Quotient.mk_symm]

/-- The inverse basepoint change prepends the original path class to a representative. -/
@[simp]
theorem basepointChangeHomeomorph_symm_apply_mk (gamma : _root_.Path x₀ x₁) (x : X)
    (q : Path.Homotopic.Quotient x₁ x) :
    (basepointChangeHomeomorph gamma).symm (mk x q) =
      mk x ((Path.Homotopic.Quotient.mk gamma).trans q) := by
  exact prependUniversalCover_mk gamma x q

/-- Basepoint change lies over the identity map of the base. -/
@[simp]
theorem proj_basepointChangeHomeomorph (gamma : _root_.Path x₀ x₁)
    (p : UniversalCover x₀) :
    proj (basepointChangeHomeomorph gamma p) = proj p := by
  exact proj_prependUniversalCover gamma.symm p

/-- The inverse basepoint change also lies over the identity map of the base. -/
@[simp]
theorem proj_basepointChangeHomeomorph_symm (gamma : _root_.Path x₀ x₁)
    (p : UniversalCover x₁) :
    proj ((basepointChangeHomeomorph gamma).symm p) = proj p := by
  exact proj_prependUniversalCover gamma p

/-- On a based-path representative, basepoint change prepends the reverse of the changing path. -/
@[simp]
theorem basepointChangeHomeomorph_apply_ofBasedPath (gamma : _root_.Path x₀ x₁)
    (beta : BasedPath x₀) :
    basepointChangeHomeomorph gamma (ofBasedPath x₀ beta) =
      ofBasedPath x₁ (BasedPath.ofPath (gamma.symm.trans beta.toPath)) :=
  prependUniversalCover_ofBasedPath gamma.symm beta

/-- On a based-path representative, inverse basepoint change prepends the changing path. -/
@[simp]
theorem basepointChangeHomeomorph_symm_apply_ofBasedPath (gamma : _root_.Path x₀ x₁)
    (beta : BasedPath x₁) :
    (basepointChangeHomeomorph gamma).symm (ofBasedPath x₁ beta) =
      ofBasedPath x₀ (BasedPath.ofPath (gamma.trans beta.toPath)) :=
  prependUniversalCover_ofBasedPath gamma beta

/-- Basepoint change intertwines the fundamental-group actions under the corresponding
basepoint-change isomorphism of fundamental groups. -/
@[simp]
theorem basepointChangeHomeomorph_smul (gamma : _root_.Path x₀ x₁)
    (g : FundamentalGroup X x₀) (p : UniversalCover x₀) :
    basepointChangeHomeomorph gamma (g • p) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath gamma g •
        basepointChangeHomeomorph gamma p := by
  rcases p with ⟨x, q⟩
  simp only [smul_mk, basepointChangeHomeomorph_apply_mk]
  congr 1
  let f := FundamentalGroup.fundamentalGroupMulEquivOfPath gamma
  have h := FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply gamma (f g⁻¹)
  rw [MulEquiv.symm_apply_apply, map_inv] at h
  -- `FundamentalGroup.toPath` is an abbreviation; expose the path-quotient identity supplied
  -- by the fundamental-group basepoint-change formula.
  change g⁻¹.toPath = (Path.Homotopic.Quotient.mk gamma).trans
    ((f g)⁻¹.toPath.trans (Path.Homotopic.Quotient.mk gamma).symm) at h
  have hprefix : (Path.Homotopic.Quotient.mk gamma).symm.trans g⁻¹.toPath =
      (f g)⁻¹.toPath.trans (Path.Homotopic.Quotient.mk gamma).symm := by
    rw [h, ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  rw [← Path.Homotopic.Quotient.trans_assoc, hprefix,
    Path.Homotopic.Quotient.trans_assoc]

/-- Inverse basepoint change intertwines the target action with transport back to the source
fundamental group. -/
@[simp]
theorem basepointChangeHomeomorph_symm_smul (gamma : _root_.Path x₀ x₁)
    (g : FundamentalGroup X x₁) (p : UniversalCover x₁) :
    (basepointChangeHomeomorph gamma).symm (g • p) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath gamma).symm g •
        (basepointChangeHomeomorph gamma).symm p := by
  apply (basepointChangeHomeomorph gamma).injective
  rw [Homeomorph.apply_symm_apply, basepointChangeHomeomorph_smul,
    MulEquiv.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- Basepoint change sends the point represented by the changing path to the constant-path point
over its target. -/
theorem basepointChangeHomeomorph_apply_self (gamma : _root_.Path x₀ x₁) :
    basepointChangeHomeomorph gamma (ofBasedPath x₀ (BasedPath.ofPath gamma)) =
      basepointLift x₁ := by
  rw [ofBasedPath_ofPath, basepointChangeHomeomorph_apply_mk, basepointLift_coe,
    Path.Homotopic.Quotient.symm_trans]

/-- The basepoint-change homeomorphism is the unique continuous map over `X` that sends the point
represented by the changing path to the constant-path point. -/
theorem eq_basepointChangeHomeomorph (gamma : _root_.Path x₀ x₁)
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {f : C(UniversalCover x₀, UniversalCover x₁)}
    (hgamma : f (ofBasedPath x₀ (BasedPath.ofPath gamma)) = basepointLift x₁)
    (hproj : proj ∘ f = proj) :
    f = (basepointChangeHomeomorph gamma : C(UniversalCover x₀, UniversalCover x₁)) := by
  have hproj' : proj ∘ f = proj ∘ (basepointChangeHomeomorph gamma :
      UniversalCover x₀ → UniversalCover x₁) := by
    rw [hproj]
    funext p
    exact (proj_basepointChangeHomeomorph gamma p).symm
  apply ContinuousMap.ext
  exact congrFun ((isSeparatedMap_proj x₁).eq_of_comp_eq (isLocallyInjective_proj x₁)
    f.continuous
    (basepointChangeHomeomorph gamma).continuous hproj'
    (ofBasedPath x₀ (BasedPath.ofPath gamma))
    (hgamma.trans (basepointChangeHomeomorph_apply_self gamma).symm))

/-- Homotopic basepoint-change paths induce the same homeomorphism. -/
theorem basepointChangeHomeomorph_eq_of_homotopic {gamma delta : _root_.Path x₀ x₁}
    (h : gamma.Homotopic delta) :
    basepointChangeHomeomorph gamma = basepointChangeHomeomorph delta := by
  apply Homeomorph.ext
  rintro ⟨x, q⟩
  simp only [basepointChangeHomeomorph_apply_mk]
  congr 1
  exact congrArg (fun r => r.trans q)
    (congrArg Path.Homotopic.Quotient.symm (Quotient.sound h))

end TauCeti.Path

namespace TauCeti.UniversalCover

/-- Changing basepoint along a constant path gives the identity homeomorphism. -/
@[simp]
theorem basepointChangeHomeomorph_refl (x : X) :
    TauCeti.Path.basepointChangeHomeomorph (Path.refl x) =
      Homeomorph.refl (UniversalCover x) := by
  apply Homeomorph.ext
  intro p
  exact prependUniversalCover_refl p

end TauCeti.UniversalCover

namespace TauCeti.Path

open UniversalCover

variable {x₀ x₁ x₂ : X}

/-- Reversing the changing path reverses the basepoint-change homeomorphism. -/
@[simp]
theorem basepointChangeHomeomorph_symm (gamma : _root_.Path x₀ x₁) :
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
theorem basepointChangeHomeomorph_trans (gamma : _root_.Path x₀ x₁)
    (delta : _root_.Path x₁ x₂) :
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
