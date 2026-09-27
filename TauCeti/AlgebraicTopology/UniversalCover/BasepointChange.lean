/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.AlgebraicTopology.UniversalCover.Action
import TauCeti.Topology.IsLocalHomeomorph

/-!
# Changing the basepoint of a universal cover

A path `γ : Path x y` singles out a point of `UniversalCover x` over `y`. There is a unique
homeomorphism over `X` from `UniversalCover y` to `UniversalCover x` carrying the constant-path
point to this point. This is the basepoint change of the universal cover. The direction agrees
with concatenation: a path beginning at `y` is regarded, after changing basepoint, as beginning
with `γ` at `x`.

The construction uses uniqueness of pointed simply connected covers, proved in
`Classification.Pointed`, rather than choosing local sheets. It supplies the path-indexed
comparison needed when the chosen lift of a basepoint changes. No external formalization is
copied. The universal-cover construction itself adapts Kim
Morrison's work in [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292).
-/

public section
noncomputable section

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] {x y : X}

/-- Changing the basepoint along `γ` gives the unique homeomorphism over `X` that sends the
constant path at `y` to the class of `γ` at `x`. -/
def basepointChangeHomeomorph (γ : Path x y) : UniversalCover y ≃ₜ UniversalCover x := by
  have : LocallyPathConnectedSpace (UniversalCover x) :=
    (isCoveringMap x).isLocalHomeomorph.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (UniversalCover y) :=
    (isCoveringMap y).isLocalHomeomorph.locallyPathConnectedSpace
  exact (IsCoveringMap.exists_homeomorph_comp_eq_of_simplyConnectedSpace
    (f₀ := mk y (Path.Homotopic.Quotient.mk γ))
    (isCoveringMap y) (isCoveringMap x) (proj_basepointLift y) (by rfl)).choose

/-- Basepoint change sends the distinguished point to the path class defining the change. -/
@[simp]
theorem basepointChangeHomeomorph_basepointLift (γ : Path x y) :
    basepointChangeHomeomorph γ (mk y (Path.Homotopic.Quotient.refl y)) =
      mk y (Path.Homotopic.Quotient.mk γ) := by
  have : LocallyPathConnectedSpace (UniversalCover x) :=
    (isCoveringMap x).isLocalHomeomorph.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (UniversalCover y) :=
    (isCoveringMap y).isLocalHomeomorph.locallyPathConnectedSpace
  have h : basepointChangeHomeomorph γ (basepointLift y : UniversalCover y) =
      mk y (Path.Homotopic.Quotient.mk γ) := by
    exact (IsCoveringMap.exists_homeomorph_comp_eq_of_simplyConnectedSpace
      (f₀ := mk y (Path.Homotopic.Quotient.mk γ))
      (isCoveringMap y) (isCoveringMap x) (proj_basepointLift y) (by rfl)).choose_spec.1
  simpa only [basepointLift_coe] using h

/-- Basepoint change commutes with the projections to `X`. -/
theorem proj_basepointChangeHomeomorph (γ : Path x y) (e : UniversalCover y) :
    proj (basepointChangeHomeomorph γ e) = proj e := by
  have : LocallyPathConnectedSpace (UniversalCover x) :=
    (isCoveringMap x).isLocalHomeomorph.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (UniversalCover y) :=
    (isCoveringMap y).isLocalHomeomorph.locallyPathConnectedSpace
  exact congrFun (IsCoveringMap.exists_homeomorph_comp_eq_of_simplyConnectedSpace
    (f₀ := mk y (Path.Homotopic.Quotient.mk γ))
    (isCoveringMap y) (isCoveringMap x) (proj_basepointLift y)
    (by rfl)).choose_spec.2 e

/-- The inverse basepoint change also commutes with projection. -/
theorem proj_basepointChangeHomeomorph_symm (γ : Path x y) (e : UniversalCover x) :
    proj ((basepointChangeHomeomorph γ).symm e) = proj e := by
  rw [← proj_basepointChangeHomeomorph γ, Homeomorph.apply_symm_apply]

/-- Projection and the image of the constant path determine the basepoint-change map uniquely
among continuous maps. -/
theorem eq_basepointChangeHomeomorph (γ : Path x y) (f : C(UniversalCover y, UniversalCover x))
    (hf₀ : f (basepointLift y : UniversalCover y) =
      mk y (Path.Homotopic.Quotient.mk γ))
    (hf : ∀ e, proj (f e) = proj e) :
    f = (basepointChangeHomeomorph γ : C(UniversalCover y, UniversalCover x)) := by
  apply ContinuousMap.ext
  have hcomp : proj ∘ f = proj ∘ basepointChangeHomeomorph γ := by
    funext e
    exact (hf e).trans (proj_basepointChangeHomeomorph γ e).symm
  have hbase : (basepointChangeHomeomorph γ) (basepointLift y : UniversalCover y) =
      mk y (Path.Homotopic.Quotient.mk γ) := by
    rw [basepointLift_coe]
    exact basepointChangeHomeomorph_basepointLift γ
  exact congrFun ((isCoveringMap x).eq_of_comp_eq f.continuous
    (basepointChangeHomeomorph γ).continuous hcomp (basepointLift y)
    (hf₀.trans hbase.symm))

/-- Changing the basepoint along a constant path is the identity. -/
@[simp]
theorem basepointChangeHomeomorph_refl (x : X) :
    basepointChangeHomeomorph (Path.refl x) = Homeomorph.refl (UniversalCover x) := by
  apply Homeomorph.ext
  have h := eq_basepointChangeHomeomorph (Path.refl x)
    (ContinuousMap.id (UniversalCover x)) (by
      simp only [ContinuousMap.id_apply, basepointLift_coe,
        Path.Homotopic.Quotient.mk_refl])
    (fun _ => rfl)
  intro e
  simpa using congrArg (fun g : C(UniversalCover x, UniversalCover x) => g e) h.symm

end TauCeti.UniversalCover

end
