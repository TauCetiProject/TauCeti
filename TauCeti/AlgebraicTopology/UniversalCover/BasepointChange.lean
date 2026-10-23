/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Covering

/-!
# Changing the basepoint of a universal cover

A path `γ : Path x y` singles out a point of `UniversalCover x` over `y`. Prepending `γ` gives
a homeomorphism over `X` from `UniversalCover y` to `UniversalCover x`, carrying the constant-path
point to this point. This is the basepoint change of the universal cover. The direction agrees
with concatenation: a path beginning at `y` is regarded, after changing basepoint, as beginning
with `γ` at `x`.

The universal-cover construction itself adapts Kim Morrison's work in
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292).
The uniqueness proof uses Thomas Browning's `IsCoveringMap.eq_of_comp_eq` in
`Mathlib.Topology.Covering.Basic`, recorded there as Proposition 1.34 of [hatcher02].
-/

public section
noncomputable section

open scoped unitInterval

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- Changing the basepoint along `γ` gives a homeomorphism over `X` that sends the constant path
at `y` to the class of `γ` at `x`. -/
def basepointChangeHomeomorph (γ : Path x y) :
    UniversalCover y ≃ₜ UniversalCover x where
  toFun e := mk e.proj ((Path.Homotopic.Quotient.mk γ).trans e.path)
  invFun e := mk e.proj ((Path.Homotopic.Quotient.mk γ.symm).trans e.path)
  left_inv e := by
    rcases e with ⟨z, q⟩
    simp only [Path.Homotopic.Quotient.mk_symm]
    congr 1
    rw [← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  right_inv e := by
    rcases e with ⟨z, q⟩
    simp only [Path.Homotopic.Quotient.mk_symm]
    congr 1
    rw [← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
  continuous_toFun := continuous_prepend γ
  continuous_invFun := continuous_prepend γ.symm

/-- Basepoint change sends the distinguished point to the path class defining the change. -/
theorem basepointChangeHomeomorph_apply_basepointLift (γ : Path x y) :
    basepointChangeHomeomorph γ (basepointLift y : UniversalCover y) =
      mk y (Path.Homotopic.Quotient.mk γ) :=
  by simp [basepointChangeHomeomorph, basepointLift_coe]

/-- Basepoint change commutes with the projections to `X`. -/
@[simp]
theorem proj_basepointChangeHomeomorph (γ : Path x y) (e : UniversalCover y) :
  proj (basepointChangeHomeomorph γ e) = proj e :=
  by simp [basepointChangeHomeomorph]

/-- Basepoint change prepends `γ` to a represented path class. -/
@[simp]
theorem basepointChangeHomeomorph_apply_mk (γ : Path x y) {z : X}
    (q : Path.Homotopic.Quotient y z) :
    basepointChangeHomeomorph γ (mk z q) =
      mk z ((Path.Homotopic.Quotient.mk γ).trans q) := by
  simp [basepointChangeHomeomorph]

/-- Changing basepoint along concatenated paths composes the corresponding homeomorphisms. -/
@[simp]
theorem basepointChangeHomeomorph_trans (γ : Path x y) {z : X} (δ : Path y z) :
    basepointChangeHomeomorph (γ.trans δ) =
      (basepointChangeHomeomorph δ).trans (basepointChangeHomeomorph γ) := by
  apply Homeomorph.ext
  rintro ⟨w, q⟩
  simp only [basepointChangeHomeomorph_apply_mk, Homeomorph.trans_apply,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

/-- Homotopic paths induce the same basepoint change. -/
theorem basepointChangeHomeomorph_eq_of_homotopic {γ δ : Path x y}
    (h : Path.Homotopic γ δ) :
    basepointChangeHomeomorph γ = basepointChangeHomeomorph δ := by
  apply Homeomorph.ext
  rintro ⟨z, q⟩
  simp only [basepointChangeHomeomorph_apply_mk]
  have hq : Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk δ :=
    Quotient.sound h
  rw [hq]

/-- Reversing the path reverses the basepoint-change homeomorphism. -/
@[simp]
theorem basepointChangeHomeomorph_symm (γ : Path x y) :
    (basepointChangeHomeomorph γ).symm = basepointChangeHomeomorph γ.symm := by
  apply Homeomorph.ext
  rintro ⟨z, q⟩
  simp [basepointChangeHomeomorph]

/-- Projection and the image of the constant path determine the basepoint-change map uniquely
among continuous maps when the projection is a covering map. -/
theorem eq_basepointChangeHomeomorph (γ : Path x y) (f : C(UniversalCover y, UniversalCover x))
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (hf₀ : f (basepointLift y : UniversalCover y) =
      mk y (Path.Homotopic.Quotient.mk γ))
    (hf : ∀ e, proj (f e) = proj e) :
    f = (basepointChangeHomeomorph γ : C(UniversalCover y, UniversalCover x)) := by
  apply ContinuousMap.ext
  have hcomp : proj ∘ f = proj ∘ basepointChangeHomeomorph γ := by
    funext e
    exact (hf e).trans (proj_basepointChangeHomeomorph γ e).symm
  have hbase := basepointChangeHomeomorph_apply_basepointLift γ
  exact congrFun ((isCoveringMap x).eq_of_comp_eq f.continuous
    (basepointChangeHomeomorph γ).continuous hcomp (basepointLift y)
    (hf₀.trans hbase.symm))

/-- Changing the basepoint along a constant path is the identity. -/
@[simp]
theorem basepointChangeHomeomorph_refl (x : X) :
    basepointChangeHomeomorph (Path.refl x) = Homeomorph.refl (UniversalCover x) := by
  apply Homeomorph.ext
  rintro ⟨z, q⟩
  simp [basepointChangeHomeomorph]

end TauCeti.UniversalCover

end
