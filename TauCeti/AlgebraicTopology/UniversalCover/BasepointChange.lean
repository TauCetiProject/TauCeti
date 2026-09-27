/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action

/-!
# Changing the basepoint of a universal cover

A path `γ : Path x y` singles out a point of `UniversalCover x` over `y`. Prepending `γ` gives
a homeomorphism over `X` from `UniversalCover y` to `UniversalCover x`, carrying the constant-path
point to this point. This is the basepoint change of the universal cover. The direction agrees
with concatenation: a path beginning at `y` is regarded, after changing basepoint, as beginning
with `γ` at `x`.

The universal-cover construction itself adapts Kim Morrison's work in
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292).
-/

public section
noncomputable section

open scoped unitInterval

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- Prepending a fixed path is continuous on the based-path quotient. -/
theorem continuous_basepointPrepend (γ : Path x y) :
    Continuous (fun e : UniversalCover y =>
      mk e.proj ((Path.Homotopic.Quotient.mk γ).trans e.path)) := by
  rw [(isQuotientMap_ofBasedPath y).continuous_iff]
  suffices h : Continuous (fun β : BasedPath y =>
      ofBasedPath x (BasedPath.ofPath (γ.trans β.toPath))) by
    apply h.congr
    intro β
    rw [ofBasedPath_ofPath, Function.comp_apply, ofBasedPath_def,
      Path.Homotopic.Quotient.mk_trans]
  refine (continuous_ofBasedPath x).comp (Continuous.subtype_mk ?_ _)
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have h_eval : Continuous fun p : BasedPath y × I => p.1.1 p.2 :=
    continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)
  -- The underlying continuous map is the concatenation of a fixed path and a family of paths.
  change Continuous fun p : BasedPath y × I => γ.trans p.1.toPath p.2
  exact Path.trans_continuous_family (a := fun _ : BasedPath y => x)
    (b := fun _ : BasedPath y => y)
    (c := fun β : BasedPath y => BasedPath.endpoint β)
    (fun _ => γ) (Path.continuous_uncurry_iff.mpr continuous_const)
    (fun β => β.toPath) h_eval

/-- Changing the basepoint along `γ` gives a homeomorphism over `X` that sends the constant path
at `y` to the class of `γ` at `x`. -/
@[expose] def basepointChangeHomeomorph (γ : Path x y) :
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
  continuous_toFun := continuous_basepointPrepend γ
  continuous_invFun := continuous_basepointPrepend γ.symm

/-- Basepoint change sends the distinguished point to the path class defining the change. -/
theorem basepointChangeHomeomorph_apply_basepointLift (γ : Path x y) :
    basepointChangeHomeomorph γ (basepointLift y : UniversalCover y) =
      mk y (Path.Homotopic.Quotient.mk γ) :=
  by simp [basepointChangeHomeomorph, basepointLift_coe]

/-- Basepoint change commutes with the projections to `X`. -/
@[simp]
theorem proj_basepointChangeHomeomorph (γ : Path x y) (e : UniversalCover y) :
    proj (basepointChangeHomeomorph γ e) = proj e :=
  rfl

/-- Basepoint change prepends `γ` to a represented path class. -/
@[simp]
theorem basepointChangeHomeomorph_apply_mk (γ : Path x y) {z : X}
    (q : Path.Homotopic.Quotient y z) :
    basepointChangeHomeomorph γ (mk z q) =
      mk z ((Path.Homotopic.Quotient.mk γ).trans q) := by
  rfl

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

/-- The inverse basepoint change also commutes with projection. -/
theorem proj_basepointChangeHomeomorph_symm (γ : Path x y) (e : UniversalCover x) :
    proj ((basepointChangeHomeomorph γ).symm e) = proj e := by
  rw [← proj_basepointChangeHomeomorph γ, Homeomorph.apply_symm_apply]

/-- Reversing the path reverses the basepoint-change homeomorphism. -/
@[simp]
theorem basepointChangeHomeomorph_symm (γ : Path x y) :
    (basepointChangeHomeomorph γ).symm = basepointChangeHomeomorph γ.symm := by
  apply Homeomorph.ext
  rintro ⟨z, q⟩
  rfl

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
