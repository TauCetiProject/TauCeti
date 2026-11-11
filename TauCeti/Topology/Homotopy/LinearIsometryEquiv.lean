/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Homotopies along paths of linear isometries

A path `γ` of linear isometries of a normed space `E`, continuous in the operator-norm topology,
moves every point `x` of `E` along the path `t ↦ γ t x`. On a subset `S` of `E` preserved by
every `γ t`, this is a homotopy `(t, x) ↦ γ t x` between any two self-maps of `S` acting as
`γ 0` and `γ 1`.

## Main declarations

* `TauCeti.linearIsometryEquivPathHomotopy`: the homotopy `(t, x) ↦ γ t x` of self-maps of an
  invariant subset `S`, read on `ULift S` so that it applies to the disks and spheres of
  `TopCat`.
* `TauCeti.coe_linearIsometryEquivPathHomotopy_apply_down`: the homotopy acts at time `t` by
  `γ t`.
-/

public section

noncomputable section

open Set unitInterval

universe u

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {S : Set E} {γ : I → (E ≃ₗᵢ[𝕜] E)}

/-- A path `γ` of linear isometries of `E`, continuous in the operator-norm topology and
preserving a subset `S`, gives the homotopy `(t, x) ↦ γ t x` from a self-map `f₀` of `S` acting as
`γ 0` to a self-map `f₁` of `S` acting as `γ 1`. -/
def linearIsometryEquivPathHomotopy (hS : ∀ t, MapsTo (γ t) S S)
    (hγ : Continuous (fun t ↦ ((γ t).toContinuousLinearEquiv : E →L[𝕜] E)))
    {f₀ f₁ : C(ULift.{u} S, ULift.{u} S)}
    (hf₀ : ∀ x, ((f₀ x).down : E) = γ 0 x.down) (hf₁ : ∀ x, ((f₁ x).down : E) = γ 1 x.down) :
    f₀.Homotopy f₁ where
  toFun p := ULift.up ⟨γ p.1 p.2.down, hS p.1 p.2.down.2⟩
  continuous_toFun := continuous_uliftUp.comp (((hγ.comp continuous_fst).clm_apply
    (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd))).subtype_mk _)
  map_zero_left x := ULift.ext (Subtype.ext (hf₀ x).symm)
  map_one_left x := ULift.ext (Subtype.ext (hf₁ x).symm)

/-- The homotopy `TauCeti.linearIsometryEquivPathHomotopy` acts at time `t` by `γ t`. -/
@[simp]
theorem coe_linearIsometryEquivPathHomotopy_apply_down (hS : ∀ t, MapsTo (γ t) S S)
    (hγ : Continuous (fun t ↦ ((γ t).toContinuousLinearEquiv : E →L[𝕜] E)))
    {f₀ f₁ : C(ULift.{u} S, ULift.{u} S)}
    (hf₀ : ∀ x, ((f₀ x).down : E) = γ 0 x.down) (hf₁ : ∀ x, ((f₁ x).down : E) = γ 1 x.down)
    (p : I × ULift.{u} S) :
    ((linearIsometryEquivPathHomotopy hS hγ hf₀ hf₁ p).down : E) = γ p.1 p.2.down :=
  (rfl)

end TauCeti
