/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Continuous bilinear maps on `ULift`s

A continuous bilinear map `L : A →L[𝕜] B →L[𝕜] G` transports along the linear isometries
`LinearIsometryEquiv.ulift` to a continuous bilinear map
`ContinuousLinearMap.uliftBilinear L : ULift A →L[𝕜] ULift B →L[𝕜] ULift G` between `ULift`s of
its spaces in arbitrary universes (`ContinuousLinearMap.uliftBilinear_apply`), without increasing
the operator norm (`ContinuousLinearMap.norm_uliftBilinear_le`). This moves a bilinear map into a
common universe, as needed by inductions that pass through spaces of continuous linear maps, such
as inductions on the order of a derivative.
-/

public section

universe uA uB uG wA wB wG

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {A : Type uA} {B : Type uB} {G : Type uG}
  [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B] [NormedSpace 𝕜 B]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A continuous bilinear map transported to `ULift`s of its spaces along
`LinearIsometryEquiv.ulift`. -/
noncomputable def uliftBilinear (L : A →L[𝕜] B →L[𝕜] G) :
    ULift.{wA} A →L[𝕜] ULift.{wB} B →L[𝕜] ULift.{wG} G :=
  compL 𝕜 (ULift.{wA} A) (ULift.{wB} B →L[𝕜] G) (ULift.{wB} B →L[𝕜] ULift.{wG} G)
    (compL 𝕜 (ULift.{wB} B) G (ULift.{wG} G)
      ((LinearIsometryEquiv.ulift 𝕜 G).symm : G →L[𝕜] ULift.{wG} G))
    ((L.comp (LinearIsometryEquiv.ulift 𝕜 A : ULift.{wA} A →L[𝕜] A)).flip.comp
      (LinearIsometryEquiv.ulift 𝕜 B : ULift.{wB} B →L[𝕜] B)).flip

@[simp]
theorem uliftBilinear_apply (L : A →L[𝕜] B →L[𝕜] G) (a : ULift.{wA} A) (b : ULift.{wB} B) :
    (uliftBilinear L : ULift.{wA} A →L[𝕜] ULift.{wB} B →L[𝕜] ULift.{wG} G) a b =
      (LinearIsometryEquiv.ulift 𝕜 G).symm
        (L (LinearIsometryEquiv.ulift 𝕜 A a) (LinearIsometryEquiv.ulift 𝕜 B b)) := by
  simp [uliftBilinear]

/-- Transporting a continuous bilinear map to `ULift`s does not increase its operator norm. -/
theorem norm_uliftBilinear_le (L : A →L[𝕜] B →L[𝕜] G) :
    ‖(uliftBilinear L : ULift.{wA} A →L[𝕜] ULift.{wB} B →L[𝕜] ULift.{wG} G)‖ ≤ ‖L‖ := by
  refine opNorm_le_bound _ (norm_nonneg L) fun v => ?_
  refine opNorm_le_bound _ (by positivity) fun w => ?_
  rw [uliftBilinear_apply, LinearIsometryEquiv.norm_map]
  exact L.le_opNorm₂ _ _

/-- Transporting a continuous bilinear map to `ULift`s does not increase its operator norm. -/
theorem nnnorm_uliftBilinear_le (L : A →L[𝕜] B →L[𝕜] G) :
    ‖(uliftBilinear L : ULift.{wA} A →L[𝕜] ULift.{wB} B →L[𝕜] ULift.{wG} G)‖₊ ≤ ‖L‖₊ :=
  norm_uliftBilinear_le L

/-- A bilinear product read through `uliftBilinear` and linear isometries of the source is the
lifted product. -/
theorem uliftBilinear_comp {E' E : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (L : A →L[𝕜] B →L[𝕜] G) (f : E → A) (g : E → B)
    (e : E' ≃ₗᵢ[𝕜] E) :
    (fun x => (uliftBilinear L : ULift.{wA} A →L[𝕜] ULift.{wB} B →L[𝕜] ULift.{wG} G)
        (((LinearIsometryEquiv.ulift 𝕜 A).symm ∘ f ∘ e) x)
        (((LinearIsometryEquiv.ulift 𝕜 B).symm ∘ g ∘ e) x)) =
      (LinearIsometryEquiv.ulift 𝕜 G).symm ∘ (fun x => L (f x) (g x)) ∘ e := by
  funext x
  simp only [Function.comp_apply, uliftBilinear_apply, LinearIsometryEquiv.apply_symm_apply]

end ContinuousLinearMap
