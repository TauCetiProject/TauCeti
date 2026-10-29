/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# The Lie derivative of differential forms on normed spaces

The Lie derivative of a differential form `ω : E → E [⋀^Fin k]→L[𝕜] F` along a vector field
`V : E → E` is

`L_V ω (x) (v₀, …, vₖ₋₁) = Dω(x)(V x)(v₀, …, vₖ₋₁) + ∑ i, ω(x)(v₀, …, DV(x) vᵢ, …, vₖ₋₁)`.

The second term is the action of `DV(x)` on `ω(x)` as a derivation, which is Mathlib's
derivative of `g ↦ (ω x).compContinuousLinearMap g` at the identity,
`ContinuousAlternatingMap.fderivCompContinuousLinearMap`. The definition needs no flow and is
total, with junk values where `ω` or `V` is not differentiable; the within-set version takes
derivatives within an arbitrary set, so it applies to chart ranges with boundary or corners.

Two characterizations follow.

* Evaluated on vector fields, `L_V ω (X₀, …, Xₖ₋₁)` is the derivative of `ω (X₀, …, Xₖ₋₁)`
  along `V` minus the terms `ω (X₀, …, [V, Xᵢ], …, Xₖ₋₁)` [Lee, Cor. 12.33].
* **Cartan's formula** `L_V = ι_V ∘ d + d ∘ ι_V` [Lee, Thm. 14.35], where the interior product
  `ι_V` is Mathlib's `ContinuousAlternatingMap.curryLeft`. In degree zero only the first term
  occurs.

## Main declarations

* `TauCeti.lieDerivFormWithin`, `TauCeti.lieDerivForm`: the Lie derivative of a form.
* `TauCeti.lieDerivFormWithin_add`, `TauCeti.lieDerivFormWithin_smul`: linearity in the form.
* `TauCeti.lieDerivFormWithin_apply_vectorField`: the bracket formula.
* `TauCeti.lieDerivFormWithin_eq_curryLeft_extDerivWithin_add`: Cartan's formula.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Corollary 12.33 and Theorem 14.35.
-/

public section

noncomputable section

open Set ContinuousAlternatingMap VectorField

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {k : ℕ} {V : E → E} {s : Set E} {x : E}

/-- The Lie derivative within `s` at `x` of a differential form `ω` along a vector field `V`:
the derivative of `ω` in the direction `V x`, plus the action of the derivative of `V` on `ω x`
as a derivation. -/
def lieDerivFormWithin (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F) (s : Set E) (x : E) :
    E [⋀^Fin k]→L[𝕜] F :=
  fderivWithin 𝕜 ω s x (V x) +
    (ω x).fderivCompContinuousLinearMap (.id 𝕜 E) (fderivWithin 𝕜 V s x)

/-- The Lie derivative of a differential form `ω` along a vector field `V`. -/
def lieDerivForm (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F) (x : E) : E [⋀^Fin k]→L[𝕜] F :=
  fderiv 𝕜 ω x (V x) + (ω x).fderivCompContinuousLinearMap (.id 𝕜 E) (fderiv 𝕜 V x)

theorem lieDerivFormWithin_def (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F) (s : Set E) (x : E) :
    lieDerivFormWithin V ω s x =
      fderivWithin 𝕜 ω s x (V x) +
        (ω x).fderivCompContinuousLinearMap (.id 𝕜 E) (fderivWithin 𝕜 V s x) := (rfl)

theorem lieDerivForm_def (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F) (x : E) :
    lieDerivForm V ω x =
      fderiv 𝕜 ω x (V x) + (ω x).fderivCompContinuousLinearMap (.id 𝕜 E) (fderiv 𝕜 V x) := (rfl)

@[simp]
theorem lieDerivFormWithin_univ (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F) :
    lieDerivFormWithin V ω univ = lieDerivForm V ω := by
  ext x : 1
  simp [lieDerivFormWithin_def, lieDerivForm_def]

/-- Evaluation of the Lie derivative on a tuple of vectors. -/
theorem lieDerivFormWithin_apply (ω : E → E [⋀^Fin k]→L[𝕜] F) (v : Fin k → E) :
    lieDerivFormWithin V ω s x v =
      fderivWithin 𝕜 ω s x (V x) v +
        ∑ i, ω x (Function.update v i (fderivWithin 𝕜 V s x (v i))) := by
  rw [lieDerivFormWithin_def, ContinuousAlternatingMap.add_apply,
    fderivCompContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (ω x) ?_
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

/-- Evaluation of the Lie derivative on a tuple of vectors. -/
theorem lieDerivForm_apply (ω : E → E [⋀^Fin k]→L[𝕜] F) (v : Fin k → E) :
    lieDerivForm V ω x v =
      fderiv 𝕜 ω x (V x) v + ∑ i, ω x (Function.update v i (fderiv 𝕜 V x (v i))) := by
  simpa only [lieDerivFormWithin_univ, fderivWithin_univ] using
    lieDerivFormWithin_apply (V := V) (s := univ) (x := x) ω v

/-! ### Linearity in the form -/

@[simp]
theorem lieDerivFormWithin_zero (V : E → E) (s : Set E) (x : E) :
    lieDerivFormWithin V (0 : E → E [⋀^Fin k]→L[𝕜] F) s x = 0 := by
  ext v
  simp [lieDerivFormWithin_apply]

@[simp]
theorem lieDerivForm_zero (V : E → E) : lieDerivForm V (0 : E → E [⋀^Fin k]→L[𝕜] F) = 0 := by
  rw [← lieDerivFormWithin_univ]
  exact funext (lieDerivFormWithin_zero V univ)

/-- The Lie derivative within a set is additive on forms differentiable within the set at the
point, wherever derivatives within the set are unique. -/
theorem lieDerivFormWithin_add {ω η : E → E [⋀^Fin k]→L[𝕜] F} (hs : UniqueDiffWithinAt 𝕜 s x)
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hη : DifferentiableWithinAt 𝕜 η s x) :
    lieDerivFormWithin V (ω + η) s x = lieDerivFormWithin V ω s x + lieDerivFormWithin V η s x := by
  ext v
  simp only [lieDerivFormWithin_apply, fderivWithin_add hs hω hη, Pi.add_apply,
    _root_.add_apply, ContinuousAlternatingMap.add_apply, Finset.sum_add_distrib]
  abel

/-- The Lie derivative is additive on forms differentiable at the point. -/
theorem lieDerivForm_add {ω η : E → E [⋀^Fin k]→L[𝕜] F} (hω : DifferentiableAt 𝕜 ω x)
    (hη : DifferentiableAt 𝕜 η x) :
    lieDerivForm V (ω + η) x = lieDerivForm V ω x + lieDerivForm V η x := by
  simpa only [lieDerivFormWithin_univ] using
    lieDerivFormWithin_add (V := V) uniqueDiffWithinAt_univ hω.differentiableWithinAt
      hη.differentiableWithinAt

/-- The Lie derivative within a set commutes with scalars wherever derivatives within the set
are unique; no differentiability of the form is needed. -/
@[simp]
theorem lieDerivFormWithin_smul (c : 𝕜) (ω : E → E [⋀^Fin k]→L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivFormWithin V (c • ω) s x = c • lieDerivFormWithin V ω s x := by
  ext v
  rw [lieDerivFormWithin_apply, fderivWithin_const_smul_field (f := ω) c hs]
  simp [lieDerivFormWithin_apply, Finset.smul_sum]

@[simp]
theorem lieDerivForm_smul (c : 𝕜) (ω : E → E [⋀^Fin k]→L[𝕜] F) :
    lieDerivForm V (c • ω) = c • lieDerivForm V ω := by
  ext x : 1
  simpa only [lieDerivFormWithin_univ, Pi.smul_apply] using
    lieDerivFormWithin_smul (V := V) (x := x) c ω uniqueDiffWithinAt_univ

/-- **The bracket formula** for the Lie derivative of a form within a set: evaluated on vector
fields `X₀, …, Xₖ₋₁`, it is the derivative of `ω (X₀, …, Xₖ₋₁)` along `V` minus the evaluations
of `ω` with one field `Xᵢ` replaced by the bracket `[V, Xᵢ]`. -/
theorem lieDerivFormWithin_apply_vectorField {ω : E → E [⋀^Fin k]→L[𝕜] F} (X : Fin k → E → E)
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hX : ∀ i, DifferentiableWithinAt 𝕜 (X i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivFormWithin V ω s x (X · x) =
      fderivWithin 𝕜 (fun y ↦ ω y (X · y)) s x (V x) -
        ∑ i, ω x (Function.update (X · x) i (lieBracketWithin 𝕜 V (X i) s x)) := by
  rw [lieDerivFormWithin_apply, fderivWithin_continuousAlternatingMap_apply_apply hω hX hs,
    add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lieBracketWithin, (ω x).map_update_sub, sub_sub_cancel]

/-- **The bracket formula** for the Lie derivative of a form: evaluated on vector fields
`X₀, …, Xₖ₋₁`, it is the derivative of `ω (X₀, …, Xₖ₋₁)` along `V` minus the evaluations of `ω`
with one field `Xᵢ` replaced by the bracket `[V, Xᵢ]`. -/
theorem lieDerivForm_apply_vectorField {ω : E → E [⋀^Fin k]→L[𝕜] F} (X : Fin k → E → E)
    (hω : DifferentiableAt 𝕜 ω x) (hX : ∀ i, DifferentiableAt 𝕜 (X i) x) :
    lieDerivForm V ω x (X · x) =
      fderiv 𝕜 (fun y ↦ ω y (X · y)) x (V x) -
        ∑ i, ω x (Function.update (X · x) i (lieBracket 𝕜 V (X i) x)) := by
  simpa only [lieDerivFormWithin_univ, fderivWithin_univ, lieBracketWithin_univ] using
    lieDerivFormWithin_apply_vectorField (V := V) X hω.differentiableWithinAt
      (fun i ↦ (hX i).differentiableWithinAt) uniqueDiffWithinAt_univ

/-- **Cartan's formula** within a set, `L_V ω = ι_V dω + d (ι_V ω)`, where the interior product
`ι_V` inserts `V` into the first slot. -/
theorem lieDerivFormWithin_eq_curryLeft_extDerivWithin_add {ω : E → E [⋀^Fin (k + 1)]→L[𝕜] F}
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hV : DifferentiableWithinAt 𝕜 V s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivFormWithin V ω s x =
      (extDerivWithin ω s x).curryLeft (V x) +
        extDerivWithin (fun y ↦ (ω y).curryLeft (V y)) s x := by
  let L := (curryLeftLI (𝕜 := 𝕜) (E := E) (F := F) (n := k)).toContinuousLinearMap
  -- Product rule for the bilinear insertion `(ω, v) ↦ ι_v ω`.
  have hd : fderivWithin 𝕜 (fun y ↦ (ω y).curryLeft (V y)) s x =
      (ω x).curryLeft ∘L fderivWithin 𝕜 V s x + L.flip (V x) ∘L fderivWithin 𝕜 ω s x := by
    have hL : HasFDerivWithinAt (fun y ↦ L (ω y)) (L ∘L fderivWithin 𝕜 ω s x) s x :=
      L.hasFDerivAt.comp_hasFDerivWithinAt x hω.hasFDerivWithinAt
    refine ((hL.clm_apply hV.hasFDerivWithinAt).fderivWithin hs).trans ?_
    ext h : 1
    simp [L]
  -- The term differentiating `ω` combines with `ι_V dω` into `Dω(V)` by the constant-field
  -- Cartan identity; the term differentiating `V` is the derivation action of `DV`.
  have hder : alternatizeUncurryFin ((ω x).curryLeft ∘L fderivWithin 𝕜 V s x) =
      (ω x).fderivCompContinuousLinearMap (.id 𝕜 E) (fderivWithin 𝕜 V s x) := by
    rw [fderivCompContinuousLinearMap_eq_alternatizeUncurryFin]
    ext v
    simp [alternatizeUncurryFin_apply]
  rw [extDerivWithin, extDerivWithin, hd, alternatizeUncurryFin_add, hder, lieDerivFormWithin_def,
    ← alternatizeUncurryFin_curryLeft_comp_add_curryLeft (fderivWithin 𝕜 ω s x) (V x)]
  abel

/-- **Cartan's formula** `L_V ω = ι_V dω + d (ι_V ω)`, where the interior product `ι_V` inserts
`V` into the first slot. -/
theorem lieDerivForm_eq_curryLeft_extDeriv_add {ω : E → E [⋀^Fin (k + 1)]→L[𝕜] F}
    (hω : DifferentiableAt 𝕜 ω x) (hV : DifferentiableAt 𝕜 V x) :
    lieDerivForm V ω x =
      (extDeriv ω x).curryLeft (V x) + extDeriv (fun y ↦ (ω y).curryLeft (V y)) x := by
  simpa only [lieDerivFormWithin_univ, extDerivWithin_univ] using
    lieDerivFormWithin_eq_curryLeft_extDerivWithin_add (V := V) hω.differentiableWithinAt
      hV.differentiableWithinAt uniqueDiffWithinAt_univ

/-- Cartan's formula in degree zero, `L_V f = ι_V df`, holds for every function and vector
field. -/
theorem lieDerivFormWithin_eq_curryLeft_extDerivWithin (V : E → E)
    (ω : E → E [⋀^Fin 0]→L[𝕜] F) (s : Set E) (x : E) :
    lieDerivFormWithin V ω s x = (extDerivWithin ω s x).curryLeft (V x) := by
  ext v
  simp [lieDerivFormWithin_apply, extDerivWithin, alternatizeUncurryFin_apply]

/-- Cartan's formula in degree zero, `L_V f = ι_V df`, holds for every function and vector
field. -/
theorem lieDerivForm_eq_curryLeft_extDeriv (V : E → E) (ω : E → E [⋀^Fin 0]→L[𝕜] F) (x : E) :
    lieDerivForm V ω x = (extDeriv ω x).curryLeft (V x) := by
  simpa only [lieDerivFormWithin_univ, extDerivWithin_univ] using
    lieDerivFormWithin_eq_curryLeft_extDerivWithin V ω univ x

end TauCeti
