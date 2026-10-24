/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives of continuous-linear-map applications

This file records a zero-value rule for differentiating the pointwise application of a varying
continuous linear map. At a zero of the vector-valued argument, the variation of the operator
contributes nothing to the derivative, so the operator-valued map need only be continuous. It also
records the derivative of the application of a varying continuous linear map to a fixed vector,
the product rule for a varying bilinear map applied to two varying vectors, and the fact that
the derivative of a field of symmetric bilinear maps takes symmetric values. Finally, a family of
continuous linear maps out of a finite-dimensional space is differentiable, or has a given
derivative in a scalar variable, within a set or at a point, exactly when each of its evaluations
does; this is how derivatives of families of linear and bilinear maps are tested on vectors.

## Main declarations

* `HasFDerivWithinAt.clm_apply_of_eq_zero`: the derivative of `y ↦ c y (u y)` at a zero of
  `u`, assuming only continuity of `c`.
* `TauCeti.fderiv_clm_apply_const_apply`: the derivative of `y ↦ c y v` in the direction `w` is
  `Dc(w) v`.
* `TauCeti.fderiv_bilin_apply`: the product rule for `y ↦ c y (A y) (B y)`.
* `TauCeti.fderiv_apply_apply_comm`: the derivative of a field of bilinear maps that is symmetric
  near a point takes symmetric values there.
* `TauCeti.differentiableWithinAt_clm_apply`: a family of continuous linear maps out of a
  finite-dimensional space is differentiable within a set exactly when each evaluation is;
  `TauCeti.differentiableAt_clm_apply` is the pointwise form.
* `TauCeti.hasDerivWithinAt_clm_apply`: such a family of a scalar variable has derivative `c'`
  within a set, at a point of unique differentiability, exactly when each evaluation at `v` has
  derivative `c' v`; `TauCeti.hasDerivAt_clm_apply` is the pointwise form.
* `TauCeti.differentiableWithinAt_clm_apply₂`, `TauCeti.hasDerivWithinAt_clm_apply₂` and their
  pointwise forms: the same criteria for families of bilinear maps, tested on pairs of vectors.
-/

public section

open Asymptotics Filter Set
open scoped Topology

variable {𝕜 E F G F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

namespace TauCeti

/-- At a zero of `u`, the variation of `c` is multiplied by `u y = O(y - z)`, so it contributes
nothing to the derivative. -/
theorem _root_.HasFDerivWithinAt.clm_apply_of_eq_zero {c : E → F →L[𝕜] F'} {u : E → F}
    {u' : E →L[𝕜] F} {s : Set E} {z : E}
    (hc : ContinuousWithinAt c s z) (hu : HasFDerivWithinAt u u' s z) (hu0 : u z = 0) :
    HasFDerivWithinAt (fun y ↦ c y (u y)) ((c z).comp u') s z := by
  have hrem : HasFDerivWithinAt (fun y ↦ (c y - c z) (u y)) (0 : E →L[𝕜] F') s z := by
    refine .of_isLittleO ?_
    simp only [hu0, map_zero, sub_self, sub_zero, zero_apply]
    refine (isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := F) (F := F')).isBigO_comp.trans_isLittleO ?_
    have hc' : (fun y ↦ ‖c y - c z‖) =o[𝓝[s] z] (fun _ ↦ (1 : ℝ)) :=
      ((isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 hc)).norm_left
    have hu' : (fun y ↦ ‖u y‖) =O[𝓝[s] z] (fun y ↦ ‖y - z‖) := by
      simpa only [hu0, sub_zero] using hu.isBigO_sub.norm_norm
    exact isLittleO_norm_right.1 (by simpa only [one_mul] using hc'.mul_isBigO hu')
  convert ((c z).hasFDerivAt.comp_hasFDerivWithinAt z hu).add hrem using 1
  · funext y
    simp
  · simp

/-- Differentiating `y ↦ c y v` for a fixed vector `v` in the direction `w` gives the derivative
of `c` in the direction `w`, applied to `v`. -/
theorem fderiv_clm_apply_const_apply {c : E → F →L[𝕜] F'} {x : E} (hc : DifferentiableAt 𝕜 c x)
    (v : F) (w : E) :
    fderiv 𝕜 (fun y ↦ c y v) x w = fderiv 𝕜 c x w v := by
  rw [fderiv_clm_apply hc (differentiableAt_const v)]
  simp

/-- The derivative of `y ↦ c y (A y) (B y)` for a field `c` of bilinear maps: the product rule. -/
theorem fderiv_bilin_apply {c : E → F →L[𝕜] G →L[𝕜] F'} {A : E → F} {B : E → G} {x : E}
    (hc : DifferentiableAt 𝕜 c x) (hA : DifferentiableAt 𝕜 A x) (hB : DifferentiableAt 𝕜 B x)
    (u : E) :
    fderiv 𝕜 (fun y ↦ c y (A y) (B y)) x u =
      fderiv 𝕜 c x u (A x) (B x) + c x (fderiv 𝕜 A x u) (B x) + c x (A x) (fderiv 𝕜 B x u) := by
  rw [((hc.hasFDerivAt.clm_apply hA.hasFDerivAt).clm_apply hB.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

/-- If a field `c` of bilinear maps takes symmetric values near `x`, then so does each directional
derivative of `c` at `x`. -/
theorem fderiv_apply_apply_comm {c : E → F →L[𝕜] F →L[𝕜] G} {x : E}
    (hc : ∀ᶠ y in 𝓝 x, ∀ v w, c y v w = c y w v) (u : E) (v w : F) :
    fderiv 𝕜 c x u v w = fderiv 𝕜 c x u w v := by
  by_cases hd : DifferentiableAt 𝕜 c x
  · -- Both sides are derivatives of functions of `y` which agree near `x`.
    have happ (a b : F) : fderiv 𝕜 (fun y ↦ c y a b) x u = fderiv 𝕜 c x u a b := by
      rw [fderiv_clm_apply_const_apply (hd.clm_apply (differentiableAt_const a)),
        fderiv_clm_apply_const_apply hd]
    have heq : (fun y ↦ c y v w) =ᶠ[𝓝 x] fun y ↦ c y w v := hc.mono fun y hy ↦ hy v w
    rw [← happ, ← happ, heq.fderiv_eq]
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- A family of continuous linear maps out of a finite-dimensional space is differentiable within
a set exactly when its evaluation at each fixed vector is differentiable within that set. -/
theorem differentiableWithinAt_clm_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    {c : E → F →L[𝕜] G} {s : Set E} {x : E} :
    DifferentiableWithinAt 𝕜 c s x ↔ ∀ v, DifferentiableWithinAt 𝕜 (fun y ↦ c y v) s x := by
  refine ⟨fun h v ↦ h.clm_apply (differentiableWithinAt_const v), fun h ↦ ?_⟩
  -- Read `c` through the evaluations at the vectors of a basis of `F`, as in the proof of
  -- Mathlib's `contDiffWithinAt_clm_apply`.
  let d := Module.finrank 𝕜 F
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := (Module.finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[𝕜] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
  have he : DifferentiableWithinAt 𝕜 (fun y ↦ e₂ (c y)) s x :=
    differentiableWithinAt_pi.mpr fun _ ↦ h _
  simpa [Function.comp_def] using e₂.symm.differentiableAt.comp_differentiableWithinAt x he

/-- A family of continuous linear maps out of a finite-dimensional space is differentiable
exactly when its evaluation at each fixed vector is differentiable. -/
theorem differentiableAt_clm_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    {c : E → F →L[𝕜] G} {x : E} :
    DifferentiableAt 𝕜 c x ↔ ∀ v, DifferentiableAt 𝕜 (fun y ↦ c y v) x := by
  simpa only [differentiableWithinAt_univ] using
    differentiableWithinAt_clm_apply (c := c) (s := univ) (x := x)

/-- A family of continuous linear maps out of a finite-dimensional space, depending on a scalar,
has derivative `c'` within a set at a point of unique differentiability exactly when its
evaluation at each fixed vector `v` has derivative `c' v` within that set. -/
theorem hasDerivWithinAt_clm_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    {c : 𝕜 → F →L[𝕜] G} {c' : F →L[𝕜] G} {s : Set 𝕜} {t : 𝕜} (hs : UniqueDiffWithinAt 𝕜 s t) :
    HasDerivWithinAt c c' s t ↔ ∀ v, HasDerivWithinAt (fun r ↦ c r v) (c' v) s t := by
  refine ⟨fun h v ↦ by simpa using h.clm_apply (hasDerivWithinAt_const t s v), fun h ↦ ?_⟩
  have hd := (differentiableWithinAt_clm_apply.mpr fun v ↦
    (h v).differentiableWithinAt).hasDerivWithinAt
  convert hd using 1
  ext v
  exact hs.eq_deriv s (h v) (by simpa using hd.clm_apply (hasDerivWithinAt_const t s v))

/-- A family of continuous linear maps out of a finite-dimensional space, depending on a scalar,
has derivative `c'` exactly when its evaluation at each fixed vector `v` has derivative `c' v`. -/
theorem hasDerivAt_clm_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] {c : 𝕜 → F →L[𝕜] G}
    {c' : F →L[𝕜] G} {t : 𝕜} :
    HasDerivAt c c' t ↔ ∀ v, HasDerivAt (fun s ↦ c s v) (c' v) t := by
  simpa only [hasDerivWithinAt_univ] using
    hasDerivWithinAt_clm_apply (c := c) (c' := c') uniqueDiffWithinAt_univ

/-- A family of continuous bilinear maps on finite-dimensional spaces is differentiable within a
set exactly when its evaluation at each fixed pair of vectors is differentiable within that set. -/
theorem differentiableWithinAt_clm_apply₂ [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 F'] {c : E → F →L[𝕜] F' →L[𝕜] G} {s : Set E} {x : E} :
    DifferentiableWithinAt 𝕜 c s x ↔ ∀ v w, DifferentiableWithinAt 𝕜 (fun y ↦ c y v w) s x :=
  differentiableWithinAt_clm_apply.trans
    (forall_congr' fun _ ↦ differentiableWithinAt_clm_apply)

/-- A family of continuous bilinear maps on finite-dimensional spaces is differentiable exactly
when its evaluation at each fixed pair of vectors is differentiable. -/
theorem differentiableAt_clm_apply₂ [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 F'] {c : E → F →L[𝕜] F' →L[𝕜] G} {x : E} :
    DifferentiableAt 𝕜 c x ↔ ∀ v w, DifferentiableAt 𝕜 (fun y ↦ c y v w) x :=
  differentiableAt_clm_apply.trans (forall_congr' fun _ ↦ differentiableAt_clm_apply)

/-- A family of continuous bilinear maps on finite-dimensional spaces, depending on a scalar, has
derivative `c'` within a set at a point of unique differentiability exactly when its evaluation
at each fixed pair `(v, w)` has derivative `c' v w` within that set. -/
theorem hasDerivWithinAt_clm_apply₂ [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 F'] {c : 𝕜 → F →L[𝕜] F' →L[𝕜] G} {c' : F →L[𝕜] F' →L[𝕜] G}
    {s : Set 𝕜} {t : 𝕜} (hs : UniqueDiffWithinAt 𝕜 s t) :
    HasDerivWithinAt c c' s t ↔ ∀ v w, HasDerivWithinAt (fun r ↦ c r v w) (c' v w) s t :=
  (hasDerivWithinAt_clm_apply hs).trans (forall_congr' fun _ ↦ hasDerivWithinAt_clm_apply hs)

/-- A family of continuous bilinear maps on finite-dimensional spaces, depending on a scalar, has
derivative `c'` exactly when its evaluation at each fixed pair `(v, w)` has derivative
`c' v w`. -/
theorem hasDerivAt_clm_apply₂ [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 F'] {c : 𝕜 → F →L[𝕜] F' →L[𝕜] G} {c' : F →L[𝕜] F' →L[𝕜] G} {t : 𝕜} :
    HasDerivAt c c' t ↔ ∀ v w, HasDerivAt (fun s ↦ c s v w) (c' v w) t :=
  hasDerivAt_clm_apply.trans (forall_congr' fun _ ↦ hasDerivAt_clm_apply)

end TauCeti

end
