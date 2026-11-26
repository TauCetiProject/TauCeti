/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.Flow.Locality
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Transverse dilations in a flow box

In a flow box a nonvanishing vector field is a constant field `u` on a real normed space `E`. Fix
a continuous linear functional `ℓ` with `ℓ u = 1`, so that `s = ℓ z` is the time coordinate along
`u` and `z - ℓ z • u` is the transverse coordinate, in `ker ℓ`. For a function `Ψ : ℝ → ℝ`, the
**transverse dilation field**

`V(z) = u + Ψ'(ℓ z) • (z - ℓ z • u)`  (`TauCeti.transverseDilationField u ℓ Ψ`)

keeps the speed `1` in the time coordinate and dilates the transverse coordinate at the rate
`Ψ'(s)`. Its flow is explicit (`TauCeti.flowOf_transverseDilationField`):

`φ_t(z) = z + t • u + (exp (Ψ(ℓ z + t) - Ψ(ℓ z)) - 1) • (z - ℓ z • u)`

(`TauCeti.transverseDilation u ℓ Ψ t z`). The time coordinate advances by `t` and the transverse
coordinate is multiplied by `exp (Ψ(ℓ z + t) - Ψ(ℓ z))`. In particular the field is complete
(`TauCeti.isCompleteVectorField_transverseDilationField`), the axis `ℝ • u` is the trajectory
`s • u ↦ (s + t) • u` of the constant field `u`, and where `Ψ' = 0` the field is `u` itself.

The derivative of the time-`t` map at a point `s • u` of the axis is the identity on `u` and the
dilation by `exp (Ψ(s + t) - Ψ(s))` on `ker ℓ`
(`TauCeti.hasFDerivAt_flowOf_transverseDilationField`). Only the field near the axis segment
matters: any `C¹` field agreeing with the dilation field on an open set containing the segment from
`s • u` to `(s + t) • u`, for instance one cut off away from it, has the same time-`t` map near
`s • u`, with the same derivative (`TauCeti.hasFDerivAt_flowOf_of_eqOn_transverseDilationField`).

For a smooth step `Ψ` from `0` to `1` across `[s₀, s₁]`, the fields of the profiles `s ↦ a * Ψ s`
are the family `u + a • Z` with `Z z = Ψ'(ℓ z) • (z - ℓ z • u)` smooth, vanishing on the axis and
outside the slab `s₀ < ℓ z < s₁`. Their time-`(s₁ - s₀)` maps carry `s₀ • u` to `s₁ • u` with
derivative the dilation by `exp a` on `ker ℓ`
(`TauCeti.exists_contDiff_hasFDerivAt_flowOf_add_smul`, which also identifies `u + a • Z` with the
dilation field of `s ↦ a * Ψ s`, so the locality results above apply to its cut-offs). The family
is affine in `a`, equal to `u` at `a = 0`, and every dilation factor `exp a > 0` occurs.

These fields are the flow-box variations of the proof of the Kupka–Smale theorem: in a chart
straightening a vector field near a point of a closed orbit
(`TauCeti.exists_chart_mfderiv_eq_const`), the orbit runs along the axis, and a variation of this
form, cut off away from the axis, leaves the orbit and its period unchanged while composing the
derivative of the transition across the box with a dilation of the transverse directions.

## Main definitions

* `TauCeti.transverseDilationField u ℓ Ψ`: the field `z ↦ u + Ψ'(ℓ z) • (z - ℓ z • u)`.
* `TauCeti.transverseDilation u ℓ Ψ t`: its explicit time-`t` map.

## Main results

* `TauCeti.flowOf_transverseDilationField`: the maximal flow of the dilation field is
  `transverseDilation`.
* `TauCeti.isCompleteVectorField_transverseDilationField`: the dilation field is complete.
* `TauCeti.hasFDerivAt_transverseDilation_smul`,
  `TauCeti.hasFDerivAt_flowOf_transverseDilationField`: along the axis, the time maps have
  derivative `w ↦ w + (exp (Ψ(s + t) - Ψ(s)) - 1) • (w - ℓ w • u)`.
* `TauCeti.flowOf_eventuallyEq_transverseDilation_of_eqOn`,
  `TauCeti.flowOf_smul_of_eqOn_transverseDilationField`,
  `TauCeti.hasFDerivAt_flowOf_of_eqOn_transverseDilationField`: the same time map, axis trajectory
  and derivative for every `C¹` field agreeing with the dilation field near the axis segment.
* `TauCeti.exists_contDiff_hasFDerivAt_flowOf_add_smul`: a smooth step `Ψ` and a smooth field `Z`
  supported in a slab such that the fields `u + a • Z`, the dilation fields of `s ↦ a * Ψ s`,
  realize every transverse dilation `exp a`.

## References

* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2 (local perturbations of closed orbits in flow boxes).
* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §§3–4
  (the Kupka–Smale theorem).
-/

public section

noncomputable section

open Filter Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Definitions

variable (u : E) (ℓ : E →L[ℝ] ℝ) (Ψ : ℝ → ℝ)

/-- The **transverse dilation field** `z ↦ u + Ψ'(ℓ z) • (z - ℓ z • u)`. When `ℓ u = 1` it moves
the time coordinate `ℓ z` at speed `1` and dilates the transverse coordinate `z - ℓ z • u` at the
rate `Ψ'(ℓ z)`; where `Ψ' = 0` it is the constant field `u`. -/
def transverseDilationField (z : E) : E :=
  u + deriv Ψ (ℓ z) • (z - ℓ z • u)

theorem transverseDilationField_apply (z : E) :
    transverseDilationField u ℓ Ψ z = u + deriv Ψ (ℓ z) • (z - ℓ z • u) :=
  (rfl)

/-- The explicit time-`t` map `z ↦ z + t • u + (exp (Ψ(ℓ z + t) - Ψ(ℓ z)) - 1) • (z - ℓ z • u)`
of the transverse dilation field (`TauCeti.flowOf_transverseDilationField`). -/
def transverseDilation (t : ℝ) (z : E) : E :=
  z + t • u + (Real.exp (Ψ (ℓ z + t) - Ψ (ℓ z)) - 1) • (z - ℓ z • u)

theorem transverseDilation_apply (t : ℝ) (z : E) :
    transverseDilation u ℓ Ψ t z =
      z + t • u + (Real.exp (Ψ (ℓ z + t) - Ψ (ℓ z)) - 1) • (z - ℓ z • u) :=
  (rfl)

end Definitions

variable {u : E} {ℓ : E →L[ℝ] ℝ} {Ψ : ℝ → ℝ}

section Field

/-- Where `Ψ'` vanishes, the transverse dilation field is the constant field `u`. -/
theorem transverseDilationField_eq_of_deriv_eq_zero {z : E} (h : deriv Ψ (ℓ z) = 0) :
    transverseDilationField u ℓ Ψ z = u := by
  simp [transverseDilationField_apply, h]

/-- On the axis `ℝ • u` the transverse dilation field is the constant field `u`. -/
@[simp]
theorem transverseDilationField_smul (hu : ℓ u = 1) (s : ℝ) :
    transverseDilationField u ℓ Ψ (s • u) = u := by
  simp [transverseDilationField_apply, hu]

/-- The fields of the multiples `s ↦ a * Ψ s` of a profile form the family `u + a • (V z - u)`
for the field `V` of `Ψ`, affine in `a`. -/
theorem transverseDilationField_const_mul (a : ℝ) (z : E) :
    transverseDilationField u ℓ (fun s ↦ a * Ψ s) z =
      u + a • (transverseDilationField u ℓ Ψ z - u) := by
  rw [transverseDilationField_apply, transverseDilationField_apply, deriv_const_mul_field,
    mul_smul, add_sub_cancel_left]

/-- A `C^(n+1)` profile gives a `C^n` transverse dilation field. -/
theorem contDiff_transverseDilationField {n : WithTop ℕ∞} (hΨ : ContDiff ℝ (n + 1) Ψ) :
    ContDiff ℝ n (transverseDilationField u ℓ Ψ) :=
  contDiff_const.add ((hΨ.deriv'.comp ℓ.contDiff).smul
    (contDiff_id.sub (ℓ.contDiff.smul contDiff_const)))

/-- A `C^(n+1)` profile gives a `C^n` transverse dilation field, as a section of the tangent
bundle. -/
theorem contMDiff_transverseDilationField {n : WithTop ℕ∞} (hΨ : ContDiff ℝ (n + 1) Ψ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent n
      (fun z : E ↦ (⟨z, (transverseDilationField u ℓ Ψ z : E)⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
  contMDiff_vectorSpace_iff_contDiff (V := transverseDilationField u ℓ Ψ) |>.mpr
    (contDiff_transverseDilationField hΨ)

end Field

section Map

/-- The time-`t` map advances the time coordinate by `t`. -/
@[simp]
theorem apply_transverseDilation (hu : ℓ u = 1) (t : ℝ) (z : E) :
    ℓ (transverseDilation u ℓ Ψ t z) = ℓ z + t := by
  simp [transverseDilation_apply, hu]

/-- The time-`t` map multiplies the transverse coordinate by `exp (Ψ(ℓ z + t) - Ψ(ℓ z))`. -/
theorem transverseDilation_sub_smul (hu : ℓ u = 1) (t : ℝ) (z : E) :
    transverseDilation u ℓ Ψ t z - ℓ (transverseDilation u ℓ Ψ t z) • u =
      Real.exp (Ψ (ℓ z + t) - Ψ (ℓ z)) • (z - ℓ z • u) := by
  rw [apply_transverseDilation hu, transverseDilation_apply, add_smul, sub_smul _ 1, one_smul]
  abel

/-- The time-`t` map translates the axis: `s • u ↦ (s + t) • u`. -/
@[simp]
theorem transverseDilation_smul (hu : ℓ u = 1) (s t : ℝ) :
    transverseDilation u ℓ Ψ t (s • u) = (s + t) • u := by
  simp [transverseDilation_apply, hu, add_smul]

/-- If `Ψ` takes the same value at `ℓ z` and `ℓ z + t`, the time-`t` map translates `z` by
`t • u`, as the flow of the constant field `u` does. -/
theorem transverseDilation_eq_add_smul {t : ℝ} {z : E} (h : Ψ (ℓ z + t) = Ψ (ℓ z)) :
    transverseDilation u ℓ Ψ t z = z + t • u := by
  simp [transverseDilation_apply, h]

/-- At time `0` the map `transverseDilation` is the identity. -/
@[simp]
theorem transverseDilation_zero (z : E) : transverseDilation u ℓ Ψ 0 z = z :=
  transverseDilation_eq_add_smul (by simp) |>.trans (by simp)

/-- Each orbit `t ↦ transverseDilation u ℓ Ψ t z` of a differentiable profile is an integral curve
of the transverse dilation field. -/
theorem isMIntegralCurve_transverseDilation (hu : ℓ u = 1) (hΨ : Differentiable ℝ Ψ) (z : E) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (fun t ↦ transverseDilation u ℓ Ψ t z)
      (transverseDilationField u ℓ Ψ) := by
  intro t
  set c : ℝ → ℝ := fun t ↦ Real.exp (Ψ (ℓ z + t) - Ψ (ℓ z))
  have hc : HasDerivAt c (c t * deriv Ψ (ℓ z + t)) t := by
    have h := (((hΨ _).hasDerivAt.comp t ((hasDerivAt_id t).const_add (ℓ z))).sub_const
      (Ψ (ℓ z))).exp
    simpa [c, mul_comm] using h
  have h : HasDerivAt (fun t ↦ transverseDilation u ℓ Ψ t z)
      (u + (c t * deriv Ψ (ℓ z + t)) • (z - ℓ z • u)) t := by
    have h₁ := ((hasDerivAt_id t).smul_const u).const_add z
    have h₂ := (hc.sub_const 1).smul_const (z - ℓ z • u)
    convert h₁.add h₂ using 1
    · funext x
      simp [transverseDilation_apply, c, add_assoc]
    · simp
  refine (h.congr_deriv ?_).hasFDerivAt.hasMFDerivAt
  beta_reduce
  rw [transverseDilationField_apply, transverseDilation_sub_smul hu, apply_transverseDilation hu,
    smul_smul, mul_comm (deriv Ψ _)]

end Map

section Flow

/-- **The flow of the transverse dilation field** of a `C²` profile is the explicit map
`z ↦ z + t • u + (exp (Ψ(ℓ z + t) - Ψ(ℓ z)) - 1) • (z - ℓ z • u)`. -/
@[simp]
theorem flowOf_transverseDilationField (hu : ℓ u = 1) (hΨ : ContDiff ℝ 2 Ψ) (t : ℝ) (z : E) :
    flowOf (I := 𝓘(ℝ, E)) (transverseDilationField u ℓ Ψ) t z = transverseDilation u ℓ Ψ t z := by
  simpa using flowOf_eq_of_isMIntegralCurve (contMDiff_transverseDilationField hΨ)
    (isMIntegralCurve_transverseDilation hu (hΨ.differentiable two_ne_zero) z) t

/-- The transverse dilation field of a `C²` profile is complete. -/
theorem isCompleteVectorField_transverseDilationField (hu : ℓ u = 1) (hΨ : ContDiff ℝ 2 Ψ) :
    IsCompleteVectorField (I := 𝓘(ℝ, E)) (transverseDilationField u ℓ Ψ) :=
  (isCompleteVectorField_iff_exists_isMIntegralCurve (contMDiff_transverseDilationField hΨ)).mpr
    fun z ↦ ⟨_, transverseDilation_zero z,
      isMIntegralCurve_transverseDilation hu (hΨ.differentiable two_ne_zero) z⟩

/-- **The derivative along the axis.** At a point `s • u` of the axis, the time-`t` map of a
profile differentiable at `s` and `s + t` has derivative
`w ↦ w + (exp (Ψ(s + t) - Ψ(s)) - 1) • (w - ℓ w • u)`: the identity on `u` and the dilation by
`exp (Ψ(s + t) - Ψ(s))` on `ker ℓ`. -/
theorem hasFDerivAt_transverseDilation_smul (hu : ℓ u = 1) {s t : ℝ}
    (hΨs : DifferentiableAt ℝ Ψ s) (hΨst : DifferentiableAt ℝ Ψ (s + t)) :
    HasFDerivAt (transverseDilation u ℓ Ψ t)
      (1 + (Real.exp (Ψ (s + t) - Ψ s) - 1) • (1 - ℓ.smulRight u)) (s • u) := by
  set P : E →L[ℝ] E := 1 - ℓ.smulRight u
  have hP (z : E) : P z = z - ℓ z • u := by simp [P]
  have hPs : P (s • u) = 0 := by simp [hP, hu]
  have hℓ : ℓ (s • u) = s := by simp [hu]
  rw [← hℓ] at hΨs hΨst
  -- The transverse factor `exp (Ψ(ℓ z + t) - Ψ(ℓ z)) - 1` is differentiable in `z`; its product
  -- with the transverse coordinate `P z`, which vanishes on the axis, has derivative `c • P` there.
  have hc : DifferentiableAt ℝ (fun z : E ↦ Real.exp (Ψ (ℓ z + t) - Ψ (ℓ z)) - 1) (s • u) :=
    (((hΨst.comp (s • u) (ℓ.differentiableAt.add_const t)).sub
      (hΨs.comp (s • u) ℓ.differentiableAt)).exp).sub_const 1
  have h := ((hasFDerivAt_id (s • u)).add_const (t • u)).add
    (hc.hasFDerivAt.smul P.hasFDerivAt)
  convert h using 1
  · ext z
    simp [transverseDilation_apply, hP]
  · ext w
    simp [hPs, hu, P]

/-- **The derivative of the flow along the axis.** For a `C²` profile, the time-`t` map of the
flow of the transverse dilation field has derivative
`w ↦ w + (exp (Ψ(s + t) - Ψ(s)) - 1) • (w - ℓ w • u)` at `s • u`. -/
theorem hasFDerivAt_flowOf_transverseDilationField (hu : ℓ u = 1) (hΨ : ContDiff ℝ 2 Ψ)
    (s t : ℝ) :
    HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) (transverseDilationField u ℓ Ψ) t)
      (1 + (Real.exp (Ψ (s + t) - Ψ s) - 1) • (1 - ℓ.smulRight u)) (s • u) := by
  have hφ : flowOf (I := 𝓘(ℝ, E)) (transverseDilationField u ℓ Ψ) t = transverseDilation u ℓ Ψ t :=
    funext (flowOf_transverseDilationField hu hΨ t)
  rw [hφ]
  exact hasFDerivAt_transverseDilation_smul hu (hΨ.differentiable two_ne_zero _)
    (hΨ.differentiable two_ne_zero _)

variable [CompleteSpace E] {W : E → E} {U : Set E}

/-- A `C¹` field agreeing with the transverse dilation field of a `C²` profile on an open set
containing the axis segment from `s • u` to `(s + t) • u` has, near `(t, s • u)`, the same flow as
the transverse dilation field. -/
private theorem eventually_flowOf_eq_transverseDilationField_of_eqOn (hu : ℓ u = 1)
    (hΨ : ContDiff ℝ 2 Ψ)
    (hW : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun z : E ↦ (⟨z, W z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hU : IsOpen U) (hWU : EqOn W (transverseDilationField u ℓ Ψ) U) {s t : ℝ}
    (hsU : ∀ τ ∈ uIcc 0 t, (s + τ) • u ∈ U) :
    ∀ᶠ y in 𝓝 (t, s • u), y ∈ flowDomain (I := 𝓘(ℝ, E)) W ∧
      flowOf (I := 𝓘(ℝ, E)) W y.1 y.2 =
        flowOf (I := 𝓘(ℝ, E)) (transverseDilationField u ℓ Ψ) y.1 y.2 :=
  eventually_flowOf_eq_of_eqOn (contMDiff_transverseDilationField hΨ) hW hU hWU
    ((isCompleteVectorField_transverseDilationField hu hΨ).mem_flowDomain t (s • u))
    fun τ hτ ↦ by
      simpa [flowOf_transverseDilationField hu hΨ, transverseDilation_smul hu] using hsU τ hτ

/-- **Locality.** Let `W` be a `C¹` field agreeing with the transverse dilation field of a `C²`
profile on an open set `U` containing the axis segment from `s • u` to `(s + t) • u`. Then near
`s • u` the time-`t` map of `W` is the explicit map `transverseDilation u ℓ Ψ t`. -/
theorem flowOf_eventuallyEq_transverseDilation_of_eqOn (hu : ℓ u = 1) (hΨ : ContDiff ℝ 2 Ψ)
    (hW : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun z : E ↦ (⟨z, W z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hU : IsOpen U) (hWU : EqOn W (transverseDilationField u ℓ Ψ) U) {s t : ℝ}
    (hsU : ∀ τ ∈ uIcc 0 t, (s + τ) • u ∈ U) :
    flowOf (I := 𝓘(ℝ, E)) W t =ᶠ[𝓝 (s • u)] transverseDilation u ℓ Ψ t := by
  have h := eventually_flowOf_eq_transverseDilationField_of_eqOn hu hΨ hW hU hWU hsU
  filter_upwards [((continuous_const.prodMk continuous_id).tendsto (s • u)).eventually h]
    with z hz
  exact hz.2.trans (flowOf_transverseDilationField hu hΨ t z)

/-- **The axis under locality.** A `C¹` field agreeing with the transverse dilation field of a
`C²` profile on an open set containing the axis segment from `s • u` to `(s + t) • u` has its flow
defined at `(t, s • u)`, and carries `s • u` to `(s + t) • u` at time `t`. -/
theorem flowOf_smul_of_eqOn_transverseDilationField (hu : ℓ u = 1) (hΨ : ContDiff ℝ 2 Ψ)
    (hW : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun z : E ↦ (⟨z, W z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hU : IsOpen U) (hWU : EqOn W (transverseDilationField u ℓ Ψ) U) {s t : ℝ}
    (hsU : ∀ τ ∈ uIcc 0 t, (s + τ) • u ∈ U) :
    (t, s • u) ∈ flowDomain (I := 𝓘(ℝ, E)) W ∧
      flowOf (I := 𝓘(ℝ, E)) W t (s • u) = (s + t) • u := by
  obtain ⟨hdom, heq⟩ :=
    (eventually_flowOf_eq_transverseDilationField_of_eqOn hu hΨ hW hU hWU hsU).self_of_nhds
  exact ⟨hdom, heq.trans (by rw [flowOf_transverseDilationField hu hΨ, transverseDilation_smul hu])⟩

/-- **The derivative under locality.** A `C¹` field agreeing with the transverse dilation field of
a `C²` profile on an open set containing the axis segment from `s • u` to `(s + t) • u` has a
time-`t` map with derivative `w ↦ w + (exp (Ψ(s + t) - Ψ(s)) - 1) • (w - ℓ w • u)` at `s • u`. -/
theorem hasFDerivAt_flowOf_of_eqOn_transverseDilationField (hu : ℓ u = 1)
    (hΨ : ContDiff ℝ 2 Ψ)
    (hW : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun z : E ↦ (⟨z, W z⟩ : TangentBundle 𝓘(ℝ, E) E)))
    (hU : IsOpen U) (hWU : EqOn W (transverseDilationField u ℓ Ψ) U) {s t : ℝ}
    (hsU : ∀ τ ∈ uIcc 0 t, (s + τ) • u ∈ U) :
    HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) W t)
      (1 + (Real.exp (Ψ (s + t) - Ψ s) - 1) • (1 - ℓ.smulRight u)) (s • u) :=
  (hasFDerivAt_transverseDilation_smul hu (hΨ.differentiable two_ne_zero s)
    (hΨ.differentiable two_ne_zero (s + t))).congr_of_eventuallyEq
    (flowOf_eventuallyEq_transverseDilation_of_eqOn hu hΨ hW hU hWU hsU)

end Flow

section Realization

/-- **Realizing a transverse dilation.** For `s₀ < s₁` there are a smooth step `Ψ` from `0` to `1`
across `[s₀, s₁]` and a smooth field `Z`, vanishing outside the slab `s₀ < ℓ z < s₁` and on the axis
`ℝ • u`, such that for every `a` the field `u + a • Z` is the transverse dilation field of the
profile `s ↦ a * Ψ s`, and its time-`(s₁ - s₀)` map carries `s₀ • u` to `s₁ • u` with derivative
`w ↦ w + (exp a - 1) • (w - ℓ w • u)` there: the identity on `u` and the dilation by `exp a` on
`ker ℓ`. -/
theorem exists_contDiff_hasFDerivAt_flowOf_add_smul (hu : ℓ u = 1) {s₀ s₁ : ℝ} (h : s₀ < s₁) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ (∀ r ≤ s₀, Ψ r = 0) ∧ (∀ r, s₁ ≤ r → Ψ r = 1) ∧
      (∀ r ∉ Ioo s₀ s₁, deriv Ψ r = 0) ∧
      ∃ Z : E → E, ContDiff ℝ ∞ Z ∧ (∀ z, ℓ z ∉ Ioo s₀ s₁ → Z z = 0) ∧ (∀ s : ℝ, Z (s • u) = 0) ∧
        ∀ a : ℝ, (fun z ↦ u + a • Z z) = transverseDilationField u ℓ (fun s ↦ a * Ψ s) ∧
          flowOf (I := 𝓘(ℝ, E)) (fun z ↦ u + a • Z z) (s₁ - s₀) (s₀ • u) = s₁ • u ∧
          HasFDerivAt (flowOf (I := 𝓘(ℝ, E)) (fun z ↦ u + a • Z z) (s₁ - s₀))
            (1 + (Real.exp a - 1) • (1 - ℓ.smulRight u)) (s₀ • u) := by
  obtain ⟨Ψ, hΨ, -, hΨ₀, hΨ₁, -, hΨ'⟩ := exists_contDiff_step h
  refine ⟨Ψ, hΨ, hΨ₀, hΨ₁, hΨ', fun z ↦ transverseDilationField u ℓ Ψ z - u,
    (contDiff_transverseDilationField (hΨ.of_le (by simp))).sub contDiff_const,
    fun z hz ↦ by simp [transverseDilationField_eq_of_deriv_eq_zero (hΨ' _ hz)],
    fun s ↦ by simp [hu], fun a ↦ ?_⟩
  have hV : (fun z ↦ u + a • (transverseDilationField u ℓ Ψ z - u)) =
      transverseDilationField u ℓ (fun s ↦ a * Ψ s) :=
    funext fun z ↦ (transverseDilationField_const_mul a z).symm
  have haΨ : ContDiff ℝ 2 fun s ↦ a * Ψ s := contDiff_const.mul (hΨ.of_le (by simp))
  refine ⟨hV, ?_, ?_⟩ <;> rw [hV]
  · simp [hu, haΨ]
  · simpa [hΨ₀ s₀ le_rfl, hΨ₁ s₁ le_rfl] using
      hasFDerivAt_flowOf_transverseDilationField hu haΨ s₀ (s₁ - s₀)

end Realization

end TauCeti
