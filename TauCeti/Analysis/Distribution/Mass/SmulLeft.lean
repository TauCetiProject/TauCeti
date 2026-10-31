/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# Mass of smooth multiples and contractions of currents

Let `T` be a linear map on test functions on an open set `Ω` of a real normed space `E`; with
test forms as tests, `T` is a current. For a smooth function `f : E → ℝ` the smooth multiple
`fT = T ∘ (f ·)` has local mass at most `sup |f| * localMass T` on every set, and for a smooth
one-form `α` the contraction `T ⌞ α = T ∘ (α ∧ ·)` of a current on `(k + 1)`-forms has local mass
at most `(k + 1) sup ‖α‖ * localMass T`, the suprema being taken over the testing set inside
`Ω`. Both operations preserve locally finite mass.

Combined with the Leibniz rule `∂(fT) = f ∂T - T ⌞ df`
(`ContinuousLinearMap.comp_smulLeftCLM_comp_extDerivCLM`) this gives the boundary estimate

`M(∂(fT)) ≤ sup |f| M(∂T) + (k + 1) sup ‖df‖ M(T)`,

together with its local form, and shows that a current `T` such that both `T` and `∂T` have
locally finite mass keeps this property after multiplication by any smooth function, which is
how smooth cutoffs act on locally normal currents. Here the mass is taken with respect to the
operator norm on forms (`Distribution.mass`); the factor `k + 1` comes from the unnormalized
alternatization defining the wedge with a one-form.

## Main declarations

* `Distribution.localMass_comp_smulLeftCLM_le`, `Distribution.mass_comp_smulLeftCLM_le`: the mass
  of a smooth multiple.
* `Distribution.localMass_comp_oneFormWedgeCLM_le`, `Distribution.mass_comp_oneFormWedgeCLM_le`:
  the mass of a contraction with a smooth one-form.
* `Distribution.HasLocallyFiniteMass.comp_smulLeftCLM`,
  `Distribution.HasLocallyFiniteMass.comp_oneFormWedgeCLM`: preservation of locally finite mass.
* `Distribution.localMass_comp_smulLeftCLM_comp_extDerivCLM_le`,
  `Distribution.mass_comp_smulLeftCLM_comp_extDerivCLM_le`: the mass of the boundary of a smooth
  multiple.
* `Distribution.HasLocallyFiniteMass.comp_smulLeftCLM_comp_extDerivCLM`: if `T` and `∂T` have
  locally finite mass, so does `∂(fT)`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the operations `T ⌞ φ` and the mass bounds
  for them).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open TopologicalSpace Set TestFunction
open scoped BoundedContinuousFunction ENNReal Distributions

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V]
  {Ω : Opens E} {n : ℕ∞} {k : ℕ} {U : Set E} {c c' : ℝ≥0∞} {f : E → ℝ} {α : E → E →L[ℝ] ℝ}

section SmulLeft

/-- Multiplication by a smooth function preserves locally finite mass. -/
theorem HasLocallyFiniteMass.comp_smulLeftCLM {T : 𝓓^{n}(Ω, F) → V}
    (hT : HasLocallyFiniteMass T) (hf : ContDiff ℝ n f) :
    HasLocallyFiniteMass (T ∘ smulLeftCLM hf) :=
  hT.comp_of_norm_apply_le
    (fun ψ => (tsupport_smulLeftCLM_subset hf ψ).trans inter_subset_right)
    (continuous_norm.comp hf.continuous) fun ψ x => by simp [norm_smul]

variable [NormedSpace ℝ V] {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) V]
  [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) V]

/-- **Local mass of a smooth multiple.** If `|f| ≤ c` on `U ∩ Ω`, then the local mass of
`fT = T ∘ (f ·)` on `U` is at most `c` times the local mass of `T` on `U`. -/
theorem localMass_comp_smulLeftCLM_le (T : 𝓕) (hf : ContDiff ℝ n f)
    (hfc : ∀ x ∈ U ∩ Ω, ‖f x‖ₑ ≤ c) :
    localMass (T ∘ smulLeftCLM hf) U ≤ c * localMass T U :=
  localMass_comp_le_of_enorm_apply_le T
    (fun ψ => (tsupport_smulLeftCLM_subset hf ψ).trans inter_subset_right)
    (fun ψ x => by simp [enorm_smul]) hfc

/-- **Mass of a smooth multiple.** If `|f| ≤ c` on `Ω`, then `M(fT) ≤ c M(T)`. -/
theorem mass_comp_smulLeftCLM_le (T : 𝓕) (hf : ContDiff ℝ n f) (hfc : ∀ x ∈ Ω, ‖f x‖ₑ ≤ c) :
    mass (T ∘ smulLeftCLM hf) ≤ c * mass T := by
  simpa using localMass_comp_smulLeftCLM_le (U := univ) T hf fun x hx => hfc x hx.2

end SmulLeft

section OneFormWedge

/-- Contraction with a smooth one-form preserves locally finite mass. -/
theorem HasLocallyFiniteMass.comp_oneFormWedgeCLM
    {T : 𝓓^{n}(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) → V} (hT : HasLocallyFiniteMass T)
    (hα : ContDiff ℝ n α) :
    HasLocallyFiniteMass (T ∘ oneFormWedgeCLM (k := k) hα) :=
  hT.comp_of_norm_apply_le
    (fun ω => (tsupport_oneFormWedgeCLM_subset hα ω).trans inter_subset_right)
    (continuous_const.mul (continuous_norm.comp hα.continuous))
    (norm_oneFormWedgeCLM_apply_le hα)

variable [NormedSpace ℝ V] {𝓕 : Type*}
  [FunLike 𝓕 𝓓^{n}(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) V]
  [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) V]

/-- **Local mass of a contraction.** If `‖α‖ ≤ c` on `U ∩ Ω`, then the local mass of
`T ⌞ α = T ∘ (α ∧ ·)` on `U` is at most `(k + 1) c` times the local mass of `T` on `U`. -/
theorem localMass_comp_oneFormWedgeCLM_le (T : 𝓕) (hα : ContDiff ℝ n α)
    (hαc : ∀ x ∈ U ∩ Ω, ‖α x‖ₑ ≤ c) :
    localMass (T ∘ oneFormWedgeCLM (k := k) hα) U ≤ (k + 1) * c * localMass T U :=
  localMass_comp_le_of_enorm_apply_le T
    (fun ω => (tsupport_oneFormWedgeCLM_subset hα ω).trans inter_subset_right)
    (enorm_oneFormWedgeCLM_apply_le hα) fun x hx => by gcongr; exact hαc x hx

/-- **Mass of a contraction.** If `‖α‖ ≤ c` on `Ω`, then `M(T ⌞ α) ≤ (k + 1) c M(T)`. -/
theorem mass_comp_oneFormWedgeCLM_le (T : 𝓕) (hα : ContDiff ℝ n α)
    (hαc : ∀ x ∈ Ω, ‖α x‖ₑ ≤ c) :
    mass (T ∘ oneFormWedgeCLM (k := k) hα) ≤ (k + 1) * c * mass T := by
  simpa using localMass_comp_oneFormWedgeCLM_le (U := univ) T hα fun x hx => hαc x hx.2

end OneFormWedge

section Boundary

variable [NormedSpace ℝ V] (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V)
  (hf : ContDiff ℝ (⊤ : ℕ∞) f)

/-- **Local mass of the boundary of a smooth multiple.** If `|f| ≤ c` and `‖df‖ ≤ c'` on
`U ∩ Ω`, then the local mass of `∂(fT)` on `U` is at most
`c * localMass (∂T) U + (k + 1) c' * localMass T U`. -/
theorem localMass_comp_smulLeftCLM_comp_extDerivCLM_le (hfc : ∀ x ∈ U ∩ Ω, ‖f x‖ₑ ≤ c)
    (hdfc : ∀ x ∈ U ∩ Ω, ‖fderiv ℝ f x‖ₑ ≤ c') :
    localMass ((T ∘L smulLeftCLM hf) ∘L extDerivCLM) U ≤
      c * localMass (T ∘L extDerivCLM) U + (k + 1) * c' * localMass T U := by
  rw [ContinuousLinearMap.comp_smulLeftCLM_comp_extDerivCLM, FunLike.coe_sub]
  refine localMass_sub_le.trans (add_le_add ?_ ?_)
  · exact localMass_comp_smulLeftCLM_le (T ∘L extDerivCLM) hf hfc
  · exact localMass_comp_oneFormWedgeCLM_le T _ hdfc

/-- **Mass of the boundary of a smooth multiple.** If `|f| ≤ c` and `‖df‖ ≤ c'` on `Ω`, then
`M(∂(fT)) ≤ c M(∂T) + (k + 1) c' M(T)`. -/
theorem mass_comp_smulLeftCLM_comp_extDerivCLM_le (hfc : ∀ x ∈ Ω, ‖f x‖ₑ ≤ c)
    (hdfc : ∀ x ∈ Ω, ‖fderiv ℝ f x‖ₑ ≤ c') :
    mass ((T ∘L smulLeftCLM hf) ∘L extDerivCLM) ≤
      c * mass (T ∘L extDerivCLM) + (k + 1) * c' * mass T := by
  simpa using localMass_comp_smulLeftCLM_comp_extDerivCLM_le (U := univ) T hf
    (fun x hx => hfc x hx.2) fun x hx => hdfc x hx.2

variable {T} in
/-- If a current `T` and its boundary `∂T` have locally finite mass, then so does the boundary
`∂(fT)` of any smooth multiple of `T`. -/
theorem HasLocallyFiniteMass.comp_smulLeftCLM_comp_extDerivCLM (hT : HasLocallyFiniteMass T)
    (hdT : HasLocallyFiniteMass (T ∘L extDerivCLM)) :
    HasLocallyFiniteMass ((T ∘L smulLeftCLM hf) ∘L extDerivCLM) := by
  rw [ContinuousLinearMap.comp_smulLeftCLM_comp_extDerivCLM, FunLike.coe_sub]
  exact (hdT.comp_smulLeftCLM hf).sub (hT.comp_oneFormWedgeCLM _)

end Boundary

end Distribution
