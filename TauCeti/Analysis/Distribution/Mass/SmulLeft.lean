/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Measure
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
public import Mathlib.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.Mass.Support
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin

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

When `f` vanishes on the support of such a current, `fT` and `f ∂T` vanish, so the Leibniz rule
gives `T ⌞ df = 0`. In particular a current such that `T` and `∂T` have locally finite mass,
supported in a hyperplane, is tangent to that hyperplane.

## Main declarations

* `Distribution.localMass_comp_smulLeftCLM_le`, `Distribution.mass_comp_smulLeftCLM_le`: the mass
  of a smooth multiple.
* `Distribution.localMass_comp_oneFormWedgeCLM_le`, `Distribution.mass_comp_oneFormWedgeCLM_le`:
  the mass of a contraction with a smooth one-form.
* `Distribution.HasLocallyFiniteMass.comp_smulLeftCLM`,
  `Distribution.HasLocallyFiniteMass.comp_oneFormWedgeCLM`: preservation of locally finite mass.
* `Distribution.mass_comp_oneFormWedgeCLM_le_lintegral`: the sharper bound
  `M(T ⌞ α) ≤ (k + 1) ∫ ‖α‖ d‖T‖` against the mass measure of `T`.
* `Distribution.localMass_comp_smulLeftCLM_comp_extDerivCLM_le`,
  `Distribution.mass_comp_smulLeftCLM_comp_extDerivCLM_le`: the mass of the boundary of a smooth
  multiple.
* `Distribution.HasLocallyFiniteMass.comp_smulLeftCLM_comp_extDerivCLM`: if `T` and `∂T` have
  locally finite mass, so does `∂(fT)`.
* `Distribution.HasLocallyFiniteMass.comp_oneFormWedgeCLM_eq_zero`: if `T` and `∂T` have locally
  finite mass and `f` vanishes on the support of `T`, then `T ⌞ df = 0`.
* `Distribution.HasLocallyFiniteMass.map_postcompCLM_compContinuousLinearMapCLM_id_sub_smulRight`:
  such a current supported in a hyperplane `{l = c}` is unchanged by pulling its test forms back
  along `id - l ⊗ e`; it is tangent to the hyperplane.

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
    (fun ψ x => by simp [eNorm_smul]) hfc

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

section MassMeasure

open MeasureTheory

variable [MeasurableSpace E] [BorelSpace E] {𝓕 : Type*}
  [FunLike 𝓕 𝓓^{n}(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) ℝ]
  [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) ℝ]

/-- **Mass of a contraction against the mass measure.** For `T` of locally finite mass,
`M(T ⌞ α) ≤ (k + 1) ∫ ‖α‖ d‖T‖`. Unlike `Distribution.mass_comp_oneFormWedgeCLM_le`, the size of
`α` is weighted by the mass measure `‖T‖` instead of bounded by its supremum. -/
theorem mass_comp_oneFormWedgeCLM_le_lintegral {T : 𝓕} (hT : HasLocallyFiniteMass T)
    (hα : ContDiff ℝ n α) :
    mass (T ∘ oneFormWedgeCLM (k := k) hα) ≤ (k + 1) * ∫⁻ x, ‖α x‖ₑ ∂massMeasure T := by
  refine mass_le_iff.2 fun ω hω => (enorm_apply_le_lintegral_massMeasure hT _).trans ?_
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x => (enorm_oneFormWedgeCLM_apply_le hα ω x).trans ?_
  have hωx : ‖ω x‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 (hω x)
  calc (k + 1 : ℝ≥0∞) * ‖α x‖ₑ * ‖ω x‖ₑ ≤ (k + 1) * ‖α x‖ₑ * 1 := by gcongr
    _ = (k + 1) * ‖α x‖ₑ := mul_one _

end MassMeasure

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

section Support

variable {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}

/-- **The contraction with the differential of a function vanishing on the support.** If a
current `T` and its boundary `∂T` have locally finite mass and the smooth function `f` vanishes on
the support of `T` in `Ω`, then `T ⌞ df = 0`. Indeed `fT = 0` and `f ∂T = 0`, since a current of
locally finite mass only sees the values of a test form on its support, so the Leibniz rule
`∂(fT) = f ∂T - T ⌞ df` leaves `T ⌞ df = 0`. -/
theorem HasLocallyFiniteMass.comp_oneFormWedgeCLM_eq_zero (hT : HasLocallyFiniteMass T)
    (hdT : HasLocallyFiniteMass (T ∘L extDerivCLM)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : EqOn f 0 ((Ω : Set E) ∩ dsupport T)) :
    T ∘L oneFormWedgeCLM (k := k) (contDiff_infty_iff_fderiv.1 hf).2 = 0 := by
  -- `f ω` vanishes on the support of every functional supported in that of `T`.
  have hfω {m : ℕ} {S : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) → ℝ} (hS : dsupport S ⊆ dsupport T)
      (ω : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)) :
      EqOn (smulLeftCLM hf ω) (0 : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)) ((Ω : Set E) ∩ dsupport S) :=
    fun x hx ↦ by simp [hf0 ⟨hx.1, hS hx.2⟩]
  have hfT : T ∘L smulLeftCLM hf = 0 := by
    ext ω
    simpa using hT.map_eq_map_of_eqOn_dsupport (hfω subset_rfl ω)
  have hfdT : (T ∘L extDerivCLM) ∘L smulLeftCLM hf = 0 := by
    ext ω
    simpa using hdT.map_eq_map_of_eqOn_dsupport
      (hfω (dsupport_comp_extDerivCLM_subset (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) → ℝ)) ω)
  have h := ContinuousLinearMap.comp_smulLeftCLM_comp_extDerivCLM T hf
  rw [hfT, hfdT, ContinuousLinearMap.zero_comp, zero_sub, eq_comm, neg_eq_zero] at h
  exact h

/-- **Normal currents in a hyperplane are tangent to it.** Let `T` be a current such that `T` and
`∂T` have locally finite mass, supported in `Ω` in the affine hyperplane `{l = c}`. Then `T` does
not change when its test forms are pulled back by the linear map `P = id - l ⊗ e`, for any vector
`e`. When `l e = 1`, `P` is the projection onto `ker l` along `e`, so `T` only sees the restriction
of test forms to the directions of the hyperplane. -/
theorem HasLocallyFiniteMass.map_postcompCLM_compContinuousLinearMapCLM_id_sub_smulRight
    (hT : HasLocallyFiniteMass T) (hdT : HasLocallyFiniteMass (T ∘L extDerivCLM))
    {l : StrongDual ℝ E} {c : ℝ} (hTl : (Ω : Set E) ∩ dsupport T ⊆ {x | l x = c}) (e : E)
    (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    T (postcompCLM
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (.id ℝ E - l.smulRight e)) ω) =
      T ω := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) fun x ↦ l x - c := l.contDiff.sub contDiff_const
  have hdf (x : E) : fderiv ℝ (fun x ↦ l x - c) x = l := by
    simpa using (l.hasFDerivAt.sub_const c).fderiv
  have hzero := hT.comp_oneFormWedgeCLM_eq_zero hdT hf fun x hx ↦ sub_eq_zero.2 (hTl hx)
  -- Pointwise, `ω - ω ∘ P = l ∧ ((ι_e ω) ∘ P)`.
  have hsplit : ω - postcompCLM
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (.id ℝ E - l.smulRight e)) ω =
      oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hf).2 (postcompCLM
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (.id ℝ E - l.smulRight e) ∘L
          ContinuousAlternatingMap.curryLeftFlipL e) ω) := by
    ext x : 1
    simp [hdf, ContinuousAlternatingMap.curryLeftFlipL_apply_apply,
      ← ContinuousAlternatingMap.sub_compContinuousLinearMap_id_sub_smulRight]
  rw [eq_comm, ← sub_eq_zero, ← map_sub, hsplit, ← ContinuousLinearMap.comp_apply, hzero,
    zero_apply]

end Support

end Distribution
