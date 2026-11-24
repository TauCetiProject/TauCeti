/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.LeftCapping
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Normalization.Continuation
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# Normalizing the Hamiltonians of the capping families

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time:
`H(t, x)` and `H(t, x) + d(t)` generate the same flow and give the same Floer equation. This file
shows how the energy identities of the two capping families, along which the pair-of-pants
product is shown to be unital, absorb such a change of normalization of their three Hamiltonians.
It is the counterpart for these families of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Normalization.Basic`, which treats the pair of pants.

* **The capped cylinder** `TauCeti.Floer.cappedCylinderComponent Hb L`: the negative PSS plane of
  `Hb 1` plumbed into the input end at `1` of the pair of pants, read on the standard cylinder,
  with the input `Hb 0` at `s = +∞` and the output `Hb ∞` at `s = -∞`.
* **The input-exchange family capped at `0`**
  `TauCeti.Floer.cappedExchangePerturbation H L c`, `0 ≤ c ≤ 1`: the negative PSS plane of `H 0`
  plumbed into the input end at `0`, with the input `H 1` and the output `H ∞` recentred at `c`.

Both data are additive in the Hamiltonians, so normalizing by `d` adds the datum of the
target-independent Hamiltonians `d_q`, which has no Hamiltonian vector field
(`TauCeti.Floer.cappedCylinderComponent_add_const`,
`TauCeti.Floer.cappedExchangePerturbation_add_const`). Consequently, for a manifold target:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density are
  unchanged (`TauCeti.SmoothTwoForm.perturbedMFDeriv_cappedCylinderComponent_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_cappedExchangePerturbation_add_const` and their
  companions);
* the curvature changes pointwise by the curvature of the datum of the `d_q`
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_cappedCylinderComponent_add_const`,
  `TauCeti.SmoothTwoForm.hamiltonianCurvature_cappedExchangePerturbation_add_const`), which does
  not depend on the target point
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_cappedCylinderComponent_const_target`,
  `TauCeti.SmoothTwoForm.hamiltonianCurvature_cappedExchangePerturbation_const_target`);
* the curvature of the datum of the `d_q` integrates to `∫₀¹ d_in - ∫₀¹ d_∞` over the domain,
  for the remaining input `in` (`0` on the capped cylinder, `1` on the family capped at `0`): over
  every rectangle `[a, b] × [0, 1]` with `a ≤ -3` and `2 ≤ b` and over the whole strip of the
  capped cylinder
  (`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_cappedCylinderComponent_const`,
  `TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_cappedCylinderComponent_const_univ_prod`),
  and over `S = ℂ ∖ {0, 1}` for the family capped at `0`
  (`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_cappedExchangePerturbation_const`).

So along every map whose curvature is integrable, the integrated curvature changes by
`∫₀¹ d_in - ∫₀¹ d_∞`
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_cappedCylinderComponent_add_const`,
`setIntegral_hamiltonianCurvature_cappedCylinderComponent_add_const_univ_prod` and
`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_cappedExchangePerturbation_add_const`).
This is exactly the change of the Hamiltonian terms at the two remaining ends in the energy
identities `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent`
and `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedExchangePerturbation`, so the
two changes cancel. The normalization of the capping Hamiltonian changes neither side: the capped
puncture is not an end of the domain and carries no Hamiltonian term, and the datum of the plane
vanishes on its pole disc.

The integral of the curvature of a target-independent datum does not depend on the target, so it
is computed once, by the energy identity along a constant map into `ℂ`, in whose energy identity
only the curvature and the end terms survive. For the capped cylinder the symplectic vector space
statements (`TauCeti.SymplecticForm.setIntegral_hamiltonianCurvature_cappedCylinderComponent_const`
and its strip version) are proved first.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
-/

public section

open Set Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold

namespace TauCeti

namespace Floer

variable {M N : Type*}

/-- The Hamiltonian family which is a target-independent `e` on the end `∞` and zero elsewhere
is the target-independent family of the scalar functions `Pi.single ∞ e`. -/
private theorem single_inf_const_target (e : ℝ → ℝ) :
    (Pi.single inf (fun t (_ : M) ↦ e t) : Puncture → ℝ → M → ℝ) =
      fun q t _ ↦ (Pi.single inf e : Puncture → ℝ → ℝ) q t := by
  funext q
  exact (Pi.apply_single (fun _ (e : ℝ → ℝ) t (_ : M) ↦ e t) (fun _ ↦ rfl) inf e q).symm

/-- **Normalizing the Hamiltonians of the capped cylinder.** Adding functions `d_r` of time to the
Hamiltonians `Hb r` adds the capped datum of the target-independent Hamiltonians `d_r`. -/
theorem cappedCylinderComponent_add_const (Hb : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ)
    (L : ℝ) (v : ℂ) (z : ℝ × ℝ) (x : M) :
    cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L v z x =
      cappedCylinderComponent Hb L v z x +
        cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L v z x := by
  have h : (fun r t y ↦ Hb r t y + d r t) = Hb + fun r t (_ : M) ↦ d r t := by
    funext r t y
    simp
  rw [h]
  simp only [cappedCylinderComponent_def, Pi.add_apply, Pi.single_add, plumbedPerturbation_add,
    add_apply]

/-- The capped datum on the cylinder of target-independent Hamiltonians does not depend on the
target: its values at points of `M` and of `N` agree. -/
theorem cappedCylinderComponent_const_target (d : Puncture → ℝ → ℝ) (L : ℝ) (v : ℂ)
    (z : ℝ × ℝ) (x : M) (y : N) :
    cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L v z x =
      cappedCylinderComponent (fun r t (_ : N) ↦ d r t) L v z y := by
  simp only [cappedCylinderComponent_def, single_inf_const_target,
    plumbedPerturbation_const_target _ _ _ _ _ x y]

/-- The components of the normalized capped datum are those of the original one plus those of the
capped datum of the normalizing functions, evaluated at any target point `y`. -/
private theorem cappedCylinderComponent_add_const_fun (Hb : Puncture → ℝ → M → ℝ)
    (d : Puncture → ℝ → ℝ) (L : ℝ) (v : ℂ) (y : M) :
    cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L v =
      fun z x ↦ cappedCylinderComponent Hb L v z x +
        cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L v z y := by
  funext z x
  rw [cappedCylinderComponent_add_const, cappedCylinderComponent_const_target d L v z x y]

/-- The components of the capped datum of target-independent Hamiltonians, as functions of the
cylinder point alone. -/
private theorem cappedCylinderComponent_const_target_fun (d : Puncture → ℝ → ℝ) (L : ℝ) (v : ℂ)
    (y : M) :
    cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L v =
      fun z _ ↦ cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L v z y := by
  funext z x
  exact cappedCylinderComponent_const_target d L v z x y

/-- Replacing the Hamiltonian at `∞` of target-independent Hamiltonians by `0` gives the
target-independent Hamiltonians `update d ∞ 0`. -/
private theorem update_inf_zero_const_target (d : Puncture → ℝ → ℝ) :
    (update (fun q t (_ : M) ↦ d q t) inf 0 : Puncture → ℝ → M → ℝ) =
      fun q t _ ↦ (update d inf 0 : Puncture → ℝ → ℝ) q t := by
  funext q
  exact (apply_update (fun _ (e : ℝ → ℝ) t (_ : M) ↦ e t) d inf 0 q).symm

/-- **Normalizing the Hamiltonians of the input-exchange family capped at `0`.** Adding functions
`d_q` of time to the Hamiltonians `H_q` adds the member of the family of the target-independent
Hamiltonians `d_q`. -/
theorem cappedExchangePerturbation_add_const (H : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ)
    (L c : ℝ) (w : ℂ) (x : M) :
    cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c w x =
      cappedExchangePerturbation H L c w x +
        cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c w x := by
  have h : (fun q t y ↦ H q t y + d q t) = H + fun q t (_ : M) ↦ d q t := by
    funext q t y
    simp
  -- Replacing the Hamiltonian at `∞` by `0` is additive, since `0 = 0 + 0`.
  have hu : update (H + fun q t (_ : M) ↦ d q t) inf 0 =
      update H inf 0 + update (fun q t (_ : M) ↦ d q t) inf 0 := by
    rw [← update_add, add_zero]
  rw [h]
  simp only [cappedExchangePerturbation_def, hu, Pi.add_apply, Pi.single_add,
    plumbedPerturbation_add, negativePlanePerturbation_def, mul_add, add_smul]
  abel

/-- The input-exchange family capped at `0` of target-independent Hamiltonians does not depend on
the target: its values at points of `M` and of `N` agree. -/
theorem cappedExchangePerturbation_const_target (d : Puncture → ℝ → ℝ) (L c : ℝ) (w : ℂ) (x : M)
    (y : N) :
    cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c w x =
      cappedExchangePerturbation (fun q t (_ : N) ↦ d q t) L c w y := by
  simp only [cappedExchangePerturbation_def, single_inf_const_target, update_inf_zero_const_target,
    plumbedPerturbation_const_target _ _ _ _ _ x y, negativePlanePerturbation_def]

/-- The components of the normalized capped family are those of the original one plus those of
the capped family of the normalizing functions, evaluated at any target point `y`. -/
private theorem cappedExchangePerturbation_add_const_fun (H : Puncture → ℝ → M → ℝ)
    (d : Puncture → ℝ → ℝ) (L c : ℝ) (v : ℂ) (y : M) :
    (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x v +
        cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [cappedExchangePerturbation_add_const, add_apply,
    cappedExchangePerturbation_const_target d L c _ x y]

/-- The components of the capped family of target-independent Hamiltonians, as functions of the
domain point alone. -/
private theorem cappedExchangePerturbation_const_target_fun (d : Puncture → ℝ → ℝ) (L c : ℝ)
    (v : ℂ) (y : M) :
    (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
        (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [cappedExchangePerturbation_const_target d L c _ x y]

end Floer

/-! ### The capped cylinder: symplectic vector spaces -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {d : Puncture → ℝ → ℝ} {L a b : ℝ}

/-- The curvature of the capped datum of target-independent Hamiltonians does not depend on the
target point. -/
theorem hamiltonianCurvature_cappedCylinderComponent_const_target (ω : SymplecticForm V)
    (d : Puncture → ℝ → ℝ) (L : ℝ) (z : ℝ × ℝ) (x y : V) :
    ω.hamiltonianCurvature (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z x =
      ω.hamiltonianCurvature (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z y := by
  rw [cappedCylinderComponent_const_target_fun d L 1 y,
    cappedCylinderComponent_const_target_fun d L Complex.I y, hamiltonianCurvature_const,
    hamiltonianCurvature_const]

/-- **The integrated curvature of a normalization of the capped cylinder.** For period-one `C¹`
functions `d_r` of time and `L > 4`, the curvature of the capped datum of the target-independent
Hamiltonians `d_r` integrates over the rectangle `[a, b] × [0, 1]`, for `a ≤ -3` and `2 ≤ b`, to
`∫₀¹ d_0 - ∫₀¹ d_∞`, along any map `u`. The normalization `d_1` of the capping Hamiltonian does
not contribute. -/
theorem setIntegral_hamiltonianCurvature_cappedCylinderComponent_const (ω : SymplecticForm V)
    (hd : ∀ r, Periodic (d r) 1) (hds : ∀ r, ContDiff ℝ 1 (d r)) (hL : 4 < L) (ha : a ≤ -3)
    (hb : 2 ≤ b) (u : ℝ × ℝ → V) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z (u z) =
      (∫ t in (0 : ℝ)..1, d zero t) - ∫ t in (0 : ℝ)..1, d inf t := by
  -- Along the constant map `0`, the energy density vanishes.
  have hE : ω.floerEnergyDensity (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
      (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) (fun _ ↦ (0 : V)) = 0 := by
    funext z
    rw [cappedCylinderComponent_const_target_fun d L 1 (0 : V),
      cappedCylinderComponent_const_target_fun d L Complex.I (0 : V), floerEnergyDensity_def,
      perturbedFDeriv_const]
    simp
  -- The energy identity for the constant map `0` leaves only the curvature and the end terms.
  have h := ω.integral_floerEnergyDensity_cappedCylinderComponent
    (Hb := fun r t (_ : V) ↦ d r t) (periodic_const_target hd)
    (contDiff_uncurry_const_target hds) hL isOpen_univ (u := fun _ ↦ (0 : V)) contDiffOn_const ha
    hb (subset_univ _) fun _ _ ↦ rfl
  rw [hE] at h
  simp only [Pi.zero_apply, integral_zero, hamiltonianAction_const] at h
  -- The curvature does not depend on the target point, so it is the same along `u` and `0`.
  have hu : (fun z ↦ ω.hamiltonianCurvature
      (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
      (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z (u z)) =
      fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z 0 :=
    funext fun z ↦ ω.hamiltonianCurvature_cappedCylinderComponent_const_target d L z (u z) 0
  rw [hu]
  linarith

/-- The curvature of the capped datum of target-independent Hamiltonians is integrable over the
strip `ℝ × [0, 1]`, along any map. -/
private theorem integrableOn_hamiltonianCurvature_cappedCylinderComponent_const
    (ω : SymplecticForm V) (hd : ∀ r, Periodic (d r) 1) (hds : ∀ r, ContDiff ℝ 1 (d r))
    (hL : 4 < L) (u : ℝ × ℝ → V) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z (u z))
      (univ ×ˢ Icc 0 1) := by
  obtain ⟨B, hB⟩ := exists_forall_abs_le_const_target (M := V) hd one_ne_zero
    fun r ↦ (hds r).continuous
  have hd' := periodic_const_target (M := V) hd
  have hds' := contDiff_uncurry_const_target (V := V) hds
  -- Along the constant map `0`, the curvature is a continuous function of the cylinder point.
  have hk (v : ℂ) : ContDiff ℝ 1
      fun z ↦ cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L v z 0 :=
    (contDiff_uncurry_cappedCylinderComponent hd' hds' hL v).comp
      (contDiff_id.prodMk contDiff_const)
  have hcont : Continuous fun z ↦ ω.hamiltonianCurvature
      (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
      (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z 0 := by
    have hf : (fun z ↦ ω.hamiltonianCurvature
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z 0) =
        fun z ↦ fderiv ℝ (fun z ↦ cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L
            Complex.I z 0) z stdComplexLineReal -
          fderiv ℝ (fun z ↦ cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1 z 0) z
            stdComplexLineImag := by
      funext z
      rw [cappedCylinderComponent_const_target_fun d L 1 (0 : V),
        cappedCylinderComponent_const_target_fun d L Complex.I (0 : V),
        hamiltonianCurvature_const]
    rw [hf]
    exact (((hk Complex.I).continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
      (((hk 1).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  -- Its integral over one period is finite by the uniform curvature bound.
  have hfin := ω.lintegral_enorm_hamiltonianCurvature_cappedCylinderComponent_le hd' hds' hL
    (Bb := B) hB 0 fun _ ↦ 0
  have hsets : ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] univ ×ˢ Icc 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc
  have h₀ : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
      (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z 0)
      (univ ×ˢ Icc 0 1) := by
    refine IntegrableOn.congr_set_ae ⟨hcont.aestronglyMeasurable, ?_⟩ hsets.symm
    rw [zero_add] at hfin
    exact hfin.trans_lt
      (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
        ENNReal.sum_lt_top.2 fun _ _ ↦ ENNReal.ofReal_lt_top⟩)
  exact h₀.congr_fun
    (fun z _ ↦ ω.hamiltonianCurvature_cappedCylinderComponent_const_target d L z 0 (u z))
    (MeasurableSet.univ.prod measurableSet_Icc)

/-- **The integrated curvature of a normalization over the whole capped cylinder.** For period-one
`C¹` functions `d_r` of time and `L > 4`, the curvature of the capped datum of the
target-independent Hamiltonians `d_r` integrates over the strip `ℝ × [0, 1]` to
`∫₀¹ d_0 - ∫₀¹ d_∞`, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_cappedCylinderComponent_const_univ_prod
    (ω : SymplecticForm V) (hd : ∀ r, Periodic (d r) 1) (hds : ∀ r, ContDiff ℝ 1 (d r))
    (hL : 4 < L) (u : ℝ × ℝ → V) :
    ∫ z in univ ×ˢ Icc 0 1, ω.hamiltonianCurvature
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : V) ↦ d r t) L Complex.I) z (u z) =
      (∫ t in (0 : ℝ)..1, d zero t) - ∫ t in (0 : ℝ)..1, d inf t := by
  -- The integral over the strip is the limit of the integrals over `[-R, R] × [0, 1]`, which are
  -- eventually constant.
  refine tendsto_nhds_unique (tendsto_setIntegral_Icc_prod tendsto_neg_atTop_atBot tendsto_id
    measurableSet_Icc (integrableOn_hamiltonianCurvature_cappedCylinderComponent_const ω hd hds hL
      u)) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 3] with R hR
  exact (ω.setIntegral_hamiltonianCurvature_cappedCylinderComponent_const hd hds hL
    (by linarith) (by simpa using hR.trans' (by norm_num)) u).symm

end SymplecticForm

/-! ### The capped cylinder: manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {Hb : Puncture → ℝ → M → ℝ} {d : Puncture → ℝ → ℝ} {L a b : ℝ}

/-- **Normalizing the Hamiltonians of the capped cylinder does not change the Floer equation.**
The perturbed derivative `du - X_K` of any map into `M` is the same for the Hamiltonians `Hb r`
and `Hb r + d r`. -/
@[simp]
theorem perturbedMFDeriv_cappedCylinderComponent_add_const (ω : SmoothTwoForm I M)
    (Hb : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ) (L : ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L 1)
        (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L Complex.I) u =
      ω.perturbedMFDeriv (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u := by
  rw [cappedCylinderComponent_add_const_fun Hb d L 1 (u 0),
    cappedCylinderComponent_add_const_fun Hb d L Complex.I (u 0), perturbedMFDeriv_add_const]

/-- **Normalizing the Hamiltonians of the capped cylinder does not change the energy density.** -/
@[simp]
theorem floerEnergyDensity_cappedCylinderComponent_add_const (ω : SmoothTwoForm I M)
    (Hb : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ) (L : ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L 1)
        (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L Complex.I) u =
      ω.floerEnergyDensity (cappedCylinderComponent Hb L 1)
        (cappedCylinderComponent Hb L Complex.I) u := by
  rw [cappedCylinderComponent_add_const_fun Hb d L 1 (u 0),
    cappedCylinderComponent_add_const_fun Hb d L Complex.I (u 0), floerEnergyDensity_add_const]

/-- The curvature of the capped datum of target-independent Hamiltonians does not depend on the
target point, for a manifold target. -/
theorem hamiltonianCurvature_cappedCylinderComponent_const_target (ω : SmoothTwoForm I M)
    (d : Puncture → ℝ → ℝ) (L : ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L Complex.I) z x =
      ω.hamiltonianCurvature (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L Complex.I) z y := by
  rw [cappedCylinderComponent_const_target_fun d L 1 x,
    cappedCylinderComponent_const_target_fun d L Complex.I x, hamiltonianCurvature_const,
    hamiltonianCurvature_const]

omit [IsManifold I ⊤ M] in
/-- The components of the capped datum are differentiable in the cylinder point. -/
private theorem differentiableAt_cappedCylinderComponent (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r))) (hL : 4 < L) (v : ℂ)
    (z : ℝ × ℝ) (x : M) :
    DifferentiableAt ℝ (fun w ↦ cappedCylinderComponent Hb L v w x) z := by
  have hg : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod I) 1 (fun w : ℝ × ℝ ↦ (w, x)) z :=
    contMDiffAt_id.prodMk contMDiffAt_const
  exact (contMDiffAt_iff_contDiffAt.1
    ((contMDiff_cappedCylinderComponent hHb hHbs hL v (z, x)).comp z hg)).differentiableAt
    one_ne_zero

/-- **The curvature of the normalized capped datum.** At every point of the cylinder, the
curvature of the capped datum of the Hamiltonians `Hb r + d r` is the curvature for `Hb r` plus
the curvature of the capped datum of the target-independent Hamiltonians `d r`. -/
theorem hamiltonianCurvature_cappedCylinderComponent_add_const (ω : SmoothTwoForm I M)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hd : ∀ r, Periodic (d r) 1) (hds : ∀ r, ContDiff ℝ 1 (d r)) (hL : 4 < L) (z : ℝ × ℝ)
    (x : M) :
    ω.hamiltonianCurvature (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L 1)
        (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L Complex.I) z x =
      ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z x +
        ω.hamiltonianCurvature (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L 1)
          (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L Complex.I) z x := by
  have hd' := periodic_const_target (M := M) hd
  have hds' := contMDiff_uncurry_const_target (I := I) (M := M) hds
  rw [cappedCylinderComponent_add_const_fun Hb d L 1 x,
    cappedCylinderComponent_add_const_fun Hb d L Complex.I x,
    hamiltonianCurvature_add_const ω (differentiableAt_cappedCylinderComponent hHb hHbs hL 1 z x)
      (differentiableAt_cappedCylinderComponent hHb hHbs hL Complex.I z x)
      (differentiableAt_cappedCylinderComponent hd' hds' hL 1 z x)
      (differentiableAt_cappedCylinderComponent hd' hds' hL Complex.I z x),
    ← cappedCylinderComponent_const_target_fun d L 1 x,
    ← cappedCylinderComponent_const_target_fun d L Complex.I x]

/-- The curvature of the capped datum of target-independent Hamiltonians on `M` is that on `ℂ`
along the constant map `0`: both are the exterior derivative of the same one-form on the
cylinder. -/
private theorem hamiltonianCurvature_cappedCylinderComponent_const_eq (ω : SmoothTwoForm I M)
    (d : Puncture → ℝ → ℝ) (L : ℝ) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L Complex.I) z x =
      stdComplexSymplecticForm.hamiltonianCurvature
        (cappedCylinderComponent (fun r t (_ : ℂ) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : ℂ) ↦ d r t) L Complex.I) z 0 := by
  rw [cappedCylinderComponent_const_target_fun d L 1 x,
    cappedCylinderComponent_const_target_fun d L Complex.I x, hamiltonianCurvature_const,
    cappedCylinderComponent_const_target_fun d L 1 (0 : ℂ),
    cappedCylinderComponent_const_target_fun d L Complex.I (0 : ℂ),
    SymplecticForm.hamiltonianCurvature_const]
  simp only [cappedCylinderComponent_const_target d L _ _ x (0 : ℂ)]

/-- **The integrated curvature of a normalization of the capped cylinder, for a manifold
target.** For period-one `C¹` functions `d_r` of time and `L > 4`, the curvature of the capped
datum of the target-independent Hamiltonians `d_r` on `M` integrates over the rectangle
`[a, b] × [0, 1]`, for `a ≤ -3` and `2 ≤ b`, to `∫₀¹ d_0 - ∫₀¹ d_∞`, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_cappedCylinderComponent_const (ω : SmoothTwoForm I M)
    (hd : ∀ r, Periodic (d r) 1) (hds : ∀ r, ContDiff ℝ 1 (d r)) (hL : 4 < L) (ha : a ≤ -3)
    (hb : 2 ≤ b) (u : ℝ × ℝ → M) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature
        (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L Complex.I) z (u z) =
      (∫ t in (0 : ℝ)..1, d zero t) - ∫ t in (0 : ℝ)..1, d inf t := by
  simp only [ω.hamiltonianCurvature_cappedCylinderComponent_const_eq]
  exact stdComplexSymplecticForm.setIntegral_hamiltonianCurvature_cappedCylinderComponent_const hd
    hds hL ha hb fun _ ↦ 0

/-- **The integrated curvature of a normalization over the whole capped cylinder, for a manifold
target.** For period-one `C¹` functions `d_r` of time and `L > 4`, the curvature of the capped
datum of the target-independent Hamiltonians `d_r` on `M` integrates over the strip `ℝ × [0, 1]`
to `∫₀¹ d_0 - ∫₀¹ d_∞`, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_cappedCylinderComponent_const_univ_prod
    (ω : SmoothTwoForm I M) (hd : ∀ r, Periodic (d r) 1) (hds : ∀ r, ContDiff ℝ 1 (d r))
    (hL : 4 < L) (u : ℝ × ℝ → M) :
    ∫ z in univ ×ˢ Icc 0 1, ω.hamiltonianCurvature
        (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L 1)
        (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L Complex.I) z (u z) =
      (∫ t in (0 : ℝ)..1, d zero t) - ∫ t in (0 : ℝ)..1, d inf t := by
  simp only [ω.hamiltonianCurvature_cappedCylinderComponent_const_eq]
  exact SymplecticForm.setIntegral_hamiltonianCurvature_cappedCylinderComponent_const_univ_prod
    stdComplexSymplecticForm hd hds hL fun _ ↦ 0

/-- **Normalizing the Hamiltonians shifts the integrated curvature of the capped cylinder.** For
`a ≤ -3` and `2 ≤ b`, along a map whose curvature for `Hb r` is integrable over the rectangle
`[a, b] × [0, 1]`, the integrated curvature for `Hb r + d r` is the integrated curvature for `Hb r`
plus `∫₀¹ d_0 - ∫₀¹ d_∞`. This is also the change of the Hamiltonian terms
`∫₀¹ Hb 0 (t, u(b, t)) dt - ∫₀¹ Hb ∞ (t, u(a, t)) dt` of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent`, so the
two changes cancel. The normalization `d_1` of the capping Hamiltonian changes neither. -/
theorem setIntegral_hamiltonianCurvature_cappedCylinderComponent_add_const (ω : SmoothTwoForm I M)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hd : ∀ r, Periodic (d r) 1) (hds : ∀ r, ContDiff ℝ 1 (d r)) (hL : 4 < L) (ha : a ≤ -3)
    (hb : 2 ≤ b) {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (Icc a b ×ˢ Icc 0 1)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature
        (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L 1)
        (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L Complex.I) z (u z) =
      (∫ z in Icc a b ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z)) +
        ((∫ t in (0 : ℝ)..1, d zero t) - ∫ t in (0 : ℝ)..1, d inf t) := by
  have hk : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L 1)
      (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L Complex.I) z (u z))
      (Icc a b ×ˢ Icc 0 1) := by
    simp only [ω.hamiltonianCurvature_cappedCylinderComponent_const_eq]
    exact (stdComplexSymplecticForm.integrableOn_hamiltonianCurvature_cappedCylinderComponent_const
      hd hds hL fun _ ↦ 0).mono_set (prod_mono (subset_univ _) le_rfl)
  rw [← ω.setIntegral_hamiltonianCurvature_cappedCylinderComponent_const hd hds hL ha hb u,
    ← integral_add hu hk]
  exact setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦
    ω.hamiltonianCurvature_cappedCylinderComponent_add_const hHb hHbs hd hds hL z (u z)

/-- **Normalizing the Hamiltonians shifts the integrated curvature over the whole capped
cylinder.** Along a map whose curvature for `Hb r` is integrable over the strip `ℝ × [0, 1]`, the
integrated curvature for `Hb r + d r` is the integrated curvature for `Hb r` plus
`∫₀¹ d_0 - ∫₀¹ d_∞`, which is also the change of the Hamiltonian terms at the asymptotic loops in
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedCylinderComponent_univ_prod`. -/
theorem setIntegral_hamiltonianCurvature_cappedCylinderComponent_add_const_univ_prod
    (ω : SmoothTwoForm I M) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hd : ∀ r, Periodic (d r) 1) (hds : ∀ r, ContDiff ℝ 1 (d r)) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
      (cappedCylinderComponent Hb L Complex.I) z (u z)) (univ ×ˢ Icc 0 1)) :
    ∫ z in univ ×ˢ Icc 0 1, ω.hamiltonianCurvature
        (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L 1)
        (cappedCylinderComponent (fun r t y ↦ Hb r t y + d r t) L Complex.I) z (u z) =
      (∫ z in univ ×ˢ Icc 0 1, ω.hamiltonianCurvature (cappedCylinderComponent Hb L 1)
          (cappedCylinderComponent Hb L Complex.I) z (u z)) +
        ((∫ t in (0 : ℝ)..1, d zero t) - ∫ t in (0 : ℝ)..1, d inf t) := by
  have hk : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L 1)
      (cappedCylinderComponent (fun r t (_ : M) ↦ d r t) L Complex.I) z (u z))
      (univ ×ˢ Icc 0 1) := by
    simp only [ω.hamiltonianCurvature_cappedCylinderComponent_const_eq]
    exact stdComplexSymplecticForm.integrableOn_hamiltonianCurvature_cappedCylinderComponent_const
      hd hds hL fun _ ↦ 0
  rw [← ω.setIntegral_hamiltonianCurvature_cappedCylinderComponent_const_univ_prod hd hds hL u,
    ← integral_add hu hk]
  exact setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Icc) fun z _ ↦
    ω.hamiltonianCurvature_cappedCylinderComponent_add_const hHb hHbs hd hds hL z (u z)

/-! ### The input-exchange family capped at `0`: manifold targets -/

section LeftCapping

variable {H : Puncture → ℝ → M → ℝ} {c : ℝ}

/-- **Normalizing the Hamiltonians of the input-exchange family capped at `0` does not change the
Floer equation.** The perturbed derivative `du - X_K` of any map into `M` is the same for the
Hamiltonians `H_q` and `H_q + d_q`. -/
@[simp]
theorem perturbedMFDeriv_cappedExchangePerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ) (L c : ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedMFDeriv
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) u := by
  rw [cappedExchangePerturbation_add_const_fun H d L c 1 (u 0),
    cappedExchangePerturbation_add_const_fun H d L c Complex.I (u 0), perturbedMFDeriv_add_const]

/-- **Normalizing the Hamiltonians of the input-exchange family capped at `0` does not change the
energy density.** -/
@[simp]
theorem floerEnergyDensity_cappedExchangePerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ) (L c : ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I) u := by
  rw [cappedExchangePerturbation_add_const_fun H d L c 1 (u 0),
    cappedExchangePerturbation_add_const_fun H d L c Complex.I (u 0), floerEnergyDensity_add_const]

/-- The curvature of the input-exchange family capped at `0` of target-independent Hamiltonians
does not depend on the target point, for a manifold target. -/
theorem hamiltonianCurvature_cappedExchangePerturbation_const_target (ω : SmoothTwoForm I M)
    (d : Puncture → ℝ → ℝ) (L c : ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [cappedExchangePerturbation_const_target_fun d L c 1 x,
    cappedExchangePerturbation_const_target_fun d L c Complex.I x, hamiltonianCurvature_const,
    hamiltonianCurvature_const]

omit [IsManifold I ⊤ M] in
/-- The components of the capped family are differentiable at the points of `S`. -/
private theorem differentiableAt_cappedExchangePerturbation (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (hL : 4 < L) (c : ℝ)
    (v : ℂ) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) (x : M) :
    DifferentiableAt ℝ
      (fun w ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm w) x v) z := by
  have hg : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 1
      (fun w : ℝ × ℝ ↦ (c, (Complex.equivRealProdCLM.symm w, x))) z :=
    contMDiffAt_const.prodMk
      (Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.prodMk contMDiffAt_const)
  have h := ((contMDiffAt_cappedExchangePerturbation hH hHs hL c
    (mem_thricePuncturedSphereReal_iff.1 hz).2 x).comp z hg).clm_apply
      (contMDiffAt_const (c := v))
  exact (contMDiffAt_iff_contDiffAt.1 h).differentiableAt one_ne_zero

/-- **The curvature of the normalized capped family.** At every point of `S`, the curvature of the
member `c` of the input-exchange family capped at `0` for the Hamiltonians `H_q + d_q` is the
curvature for `H_q` plus the curvature of the member for the target-independent Hamiltonians
`d_q`. -/
theorem hamiltonianCurvature_cappedExchangePerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (hL : 4 < L) (c : ℝ)
    {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) z x +
        ω.hamiltonianCurvature
          (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have hd' := periodic_const_target (M := M) hd
  have hds' := contMDiff_uncurry_const_target (I := I) (M := M) hds
  rw [cappedExchangePerturbation_add_const_fun H d L c 1 x,
    cappedExchangePerturbation_add_const_fun H d L c Complex.I x,
    hamiltonianCurvature_add_const ω
      (differentiableAt_cappedExchangePerturbation hH hHs hL c 1 hz x)
      (differentiableAt_cappedExchangePerturbation hH hHs hL c Complex.I hz x)
      (differentiableAt_cappedExchangePerturbation hd' hds' hL c 1 hz x)
      (differentiableAt_cappedExchangePerturbation hd' hds' hL c Complex.I hz x),
    ← cappedExchangePerturbation_const_target_fun d L c 1 x,
    ← cappedExchangePerturbation_const_target_fun d L c Complex.I x]

/-- The curvature of the capped family of target-independent Hamiltonians on `M` is that on `ℂ`
along the constant map `0`: both are the exterior derivative of the same one-form on the
domain. -/
private theorem hamiltonianCurvature_cappedExchangePerturbation_const_eq (ω : SmoothTwoForm I M)
    (d : Puncture → ℝ → ℝ) (L c : ℝ) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      stdComplexSymplecticForm.constSmooth.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : ℂ) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : ℂ) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 := by
  rw [cappedExchangePerturbation_const_target_fun d L c 1 x,
    cappedExchangePerturbation_const_target_fun d L c Complex.I x, hamiltonianCurvature_const,
    cappedExchangePerturbation_const_target_fun d L c 1 (0 : ℂ),
    cappedExchangePerturbation_const_target_fun d L c Complex.I (0 : ℂ),
    hamiltonianCurvature_const]
  simp only [cappedExchangePerturbation_const_target d L c _ x (0 : ℂ)]

/-- **The integrated curvature of a normalization of the input-exchange family capped at `0`.**
For period-one `C¹` functions `d_q` of time, `L > 4` and `0 ≤ c ≤ 1`, the curvature of the member
`c` of the family for the target-independent Hamiltonians `d_q` on `M` integrates over `S` to
`∫₀¹ d_1 - ∫₀¹ d_∞`, along any map `u`. The normalization `d_0` of the capping Hamiltonian does
not contribute. -/
theorem setIntegral_hamiltonianCurvature_cappedExchangePerturbation_const (ω : SmoothTwoForm I M)
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (hL : 4 < L) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) (u : ℝ × ℝ → M) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ t in (0 : ℝ)..1, d one t) - ∫ t in (0 : ℝ)..1, d inf t := by
  simp only [ω.hamiltonianCurvature_cappedExchangePerturbation_const_eq]
  obtain ⟨B, hB⟩ := exists_forall_abs_le_const_target (M := ℂ) hd one_ne_zero
    fun q ↦ (hds q).continuous
  -- Along the constant map `0` into `ℂ`, the energy density and the area density vanish.
  have hE : stdComplexSymplecticForm.constSmooth.floerEnergyDensity
      (fun z x ↦ cappedExchangePerturbation (fun q t (_ : ℂ) ↦ d q t) L c
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation (fun q t (_ : ℂ) ↦ d q t) L c
        (Complex.equivRealProdCLM.symm z) x Complex.I) (fun _ ↦ (0 : ℂ)) = 0 := by
    funext z
    rw [cappedExchangePerturbation_const_target_fun d L c 1 (0 : ℂ),
      cappedExchangePerturbation_const_target_fun d L c Complex.I (0 : ℂ),
      SymplecticForm.floerEnergyDensity_constSmooth, SymplecticForm.floerEnergyDensity_def,
      SymplecticForm.perturbedFDeriv_const]
    simp
  have hA : (fun z : ℝ × ℝ ↦ (SmoothBundleForm.eval₂ stdComplexSymplecticForm.constSmooth (0 : ℂ)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun _ ↦ (0 : ℂ)) z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun _ ↦ (0 : ℂ)) z stdComplexLineImag) : ℝ)) = 0 := by
    funext z
    simp only [mfderiv_const, SmoothBundleForm.eval₂_apply, Pi.zero_apply]
    -- The first vector is the zero map of tangent spaces applied to a vector.
    exact ContinuousAlternatingMap.map_coord_zero _ (0 : Fin 2) (by rfl)
  -- The energy identity for the constant map `0` leaves only the curvature and the end terms.
  have h := (SymplecticForm.isNondegenerate_constSmooth stdComplexSymplecticForm
    ).integral_floerEnergyDensity_cappedExchangePerturbation (H := fun q t (_ : ℂ) ↦ d q t)
    (periodic_const_target hd) (contMDiff_uncurry_const_target hds)
    (B := B) hB hL hc₀ hc₁ (u := fun _ ↦ (0 : ℂ))
    contMDiffOn_const
    (x₁ := fun _ ↦ 0) (xinf := fun _ ↦ 0) (fun _ ↦ tendsto_const_nhds)
    (fun _ ↦ tendsto_const_nhds) (by rw [hE]; exact integrableOn_zero)
    (by rw [hA]; exact integrableOn_zero)
  rw [hE, hA] at h
  simp only [integral_zero', zero_add] at h
  linarith

/-- **Normalizing the Hamiltonians shifts the integrated curvature of the input-exchange family
capped at `0`.** For `L > 4` and `0 ≤ c ≤ 1`, along a map whose curvature for `H_q` is integrable
over `S`, the integrated curvature for `H_q + d_q` is the integrated curvature for `H_q` plus
`∫₀¹ d_1 - ∫₀¹ d_∞`. This is also the change of the Hamiltonian terms
`∫₀¹ H_1(t, x_1(t)) dt - ∫₀¹ H_∞(t, x_∞(t)) dt` of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedExchangePerturbation`, so the two
changes cancel. The normalization `d_0` of the capping Hamiltonian changes neither. -/
theorem setIntegral_hamiltonianCurvature_cappedExchangePerturbation_add_const
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (hL : 4 < L) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation (fun q t y ↦ H q t y + d q t) L c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z)) +
        ((∫ t in (0 : ℝ)..1, d one t) - ∫ t in (0 : ℝ)..1, d inf t) := by
  -- The curvature of the normalization is that along a constant map into `ℂ`, so it is integrable.
  have hk : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedExchangePerturbation (fun q t (_ : M) ↦ d q t) L c
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) thricePuncturedSphereReal := by
    simp only [ω.hamiltonianCurvature_cappedExchangePerturbation_const_eq]
    obtain ⟨B, hB⟩ := exists_forall_abs_le_const_target (M := ℂ) hd one_ne_zero
      fun q ↦ (hds q).continuous
    exact ((SymplecticForm.isNondegenerate_constSmooth stdComplexSymplecticForm
      ).integrable_hamiltonianCurvature_cappedExchangePerturbation (H := fun q t (_ : ℂ) ↦ d q t)
      (periodic_const_target hd) (contMDiff_uncurry_const_target hds)
      (B := B) hB hL hc₀ hc₁ (u := fun _ ↦ (0 : ℂ))
      continuousOn_const).integrableOn
  rw [← ω.setIntegral_hamiltonianCurvature_cappedExchangePerturbation_const hd hds hL hc₀ hc₁ u,
    ← integral_add hu hk]
  exact setIntegral_congr_fun isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
    ω.hamiltonianCurvature_cappedExchangePerturbation_add_const hH hHs hd hds hL c hz (u z)

end LeftCapping

end SmoothTwoForm

end TauCeti
