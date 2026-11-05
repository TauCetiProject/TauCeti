/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# Translations of Floer cylinders

The Floer differential, and the cylinders inserted at the ends of a pair of pants, count solutions
`u : ℝ × [0, 1] → V` of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the
cylindrical perturbation `K = H_t dt` up to the translations `(s, t) ↦ (s + c, t)`. The
perturbation does not depend on `s`, so the perturbed derivative of the translate of `u` is the
translate of the perturbed derivative of `u` (`SymplecticForm.perturbedFDeriv_comp_add_right`).
Hence the translate of a solution for the almost complex structures `J` solves the equation for
the translated structures `J(· + (c, 0))`, which are `J` itself when `J` does not depend on `s`,
and translations preserve the energy (`SymplecticForm.lintegral_floerEnergyDensity_comp_add_right`).
This file identifies the fixed points of this action of `ℝ` on finite-energy solutions and shows
that it is free elsewhere, so that the quotient by translations is taken only away from the
stationary cylinders.

For this perturbation the two components of the perturbed derivative are `∂_s u` and
`∂_t u - X_{H_t}(u)` (`SymplecticForm.perturbedFDeriv_cylindrical_apply_stdComplexLineReal` and
`SymplecticForm.perturbedFDeriv_cylindrical_apply_stdComplexLineImag`).

The *stationary* cylinders `u(s, t) = x(t)` are fixed by every translation. The perturbed
derivative of such a cylinder sends `(a, b)` to `b (x' - X_{H_t}(x))`
(`SymplecticForm.perturbedFDeriv_comp_snd_apply`), so it solves the Floer equation exactly when
`x' = X_{H_t}(x)`, that is, when `x` is a Hamiltonian orbit
(`SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_snd_iff`), and its energy density
vanishes (`SymplecticForm.floerEnergyDensity_comp_snd`). Conversely, for almost complex structures
tamed by `ω`, a `C¹` solution has zero energy exactly when it is stationary
(`SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`): the energy density of a solution
vanishes only where `∂_s u = 0`.

A solution of finite energy that is invariant under a translation by `c ≠ 0` has the same energy
over each of the infinitely many disjoint period rectangles of the strip, so its energy is zero
(`SymplecticForm.lintegral_floerEnergyDensity_eq_zero_of_periodic`, from
`TauCeti.setLIntegral_univ_prod_eq_zero_of_periodic`), and it is stationary. Hence a
nonstationary finite-energy solution is fixed by no nontrivial translation
(`SymplecticForm.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`). The stationary
cylinders, where the action is not free, are treated separately in Floer theory through their
linearized operator.

The target is a symplectic vector space `(V, ω)` and the almost complex structures may depend on
the domain point. These are statements about classical solutions; no Sobolev completion,
compactness or transversality is asserted.

## Main results

* `SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_snd_iff`: stationary solutions are the
  Hamiltonian orbits.
* `SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`: a solution has zero energy exactly
  when it is stationary.
* `SymplecticForm.lintegral_floerEnergyDensity_eq_zero_of_periodic`: a finite-energy solution
  invariant under a nontrivial translation has zero energy.
* `SymplecticForm.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`: translations act
  freely on nonstationary finite-energy solutions.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the translation action on connecting trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on the energy of Floer cylinders and the stationary solutions.
-/

public section

open Filter Function MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Cylinder

/-- For the cylindrical perturbation `K = H_t dt`, the energy density of the translate
`(s, t) ↦ u(s + c, t)` at `z` is the energy density of `u` at `z + (c, 0)`. -/
private theorem floerEnergyDensity_cylindrical_comp_add_right (ω : SymplecticForm V) (H : ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (c : ℝ) (z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (c, 0))) z =
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (z + (c, 0)) := by
  simpa using ω.floerEnergyDensity_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u (c, 0) z

variable {ω : SymplecticForm V} {H : ℝ → V → ℝ} {x : ℝ → V} {z : ℝ × ℝ}

/-- For `K = H_t dt` the `s`-component of the perturbed derivative is `∂_s u`. -/
theorem perturbedFDeriv_cylindrical_apply_stdComplexLineReal (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineReal =
      fderiv ℝ u z (1, 0) := by
  rw [perturbedFDeriv_apply_stdComplexLineReal, stdComplexLineReal_eq,
    hamiltonianVectorField_const, Pi.zero_apply, sub_zero]

/-- For `K = H_t dt` the `t`-component of the perturbed derivative is `∂_t u - X_{H_t}(u)`. -/
theorem perturbedFDeriv_cylindrical_apply_stdComplexLineImag (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag =
      fderiv ℝ u z (0, 1) - ω.hamiltonianVectorField (H z.2) (u z) := by
  rw [perturbedFDeriv_apply_stdComplexLineImag, stdComplexLineImag_eq]

/-- The perturbed derivative of a stationary map `(s, t) ↦ x(t)` for `K = H_t dt` sends `(a, b)`
to `b (x'(t) - X_{H_t}(x(t)))`. -/
theorem perturbedFDeriv_comp_snd_apply (hx : DifferentiableAt ℝ x z.2) (v : ℝ × ℝ) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z v =
      v.2 • (deriv x z.2 - ω.hamiltonianVectorField (H z.2) (x z.2)) := by
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ x w.2)
      ((fderiv ℝ x z.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    hx.hasFDerivAt.comp z hasFDerivAt_snd
  have h₁ : fderiv ℝ x z.2 v.2 = v.2 • deriv x z.2 := by
    rw [← fderiv_apply_one_eq_deriv, ← map_smul, smul_eq_mul, mul_one]
  rw [perturbedFDeriv_apply, h.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', h₁, hamiltonianVectorField_const]
  simp [smul_sub]

/-- **Stationary Floer cylinders are Hamiltonian orbits.** For the cylindrical perturbation
`K = H_t dt`, the stationary map `(s, t) ↦ x(t)` solves the Floer equation at `z` exactly when
`x'(t) = X_{H_t}(x(t))`, where `t = z.2`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_snd_iff {J : AlmostComplexStructure V}
    (hx : DifferentiableAt ℝ x z.2) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z : ℝ × ℝ →ₗ[ℝ] V) ↔
      deriv x z.2 = ω.hamiltonianVectorField (H z.2) (x z.2) := by
  rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe,
    perturbedFDeriv_comp_snd_apply hx, perturbedFDeriv_comp_snd_apply hx]
  simp [sub_eq_zero]

/-- **The energy density of a stationary map.** For the cylindrical perturbation `K = H_t dt`,
the Floer energy density of `(s, t) ↦ x(t)` vanishes. -/
theorem floerEnergyDensity_comp_snd (hx : DifferentiableAt ℝ x z.2) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z = 0 := by
  simp [floerEnergyDensity_def, perturbedFDeriv_comp_snd_apply hx]

end Cylinder

section Stationary

variable {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)}

/-- The open strip `ℝ × (0, 1)` lies in the closed strip `ℝ × [0, 1]`. -/
private theorem strip_Ioo_subset_Icc :
    (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
  prod_mono subset_rfl Ioo_subset_Icc_self

/-- The closed strip `ℝ × [0, 1]` is the closure of the open strip `ℝ × (0, 1)`. -/
private theorem closure_univ_prod_Ioo :
    closure ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) = (univ : Set ℝ) ×ˢ Icc 0 1 := by
  rw [closure_prod_eq, closure_univ, closure_Ioo zero_ne_one]

/-- A map that is `C¹` on a neighbourhood of the closed strip `ℝ × [0, 1]`, solves the Floer
equation for `K = H_t dt` and tamed almost complex structures there, and has zero energy density
on the open strip `ℝ × (0, 1)`, is stationary on the closed strip. -/
private theorem eq_of_forall_floerEnergyDensity_eq_zero (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U)
    (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U) (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (h0 : ∀ z ∈ (univ : Set ℝ) ×ˢ Ioo 0 1,
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0) :
    ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s, t) = u (0, t) := by
  -- The `s`-derivative vanishes on the open strip, since the perturbed derivative does.
  have hds : EqOn (fun z ↦ fderiv ℝ u z stdComplexLineReal) 0 ((univ : Set ℝ) ×ˢ Ioo 0 1) := by
    intro z hz
    have hz' := strip_Ioo_subset_Icc hz
    have h := (ω.floerEnergyDensity_eq_zero_iff (hJ z hz') (hfloer z hz')).1 (h0 z hz)
    simpa using congrArg (· stdComplexLineReal) h
  -- By continuity it vanishes on the closed strip.
  have hds' : EqOn (fun z ↦ fderiv ℝ u z stdComplexLineReal) 0 ((univ : Set ℝ) ×ˢ Icc 0 1) :=
    hds.of_subset_closure
      (((hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono hRU)
      continuous_zero.continuousOn strip_Ioo_subset_Icc closure_univ_prod_Ioo.ge
  -- Along each horizontal line of the closed strip `u` has zero derivative, so it is constant.
  intro s t ht
  have hline (r : ℝ) : HasDerivAt (fun r ↦ u (r, t)) 0 r := by
    have hr : (r, t) ∈ U := hRU ⟨mem_univ r, ht⟩
    have h0 := hds' (show (r, t) ∈ (univ : Set ℝ) ×ˢ Icc 0 1 from ⟨mem_univ r, ht⟩)
    rw [stdComplexLineReal_eq] at h0
    simpa [h0] using hasDerivAt_slice_left
      ((hu.differentiableOn one_ne_zero _ hr).differentiableAt (hU.mem_nhds hr))
  exact is_const_of_deriv_eq_zero (fun r ↦ (hline r).differentiableAt)
    (fun r ↦ (hline r).deriv) s 0

/-- A map that is `C¹` on a neighbourhood of the closed strip `ℝ × [0, 1]` and solves the Floer
equation for `K = H_t dt` and tamed almost complex structures there has zero energy density at
every point of the open strip `ℝ × (0, 1)` if its energy over the open strip vanishes. -/
private theorem floerEnergyDensity_eq_zero_of_lintegral_eq_zero (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Ioo 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) = 0) :
    ∀ z ∈ (univ : Set ℝ) ×ˢ Ioo 0 1,
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0 := by
  have hopen : IsOpen ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) := isOpen_univ.prod isOpen_Ioo
  have hc : ContinuousOn (fun z ↦ ENNReal.ofReal
      (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)) ((univ : Set ℝ) ×ˢ Ioo 0 1) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((ω.continuousOn_floerEnergyDensity hU hu contDiffOn_const
        (contDiff_uncurry_cylindrical hH).contDiffOn).mono (strip_Ioo_subset_Icc.trans hRU))
  -- A continuous function with zero integral over an open set vanishes there.
  have hae := (lintegral_eq_zero_iff' (hc.aemeasurable hopen.measurableSet)).1 hE
  intro z hz
  have h := Measure.eqOn_open_of_ae_eq hae hopen hc continuous_zero.continuousOn hz
  have hz' := strip_Ioo_subset_Icc hz
  exact le_antisymm (ENNReal.ofReal_eq_zero.1 h)
    (ω.floerEnergyDensity_nonneg (hJ z hz') (hfloer z hz'))

/-- **Zero energy characterizes stationary Floer cylinders.** Let `H` be a `C¹` time-dependent
Hamiltonian and let `u` be `C¹` on an open neighbourhood `U` of the strip `ℝ × [0, 1]`, solving
the Floer equation for the cylindrical perturbation `K = H_t dt` there, for almost complex
structures `J z` tamed by `ω`. Then the energy of `u` over the strip vanishes exactly when `u` is
stationary there, `u(s, t) = u(0, t)`. -/
theorem lintegral_floerEnergyDensity_eq_zero_iff (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) = 0 ↔
      ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s, t) = u (0, t) := by
  refine ⟨fun hE ↦ eq_of_forall_floerEnergyDensity_eq_zero ω hU hu hRU hJ hfloer
    (floerEnergyDensity_eq_zero_of_lintegral_eq_zero ω hH hU hu hRU hJ hfloer
      (le_antisymm (hE ▸ lintegral_mono_set strip_Ioo_subset_Icc) zero_le)), fun hst ↦ ?_⟩
  -- Near a point of the open strip `u` agrees with the stationary map `(s, t) ↦ u(0, t)`.
  have h0 : EqOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u) 0
      ((univ : Set ℝ) ×ˢ Ioo 0 1) := by
    intro z hz
    have hev : u =ᶠ[𝓝 z] fun w ↦ u (0, w.2) :=
      Filter.mem_of_superset ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
        fun w hw ↦ hst w.1 w.2 (Ioo_subset_Icc_self hw.2)
    have hx : DifferentiableAt ℝ (fun t ↦ u (0, t)) z.2 := by
      have hz' : ((0 : ℝ), z.2) ∈ U := hRU ⟨mem_univ _, Ioo_subset_Icc_self hz.2⟩
      exact ((hu.differentiableOn one_ne_zero _ hz').differentiableAt
        (hU.mem_nhds hz')).comp z.2 ((differentiableAt_const _).prodMk differentiableAt_id)
    rw [Pi.zero_apply, ω.floerEnergyDensity_congr_of_eventuallyEq _ _ hev]
    exact floerEnergyDensity_comp_snd hx
  -- By continuity the energy density vanishes on the closed strip.
  have h0' : EqOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u) 0
      ((univ : Set ℝ) ×ˢ Icc 0 1) :=
    h0.of_subset_closure ((ω.continuousOn_floerEnergyDensity hU hu contDiffOn_const
        (contDiff_uncurry_cylindrical hH).contDiffOn).mono hRU)
      continuous_zero.continuousOn strip_Ioo_subset_Icc closure_univ_prod_Ioo.ge
  rw [setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ by
    rw [h0' hz, Pi.zero_apply, ENNReal.ofReal_zero]]
  exact lintegral_zero

/-- **Translation-invariant Floer cylinders have zero energy.** Under the hypotheses of
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`, suppose that `u` has finite
energy over the strip `ℝ × [0, 1]` and is invariant there under the translation
`(s, t) ↦ (s + c, t)` for some `c ≠ 0`. Then the energy of `u` vanishes, so `u` is stationary. -/
theorem lintegral_floerEnergyDensity_eq_zero_of_periodic (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {c : ℝ} (hc : c ≠ 0) (hper : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s + c, t) = u (s, t)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) = 0 := by
  set f : ℝ × ℝ → ENNReal := fun z ↦
    ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)
  -- `u` is also invariant under the translation by the positive period `|c|`.
  have hper' : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s + |c|, t) = u (s, t) := by
    intro s t ht
    rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩
    · rw [hc', hper s t ht]
    · rw [hc', ← hper (s + -c) t ht, neg_add_cancel_right]
  -- So is its energy density on the open strip, where the translate agrees with `u` nearby.
  have hf : ∀ s, ∀ t ∈ Ioo (0 : ℝ) 1, f (s + |c|, t) = f (s, t) := by
    intro s t ht
    have hev : (fun w ↦ u (w + (|c|, 0))) =ᶠ[𝓝 (s, t)] u :=
      Filter.mem_of_superset ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ s, ht⟩)
        fun ⟨a, b⟩ hw ↦ by simpa using hper' a b (Ioo_subset_Icc_self hw.2)
    have h := floerEnergyDensity_cylindrical_comp_add_right ω H u |c| (s, t)
    rw [ω.floerEnergyDensity_congr_of_eventuallyEq _ _ hev, Prod.mk_add_mk, add_zero] at h
    simp only [f, ← h]
  have hμ : MeasurePreserving (fun z : ℝ × ℝ ↦ (z.1 + |c|, z.2)) volume volume :=
    (measurePreserving_add_right volume |c|).prod (MeasurePreserving.id volume)
  -- The energy over the open strip vanishes, so `u` is stationary.
  have hE := setLIntegral_univ_prod_eq_zero_of_periodic measurableSet_Ioo (abs_pos.2 hc) hμ hf
    (ne_top_of_le_ne_top hfin (lintegral_mono_set strip_Ioo_subset_Icc))
  exact (ω.lintegral_floerEnergyDensity_eq_zero_iff hH hU hu hRU hJ hfloer).2
    (eq_of_forall_floerEnergyDensity_eq_zero ω hU hu hRU hJ hfloer
      (floerEnergyDensity_eq_zero_of_lintegral_eq_zero ω hH hU hu hRU hJ hfloer hE))

/-- **Translations act freely on nonstationary finite-energy Floer cylinders.** Under the
hypotheses of `TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`, if `u` has finite
energy over the strip `ℝ × [0, 1]` and is not stationary there, then the only translation
`(s, t) ↦ (s + c, t)` leaving `u` invariant on the strip is the identity, `c = 0`. -/
theorem eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hns : ∃ s, ∃ t ∈ Icc (0 : ℝ) 1, u (s, t) ≠ u (0, t))
    {c : ℝ} (hper : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s + c, t) = u (s, t)) :
    c = 0 := by
  by_contra hc
  obtain ⟨s, t, ht, hne⟩ := hns
  exact hne ((ω.lintegral_floerEnergyDensity_eq_zero_iff hH hU hu hRU hJ hfloer).1
    (ω.lintegral_floerEnergyDensity_eq_zero_of_periodic hH hU hu hRU hJ hfloer hfin hc hper) s t ht)

end Stationary

end TauCeti.SymplecticForm
