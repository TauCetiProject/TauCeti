/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Normed.Group.Prod
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Sobolev.Poincare.Infinity
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.CompactSupport
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The semi-Fredholm estimate of the linearized Floer operator on the Riemann sphere

Let `(V, ω)` be a finite-dimensional symplectic vector space. Some Floer problems live on a closed
domain: the comparison between the pair-of-pants product and the quantum product deforms Floer
data on the sphere with three poles, read in the coordinate `w ∈ ℂ ≅ ℝ × ℝ` in which the poles are
`0`, `1` and `∞`. Near the pole `∞` such data are unperturbed: the Hamiltonian perturbation
vanishes and the almost complex structure is a fixed `ω`-compatible `J₀`, independent of the
domain point and of the target point. This file proves the a priori estimate behind the Fredholm
property of the linearized operator `D_u` (`TauCeti.SymplecticForm.floerLinearization`) of such
data on the whole sphere.

The `W^{1,2}` norm of a section of the sphere, written in the coordinate `w`, is

`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`,  `ρ(w) = (1 + |w|²)⁻²`,

because the Dirichlet energy is conformally invariant and the spherical area element is `4 ρ`
times Lebesgue measure. If the data are `J₀` and `0` on `‖w‖ ≥ T`, and `J(w, u w)` is compatible
and the data are regular along `u`, then there are `R` and `C` such that every compactly supported
`C²` section `ξ` of the plane satisfies

`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ R} ‖ξ‖²)`

(`TauCeti.SymplecticForm.exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base`).
Here `‖w‖` is the sup norm of `ℝ × ℝ`, so `‖w‖ ≤ R` is a square. The error term is the `L²` norm
over a compact subset of the plane, on which restriction from
`W^{1,2}` to `L²` is compact by Rellich's theorem, so this is the estimate that Peetre's argument
turns into finite-dimensional kernel and closed range. Compactly supported sections of the plane
are dense in `W^{1,2}` of the sphere, since a point has capacity zero in dimension two.

The proof cuts `ξ` with a bump function `β` equal to `1` on the square `‖w‖ ≤ R` into `β ξ` and
`χ = (1 - β) ξ`.

* On the square `‖w‖ ≤ 2 R` the interior estimate of the linearized operator, from
  `TauCeti.Geometry.Symplectic.Floer.InteriorEstimate`, bounds the derivatives of `β ξ`, and
  the derivative of `β` only adds `L²` norms of `ξ` there.
* Where `χ` lives, `D_u χ = ∂s χ + J₀ ∂t χ` is the Cauchy–Riemann operator of `J₀`, and the energy
  identity for compactly supported maps
  (`TauCeti.SymplecticForm.integral_stdComplexLineEnergyDensity_eq_integral_associatedBilinForm`)
  bounds the Dirichlet energy of `χ` by `∫ ‖D_u χ‖²`, with no error term. The weighted `L²` norm
  of `χ` is bounded by its Dirichlet energy by the Poincaré inequality at infinity
  (`TauCeti.integral_inv_sq_mul_norm_sq_le`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate of Cauchy–Riemann operators on closed surfaces.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Floer problems on the sphere comparing the pair-of-pants and quantum products.
-/

public section

open Filter Function MeasureTheory Metric Set
open scoped Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ × ℝ → V → AlmostComplexStructure V}
  {J₀ : AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}

/-- Where the data are `J₀` and `0`, and in particular on sections vanishing elsewhere, the
linearized operator is the Cauchy–Riemann operator `∂s + J₀ ∂t` of `J₀`. -/
private theorem floerLinearization_eq_of_eq_base
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    {χ : ℝ × ℝ → V} (hχ : ∀ z : ℝ × ℝ, ‖z‖ < T → χ z = 0) (z : ℝ × ℝ) :
    ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u χ z =
      fderiv ℝ χ z stdComplexLineReal + J₀ (fderiv ℝ χ z stdComplexLineImag) := by
  rcases lt_or_ge ‖z‖ T with hz | hz
  · have hev : χ =ᶠ[𝓝 z] 0 :=
      mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hz) fun w hw ↦ hχ w hw
    rw [floerLinearization_congr_of_eventuallyEq _ _ _ _ _ hev, hev.fderiv_eq]
    simp
  · rw [floerLinearization_eq_add, floerLinearizationCoeff_apply]
    have hKs : Ks z = fun _ ↦ 0 := funext (hKs₀ z hz)
    have hKt : Kt z = fun _ ↦ 0 := funext (hKt₀ z hz)
    simp [hJ₀ z hz, hKs, hKt, hamiltonianVectorField_const]

/-- **The Cauchy–Riemann operator of `J₀` controls the Dirichlet energy.** On compactly supported
`C²` sections vanishing where the data differ from `J₀` and `0`, the linearized operator bounds
the Dirichlet energy, with no lower-order term. -/
private theorem exists_forall_integral_norm_fderiv_sq_le_of_eq_base (h₀ : ω.Compatible J₀)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃χ : ℝ × ℝ → V⦄, ContDiff ℝ 2 χ → HasCompactSupport χ →
      (∀ z : ℝ × ℝ, ‖z‖ < T → χ z = 0) →
      ∫ z, (‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2) ≤
        C * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u χ z‖ ^ 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    (J := fun _ : Unit ↦ J₀) isCompact_univ continuousOn_const fun _ _ ↦ h₀.tames
  refine ⟨b / a, by positivity, fun χ hχ hc hχT ↦ ?_⟩
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hdχ : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv two_ne_zero
  set F : ℝ × ℝ → V := fun z ↦ fderiv ℝ χ z stdComplexLineReal +
    J₀ (fderiv ℝ χ z stdComplexLineImag)
  have hF : Continuous F := (hdχ.clm_apply continuous_const).add
    ((J₀.toLinearMap.toContinuousLinearMap.continuous).comp (hdχ.clm_apply continuous_const))
  have hFc : HasCompactSupport F :=
    (hc.fderiv_apply (𝕜 := ℝ) stdComplexLineReal).add
      ((hc.fderiv_apply (𝕜 := ℝ) stdComplexLineImag).comp_left (map_zero J₀.toLinearMap))
  have hD : (fun z ↦ ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      Ks Kt u χ z‖ ^ 2) = fun z ↦ ‖F z‖ ^ 2 :=
    funext fun z ↦ by rw [floerLinearization_eq_of_eq_base hJ₀ hKs₀ hKt₀ hχT z]
  have hid := ω.integral_stdComplexLineEnergyDensity_eq_integral_associatedBilinForm
    (μ := volume) h₀.invariant hχ hc
  simp only [stdComplexLineEnergyDensity_def, ContinuousLinearMap.coe_coe] at hid
  have hlow : a * ∫ z, (‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2) ≤
      ∫ z, (ω.associatedBilinForm J₀ (fderiv ℝ χ z stdComplexLineReal)
          (fderiv ℝ χ z stdComplexLineReal) +
        ω.associatedBilinForm J₀ (fderiv ℝ χ z stdComplexLineImag)
          (fderiv ℝ χ z stdComplexLineImag)) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ by positivity) ?_
      (Eventually.of_forall fun z ↦ ?_)
    · simpa [stdComplexLineEnergyDensity_def] using
        ω.integrable_stdComplexLineEnergyDensity_fderiv (J := J₀) (μ := volume)
          (hχ.of_le one_le_two) hc
    · have h1 := (hab () trivial (fderiv ℝ χ z stdComplexLineReal)).1
      have h2 := (hab () trivial (fderiv ℝ χ z stdComplexLineImag)).1
      simp only at h1 h2 ⊢
      linarith
  have hup : ∫ z, ω.associatedBilinForm J₀ (F z) (F z) ≤ ∫ z, b * ‖F z‖ ^ 2 :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun z ↦ (mul_nonneg ha.le (sq_nonneg _)).trans (hab () trivial _).1)
      ((hF.integrable_norm_sq_of_hasCompactSupport hFc).const_mul b)
      (Eventually.of_forall fun z ↦ (hab () trivial _).2)
  rw [hD, div_mul_eq_mul_div, le_div_iff₀' ha]
  rw [integral_const_mul] at hup
  exact (hlow.trans_eq hid).trans hup

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Off the disc `‖w‖ < R` the weight `|w|⁻⁴` is at most `R⁻⁴`, and it dominates the weight
`(1 + |w|²)⁻²` of the sphere. -/
private theorem inv_sq_mul_norm_sq_le {χ : ℝ × ℝ → V} {R : ℝ} (hR : 0 < R)
    (hχR : ∀ z : ℝ × ℝ, ‖z‖ < R → χ z = 0) (z : ℝ × ℝ) :
    ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 ≤ ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 ∧
      ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 ≤ ((R ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 := by
  by_cases hχz : χ z = 0
  · simp [hχz]
  have hzR : R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 :=
    (pow_le_pow_left₀ hR.le (not_lt.1 fun h ↦ hχz (hχR z h)) 2).trans
      (Prod.norm_sq_le_sq_add_sq z)
  have hR2 : 0 < R ^ 2 := by positivity
  constructor <;> gcongr <;> nlinarith

omit [FiniteDimensional ℝ V] in
/-- **Splitting the `W^{1,2}` norm on the sphere.** If `ξ = ξ₁ + χ`, where `χ` vanishes on the
disc `‖w‖ < R`, the squared `W^{1,2}` norm of `ξ` on the sphere is at most twice the sum of the
`L²` norm of `ξ₁`, the weighted `L²` norm of `χ` near infinity and the two Dirichlet energies. -/
private theorem integral_le_of_eq_add {ξ ξ₁ χ : ℝ × ℝ → V} {R : ℝ} (hR : 0 < R)
    (hξ₁ : ContDiff ℝ 1 ξ₁) (hχ : ContDiff ℝ 1 χ) (hξ₁c : HasCompactSupport ξ₁)
    (hχc : HasCompactSupport χ) (hsplit : ξ = ξ₁ + χ) (hχR : ∀ z : ℝ × ℝ, ‖z‖ < R → χ z = 0) :
    ∫ z, (((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖ξ z‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
      2 * (∫ z, ‖ξ₁ z‖ ^ 2) + 2 * (∫ z, ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2) +
        2 * (∫ z, (‖fderiv ℝ ξ₁ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₁ z stdComplexLineImag‖ ^ 2)) +
        2 * ∫ z, (‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hsq (a b : V) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h := norm_smul_add_smul_sq_le (1 : ℝ) 1 a b
    rw [one_smul, one_smul] at h
    linarith
  set f₁ : ℝ × ℝ → ℝ := fun z ↦ ‖ξ₁ z‖ ^ 2
  set f₂ : ℝ × ℝ → ℝ := fun z ↦ ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2
  set f₃ : ℝ × ℝ → ℝ := fun z ↦ ‖fderiv ℝ ξ₁ z stdComplexLineReal‖ ^ 2 +
    ‖fderiv ℝ ξ₁ z stdComplexLineImag‖ ^ 2
  set f₄ : ℝ × ℝ → ℝ := fun z ↦ ‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 +
    ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2
  have i₁ := (hξ₁.continuous.integrable_norm_sq_of_hasCompactSupport (μ := volume) hξ₁c).const_mul 2
  have hf₂ : Integrable f₂ :=
    ((hχ.continuous.integrable_norm_sq_of_hasCompactSupport hχc).const_mul ((R ^ 2) ^ 2)⁻¹).mono'
      (((by fun_prop : Continuous fun z : ℝ × ℝ ↦ (z.1 ^ 2 + z.2 ^ 2) ^ 2).measurable.inv.mul
        (hχ.continuous.norm.pow 2).measurable).aestronglyMeasurable)
      (Eventually.of_forall fun z ↦ by
        rw [Real.norm_of_nonneg (by simp only [f₂]; positivity)]
        exact (inv_sq_mul_norm_sq_le hR hχR z).2)
  have i₂ := hf₂.const_mul 2
  have i₃ := (integrable_norm_fderiv_sq_add (μ := volume) hξ₁ hξ₁c stdComplexLineReal
    stdComplexLineImag).const_mul 2
  have i₄ := (integrable_norm_fderiv_sq_add (μ := volume) hχ hχc stdComplexLineReal
    stdComplexLineImag).const_mul 2
  have hsum : 2 * (∫ z, f₁ z) + 2 * (∫ z, f₂ z) + 2 * (∫ z, f₃ z) + 2 * ∫ z, f₄ z =
      ∫ z, (2 * f₁ z + 2 * f₂ z + 2 * f₃ z + 2 * f₄ z) := by
    rw [integral_add (f := fun z ↦ 2 * f₁ z + 2 * f₂ z + 2 * f₃ z) (g := fun z ↦ 2 * f₄ z)
        ((i₁.add i₂).add i₃) i₄,
      integral_add (f := fun z ↦ 2 * f₁ z + 2 * f₂ z) (g := fun z ↦ 2 * f₃ z) (i₁.add i₂) i₃,
      integral_add (f := fun z ↦ 2 * f₁ z) (g := fun z ↦ 2 * f₂ z) i₁ i₂, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hsum]
  refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ by positivity)
    (((i₁.add i₂).add i₃).add i₄) (Eventually.of_forall fun z ↦ ?_)
  have hd (v : ℝ × ℝ) : fderiv ℝ ξ z v = fderiv ℝ ξ₁ z v + fderiv ℝ χ z v := by
    rw [hsplit, fderiv_add (hξ₁.differentiable one_ne_zero z) (hχ.differentiable one_ne_zero z),
      add_apply]
  have hρ1 : ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hρ0 : 0 ≤ ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ := by positivity
  have h0 := hsq (ξ₁ z) (χ z)
  have h1 := hsq (fderiv ℝ ξ₁ z stdComplexLineReal) (fderiv ℝ χ z stdComplexLineReal)
  have h2 := hsq (fderiv ℝ ξ₁ z stdComplexLineImag) (fderiv ℝ χ z stdComplexLineImag)
  simp only [f₁, f₂, f₃, f₄]
  rw [congrFun hsplit z, hd, hd]
  simp only [Pi.add_apply]
  nlinarith [(inv_sq_mul_norm_sq_le hR hχR z).1, mul_le_mul_of_nonneg_left h0 hρ0,
    sq_nonneg ‖ξ₁ z‖, mul_le_mul_of_nonneg_right hρ1 (sq_nonneg ‖ξ₁ z‖)]

/-- **The interior estimate for a section supported in `K`.** If the interior estimate holds on
`K` with constant `C₁`, a `C²` section `ξ₁` supported in `K` with `∫ ‖D_u ξ₁‖² ≤ c` and
`∫_K ‖ξ₁‖² ≤ d` has Dirichlet energy at most `C₁ (c + d)`. -/
private theorem integral_dirichlet_le_of_tsupport_subset
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {K : Set (ℝ × ℝ)} {C₁ c d : ℝ} (hC₁ : 0 ≤ C₁)
    (hint : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → tsupport ξ ⊆ K →
      ∫ z in K, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C₁ * ∫ z in K, (‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 + ‖ξ z‖ ^ 2))
    {ξ₁ : ℝ × ℝ → V} (hξ₁ : ContDiff ℝ 2 ξ₁) (hξ₁c : HasCompactSupport ξ₁) (hξ₁K : tsupport ξ₁ ⊆ K)
    (hD : ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      Ks Kt u ξ₁ z‖ ^ 2 ≤ c) (hL : ∫ z in K, ‖ξ₁ z‖ ^ 2 ≤ d) :
    ∫ z, (‖fderiv ℝ ξ₁ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ₁ z stdComplexLineImag‖ ^ 2) ≤
      C₁ * (c + d) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hiD₁ := ω.integrable_norm_floerLinearization_sq (μ := volume)
    (ω.continuous_floerLinearization
      (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu
      (hξ₁.of_le one_le_two)) hξ₁c
  have hiξ₁ := hξ₁.continuous.integrable_norm_sq_of_hasCompactSupport (μ := volume) hξ₁c
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun z hz ↦ by
    simp [Function.notMem_support.1 fun h ↦ hz (hξ₁K (support_fderiv_subset ℝ h))]]
  refine (hint hξ₁ hξ₁K).trans (mul_le_mul_of_nonneg_left ?_ hC₁)
  rw [integral_add hiD₁.integrableOn hiξ₁.integrableOn]
  linarith [setIntegral_le_integral (s := K) hiD₁ (Eventually.of_forall fun _ ↦ sq_nonneg _)]

/-- The arithmetic combining the four bounds of the proof of `integral_le_of_bump`. -/
private theorem add_le_of_bounds {X₁ X₂ X₃ X₄ ID IK C₁ C₂ M R : ℝ} (h₁ : X₁ ≤ IK)
    (h₂ : X₂ ≤ (4 / R) ^ 2 * X₄) (h₃ : X₃ ≤ C₁ * (2 * ID + M * IK + IK))
    (h₄ : X₄ ≤ C₂ * (2 * ID + M * IK)) (hID : 0 ≤ ID) (hIK : 0 ≤ IK) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hM : 0 ≤ M) :
    2 * X₁ + 2 * X₂ + 2 * X₃ + 2 * X₄ ≤
      (2 + 2 * C₁ * (M + 3) + (2 + 2 * (4 / R) ^ 2) * C₂ * (M + 2)) * (ID + IK) := by
  have h₃' : C₁ * (2 * ID + M * IK + IK) ≤ C₁ * (M + 3) * (ID + IK) := by
    rw [mul_assoc C₁]
    exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hM hID]) hC₁
  have h₄' : C₂ * (2 * ID + M * IK) ≤ C₂ * (M + 2) * (ID + IK) := by
    rw [mul_assoc C₂]
    exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hM hID]) hC₂
  have h₂' := mul_le_mul_of_nonneg_left (h₄.trans h₄') (sq_nonneg (4 / R))
  nlinarith [h₃.trans h₃', h₄.trans h₄']

/-- **The estimate for one section.** Let `β` be a `C²` bump function with `0 ≤ β ≤ 1`, equal to
`1` on the square `‖w‖ ≤ R` and supported in `K = {‖w‖ ≤ 2 R}`, such that multiplying `ξ` by `β`
or by `1 - β` costs at most `M ∫_K ‖ξ‖²` in `∫ ‖D_u ·‖²`
(`TauCeti.SymplecticForm.exists_integral_norm_floerLinearization_smul_sq_le`). Given the interior
estimate on `K`, with constant `C₁`, and the estimate near infinity on sections vanishing on
`‖w‖ < R`, with constant `C₂`, the squared `W^{1,2}` norm of `ξ` on the sphere is bounded by
`∫ ‖D_u ξ‖²` and the `L²` norm of `ξ` on `K`. -/
private theorem integral_le_of_bump
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {β : ℝ × ℝ → ℝ} {R M C₁ C₂ : ℝ} (hR : 0 < R) (hβ : ContDiff ℝ 2 β)
    (hβ01 : ∀ z, β z ∈ Icc 0 1) (hβR : ∀ z : ℝ × ℝ, ‖z‖ ≤ R → β z = 1)
    (hβK : tsupport β ⊆ closedBall 0 (2 * R))
    (hC₁ : 0 ≤ C₁) (hint : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → tsupport ξ ⊆ closedBall 0 (2 * R) →
      ∫ z in closedBall 0 (2 * R), (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C₁ * ∫ z in closedBall 0 (2 * R), (‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 + ‖ξ z‖ ^ 2))
    (hC₂ : 0 ≤ C₂) (hinf : ∀ ⦃χ : ℝ × ℝ → V⦄, ContDiff ℝ 2 χ → HasCompactSupport χ →
      (∀ z : ℝ × ℝ, ‖z‖ < R → χ z = 0) →
      ∫ z, (‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2) ≤
        C₂ * ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u χ z‖ ^ 2)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) (hM : 0 ≤ M)
    (hY₁ : ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        Ks Kt u (fun w ↦ β w • ξ w) z‖ ^ 2 ≤ 2 * (∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
        M * ∫ z in closedBall 0 (2 * R), ‖ξ z‖ ^ 2)
    (hY₂ : ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        Ks Kt u (fun w ↦ (1 - β w) • ξ w) z‖ ^ 2 ≤ 2 * (∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
        M * ∫ z in closedBall 0 (2 * R), ‖ξ z‖ ^ 2) :
    ∫ z, (((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖ξ z‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
      (2 + 2 * C₁ * (M + 3) + (2 + 2 * (4 / R) ^ 2) * C₂ * (M + 2)) *
        ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ z‖ ^ 2) + ∫ z in closedBall 0 (2 * R), ‖ξ z‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set K := closedBall (0 : ℝ × ℝ) (2 * R)
  set ID := ∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
    Ks Kt u ξ z‖ ^ 2
  set IK := ∫ z in K, ‖ξ z‖ ^ 2
  -- The pieces `β ξ`, supported in `K`, and `χ = (1 - β) ξ`, vanishing on `‖w‖ < R`.
  set ξ₁ : ℝ × ℝ → V := fun w ↦ β w • ξ w
  set χ : ℝ × ℝ → V := fun w ↦ (1 - β w) • ξ w
  have hξ₁ : ContDiff ℝ 2 ξ₁ := hβ.smul hξ
  have hχ : ContDiff ℝ 2 χ := (contDiff_const.sub hβ).smul hξ
  have hξ₁c : HasCompactSupport ξ₁ := hξc.smul_left
  have hξ₁K : tsupport ξ₁ ⊆ K := (tsupport_smul_subset_left _ _).trans hβK
  have hχR (z : ℝ × ℝ) (hz : ‖z‖ < R) : χ z = 0 := by simp [χ, hβR z hz.le]
  have hξ₁ξ (z : ℝ × ℝ) : ‖ξ₁ z‖ ≤ ‖ξ z‖ := by
    simp only [ξ₁, norm_smul, Real.norm_of_nonneg (hβ01 z).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hβ01 z).2
  have hiξ := hξ.continuous.integrable_norm_sq_of_hasCompactSupport (μ := volume) hξc
  have hiξ₁ := hξ₁.continuous.integrable_norm_sq_of_hasCompactSupport (μ := volume) hξ₁c
  have hX₁ : ∫ z in K, ‖ξ₁ z‖ ^ 2 ≤ IK :=
    setIntegral_mono_on hiξ₁.integrableOn hiξ.integrableOn measurableSet_closedBall
      fun z _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hξ₁ξ z) 2
  have hX₃ := integral_dirichlet_le_of_tsupport_subset (ω := ω) hJ hKs hKt hu hC₁ hint hξ₁ hξ₁c
    hξ₁K (c := 2 * ID + M * IK) hY₁ hX₁
  have hX₄ := (hinf hχ ((hξc.smul_left (f := fun z ↦ 1 - β z))) hχR).trans
    (mul_le_mul_of_nonneg_left hY₂ hC₂)
  have hX₂ := integral_inv_sq_mul_norm_sq_le hR (hχ.of_le one_le_two)
    (hξc.smul_left (f := fun z ↦ 1 - β z)) fun z hz ↦ hχR z
      (lt_of_pow_lt_pow_left₀ 2 hR.le ((Prod.norm_sq_le_sq_add_sq z).trans_lt hz))
  simp only [← stdComplexLineReal_eq, ← stdComplexLineImag_eq] at hX₂
  have hX₁' : ∫ z, ‖ξ₁ z‖ ^ 2 ≤ IK := by
    rwa [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun z hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hξ₁K h)]]
  refine (integral_le_of_eq_add hR (hξ₁.of_le one_le_two) (hχ.of_le one_le_two) hξ₁c
    (hξc.smul_left (f := fun z ↦ 1 - β z)) (by funext w; simp [ξ₁, χ, sub_smul]) hχR).trans
    (add_le_of_bounds hX₁' hX₂ hX₃ hX₄ (integral_nonneg fun _ ↦ sq_nonneg _)
      (setIntegral_nonneg measurableSet_closedBall fun _ _ ↦ sq_nonneg _) hC₁ hC₂ hM)

/-- **The semi-Fredholm estimate on the Riemann sphere.** Let the Floer data `J`, `K_s`, `K_t` on
the plane `ℝ × ℝ ≅ ℂ` be the fixed `ω`-compatible structure `J₀` and the zero perturbation on
`‖w‖ ≥ T`, a neighbourhood of the point at infinity of the sphere. Let `J` be `C¹` and `K_s`, `K_t`
be `C²` along a `C¹` map `u`, with `J(w, u w)` compatible. Then there are `R` and `C ≥ 0` such that
every compactly supported `C²` section `ξ` satisfies

`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ R} ‖ξ‖²)`,  `ρ(w) = (1 + |w|²)⁻²`,

where the left side is the squared `W^{1,2}` norm of `ξ` on the sphere. -/
theorem exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    ∃ R C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      ∫ z, (((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖ξ z‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            Ks Kt u ξ z‖ ^ 2) + ∫ z in closedBall 0 R, ‖ξ z‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- `J₀` is the compatible structure `J` takes at a point far out.
  have h₀ : ω.Compatible J₀ :=
    hJ₀ (|T|, 0) (by simp [Prod.norm_def, le_abs_self]) (u (|T|, 0)) ▸ hc (|T|, 0)
  set R : ℝ := max T 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- A bump function `β`, equal to `1` on the square `‖w‖ ≤ R` and supported in `‖w‖ ≤ 2 R`.
  let β : ContDiffBump (0 : ℝ × ℝ) := ⟨R, 2 * R, hR, by linarith⟩
  -- The cost of multiplying by `β` and by `1 - β`, whose derivatives vanish off `‖w‖ ≤ 2 R`.
  have hβK (z : ℝ × ℝ) (hz : z ∉ closedBall 0 (2 * R)) : fderiv ℝ β z = 0 :=
    Function.notMem_support.1 fun h ↦ hz (β.tsupport_eq.subset (support_fderiv_subset ℝ h))
  obtain ⟨M₁, hM₁, hY₁⟩ := ω.exists_integral_norm_floerLinearization_smul_sq_le
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu
    (β.contDiff (n := 1)) (fun z ↦ ⟨β.nonneg, β.le_one⟩) (isCompact_closedBall 0 (2 * R)) hβK
  obtain ⟨M₂, -, hY₂⟩ := ω.exists_integral_norm_floerLinearization_smul_sq_le
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu
    (β := fun z ↦ 1 - β z) (contDiff_const.sub (β.contDiff (n := 1)))
    (fun z ↦ ⟨sub_nonneg.2 β.le_one, sub_le_self _ β.nonneg⟩) (isCompact_closedBall 0 (2 * R))
    fun z hz ↦ by rw [fderiv_const_sub, hβK z hz, neg_zero]
  have hY (M' : ℝ) (hM' : M' ≤ max M₁ M₂) {ξ : ℝ × ℝ → V} {X : ℝ}
      (h : X ≤ 2 * (∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
        M' * ∫ z in closedBall 0 (2 * R), ‖ξ z‖ ^ 2) :
      X ≤ 2 * (∫ z, ‖ω.floerLinearization
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) +
        max M₁ M₂ * ∫ z in closedBall 0 (2 * R), ‖ξ z‖ ^ 2 :=
    h.trans (add_le_add_right (mul_le_mul_of_nonneg_right hM'
      (setIntegral_nonneg measurableSet_closedBall fun _ _ ↦ sq_nonneg _)) _)
  -- The interior estimate on the disc, and the estimate near infinity.
  obtain ⟨C₁, hC₁, hint⟩ :=
   exists_forall_setIntegral_norm_fderiv_sq_le_mul_setIntegral_floerLinearization_of_tsupport_subset
      ω (μ := volume) (isCompact_closedBall (0 : ℝ × ℝ) (2 * R)) (fun z _ ↦ hJ z)
      (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt) fun z _ ↦ hc z
  obtain ⟨C₂, hC₂, hinf⟩ := exists_forall_integral_norm_fderiv_sq_le_of_eq_base (u := u) h₀ hJ₀
    hKs₀ hKt₀
  refine ⟨2 * R, _, by positivity, fun ξ hξ hξc ↦ integral_le_of_bump hJ hKs hKt hu hR
    β.contDiff (fun z ↦ ⟨β.nonneg, β.le_one⟩)
    (fun z hz ↦ β.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hz)) β.tsupport_eq.subset
    hC₁ hint hC₂ (fun χ hχ hχc h ↦ hinf hχ hχc fun z hz ↦ h z (hz.trans_le (le_max_left _ _)))
    hξ hξc (hM₁.trans (le_max_left _ _))
    (hY M₁ (le_max_left _ _) (hY₁ (hξ.of_le one_le_two) hξc))
    (hY M₂ (le_max_right _ _) (hY₂ (hξ.of_le one_le_two) hξc))⟩
end TauCeti.SymplecticForm
