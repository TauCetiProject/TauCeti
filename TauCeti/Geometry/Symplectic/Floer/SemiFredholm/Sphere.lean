/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Complex.EquivRealProd
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

The proof splits the plane at a Euclidean disc `|w| ≤ 2 R + 1`.

* On the disc, the estimate of the linearized operator on a disc
  (`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt`),
  which combines the interior estimate with the cost of a cutoff, bounds the `W^{1,2}` norm of `ξ`.
* Off the disc, `ξ` agrees with `χ = (1 - ψ) ξ`, where the cutoff `ψ` is `1` on `|w| ≤ 2 R`, and
  multiplying by `1 - ψ` only adds the `L²` norm of `ξ` on a disc to `∫ ‖D_u ·‖²`. Where `χ` lives,
  `D_u χ = ∂s χ + J₀ ∂t χ` is the Cauchy–Riemann operator of `J₀`, and the energy identity for
  compactly supported maps
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
/-- Off the disc `|w| < R` the weight `|w|⁻⁴` is at most `R⁻⁴`, and it dominates the weight
`(1 + |w|²)⁻²` of the sphere. -/
private theorem inv_sq_mul_norm_sq_le {χ : ℝ × ℝ → V} {R : ℝ} (hR : 0 < R)
    (hχR : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < R ^ 2 → χ z = 0) (z : ℝ × ℝ) :
    ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 ≤ ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 ∧
      ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 ≤ ((R ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 := by
  by_cases hχz : χ z = 0
  · simp [hχz]
  have hzR : R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := not_lt.1 fun h ↦ hχz (hχR z h)
  have hR2 : 0 < R ^ 2 := by positivity
  constructor <;> gcongr <;> nlinarith

omit [FiniteDimensional ℝ V] in
/-- **The `W^{1,2}` norm on the sphere near infinity.** A compactly supported `C¹` map `χ`
vanishing on the disc `|w| < R` has squared `W^{1,2}` norm on the sphere at most `1 + (4 / R)²`
times its Dirichlet energy, by the Poincaré inequality at infinity. -/
private theorem integral_le_mul_integral_norm_fderiv_sq {χ : ℝ × ℝ → V} {R : ℝ} (hR : 0 < R)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχR : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < R ^ 2 → χ z = 0) :
    ∫ z, (((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 +
        ‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2) ≤
      (1 + (4 / R) ^ 2) * ∫ z, (‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hD := integrable_norm_fderiv_sq_add (μ := volume) hχ hχc stdComplexLineReal
    stdComplexLineImag
  have hw : Integrable fun z : ℝ × ℝ ↦ ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 :=
    ((hχ.continuous.integrable_norm_sq_of_hasCompactSupport hχc).const_mul ((R ^ 2) ^ 2)⁻¹).mono'
      (((by fun_prop : Continuous fun z : ℝ × ℝ ↦ (z.1 ^ 2 + z.2 ^ 2) ^ 2).measurable.inv.mul
        (hχ.continuous.norm.pow 2).measurable).aestronglyMeasurable)
      (Eventually.of_forall fun z ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact (inv_sq_mul_norm_sq_le hR hχR z).2)
  have hP := integral_inv_sq_mul_norm_sq_le hR hχ hχc hχR
  simp only [← stdComplexLineReal_eq, ← stdComplexLineImag_eq] at hP
  calc _ ≤ ∫ z, (((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 +
        (‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z ↦ by positivity) (hw.add hD)
          (Eventually.of_forall fun z ↦ by linarith [(inv_sq_mul_norm_sq_le hR hχR z).1])
    _ = _ := integral_add hw hD
    _ ≤ _ := by rw [add_mul, one_mul, add_comm]; exact add_le_add_right hP _

omit [FiniteDimensional ℝ V] in
/-- **Splitting the `W^{1,2}` norm on the sphere at a disc.** If `χ` agrees with `ξ` on `|w| > a`,
the squared `W^{1,2}` norm of `ξ` on the sphere is at most its squared `W^{1,2}` norm on the disc
`|w| ≤ a` plus the squared `W^{1,2}` norm of `χ` on the sphere. -/
private theorem integral_le_setIntegral_add_integral {ξ χ : ℝ × ℝ → V} {a : ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) (hχξ : ∀ z, a < ‖Complex.equivRealProdCLM.symm z‖ → χ z = ξ z) :
    ∫ z, (((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖ξ z‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
      (∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a},
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2)) +
        ∫ z, (((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 +
          ‖fderiv ℝ χ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ χ z stdComplexLineImag‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hρ1 (z : ℝ × ℝ) : ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith)
  have hint {η : ℝ × ℝ → V} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
      Integrable fun z ↦ ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖η z‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 := by
    have hρη : Integrable fun z ↦ ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖η z‖ ^ 2 :=
      (hη.continuous.integrable_norm_sq_of_hasCompactSupport hηc).mono'
        ((by fun_prop : Continuous fun z : ℝ × ℝ ↦ (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2).measurable.inv.mul
          (hη.continuous.norm.pow 2).measurable).aestronglyMeasurable
        (Eventually.of_forall fun z ↦ by
          rw [Real.norm_of_nonneg (by positivity)]
          exact mul_le_of_le_one_left (by positivity) (hρ1 z))
    refine (hρη.add (integrable_norm_fderiv_sq_add hη hηc stdComplexLineReal
      stdComplexLineImag)).congr (Eventually.of_forall fun z ↦ ?_)
    simp only [Pi.add_apply, add_assoc]
  have hD : MeasurableSet {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ a} :=
    measurableSet_le Complex.equivRealProdCLM.symm.continuous.norm.measurable measurable_const
  rw [← integral_add_compl hD (hint hξ hξc)]
  refine add_le_add (setIntegral_mono_on (hint hξ hξc).integrableOn
    ((integrable_norm_fderiv_sq_add hξ hξc _ _).add
      (hξ.continuous.integrable_norm_sq_of_hasCompactSupport hξc)).integrableOn hD
    fun z _ ↦ by nlinarith [hρ1 z, sq_nonneg ‖ξ z‖]) ?_
  -- Off the disc, `ξ` agrees with `χ` on a neighbourhood of each point.
  refine le_of_eq_of_le (setIntegral_congr_fun hD.compl fun z hz ↦ ?_)
    (setIntegral_le_integral (hint hχ hχc) (Eventually.of_forall fun z ↦ by positivity))
  have hev : χ =ᶠ[𝓝 z] ξ :=
    mem_of_superset ((isOpen_lt continuous_const
      Complex.equivRealProdCLM.symm.continuous.norm).mem_nhds (not_le.1 hz)) fun w hw ↦ hχξ w hw
  simp only [hev.fderiv_eq, hev.eq_of_nhds]

/-- The arithmetic combining the bounds of the proof of
`exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base`. -/
private theorem le_mul_add_of_bounds {L X Y E F ID IB IK IS C₁ C₂ M P : ℝ} (h₁ : L ≤ X + Y)
    (h₂ : X ≤ C₁ * (ID + IB)) (h₃ : Y ≤ P * E) (h₄ : E ≤ C₂ * F) (h₅ : F ≤ 2 * ID + M * IK)
    (hIB : IB ≤ IS) (hIK : IK ≤ IS) (hID : 0 ≤ ID) (hIS : 0 ≤ IS) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hM : 0 ≤ M) (hP : 0 ≤ P) :
    L ≤ (C₁ + P * C₂ * (M + 2)) * (ID + IS) := by
  have hF : F ≤ (M + 2) * (ID + IS) := by nlinarith [mul_le_mul_of_nonneg_left hIK hM]
  have hX : X ≤ C₁ * (ID + IS) := h₂.trans (by gcongr)
  have hY : Y ≤ P * (C₂ * ((M + 2) * (ID + IS))) := h₃.trans (by gcongr; exact h₄.trans (by gcongr))
  nlinarith

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
  -- A cutoff `ψ`, equal to `1` near the disc `|w| ≤ 2 R` and to `0` near `|w| ≥ 2 R + 1`.
  obtain ⟨ψ, hψ, hψ01, hψ1, hψ0, hψK, -⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * R)).exists_contDiff_cutoff_sublevel
      Complex.equivRealProdCLM.symm.continuous.norm (lt_add_one (2 * R))
  have hψ2 : ContDiff ℝ 2 fun z ↦ 1 - ψ z := contDiff_const.sub (hψ.of_le (by simp))
  -- The cost of multiplying by `1 - ψ`, the disc estimate and the estimate near infinity.
  obtain ⟨M, hM, hY⟩ := ω.exists_integral_norm_floerLinearization_smul_sq_le
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) hJ hKs hKt hu
    (hψ2.of_le one_le_two) (fun z ↦ ⟨sub_nonneg.2 (hψ01 z).2, sub_le_self _ (hψ01 z).1⟩)
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * R + 1))
    fun z hz ↦ by rw [fderiv_const_sub, hψK z (not_le.1 hz), neg_zero]
  obtain ⟨C₁, hC₁, hdisc⟩ :=
    ω.exists_forall_setIntegral_le_mul_integral_floerLinearization_add_of_lt hJ hKs hKt hu
      (a := 2 * R + 1) (b := 2 * R + 2) (fun z _ ↦ hc z) (by linarith)
  obtain ⟨C₂, hC₂, hinf⟩ := exists_forall_integral_norm_fderiv_sq_le_of_eq_base (u := u) h₀ hJ₀
    hKs₀ hKt₀
  refine ⟨2 * R + 2, C₁ + (1 + (4 / (2 * R)) ^ 2) * C₂ * (M + 2), by positivity,
    fun ξ hξ hξc ↦ ?_⟩
  -- `χ = (1 - ψ) ξ` vanishes on `|w| ≤ 2 R` and agrees with `ξ` on `|w| > 2 R + 1`.
  set χ : ℝ × ℝ → V := fun w ↦ (1 - ψ w) • ξ w
  have hχc : HasCompactSupport χ := hξc.smul_left
  have hχ0 (z : ℝ × ℝ) (hz : ‖Complex.equivRealProdCLM.symm z‖ ≤ 2 * R) : χ z = 0 := by
    simp [χ, (hψ1 z hz).eq_of_nhds]
  -- The `L²` norms of `ξ` on the discs are at most the one on the square `‖w‖ ≤ 2 R + 2`.
  have hsq (r : ℝ) (hr : r ≤ 2 * R + 2) : ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ r},
      ‖ξ z‖ ^ 2 ≤ ∫ z in closedBall 0 (2 * R + 2), ‖ξ z‖ ^ 2 :=
    setIntegral_mono_set (hξ.continuous.integrable_norm_sq_of_hasCompactSupport hξc).integrableOn
      (Eventually.of_forall fun _ ↦ sq_nonneg _) (Eventually.of_forall fun z (hz : _ ≤ r) ↦
        mem_closedBall_zero_iff.2 (((norm_le_norm_equivRealProdCLM_symm z).trans hz).trans hr))
  exact le_mul_add_of_bounds
    (integral_le_setIntegral_add_integral (hξ.of_le one_le_two) hξc
      ((hψ2.smul hξ).of_le one_le_two) hχc fun z hz ↦ by simp [(hψ0 z hz.le).eq_of_nhds])
    (hdisc hξ hξc)
    (integral_le_mul_integral_norm_fderiv_sq (R := 2 * R) (by positivity)
      ((hψ2.smul hξ).of_le one_le_two) hχc fun z hz ↦ hχ0 z (lt_of_pow_lt_pow_left₀ 2
        (by positivity) ((sq_norm_equivRealProdCLM_symm z).trans_lt hz)).le)
    (hinf (hψ2.smul hξ) hχc fun z hz ↦ hχ0 z ((norm_equivRealProdCLM_symm_le_two_mul z).trans
      (by linarith [le_max_left T 1])))
    (hY (hξ.of_le one_le_two) hξc) (hsq _ (by linarith)) (hsq _ (by linarith))
    (integral_nonneg fun _ ↦ sq_nonneg _)
    (setIntegral_nonneg measurableSet_closedBall fun _ _ ↦ sq_nonneg _) hC₁ hC₂ hM (by positivity)
end TauCeti.SymplecticForm
