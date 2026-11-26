/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RealChart
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Sobolev.Poincare.Infinity
import TauCeti.Analysis.Sobolev.Poincare.Slab
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Floer.InteriorEstimate
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.CompactSupport
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Constructions.SumProd

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

**The formal adjoint.** The cokernel of `D_u` is the kernel of its formal adjoint `D_u^*` on
covector fields (`TauCeti.SymplecticForm.floerLinearizationAdjoint`), and the finiteness of the
cokernel rests on the same kind of estimate for `D_u^*`. A covector field `η` is a `(0, 1)`-form,
so near the point at infinity it is read in the chart `ζ = w⁻¹` of the sphere as the form
`η' = η (ζ⁻¹) ∘ (a + b J)` (`TauCeti.Floer.covectorPullback` along the inversion, in real
coordinates `TauCeti.Complex.realChart (·⁻¹)`). The squared `W^{1,2}` norm of `η` on the sphere is
`∫_{|w| ≤ R} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) + ∫_{|ζ| ≤ R⁻¹} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²)`, and it
is at most `C (∫ (1 + |w|²)² ‖D_u^* η‖² + ∫_{‖w‖ ≤ R + 1} ‖η‖²)`
(`exists_forall_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_eq_base`).
The weight `(1 + |w|²)²` is the inverse of `ρ`, as for the dual of `W^{1,2}`.

* On the disc `|w| ≤ R`, a cutoff reduces the estimate to the `L²` estimate of the adjoint on
  compact sets
  (`exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add`).
* Near infinity the data are `J₀` and `0`, and the adjoint is `-ω♭ (∂s ζ - J₀ ∂t ζ)` for
  `ζ = ω♭⁻¹ ∘ η` (`TauCeti.SymplecticForm.floerLinearizationAdjoint_eq_neg_flatEquiv`), a
  Cauchy–Riemann operator for `-J₀`, which preserves `ω`. Its energy identity
  (`TauCeti.SymplecticForm.integral_stdComplexLineEnergyDensity_eq_integral_associatedBilinForm`)
  bounds the Dirichlet energy by the `L²` norm of the adjoint, with no lower-order term. Applied in
  the chart `ζ`, where the field is supported in a bounded disc and the Poincaré inequality on a
  strip controls its `L²` norm, this bounds the `W^{1,2}` norm of `η'`. The inversion multiplies
  the adjoint by its Jacobian `|w|⁴`
  (`TauCeti.SymplecticForm.floerLinearizationAdjoint_perturbationPullback`), and the change of
  variables along the inversion absorbs one Jacobian, which leaves the weight `|w|⁴ ≤ (1 + |w|²)²`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate of Cauchy–Riemann operators on closed surfaces,
  and Appendix C.1, on the formal adjoint of a real Cauchy–Riemann operator.
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
  obtain ⟨ψ, hψ, hψ01, hψ1, hψ0, hψK⟩ :=
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
/-! ### The formal adjoint -/

/-- **The formal adjoint of constant data.** For a constant `ω`-invariant structure `J₀` and the
zero perturbation, the formal adjoint is `-ω♭ (∂s ζ - J₀ ∂t ζ)` for `ζ = ω♭⁻¹ ∘ η`, along any map:
a Cauchy–Riemann operator for `-J₀`. -/
private theorem floerLinearizationAdjoint_const_eq (u : ℝ × ℝ → V) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η z) (h : ω.Invariant J₀) :
    ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) u η z =
      -ω.flatEquiv (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η w)) z stdComplexLineReal +
        (-J₀) (fderiv ℝ (fun w ↦ ω.flatEquiv.symm (η w)) z stdComplexLineImag)) := by
  have h0 : ω.floerLinearizationCoeff (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z = 0 := by
    ext v
    simp [floerLinearizationCoeff_apply]
  rw [ω.floerLinearizationAdjoint_eq_neg_flatEquiv (J := fun _ _ ↦ J₀) hη
    (differentiableAt_const _) h, h0]
  simp

/-- **The energy estimate for the adjoint of constant data.** For a constant `ω`-compatible
structure `J₀` and the zero perturbation, the Dirichlet energy of a compactly supported `C²`
covector field is controlled by the `L²` norm of its formal adjoint, with no lower-order term. This
is the energy identity for the Cauchy–Riemann operator of `-J₀`, which preserves `ω` and whose
associated form `ω(·, -J₀ ·)` is minus the metric of `J₀`. -/
private theorem exists_forall_integral_norm_fderiv_sq_le_of_const (h₀ : ω.Compatible J₀) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2) ≤
        C * ∫ z, ‖ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η z‖ ^ 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    (J := fun _ : Unit ↦ J₀) isCompact_univ continuousOn_const fun _ _ ↦ h₀.tames
  set c₁ := ‖(ω.flatEquiv : (V →L[ℝ] (V →L[ℝ] ℝ)))‖
  set c₂ := ‖(ω.flatEquiv.symm : (V →L[ℝ] ℝ) →L[ℝ] V)‖
  refine ⟨c₁ ^ 2 * (b / a) * c₂ ^ 2, by positivity, fun η hη hc ↦ ?_⟩
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set ζ : ℝ × ℝ → V := fun w ↦ ω.flatEquiv.symm (η w)
  have hζ : ContDiff ℝ 2 ζ := ω.flatEquiv.symm.contDiff.comp hη
  have hζc : HasCompactSupport ζ := hc.comp_left (map_zero _)
  have hdζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv two_ne_zero
  set F : ℝ × ℝ → V := fun z ↦ fderiv ℝ ζ z stdComplexLineReal +
    (-J₀) (fderiv ℝ ζ z stdComplexLineImag)
  have hF : Continuous F := (hdζ.clm_apply continuous_const).add
    ((-J₀).toLinearMap.toContinuousLinearMap.continuous.comp (hdζ.clm_apply continuous_const))
  have hFc : HasCompactSupport F :=
    (hζc.fderiv_apply (𝕜 := ℝ) stdComplexLineReal).add
      ((hζc.fderiv_apply (𝕜 := ℝ) stdComplexLineImag).comp_left (map_zero (-J₀).toLinearMap))
  -- `D₀^* η = -ω♭ F`.
  have hD (z : ℝ × ℝ) : ω.floerLinearizationAdjoint
      (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η z =
      -ω.flatEquiv (F z) :=
    floerLinearizationAdjoint_const_eq 0 (hη.differentiable two_ne_zero z) h₀.invariant
  -- The energy identity for `-J₀`, whose associated form is `-g₀`.
  have hinv : ω.Invariant (-J₀) := by
    have h := h₀.invariant
    rw [invariant_iff] at h ⊢
    intro v w
    simp [h]
  have hid := ω.integral_stdComplexLineEnergyDensity_eq_integral_associatedBilinForm
    (μ := volume) hinv hζ hζc
  have hneg (v w : V) : ω.associatedBilinForm (-J₀) v w = -ω.associatedBilinForm J₀ v w := by
    simp
  simp only [stdComplexLineEnergyDensity_def, hneg, ContinuousLinearMap.coe_coe, ← neg_add,
    integral_neg, neg_inj] at hid
  -- Pointwise bounds.
  have hη' (z v : ℝ × ℝ) : fderiv ℝ η z v = ω.flatEquiv (fderiv ℝ ζ z v) := by
    simp [ζ, fderiv_flatEquiv_symm_apply]
  have h1 (z : ℝ × ℝ) : ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 ≤ c₁ ^ 2 *
      (‖fderiv ℝ ζ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ζ z stdComplexLineImag‖ ^ 2) := by
    have e1 := (ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ)).le_opNorm (fderiv ℝ ζ z stdComplexLineReal)
    have e2 := (ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ)).le_opNorm (fderiv ℝ ζ z stdComplexLineImag)
    simp only [ContinuousLinearEquiv.coe_coe] at e1 e2
    rw [hη', hη', mul_add, ← mul_pow, ← mul_pow]
    gcongr
  have h2 (z : ℝ × ℝ) : a * (‖fderiv ℝ ζ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ζ z stdComplexLineImag‖ ^ 2) ≤
      ω.associatedBilinForm J₀ (fderiv ℝ ζ z stdComplexLineReal)
          (fderiv ℝ ζ z stdComplexLineReal) +
        ω.associatedBilinForm J₀ (fderiv ℝ ζ z stdComplexLineImag)
          (fderiv ℝ ζ z stdComplexLineImag) := by
    rw [mul_add]
    exact add_le_add (hab () trivial _).1 (hab () trivial _).1
  have h4 (z : ℝ × ℝ) : ‖F z‖ ≤ c₂ * ‖ω.floerLinearizationAdjoint
      (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η z‖ := by
    have e := (ω.flatEquiv.symm : (V →L[ℝ] ℝ) →L[ℝ] V).le_opNorm (ω.flatEquiv (F z))
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at e
    rw [hD z, norm_neg]
    exact e
  -- Integrability.
  have iη := integrable_norm_fderiv_sq_add (μ := volume) (hη.of_le one_le_two) hc
    stdComplexLineReal stdComplexLineImag
  have iζ := integrable_norm_fderiv_sq_add (μ := volume) (hζ.of_le one_le_two) hζc
    stdComplexLineReal stdComplexLineImag
  have ig : Integrable fun z ↦ ω.associatedBilinForm J₀ (fderiv ℝ ζ z stdComplexLineReal)
      (fderiv ℝ ζ z stdComplexLineReal) + ω.associatedBilinForm J₀
        (fderiv ℝ ζ z stdComplexLineImag) (fderiv ℝ ζ z stdComplexLineImag) := by
    simpa [stdComplexLineEnergyDensity_def] using
      ω.integrable_stdComplexLineEnergyDensity_fderiv (J := J₀) (μ := volume)
        (hζ.of_le one_le_two) hζc
  have iD : Integrable fun z ↦ ‖ω.floerLinearizationAdjoint
      (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η z‖ ^ 2 := by
    simp only [hD, norm_neg]
    exact (ω.flatEquiv.continuous.comp hF).integrable_norm_sq_of_hasCompactSupport
      (hFc.comp_left (map_zero _))
  calc _ ≤ ∫ z, c₁ ^ 2 * (‖fderiv ℝ ζ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ζ z stdComplexLineImag‖ ^ 2) := integral_mono iη (iζ.const_mul _) h1
    _ ≤ ∫ z, c₁ ^ 2 / a * (ω.associatedBilinForm J₀ (fderiv ℝ ζ z stdComplexLineReal)
          (fderiv ℝ ζ z stdComplexLineReal) + ω.associatedBilinForm J₀
            (fderiv ℝ ζ z stdComplexLineImag) (fderiv ℝ ζ z stdComplexLineImag)) := by
        refine integral_mono (iζ.const_mul _) (ig.const_mul _) fun z ↦ ?_
        have := h2 z
        rw [div_mul_eq_mul_div, le_div_iff₀ ha]
        nlinarith [sq_nonneg c₁]
    _ = c₁ ^ 2 / a * ∫ z, ω.associatedBilinForm J₀ (F z) (F z) := by
        rw [integral_const_mul, hid]
    _ ≤ c₁ ^ 2 / a * ∫ z, b * c₂ ^ 2 * ‖ω.floerLinearizationAdjoint
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η
            z‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (Eventually.of_forall fun z ↦ (mul_nonneg ha.le (sq_nonneg _)).trans
            (hab () trivial _).1) (iD.const_mul _) (Eventually.of_forall fun z ↦ ?_))
          (by positivity)
        refine (hab () trivial _).2.trans ?_
        dsimp only
        rw [mul_assoc, ← mul_pow]
        gcongr
        exact h4 z
    _ = _ := by rw [integral_const_mul]; field_simp

/-- The inversion `ζ ↦ ζ⁻¹`, read in real coordinates, is an involution. -/
private theorem realChart_inv_realChart_inv (ζ : ℝ × ℝ) :
    TauCeti.Complex.realChart (·⁻¹) (TauCeti.Complex.realChart (·⁻¹) ζ) = ζ := by
  rw [TauCeti.Complex.realChart_apply, TauCeti.Complex.equivRealProdCLM_symm_realChart, inv_inv,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The inversion inverts the Euclidean norm. -/
private theorem norm_symm_realChart_inv (ζ : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ =
      ‖Complex.equivRealProdCLM.symm ζ‖⁻¹ := by
  rw [TauCeti.Complex.equivRealProdCLM_symm_realChart, norm_inv]

/-- Away from `0`, the inversion has complex derivative `-ζ⁻²`. -/
private theorem hasDerivAt_inv_symm {ζ : ℝ × ℝ} (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0) :
    HasDerivAt (fun x : ℂ ↦ x⁻¹) (-(Complex.equivRealProdCLM.symm ζ ^ 2)⁻¹)
      (Complex.equivRealProdCLM.symm ζ) :=
  hasDerivAt_inv hζ

/-- Away from `0`, the Jacobian of the inversion at `ζ` is `|ζ|⁻⁴ = |ζ⁻¹|⁴`. -/
private theorem det_fderiv_realChart_inv {ζ : ℝ × ℝ} (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0) :
    (fderiv ℝ (TauCeti.Complex.realChart (·⁻¹)) ζ).det =
      ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ ^ 4 := by
  rw [TauCeti.Complex.det_fderiv_realChart (hasDerivAt_inv_symm hζ), norm_symm_realChart_inv,
    Complex.normSq_eq_norm_sq, norm_neg, norm_inv, norm_pow]
  ring

/-- Away from `0`, the inversion is smooth. -/
private theorem contDiffAt_realChart_inv {ζ : ℝ × ℝ} (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (TauCeti.Complex.realChart (·⁻¹)) ζ := by
  rw [show TauCeti.Complex.realChart (fun x : ℂ ↦ x⁻¹) = Complex.equivRealProdCLM ∘
      (fun x : ℂ ↦ x⁻¹) ∘ Complex.equivRealProdCLM.symm from
    funext (TauCeti.Complex.realChart_apply _)]
  exact Complex.equivRealProdCLM.contDiff.contDiffAt.comp ζ
    (((contDiffAt_inv ℂ hζ).restrict_scalars ℝ).comp ζ
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

/-- **The adjoint of constant data through the inversion.** For a constant structure `J₀` and the
zero perturbation, read a covector field `η` in the chart `ζ = w⁻¹` of the point at infinity as the
`(0, 1)`-form `η' = η (ζ⁻¹) ∘ (a + b J₀)` (`TauCeti.Floer.covectorPullback`). Away from `ζ = 0`, the
formal adjoint of `η'` at `ζ` is the Jacobian `|ζ⁻¹|⁴` of the inversion times the formal adjoint of
`η` at `ζ⁻¹`. -/
private theorem floerLinearizationAdjoint_const_covectorPullback_realChart_inv
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {ζ : ℝ × ℝ} (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0)
    (hη : DifferentiableAt ℝ η (TauCeti.Complex.realChart (·⁻¹) ζ)) :
    ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0
        (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η) ζ =
      ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ ^ 4 •
        ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η (TauCeti.Complex.realChart (·⁻¹) ζ) := by
  have hopen : IsOpen {ζ' : ℝ × ℝ | Complex.equivRealProdCLM.symm ζ' ≠ 0} :=
    isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const
  have h := ω.floerLinearizationAdjoint_perturbationPullback (J := fun _ _ ↦ J₀)
    (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) (u := 0) (contDiffAt_realChart_inv hζ)
    (Filter.mem_of_superset (hopen.mem_nhds hζ) fun ζ' hζ' ↦
      isComplexLinearMap_fderiv_realChart (hasDerivAt_inv_symm hζ'))
    (differentiableAt_const _) (.of_forall fun _ ↦ differentiableAt_const _)
    (.of_forall fun _ ↦ differentiableAt_const _) (by simp) (by simp)
    (by simp [floerOperator_def]) hη (differentiableAt_const _)
  rw [← det_fderiv_realChart_inv hζ, ← h]
  congr 1 <;> funext w x <;> simp [Floer.perturbationPullback_apply]

omit [FiniteDimensional ℝ V] in
/-- A covector field vanishing on the disc `|w| < r` vanishes, read through the inversion, on
`|ζ| > r⁻¹`. -/
private theorem apply_realChart_inv_eq_zero {η : ℝ × ℝ → V →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r)
    (hη0 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < r → η z = 0) {ζ : ℝ × ℝ}
    (hζ : r⁻¹ < ‖Complex.equivRealProdCLM.symm ζ‖) :
    η (TauCeti.Complex.realChart (·⁻¹) ζ) = 0 :=
  hη0 _ (by rw [norm_symm_realChart_inv]; exact inv_lt_of_inv_lt₀ hr hζ)

omit [FiniteDimensional ℝ V] in
/-- A compactly supported covector field vanishing on the disc `|w| < r` vanishes, read through the
inversion, on a neighbourhood `|ζ| < δ` of `ζ = 0`, the point at infinity. -/
private theorem exists_pos_forall_apply_realChart_inv_eq_zero {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hc : HasCompactSupport η) {r : ℝ} (hr : 0 < r)
    (hη0 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < r → η z = 0) :
    ∃ δ > 0, ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < δ →
      η (TauCeti.Complex.realChart (·⁻¹) ζ) = 0 := by
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn
    Complex.equivRealProdCLM.symm.continuous.continuousOn
  refine ⟨(max M 1)⁻¹, by positivity, fun ζ hζ ↦ ?_⟩
  by_cases hx : Complex.equivRealProdCLM.symm ζ = 0
  · have h0 : TauCeti.Complex.realChart (·⁻¹) ζ = 0 := by
      simp [TauCeti.Complex.realChart_apply, hx]
    exact h0 ▸ hη0 0 (by simpa using hr)
  · refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
    have h1 := hM _ hmem
    rw [norm_symm_realChart_inv] at h1
    have h2 : max M 1 < ‖Complex.equivRealProdCLM.symm ζ‖⁻¹ :=
      lt_inv_of_lt_inv₀ (norm_pos_iff.2 hx) hζ
    linarith [le_max_left M 1]

/-- **A covector field read through the inversion.** A compactly supported `C²` covector field
vanishing on the disc `|w| < r`, read in the chart `ζ = w⁻¹` as the form `η (ζ⁻¹) ∘ (a + b J₀)`, is
`C²` and vanishes on `|ζ| > r⁻¹`: near `ζ = 0`, the one point where the inversion is singular, it
vanishes since `η` has compact support. -/
private theorem contDiff_covectorPullback_realChart_inv {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) {r : ℝ} (hr : 0 < r)
    (hη0 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < r → η z = 0) :
    ContDiff ℝ 2 (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η) ∧
      ∀ ζ, r⁻¹ < ‖Complex.equivRealProdCLM.symm ζ‖ →
        Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η ζ = 0 := by
  set ι : ℝ × ℝ → ℝ × ℝ := TauCeti.Complex.realChart (·⁻¹)
  set U : Set (ℝ × ℝ) := {ζ | Complex.equivRealProdCLM.symm ζ ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const
  obtain ⟨δ, hδ, hδ0⟩ := exists_pos_forall_apply_realChart_inv_eq_zero hc hr hη0
  have hnear0 (ζ : ℝ × ℝ) (hζ : ζ ∉ U) : (η ∘ ι) =ᶠ[𝓝 ζ] 0 := by
    have hx : Complex.equivRealProdCLM.symm ζ = 0 := not_not.1 hζ
    filter_upwards [(isOpen_lt Complex.equivRealProdCLM.symm.continuous.norm
      continuous_const).mem_nhds
        (show ‖Complex.equivRealProdCLM.symm ζ‖ < δ by simpa [hx] using hδ)]
      with ζ' hζ'
    exact hδ0 ζ' hζ'
  have hηι : ContDiff ℝ 2 (η ∘ ι) := contDiff_iff_contDiffAt.2 fun ζ ↦ by
    by_cases hζ : ζ ∈ U
    · exact hη.contDiffAt.comp ζ (contDiffAt_realChart_inv hζ)
    · exact contDiffAt_const.congr_of_eventuallyEq (hnear0 ζ hζ)
  have hsupp : tsupport (η ∘ ι) ⊆ U := fun ζ hζ ↦ by
    by_contra h
    exact (notMem_tsupport_iff_eventuallyEq.2 (hnear0 ζ h)) hζ
  -- On `U` the factor `a + b J₀` is as smooth as the inversion.
  have hM : ContDiffOn ℝ 2 (fun ζ ↦ (fderiv ℝ ι ζ stdComplexLineReal).1 • (1 : V →L[ℝ] V) +
      (fderiv ℝ ι ζ stdComplexLineReal).2 • J₀.toLinearMap.toContinuousLinearMap) U := by
    have hιU : ContDiffOn ℝ ⊤ ι U := fun ζ hζ ↦ (contDiffAt_realChart_inv hζ).contDiffWithinAt
    have hd : ContDiffOn ℝ 2 (fun ζ ↦ fderiv ℝ ι ζ stdComplexLineReal) U :=
      (hιU.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    exact ((contDiff_fst.comp_contDiffOn hd).smul contDiffOn_const).add
      ((contDiff_snd.comp_contDiffOn hd).smul contDiffOn_const)
  exact ⟨Floer.contDiff_covectorPullback_of_contDiffOn hU hM hηι hsupp, fun ζ hζ ↦
    Floer.covectorPullback_eq_zero_of_apply_eq_zero _ _ _ (apply_realChart_inv_eq_zero hr hη0 hζ)⟩

/-- **Changing variables along the inversion.** For constant data, the `L²` norm of the adjoint of a
compactly supported `C²` covector field read through the inversion is at most
`∫ |w|⁴ ‖D^* η‖²`: the adjoint is multiplied by the Jacobian `|w|⁴` of the inversion, and the
change of variables along the inversion, an involution, absorbs one Jacobian. -/
private theorem integral_norm_floerLinearizationAdjoint_covectorPullback_realChart_inv_sq_le
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) :
    ∫ ζ, ‖ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η) ζ‖ ^ 2 ≤
      ∫ z, ‖Complex.equivRealProdCLM.symm z‖ ^ 4 *
        ‖ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η z‖ ^ 2 := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set ι : ℝ × ℝ → ℝ × ℝ := TauCeti.Complex.realChart (·⁻¹)
  set D := ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0
  set U : Set (ℝ × ℝ) := {ζ | Complex.equivRealProdCLM.symm ζ ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const
  set g : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖ ^ 4 * ‖D η z‖ ^ 2
  have hDη' (ζ : ℝ × ℝ) (hζ : ζ ∈ U) : ‖D (Floer.covectorPullback ι
      (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η) ζ‖ ^ 2 =
      |(fderiv ℝ ι ζ).det| * g (ι ζ) := by
    rw [show D _ ζ = _ from floerLinearizationAdjoint_const_covectorPullback_realChart_inv hζ
      (hη.differentiable two_ne_zero _), norm_smul, det_fderiv_realChart_inv hζ,
      Real.norm_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    ring
  have hDc : Continuous (D η) := continuous_floerLinearizationAdjoint_of_tsupport_subset
    (U := univ) (fun _ _ ↦ contDiffAt_const) (fun _ _ ↦ contDiffAt_const)
    (fun _ _ ↦ contDiffAt_const) (fun _ _ ↦ contDiffAt_const) (hη.of_le one_le_two)
    (subset_univ _)
  have hg : Integrable g :=
    ((Complex.equivRealProdCLM.symm.continuous.norm.pow 4).mul
      (hDc.norm.pow 2)).integrable_of_hasCompactSupport (hc.mono' fun z hz ↦ by
        by_contra h
        simp [D, floerLinearizationAdjoint_of_notMem_tsupport h] at hz)
  have hU0 : ∀ᵐ ζ ∂(volume : Measure (ℝ × ℝ)), ζ ∈ U :=
    (Measure.ae_ne volume 0).mono fun ζ hζ h ↦
      hζ (Complex.equivRealProdCLM.symm.map_eq_zero_iff.1 h)
  calc _ = ∫ ζ in U, ‖D (Floer.covectorPullback ι
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η) ζ‖ ^ 2 :=
        (setIntegral_eq_integral_of_ae_compl_eq_zero (hU0.mono fun ζ hζ h ↦ (h hζ).elim)).symm
    _ = ∫ z in ι '' U, g z :=
        (integral_image_eq_integral_of_eq_abs_det_smul hU.measurableSet
          (Function.LeftInverse.injective realChart_inv_realChart_inv).injOn
          (fun ζ hζ ↦ (contDiffAt_realChart_inv hζ (n := 1)).differentiableAt one_ne_zero)
          fun ζ hζ ↦ by rw [hDη' ζ hζ, smul_eq_mul]).symm
    _ ≤ ∫ z, g z := setIntegral_le_integral hg (ae_of_all _ fun z ↦ by positivity)

/-- **The estimate at infinity for constant data.** For a constant `ω`-compatible structure `J₀` and
the zero perturbation, a compactly supported `C²` covector field vanishing on the disc `|w| < r`,
read through the inversion, has integrable `W^{1,2}` density whose integral is controlled by
`∫ |w|⁴ ‖D^* η‖²`. In the chart `ζ = w⁻¹` the field is supported in the disc `|ζ| ≤ r⁻¹`, so the
Poincaré inequality on a strip bounds its `L²` norm by its Dirichlet energy; the energy estimate of
constant data bounds that by the `L²` norm of its adjoint, which is the Jacobian `|w|⁴` times the
adjoint of `η`, and the change of variables along the inversion absorbs one Jacobian. -/
private theorem exists_forall_integral_sobolevDensity_covectorPullback_realChart_inv_le
    (h₀ : ω.Compatible J₀) {r : ℝ} (hr : 0 < r) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∀ z, ‖Complex.equivRealProdCLM.symm z‖ < r → η z = 0) →
      Integrable (Floer.sobolevDensity (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η)) ∧
      ∫ ζ, Floer.sobolevDensity (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η) ζ ≤
        C * ∫ z, ‖Complex.equivRealProdCLM.symm z‖ ^ 4 *
          ‖ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
            (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η z‖ ^ 2 := by
  obtain ⟨C, hC, hE⟩ := exists_forall_integral_norm_fderiv_sq_le_of_const h₀
  refine ⟨(1 + (2 * (2 * r⁻¹)) ^ 2) * C, by positivity, fun η hη hc hη0 ↦ ?_⟩
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set η' := Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
    (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η
  obtain ⟨hη'2, hη'far⟩ := contDiff_covectorPullback_realChart_inv (J₀ := J₀) hη hc hr hη0
  have hη'c : HasCompactSupport η' :=
    HasCompactSupport.intro (isCompact_setOf_norm_equivRealProdCLM_symm_le r⁻¹) fun ζ hζ ↦
      hη'far ζ (not_le.1 hζ)
  -- The Poincaré inequality in the chart, where `η'` vanishes off the disc `|ζ| ≤ r⁻¹`.
  have hP := integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_abs_snd (r := 2 * r⁻¹)
    (hη'2.of_le one_le_two) hη'c fun ζ hζ ↦ hη'far ζ (by
      have h1 := Complex.abs_im_le_norm (Complex.equivRealProdCLM.symm ζ)
      have h2 : 0 < r⁻¹ := inv_pos.2 hr
      simp only [Complex.equivRealProdCLM_symm_apply_im] at h1
      linarith)
  rw [← stdComplexLineImag_eq] at hP
  -- The energy estimate in the chart, and the change of variables back to the plane.
  have hEη := hE hη'2 hη'c
  have hcv := integral_norm_floerLinearizationAdjoint_covectorPullback_realChart_inv_sq_le
    (ω := ω) (J₀ := J₀) hη hc
  have iD := integrable_norm_fderiv_sq_add (μ := volume) (hη'2.of_le one_le_two) hη'c
    stdComplexLineReal stdComplexLineImag
  have iL : Integrable fun ζ ↦ ‖η' ζ‖ ^ 2 :=
    hη'2.continuous.integrable_norm_sq_of_hasCompactSupport hη'c
  have iI : Integrable fun ζ ↦ ‖fderiv ℝ η' ζ stdComplexLineImag‖ ^ 2 :=
    iD.mono' (((hη'2.continuous_fderiv two_ne_zero).clm_apply
      continuous_const).norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun ζ ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        nlinarith [sq_nonneg ‖fderiv ℝ η' ζ stdComplexLineReal‖])
  have hI : ∫ ζ, ‖fderiv ℝ η' ζ stdComplexLineImag‖ ^ 2 ≤
      ∫ ζ, (‖fderiv ℝ η' ζ stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η' ζ stdComplexLineImag‖ ^ 2) :=
    integral_mono iI iD fun ζ ↦ by
      dsimp only
      nlinarith [sq_nonneg ‖fderiv ℝ η' ζ stdComplexLineReal‖]
  refine ⟨(iD.add iL).congr (Eventually.of_forall fun ζ ↦
    (Floer.sobolevDensity_apply η' ζ).symm), ?_⟩
  simp only [Floer.sobolevDensity_apply]
  rw [integral_add iD iL]
  calc _ ≤ (1 + (2 * (2 * r⁻¹)) ^ 2) * ∫ ζ, (‖fderiv ℝ η' ζ stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η' ζ stdComplexLineImag‖ ^ 2) := by nlinarith
    _ ≤ (1 + (2 * (2 * r⁻¹)) ^ 2) * (C * ∫ ζ, ‖ω.floerLinearizationAdjoint
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η'
            ζ‖ ^ 2) := by gcongr
    _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hcv (by positivity)

/-- **The cost of a cutoff for the formal adjoint.** For a `C¹` cutoff `β` with values in `[0, 1]`
whose derivative vanishes off a compact set `K`, the formal adjoint of `β η` is pointwise at most
`2 ‖D_u^* η‖² + c ‖η‖²` on `K` and `2 ‖D_u^* η‖²` off it. -/
private theorem exists_forall_norm_floerLinearizationAdjoint_smul_sq_le
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β) (hβ1 : ∀ z, β z ∈ Icc 0 1)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hβK : ∀ z ∉ K, fderiv ℝ β z = 0) :
    ∃ c, 0 ≤ c ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, Differentiable ℝ η → ∀ z,
      ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (fun w ↦ β w • η w) z‖ ^ 2 ≤
        2 * ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u η z‖ ^ 2 + c * K.indicator (fun z ↦ ‖η z‖ ^ 2) z := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_comp_prodMk_of_continuousAt
    (fun z ↦ (hJ z).continuousAt) hu.continuous).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hβ.continuous_fderiv one_ne_zero).continuousOn
  set c := max M 0 * (1 + max B 0)
  refine ⟨2 * c ^ 2, by positivity, fun η hη z ↦ ?_⟩
  have hJu : DifferentiableAt ℝ
      (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z :=
    ((hJ z).differentiableAt one_ne_zero).comp (f := fun w ↦ (w, u w)) z
      (differentiableAt_id.prodMk (hu.differentiable one_ne_zero z))
  rw [floerLinearizationAdjoint_fun_smul (hβ.differentiable one_ne_zero z) (hη z) hJu]
  set D := ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
    η z
  have hβD : ‖β z • D‖ ≤ ‖D‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hβ1 z).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hβ1 z).2
  by_cases hz : z ∈ K
  · -- On `K` the derivative of `β` and the structure are bounded.
    have hdβ : ‖fderiv ℝ β z‖ ≤ max M 0 := (hM z hz).trans (le_max_left _ _)
    have hJz : ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ max B 0 :=
      (hB z hz).trans (le_max_left _ _)
    have h1 : ‖fderiv ℝ β z stdComplexLineReal • η z‖ ≤ max M 0 * ‖η z‖ := by
      rw [norm_smul]
      gcongr
      exact ((fderiv ℝ β z).le_opNorm _).trans (by simp [stdComplexLineReal, hdβ])
    have h2 : ‖fderiv ℝ β z stdComplexLineImag • (η z).comp
        (J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ max M 0 * (max B 0 * ‖η z‖) := by
      rw [norm_smul]
      gcongr
      · exact ((fderiv ℝ β z).le_opNorm _).trans (by simp [stdComplexLineImag, hdβ])
      · exact ((η z).opNorm_comp_le _).trans (by rw [mul_comm]; gcongr)
    have htri : ‖β z • D - fderiv ℝ β z stdComplexLineReal • η z -
        fderiv ℝ β z stdComplexLineImag • (η z).comp
          (J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ ‖D‖ + c * ‖η z‖ := by
      refine (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) h2).trans ?_)
      nlinarith [norm_nonneg (η z), le_max_right M 0, le_max_right B 0]
    rw [indicator_of_mem hz]
    nlinarith [sq_nonneg (‖D‖ - c * ‖η z‖), norm_nonneg D, norm_nonneg (η z),
      norm_nonneg (β z • D - fderiv ℝ β z stdComplexLineReal • η z -
        fderiv ℝ β z stdComplexLineImag • (η z).comp
          (J z (u z)).toLinearMap.toContinuousLinearMap)]
  · -- Off `K` the cutoff is locally constant.
    rw [hβK z hz, indicator_of_notMem hz]
    simp only [zero_apply, zero_smul, sub_zero, mul_zero, add_zero]
    nlinarith [norm_nonneg (β z • D), norm_nonneg D]

/-- The formal adjoint of a compactly supported `C¹` covector field is continuous and compactly
supported, so its square is integrable. -/
private theorem integrable_norm_floerLinearizationAdjoint_sq
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) :
    Integrable fun z ↦ f z * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 := by
  have hDc := continuous_floerLinearizationAdjoint_of_tsupport_subset (ω := ω) (U := univ)
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) (Ks := Ks) (Kt := Kt)
    (fun z _ ↦ by simpa only [Function.uncurry_def] using hJ z) (fun z _ ↦ hKs z)
    (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt) hη (subset_univ _)
  exact (hf.mul (hDc.norm.pow 2)).integrable_of_hasCompactSupport (hηc.mono' fun z hz ↦ by
    by_contra h
    simp [floerLinearizationAdjoint_of_notMem_tsupport h] at hz)

/-- **The estimate of the formal adjoint on a disc.** The `W^{1,2}` norm of a compactly supported
covector field on the disc `|w| ≤ a` is controlled by the `L²` norm of `D_u^* η` and the `L²` norm
of `η` on the square `‖w‖ ≤ a + 1`. -/
private theorem exists_forall_setIntegral_sobolevDensity_le_floerLinearizationAdjoint_disc
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) (a : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}, Floer.sobolevDensity η z ≤
        C * ((∫ z, ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set K₁ : Set (ℝ × ℝ) := {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a + 1}
  have hK₁ : IsCompact K₁ := isCompact_setOf_norm_equivRealProdCLM_symm_le (a + 1)
  have hK₁m : MeasurableSet K₁ := hK₁.isClosed.measurableSet
  -- A cutoff `ψ`, equal to `1` near the disc `|w| ≤ a` and to `0` near `|w| ≥ a + 1`.
  obtain ⟨ψ, hψ, hψ01, hψ1, hψ0, hψK⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le a).exists_contDiff_cutoff_sublevel
      Complex.equivRealProdCLM.symm.continuous.norm (lt_add_one a)
  obtain ⟨C₁, hC₁, hdisc⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add hK₁
      (fun z _ ↦ hJ z) (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt)
      (fun z _ ↦ hc z)
  obtain ⟨c, hc0, hcut⟩ := exists_forall_norm_floerLinearizationAdjoint_smul_sq_le (ω := ω)
    (Ks := Ks) (Kt := Kt) hJ hu (hψ.of_le (by simp)) hψ01 hK₁ fun z hz ↦ hψK z (not_le.1 hz)
  refine ⟨C₁ * (c + 3), by positivity, fun η hη hηc ↦ ?_⟩
  set η₁ : ℝ × ℝ → V →L[ℝ] ℝ := fun w ↦ ψ w • η w
  have hη₁ : ContDiff ℝ 2 η₁ := (hψ.of_le (by simp)).smul hη
  have hη₁K : tsupport η₁ ⊆ K₁ := (tsupport_smul_subset_left ψ η).trans <|
    closure_minimal (fun z hz ↦ not_lt.1 fun h ↦ hz (hψ0 z h.le).eq_of_nhds) hK₁.isClosed
  -- On the disc `η₁` agrees with `η` near each point.
  have hstep₁ : ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}, Floer.sobolevDensity η z ≤
      ∫ z in K₁, Floer.sobolevDensity η₁ z := by
    refine le_of_eq_of_le (setIntegral_congr_fun (measurableSet_le
      Complex.equivRealProdCLM.symm.continuous.norm.measurable measurable_const) fun z hz ↦ ?_)
      (setIntegral_mono_set
        ((Floer.continuous_sobolevDensity (hη₁.of_le one_le_two)).continuousOn.integrableOn_compact
          hK₁) (Eventually.of_forall fun z ↦ by simp only [Floer.sobolevDensity_apply]; positivity)
        (Eventually.of_forall fun z (hz : _ ≤ a) ↦ (show _ ≤ a + 1 by linarith : z ∈ K₁)))
    have hev : η₁ =ᶠ[𝓝 z] η := (hψ1 z hz).mono fun w hw ↦ by simp [η₁, hw]
    simp only [Floer.sobolevDensity_apply, hev.fderiv_eq, hev.eq_of_nhds]
  -- The cutoff costs `c ‖η‖²` on `K₁`.
  have hpt (z : ℝ × ℝ) (hz : z ∈ K₁) :
      ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
          η₁ z‖ ^ 2 + ‖η₁ z‖ ^ 2 ≤
        2 * ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          Ks Kt u η z‖ ^ 2 + (c + 1) * ‖η z‖ ^ 2 := by
    have h1 := hcut (hη.differentiable two_ne_zero) z
    rw [indicator_of_mem hz] at h1
    have h2 : ‖η₁ z‖ ≤ ‖η z‖ := by
      simp only [η₁, norm_smul, Real.norm_of_nonneg (hψ01 z).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hψ01 z).2
    nlinarith [norm_nonneg (η₁ z)]
  have iD := integrable_norm_floerLinearizationAdjoint_sq (ω := ω) hJ hKs hKt hu
    (hη.of_le one_le_two) hηc continuous_const (f := fun _ ↦ (1 : ℝ))
  simp only [one_mul] at iD
  have iη : Integrable fun z ↦ ‖η z‖ ^ 2 :=
    hη.continuous.integrable_norm_sq_of_hasCompactSupport hηc
  have hball : ∫ z in K₁, ‖η z‖ ^ 2 ≤ ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2 :=
    setIntegral_mono_set iη.integrableOn (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall fun z (hz : _ ≤ a + 1) ↦
        mem_closedBall_zero_iff.2 ((norm_le_norm_equivRealProdCLM_symm z).trans hz))
  have hfull : ∫ z in K₁, ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 ≤
      ∫ z, ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 :=
    setIntegral_le_integral iD (Eventually.of_forall fun _ ↦ sq_nonneg _)
  calc _ ≤ ∫ z in K₁, Floer.sobolevDensity η₁ z := hstep₁
    _ ≤ C₁ * ∫ z in K₁, (‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η₁ z‖ ^ 2 +
          ‖η₁ z‖ ^ 2) := hdisc hη₁ hη₁K
    _ ≤ C₁ * ∫ z in K₁, (2 * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 +
          (c + 1) * ‖η z‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_on ?_
          ((iD.const_mul 2).add (iη.const_mul _)).integrableOn hK₁m hpt) hC₁
        have hη₁c : HasCompactSupport η₁ := HasCompactSupport.intro hK₁ fun z hz ↦
          image_eq_zero_of_notMem_tsupport fun h ↦ hz (hη₁K h)
        exact ((integrable_norm_floerLinearizationAdjoint_sq (ω := ω) hJ hKs hKt hu
          (hη₁.of_le one_le_two) hη₁c continuous_const (f := fun _ ↦ (1 : ℝ))).congr
            (Eventually.of_forall fun z ↦ by simp)).add
          (hη₁.continuous.integrable_norm_sq_of_hasCompactSupport hη₁c) |>.integrableOn
    _ = C₁ * (2 * (∫ z in K₁, ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          (c + 1) * ∫ z in K₁, ‖η z‖ ^ 2) := by
        rw [integral_add ((iD.const_mul 2).integrableOn) ((iη.const_mul _).integrableOn),
          integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        have h0 : 0 ≤ ∫ z, ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 :=
          integral_nonneg fun _ ↦ sq_nonneg _
        have h0' : 0 ≤ ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2 :=
          setIntegral_nonneg measurableSet_closedBall fun _ _ ↦ sq_nonneg _
        have key : 2 * (∫ z in K₁, ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
            (c + 1) * ∫ z in K₁, ‖η z‖ ^ 2 ≤ (c + 3) * ((∫ z, ‖ω.floerLinearizationAdjoint
              (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
              ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hball (by linarith : (0 : ℝ) ≤ c + 1)]
        calc _ ≤ C₁ * ((c + 3) * ((∫ z, ‖ω.floerLinearizationAdjoint
              (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
              ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2)) := mul_le_mul_of_nonneg_left key hC₁
          _ = _ := by ring

/-- Where `2 T < |w|`, so that `T < ‖w‖`, the structures are `J₀` near `w`. -/
private theorem eventuallyEq_const_of_eq_base (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    {w : ℝ × ℝ} (hw : 2 * T < ‖Complex.equivRealProdCLM.symm w‖) :
    (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) =ᶠ[𝓝 w]
      fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap := by
  have hT : T < ‖w‖ := by linarith [norm_equivRealProdCLM_symm_le_two_mul w]
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hT] with z hz
  funext y
  simp [hJ₀ z hz.le y]

/-- Let the data be `J₀` and `0` on `‖w‖ ≥ T`. For a covector field `η₂` vanishing on the disc
`|w| < a`, with `2 T < a`, the formal adjoint of the data along `u` is that of the constant data
`J₀`, `0` along the zero map. -/
private theorem floerLinearizationAdjoint_const_eq_of_eq_base
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0) {a : ℝ} (haT : 2 * T < a)
    {η₂ : ℝ × ℝ → V →L[ℝ] ℝ} (hη₂0 : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ < a → η₂ z = 0)
    (w : ℝ × ℝ) :
    ω.floerLinearizationAdjoint
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₂ w =
      ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
        η₂ w := by
  by_cases hw : w ∈ tsupport η₂
  · have haw : a ≤ ‖Complex.equivRealProdCLM.symm w‖ := not_lt.1 fun h ↦
      (notMem_tsupport_iff_eventuallyEq.2 (Filter.mem_of_superset
        ((isOpen_lt Complex.equivRealProdCLM.symm.continuous.norm continuous_const).mem_nhds h)
        fun z hz ↦ hη₂0 z hz)) hw
    have hT : T ≤ ‖w‖ := by linarith [norm_equivRealProdCLM_symm_le_two_mul w]
    rw [ω.floerLinearizationAdjoint_congr_data (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0) u η₂
      (eventuallyEq_const_of_eq_base hJ₀ (by linarith)) (funext (hKs₀ w hT))
      (funext (hKt₀ w hT))]
    -- The constant data have no zeroth-order part, along any map.
    have h0 (u' : ℝ × ℝ → V) : ω.floerLinearizationCoeff
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) u' w =
          0 := by
      ext v
      simp [floerLinearizationCoeff_apply]
    simp only [floerLinearizationAdjoint_def, h0]
  · rw [floerLinearizationAdjoint_of_notMem_tsupport hw,
      floerLinearizationAdjoint_of_notMem_tsupport hw]

/-- Let `J = J₀` on `‖w‖ ≥ T`, let `2 T < a`, and let `η₂` agree with `η` near every point of
`|w| ≥ a + 1`. Then on the disc `|ζ| ≤ (a + 1)⁻¹`, which is the part `|w| ≥ a + 1` of the sphere,
the form `η` read through the inversion with the structures `J` along `u` is, away from `ζ = 0`, the
form `η₂` read with the constant structure `J₀`; so the `W^{1,2}` norm of the first on that disc is
at most the `W^{1,2}` norm of the second on the whole chart. -/
private theorem setIntegral_sobolevDensity_covectorPullback_le_of_eventuallyEq
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀) {a : ℝ} (ha : 0 < a) (haT : 2 * T < a)
    {η η₂ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hagree : ∀ w, a + 1 ≤ ‖Complex.equivRealProdCLM.symm w‖ → η₂ =ᶠ[𝓝 w] η)
    (hint : Integrable (Floer.sobolevDensity (Floer.covectorPullback
      (TauCeti.Complex.realChart (·⁻¹)) (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η₂))) :
    ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ (a + 1)⁻¹},
        Floer.sobolevDensity (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
      ∫ ζ, Floer.sobolevDensity (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η₂) ζ := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hmeas : MeasurableSet {ζ : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ (a + 1)⁻¹} :=
    measurableSet_le Complex.equivRealProdCLM.symm.continuous.norm.measurable measurable_const
  refine le_of_eq_of_le (setIntegral_congr_ae hmeas ((Measure.ae_ne volume 0).mono
      fun ζ hζ0 hζ ↦ ?_))
    (setIntegral_le_integral hint (Eventually.of_forall fun ζ ↦ by
      simp only [Floer.sobolevDensity_apply]
      positivity))
  have hζU : Complex.equivRealProdCLM.symm ζ ≠ 0 := fun h ↦
    hζ0 (Complex.equivRealProdCLM.symm.map_eq_zero_iff.1 h)
  have hw : a + 1 ≤ ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ := by
    rw [norm_symm_realChart_inv]
    exact (le_inv_comm₀ (norm_pos_iff.2 hζU) (by linarith)).1 hζ
  have hten : Tendsto (TauCeti.Complex.realChart (·⁻¹)) (𝓝 ζ)
      (𝓝 (TauCeti.Complex.realChart (·⁻¹) ζ)) :=
    (contDiffAt_realChart_inv hζU (n := 0)).continuousAt
  -- Near `ζ` both forms read the same covector and the same structure.
  have hev : Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η =ᶠ[𝓝 ζ]
      Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η₂ := by
    filter_upwards [hten.eventually (hagree _ hw), hten.eventually
      (eventuallyEq_const_of_eq_base hJ₀ (w := TauCeti.Complex.realChart (·⁻¹) ζ)
        (by linarith))] with ζ' hηζ' hJζ'
    have hJ' := congr_fun hJζ' (u (TauCeti.Complex.realChart (·⁻¹) ζ'))
    simp only [Floer.covectorPullback_apply, hηζ', hJ']
  simp only [Floer.sobolevDensity_apply, hev.fderiv_eq, hev.eq_of_nhds]

/-- **The estimate of the formal adjoint near the point at infinity.** Let the data be `J₀` and the
zero perturbation on `‖w‖ ≥ T`, and let `a > 2 T`, so that they are `J₀` and `0` near every point
of `|w| ≥ a`. Read through the inversion `ζ = w⁻¹`, the `W^{1,2}` norm of a compactly supported
covector field on the disc `|ζ| ≤ (a + 1)⁻¹`, which is the part `|w| ≥ a + 1` of the sphere, is
controlled by `∫ (1 + |w|²)² ‖D_u^* η‖²` and the `L²` norm of `η` on the square `‖w‖ ≤ a + 1`. -/
private theorem exists_forall_setIntegral_sobolevDensity_covectorPullback_le_of_eq_base
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) {a : ℝ} (ha : 0 < a)
    (haT : 2 * T < a) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ (a + 1)⁻¹},
          Floer.sobolevDensity (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
            (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ((∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- `J₀` is the compatible structure `J` takes at a point far out.
  have h₀ : ω.Compatible J₀ :=
    hJ₀ (|T|, 0) (by simp [Prod.norm_def, le_abs_self]) (u (|T|, 0)) ▸ hc (|T|, 0)
  set K₁ : Set (ℝ × ℝ) := {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a + 1}
  have hK₁ : IsCompact K₁ := isCompact_setOf_norm_equivRealProdCLM_symm_le (a + 1)
  -- A cutoff `β = 1 - ψ`, equal to `0` near the disc `|w| ≤ a` and to `1` near `|w| ≥ a + 1`.
  obtain ⟨ψ, hψ, hψ01, hψ1, hψ0, hψK⟩ :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le a).exists_contDiff_cutoff_sublevel
      Complex.equivRealProdCLM.symm.continuous.norm (lt_add_one a)
  have hβ : ContDiff ℝ 2 fun z ↦ 1 - ψ z := contDiff_const.sub (hψ.of_le (by simp))
  obtain ⟨c, hc0, hcut⟩ := exists_forall_norm_floerLinearizationAdjoint_smul_sq_le (ω := ω)
    (Ks := Ks) (Kt := Kt) hJ hu (hβ.of_le one_le_two)
    (fun z ↦ ⟨sub_nonneg.2 (hψ01 z).2, sub_le_self _ (hψ01 z).1⟩) hK₁
    fun z hz ↦ by rw [fderiv_const_sub, hψK z (not_le.1 hz), neg_zero]
  obtain ⟨C₂, hC₂, hinf⟩ := exists_forall_integral_sobolevDensity_covectorPullback_realChart_inv_le
    (ω := ω) h₀ ha
  refine ⟨C₂ * (2 + c * (1 + (a + 1) ^ 2) ^ 2), by positivity, fun η hη hηc ↦ ?_⟩
  obtain ⟨η₂, hη₂def⟩ : ∃ η₂ : ℝ × ℝ → V →L[ℝ] ℝ, η₂ = fun z ↦ (1 - ψ z) • η z := ⟨_, rfl⟩
  have hη₂ : ContDiff ℝ 2 η₂ := hη₂def ▸ hβ.smul hη
  have hη₂c : HasCompactSupport η₂ := hηc.mono fun z hz h ↦ hz (by simp [hη₂def, h])
  have hη₂0 (z : ℝ × ℝ) (hz : ‖Complex.equivRealProdCLM.symm z‖ < a) : η₂ z = 0 := by
    simp [hη₂def, (hψ1 z hz.le).eq_of_nhds]
  obtain ⟨hint, hest⟩ := hinf hη₂ hη₂c hη₂0
  -- The part `|w| ≥ a + 1` of the sphere, where `η₂ = η`, read in the chart `ζ = w⁻¹`.
  have hA := setIntegral_sobolevDensity_covectorPullback_le_of_eventuallyEq (u := u) (η := η)
    hJ₀ ha haT (fun w hw ↦ (hψ0 w hw).mono fun z hz ↦ by simp [hη₂def, hz]) hint
  have hB := floerLinearizationAdjoint_const_eq_of_eq_base (ω := ω) (u := u) hJ₀ hKs₀ hKt₀ haT
    hη₂0
  -- (C) The pointwise bound, with the weight `|w|⁴ ≤ (1 + |w|²)²`.
  have hC (w : ℝ × ℝ) : ‖Complex.equivRealProdCLM.symm w‖ ^ 4 * ‖ω.floerLinearizationAdjoint
      (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₂ w‖ ^ 2 ≤
      2 * ((1 + w.1 ^ 2 + w.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η w‖ ^ 2) +
      c * (1 + (a + 1) ^ 2) ^ 2 * K₁.indicator (fun z ↦ ‖η z‖ ^ 2) w := by
    have hcw := hcut (hη.differentiable two_ne_zero) w
    rw [← hη₂def, ← hB] at hcw
    have h4 : ‖Complex.equivRealProdCLM.symm w‖ ^ 4 ≤ (1 + w.1 ^ 2 + w.2 ^ 2) ^ 2 := by
      have := sq_norm_equivRealProdCLM_symm w
      nlinarith [sq_nonneg w.1, sq_nonneg w.2]
    have hK : (1 + w.1 ^ 2 + w.2 ^ 2) ^ 2 * K₁.indicator (fun z ↦ ‖η z‖ ^ 2) w ≤
        (1 + (a + 1) ^ 2) ^ 2 * K₁.indicator (fun z ↦ ‖η z‖ ^ 2) w := by
      by_cases hwK : w ∈ K₁
      · rw [indicator_of_mem hwK]
        have hwK' : ‖Complex.equivRealProdCLM.symm w‖ ≤ a + 1 := hwK
        have := sq_norm_equivRealProdCLM_symm w
        have h2 : 1 + w.1 ^ 2 + w.2 ^ 2 ≤ 1 + (a + 1) ^ 2 := by
          nlinarith [norm_nonneg (Complex.equivRealProdCLM.symm w)]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h2 2) (sq_nonneg _)
      · simp [indicator_of_notMem hwK]
    calc _ ≤ (1 + w.1 ^ 2 + w.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₂
            w‖ ^ 2 := by
          gcongr
      _ ≤ (1 + w.1 ^ 2 + w.2 ^ 2) ^ 2 * (2 * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η w‖ ^ 2 +
          c * K₁.indicator (fun z ↦ ‖η z‖ ^ 2) w) := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hK hc0]
  -- (D) Integrating the pointwise bound.
  have iW := integrable_norm_floerLinearizationAdjoint_sq (ω := ω) hJ hKs hKt hu
    (hη.of_le one_le_two) hηc (f := fun z ↦ (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2) (by fun_prop)
  have iη : Integrable fun z ↦ ‖η z‖ ^ 2 :=
    hη.continuous.integrable_norm_sq_of_hasCompactSupport hηc
  have hK₁m : MeasurableSet K₁ := hK₁.isClosed.measurableSet
  have iK := (integrable_indicator_iff hK₁m).2 iη.integrableOn
  have hX : 0 ≤ ∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 :=
    integral_nonneg fun _ ↦ by positivity
  have hY : ∫ z in K₁, ‖η z‖ ^ 2 ≤ ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2 :=
    setIntegral_mono_set iη.integrableOn (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall fun z (hz : _ ≤ a + 1) ↦
        mem_closedBall_zero_iff.2 ((norm_le_norm_equivRealProdCLM_symm z).trans hz))
  have hY0 : 0 ≤ ∫ z in K₁, ‖η z‖ ^ 2 := setIntegral_nonneg hK₁m fun _ _ ↦ sq_nonneg _
  calc _ ≤ _ := hA
    _ ≤ _ := hest
    _ ≤ C₂ * ∫ w, (2 * ((1 + w.1 ^ 2 + w.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η w‖ ^ 2) +
          c * (1 + (a + 1) ^ 2) ^ 2 * K₁.indicator (fun z ↦ ‖η z‖ ^ 2) w) :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (Eventually.of_forall fun w ↦ by positivity) ((iW.const_mul 2).add (iK.const_mul _))
          (Eventually.of_forall hC)) hC₂
    _ = C₂ * (2 * (∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          c * (1 + (a + 1) ^ 2) ^ 2 * ∫ z in K₁, ‖η z‖ ^ 2) := by
        rw [integral_add (iW.const_mul 2) (iK.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator hK₁m]
    _ ≤ _ := by
        have hc' : 0 ≤ c * (1 + (a + 1) ^ 2) ^ 2 := by positivity
        have key : 2 * (∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
            c * (1 + (a + 1) ^ 2) ^ 2 * (∫ z in K₁, ‖η z‖ ^ 2) ≤
            (2 + c * (1 + (a + 1) ^ 2) ^ 2) * ((∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 *
              ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
                Ks Kt u η z‖ ^ 2) + ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hY hc', mul_nonneg hc' hX]
        calc _ ≤ C₂ * ((2 + c * (1 + (a + 1) ^ 2) ^ 2) * ((∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 *
              ‖ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
                Ks Kt u η z‖ ^ 2) + ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left key hC₂
          _ = _ := by ring

/-- **The semi-Fredholm estimate of the formal adjoint on the Riemann sphere.** Let the Floer data
`J`, `K_s`, `K_t` on the plane `ℝ × ℝ ≅ ℂ` be the fixed `ω`-compatible structure `J₀` and the zero
perturbation on `‖w‖ ≥ T`, a neighbourhood of the point at infinity of the sphere. Let `J` be `C¹`
and `K_s`, `K_t` be `C²` along a `C¹` map `u`, with `J(w, u w)` compatible. Then there are `R > 0`
and `C ≥ 0` such that every compactly supported `C²` covector field `η` satisfies

`∫_{|w| ≤ R} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) + ∫_{|ζ| ≤ R⁻¹} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²)`
`  ≤ C (∫ (1 + |w|²)² ‖D_u^* η‖² + ∫_{‖w‖ ≤ R + 1} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator, where
`η' = η (ζ⁻¹) ∘ (a + b J)` is `η` read as a `(0, 1)`-form in the chart `ζ = w⁻¹` of the point at
infinity (`TauCeti.Floer.covectorPullback`). The left side is the squared `W^{1,2}` norm of `η` on
the sphere, in the chart `w` on the disc `|w| ≤ R` and in the chart `ζ` on the rest of the sphere.
The weight `(1 + |w|²)²` is the inverse of the weight `(1 + |w|²)⁻²` of the `L²` part of `W^{1,2}`
of the sphere, as for the dual of `W^{1,2}`. This is the estimate for `D_u^*` that
`exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base` is for `D_u`. -/
theorem
    exists_forall_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_eq_base
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    ∃ R C, 0 < R ∧ 0 ≤ C ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      (∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ R}, Floer.sobolevDensity η z) +
          ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ R⁻¹},
            Floer.sobolevDensity (Floer.covectorPullback (TauCeti.Complex.realChart (·⁻¹))
              (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C * ((∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in closedBall 0 (R + 1), ‖η z‖ ^ 2) := by
  set a : ℝ := 2 * max T 0 + 1
  have ha : 0 < a := by positivity
  have haT : 2 * T < a := by linarith [le_max_left T 0]
  obtain ⟨C₁, hC₁, hdisc⟩ :=
    exists_forall_setIntegral_sobolevDensity_le_floerLinearizationAdjoint_disc (ω := ω) hJ hKs hKt
      hu hc (a + 1)
  obtain ⟨C₂, hC₂, hinf⟩ := exists_forall_setIntegral_sobolevDensity_covectorPullback_le_of_eq_base
    (ω := ω) hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc ha haT
  refine ⟨a + 1, C₁ + C₂, by positivity, by positivity, fun η hη hηc ↦ ?_⟩
  have h1 := hdisc hη hηc
  have h2 := hinf hη hηc
  have iη : Integrable fun z ↦ ‖η z‖ ^ 2 :=
    hη.continuous.integrable_norm_sq_of_hasCompactSupport hηc
  -- The unweighted `L²` norm of `D_u^* η` is at most the weighted one, since the weight is `≥ 1`.
  have hX : ∫ z, ‖ω.floerLinearizationAdjoint
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 ≤
      ∫ z, (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2 * ‖ω.floerLinearizationAdjoint
        (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (integrable_norm_floerLinearizationAdjoint_sq (ω := ω) hJ hKs hKt hu (hη.of_le one_le_two)
        hηc (by fun_prop)) (Eventually.of_forall fun z ↦ le_mul_of_one_le_left (sq_nonneg _)
          (one_le_pow₀ (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])))
  have hY : ∫ z in closedBall 0 (a + 1), ‖η z‖ ^ 2 ≤ ∫ z in closedBall 0 (a + 1 + 1), ‖η z‖ ^ 2 :=
    setIntegral_mono_set iη.integrableOn (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall (closedBall_subset_closedBall (by linarith)))
  nlinarith [mul_le_mul_of_nonneg_left hX hC₁, mul_le_mul_of_nonneg_left hY hC₂]

end TauCeti.SymplecticForm
