/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Plane.Linearization
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Complex.RealChart
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart

/-!
# The linearized Floer operator of a PSS plane on `W^{1,2}`

The Fredholm theory of the linearized Floer operator on a PSS plane `ℂ` uses Sobolev norms of a
metric that is Euclidean near the pole `0` and cylindrical on the end at `∞`, where it is
`ds² + dt²` in the coordinates `(s, t)` of the end lift `φ(s, t) = exp (2π ε (s + i t))`
(`TauCeti.Floer.PSSPlane.cylindricalEndLift`). In the coordinate `w` of `ℂ` the cylindrical
metric is `|dw|² / (4π² |w|²)`, so this file fixes the conformal weight

`ρ(w) = (1 + |w|²)⁻¹` (`TauCeti.Floer.PSSPlane.cylindricalWeight`),

a conformal weight on the whole plane (`TauCeti.Floer.PSSPlane.isWeight_cylindricalWeight`). The
Sobolev space `TauCeti.ConformalSobolev.H1 V univ ρ` of `TauCeti.Analysis.Sobolev.Conformal` is
then the completion of the compactly supported sections in the norm
`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`, which is the `W^{1,2}` norm of the plane on every disc and agrees
on the end, up to constants, with the `W^{1,2}` norm of the cylinder.

* **The weight on the end.** The Jacobian of the end lift is `4π² |φ|²`
  (`TauCeti.Floer.PSSPlane.det_fderiv_realChart_cylindricalEndLift`), and the weight times the
  Jacobian is at most `4π²`
  (`TauCeti.Floer.PSSPlane.cylindricalWeight_mul_det_fderiv_realChart_cylindricalEndLift_le`).
  Pointwise, `ρ(w)^(-1/2) ≤ 1 + |w|`
  (`TauCeti.Floer.PSSPlane.inv_sqrt_cylindricalWeight_le`).
* **The realization of `D_u`.** Let `u` solve the Floer equation on the end for the perturbation
  `TauCeti.Floer.PSSPlane.perturbation` of a period-one Hamiltonian `H`, with values in a symplectic
  vector space. Its linearized operator `D_u ξ = ∂s ξ + J(z, u z) ∂t ξ + C(z) ξ`
  (`TauCeti.SymplecticForm.floerLinearization`) has a zeroth-order part `C(w)` that decays only like
  `|w|⁻¹` on the end: there the perturbation is `H(t) dt`, and `dt` has size `|w|⁻¹ / 2π`, while
  the conformal jets carry the factor `ρ^(-1/2) ~ |w|`. Read in end coordinates, the operator
  at `φ(ζ)` is `a D_u - b J D_u` for `(a, b) = dφ (1, 0)`
  (`TauCeti.SymplecticForm.floerLinearization_comp_realChart_cylindricalEndLift`), so on constant
  sections `C_end(ζ) = (a - b J) C(φ ζ)`, and since `a² + b² = 4π² |φ(ζ)|²`,
  `2π |φ(ζ)| ‖C(φ ζ)‖ ≤ (1 + ‖J‖) ‖C_end(ζ)‖`
  (`TauCeti.SymplecticForm.mul_norm_floerLinearizationCoeff_cylindricalEndLift_le`). With
  `ρ^(-1/2) ≤ 2 |w|` on the end, the coefficient field of `D_u` on the conformal jets
  `(√ρ ξ, ∂s ξ, ∂t ξ)` is bounded where the end datum is
  (`TauCeti.SymplecticForm.norm_floerConformalJetCoeff_cylindricalEndLift_le`). Hence, when far out
  on the end `J` is a `C¹` family `J_q(t)` and `u` and its slice defect are bounded, the coefficient
  field is essentially bounded on the plane
  (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_pssPlane`), and
  `TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` from `W^{1,2}` to `L²`.
* **Finite-dimensional kernel and closed range.** The semi-Fredholm estimate of a PSS plane
  (`TauCeti.SymplecticForm.exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy`)
  bounds the `W^{1,2}` norm of the cylinder on the end `ε s > R` and of the plane on the disc
  `|w| ≤ exp (2π R)` by `‖D_u ξ‖_{L²}` and an `L²` norm on a larger disc `K`. Changing variables
  along the end lift, which is injective on a strip of angular width one and maps the half-strip
  `ε s > R`, `0 ≤ t < 1` onto `|w| > exp (2π R)`, the weighted energy of `ξ` on the end is at most
  `4π²` times its energy in end coordinates, and on the disc `ρ ≤ 1`
  (`TauCeti.Floer.PSSPlane.integral_cylindricalWeight_mul_add_le`); on `K` the weight is bounded
  below. So the estimate becomes `‖x‖ ≤ A (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` on the jets `x` of test
  sections, and Peetre's argument gives finite-dimensional kernel
  (`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pssPlane`) and
  closed range (`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_pssPlane`).

The target is a symplectic vector space throughout. The finite cokernel and the index of `D_u` on
the plane are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Fredholm theory of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on Sobolev spaces on Riemann surfaces with cylindrical ends.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)
open scoped ENNReal Topology

namespace TauCeti

namespace Floer.PSSPlane

/-- The **cylindrical weight** of a PSS plane, in the real coordinates `ℝ × ℝ ≃ ℂ`:
`ρ(w) = (1 + |w|²)⁻¹`. The conformal metric `ρ |dw|²` is Euclidean up to constants on every disc,
and its area is at most `4π²` times that of the cylindrical metric `ds² + dt²` of the end
(`TauCeti.Floer.PSSPlane.cylindricalWeight_mul_det_fderiv_realChart_cylindricalEndLift_le`). -/
def cylindricalWeight (z : ℝ × ℝ) : ℝ :=
  (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹

theorem cylindricalWeight_apply (z : ℝ × ℝ) :
    cylindricalWeight z = (1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹ :=
  (rfl)

/-- The cylindrical weight is a conformal weight on the whole plane: it is continuous and
positive. -/
theorem isWeight_cylindricalWeight : ConformalSobolev.IsWeight univ cylindricalWeight where
  isOpen := isOpen_univ
  continuousOn :=
    ((continuous_const.add (Complex.equivRealProdCLM.symm.continuous.norm.pow 2)).inv₀
      fun z ↦ (add_pos_of_pos_of_nonneg one_pos
        (sq_nonneg ‖Complex.equivRealProdCLM.symm z‖)).ne').continuousOn
  pos z _ := by
    rw [cylindricalWeight_apply]
    positivity

/-- The inverse square root of the cylindrical weight at `w` is at most `1 + |w|`. -/
theorem inv_sqrt_cylindricalWeight_le (z : ℝ × ℝ) :
    (√(cylindricalWeight z))⁻¹ ≤ 1 + ‖Complex.equivRealProdCLM.symm z‖ := by
  rw [cylindricalWeight_apply, Real.sqrt_inv, inv_inv]
  have h := norm_nonneg (Complex.equivRealProdCLM.symm z)
  calc √(1 + ‖Complex.equivRealProdCLM.symm z‖ ^ 2)
      ≤ √((1 + ‖Complex.equivRealProdCLM.symm z‖) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 + ‖Complex.equivRealProdCLM.symm z‖ := Real.sqrt_sq (by positivity)

/-- **The cylindrical weight on the end.** The cylindrical weight times the Jacobian of the end
lift is at most `4π²`: the area of the conformal metric `ρ |dw|²` is at most `4π²` times the area
`ds dt` of the cylinder. -/
theorem cylindricalWeight_mul_det_fderiv_realChart_cylindricalEndLift_le (p : PSSPlane)
    (ζ : ℝ × ℝ) :
    cylindricalWeight (realChart p.cylindricalEndLift ζ) *
        (fderiv ℝ (realChart p.cylindricalEndLift) ζ).det ≤ 4 * π ^ 2 := by
  rw [det_fderiv_realChart_cylindricalEndLift, cylindricalWeight_apply, inv_mul_le_iff₀
    (by positivity)]
  nlinarith [sq_nonneg π, sq_nonneg ‖Complex.equivRealProdCLM.symm
    (realChart p.cylindricalEndLift ζ)‖]

/-! ### Comparing the weighted energy with the energies on a disc and on the end -/

section Energy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The weighted density on the end, from the `W^{1,2}` density of the cylinder.** The Jacobian
of the end lift `φ` times the weighted density `ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²` at `φ(ζ)` is at most
`4π²` times the `W^{1,2}` density of `ξ ∘ φ` in the end coordinates. -/
private theorem det_fderiv_mul_cylindricalWeight_le (p : PSSPlane) {ξ : ℝ × ℝ → V}
    {ζ : ℝ × ℝ} (hξ : DifferentiableAt ℝ ξ (realChart p.cylindricalEndLift ζ)) :
    (fderiv ℝ (realChart p.cylindricalEndLift) ζ).det *
        (PSSPlane.cylindricalWeight (realChart p.cylindricalEndLift ζ) *
            ‖ξ (realChart p.cylindricalEndLift ζ)‖ ^ 2 +
          ‖fderiv ℝ ξ (realChart p.cylindricalEndLift ζ) (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ (realChart p.cylindricalEndLift ζ) (0, 1)‖ ^ 2) ≤
      4 * π ^ 2 * (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
        ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c, HasDerivAt p.cylindricalEndLift c (Complex.equivRealProdCLM.symm ζ) :=
    ⟨_, p.hasDerivAt_cylindricalEndLift _⟩
  have hρ := cylindricalWeight_mul_det_fderiv_realChart_cylindricalEndLift_le p ζ
  set φ := realChart p.cylindricalEndLift
  have hconf := le_two_mul_norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq c.re c.im
    (fderiv ℝ ξ (φ ζ) (1, 0)) (fderiv ℝ ξ (φ ζ) (0, 1))
  simp only [stdComplexLineReal, stdComplexLineImag, Function.comp_apply]
  rw [TauCeti.Complex.fderiv_comp_realChart_apply_one_zero hc hξ,
    TauCeti.Complex.fderiv_comp_realChart_apply_zero_one hc hξ]
  rw [TauCeti.Complex.det_fderiv_realChart hc, Complex.normSq_apply] at hρ ⊢
  have hπ : 2 ≤ 4 * π ^ 2 := by nlinarith [Real.two_le_pi]
  nlinarith [sq_nonneg ‖ξ (φ ζ)‖,
    sq_nonneg ‖c.re • fderiv ℝ ξ (φ ζ) (1, 0) + c.im • fderiv ℝ ξ (φ ζ) (0, 1)‖,
    sq_nonneg ‖(-c.im) • fderiv ℝ ξ (φ ζ) (1, 0) + c.re • fderiv ℝ ξ (φ ζ) (0, 1)‖]

/-- On the part `|w| > exp (2π R)` of the plane, the weighted energy of a `C¹` section `ξ` of
compact support is at most `4π²` times the `W^{1,2}` energy of `ξ ∘ φ` on the half-cylinder
`ε s > R`, `0 ≤ t ≤ 1`: the end lift maps the half-strip `ε s > R`, `0 ≤ t < 1` bijectively onto
that part of the plane. -/
private theorem setIntegral_cylindricalWeight_mul_add_le (p : PSSPlane) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) (R : ℝ) :
    ∫ z in {z : ℝ × ℝ | Real.exp (2 * π * R) < ‖Complex.equivRealProdCLM.symm z‖},
        (cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
      4 * π ^ 2 * ∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
          ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) := by
  set band := {s : ℝ | R < p.endSign * s} ×ˢ Ico (0 : ℝ) 1
  have hband : MeasurableSet band :=
    (measurableSet_lt measurable_const (measurable_id.const_mul _)).prod measurableSet_Ico
  have himage : realChart p.cylindricalEndLift '' band =
      {z : ℝ × ℝ | Real.exp (2 * π * R) < ‖Complex.equivRealProdCLM.symm z‖} := by
    ext z
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      exact p.exp_lt_norm_symm_realChart_cylindricalEndLift_iff.2 hζ.1
    · intro hz
      obtain ⟨ζ, hζ1, hζ2, hζz⟩ := p.exists_realChart_cylindricalEndLift_eq hz
      exact ⟨ζ, ⟨hζ1, hζ2⟩, hζz⟩
  -- The lift of `ξ` vanishes far out on the end, so its energy density is integrable there.
  obtain ⟨N, hN⟩ := p.exists_eventuallyEq_zero_comp_realChart_cylindricalEndLift hξc
  obtain ⟨a, b, -, hab, -, -⟩ := exists_Icc_eq_preimage_endSign_mul p (le_max_left R N)
  have hEc := (p.integrableOn_comp_realChart_cylindricalEndLift hξ
    (measurableSet_lt measurable_const (measurable_id.const_mul _)) fun ζ hζ hζab ↦
      hN ζ ((le_max_right R N).trans_lt
        (not_le.1 fun h ↦ hζab ((hab ζ.1).2 ⟨le_of_lt hζ, h⟩)))).const_mul (4 * π ^ 2)
  rw [← himage, integral_image_eq_integral_of_eq_abs_det_smul hband
    ((p.injOn_realChart_cylindricalEndLift 0).mono
      (prod_mono (subset_univ _) (by rw [zero_add])))
    (fun ζ _ ↦ (contDiff_realChart (n := 1) p.contDiff_cylindricalEndLift).differentiable
      one_ne_zero ζ) (fun ζ _ ↦ rfl), ← integral_const_mul]
  -- Pointwise, the pulled-back weighted density is at most `4π²` times the cylinder density.
  refine (integral_mono_of_nonneg (Eventually.of_forall fun ζ ↦ smul_nonneg (abs_nonneg _)
    (add_nonneg (add_nonneg (mul_nonneg (isWeight_cylindricalWeight.pos _ (mem_univ _)).le
      (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)))
    (IntegrableOn.mono_set hEc (prod_mono subset_rfl Ico_subset_Icc_self))
    ((ae_restrict_iff' hband).2 (Eventually.of_forall fun ζ _ ↦ ?_))).trans
    (setIntegral_mono_set hEc (Eventually.of_forall fun ζ ↦ by positivity)
      (Eventually.of_forall (prod_mono subset_rfl Ico_subset_Icc_self)))
  beta_reduce
  rw [smul_eq_mul, abs_of_pos (p.det_fderiv_realChart_cylindricalEndLift_pos ζ)]
  exact det_fderiv_mul_cylindricalWeight_le p ((hξ.differentiable one_ne_zero) _)

/-- **The weighted energy, from the energies on a disc and on the end.** For a `C¹` section `ξ` of
compact support and every `R`, the weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of `ξ` over the
plane is at most its `W^{1,2}` energy on the disc `|w| ≤ exp (2π R)` plus `4π²` times the
`W^{1,2}` energy of `ξ ∘ φ` on the half-cylinder `ε s > R`, `0 ≤ t ≤ 1` of the end. -/
theorem integral_cylindricalWeight_mul_add_le (p : PSSPlane) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) (R : ℝ) :
    ∫ z, (cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ ξ z (0, 1)‖ ^ 2) ≤
      (∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
        (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
          ‖ξ z‖ ^ 2)) +
      4 * π ^ 2 * ∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
          ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2) := by
  set DR := {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)}
  have hDR : IsCompact DR := isCompact_setOf_norm_equivRealProdCLM_symm_le _
  have := hξ.continuous_fderiv one_ne_zero
  have hρc : Continuous cylindricalWeight :=
    continuousOn_univ.1 isWeight_cylindricalWeight.continuousOn
  have hGc : Continuous fun z ↦ cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 := by fun_prop
  -- The weighted density vanishes off the support of `ξ`.
  have hGi : Integrable fun z ↦ cylindricalWeight z * ‖ξ z‖ ^ 2 + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 := hGc.integrable_of_hasCompactSupport (hξc.mono' fun z hz ↦ by
    by_contra h
    have hev : ξ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 h
    exact hz (by simp [hev.eq_of_nhds, hev.fderiv_eq]))
  have hc : DRᶜ = {z : ℝ × ℝ | Real.exp (2 * π * R) < ‖Complex.equivRealProdCLM.symm z‖} := by
    ext z
    simp [DR]
  rw [← integral_add_compl hDR.isClosed.measurableSet hGi, hc]
  gcongr ?_ + ?_
  · -- On the disc the weight is at most `1`.
    have hEp : Continuous fun z ↦ ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2 := by fun_prop
    refine setIntegral_mono_on (hGc.continuousOn.integrableOn_compact hDR)
      (hEp.continuousOn.integrableOn_compact hDR) hDR.isClosed.measurableSet fun z _ ↦ ?_
    have hρ1 : cylindricalWeight z ≤ 1 :=
      inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _))
    have := mul_le_mul_of_nonneg_right hρ1 (sq_nonneg ‖ξ z‖)
    simp only [stdComplexLineReal, stdComplexLineImag]
    linarith
  · exact setIntegral_cylindricalWeight_mul_add_le p hξ hξc R

end Energy

end Floer.PSSPlane

namespace SymplecticForm

open Floer Floer.PSSPlane ConformalSobolev ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : PSSPlane} {H : ℝ → V → ℝ}

/-- **The zeroth-order part of the linearized operator on the end.** Let `u` solve the Floer
equation for the perturbation of the PSS plane `p` at the point `w = φ(ζ)` of the end, with
`ε s ≥ 2`, where `φ` is the end lift, and let each `H(t)` be `C²`. Then the zeroth-order part
`C(w)` of the linearized operator in the coordinate of `ℂ` is controlled by the zeroth-order part
`C_end(ζ)` of the linearized operator of the end datum `H(t) dt` along `u ∘ φ`, with the factor
`2π |w|` of the end lift: `2π |w| ‖C(w)‖ ≤ (1 + ‖J(w, u w)‖) ‖C_end(ζ)‖`. -/
theorem mul_norm_floerLinearizationCoeff_cylindricalEndLift_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ∀ t, ContDiff ℝ 2 (H t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V} {ζ : ℝ × ℝ}
    (hζ : 2 ≤ p.endSign * ζ.1) (hu : DifferentiableAt ℝ u (realChart p.cylindricalEndLift ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart p.cylindricalEndLift ζ) (u (realChart p.cylindricalEndLift ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (realChart p.cylindricalEndLift ζ) : ℝ × ℝ →ₗ[ℝ] V)) :
    2 * π * ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift ζ)‖ *
        ‖ω.floerLinearizationCoeff (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u (realChart p.cylindricalEndLift ζ)‖ ≤
      (1 + ‖(J (realChart p.cylindricalEndLift ζ)
          (u (realChart p.cylindricalEndLift ζ))).toLinearMap.toContinuousLinearMap‖) *
        ‖ω.floerLinearizationCoeff
          (fun ζ' y ↦ (J (realChart p.cylindricalEndLift ζ') y).toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun ζ' ↦ H ζ'.2) (u ∘ realChart p.cylindricalEndLift) ζ‖ := by
  set w := realChart p.cylindricalEndLift ζ
  set C := ω.floerLinearizationCoeff (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u w
  set Ce := ω.floerLinearizationCoeff
    (fun ζ' y ↦ (J (realChart p.cylindricalEndLift ζ') y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun ζ' ↦ H ζ'.2) (u ∘ realChart p.cylindricalEndLift) ζ
  set Jw := J w (u w)
  set a := (fderiv ℝ (realChart p.cylindricalEndLift) ζ stdComplexLineReal).1
  set b := (fderiv ℝ (realChart p.cylindricalEndLift) ζ stdComplexLineReal).2
  set r := 2 * π * ‖Complex.equivRealProdCLM.symm w‖
  -- On constant sections the two linearized operators are their zeroth-order parts, so the
  -- end-coordinate identity `D_end = a D - b J D` becomes `C_end = (a - b J) C`.
  have hid (v : V) : Ce v = a • C v - b • Jw (C v) := by
    have h := ω.floerLinearization_comp_realChart_cylindricalEndLift hH hHs (ξ := fun _ ↦ v) hζ hu
      (differentiableAt_const v) hfl
    have hc : (fun _ : ℝ × ℝ ↦ v) ∘ realChart p.cylindricalEndLift = fun _ ↦ v := rfl
    rw [hc, floerLinearization_eq_add, floerLinearization_eq_add] at h
    simpa only [fderiv_const_apply, FunLike.coe_zero, Pi.zero_apply, map_zero, zero_add,
      Function.comp_apply] using h
  -- The Jacobian of the end lift is `a² + b² = (2π |w|)²`.
  have hdet : a ^ 2 + b ^ 2 = r ^ 2 := by
    have hab : (fderiv ℝ (realChart p.cylindricalEndLift) ζ).det = a ^ 2 + b ^ 2 := by
      rw [ContinuousLinearMap.det,
        (isComplexLinearMap_fderiv_realChart (p.hasDerivAt_cylindricalEndLift _)).det_eq_sq_add_sq,
        ContinuousLinearMap.coe_coe]
    rw [← hab, det_fderiv_realChart_cylindricalEndLift]
  have hr : 0 < r := by
    have hne : Complex.equivRealProdCLM.symm w ≠ 0 := by
      rw [TauCeti.Complex.equivRealProdCLM_symm_realChart]
      exact p.cylindricalEndLift_ne_zero _
    exact mul_pos Real.two_pi_pos (norm_pos_iff.2 hne)
  exact Jw.mul_opNorm_le_of_eq_smul_sub_smul hid hdet hr

/-- **The coefficient field on conformal jets on the end.** Let `u` solve the Floer equation for
the perturbation of the PSS plane `p` at the point `w = φ(ζ)` of the end, with `ε s ≥ 2`, for a
period-one Hamiltonian `H` with each `H(t)` of class `C²`, and let the structures at `w` be
`J(w, ·) = J_q(t)`. If `B` bounds the coefficient field on jets of the end datum `H(t) dt`, with the
structures `J_q(t)`, along `u ∘ φ` at `ζ`, then the coefficient field on the conformal jets of the
cylindrical weight is at most `1 + B + (1 + B) B / π` at `w`. -/
theorem norm_floerConformalJetCoeff_cylindricalEndLift_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ∀ t, ContDiff ℝ 2 (H t))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Jq : ℝ → V → AlmostComplexStructure V}
    {u : ℝ × ℝ → V} {ζ : ℝ × ℝ} (hζ : 2 ≤ p.endSign * ζ.1)
    (hJz : J (realChart p.cylindricalEndLift ζ) = Jq ζ.2)
    (hu : DifferentiableAt ℝ u (realChart p.cylindricalEndLift ζ))
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart p.cylindricalEndLift ζ) (u (realChart p.cylindricalEndLift ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (realChart p.cylindricalEndLift ζ) : ℝ × ℝ →ₗ[ℝ] V)) {B : ℝ}
    (hB : ‖ω.floerJetCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) ζ‖ ≤ B) :
    ‖ω.floerConformalJetCoeff PSSPlane.cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
      (realChart p.cylindricalEndLift ζ)‖ ≤ 1 + B + (1 + B) * B / π := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  rw [floerJetCoeff_def] at hB
  -- The leading coefficient `J(w, u w) = J_q(t)(u w)` and the end coefficient `C_end(ζ)` are
  -- components of the coefficient field on jets of the end datum.
  have hJb : ‖(J (realChart p.cylindricalEndLift ζ)
      (u (realChart p.cylindricalEndLift ζ))).toLinearMap.toContinuousLinearMap‖ ≤ B := by
    rw [hJz]
    exact (norm_le_norm_firstOrderJetCoeff_left _ _).trans hB
  have hCe : ‖ω.floerLinearizationCoeff
      (fun ζ' y ↦ (J (realChart p.cylindricalEndLift ζ') y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun ζ' ↦ H ζ'.2) (u ∘ realChart p.cylindricalEndLift) ζ‖ ≤ B := by
    have heq : ω.floerLinearizationCoeff
        (fun ζ' y ↦ (J (realChart p.cylindricalEndLift ζ') y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun ζ' ↦ H ζ'.2) (u ∘ realChart p.cylindricalEndLift) ζ =
      ω.floerLinearizationCoeff (fun w y ↦ (Jq w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) (u ∘ realChart p.cylindricalEndLift) ζ := by
      ext v
      simp only [floerLinearizationCoeff_apply, Function.comp_apply, hJz]
    rw [heq]
    exact (norm_le_norm_firstOrderJetCoeff_right _ _).trans hB
  -- The zeroth-order part `C(w)` is at most `(1 + B) B / (2π d)` with `d = |w| ≥ 1`, and the
  -- inverse square root of the weight is at most `1 + d ≤ 2 d`.
  have hcmp := ω.mul_norm_floerLinearizationCoeff_cylindricalEndLift_le hH hHs hζ hu hfl
  have hρd := inv_sqrt_cylindricalWeight_le (realChart p.cylindricalEndLift ζ)
  have hd1 : 1 ≤ ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift ζ)‖ := by
    rw [norm_symm_realChart_cylindricalEndLift]
    exact Real.one_le_exp (by nlinarith [Real.two_pi_pos])
  generalize ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift ζ)‖ = d
    at hcmp hρd hd1
  refine (ω.norm_floerConformalJetCoeff_le _ _ _ _ _ _).trans ?_
  have hc := norm_nonneg (ω.floerLinearizationCoeff
    (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
    (realChart p.cylindricalEndLift ζ))
  generalize ‖ω.floerLinearizationCoeff (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
    (realChart p.cylindricalEndLift ζ)‖ = c at hcmp hc ⊢
  have hC : 2 * d * c ≤ (1 + B) * B / π := by
    rw [le_div_iff₀ pi_pos]
    calc 2 * d * c * π = 2 * π * d * c := by ring
      _ ≤ _ := hcmp
      _ ≤ (1 + B) * B := mul_le_mul (by linarith) hCe (norm_nonneg _) (by linarith)
  have hρc : (√(PSSPlane.cylindricalWeight (realChart p.cylindricalEndLift ζ)))⁻¹ * c ≤
      2 * d * c := by
    nlinarith
  calc _ ≤ 1 + B + (√(PSSPlane.cylindricalWeight (realChart p.cylindricalEndLift ζ)))⁻¹ * c := by
        gcongr
    _ ≤ 1 + B + (1 + B) * B / π := by linarith

/-- **The linearized operator of a PSS plane is bounded on `W^{1,2}`.** Let `H` be a jointly `C²`
period-one Hamiltonian, let `u` be `C¹` on the plane, and let the almost complex structures
`J(z, ·)` be `C¹` along the graph of `u`. Suppose that on the part `ε s ≥ T` of the end, with
`T ≥ 2`, read through the end lift `φ`, the structures are a `C¹` family `J_q(t)` of the angular
coordinate `t`, `u` is bounded and solves the Floer equation for the perturbation of the plane, and
the slice defect `∂t (u ∘ φ) - X_{H(t)}(u ∘ φ)` of the end datum is bounded. Then the coefficient
field of the linearized Floer operator on the conformal jets of the cylindrical weight is
essentially bounded on the plane, so that `TauCeti.SymplecticForm.floerConformalSobolevOperator`
realizes `D_u` from `W^{1,2}(ℂ, V)` to `L²(ℂ, V)`. -/
theorem memLp_floerConformalJetCoeff_pssPlane (ω : SymplecticForm V) (hH : Periodic H 1)
    (hHs : ContDiff ℝ 2 (uncurry H)) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 1 fun q : ℝ × V ↦ (Jq q.1 q.2).toLinearMap.toContinuousLinearMap)
    {T : ℝ} (hT : 2 ≤ T)
    (hJend : ∀ ζ : ℝ × ℝ, T ≤ p.endSign * ζ.1 → J (realChart p.cylindricalEndLift ζ) = Jq ζ.2)
    (hfl : ∀ ζ : ℝ × ℝ, T ≤ p.endSign * ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (realChart p.cylindricalEndLift ζ) (u (realChart p.cylindricalEndLift ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
        (realChart p.cylindricalEndLift ζ) : ℝ × ℝ →ₗ[ℝ] V))
    {Cu Cδ : ℝ} (hub : ∀ ζ : ℝ × ℝ, T ≤ p.endSign * ζ.1 →
      ‖u (realChart p.cylindricalEndLift ζ)‖ ≤ Cu)
    (hδ : ∀ ζ : ℝ × ℝ, T ≤ p.endSign * ζ.1 →
      ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t))
        (u ∘ realChart p.cylindricalEndLift) ζ‖ ≤ Cδ) :
    MemLp (ω.floerConformalJetCoeff PSSPlane.cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u) ∞
      (volume.restrict univ) := by
  set M := ω.floerConformalJetCoeff PSSPlane.cylindricalWeight
    (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
  have hcont : ContinuousOn M univ :=
    ω.continuousOn_floerConformalJetCoeff isWeight_cylindricalWeight (fun z _ ↦ hJ z)
      (fun z _ ↦ (contDiff_uncurry_perturbation (p := p) hH hHs 1).contDiffAt)
      (fun z _ ↦ (contDiff_uncurry_perturbation (p := p) hH hHs Complex.I).contDiffAt)
      hu.contDiffOn
  -- On the compact disc `|w| ≤ exp (2π T)` the field is continuous, hence bounded.
  obtain ⟨B₀, hB₀⟩ := (isCompact_setOf_norm_equivRealProdCLM_symm_le
    (Real.exp (2 * π * T))).exists_bound_of_continuousOn (hcont.mono (subset_univ _))
  -- On the end the coefficient field of the end datum is bounded, by the estimate on cylinders.
  obtain ⟨B, hB⟩ := ω.exists_forall_norm_floerJetCoeff_le hHs hJq
    (u ∘ realChart p.cylindricalEndLift) Cu Cδ
  refine memLp_top_of_bound (hcont.aestronglyMeasurable MeasurableSet.univ)
    (max B₀ (1 + B + (1 + B) * B / π)) (Eventually.of_forall fun z ↦ ?_)
  rcases le_or_gt ‖Complex.equivRealProdCLM.symm z‖ (Real.exp (2 * π * T)) with hz | hz
  · exact (hB₀ z hz).trans (le_max_left _ _)
  refine le_max_of_le_right ?_
  -- A point beyond the disc is `φ(ζ)` for some `ζ = (s, t)` with `ε s > T` and `t ∈ [0, 1)`.
  obtain ⟨ζ, hζ1, hζ2, rfl⟩ := p.exists_realChart_cylindricalEndLift_eq hz
  exact ω.norm_floerConformalJetCoeff_cylindricalEndLift_le hH
    (fun t ↦ hHs.comp (contDiff_const.prodMk contDiff_id)) (hT.trans hζ1.le)
    (hJend ζ hζ1.le) ((hu.differentiable one_ne_zero) _) (hfl ζ hζ1.le)
    (hB ζ (Ico_subset_Icc_self hζ2) (hub ζ hζ1.le) (hδ ζ hζ1.le))

/-! ### Peetre's argument on the plane -/

variable {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **The semi-Fredholm estimate in the norm of `W^{1,2}`.** Let the coefficient field of the
linearized Floer operator `D_u` on conformal jets be essentially bounded on the plane, and let `D_u`
satisfy the semi-Fredholm estimate of a PSS plane, with the `W^{1,2}` norm of the cylinder on the
end `ε s > R` and of the plane on the disc `|w| ≤ exp (2π R)`, up to an `L²` norm on the disc
`K = {|w| ≤ exp (2π (R + 1))}`. Then the realization of `D_u` on `W^{1,2}` satisfies the estimate
`‖x‖ ≤ A (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` on the jets `x` of test sections that Peetre's argument
needs. -/
private theorem exists_norm_le_floerConformalSobolevOperator_pssPlane (ω : SymplecticForm V)
    (p : PSSPlane)
    (hM : MemLp (ω.floerConformalJetCoeff PSSPlane.cylindricalWeight J Ks Kt u) ∞
      (volume.restrict univ))
    {C R : ℝ} (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      (∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2)) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖ξ z‖ ^ 2)) :
    ∃ A, ∀ x : H1 V univ PSSPlane.cylindricalWeight,
      (x : Lp (V × V × V) 2 (volume.restrict univ)) ∈
          jetSubmodule V univ PSSPlane.cylindricalWeight →
        ‖x‖ ≤ A * (‖ω.floerConformalSobolevOperator univ PSSPlane.cylindricalWeight J Ks Kt u x‖ +
          ‖restrictWeightedValue V univ
            {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))} x‖) := by
  -- The weighted energy is at most `4π²` times the left side of the semi-Fredholm estimate.
  refine ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le
    isWeight_cylindricalWeight hM (isCompact_setOf_norm_equivRealProdCLM_symm_le _)
    (subset_univ _) (C := 4 * π ^ 2 * C) fun ξ hξ ↦ ?_
  obtain ⟨hξs, hξc, -⟩ := mem_testSection_iff.1 hξ
  have hEp0 : 0 ≤ ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
      (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
        ‖ξ z‖ ^ 2) := setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun _ ↦ by positivity)
  have hπ : 1 ≤ 4 * π ^ 2 := by nlinarith [Real.two_le_pi]
  rw [setIntegral_univ]
  refine (integral_cylindricalWeight_mul_add_le p (hξs.of_le one_le_two) hξc R).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left (hest hξs hξc) (show (0 : ℝ) ≤ 4 * π ^ 2 by positivity),
    mul_le_mul_of_nonneg_left hEp0 (show (0 : ℝ) ≤ 4 * π ^ 2 - 1 by linarith)]

/-- **The linearized operator of a PSS plane has finite-dimensional kernel on `W^{1,2}`.** Let the
coefficient field of `D_u` on the conformal jets of the cylindrical weight be essentially bounded
on the plane (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_pssPlane`), and let `D_u`
satisfy the semi-Fredholm estimate of the PSS plane `p`: for some `C` and `R`, every `C²` section
`ξ` of compact support satisfies

`∫_{ε s > R} (‖∂s (ξ ∘ φ)‖² + ‖∂t (ξ ∘ φ)‖² + ‖ξ ∘ φ‖²) +`
`  ∫_{‖w‖ ≤ e^{2πR}} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{‖w‖ ≤ e^{2π (R + 1)}} ‖ξ‖²)`,

the first integral over `{s | ε s > R} × [0, 1]` in the cylinder coordinates of the end lift `φ`,
as for a finite-energy plane
(`TauCeti.SymplecticForm.exists_forall_le_mul_integral_floerLinearization_add_of_finite_energy`).
Then the realization of `D_u` from `W^{1,2}(ℂ, V)` to `L²(ℂ, V)` has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_pssPlane
    (ω : SymplecticForm V) (p : PSSPlane)
    (hM : MemLp (ω.floerConformalJetCoeff PSSPlane.cylindricalWeight J Ks Kt u) ∞
      (volume.restrict univ))
    {C R : ℝ} (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      (∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2)) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖ξ z‖ ^ 2)) :
    FiniteDimensional ℝ
      (ω.floerConformalSobolevOperator univ PSSPlane.cylindricalWeight J Ks Kt u).ker := by
  obtain ⟨A, hA⟩ := exists_norm_le_floerConformalSobolevOperator_pssPlane ω p hM hest
  exact finiteDimensional_ker_of_estimate isWeight_cylindricalWeight
    (isCompact_setOf_norm_equivRealProdCLM_symm_le _) (subset_univ _) _ hA

/-- **The linearized operator of a PSS plane has closed range on `W^{1,2}`.** Under the
hypotheses of
`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pssPlane`, the
realization of `D_u` from `W^{1,2}(ℂ, V)` to `L²(ℂ, V)` has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_pssPlane
    (ω : SymplecticForm V) (p : PSSPlane)
    (hM : MemLp (ω.floerConformalJetCoeff PSSPlane.cylindricalWeight J Ks Kt u) ∞
      (volume.restrict univ))
    {C R : ℝ} (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      (∫ ζ in {s : ℝ | R < p.endSign * s} ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ (ξ ∘ realChart p.cylindricalEndLift) ζ stdComplexLineImag‖ ^ 2 +
            ‖(ξ ∘ realChart p.cylindricalEndLift) ζ‖ ^ 2)) +
        ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * R)},
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) ≤
        C * ((∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
          ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ Real.exp (2 * π * (R + 1))},
            ‖ξ z‖ ^ 2)) :
    IsClosed
      (Set.range (ω.floerConformalSobolevOperator univ PSSPlane.cylindricalWeight J Ks Kt u)) := by
  obtain ⟨A, hA⟩ := exists_norm_le_floerConformalSobolevOperator_pssPlane ω p hM hest
  simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
    isClosed_range_of_estimate isWeight_cylindricalWeight
    (isCompact_setOf_norm_equivRealProdCLM_symm_le _) (subset_univ _) _ hA

end SymplecticForm

end TauCeti
