/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Sphere
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
public import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Sobolev.Poincare.Slab
import TauCeti.Geometry.Symplectic.Floer.Linearization.Infinity
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Cokernel
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The linearized Floer operator on `W^{1,2}` of the Riemann sphere

Some Floer problems live on a closed domain: the comparison between the pair-of-pants product and
the quantum product deforms Floer data on the sphere with three poles, read in the coordinate
`w ∈ ℂ ≅ ℝ × ℝ` in which the poles are `0`, `1` and `∞`, and the data are unperturbed near `∞`.
This file realizes the linearized Floer operator `D_u` of such data on the Sobolev space of the
round metric of the sphere and proves that the realization is Fredholm.

In the coordinate `w` the round metric is `4 ρ |dw|²` for the conformal weight

`ρ(w) = (1 + |w|²)⁻²` (`TauCeti.Floer.sphereWeight`),

a conformal weight on the whole plane (`TauCeti.Floer.isWeight_sphereWeight`). The Sobolev space
`TauCeti.ConformalSobolev.H1 V univ ρ` of `TauCeti.Analysis.Sobolev.Conformal` is the completion
of the compactly supported sections of the plane in the norm `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)`,
the squared `W^{1,2}` norm of the sphere up to the constant `4` in front of `ρ`, since the
Dirichlet energy is conformally invariant. A point of the plane has capacity zero, so these
sections are dense in `W^{1,2}` of the sphere.

* **The coefficient field.** Suppose that on `‖w‖ ≥ T` the almost complex structures are a fixed
  `J₀` and the Hamiltonian perturbation vanishes. There the zeroth-order part of `D_u` vanishes,
  so the coefficient field of `D_u` on the conformal jets `(√ρ ξ, ∂s ξ, ∂t ξ)` is that of the
  Cauchy–Riemann operator `∂s + J₀ ∂t`; on the compact square `‖w‖ ≤ T` it is continuous. Hence
  it is essentially bounded on the plane, as for every conformal weight on the plane
  (`TauCeti.SymplecticForm.memLp_floerConformalJetCoeff_of_eq_base`), and
  `TauCeti.SymplecticForm.floerConformalSobolevOperator` realizes `D_u` from `W^{1,2}` to `L²`.
* **Finite-dimensional kernel and closed range.** If moreover `J(w, u w)` is compatible with `ω`,
  the semi-Fredholm estimate on the sphere,
  `exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base` in the namespace
  `TauCeti.SymplecticForm`, bounds the norm of `W^{1,2}` by `‖D_u ξ‖_{L²}` and an `L²` norm on a
  compact square, and Peetre's argument gives finite-dimensional kernel
  (`finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base`) and closed range
  (`isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base`), both in the namespace
  `TauCeti.SymplecticForm`.
* **Finite cokernel.** A cokernel element is represented by a square-integrable `C²` covector
  field `η` with `D_u^* η = 0`
  (`exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero`). Near the point at
  infinity, where the data are constant, it is read in the chart `ζ = w⁻¹` as a `(0, 1)`-form
  `η'` which extends smoothly across `ζ = 0`
  (`exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero`).
  A cutoff of `η'` near `ζ = 0` is a compactly supported field of the chart, to which the energy
  estimate of the Cauchy–Riemann operator of `J₀` and the Poincaré inequality on a strip apply;
  they bound the `L²` norm of `η'` near `ζ = 0` by its `L²` norm on an annulus. Changing
  variables along the inversion, `∫ ‖η‖² ≤ A ∫_{|w| ≤ b} ‖η‖²` for every cokernel element, and
  Peetre's argument
  (`finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_integral_norm_sq_le`)
  shows that the cokernel is finite-dimensional
  (`finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base`),
  so that `D_u` is Fredholm (`isFredholm_floerConformalSobolevOperator_sphereWeight_of_eq_base`),
  all in the namespace `TauCeti.SymplecticForm`.

The target is a symplectic vector space. The index of `D_u` is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the Sobolev realization and the semi-Fredholm estimate of real
  Cauchy–Riemann operators on closed surfaces.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Floer problems on the sphere comparing the pair-of-pants and quantum products.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Metric TauCeti.ConformalSobolev
open scoped ENNReal

namespace TauCeti

namespace Floer

/-- The **conformal weight of the Riemann sphere** in the real coordinates `ℝ × ℝ ≃ ℂ`:
`ρ(w) = (1 + |w|²)⁻²`. The round metric of the sphere, of area `4π`, is `4 ρ |dw|²` in the
coordinate `w`. -/
def sphereWeight (z : ℝ × ℝ) : ℝ :=
  ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹

theorem sphereWeight_apply (z : ℝ × ℝ) : sphereWeight z = ((1 + z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ :=
  (rfl)

/-- The conformal weight of the Riemann sphere is a conformal weight on the whole plane: it is
continuous and positive. -/
theorem isWeight_sphereWeight : IsWeight univ sphereWeight where
  isOpen := isOpen_univ
  continuousOn := by
    refine Continuous.continuousOn ?_
    unfold sphereWeight
    exact (by fun_prop : Continuous fun z : ℝ × ℝ ↦ (1 + z.1 ^ 2 + z.2 ^ 2) ^ 2).inv₀
      fun z ↦ by positivity
  pos z _ := by
    rw [sphereWeight_apply]
    positivity

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℝ × ℝ → V → AlmostComplexStructure V}
  {J₀ : AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}

/-- **Peetre's estimate on the sphere.** Under the hypotheses of the semi-Fredholm estimate on the
sphere, `exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base`, the realization
of `D_u` on `W^{1,2}` of the sphere satisfies `‖x‖ ≤ A (‖D_u x‖ + ‖√ρ ξ‖_{L²(K)})` on the jets `x`
of test sections, for a compact square `K`. -/
private theorem exists_norm_le_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V) (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    ∃ R A, ∀ x : H1 V univ sphereWeight,
      (x : Lp (V × V × V) 2 (volume.restrict univ)) ∈ jetSubmodule V univ sphereWeight →
        ‖x‖ ≤ A * (‖ω.floerConformalSobolevOperator univ sphereWeight
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u x‖ +
          ‖restrictWeightedValue V univ (closedBall 0 R) x‖) := by
  obtain ⟨R, C, -, hest⟩ :=
    exists_forall_integral_le_mul_integral_floerLinearization_add_of_eq_base hJ₀ hKs₀ hKt₀ hJ hKs
      hKt hu hc
  obtain ⟨A, hA⟩ :=
    ω.exists_forall_norm_le_mul_norm_floerConformalSobolevOperator_add_of_integral_le
      isWeight_sphereWeight
      (ω.memLp_floerConformalJetCoeff_of_eq_base isWeight_sphereWeight
        (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        (fun z hz y ↦ by rw [hJ₀ z hz y]) hKs₀ hKt₀ hJ hKs hKt hu)
      (isCompact_closedBall 0 R) (subset_univ _) (C := C) fun ξ hξ ↦ by
        obtain ⟨hξs, hξc, -⟩ := mem_testSection_iff.1 hξ
        simpa only [setIntegral_univ, sphereWeight_apply, stdComplexLineReal_eq,
          stdComplexLineImag_eq] using hest hξs hξc
  exact ⟨R, A, hA⟩

/-- **The linearized operator on the sphere has finite-dimensional kernel on `W^{1,2}`.** Let the
Floer data `J`, `K_s`, `K_t` on the plane `ℝ × ℝ ≅ ℂ` be the fixed structure `J₀` and the zero
perturbation on `‖w‖ ≥ T`, a neighbourhood of the point at infinity of the sphere. Let `J` be `C¹`
and `K_s`, `K_t` be `C²` along a `C¹` map `u`, with `J(w, u w)` compatible. Then the realization of
`D_u` from `W^{1,2}` of the sphere to `L²` has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).ker := by
  obtain ⟨R, A, hA⟩ := exists_norm_le_floerConformalSobolevOperator_sphereWeight_of_eq_base ω
    hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc
  exact finiteDimensional_ker_of_estimate isWeight_sphereWeight (isCompact_closedBall 0 R)
    (subset_univ _) _ hA

/-- **The linearized operator on the sphere has closed range on `W^{1,2}`.** Under the hypotheses
of `finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base`, the realization
of `D_u` from `W^{1,2}` of the sphere to `L²` has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 1 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    IsClosed (Set.range (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u)) := by
  obtain ⟨R, A, hA⟩ := exists_norm_le_floerConformalSobolevOperator_sphereWeight_of_eq_base ω
    hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc
  simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
    isClosed_range_of_estimate isWeight_sphereWeight (isCompact_closedBall 0 R) (subset_univ _) _ hA

end SymplecticForm

/-! ### The cokernel on the sphere -/

namespace SymplecticForm

open Floer
open scoped Topology

section Cokernel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℝ × ℝ → V → AlmostComplexStructure V}
  {J₀ : AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}

/-- **The `L²` norm of a field of the chart from its adjoint.** For a constant `ω`-compatible
structure `J₀` and the zero perturbation, a compactly supported `C²` covector field `g` vanishing on
`|ζ| ≥ a` satisfies `∫ ‖g‖² ≤ (2a)² C ∫ ‖D₀^* g‖²`: the Poincaré inequality on the strip
`|Im ζ| ≤ a` bounds `∫ ‖g‖²` by the Dirichlet energy, and the energy estimate of constant data
bounds that by the `L²` norm of the adjoint. -/
private theorem exists_integral_norm_sq_le_mul_integral_floerLinearizationAdjoint_const
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃a : ℝ⦄ ⦃g : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 g → HasCompactSupport g →
      (∀ ζ, a ≤ ‖Complex.equivRealProdCLM.symm ζ‖ → g ζ = 0) →
      ∫ ζ, ‖g ζ‖ ^ 2 ≤ (2 * a) ^ 2 * C * ∫ ζ, ‖ω.floerLinearizationAdjoint
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 g
          ζ‖ ^ 2 := by
  obtain ⟨C, hC, hE⟩ := exists_forall_integral_norm_fderiv_sq_le_of_const (ω := ω) h₀
  refine ⟨C, hC, fun a g hg hgc hga ↦ ?_⟩
  have hP := integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_abs_snd (r := a)
    (hg.of_le one_le_two) hgc fun ζ hζ ↦ hga ζ (hζ.trans (by
      simpa using Complex.abs_im_le_norm (Complex.equivRealProdCLM.symm ζ)))
  rw [← stdComplexLineImag_eq] at hP
  have iD := integrable_norm_fderiv_sq_add (μ := volume) (hg.of_le one_le_two) hgc
    stdComplexLineReal stdComplexLineImag
  have hI : ∫ ζ, ‖fderiv ℝ g ζ stdComplexLineImag‖ ^ 2 ≤
      ∫ ζ, (‖fderiv ℝ g ζ stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ g ζ stdComplexLineImag‖ ^ 2) :=
    integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) iD
      (ae_of_all _ fun ζ ↦ by simp only; nlinarith [sq_nonneg ‖fderiv ℝ g ζ stdComplexLineReal‖])
  calc _ ≤ (2 * a) ^ 2 * ∫ ζ, (‖fderiv ℝ g ζ stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ g ζ stdComplexLineImag‖ ^ 2) :=
        hP.trans (mul_le_mul_of_nonneg_left hI (sq_nonneg _))
    _ ≤ (2 * a) ^ 2 * (C * _) := mul_le_mul_of_nonneg_left (hE hg hgc) (sq_nonneg _)
    _ = _ := by ring

/-- **The adjoint of a cut-off field of the chart, pointwise.** Let `η₀` be smooth on the disc
`|ζ| < ρ₀` and annihilated there, off `ζ = 0`, by the adjoint `D₀^*` of the constant data `J₀`,
`0`. Let `χ` be a cutoff whose derivative has norm at most `M` and vanishes off the annulus
`r ≤ |ζ| ≤ 2r`, and which vanishes on `|ζ| ≥ 2r`, with `2r < ρ₀`. Then at every `ζ ≠ 0`,
`‖D₀^* (χ η₀)‖² ≤ (M (1 + ‖J₀‖))² ‖η₀‖²` on the annulus, and `D₀^* (χ η₀) = 0` off it. -/
private theorem norm_floerLinearizationAdjoint_const_smul_sq_le_indicator (ω : SymplecticForm V)
    {r ρ₀ M : ℝ} (h2r : 2 * r < ρ₀) {η₀ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη₀ : ContDiffOn ℝ (⊤ : ℕ∞) η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀})
    (hη₀D : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
      ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₀ ζ = 0)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχ0 : ∀ ζ, 2 * r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ → χ ζ = 0)
    (hχd0 : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < r → fderiv ℝ χ ζ = 0)
    (hχd2 : ∀ ζ, 2 * r < ‖Complex.equivRealProdCLM.symm ζ‖ → fderiv ℝ χ ζ = 0)
    (hχM : ∀ ζ, ‖fderiv ℝ χ ζ‖ ≤ M) {ζ : ℝ × ℝ} (hζ0 : Complex.equivRealProdCLM.symm ζ ≠ 0) :
    ‖ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 (fun ζ ↦ χ ζ • η₀ ζ) ζ‖ ^ 2 ≤
      (M * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖)) ^ 2 *
        ({ζ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖} ∩
          {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}).indicator (fun ζ ↦ ‖η₀ ζ‖ ^ 2) ζ := by
  set D₀ := ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ 0) (0 : ℝ × ℝ → V)
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  have hν : Continuous ν := Complex.equivRealProdCLM.symm.continuous.norm
  set g : ℝ × ℝ → V →L[ℝ] ℝ := fun ζ ↦ χ ζ • η₀ ζ
  by_cases hζ : ν ζ < ρ₀
  · have hle : ‖D₀ g ζ‖ ≤ |χ ζ| * ‖D₀ η₀ ζ‖ +
        ‖fderiv ℝ χ ζ‖ * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) * ‖η₀ ζ‖ :=
      ω.norm_floerLinearizationAdjoint_fun_smul_le ((hχ.differentiable one_ne_zero) ζ)
        ((hη₀.differentiableOn (by simp)).differentiableAt
          ((isOpen_lt hν continuous_const).mem_nhds hζ))
        (differentiableAt_const _)
    rw [hη₀D ζ hζ hζ0, norm_zero, mul_zero, zero_add] at hle
    by_cases hA : r ≤ ν ζ ∧ ν ζ ≤ 2 * r
    · rw [indicator_of_mem hA]
      calc ‖D₀ g ζ‖ ^ 2 ≤ (M * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) * ‖η₀ ζ‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hle.trans (by gcongr; exact hχM ζ)) 2
        _ = _ := by ring
    · rw [indicator_of_notMem hA, mul_zero]
      -- Off the annulus the derivative of `χ` vanishes.
      have hd : fderiv ℝ χ ζ = 0 := by
        rcases not_and_or.1 hA with h | h
        · exact hχd0 ζ (not_le.1 h)
        · exact hχd2 ζ (not_le.1 h)
      rw [hd, norm_zero, zero_mul, zero_mul] at hle
      rw [norm_le_zero_iff.1 hle, norm_zero]
      simp
  · -- Off the disc `|ζ| < ρ₀` the cut-off field vanishes near `ζ`.
    have hts : tsupport g ⊆ {ζ | ν ζ ≤ 2 * r} :=
      closure_minimal (fun ζ hζ ↦ by
        simp only [mem_ofPred_eq]
        exact not_lt.1 fun h ↦ hζ (by simp [g, hχ0 ζ h.le]))
        (isClosed_le hν continuous_const)
    have h0 : D₀ g ζ = 0 := floerLinearizationAdjoint_of_notMem_tsupport fun h ↦ by
      have := hts h
      simp only [mem_ofPred_eq] at this
      linarith [not_lt.1 hζ]
    rw [h0]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)

/-- **The adjoint of a cut-off field of the chart.** Under the hypotheses of
`norm_floerLinearizationAdjoint_const_smul_sq_le_indicator`,
`∫ ‖D₀^* (χ η₀)‖² ≤ (M (1 + ‖J₀‖))² ∫_{r ≤ |ζ| ≤ 2r} ‖η₀‖²`. -/
private theorem integral_norm_floerLinearizationAdjoint_const_smul_sq_le (ω : SymplecticForm V)
    {r ρ₀ M : ℝ} (h2r : 2 * r < ρ₀) {η₀ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη₀ : ContDiffOn ℝ (⊤ : ℕ∞) η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀})
    (hη₀D : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
      ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₀ ζ = 0)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχ0 : ∀ ζ, 2 * r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ → χ ζ = 0)
    (hχd0 : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < r → fderiv ℝ χ ζ = 0)
    (hχd2 : ∀ ζ, 2 * r < ‖Complex.equivRealProdCLM.symm ζ‖ → fderiv ℝ χ ζ = 0)
    (hχM : ∀ ζ, ‖fderiv ℝ χ ζ‖ ≤ M) :
    ∫ ζ, ‖ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 (fun ζ ↦ χ ζ • η₀ ζ) ζ‖ ^ 2 ≤
      (M * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖)) ^ 2 *
        ∫ ζ in {ζ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖} ∩
          {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}, ‖η₀ ζ‖ ^ 2 := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set Ann := {ζ : ℝ × ℝ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖} ∩
    {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}
  have hAnnK : IsCompact Ann :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * r)).inter_left
      (isClosed_le continuous_const Complex.equivRealProdCLM.symm.continuous.norm)
  have hiAnn : IntegrableOn (fun ζ ↦ ‖η₀ ζ‖ ^ 2) Ann :=
    ((hη₀.continuousOn.mono fun ζ (hζ : ζ ∈ Ann) ↦ lt_of_le_of_lt hζ.2 h2r).norm.pow
      2).integrableOn_compact hAnnK
  rw [← integral_indicator hAnnK.measurableSet, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _)
    ((hiAnn.integrable_indicator hAnnK.measurableSet).const_mul _) ?_
  filter_upwards [Measure.ae_ne volume 0] with ζ hζ0
  exact norm_floerLinearizationAdjoint_const_smul_sq_le_indicator ω h2r hη₀ hη₀D hχ hχ0 hχd0 hχd2
    hχM fun h ↦ hζ0 (Complex.equivRealProdCLM.symm.map_eq_zero_iff.1 h)

/-- **The estimate in the chart at infinity.** Let `J₀` be `ω`-compatible, and let `0 < r` with
`2r < ρ₀`. There is `c ≥ 0` such that every covector field `η₀`, smooth on the disc `|ζ| < ρ₀` and
annihilated there, off `ζ = 0`, by the adjoint of the constant data `J₀`, `0`, satisfies
`∫_{|ζ| ≤ r} ‖η₀‖² ≤ c ∫_{r ≤ |ζ| ≤ 2r} ‖η₀‖²`. The cutoff `χ η₀`, equal to `η₀` on `|ζ| ≤ r`, is
a compactly supported field of the chart, and its adjoint only involves the derivative of `χ`. -/
private theorem exists_setIntegral_norm_sq_le_mul_setIntegral_annulus (ω : SymplecticForm V)
    (h₀ : ω.Compatible J₀) {r ρ₀ : ℝ} (hr : 0 < r) (h2r : 2 * r < ρ₀) :
    ∃ c, 0 ≤ c ∧ ∀ ⦃η₀ : ℝ × ℝ → V →L[ℝ] ℝ⦄,
      ContDiffOn ℝ (⊤ : ℕ∞) η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀} →
      (∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
        ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₀ ζ = 0) →
      ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r}, ‖η₀ ζ‖ ^ 2 ≤
        c * ∫ ζ in {ζ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖} ∩
          {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}, ‖η₀ ζ‖ ^ 2 := by
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  have hν : Continuous ν := Complex.equivRealProdCLM.symm.continuous.norm
  obtain ⟨C, hC, hPE⟩ :=
    exists_integral_norm_sq_le_mul_integral_floerLinearizationAdjoint_const ω h₀
  obtain ⟨χ, hχs, -, hχ1, hχ0, hχd0, hχd2, hχM⟩ :=
    exists_contDiff_cutoff_comp_continuousLinearMap
      (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) hr
  set M := 2 * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖ / r
  refine ⟨(2 * (2 * r)) ^ 2 * C * (M * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖)) ^ 2,
    by positivity, fun η₀ hη₀ hη₀D ↦ ?_⟩
  have hUd : IsOpen {ζ : ℝ × ℝ | ν ζ < ρ₀} := isOpen_lt hν continuous_const
  -- The cut-off field `g = χ η₀` is a compactly supported `C²` field of the chart.
  set g : ℝ × ℝ → V →L[ℝ] ℝ := fun ζ ↦ χ ζ • η₀ ζ
  have hgz (ζ : ℝ × ℝ) (hζ : 2 * r < ν ζ) : g =ᶠ[𝓝 ζ] 0 := by
    filter_upwards [(isOpen_lt continuous_const hν).mem_nhds hζ] with ζ' h
    simp [g, hχ0 ζ' h.le]
  have hg : ContDiff ℝ 2 g := contDiff_iff_contDiffAt.2 fun ζ ↦ by
    by_cases hζ : ν ζ < ρ₀
    · exact (hχs.of_le (by simp)).contDiffAt.smul
        ((hη₀.contDiffAt (hUd.mem_nhds hζ)).of_le (WithTop.coe_le_coe.2 le_top))
    · exact contDiffAt_const.congr_of_eventuallyEq (hgz ζ (by linarith [not_lt.1 hζ]))
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * r))
      fun ζ hζ ↦ (hgz ζ (not_le.1 hζ)).self_of_nhds
  have hX : ∫ ζ in {ζ | ν ζ ≤ r}, ‖η₀ ζ‖ ^ 2 ≤ ∫ ζ, ‖g ζ‖ ^ 2 := by
    rw [setIntegral_congr_fun (isCompact_setOf_norm_equivRealProdCLM_symm_le r).measurableSet
      (g := fun ζ ↦ ‖g ζ‖ ^ 2) fun ζ hζ ↦ by simp [g, hχ1 ζ hζ]]
    exact setIntegral_le_integral (hg.continuous.integrable_norm_sq_of_hasCompactSupport hgc)
      (ae_of_all _ fun _ ↦ sq_nonneg _)
  calc _ ≤ ∫ ζ, ‖g ζ‖ ^ 2 := hX
    _ ≤ (2 * (2 * r)) ^ 2 * C * _ := hPE hg hgc fun ζ hζ ↦ by simp [g, hχ0 ζ hζ]
    _ ≤ (2 * (2 * r)) ^ 2 * C * ((M * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖)) ^ 2 * _) :=
        mul_le_mul_of_nonneg_left (integral_norm_floerLinearizationAdjoint_const_smul_sq_le ω h2r
          hη₀ hη₀D (hχs.of_le (by simp)) hχ0 hχd0 hχd2 hχM) (by positivity)
    _ = _ := by ring

/-- **The part of the plane near infinity, through the inversion.** Let `η₀` agree, on the
punctured disc `0 < |ζ| < ρ₀`, with the form `η' = η (ζ⁻¹) ∘ (a + b J₀)` read through the inversion
`ι`, and let `0 < r < ρ₀`. The part `|w| ≥ r⁻¹` of the plane is the image of the punctured disc
`0 < |ζ| ≤ r`, and `∫_{|w| ≥ r⁻¹} ‖η‖² ≤ (1 + ‖J₀‖)² ∫_{|ζ| ≤ r} ‖η₀‖²`. -/
private theorem setIntegral_norm_sq_le_of_eq_covectorPullback_realChart_inv
    {η η₀ : ℝ × ℝ → V →L[ℝ] ℝ} {r ρ₀ : ℝ} (hr : 0 < r) (hrρ : r < ρ₀)
    (hη₀ : ContinuousOn η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀})
    (hη₀eq : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
      η₀ ζ = covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η ζ) :
    ∫ w in {w | r⁻¹ ≤ ‖Complex.equivRealProdCLM.symm w‖}, ‖η w‖ ^ 2 ≤
      (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 *
        ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r}, ‖η₀ ζ‖ ^ 2 := by
  set ι : ℝ × ℝ → ℝ × ℝ := TauCeti.Complex.realChart (·⁻¹)
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  set Br := {ζ : ℝ × ℝ | ν ζ ≤ r}
  have hBr : IsCompact Br := isCompact_setOf_norm_equivRealProdCLM_symm_le r
  set S := {ζ : ℝ × ℝ | 0 < ν ζ} ∩ Br
  have hSm : MeasurableSet S := (measurableSet_lt measurable_const
    Complex.equivRealProdCLM.symm.continuous.norm.measurable).inter hBr.measurableSet
  have hS0 (ζ : ℝ × ℝ) (hζ : ζ ∈ S) : Complex.equivRealProdCLM.symm ζ ≠ 0 := norm_pos_iff.1 hζ.1
  have hιS : ι '' S = {w | r⁻¹ ≤ ν w} := by
    rw [TauCeti.Complex.realChart_inv_involutive.image_eq_preimage_symm]
    ext w
    simp only [S, Br, ν, mem_preimage, mem_inter_iff, mem_ofPred_eq,
      TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv]
    constructor
    · rintro ⟨h1, h2⟩
      exact (inv_le_comm₀ (inv_pos.1 h1) hr).1 h2
    · intro h
      have hw : 0 < ‖Complex.equivRealProdCLM.symm w‖ := (inv_pos.2 hr).trans_le h
      exact ⟨inv_pos.2 hw, (inv_le_comm₀ hw hr).2 h⟩
  have hBrU (ζ : ℝ × ℝ) (hζ : ζ ∈ Br) : ν ζ < ρ₀ := lt_of_le_of_lt (b := r) hζ hrρ
  have hiBr : IntegrableOn (fun ζ ↦ ‖η₀ ζ‖ ^ 2) Br :=
    ((hη₀.mono hBrU).norm.pow 2).integrableOn_compact hBr
  rw [← hιS, integral_image_realChart_inv hSm hS0, ← integral_const_mul]
  simp only [smul_eq_mul]
  refine (integral_mono_of_nonneg (ae_restrict_of_forall_mem hSm fun ζ hζ ↦ ?_)
    ((hiBr.mono_set (inter_subset_right : S ⊆ Br)).const_mul _)
    (ae_restrict_of_forall_mem hSm fun ζ hζ ↦ ?_)).trans
      (setIntegral_mono_set (hiBr.const_mul _) (ae_of_all _ fun _ ↦ by positivity)
        (ae_of_all _ fun _ h ↦ h.2))
  · have h : (fderiv ℝ ι ζ).det = ν (ι ζ) ^ 4 := TauCeti.Complex.det_fderiv_realChart_inv (hS0 ζ hζ)
    rw [Pi.zero_apply, h]
    positivity
  · have h := (det_mul_norm_sq_le_and_norm_covectorPullback_realChart_sq_le
      (hasDerivAt_inv (hS0 ζ hζ)) (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 (hS0 ζ hζ))))
      (fun _ _ ↦ J₀) 0 η).1
    rwa [← hη₀eq ζ (hBrU ζ hζ.2) (hS0 ζ hζ)] at h

/-- **The annulus of the chart at infinity, through the inversion.** Let `η₀` agree, on the
punctured disc `0 < |ζ| < ρ₀`, with the form `η' = η (ζ⁻¹) ∘ (a + b J₀)` read through the inversion
`ι`, for a continuous square-integrable `η`, and let `0 < r` with `2r < ρ₀`. The image of the
annulus `r ≤ |ζ| ≤ 2r` lies in the disc `|w| ≤ r⁻¹`, and
`∫_{r ≤ |ζ| ≤ 2r} ‖η₀‖² ≤ (1 + ‖J₀‖)² ∫_{|w| ≤ r⁻¹} ‖η‖²`. -/
private theorem setIntegral_annulus_norm_sq_le_of_eq_covectorPullback_realChart_inv
    {η η₀ : ℝ × ℝ → V →L[ℝ] ℝ} (hη : Continuous η) (hηi : Integrable fun z ↦ ‖η z‖ ^ 2)
    {r ρ₀ : ℝ} (hr : 0 < r) (h2r : 2 * r < ρ₀)
    (hη₀eq : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < ρ₀ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
      η₀ ζ = covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η ζ) :
    ∫ ζ in {ζ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖} ∩
        {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}, ‖η₀ ζ‖ ^ 2 ≤
      (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 *
        ∫ w in {w | ‖Complex.equivRealProdCLM.symm w‖ ≤ r⁻¹}, ‖η w‖ ^ 2 := by
  set ι : ℝ × ℝ → ℝ × ℝ := TauCeti.Complex.realChart (·⁻¹)
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  have hν : Continuous ν := Complex.equivRealProdCLM.symm.continuous.norm
  set Ann := {ζ : ℝ × ℝ | r ≤ ν ζ} ∩ {ζ | ν ζ ≤ 2 * r}
  have hAnnK : IsCompact Ann :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * r)).inter_left
      (isClosed_le continuous_const hν)
  have hAnn0 (ζ : ℝ × ℝ) (hζ : ζ ∈ Ann) : Complex.equivRealProdCLM.symm ζ ≠ 0 :=
    norm_pos_iff.1 (hr.trans_le hζ.1)
  have hιAnn : ι '' Ann ⊆ {w | ν w ≤ r⁻¹} := by
    rintro _ ⟨ζ, hζ, rfl⟩
    simp only [ν, ι, mem_ofPred_eq, TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv]
    exact inv_anti₀ hr hζ.1
  -- The density `det dι ‖η ∘ ι‖²` is continuous on the compact annulus.
  have hiAnn : IntegrableOn (fun ζ ↦ (fderiv ℝ ι ζ).det * ‖η (ι ζ)‖ ^ 2) Ann := by
    have hιc : ContinuousOn ι Ann := fun ζ hζ ↦
      (TauCeti.Complex.contDiffAt_realChart_inv (hAnn0 ζ hζ) (n := 0)).continuousAt
        |>.continuousWithinAt
    refine IntegrableOn.congr_fun (f := fun ζ ↦ ν (ι ζ) ^ 4 * ‖η (ι ζ)‖ ^ 2) ?_
      (fun ζ hζ ↦ by rw [TauCeti.Complex.det_fderiv_realChart_inv (hAnn0 ζ hζ)])
      hAnnK.measurableSet
    exact (((hν.comp_continuousOn hιc).pow 4).mul
      ((hη.comp_continuousOn hιc).norm.pow 2)).integrableOn_compact hAnnK
  calc ∫ ζ in Ann, ‖η₀ ζ‖ ^ 2 ≤
        ∫ ζ in Ann, (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 *
          ((fderiv ℝ ι ζ).det * ‖η (ι ζ)‖ ^ 2) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (hiAnn.const_mul _)
          (ae_restrict_of_forall_mem hAnnK.measurableSet fun ζ hζ ↦ by
            have h := (det_mul_norm_sq_le_and_norm_covectorPullback_realChart_sq_le
              (hasDerivAt_inv (hAnn0 ζ hζ))
              (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 (hAnn0 ζ hζ)))) (fun _ _ ↦ J₀) 0 η).2
            rwa [← hη₀eq ζ (lt_of_le_of_lt hζ.2 h2r) (hAnn0 ζ hζ)] at h)
    _ = (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 * ∫ w in ι '' Ann, ‖η w‖ ^ 2 := by
        -- `ι` is the local name of the inversion, so the two sides agree after unfolding it.
        rw [integral_const_mul, integral_image_realChart_inv hAnnK.measurableSet hAnn0]
        simp only [smul_eq_mul, ι]
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_mono_set hηi.integrableOn
        (ae_of_all _ fun _ ↦ sq_nonneg _) (ae_of_all _ hιAnn)) (sq_nonneg _)

/-- **Cokernel elements in the chart at infinity.** Let the Floer data be an `ω`-compatible
structure `J₀` and the zero perturbation on `‖w‖ ≥ T`, and let `2T ≤ T₁` with `0 < T₁`. A
square-integrable `C²` covector field `η` with `D_u^* η = 0`, read in the chart `ζ = w⁻¹` as the
form `η' = η (ζ⁻¹) ∘ (a + b J₀)`, agrees off `ζ = 0` with a field `η₀` smooth on the disc
`|ζ| < T₁⁻¹` and annihilated there, off `ζ = 0`, by the adjoint of the constant data `J₀`, `0`. -/
private theorem exists_contDiffOn_eq_covectorPullback_inv_and_floerLinearizationAdjoint_eq_zero
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0) {T₁ : ℝ} (hT₁ : 0 < T₁) (h2T : 2 * T ≤ T₁)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η)
    (hD : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η z = 0) (hηi : Integrable fun z ↦ ‖η z‖ ^ 2) :
    ∃ η₀ : ℝ × ℝ → V →L[ℝ] ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < T₁⁻¹} ∧
      (∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < T₁⁻¹ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
        η₀ ζ = covectorPullback (TauCeti.Complex.realChart (·⁻¹))
          (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η ζ) ∧
      ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < T₁⁻¹ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
        ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₀ ζ = 0 := by
  set ι : ℝ × ℝ → ℝ × ℝ := TauCeti.Complex.realChart (·⁻¹)
  set J₀' := J₀.toLinearMap.toContinuousLinearMap
  set D₀ := ω.floerLinearizationAdjoint (fun _ _ ↦ J₀') (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ 0)
    (0 : ℝ × ℝ → V)
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  have hν : Continuous ν := Complex.equivRealProdCLM.symm.continuous.norm
  -- Near infinity the adjoint is that of the constant data, so `η'` extends across `ζ = 0`.
  have hD₀ (w : ℝ × ℝ) (hw : T₁ < ν w) : D₀ η w = 0 := by
    have h := floerLinearizationAdjoint_eq_const_of_eq_base (ω := ω) (u := u) hJ₀ hKs₀ hKt₀ η
      (w := w) (by simp only [ν] at hw; linarith)
    rw [hD w] at h
    exact h.symm
  obtain ⟨η₀, hη₀, hη₀eq⟩ :=
    exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero h₀.invariant
      (0 : ℝ × ℝ → V) (η := η) (T := T₁) (fun z _ ↦ hη.differentiable two_ne_zero z)
      (fun z hz ↦ hD₀ z hz) hηi.integrableOn
  refine ⟨η₀, hη₀, hη₀eq, fun ζ hζ hζ0 ↦ ?_⟩
  -- Near `ζ ≠ 0` the field `η₀` is `η'`, whose adjoint is the Jacobian times `D₀ η` at `ζ⁻¹`.
  have hev : η₀ =ᶠ[𝓝 ζ] covectorPullback ι (fun _ _ ↦ J₀') 0 η := by
    filter_upwards [(isOpen_lt hν continuous_const).mem_nhds hζ,
      (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds hζ0]
      with ζ' h1 h2
    exact hη₀eq ζ' h1 h2
  have h1 : D₀ η₀ ζ = D₀ (covectorPullback ι (fun _ _ ↦ J₀') 0 η) ζ :=
    ω.floerLinearizationAdjoint_congr_of_eventuallyEq _ _ _ _ hev
  have h2 : D₀ (covectorPullback ι (fun _ _ ↦ J₀') 0 η) ζ = ν (ι ζ) ^ 4 • D₀ η (ι ζ) :=
    floerLinearizationAdjoint_const_covectorPullback_realChart_inv hζ0
      (hη.differentiable two_ne_zero _)
  rw [h1, h2, hD₀ _ ?_, smul_zero]
  simp only [ν, ι, TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv]
  exact (lt_inv_comm₀ (norm_pos_iff.2 hζ0) hT₁).1 hζ

/-- **The `L²` norm of a cokernel element on the sphere is controlled on a disc.** Let the Floer
data be an `ω`-compatible structure `J₀` and the zero perturbation on `‖w‖ ≥ T`. Then there are
`A` and `b` such that every square-integrable `C²` covector field `η` with `D_u^* η = 0` satisfies
`∫ ‖η‖² ≤ A ∫_{|w| ≤ b} ‖η‖²`.

Near the point at infinity `η` is read in the chart `ζ = w⁻¹` as a form which extends smoothly
across `ζ = 0` and is annihilated there by the adjoint of the constant data. The estimate in the
chart bounds its `L²` norm on `|ζ| ≤ r` by that on the annulus `r ≤ |ζ| ≤ 2r`, and changing
variables along the inversion turns `|ζ| ≤ r` into `|w| ≥ r⁻¹` and the annulus into a part of the
disc `|w| ≤ r⁻¹`. -/
private theorem exists_integral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero_of_eq_base
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0) :
    ∃ A b, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, ‖η z‖ ^ 2 ≤ A * ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}, ‖η z‖ ^ 2 := by
  set NJ := ‖J₀.toLinearMap.toContinuousLinearMap‖
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  -- The radii: the data are constant on `|w| > T₁`, and the cutoff lives on `|ζ| ≤ 2r < T₁⁻¹`.
  set T₁ := 2 * max T 1
  have hT₁ : 0 < T₁ := by positivity
  have h2T : 2 * T ≤ T₁ := by simp only [T₁]; linarith [le_max_left T 1]
  set r := (4 * T₁)⁻¹
  have hr : 0 < r := by positivity
  have h2r : 2 * r < T₁⁻¹ := by
    simp only [r, mul_inv]
    nlinarith [inv_pos.2 hT₁]
  obtain ⟨c, hc0, hchart⟩ := exists_setIntegral_norm_sq_le_mul_setIntegral_annulus ω h₀ hr h2r
  refine ⟨1 + (1 + NJ) ^ 2 * c * (1 + NJ) ^ 2, r⁻¹, fun η hη hD hηi ↦ ?_⟩
  obtain ⟨η₀, hη₀, hη₀eq, hη₀D⟩ :=
    exists_contDiffOn_eq_covectorPullback_inv_and_floerLinearizationAdjoint_eq_zero ω h₀ hJ₀ hKs₀
      hKt₀ hT₁ h2T hη hD hηi
  have hG1 := setIntegral_norm_sq_le_of_eq_covectorPullback_realChart_inv hr
    (by linarith : r < T₁⁻¹) hη₀.continuousOn hη₀eq
  have hG2 := setIntegral_annulus_norm_sq_le_of_eq_covectorPullback_realChart_inv hη.continuous
    hηi hr h2r hη₀eq
  have hY := hchart hη₀ hη₀D
  -- Assembling: the part `|w| > r⁻¹` is controlled by the disc `|w| ≤ r⁻¹`.
  set P := ∫ w in {w | ν w ≤ r⁻¹}, ‖η w‖ ^ 2
  have hKb : MeasurableSet {w : ℝ × ℝ | ν w ≤ r⁻¹} :=
    measurableSet_le Complex.equivRealProdCLM.symm.continuous.norm.measurable measurable_const
  have hout : ∫ w in {w | ν w ≤ r⁻¹}ᶜ, ‖η w‖ ^ 2 ≤ ∫ w in {w | r⁻¹ ≤ ν w}, ‖η w‖ ^ 2 :=
    setIntegral_mono_set hηi.integrableOn (ae_of_all _ fun _ ↦ sq_nonneg _)
      (ae_of_all _ fun w (hw : ¬ ν w ≤ r⁻¹) ↦ ((not_le.1 hw).le : r⁻¹ ≤ ν w))
  have hfin : ∫ w in {w | ν w ≤ r⁻¹}ᶜ, ‖η w‖ ^ 2 ≤ (1 + NJ) ^ 2 * c * (1 + NJ) ^ 2 * P :=
    calc _ ≤ (1 + NJ) ^ 2 * ∫ ζ in {ζ | ν ζ ≤ r}, ‖η₀ ζ‖ ^ 2 := hout.trans hG1
      _ ≤ (1 + NJ) ^ 2 * (c * ((1 + NJ) ^ 2 * P)) :=
          mul_le_mul_of_nonneg_left (hY.trans (mul_le_mul_of_nonneg_left hG2 hc0)) (sq_nonneg _)
      _ = _ := by ring
  rw [← integral_add_compl hKb hηi]
  linarith

/-- **The cokernel of the linearized operator on the sphere is finite-dimensional.** Let the Floer
data `J`, `K_s`, `K_t` on the plane `ℝ × ℝ ≅ ℂ` be the fixed structure `J₀` and the zero
perturbation on `‖w‖ ≥ T`, a neighbourhood of the point at infinity of the sphere. Let `J` be `C³`
and `K_s`, `K_t` be `C⁴` at the points `(z, u z)` along a `C³` map `u`, with `J(w, u w)`
compatible. Then the orthogonal complement of the range of the realization of `D_u` from
`W^{1,2}` of the sphere to `L²` is finite-dimensional. -/
theorem finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 3 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ := by
  -- The structure at infinity is the compatible structure `J₀`.
  have hT : T ≤ ‖((|T|, 0) : ℝ × ℝ)‖ := by simp [le_abs_self]
  have h₀ : ω.Compatible J₀ := by simpa [hJ₀ _ hT] using hc (|T|, 0)
  -- `J` is bounded along `u`: it is continuous on the compact ball `‖w‖ ≤ T`, and `J₀` outside.
  have hJc : Continuous fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap :=
    continuous_iff_continuousAt.2 fun z ↦
    (hJ z).continuousAt.comp (f := fun z ↦ (z, u z))
      (continuousAt_id.prodMk (hu.continuous.continuousAt))
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall (0 : ℝ × ℝ) T).exists_bound_of_continuousOn
    hJc.continuousOn
  have hB (z : ℝ × ℝ) : ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤
      max B₁ ‖J₀.toLinearMap.toContinuousLinearMap‖ := by
    rcases le_or_gt ‖z‖ T with hz | hz
    · exact (hB₁ z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
    · rw [hJ₀ z hz.le]
      exact le_max_right _ _
  have hρ1 (z : ℝ × ℝ) : sphereWeight z ≤ 1 := by
    rw [sphereWeight_apply]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith [sq_nonneg z.1, sq_nonneg z.2]))
  obtain ⟨A, b, hglob⟩ :=
    exists_integral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero_of_eq_base (u := u) ω h₀ hJ₀
      hKs₀ hKt₀
  exact finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_integral_norm_sq_le ω
    isWeight_sphereWeight hρ1 hJ hKs hKt hu hc hB
    (ω.memLp_floerConformalJetCoeff_of_eq_base isWeight_sphereWeight
      (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (fun z hz y ↦ by rw [hJ₀ z hz y]) hKs₀ hKt₀ (fun z ↦ (hJ z).of_le (by norm_num))
      (fun z ↦ (hKs z).of_le (by norm_num)) (fun z ↦ (hKt z).of_le (by norm_num))
      (hu.of_le (by norm_num)))
    hglob

/-- **The linearized operator on the sphere is Fredholm.** Let the Floer data `J`, `K_s`, `K_t` on
the plane `ℝ × ℝ ≅ ℂ` be the fixed structure `J₀` and the zero perturbation on `‖w‖ ≥ T`, a
neighbourhood of the point at infinity of the sphere. Let `J` be `C³` and `K_s`, `K_t` be `C⁴` at
the points `(z, u z)` along a `C³` map `u`, with `J(w, u w)` compatible. Then the realization of
`D_u` from `W^{1,2}` of the sphere to `L²` is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 3 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  set D := ω.floerConformalSobolevOperator univ sphereWeight
    (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
  have hJ1 (z : ℝ × ℝ) := (hJ z).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hKs2 (z : ℝ × ℝ) := (hKs z).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)
  have hKt2 (z : ℝ × ℝ) := (hKt z).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  rw [TauCeti.isFredholm_iff_finite_ker_coker]
  refine ⟨finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base ω hJ₀ hKs₀
    hKt₀ hJ1 hKs2 hKt2 hu1 hc, ?_⟩
  -- The range is closed, so the cokernel is the orthogonal complement of the range.
  have hcl := isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base ω hJ₀ hKs₀
    hKt₀ hJ1 hKs2 hKt2 hu1 hc
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range] at hcl
  have : CompleteSpace D.range := hcl.completeSpace_coe
  have := finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
    ω hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc
  exact (Submodule.quotientEquivOfIsCompl D.range D.rangeᗮ
    (Submodule.isCompl_orthogonal _)).symm.finiteDimensional

end Cokernel

end SymplecticForm

end TauCeti
