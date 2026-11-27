/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Sphere
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal

/-!
# The linearized Floer operator on `W^{1,2}` of the Riemann sphere

Some Floer problems live on a closed domain: the comparison between the pair-of-pants product and
the quantum product deforms Floer data on the sphere with three poles, read in the coordinate
`w ∈ ℂ ≅ ℝ × ℝ` in which the poles are `0`, `1` and `∞`, and the data are unperturbed near `∞`.
This file realizes the linearized Floer operator `D_u` of such data on the Sobolev space of the
round metric of the sphere and proves that the realization has finite-dimensional kernel and
closed range.

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

The target is a symplectic vector space. The finiteness of the cokernel and the index are not
treated here.

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

end TauCeti
