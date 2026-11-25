/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EquationMap
public import TauCeti.Analysis.PDE.Vortex.Gauge.Slice
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The first cohomology of the vortex deformation complex

At a plane vortex field `x = (b₁, b₂, p, q)` the deformation complex is

`H^(k+2)(ℂ; ℝ) --d₀--> H^(k+1)(ℂ; ℝ⁴) --d₁--> H^k(ℂ; ℝ³)`,

where `d₀ = TauCeti.Vortex.gaugeDirection x` is the infinitesimal gauge action
`u ↦ (-∂₁ u, -∂₂ u, -q u, p u)` and `d₁ = TauCeti.Vortex.linearizedEquation x` is the linearized
vortex equation (`TauCeti.Vortex.gaugeDirection_mem_sobolevFields`,
`TauCeti.Vortex.linearizedEquation_apply_mem_realSobolevFunctions`). At a solution `d₁ d₀ = 0`
(`TauCeti.Vortex.linearizedEquation_gaugeDirection_eq_zero`), and its first cohomology
`ker d₁ / im d₀` is the formal tangent space of the moduli space of vortices: infinitesimal
solutions of the equation modulo infinitesimal gauge transformations. The gauge-fixed operator
`L_x = d₀* ⊕ d₁` (`TauCeti.Vortex.gaugeFixedOperator`) instead selects, in each class, the
representative in the Coulomb slice `d₀* y = 0`. This file proves that the two descriptions agree.

Let `k ≥ 3` and let `x ∈ A_m^(k+1)` be a continuous, hence `C²`, solution of the vortex equation.
Take as cocycles the `C²` variations `y ∈ H^(k+1)` with `d₁ y = 0`
(`TauCeti.Vortex.deformationCocycles x k`), and as coboundaries the variations `d₀ u` with
`u ∈ H^(k+2)` of class `C³` (`TauCeti.Vortex.deformationCoboundaries x k`). The coboundaries are
cocycles (`TauCeti.Vortex.deformationCoboundaries_le_deformationCocycles`). The `C²` kernel of
`L_x` in `H^(k+1)` consists of cocycles, and the quotient map restricted to it is a linear
equivalence

`ker L_x ∩ H^(k+1) ≃ ker d₁ / im d₀`

(`TauCeti.Vortex.gaugeFixedKernelEquivDeformationCohomology`). It is onto by the infinitesimal
Coulomb slice (`TauCeti.Vortex.exists_gaugeFixedOperator_sub_gaugeDirection_eq_zero`): every
cocycle `y` has a phase `u ∈ H^(k+2)` with `y - d₀ u ∈ ker L_x`, and `u` is `C³` by the Sobolev
embedding. It is injective since no nonzero decaying infinitesimal gauge transformation is
Coulomb (`TauCeti.Vortex.eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero`): an element `d₀ u` of
`ker L_x` has `d₀* d₀ u = 0`, and `u ∈ H^(k+2)` tends to zero at infinity, so `u = 0`.

Thus the kernel of the gauge-fixed operator is the tangent space of the vortex moduli space
computed by the deformation complex, which is the infinitesimal form of the Coulomb slice theorem.
These are statements about classical representatives on the Sobolev scale.

## Main results

All in the namespace `TauCeti.Vortex`:

* `deformationCocycles`, `deformationCoboundaries`: the cocycles `ker d₁` and coboundaries
  `im d₀` of the deformation complex on the Sobolev scale.
* `deformationCoboundaries_le_deformationCocycles`: `d₁ d₀ = 0` at a vortex, on these spaces.
* `eq_zero_of_mem_gaugeFixedKernel_of_mem_deformationCoboundaries`,
  `exists_sub_gaugeDirection_mem_gaugeFixedKernel`: a coboundary in the kernel of `L_x` vanishes,
  and every cocycle differs from an element of the kernel of `L_x` by a coboundary.
* `gaugeFixedKernelEquivDeformationCohomology`: the kernel of `L_x` in `H^(k+1)` is linearly
  equivalent to the first cohomology `ker d₁ / im d₀`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277--292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory TemperedDistribution

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

variable (x) in
/-- The cocycles of the vortex deformation complex at `x` on the Sobolev scale: the `C²`
variations `y ∈ H^(k+1)` with `d₁ y = 0`, the infinitesimal solutions of the vortex equation. -/
def deformationCocycles (k : ℕ) : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | y ∈ sobolevFields (k + 1) ∧ ContDiff ℝ 2 y ∧ ∀ z, linearizedEquation x y z = 0}
  add_mem' := by
    rintro y v ⟨hy, hyc, hyl⟩ ⟨hv, hvc, hvl⟩
    refine ⟨add_mem hy hv, hyc.add hvc, fun z ↦ ?_⟩
    rw [linearizedEquation_add x (differentiableAt_euclidean.1 (hyc.differentiable two_ne_zero z))
      (differentiableAt_euclidean.1 (hvc.differentiable two_ne_zero z)), hyl, hvl, add_zero]
  zero_mem' := ⟨zero_mem _, contDiff_zero_fun, fun z ↦ by simp⟩
  smul_mem' := by
    rintro t y ⟨hy, hyc, hyl⟩
    exact ⟨Submodule.smul_mem _ t hy, hyc.const_smul t, fun z ↦ by
      rw [linearizedEquation_smul, hyl, smul_zero]⟩

@[simp]
theorem mem_deformationCocycles {k : ℕ} {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ deformationCocycles x k ↔
      y ∈ sobolevFields (k + 1) ∧ ContDiff ℝ 2 y ∧ ∀ z, linearizedEquation x y z = 0 :=
  Iff.rfl

variable (x) in
/-- The coboundaries of the vortex deformation complex at `x` on the Sobolev scale: the
infinitesimal gauge transformations `d₀ u` with `u ∈ H^(k+2)` of class `C³`. -/
def deformationCoboundaries (k : ℕ) : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | ∃ u ∈ realSobolevFunctions ℂ (k + 2) 2, ContDiff ℝ 3 u ∧ gaugeDirection x u = y}
  add_mem' := by
    rintro _ _ ⟨u, hu, huc, rfl⟩ ⟨v, hv, hvc, rfl⟩
    refine ⟨u + v, add_mem hu hv, huc.add hvc, funext fun z ↦ ?_⟩
    exact gaugeDirection_add x (huc.differentiable (by norm_num) z)
      (hvc.differentiable (by norm_num) z)
  zero_mem' := ⟨0, zero_mem _, contDiff_zero_fun, gaugeDirection_zero x⟩
  smul_mem' := by
    rintro t _ ⟨u, hu, huc, rfl⟩
    exact ⟨t • u, Submodule.smul_mem _ t hu, huc.const_smul t,
      funext fun z ↦ gaugeDirection_smul x u t z⟩

@[simp]
theorem mem_deformationCoboundaries {k : ℕ} {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ deformationCoboundaries x k ↔
      ∃ u ∈ realSobolevFunctions ℂ (k + 2) 2, ContDiff ℝ 3 u ∧ gaugeDirection x u = y :=
  Iff.rfl

/-- **`d₁ d₀ = 0` on the Sobolev scale.** At a `C²` solution `x ∈ A_m^(k+1)`, `k ≥ 1`, of the
vortex equation, every coboundary is a cocycle. -/
theorem deformationCoboundaries_le_deformationCocycles {k : ℕ} (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hxc : ContDiff ℝ 2 x)
    (hsol : ∀ z, equation x z = 0) :
    deformationCoboundaries x k ≤ deformationCocycles x k := by
  rintro _ ⟨u, hu, huc, rfl⟩
  have hxi (z : ℂ) := differentiableAt_euclidean.1 (hxc.differentiable two_ne_zero z)
  exact ⟨gaugeDirection_mem_sobolevFields hk hx hu (huc.of_le (by norm_num)),
    contDiff_gaugeDirection (n := 2) hxc huc, fun z ↦
      linearizedEquation_gaugeDirection_eq_zero (hxi z 2) (hxi z 3)
        (huc.contDiffAt.of_le (by norm_num)) (hsol z)⟩

/-- The `C²` kernel of `L_x` in `H^(k+1)` consists of cocycles of the deformation complex. -/
theorem gaugeFixedKernel_inf_sobolevFields_le_deformationCocycles (k : ℕ) :
    gaugeFixedKernel x ⊓ sobolevFields (k + 1) ≤ deformationCocycles x k := by
  intro y hy
  obtain ⟨hyK, hy⟩ := Submodule.mem_inf.1 hy
  obtain ⟨hyc, -, hyk⟩ := mem_gaugeFixedKernel.1 hyK
  refine ⟨hy, hyc, fun z ↦ ?_⟩
  ext i
  simpa [gaugeFixedOperator_apply_succ] using congrArg (· i.succ) (hyk z)

/-- **Harmonic coboundaries vanish.** At any field `x`, a coboundary `d₀ u` in the kernel of
`L_x` is zero: `d₀* d₀ u = 0`, and `u ∈ H^(k+2)` tends to zero at infinity. -/
theorem eq_zero_of_mem_gaugeFixedKernel_of_mem_deformationCoboundaries {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hyK : y ∈ gaugeFixedKernel x)
    (hyB : y ∈ deformationCoboundaries x k) : y = 0 := by
  obtain ⟨u, hu, huc, rfl⟩ := hyB
  have hs : (Module.finrank ℝ ℂ : ℝ) < 2 * (k + 2) := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith [k.cast_nonneg (α := ℝ)]
  have hu0 : u = 0 := eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero x (huc.of_le (by norm_num))
    (tendsto_cocompact_of_mem_realSobolevFunctions hs hu huc.continuous) fun z ↦ by
      simpa using congrArg (· 0) ((mem_gaugeFixedKernel.1 hyK).2.2 z)
  rw [hu0, gaugeDirection_zero]

/-- **Every cocycle has a harmonic representative.** Let `k ≥ 3` and let `x ∈ A_m^(k+1)` be a
continuous solution of the vortex equation. For every cocycle `y` there is a phase `u ∈ H^(k+2)`
of class `C³` such that `y - d₀ u` lies in the kernel of `L_x` in `H^(k+1)`. -/
theorem exists_sub_gaugeDirection_mem_gaugeFixedKernel {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hcont : Continuous x)
    (hsol : ∀ z, equation x z = 0) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ deformationCocycles x k) :
    ∃ u ∈ realSobolevFunctions ℂ (k + 2) 2, ContDiff ℝ 3 u ∧
      y - gaugeDirection x u ∈ gaugeFixedKernel x ⊓ sobolevFields (k + 1) := by
  obtain ⟨hy, hyc, hyl⟩ := hy
  have hcast : ((k + 1 : ℕ) : ℝ) = k + 1 := Nat.cast_succ k
  obtain ⟨u, hu, hu2, hdu, hL⟩ := exists_gaugeFixedOperator_sub_gaugeDirection_eq_zero
    (k := k + 1) (by omega) (by rwa [hcast]) hcont hsol (by rwa [hcast]) hyc.continuous hyl
  rw [hcast] at hdu
  have hu' : u ∈ realSobolevFunctions ℂ (k + 2) 2 := by convert hu using 2; push_cast; ring
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hu3 : ContDiff ℝ 3 u := contDiff_of_mem_realSobolevFunctions
    (by rw [Complex.finrank_real_complex]; push_cast; linarith) hu' hu2.continuous
  have hxc : ContDiff ℝ 2 x := contDiff_of_mem_framedFieldSpace (by push_cast; linarith) hcont hx
  exact ⟨u, hu', hu3, Submodule.mem_inf.2 ⟨mem_gaugeFixedKernel.2
    ⟨hyc.sub (contDiff_gaugeDirection (n := 2) hxc hu3),
      memLp_of_mem_sobolevFields (sub_mem hy hdu), hL⟩, sub_mem hy hdu⟩⟩

/-- **The kernel of the gauge-fixed operator is the first cohomology of the deformation
complex.** Let `k ≥ 3` and let `x ∈ A_m^(k+1)` be a continuous solution of the vortex equation.
The quotient map from the cocycles `ker d₁` to `ker d₁ / im d₀`, restricted to the `C²` kernel of
`L_x = d₀* ⊕ d₁` in `H^(k+1)`, is a linear equivalence. -/
def gaugeFixedKernelEquivDeformationCohomology {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hcont : Continuous x)
    (hsol : ∀ z, equation x z = 0) :
    ↥(gaugeFixedKernel x ⊓ sobolevFields (k + 1)) ≃ₗ[ℝ]
      deformationCocycles x k ⧸
        (deformationCoboundaries x k).comap (deformationCocycles x k).subtype :=
  LinearEquiv.ofBijective
    (((deformationCoboundaries x k).comap (deformationCocycles x k).subtype).mkQ ∘ₗ
      Submodule.inclusion (gaugeFixedKernel_inf_sobolevFields_le_deformationCocycles k)) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      rintro ⟨y, hyK, _⟩ hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hy
      exact (Submodule.mem_bot ℝ).2 <| Subtype.ext <|
        eq_zero_of_mem_gaugeFixedKernel_of_mem_deformationCoboundaries hyK hy
    · intro b
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      obtain ⟨u, hu, hu3, hK⟩ := exists_sub_gaugeDirection_mem_gaugeFixedKernel hk hx hcont hsol hy
      refine ⟨⟨_, hK⟩, ?_⟩
      rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq']
      exact ⟨u, hu, hu3, funext fun z ↦ by simp⟩

@[simp]
theorem gaugeFixedKernelEquivDeformationCohomology_apply {k : ℕ} (hk : 3 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hcont : Continuous x)
    (hsol : ∀ z, equation x z = 0) (y : ↥(gaugeFixedKernel x ⊓ sobolevFields (k + 1))) :
    gaugeFixedKernelEquivDeformationCohomology hk hx hcont hsol y =
      Submodule.Quotient.mk
        ⟨y, gaugeFixedKernel_inf_sobolevFields_le_deformationCocycles k y.property⟩ := by
  unfold gaugeFixedKernelEquivDeformationCohomology
  rfl

end TauCeti.Vortex
