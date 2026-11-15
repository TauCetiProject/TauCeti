/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EquationMap
public import TauCeti.Analysis.PDE.Vortex.Gauge.Laplacian
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Coulomb decomposition and the first cohomology of the vortex deformation complex

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

**The Coulomb decomposition.** Let `k ≥ 2` and let `x ∈ A_m^(k+1)` be a continuous field, hence a
`C¹` one by the Sobolev embedding (`TauCeti.Vortex.contDiff_of_mem_framedFieldSpace`). Every `C¹`
variation `y ∈ H^(k+1)` decomposes as

`y = d₀ u + h`,   `u ∈ H^(k+2)` of class `C^k`,   `d₀* h = 0`

(`TauCeti.Vortex.exists_gaugeAdjoint_sub_gaugeDirection_eq_zero`). The phase `u` solves the gauge
Laplacian equation `d₀* d₀ u = d₀* y`: the gauge Laplacian `-Δ + (p² + q²)` has a weak solution in
`H^(k+2)`
(`TauCeti.Vortex.exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq`),
which has a `C^k` representative in `H^(k+2)`
(`TemperedDistribution.exists_contDiff_ae_eq_of_mem_realSobolevFunctions`). Integrating by parts
against test phases (`TauCeti.Vortex.integral_mul_gaugeAdjoint`) and Green's identity for the
gauge Laplacian (`TauCeti.Vortex.integral_mul_gaugeAdjoint_gaugeDirection_comm`) turn the weak
equation into
the vanishing of `∫ φ d₀* (y - d₀ u)` for all test phases `φ`, so the continuous function
`d₀* (y - d₀ u)` vanishes. The phase is unique: a square-integrable `C²` phase with
`d₀* d₀ u = 0` vanishes (`TauCeti.Vortex.eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero`), by the
uniqueness of weak solutions of the gauge Laplacian
(`TauCeti.Vortex.ae_eq_of_integral_mul_gaugeAdjoint_gaugeDirection_eq`).

**The first cohomology.** Let `k ≥ 3` and let `x ∈ A_m^(k+1)` be a continuous, hence `C²`,
solution of the vortex equation. Take as cocycles the `C²` variations `y ∈ H^(k+1)` with `d₁ y = 0`
(`TauCeti.Vortex.deformationCocycles x k`), and as coboundaries the variations `d₀ u` with
`u ∈ H^(k+2)` of class `C³` (`TauCeti.Vortex.deformationCoboundaries x k`). The coboundaries are
cocycles (`TauCeti.Vortex.deformationCoboundaries_le_deformationCocycles`). The `C²` kernel of
`L_x` in `H^(k+1)` consists of cocycles, and the quotient map restricted to it is a linear
equivalence

`ker L_x ∩ H^(k+1) ≃ ker d₁ / im d₀`

(`TauCeti.Vortex.gaugeFixedKernelEquivDeformationCohomology`). It is onto by the Coulomb
decomposition: the Coulomb part `h = y - d₀ u` of a cocycle `y` satisfies
`d₁ h = d₁ y - d₁ d₀ u = 0` and `d₀* h = 0`, so `h ∈ ker L_x`. It is injective by uniqueness: an
element `d₀ u` of `ker L_x` has `d₀* d₀ u = 0`, so `u = 0`.

Thus the kernel of the gauge-fixed operator is the tangent space of the vortex moduli space
computed by the deformation complex, which is the infinitesimal form of the Coulomb slice theorem.
These are statements about classical representatives on the Sobolev scale; the nonlinear slice,
by an implicit function theorem for the action of the Sobolev gauge group, is not treated here.

## Main results

All in the namespace `TauCeti.Vortex`:

* `exists_gaugeAdjoint_sub_gaugeDirection_eq_zero`: the Coulomb decomposition `y = d₀ u + h`,
  `d₀* h = 0`, of a `C¹` variation `y ∈ H^(k+1)`.
* `eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero`: uniqueness of the phase.
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
open scoped ContDiff RealInnerProductSpace

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Uniqueness of the Coulomb phase.** At a continuous field `x` of `A_m^s`, `s > 2`, a
square-integrable `C²` phase `u` with `d₀* d₀ u = 0` vanishes. -/
theorem eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero {s : ℝ} (hs : 2 < s)
    (hx : x ∈ framedFieldSpace f m s) (hcont : Continuous x) {u : ℂ → ℝ}
    (hu : MemLp u 2 (volume : Measure ℂ)) (huc : ContDiff ℝ 2 u)
    (h : ∀ z, gaugeAdjoint x (gaugeDirection x u) z = 0) : u = 0 := by
  have hxc : ContDiff ℝ 1 x := contDiff_of_mem_framedFieldSpace (by push_cast; linarith) hx hcont
  have hae : u =ᵐ[volume] 0 :=
    ae_eq_of_integral_mul_gaugeAdjoint_gaugeDirection_eq (by linarith) hx hcont hu
      (MemLp.zero (ε := ℝ)) (g := 0)
      (fun φ hφ hφc ↦ by
        rw [integral_mul_gaugeAdjoint_gaugeDirection_comm hxc huc (hφ.of_le (by simp)) hφc]
        simp only [h, mul_zero, integral_zero, Pi.zero_apply, zero_mul])
      (fun φ _ _ ↦ by simp)
  exact (huc.continuous.ae_eq_iff_eq volume continuous_const).1 hae

/-- **The Coulomb decomposition.** Let `k ≥ 2` and let `x ∈ A_m^(k+1)` be a continuous field.
Every `C¹` variation `y ∈ H^(k+1)` is `d₀ u + h` with `u ∈ H^(k+2)` of class `C^k` and
`d₀* h = 0`. -/
theorem exists_gaugeAdjoint_sub_gaugeDirection_eq_zero {k : ℕ} (hk : 2 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hcont : Continuous x)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y) :
    ∃ u ∈ realSobolevFunctions ℂ (k + 2) 2, ContDiff ℝ k u ∧
      ∀ z, gaugeAdjoint x (y - gaugeDirection x u) z = 0 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hxc : ContDiff ℝ 1 x := contDiff_of_mem_framedFieldSpace (by push_cast; linarith) hx hcont
  have hg := gaugeAdjoint_mem_realSobolevFunctions (by omega) hx hy hyc
  have hx' : x ∈ framedFieldSpace f m ((k + 1 : ℕ) : ℝ) := by rwa [Nat.cast_succ]
  obtain ⟨u₀, hu₀, hw₀⟩ :=
    exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq (k := k + 1)
      (j := k) (by omega) (by omega) hx' hxc.continuous hg
  obtain ⟨u, hu, huS, hae⟩ := exists_contDiff_ae_eq_of_mem_realSobolevFunctions (k := k)
    (by rw [Complex.finrank_real_complex]; push_cast; linarith) hu₀
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by exact_mod_cast hk)
  -- The weak equation `d₀* d₀ u = d₀* y` for the `C^k` representative.
  have hw (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
      ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, gaugeAdjoint x y z * φ z := by
    rw [← hw₀ φ hφ hφc]
    exact integral_congr_ae (hae.mono fun z hz ↦ by simp only [hz])
  have hdu : ContDiff ℝ 1 (gaugeDirection x u) := contDiff_gaugeDirection (n := 1) hxc hu2
  have hh : ContDiff ℝ 1 (y - gaugeDirection x u) := hyc.sub hdu
  have hdc : Continuous (gaugeAdjoint x (y - gaugeDirection x u)) :=
    continuous_gaugeAdjoint hxc.continuous hh
  refine ⟨u, huS, hu, fun z ↦ congrFun ((hdc.ae_eq_iff_eq volume continuous_const).1 ?_) z⟩
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hdc.locallyIntegrable
    fun φ hφ hφc ↦ ?_
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hdφ : Continuous (gaugeDirection x φ) :=
    (contDiff_gaugeDirection (n := 1) hxc hφ2).continuous
  have hdφc := hasCompactSupport_gaugeDirection x hφc
  have hi (v : ℂ → EuclideanSpace ℝ (Fin 4)) (hv : Continuous v) :
      Integrable (fun z ↦ ⟪gaugeDirection x φ z, v z⟫) volume :=
    (hdφ.inner hv).integrable_of_hasCompactSupport
      (hdφc.mono fun z hz ↦ fun hvz ↦ hz (by simp [hvz]))
  simp only [smul_eq_mul]
  rw [integral_mul_gaugeAdjoint hxc.continuous hh (hφ.of_le (by simp)) hφc]
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub (hi y hyc.continuous) (hi _ hdu.continuous),
    ← integral_mul_gaugeAdjoint hxc.continuous hyc (hφ.of_le (by simp)) hφc,
    ← integral_mul_gaugeAdjoint hxc.continuous hdu (hφ.of_le (by simp)) hφc,
    ← integral_mul_gaugeAdjoint_gaugeDirection_comm hxc hu2 hφ2 hφc, hw φ hφ2 hφc]
  simp_rw [mul_comm (φ _)]
  exact sub_self _

/-! ### The first cohomology of the deformation complex -/

variable (x) in
/-- The cocycles of the vortex deformation complex at `x` on the Sobolev scale: the `C²`
variations `y ∈ H^(k+1)` with `d₁ y = 0`, the infinitesimal solutions of the vortex equation. -/
def deformationCocycles (k : ℕ) : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | y ∈ sobolevFields (k + 1) ∧ ContDiff ℝ 2 y ∧ ∀ z, linearizedEquation x y z = 0}
  add_mem' := by
    rintro y v ⟨hy, hyc, hyl⟩ ⟨hv, hvc, hvl⟩
    refine ⟨add_mem hy hv, hyc.add hvc, fun z ↦ ?_⟩
    have hd {w : ℂ → EuclideanSpace ℝ (Fin 4)} (hw : ContDiff ℝ 2 w) (i : Fin 4) :
        DifferentiableAt ℝ (fun w' ↦ w w' i) z :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z
        (hw.differentiable (by norm_num) z) :)
    rw [linearizedEquation_add x (hd hyc) (hd hvc), hyl, hvl, add_zero]
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
  have hxi (i : Fin 4) (z : ℂ) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z
      (hxc.differentiable (by norm_num) z) :)
  exact ⟨gaugeDirection_mem_sobolevFields hk hx hu (huc.of_le (by norm_num)),
    contDiff_gaugeDirection (n := 2) hxc huc, fun z ↦
      linearizedEquation_gaugeDirection_eq_zero (hxi 2 z) (hxi 3 z)
        (huc.contDiffAt.of_le (by norm_num)) (hsol z)⟩

/-- The `C²` kernel of `L_x` in `H^(k+1)` consists of cocycles of the deformation complex. -/
theorem gaugeFixedKernel_inf_sobolevFields_le_deformationCocycles (k : ℕ) :
    gaugeFixedKernel x ⊓ sobolevFields (k + 1) ≤ deformationCocycles x k := by
  intro y hy
  obtain ⟨hyK, hy⟩ := Submodule.mem_inf.1 hy
  obtain ⟨hyc, -, hyk⟩ := mem_gaugeFixedKernel.1 hyK
  refine ⟨hy, hyc, fun z ↦ ?_⟩
  ext i
  fin_cases i
  · simpa using congrArg (· 1) (hyk z)
  · simpa using congrArg (· 2) (hyk z)
  · simpa using congrArg (· 3) (hyk z)

/-- **Harmonic coboundaries vanish.** At a continuous field `x ∈ A_m^(k+1)`, `k ≥ 2`, a
coboundary `d₀ u` in the kernel of `L_x` is zero. -/
theorem eq_zero_of_mem_gaugeFixedKernel_of_mem_deformationCoboundaries {k : ℕ} (hk : 2 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hcont : Continuous x)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hyK : y ∈ gaugeFixedKernel x)
    (hyB : y ∈ deformationCoboundaries x k) : y = 0 := by
  obtain ⟨u, hu, huc, rfl⟩ := hyB
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hu0 : u = 0 := eq_zero_of_gaugeAdjoint_gaugeDirection_eq_zero (by linarith) hx hcont
    (memLp_of_mem_realSobolevFunctions hu) (huc.of_le (by norm_num)) fun z ↦ by
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
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hxc : ContDiff ℝ 2 x := contDiff_of_mem_framedFieldSpace (by push_cast; linarith) hx hcont
  obtain ⟨u, hu, huc, hcoul⟩ := exists_gaugeAdjoint_sub_gaugeDirection_eq_zero
    (by omega) hx hcont hy (hyc.of_le (by norm_num))
  have hu3 : ContDiff ℝ 3 u := huc.of_le (by exact_mod_cast hk)
  obtain ⟨hdu, hduc, hdul⟩ :=
    deformationCoboundaries_le_deformationCocycles (by omega) hx hxc hsol ⟨u, hu, hu3, rfl⟩
  have hd {w : ℂ → EuclideanSpace ℝ (Fin 4)} (hw : ContDiff ℝ 2 w) (z : ℂ) (i : Fin 4) :
      DifferentiableAt ℝ (fun w' ↦ w w' i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z
      (hw.differentiable (by norm_num) z) :)
  refine ⟨u, hu, hu3, Submodule.mem_inf.2 ⟨mem_gaugeFixedKernel.2
    ⟨hyc.sub hduc, memLp_of_mem_sobolevFields (sub_mem hy hdu), fun z ↦ ?_⟩, sub_mem hy hdu⟩⟩
  have hl : linearizedEquation x (y - gaugeDirection x u) z = 0 := by
    rw [linearizedEquation_sub x (hd hyc z) (hd hduc z), hyl z, hdul z, sub_zero]
  ext i
  fin_cases i
  · simpa using hcoul z
  · simpa using congrArg (· 0) hl
  · simpa using congrArg (· 1) hl
  · simpa using congrArg (· 2) hl

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
        eq_zero_of_mem_gaugeFixedKernel_of_mem_deformationCoboundaries (by omega) hx hcont hyK hy
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
        ⟨y, gaugeFixedKernel_inf_sobolevFields_le_deformationCocycles k y.2⟩ := by
  unfold gaugeFixedKernelEquivDeformationCohomology
  rfl

end TauCeti.Vortex
