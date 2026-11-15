/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Diagonal
public import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# Coefficient kernels of operators on null sequences

The coefficient kernel of an operator on `C₀(ℕ, R)` is the iterated formal series
`∑ j, (∑ i, aᵢⱼ Xⁱ) Yʲ`, where `aᵢⱼ` is its matrix entry. The inner variable records output
coordinates and the outer variable records input coordinates. This is a coefficient kernel,
not an integral kernel: composition contracts the middle index by a convergent infinite sum,
not by multiplication of formal series.

Over complete ultrametric Tate rings, precisely the series with uniformly bounded coefficients
and null output columns arise in this way. The kernel determines the operator, and its action
and composition are unconditional coefficient sums. Bounded diagonal operators rescale the two
coefficient indices; geometric diagonals correspond to formal rescaling of the variables.

For columns `g hʲ`, the kernel satisfies `K(X,Y) (1 - h(X) Y) = g(X)`. The denominator is a
formal unit regardless of the constant coefficient of `h`; analytic conditions for a bounded
substitution operator are separate from this formal identity.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
-/

public section

open Filter Topology PowerSeries
open scoped ZeroAtInfty BoundedContinuousFunction TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {R : Type*}

section SeminormedRing

variable [SeminormedRing R]

/-- The coefficient kernel `∑ j, (∑ i, aᵢⱼ Xⁱ) Yʲ` of an operator on null sequences.
The inner coefficient index is the output coordinate. -/
noncomputable def coefficientKernel (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) :
    PowerSeries (PowerSeries R) :=
  PowerSeries.mk fun j ↦ PowerSeries.mk fun i ↦ u.matrixCoeff i j

/-- Coefficients of the kernel are the matrix entries, with output index first. -/
@[simp]
theorem coeff_coeff_coefficientKernel (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) (i j : ℕ) :
    coeff i (coeff j u.coefficientKernel) = u.matrixCoeff i j := by
  simp [coefficientKernel]

@[simp]
theorem coefficientKernel_zero :
    (0 : C₀(ℕ, R) →L[R] C₀(ℕ, R)).coefficientKernel = 0 := by
  ext j i
  simp

@[simp]
theorem coefficientKernel_add (u v : C₀(ℕ, R) →L[R] C₀(ℕ, R)) :
    (u + v).coefficientKernel = u.coefficientKernel + v.coefficientKernel := by
  ext j i
  simp

@[simp]
theorem coefficientKernel_neg (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) :
    (-u).coefficientKernel = -u.coefficientKernel := by
  ext j i
  simp

/-- The identity has kernel `∑ j, Xʲ Yʲ`, the formal inverse of `1 - X Y`. -/
@[simp]
theorem coefficientKernel_one :
    (1 : C₀(ℕ, R) →L[R] C₀(ℕ, R)).coefficientKernel =
      PowerSeries.mk (fun j ↦ (PowerSeries.X : PowerSeries R) ^ j) := by
  ext j i
  simp [Matrix.one_apply, PowerSeries.coeff_X_pow, eq_comm]

/-- Each output column of a coefficient kernel tends to zero. -/
theorem tendsto_coeff_coefficientKernel (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) (j : ℕ) :
    Tendsto (fun i ↦ coeff i (coeff j u.coefficientKernel)) cofinite (𝓝 0) := by
  simpa using u.tendsto_matrixCoeff_cofinite j

/-- Over Tate scalars all coefficients of the kernel are bounded by the operator norm. -/
theorem norm_coeff_coeff_coefficientKernel_le [TauCeti.NormedRing.IsTate R]
    (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) (i j : ℕ) :
    ‖coeff i (coeff j u.coefficientKernel)‖ ≤ ‖u‖ := by
  simpa using u.norm_matrixCoeff_le i j

end SeminormedRing

section NormedRing

variable [NormedRing R]

/-- A coefficient kernel determines its operator uniquely. -/
theorem coefficientKernel_injective :
    Function.Injective (coefficientKernel :
      (C₀(ℕ, R) →L[R] C₀(ℕ, R)) → PowerSeries (PowerSeries R)) := by
  intro u v huv
  apply matrixCoeff_injective
  ext i j
  simpa using congrArg (fun F ↦ coeff i (coeff j F)) huv

@[simp]
theorem coefficientKernel_inj {u v : C₀(ℕ, R) →L[R] C₀(ℕ, R)} :
    u.coefficientKernel = v.coefficientKernel ↔ u = v :=
  coefficientKernel_injective.eq_iff

/-- Over complete ultrametric Tate rings, kernels of bounded operators are exactly the
uniformly bounded coefficient arrays whose output columns tend to zero. -/
theorem mem_range_coefficientKernel_iff [IsUltrametricDist R] [CompleteSpace R]
    [TauCeti.NormedRing.IsTate R] {F : PowerSeries (PowerSeries R)} :
    F ∈ Set.range (coefficientKernel :
      (C₀(ℕ, R) →L[R] C₀(ℕ, R)) → PowerSeries (PowerSeries R)) ↔
      (∀ j, Tendsto (fun i ↦ coeff i (coeff j F)) cofinite (𝓝 0)) ∧
        ∃ C, ∀ i j, ‖coeff i (coeff j F)‖ ≤ C := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.tendsto_coeff_coefficientKernel, ‖u‖, u.norm_coeff_coeff_coefficientKernel_le⟩
  · intro hF
    obtain ⟨u, hu⟩ := mem_range_matrixCoeff_iff.mpr hF
    refine ⟨u, ?_⟩
    ext j i
    simpa using congr_fun₂ hu i j

end NormedRing

section CommRing

variable [SeminormedCommRing R]

@[simp]
theorem coefficientKernel_smul (a : R) (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) :
    (a • u).coefficientKernel = a • u.coefficientKernel := by
  ext j i
  simp

/-- The action of an operator is recovered by contracting the input coefficients of its kernel
against a null sequence. The sum converges unconditionally. -/
theorem hasSum_coefficientKernel_apply (u : C₀(ℕ, R) →L[R] C₀(ℕ, R))
    (x : C₀(ℕ, R)) (i : ℕ) :
    HasSum (fun j ↦ coeff i (coeff j u.coefficientKernel) * x j) (u x i) := by
  simpa using u.hasSum_matrixCoeff_mul x i

/-- Composition contracts the middle coefficient index by an unconditional sum. It is not
multiplication of the two bivariate formal series. -/
theorem hasSum_coefficientKernel_comp (u v : C₀(ℕ, R) →L[R] C₀(ℕ, R)) (i k : ℕ) :
    HasSum (fun j ↦ coeff i (coeff j u.coefficientKernel) *
      coeff j (coeff k v.coefficientKernel))
      (coeff i (coeff k (u.comp v).coefficientKernel)) := by
  simpa using u.hasSum_matrixCoeff_comp v i k

/-- Bounded diagonal maps on the output and input multiply the corresponding coefficient
indices of the kernel. No inverse diagonal or change-of-basis hypothesis is required. -/
theorem coeff_coeff_coefficientKernel_diagonalCLM_comp
    (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) (d e : ℕ →ᵇ R) (i j : ℕ) :
    coeff i (coeff j ((ZeroAtInftyContinuousMap.diagonalCLM d).comp
      (u.comp (ZeroAtInftyContinuousMap.diagonalCLM e))).coefficientKernel) =
      d i * coeff i (coeff j u.coefficientKernel) * e j := by
  simp only [coeff_coeff_coefficientKernel, matrixCoeff_apply, comp_apply,
    ZeroAtInftyContinuousMap.diagonalCLM_apply, ZeroAtInftyContinuousMap.diagonalCLM_single]
  rw [← ZeroAtInftyContinuousMap.smul_single_one, map_smul]
  simp [mul_comm, mul_left_comm]

/-- Geometric diagonal rescaling is formal substitution `X ↦ a X`, `Y ↦ b Y` in the kernel.
The given diagonals must be bounded, but they need not be invertible. -/
theorem coefficientKernel_diagonalCLM_comp_of_pow
    (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) (d e : ℕ →ᵇ R) (a b : R)
    (hd : ∀ i, d i = a ^ i) (he : ∀ j, e j = b ^ j) :
    ((ZeroAtInftyContinuousMap.diagonalCLM d).comp
      (u.comp (ZeroAtInftyContinuousMap.diagonalCLM e))).coefficientKernel =
      PowerSeries.map (PowerSeries.rescale a)
        (PowerSeries.rescale (PowerSeries.C b) u.coefficientKernel) := by
  ext j i
  rw [coeff_coeff_coefficientKernel_diagonalCLM_comp, coeff_map, coeff_rescale,
    coeff_rescale, ← map_pow, coeff_C_mul, hd, he]
  ring

/-- The kernel is `g(X)/(1 - h(X)Y)` exactly when the image of the `j`-th coordinate vector
has coefficient series `g hʲ`. The rational expression is stated as a denominator identity;
no analytic substitution or convergence of the bivariate series is assumed. -/
theorem coefficientKernel_mul_one_sub_eq_C_iff
    (u : C₀(ℕ, R) →L[R] C₀(ℕ, R)) (g h : PowerSeries R) :
    u.coefficientKernel * (1 - PowerSeries.C h * PowerSeries.X) = PowerSeries.C g ↔
      ∀ i j, u.matrixCoeff i j = coeff i (g * h ^ j) := by
  have hgeom := TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one h
  have hunit : IsUnit (1 - PowerSeries.C h * PowerSeries.X) :=
    ⟨⟨_, PowerSeries.mk (fun j ↦ h ^ j), (mul_comm _ _).trans hgeom, hgeom⟩, rfl⟩
  have hprod : (PowerSeries.C g * PowerSeries.mk (fun j ↦ h ^ j)) *
      (1 - PowerSeries.C h * PowerSeries.X) = PowerSeries.C g := by
    rw [mul_assoc, hgeom, mul_one]
  rw [← hprod, hunit.mul_left_inj]
  constructor
  · intro hkernel i j
    simpa using congrArg (fun F ↦ coeff i (coeff j F)) hkernel
  · intro hu
    ext j i
    simp [hu]

end CommRing

end ContinuousLinearMap
