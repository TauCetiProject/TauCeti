/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Complex
public import TauCeti.Analysis.PDE.Vortex.Gauge.ComplexStructure
public import TauCeti.Analysis.PDE.Vortex.Index
public import TauCeti.Geometry.Symplectic.Complex.Module.Hom

/-!
# The linearized vortex operator as a complex-linear family, and its kernel charts

The gauge-fixed linearization `L_a = d₀* ⊕ d₁` of the plane vortex equations, realized as the
operator `H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` with `L∞` coefficient class `a`
(`TauCeti.Vortex.sobolevGaugeFixedOperator`), intertwines the signed coordinate permutation `J` on
`H¹(ℂ)⁴` (`TauCeti.Vortex.sobolevVariationAlmostComplexStructure`) with the pointwise action `J'` of
`TauCeti.Vortex.targetComplexStructure` on `L²(ℂ; ℝ⁴)`, the almost complex structure
`TauCeti.Vortex.sobolevTargetAlmostComplexStructure`
(`TauCeti.Vortex.isComplexLinearMap_sobolevGaugeFixedOperator`). This file packages `L_a`
as a complex-linear operator for the complex vector space structures in which `i` acts by `J` and
by `J'` (`TauCeti.Vortex.sobolevGaugeFixedComplexOperator`), depending continuously on `a`. The two
complex structures are `TauCeti.Vortex.sobolevVariationComplexModule` and
`TauCeti.Vortex.sobolevTargetComplexModule`. They are not global instances, because neither space
has a canonical complex structure; a user activates them, together with the scalar tower and
continuity facts `TauCeti.Vortex.sobolevVariationComplexModule_isScalarTower`,
`TauCeti.Vortex.sobolevTargetComplexModule_isScalarTower` and
`TauCeti.Vortex.sobolevVariationComplexModule_continuousConstSMul` needed to state the results
below, with `attribute [local instance high]`, as this file does.

The determinant line `det (ker L_a) ⊗ (det (coker L_a))^*` of a vortex deformation operator is
therefore oriented by its complex orientation (`LinearMap.IsComplexPositiveDetLine`). At a plane
vortex `x` lying in the affine field space `A_m^k` for every `k`, with `L∞` class `a₀`, the operator
`L_{a₀}` is onto, with kernel of real dimension `2m`, the dimension of the divisor space
`Sym^m ℂ`. One complex-linear kernel coordinate `q : H¹(ℂ)⁴ × ℂ⁰ →L[ℂ] ℂᵐ` then trivializes the
determinant lines of all `L_a` with `a` near `a₀`
(`TauCeti.Vortex.exists_isOpen_isInvertible_prod_coprod_sobolevGaugeFixedComplexOperator`, from
`ContinuousLinearMap.exists_isOpen_isInvertible_prod_coprod_of_surjective`). Since the chart is
complex, it reads the complex orientations of all these determinant lines as the complex
orientation of the fixed line `det ℂᵐ ⊗ (det ℂ⁰)^*`
(`ContinuousLinearMap.isComplexPositiveTMulDual_detLineChartEquiv_iff`): near every vortex, the
complex orientations of the vortex deformation determinants are continuous in the `L∞`
coefficient.

## Main declarations

All in the namespace `TauCeti.Vortex`:

* `sobolevVariationComplexModule`, `sobolevTargetComplexModule`: the complex structures of
  `H¹(ℂ)⁴` and `L²(ℂ; ℝ⁴)` in which `i` acts by `J` and by `J'`, with
  `sobolevVariationComplexModule_isScalarTower`, `sobolevTargetComplexModule_isScalarTower` and
  `sobolevVariationComplexModule_continuousConstSMul`.
* `sobolevGaugeFixedComplexOperator`: `L_a` as a complex-linear operator, with
  `restrictScalars_sobolevGaugeFixedComplexOperator` and
  `continuous_restrictScalars_sobolevGaugeFixedComplexOperator`.
* `exists_isOpen_isInvertible_prod_coprod_sobolevGaugeFixedComplexOperator`: near the coefficient
  class of a plane vortex of degree `m`, one complex kernel chart with model `ℂᵐ` serves every
  `L_a`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (the canonical orientation of the
  determinant line bundle of a family of complex-linear Fredholm operators).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Topology Module
open scoped ENNReal

namespace TauCeti.Vortex

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### The complex-linear family -/

/-- The complex vector space structure of `H¹(ℂ)⁴` in which `i` acts by `J`. -/
@[instance_reducible]
def sobolevVariationComplexModule : Module ℂ (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  sobolevVariationAlmostComplexStructure.complexModule

/-- The complex vector space structure of `L²(ℂ; ℝ⁴)` in which `i` acts by `J'`. -/
@[instance_reducible]
def sobolevTargetComplexModule : Module ℂ (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :=
  sobolevTargetAlmostComplexStructure.complexModule

attribute [local instance high] sobolevVariationComplexModule sobolevTargetComplexModule

/-- `ℝ`, `ℂ` and `H¹(ℂ)⁴` form a scalar tower for `TauCeti.Vortex.sobolevVariationComplexModule`. -/
theorem sobolevVariationComplexModule_isScalarTower :
    IsScalarTower ℝ ℂ (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  sobolevVariationAlmostComplexStructure.complexModule_isScalarTower

/-- `ℝ`, `ℂ` and `L²(ℂ; ℝ⁴)` form a scalar tower for `TauCeti.Vortex.sobolevTargetComplexModule`. -/
theorem sobolevTargetComplexModule_isScalarTower :
    IsScalarTower ℝ ℂ (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :=
  sobolevTargetAlmostComplexStructure.complexModule_isScalarTower

/-- Multiplication by each complex scalar is continuous on `H¹(ℂ)⁴` for
`TauCeti.Vortex.sobolevVariationComplexModule`. -/
theorem sobolevVariationComplexModule_continuousConstSMul :
    ContinuousConstSMul ℂ (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
  sobolevVariationAlmostComplexStructure.complexModule_continuousConstSMul
    continuous_sobolevVariationAlmostComplexStructure

attribute [local instance high] sobolevVariationComplexModule_isScalarTower
  sobolevTargetComplexModule_isScalarTower sobolevVariationComplexModule_continuousConstSMul

/-- The Sobolev realization of `L_a`, as a complex-linear operator for the complex structures in
which `i` acts by `J` on `H¹(ℂ)⁴` and by `J'` on `L²(ℂ; ℝ⁴)`. Its underlying real operator is
`TauCeti.Vortex.sobolevGaugeFixedOperator a`
(`TauCeti.Vortex.restrictScalars_sobolevGaugeFixedComplexOperator`), through which it is used; it
is irreducible so that its large body is never unfolded when instances of its domain and target
are compared. -/
@[irreducible]
def sobolevGaugeFixedComplexOperator (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℂ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  { (isComplexLinearMap_sobolevGaugeFixedOperator a).toComplexLinearMap with
    cont := (sobolevGaugeFixedOperator a).continuous }

/-- The complex-linear operator `TauCeti.Vortex.sobolevGaugeFixedComplexOperator a` is the Sobolev
realization of `L_a` with its real scalars. -/
@[simp]
theorem restrictScalars_sobolevGaugeFixedComplexOperator
    (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (sobolevGaugeFixedComplexOperator a).restrictScalars ℝ = sobolevGaugeFixedOperator a := by
  unfold sobolevGaugeFixedComplexOperator
  exact ContinuousLinearMap.ext fun _ ↦ rfl

/-- The complex-linear operator `TauCeti.Vortex.sobolevGaugeFixedComplexOperator a` acts as the
Sobolev realization of `L_a`. This is not a `simp` lemma: the carrier types mention
`((⊤ : Opens ℂ) : Set ℂ)`, which `simp` rewrites to `Set.univ` inside the type, so the left-hand
side is not in `simp` normal form. -/
theorem sobolevGaugeFixedComplexOperator_apply (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevGaugeFixedComplexOperator a y = sobolevGaugeFixedOperator a y := by
  rw [← restrictScalars_sobolevGaugeFixedComplexOperator, ContinuousLinearMap.coe_restrictScalars']

/-- **The complex-linear family is continuous.** The real operators underlying
`TauCeti.Vortex.sobolevGaugeFixedComplexOperator a` depend continuously, indeed Lipschitz, on the
coefficient class `a` in `L∞` (`TauCeti.Vortex.exists_lipschitzWith_sobolevGaugeFixedOperator`). -/
theorem continuous_restrictScalars_sobolevGaugeFixedComplexOperator :
    Continuous fun a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ ↦
      (sobolevGaugeFixedComplexOperator a).restrictScalars ℝ := by
  simp_rw [restrictScalars_sobolevGaugeFixedComplexOperator]
  obtain ⟨K, hK⟩ := exists_lipschitzWith_sobolevGaugeFixedOperator
  exact hK.continuous

/-! ### Complex kernel charts near a vortex -/

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {a₀ : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- **Complex kernel charts of the vortex deformation operators.** Let `x` be a continuous plane
vortex lying in the affine field space `A_m^k` for every `k`, with `L∞` class `a₀`. Then one
complex-linear kernel coordinate `q : H¹(ℂ)⁴ × ℂ⁰ →L[ℂ] ℂᵐ`, with the zero stabilizer, is a kernel
chart of the complex-linear operators `L_a` for every `a` in an open neighbourhood of `a₀`: the
pair of the underlying real operators is invertible there. Its model is `ℂᵐ`, of the real
dimension `2m` of the kernel of `L_{a₀}`, the tangent space of `Sym^m ℂ`. By
`ContinuousLinearMap.isComplexPositiveTMulDual_detLineChartEquiv_iff`, the chart reads the complex
orientations of all these determinant lines as the complex orientation of
`det ℂᵐ ⊗ (det ℂ⁰)^*`. -/
theorem exists_isOpen_isInvertible_prod_coprod_sobolevGaugeFixedComplexOperator
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hsol : ∀ z, equation x z = 0) (hax : a₀ =ᵐ[μ⊤] x) :
    ∃ q : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) × (Fin 0 → ℂ) →L[ℂ] (Fin m → ℂ),
      ∃ U : Set (Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤), IsOpen U ∧ a₀ ∈ U ∧ ∀ a ∈ U,
        ((((sobolevGaugeFixedComplexOperator a).restrictScalars ℝ).coprod
          ((0 : (Fin 0 → ℂ) →L[ℂ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤).restrictScalars ℝ)).prod
            (q.restrictScalars ℝ)).IsInvertible := by
  have hxs := contDiff_of_forall_mem_framedFieldSpace hx hmem
  have hsurj : Function.Surjective ((sobolevGaugeFixedComplexOperator a₀).restrictScalars ℝ) := by
    rw [restrictScalars_sobolevGaugeFixedComplexOperator]
    exact sobolevGaugeFixedOperator_surjective (hxs.of_le (by simp)) hsol
      (tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx) hax
  have hdim : finrank ℝ ((sobolevGaugeFixedComplexOperator a₀).restrictScalars ℝ).ker = 2 * m := by
    rw [restrictScalars_sobolevGaugeFixedComplexOperator]
    exact finrank_ker_sobolevGaugeFixedOperator_eq_two_mul hx hmem (fun w ↦ by simp [hsol w]) hax
  have : FiniteDimensional ℝ ((sobolevGaugeFixedComplexOperator a₀).restrictScalars ℝ).ker := by
    rw [restrictScalars_sobolevGaugeFixedComplexOperator]
    exact (isFredholm_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace hx hmem hsol
      hax).finite_ker
  obtain ⟨n, hn, q, U, hU, ha₀, hUinv⟩ :=
    ContinuousLinearMap.exists_isOpen_isInvertible_prod_coprod_of_surjective
      continuous_restrictScalars_sobolevGaugeFixedComplexOperator.continuousAt hsurj
  obtain rfl : n = m := by omega
  exact ⟨q, U, hU, ha₀, hUinv⟩

end TauCeti.Vortex
