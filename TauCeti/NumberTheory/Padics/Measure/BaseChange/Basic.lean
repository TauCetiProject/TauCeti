/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.NumberTheory.Padics.Measure.FiniteProjection
public import TauCeti.Topology.ContinuousMap.AutomaticContinuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.NumberTheory.Padics.Measure.Topology.Basic

/-!
# Finite free base change of abstract measures

Let `R` be a compact topological commutative ring and `O` a Hausdorff topological commutative
`R`-algebra that is finite and free as an `R`-module and has continuous `R`-scalar action
(`ContinuousSMul R O`). The main arithmetic case is `R = ℤ_p` and `O` the valuation ring of a
finite extension of `ℚ_p` (or any normed commutative ring that is finite and free over `ℤ_p` with
continuous `ℤ_p`-action).

Because `R` is compact and `O` is finitely generated and Hausdorff over `R`, every `R`-linear
functional `l : O →ₗ[R] R` is automatically continuous
(`LinearMap.toContinuousLinearMapOfFiniteOfCompactSpace`), inducing a basis-free scalar-retraction
map `mapScalars l : D(X, O) →+ D(X, R)` sending `ν` to `g ↦ l (ν (algebraMap R O ∘ g))`. When `O`
is moreover free over `R`, choosing a finite `R`-basis `(b_i)` of `O` decomposes every test
function `f ∈ C(X, O)` into continuous `R`-valued coordinate functions
(`ContinuousMap.eq_sum_smul_algebraMapCLM_comp`), allowing an `R`-valued measure `μ ∈ D(X, R)` on
any topological space `X` to be extended to an `O`-valued measure `extendScalars O μ ∈ D(X, O)`.
Although constructed via a basis, `extendScalars O μ` is uniquely determined by the basis-free
identity `extendScalars O μ (algebraMap R O ∘ g) = algebraMap R O (μ g)` for `g ∈ C(X, R)`.
Assembling scalar multiplication on the left with `extendScalars O` produces a canonical `O`-linear
equivalence `baseChangeLinearEquiv O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)` whose inverse expands in any
finite `R`-basis via `mapScalars (b.coord i)`.

When `G` is a locally compact topological monoid (not necessarily commutative or compact),
`extendScalars O` respects right convolution, upgrading `baseChangeLinearEquiv O` to an `O`-algebra
isomorphism `baseChangeAlgEquiv O : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` sending `a ⊗ₜ dirac R x` to
`a • dirac O x`. On `ℤ_p`, `mapScalars l` and `extendScalars O` act coefficientwise on the Amice
transform (`coeff_amiceTransform_mapScalars`, `amiceTransform_extendScalars`). The comparison with
the completed group algebra `O[[Γ]]` of a profinite group `Γ` is developed in
`TauCeti.NumberTheory.Padics.Measure.BaseChange.CompletedGroupAlgebra`.

The continuity assumption `ContinuousSMul ℤ_p O` is essential: equipping `O = ℤ_p` with an
archimedean norm `|ι(·)|` via an abstract field embedding `ι : ℚ_p → ℂ` produces a free rank-one
normed `ℤ_p`-algebra on which the `ℤ_p`-measure `μ = ∑_{n ≥ 1} p^n δ_{p^n}` cannot extend to a
continuous linear functional on `C(ℤ_p, O)`, because the indicator multiples
`(p^m + 1)⁻¹ • 1_{p^m + p^{m + 1} ℤ_p}` tend uniformly to `0` in `C(ℤ_p, O)` while their putative
integrals `p^m / (p^m + 1)` tend to `1`. A negative-control `example` at the end of the file
records that `ContinuousSMul ℤ_[p] O` fails whenever `p^n • (1 : O)` does not tend to `0`.

## Main definitions

* `AbstractMeasure.mapScalars l`: the additive retraction `D(X, O) →+ D(X, R)` along `l : O →ₗ[R] R`
  when `O` is finite and Hausdorff over compact `R` with `ContinuousSMul R O`.
* `AbstractMeasure.extendScalars O`: the `algebraMap R O`-semilinear extension map
  `D(X, R) →ₛₗ[algebraMap R O] D(X, O)`.
* `AbstractMeasure.baseChangeLinearEquiv O`: the `O`-linear isomorphism
  `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.
* `AbstractMeasure.extendScalarsRingHom O`: `extendScalars O` bundled as a ring homomorphism
  `D(G, R) →+* D(G, O)` on a locally compact topological monoid `G`.
* `AbstractMeasure.baseChangeAlgEquiv O`: the `O`-algebra isomorphism
  `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` on a locally compact topological monoid `G`.

## Main results

* `AbstractMeasure.ext_of_apply_comp_algebraMap`: for a finite free Hausdorff topological
  `R`-algebra `O` with `ContinuousSMul R O`, two `O`-valued measures agree if they agree on test
  functions of the form `algebraMap R O ∘ g` with `g ∈ C(X, R)`.
* `AbstractMeasure.mapScalars_smul_dirac`, `AbstractMeasure.mapScalars_mapScalars`,
  `AbstractMeasure.extendScalars_apply_comp_algebraMap`,
  `AbstractMeasure.extendScalars_apply_eq_sum`, `AbstractMeasure.extendScalars_self`,
  `AbstractMeasure.extendScalars_apply_one`, `AbstractMeasure.extendScalars_extendScalars`,
  `AbstractMeasure.extendScalars_injective`, `AbstractMeasure.extendScalars_dirac`,
  `AbstractMeasure.extendScalars_map`, `AbstractMeasure.finiteProjection_extendScalars`,
  `AbstractMeasure.baseChangeLinearEquiv_symm_extendScalars`,
  `AbstractMeasure.baseChangeLinearEquiv_symm_dirac`,
  `AbstractMeasure.baseChangeLinearEquiv_symm_apply`.
* `AbstractMeasure.coeff_amiceTransform_mapScalars`, `AbstractMeasure.amiceTransform_extendScalars`:
  Amice-transform formulas for `mapScalars` and `extendScalars` on `ℤ_p`.
* `AbstractMeasure.continuous_mapScalars_weak`, `AbstractMeasure.continuous_extendScalars_weak`:
  weak-topology continuity of `mapScalars` and `extendScalars` over normed commutative rings.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, §3.3, Proposition 3.16.
-/

public noncomputable section

open ContinuousMap
open scoped PowerSeries TensorProduct

namespace AbstractMeasure

section TopologicalSpace

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]

section Finite

variable {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O] [Module.Finite R O]

/-- **Scalar retraction of abstract measures along an `R`-linear form.** For `l : O →ₗ[R] R` on a
finitely generated Hausdorff topological `R`-algebra `O` over a compact ring `R` with continuous
`R`-action, `mapScalars l` sends `ν ∈ D(X, O)` to the `R`-valued measure
`g ↦ l (ν (algebraMap R O ∘ g))`. -/
def mapScalars (l : O →ₗ[R] R) : D(X, O) →+ D(X, R) where
  toFun ν := toCLMEquiv.symm
    (l.toContinuousLinearMapOfFiniteOfCompactSpace.comp
      (((toCLMEquiv ν).restrictScalars R).comp
        ((algebraMapCLM R O).compLeftContinuous R X)))
  map_zero' := by ext g; simp [← coe_toCLMEquiv]
  map_add' ν₁ ν₂ := by ext g; simp [← coe_toCLMEquiv]

/-- Evaluating `mapScalars l ν` on `g ∈ C(X, R)` applies `l` to `ν (algebraMap R O ∘ g)`. -/
@[simp]
theorem mapScalars_apply (l : O →ₗ[R] R) (ν : D(X, O)) (g : C(X, R)) :
    mapScalars l ν g = l (ν ((algebraMapCLM R O : C(R, O)).comp g)) := by
  simp only [mapScalars, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coe_symm_toCLMEquiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    LinearMap.coe_toContinuousLinearMapOfFiniteOfCompactSpace, coe_toCLMEquiv,
    ContinuousLinearMap.compLeftContinuous_apply]
  rfl

/-- Retracting along the zero linear form gives the zero homomorphism. -/
@[simp]
theorem mapScalars_zero :
    mapScalars (X := X) (0 : O →ₗ[R] R) = 0 := by
  ext ν g
  rw [AddMonoidHom.zero_apply, mapScalars_apply, LinearMap.zero_apply]
  simp [← coe_toCLMEquiv]

/-- Retracting along a sum of linear forms is the sum of the retractions. -/
@[simp]
theorem mapScalars_add (l₁ l₂ : O →ₗ[R] R) :
    mapScalars (X := X) (l₁ + l₂) = mapScalars l₁ + mapScalars l₂ := by
  ext ν g
  rw [AddMonoidHom.add_apply, mapScalars_apply, LinearMap.add_apply, ← mapScalars_apply,
    ← mapScalars_apply]
  simp [← coe_toCLMEquiv]

/-- Retracting along `r • l` scales the retracted measure by `r`. -/
@[simp]
theorem mapScalars_smul (r : R) (l : O →ₗ[R] R) (ν : D(X, O)) :
    mapScalars (r • l) ν = r • mapScalars l ν := by
  ext g
  simp

/-- Retracting `a • dirac O x` along `l : O →ₗ[R] R` gives `l a • dirac R x`. -/
@[simp]
theorem mapScalars_smul_dirac (l : O →ₗ[R] R) (a : O) (x : X) :
    mapScalars l (a • dirac O x) = l a • dirac R x := by
  ext g
  simp only [mapScalars_apply, _root_.smul_apply, dirac_apply, comp_apply,
    ContinuousMap.coe_ofClass, algebraMapCLM_apply, smul_eq_mul]
  rw [mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- Retracting a Dirac measure along `l : O →ₗ[R] R` scales the scalar Dirac measure by `l 1`. -/
@[simp]
theorem mapScalars_dirac (l : O →ₗ[R] R) (x : X) :
    mapScalars l (dirac O x) = l 1 • dirac R x := by
  simpa using mapScalars_smul_dirac l (1 : O) x

/-- Retracting scalars in two steps along a scalar tower `R → O → O'` agrees with retracting
directly along `l₁.comp (l₂.restrictScalars R)`. -/
@[simp]
theorem mapScalars_mapScalars [CompactSpace O]
    {O' : Type*} [CommRing O'] [TopologicalSpace O'] [IsTopologicalRing O'] [T2Space O']
    [Algebra R O'] [Algebra O O'] [IsScalarTower R O O']
    [ContinuousSMul R O'] [ContinuousSMul O O'] [Module.Finite O O'] [Module.Finite R O']
    (l₁ : O →ₗ[R] R) (l₂ : O' →ₗ[O] O) (ν : D(X, O')) :
    mapScalars l₁ (mapScalars l₂ ν) = mapScalars (l₁.comp (l₂.restrictScalars R)) ν := by
  ext g
  have hcomp : (algebraMapCLM O O' : C(O, O')).comp ((algebraMapCLM R O : C(R, O)).comp g) =
      (algebraMapCLM R O' : C(R, O')).comp g := by
    ext x
    simp [IsScalarTower.algebraMap_apply R O O']
  simp [hcomp]

/-- Scalar retraction commutes with pushforward along any continuous map `X → Y`. -/
@[simp]
theorem mapScalars_map (l : O →ₗ[R] R) (φ : C(X, Y)) (ν : D(X, O)) :
    mapScalars l (map φ ν) = map φ (mapScalars l ν) := by
  ext g
  have hcomp : ((algebraMapCLM R O : C(R, O)).comp g).comp φ =
      (algebraMapCLM R O : C(R, O)).comp (g.comp φ) := by ext x; rfl
  simp [hcomp]

/-- Scalar retraction applies `l` to all finite projections. -/
@[simp]
theorem finiteProjection_mapScalars {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (l : O →ₗ[R] R) (q : C(X, A)) (ν : D(X, O)) :
    finiteProjection q (mapScalars l ν) = (finiteProjection q ν).mapRange l (map_zero l) := by
  classical
  ext a
  have hfib : q.fiberIndicator (R := O) a =
      (algebraMapCLM R O : C(R, O)).comp (q.fiberIndicator (R := R) a) := by
    ext x
    by_cases hx : q x = a <;> simp [fiberIndicator_apply, hx]
  rw [finiteProjection_apply, Finsupp.mapRange_apply, finiteProjection_apply, hfib,
    mapScalars_apply]

end Finite

/-- Over a Hausdorff compact commutative ring `R`, retracting along `LinearMap.id` is the identity
on `D(X, R)`. -/
@[simp]
theorem mapScalars_id [T2Space R] (μ : D(X, R)) :
    mapScalars (LinearMap.id : R →ₗ[R] R) μ = μ := by
  ext g
  have hg : (algebraMapCLM R R : C(R, R)).comp g = g := by ext x; simp
  simp [hg]

section FiniteFree

variable (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O]

variable (R) {O} in
/-- **Scalar-test extensionality for `O`-valued measures.** When `O` is a finite free Hausdorff
topological `R`-algebra (`T2Space O`) over a compact ring `R` with continuous `R`-action, two
`O`-valued measures on `X` agree if they agree on all test functions of the form
`algebraMap R O ∘ g` with `g ∈ C(X, R)`. -/
theorem ext_of_apply_comp_algebraMap [Module.Free R O] [Module.Finite R O] {ν₁ ν₂ : D(X, O)}
    (h : ∀ g : C(X, R),
      ν₁ ((algebraMapCLM R O : C(R, O)).comp g) = ν₂ ((algebraMapCLM R O : C(R, O)).comp g)) :
    ν₁ = ν₂ := by
  let b := Module.Free.chooseBasis R O
  ext f
  rw [f.eq_sum_smul_algebraMapCLM_comp b]
  simp only [map_sum, map_smul, h]

/-- Auxiliary `O`-measure attached to `μ : D(X, R)` using an explicit finite `R`-basis `b` of
`O`. -/
private def extendScalarsWithBasis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (μ : D(X, R)) : D(X, O) :=
  have : Module.Finite R O := Module.Finite.of_basis b
  let coordCLM (i : ι) : C(X, O) →L[R] C(X, R) :=
    (b.coord i).toContinuousLinearMapOfFiniteOfCompactSpace.compLeftContinuous R X
  let φ : C(X, O) →L[R] O :=
    ∑ i : ι, ((toCLMEquiv μ).comp (coordCLM i)).smulRight (b i)
  toCLMEquiv.symm
    { toFun := φ
      map_add' := φ.map_add
      map_smul' c f := by
        have hval (j : ι) (g : C(X, O)) (x : X) : coordCLM j g x = b.coord j (g x) := by
          simp [coordCLM]
        have hcomp (i : ι) :
            coordCLM i (c • f) = ∑ j : ι, b.coord i (c * b j) • coordCLM j f := by
          ext x
          simp only [hval, ContinuousMap.coe_smul, Pi.smul_apply, ContinuousMap.coe_sum,
            Finset.sum_apply, smul_eq_mul]
          conv_lhs => rw [← b.sum_repr (f x)]
          simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Module.Basis.coord_apply,
            smul_eq_mul, mul_comm]
        simp only [φ, FunLike.coe_sum, Finset.sum_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, coe_toCLMEquiv,
          RingHom.id_apply]
        calc
          ∑ i : ι, μ (coordCLM i (c • f)) • b i
              = ∑ i : ι, ∑ j : ι,
                  (b.coord i (c * b j) * μ (coordCLM j f)) • b i := by
                refine Finset.sum_congr rfl fun i _ ↦ ?_
                rw [hcomp i, map_sum, Finset.sum_smul]
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                rw [map_smul, smul_eq_mul]
          _ = ∑ j : ι, μ (coordCLM j f) •
                ∑ i : ι, b.coord i (c * b j) • b i := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun i _ ↦ ?_
                rw [mul_comm, mul_smul]
          _ = c • ∑ j : ι, μ (coordCLM j f) • b j := by
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                simp_rw [Module.Basis.coord_apply]
                rw [b.sum_repr, ← smul_eq_mul c, smul_comm]
      cont := φ.continuous }

private theorem extendScalarsWithBasis_apply_comp_algebraMap {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (μ : D(X, R)) (g : C(X, R)) :
    extendScalarsWithBasis O b μ ((algebraMapCLM R O : C(R, O)).comp g) =
      algebraMap R O (μ g) := by
  have : Module.Finite R O := Module.Finite.of_basis b
  have hcomp (i : ι) :
      (b.coord i).toContinuousLinearMapOfFiniteOfCompactSpace.compLeftContinuous R X
        ((algebraMapCLM R O : C(R, O)).comp g) = b.coord i 1 • g := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
  simp only [extendScalarsWithBasis, coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, coe_toCLMEquiv, hcomp,
    map_smul, smul_eq_mul]
  calc
    ∑ i : ι, (b.coord i 1 * μ g) • b i
        = μ g • ∑ i : ι, b.coord i 1 • b i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [mul_comm, mul_smul]
    _ = algebraMap R O (μ g) := by
          simp only [Module.Basis.coord_apply, b.sum_repr, Algebra.algebraMap_eq_smul_one]

variable [Module.Free R O] [Module.Finite R O]

/-- **Scalar extension of abstract measures.** Extends `R`-valued measures on `X` semilinearly
along `algebraMap R O` to `O`-valued measures on `X`, uniquely determined by
`extendScalars_apply_comp_algebraMap`. -/
def extendScalars : D(X, R) →ₛₗ[algebraMap R O] D(X, O) where
  toFun := extendScalarsWithBasis O (Module.Free.chooseBasis R O)
  map_add' μ ν := ext_of_apply_comp_algebraMap R fun g ↦ by
    simp [extendScalarsWithBasis_apply_comp_algebraMap]
  map_smul' r μ := ext_of_apply_comp_algebraMap R fun g ↦ by
    simp [extendScalarsWithBasis_apply_comp_algebraMap]

variable {O}

/-- On scalar-valued test functions `algebraMap R O ∘ g`, `extendScalars O μ` applies
`algebraMap R O` to `μ g`. -/
@[simp]
theorem extendScalars_apply_comp_algebraMap (μ : D(X, R)) (g : C(X, R)) :
    extendScalars O μ ((algebraMapCLM R O : C(R, O)).comp g) = algebraMap R O (μ g) := by
  rw [extendScalars]
  exact extendScalarsWithBasis_apply_comp_algebraMap O (Module.Free.chooseBasis R O) μ g

/-- An `O`-valued measure equals `extendScalars O μ` if and only if it takes the value
`algebraMap R O (μ g)` on `algebraMap R O ∘ g` for every `g ∈ C(X, R)`. -/
theorem eq_extendScalars_iff {ν : D(X, O)} {μ : D(X, R)} :
    ν = extendScalars O μ ↔
      ∀ g : C(X, R), ν ((algebraMapCLM R O : C(R, O)).comp g) = algebraMap R O (μ g) :=
  ⟨fun h g ↦ h ▸ extendScalars_apply_comp_algebraMap μ g,
    fun h ↦ ext_of_apply_comp_algebraMap R fun g ↦
      (h g).trans (extendScalars_apply_comp_algebraMap μ g).symm⟩

/-- Explicit coordinate formula for `extendScalars O μ f` in any finite `R`-basis `b` of `O`. -/
theorem extendScalars_apply_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι R O) (μ : D(X, R))
    (f : C(X, O)) :
    extendScalars O μ f =
      ∑ i : ι,
        μ (((b.coord i).toContinuousLinearMapOfFiniteOfCompactSpace : C(O, R)).comp f) • b i := by
  conv_lhs => rw [f.eq_sum_smul_algebraMapCLM_comp b]
  simp only [map_sum, map_smul, extendScalars_apply_comp_algebraMap, smul_eq_mul,
    mul_comm (b _), ← Algebra.smul_def]

/-- Evaluating `extendScalars O μ` at the constant test function `1 : C(X, O)` applies
`algebraMap R O` to `μ 1`. -/
@[simp]
theorem extendScalars_apply_one (μ : D(X, R)) :
    extendScalars O μ 1 = algebraMap R O (μ 1) := by
  have h1 : (1 : C(X, O)) = (algebraMapCLM R O : C(R, O)).comp 1 := by ext x; simp
  rw [h1, extendScalars_apply_comp_algebraMap]

/-- When `algebraMap R O` is injective, `extendScalars O : D(X, R) → D(X, O)` is injective. -/
theorem extendScalars_injective (hinj : Function.Injective (algebraMap R O)) :
    Function.Injective (extendScalars (X := X) (R := R) O) := fun μ₁ μ₂ h ↦ by
  ext g
  exact hinj <| by
    simpa only [extendScalars_apply_comp_algebraMap] using
      congrArg (fun ν : D(X, O) ↦ ν ((algebraMapCLM R O : C(R, O)).comp g)) h

/-- Extending scalars in two steps along a scalar tower `R → O → O'` agrees with extending directly
from `R` to `O'`. -/
@[simp]
theorem extendScalars_extendScalars [CompactSpace O]
    {O' : Type*} [CommRing O'] [TopologicalSpace O'] [IsTopologicalRing O'] [T2Space O']
    [Algebra R O'] [Algebra O O'] [IsScalarTower R O O']
    [ContinuousSMul R O'] [ContinuousSMul O O']
    [Module.Free O O'] [Module.Finite O O'] [Module.Free R O'] [Module.Finite R O']
    (μ : D(X, R)) :
    extendScalars O' (extendScalars O μ) = extendScalars O' μ := by
  refine eq_extendScalars_iff.mpr fun g ↦ ?_
  have hcomp : (algebraMapCLM R O' : C(R, O')).comp g =
      (algebraMapCLM O O' : C(O, O')).comp ((algebraMapCLM R O : C(R, O)).comp g) := by
    ext x
    simp [IsScalarTower.algebraMap_apply R O O']
  rw [hcomp, extendScalars_apply_comp_algebraMap, extendScalars_apply_comp_algebraMap,
    IsScalarTower.algebraMap_apply R O O']

/-- Extending scalars sends Dirac measures to Dirac measures. -/
@[simp]
theorem extendScalars_dirac (x : X) :
    extendScalars O (dirac R x) = dirac O x :=
  ext_of_apply_comp_algebraMap R fun g ↦ by simp

/-- Extending scalars commutes with pushforward along any continuous map `X → Y`. -/
@[simp]
theorem extendScalars_map (φ : C(X, Y)) (μ : D(X, R)) :
    extendScalars O (map φ μ) = map φ (extendScalars O μ) :=
  ext_of_apply_comp_algebraMap R fun g ↦ by
    have hcomp : ((algebraMapCLM R O : C(R, O)).comp g).comp φ =
        (algebraMapCLM R O : C(R, O)).comp (g.comp φ) := by ext x; rfl
    simp [hcomp]

/-- Extending scalars applies `algebraMap R O` to all finite projections. -/
@[simp]
theorem finiteProjection_extendScalars {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (q : C(X, A)) (μ : D(X, R)) :
    finiteProjection q (extendScalars O μ) =
      (finiteProjection q μ).mapRange (algebraMap R O) (map_zero _) := by
  classical
  ext a
  have hfib : q.fiberIndicator (R := O) a =
      (algebraMapCLM R O : C(R, O)).comp (q.fiberIndicator (R := R) a) := by
    ext x
    by_cases hx : q x = a <;> simp [fiberIndicator_apply, hx]
  rw [finiteProjection_apply, Finsupp.mapRange_apply, finiteProjection_apply, hfib,
    extendScalars_apply_comp_algebraMap]

/-- Retracting `a • extendScalars O μ` along an `R`-linear form `l : O →ₗ[R] R` gives `l a • μ`. -/
@[simp]
theorem mapScalars_smul_extendScalars (l : O →ₗ[R] R) (a : O) (μ : D(X, R)) :
    mapScalars l (a • extendScalars O μ) = l a • μ := by
  ext g
  simp only [mapScalars_apply, _root_.smul_apply, extendScalars_apply_comp_algebraMap,
    smul_eq_mul]
  rw [mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- Retracting `extendScalars O μ` along an `R`-linear form `l : O →ₗ[R] R` scales `μ` by `l 1`. -/
@[simp]
theorem mapScalars_extendScalars (l : O →ₗ[R] R) (μ : D(X, R)) :
    mapScalars l (extendScalars O μ) = l 1 • μ := by
  simpa using mapScalars_smul_extendScalars l (1 : O) μ

variable (O)

/-- Forward `O`-linear map `O ⊗[R] D(X, R) →ₗ[O] D(X, O)` sending `a ⊗ₜ μ` to
`a • extendScalars O μ`. -/
private def baseChangeLinearMap : O ⊗[R] D(X, R) →ₗ[O] D(X, O) :=
  letI : Module R D(X, O) := .restrictScalars R O D(X, O)
  haveI : IsScalarTower R O D(X, O) := .restrictScalars R O D(X, O)
  LinearMap.liftBaseChange O
    { (extendScalars O).toAddHom with
      map_smul' := (extendScalars O).map_smulₛₗ }

@[simp]
private theorem baseChangeLinearMap_tmul (a : O) (μ : D(X, R)) :
    baseChangeLinearMap O (a ⊗ₜ[R] μ) = a • extendScalars O μ :=
  (rfl)

private def baseChangeInvAux {ι : Type*} [Fintype ι] (b : Module.Basis ι R O) :
    D(X, O) →+ O ⊗[R] D(X, R) where
  toFun ν := ∑ i : ι, b i ⊗ₜ[R] mapScalars (b.coord i) ν
  map_zero' := by simp
  map_add' ν₁ ν₂ := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

private theorem baseChangeInvAux_comp_baseChangeLinearMap {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (z : O ⊗[R] D(X, R)) :
    baseChangeInvAux O b (baseChangeLinearMap O z) = z := by
  refine TensorProduct.inductionOn z ?_ fun z₁ z₂ hz₁ hz₂ ↦ by
    rw [map_add, map_add, hz₁, hz₂]
  intro a μ
  simp only [baseChangeLinearMap_tmul, baseChangeInvAux, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    mapScalars_smul_extendScalars]
  simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, Module.Basis.coord_apply,
    b.sum_repr]

private theorem baseChangeLinearMap_comp_baseChangeInvAux {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (ν : D(X, O)) :
    baseChangeLinearMap O (baseChangeInvAux O b ν) = ν := by
  apply ext_of_apply_comp_algebraMap R
  intro g
  rw [← coe_toCLMEquiv]
  simp only [baseChangeInvAux, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum,
    baseChangeLinearMap_tmul, _root_.sum_apply, coe_toCLMEquiv, _root_.smul_apply,
    extendScalars_apply_comp_algebraMap, mapScalars_apply, smul_eq_mul, mul_comm (b _),
    ← Algebra.smul_def, Module.Basis.coord_apply]
  exact b.sum_repr (ν ((algebraMapCLM R O : C(R, O)).comp g))

/-- **Finite free base change of abstract measures.** When `O` is a finite free Hausdorff
topological `R`-algebra over a compact commutative ring `R` with continuous `R`-action,
`O ⊗[R] D(X, R)` is canonically isomorphic as an `O`-module to `D(X, O)`. -/
def baseChangeLinearEquiv : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O) :=
  let b := Module.Free.chooseBasis R O
  LinearEquiv.ofBijective (baseChangeLinearMap O)
    ⟨Function.LeftInverse.injective (baseChangeInvAux_comp_baseChangeLinearMap O b),
      Function.RightInverse.surjective (baseChangeLinearMap_comp_baseChangeInvAux O b)⟩

variable {O}

/-- `baseChangeLinearEquiv O` sends `a ⊗ₜ μ` to `a • extendScalars O μ`. -/
@[simp]
theorem baseChangeLinearEquiv_tmul (a : O) (μ : D(X, R)) :
    baseChangeLinearEquiv O (a ⊗ₜ[R] μ) = a • extendScalars O μ :=
  (rfl)

/-- `(baseChangeLinearEquiv O).symm` sends `extendScalars O μ` to `1 ⊗ₜ μ`. -/
@[simp]
theorem baseChangeLinearEquiv_symm_extendScalars (μ : D(X, R)) :
    (baseChangeLinearEquiv O).symm (extendScalars O μ) = (1 : O) ⊗ₜ[R] μ := by
  apply (baseChangeLinearEquiv O).injective
  simp

/-- `(baseChangeLinearEquiv O).symm` sends `dirac O x` to `1 ⊗ₜ dirac R x`. -/
@[simp]
theorem baseChangeLinearEquiv_symm_dirac (x : X) :
    (baseChangeLinearEquiv O).symm (dirac O x) = (1 : O) ⊗ₜ[R] dirac R x := by
  rw [← extendScalars_dirac (R := R), baseChangeLinearEquiv_symm_extendScalars]

/-- In any finite `R`-basis `b` of `O`, `(baseChangeLinearEquiv O).symm ν` decomposes as
`∑ i, b i ⊗ₜ mapScalars (b.coord i) ν`. -/
theorem baseChangeLinearEquiv_symm_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (ν : D(X, O)) :
    (baseChangeLinearEquiv O).symm ν = ∑ i : ι, b i ⊗ₜ[R] mapScalars (b.coord i) ν := by
  apply (baseChangeLinearEquiv O).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (baseChangeLinearMap_comp_baseChangeInvAux O b ν).symm

end FiniteFree

/-- Extending scalars from a Hausdorff compact commutative ring `R` to itself is the identity map
on `D(X, R)`. -/
@[simp]
theorem extendScalars_self [T2Space R] (μ : D(X, R)) :
    extendScalars R μ = μ :=
  ext_of_apply_comp_algebraMap R fun g ↦ by
    have hg : (algebraMapCLM R R : C(R, R)).comp g = g := by ext x; simp
    rw [extendScalars_apply_comp_algebraMap, hg]
    simp

end TopologicalSpace

section WeakTopology

variable {X R O : Type*} [TopologicalSpace X]
  [NormedCommRing R] [CompactSpace R]
  [NormedCommRing O] [Algebra R O] [ContinuousSMul R O]

/-- Over a compact normed commutative ring `R`, `mapScalars l : D(X, O) → D(X, R)` is continuous
for the weak topologies whenever `O` is finite over `R`. -/
theorem continuous_mapScalars_weak [Module.Finite R O] (l : O →ₗ[R] R) :
    @Continuous _ _ (WeakTopology (X := X) (R := O) (E := O))
      (WeakTopology (X := X) (R := R) (E := R)) (mapScalars l) := by
  let _ : TopologicalSpace D(X, O) := WeakTopology
  refine (continuous_weak_iff _).mpr fun g ↦ ?_
  simp only [mapScalars_apply]
  exact l.continuous_of_finite_of_compactSpace.comp
    (continuous_apply_weak ((algebraMapCLM R O : C(R, O)).comp g))

/-- Over a compact normed commutative ring `R`, `extendScalars O : D(X, R) → D(X, O)` is
continuous for the weak topologies whenever `O` is finite and free over `R`. -/
theorem continuous_extendScalars_weak [Module.Free R O] [Module.Finite R O] :
    @Continuous _ _ (WeakTopology (X := X) (R := R) (E := R))
      (WeakTopology (X := X) (R := O) (E := O)) (extendScalars O) := by
  let _ : TopologicalSpace D(X, R) := WeakTopology
  let b := Module.Free.chooseBasis R O
  refine (continuous_weak_iff _).mpr fun f ↦ ?_
  simp only [extendScalars_apply_eq_sum b]
  exact continuous_finsetSum _ fun i _ ↦
    (continuous_apply_weak
      (((b.coord i).toContinuousLinearMapOfFiniteOfCompactSpace : C(O, R)).comp f)).smul
      continuous_const

end WeakTopology

section Monoid

variable {G R O : Type*} [TopologicalSpace G] [Monoid G] [ContinuousMul G]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O] [Module.Free R O] [Module.Finite R O]

/-- Right convolution of `extendScalars O ν` with `algebraMap R O ∘ g` is `algebraMap R O`
postcomposed with `convolveFunRight ν g`. -/
theorem convolveFunRight_extendScalars_comp_algebraMap (ν : D(G, R)) (g : C(G, R)) :
    convolveFunRight (extendScalars O ν) ((algebraMapCLM R O : C(R, O)).comp g) =
      (algebraMapCLM R O : C(R, O)).comp (convolveFunRight ν g) := by
  ext x
  simp only [convolveFunRight_apply, comp_apply, ContinuousMap.coe_ofClass, algebraMapCLM_apply]
  exact extendScalars_apply_comp_algebraMap ν ⟨fun y ↦ g (x * y), by fun_prop⟩

omit [ContinuousMul G] [Module.Free R O] in
/-- Retracting the multiplicative identity `1 = dirac 1` along `l : O →ₗ[R] R` scales `1` by
`l 1`. -/
@[simp]
theorem mapScalars_one (l : O →ₗ[R] R) :
    mapScalars l (1 : D(G, O)) = l 1 • (1 : D(G, R)) := by
  simp [one_def]

omit [ContinuousMul G] [Module.Free R O] in
/-- Retracting `a • 1` along `l : O →ₗ[R] R` gives `l a • 1`. -/
@[simp]
theorem mapScalars_smul_one (l : O →ₗ[R] R) (a : O) :
    mapScalars l (a • (1 : D(G, O))) = l a • (1 : D(G, R)) := by
  simp [one_def]

omit [ContinuousMul G] in
/-- Extending scalars preserves the multiplicative identity `1 = dirac 1`. -/
@[simp]
theorem extendScalars_one : extendScalars O (1 : D(G, R)) = 1 := by
  simp [one_def]

section LocallyCompact

variable [LocallyCompactSpace G]

/-- Extending scalars preserves convolution of measures on any locally compact topological
monoid. -/
@[simp]
theorem extendScalars_mul (μ ν : D(G, R)) :
    extendScalars O (μ * ν) = extendScalars O μ * extendScalars O ν :=
  ext_of_apply_comp_algebraMap R fun g ↦ by
    rw [extendScalars_apply_comp_algebraMap, mul_apply, mul_apply,
      convolveFunRight_extendScalars_comp_algebraMap, extendScalars_apply_comp_algebraMap]

omit [Module.Free R O] in
/-- Scalar retraction intertwines the scalar embeddings `O → D(G, O)` and `R → D(G, R)`. -/
@[simp]
theorem mapScalars_algebraMap (l : O →ₗ[R] R) (a : O) :
    mapScalars l (algebraMap O D(G, O) a) = algebraMap R D(G, R) (l a) := by
  rw [Algebra.algebraMap_eq_smul_one, mapScalars_smul_one, ← Algebra.algebraMap_eq_smul_one]

/-- Extending scalars intertwines the scalar embeddings `R → D(G, R)` and `O → D(G, O)`. -/
@[simp]
theorem extendScalars_algebraMap (r : R) :
    extendScalars O (algebraMap R D(G, R) r) = algebraMap O D(G, O) (algebraMap R O r) := by
  rw [Algebra.algebraMap_eq_smul_one (R := R) (A := D(G, R)), map_smulₛₗ, extendScalars_one,
    ← Algebra.algebraMap_eq_smul_one]

variable (O) in
/-- `extendScalars O` bundled as a ring homomorphism of convolution rings `D(G, R) →+* D(G, O)`. -/
def extendScalarsRingHom : D(G, R) →+* D(G, O) where
  toFun := extendScalars O
  map_one' := extendScalars_one
  map_mul' := extendScalars_mul
  map_zero' := (extendScalars O).map_zero
  map_add' := (extendScalars O).map_add

/-- The underlying function of `extendScalarsRingHom O` is `extendScalars O`. -/
@[simp]
theorem coe_extendScalarsRingHom :
    ⇑(extendScalarsRingHom (G := G) (R := R) O) = extendScalars O :=
  (rfl)

variable (O) in
/-- **Finite free base-change algebra equivalence for measures.** On a locally compact topological
monoid `G` (not necessarily commutative), `O ⊗[R] D(G, R)` is canonically isomorphic as an
`O`-algebra to `D(G, O)`. -/
def baseChangeAlgEquiv : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (baseChangeLinearEquiv O)
    (fun a₁ a₂ μ₁ μ₂ ↦ by simp [smul_smul, mul_comm a₁ a₂])
    (by simp)

/-- The underlying `O`-linear equivalence of `baseChangeAlgEquiv O` is `baseChangeLinearEquiv O`. -/
@[simp]
theorem toLinearEquiv_baseChangeAlgEquiv :
    (baseChangeAlgEquiv (G := G) (R := R) O).toLinearEquiv = baseChangeLinearEquiv O :=
  (rfl)

/-- The underlying function of `baseChangeAlgEquiv O` is `baseChangeLinearEquiv O`. -/
@[simp]
theorem coe_baseChangeAlgEquiv :
    ⇑(baseChangeAlgEquiv (G := G) (R := R) O) = baseChangeLinearEquiv O :=
  (rfl)

/-- The inverse function of `baseChangeAlgEquiv O` is `(baseChangeLinearEquiv O).symm`. -/
@[simp]
theorem coe_symm_baseChangeAlgEquiv :
    ⇑(baseChangeAlgEquiv (G := G) (R := R) O).symm = ⇑(baseChangeLinearEquiv O).symm :=
  (rfl)

/-- `baseChangeLinearEquiv O` preserves the convolution identity. -/
@[simp]
theorem baseChangeLinearEquiv_one :
    baseChangeLinearEquiv O (1 : O ⊗[R] D(G, R)) = 1 :=
  (baseChangeAlgEquiv (G := G) (R := R) O).map_one

/-- `baseChangeLinearEquiv O` preserves convolution multiplication. -/
@[simp]
theorem baseChangeLinearEquiv_mul (z w : O ⊗[R] D(G, R)) :
    baseChangeLinearEquiv O (z * w) =
      baseChangeLinearEquiv O z * baseChangeLinearEquiv O w :=
  (baseChangeAlgEquiv (G := G) (R := R) O).map_mul z w

/-- `(baseChangeLinearEquiv O).symm` preserves the convolution identity. -/
@[simp]
theorem baseChangeLinearEquiv_symm_one :
    (baseChangeLinearEquiv (R := R) O).symm (1 : D(G, O)) = 1 :=
  (baseChangeAlgEquiv (G := G) (R := R) O).symm.map_one

/-- `(baseChangeLinearEquiv O).symm` preserves convolution multiplication. -/
@[simp]
theorem baseChangeLinearEquiv_symm_mul (ν₁ ν₂ : D(G, O)) :
    (baseChangeLinearEquiv (R := R) O).symm (ν₁ * ν₂) =
      (baseChangeLinearEquiv (R := R) O).symm ν₁ * (baseChangeLinearEquiv (R := R) O).symm ν₂ :=
  (baseChangeAlgEquiv (G := G) (R := R) O).symm.map_mul ν₁ ν₂

end LocallyCompact

end Monoid

section Amice

variable {p : ℕ} [Fact p.Prime]
  {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Finite ℤ_[p] O]

/-- Scalar retraction along `l : O →ₗ[ℤ_[p]] ℤ_[p]` acts coefficientwise on the Amice
transform. -/
@[simp]
theorem coeff_amiceTransform_mapScalars (l : O →ₗ[ℤ_[p]] ℤ_[p]) (ν : D(ℤ_[p], O)) (n : ℕ) :
    (mapScalars l ν).amiceTransform.coeff n = l (ν.amiceTransform.coeff n) := by
  simp only [coeff_amiceTransform, mapScalars_apply]
  congr 2
  ext x
  simp [Algebra.algebraMap_eq_smul_one]

/-- Extending scalars from `ℤ_p` to `O` applies `algebraMap ℤ_[p] O` to the coefficients of the
Amice transform. -/
@[simp]
theorem amiceTransform_extendScalars [Module.Free ℤ_[p] O] (μ : D(ℤ_[p], ℤ_[p])) :
    (extendScalars O μ).amiceTransform =
      PowerSeries.map (algebraMap ℤ_[p] O) μ.amiceTransform := by
  ext n
  simp only [coeff_amiceTransform, PowerSeries.coeff_map]
  rw [← extendScalars_apply_comp_algebraMap]
  congr 1
  ext x
  simp [Algebra.algebraMap_eq_smul_one]

end Amice

section Examples

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Monoid G] [TopologicalSpace G]
  [ContinuousMul G] [LocallyCompactSpace G]

/-! Sanity checks:
* for `O = ℤ_p`, `baseChangeAlgEquiv ℤ_[p]` is the canonical left-unit equivalence
  `Algebra.TensorProduct.lid`;
* `1 ⊗ₜ dirac ℤ_[p] x` maps to `dirac O x`;
* distinct scalars `a ≠ b` in `O` give distinct measures `a ⊗ₜ dirac ℤ_[p] x ≠ b ⊗ₜ dirac ℤ_[p] x`;
* negative control for `ContinuousSMul ℤ_[p] O`: if `p^n • (1 : O)` does not tend to `0` (as happens
  for `ℤ_p` equipped with an archimedean norm via an abstract field embedding `ℚ_p → ℂ`), the
  `ℤ_p`-action cannot be continuous. -/

example :
    baseChangeAlgEquiv (G := G) (R := ℤ_[p]) ℤ_[p] =
      Algebra.TensorProduct.lid ℤ_[p] D(G, ℤ_[p]) :=
  AlgEquiv.ext fun z ↦
    TensorProduct.inductionOn z
      (fun r μ ↦ by
        rw [coe_baseChangeAlgEquiv, baseChangeLinearEquiv_tmul, extendScalars_self,
          Algebra.TensorProduct.lid_tmul])
      fun z₁ z₂ hz₁ hz₂ ↦ by rw [map_add, map_add, hz₁, hz₂]

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] (x : G) :
    baseChangeAlgEquiv O ((1 : O) ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = dirac O x := by
  simp

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] {a b : O} (hab : a ≠ b) (x : G) :
    baseChangeAlgEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) ≠
      baseChangeAlgEquiv O (b ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) := by
  intro h
  apply hab
  have h1 := congrArg (fun ν : D(G, O) ↦ ν 1) h
  simpa using h1

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O]
    (h : ¬ Filter.Tendsto (fun n : ℕ ↦ ((p : ℤ_[p]) ^ n) • (1 : O)) Filter.atTop (nhds 0)) :
    ¬ ContinuousSMul ℤ_[p] O := by
  intro hc
  apply h
  have hp : ‖(p : ℤ_[p])‖ < 1 := by simpa using Padic.norm_p_lt_one (p := p)
  simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).smul_const (1 : O)

end Examples

end AbstractMeasure
