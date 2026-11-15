/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Algebra
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.BaseChange
import Mathlib.Data.Finsupp.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.NumberTheory.Padics.Measure.IntegralUnitBall
import TauCeti.Topology.Algebra.Module.Finite

/-!
# Finite free coefficient extension of abstract measures

Let `R` be a topological commutative ring and `O` a topological commutative `R`-algebra that is
finite and free as an `R`-module and carries the `R`-module topology (`IsModuleTopology R O`).
Every `R`-linear functional `φ : O →ₗ[R] R` is then continuous, as is `algebraMap R O`, so:

1. composing with `algebraMap R O` on test functions and applying `φ` on outputs extracts an
   `R`-valued coordinate measure `AbstractMeasure.mapAdd φ ν ∈ D(X, R)` from any `ν ∈ D(X, O)`;
2. decomposing `O`-valued test functions along a finite `R`-basis `b` of `O` extends any
   `μ ∈ D(X, R)` to an `O`-valued measure `AbstractMeasure.scalarExtend O μ ∈ D(X, O)` characterised
   basis-independently by `φ (scalarExtend O μ f) = μ (φ ∘ f)` for every `φ : O →ₗ[R] R`.

Because `C(X, O)` decomposes over any finite `R`-basis of `O` into finitely many `R`-valued
coordinate functions, these two constructions assemble — on *any* topological space `X`, without
compactness or total disconnectedness — into a canonical `O`-linear base-change equivalence
`AbstractMeasure.baseChange O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)` sending `a ⊗ₜ μ` to
`a • scalarExtend O μ`, with inverse `ν ↦ ∑ i, b i ⊗ₜ mapAdd (b.coord i) ν`. On any locally compact
topological monoid `G` with continuous multiplication, `scalarExtend O` preserves the convolution
unit and product, upgrading `baseChange O` to an `O`-algebra equivalence
`AbstractMeasure.baseChangeAlgEquiv O : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` without requiring `G` to be
commutative or compact.

Over `R = ℤ_[p]`, compactness of `ℤ_[p]` implies (`IsModuleTopology.of_compactSpace`) that *every*
Hausdorff topological `ℤ_[p]`-algebra `O` with continuous `ℤ_[p]`-scalar action that is finite and
free over `ℤ_[p]` — in particular every normed commutative `ℤ_[p]`-algebra `O` finite and free over
`ℤ_[p]` with `ContinuousSMul ℤ_[p] O`, such as the ring of integers of a finite extension of `ℚ_p` —
carries the `ℤ_[p]`-module topology. Specialising `baseChange` and `baseChangeAlgEquiv` therefore
produces `AbstractMeasure.completedGroupAlgebraBaseChange` and
`AbstractMeasure.completedGroupAlgebraBaseChangeAlgEquiv`. The `ContinuousSMul ℤ_[p] O` hypothesis
is essential: equipping `O` with an archimedean norm along an abstract embedding into `ℂ` makes
`p ^ n • 1` fail to tend to `0`, violating `ContinuousSMul ℤ_[p] O` and obstructing continuous
coordinate extraction.

For a profinite group `Γ`, base change of measures intertwines `toCompletedGroupAlgebra` with
`TauCeti.completedGroupAlgebra.baseChange ℤ_[p] O Γ`, identifying `D(Γ, O)` with `O[[Γ]]` as an
`O`-algebra (`AbstractMeasure.completedGroupAlgebraEquivOfFiniteFree`) and, when `O` is normed, as
a compact topological ring in the weak topology
(`AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree`,
`AbstractMeasure.compactSpace_measures_weak_of_finiteFree`,
`AbstractMeasure.isTopologicalRing_measures_weak_of_finiteFree`). Finally, finite free base change
commutes with `extendCoefficients` into the closed unit ball of a complete ultrametric field and
with the Amice transform on `ℤ_[p]`.

## Main definitions

* `AbstractMeasure.mapAdd φ`: additive coordinate map `D(X, O) →+ D(X, R)` attached to
  `φ : O →ₗ[R] R`.
* `AbstractMeasure.scalarExtend O`: additive extension `D(X, R) →+ D(X, O)` characterised by
  `φ (scalarExtend O μ f) = μ (φ ∘ f)`.
* `AbstractMeasure.baseChange O`: canonical `O`-linear equivalence `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.
* `AbstractMeasure.baseChangeAlgEquiv O`: canonical `O`-algebra equivalence
  `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` for convolution on a locally compact topological monoid `G`.
* `AbstractMeasure.completedGroupAlgebraBaseChange O`,
  `AbstractMeasure.completedGroupAlgebraBaseChangeAlgEquiv O`: the `ℤ_[p]`-specialisations under
  `[T2Space O] [ContinuousSMul ℤ_[p] O]`.
* `AbstractMeasure.completedGroupAlgebraEquivOfFiniteFree p O`: the `O`-algebra isomorphism
  `D(Γ, O) ≃ₐ[O] O[[Γ]]` for a profinite group `Γ`.

## Main results

* `AbstractMeasure.map_scalarExtend_apply`: basis-free characterisation of `scalarExtend O`.
* `AbstractMeasure.baseChange_tmul_dirac`, `AbstractMeasure.baseChange_mul`,
  `AbstractMeasure.baseChange_symm_eq_sum_basis`: values on Dirac tensors, multiplicativity, and
  basis expansion of the inverse.
* `AbstractMeasure.completedGroupAlgebraBaseChange_tmul_dirac`,
  `AbstractMeasure.completedGroupAlgebraBaseChange_mul`,
  `AbstractMeasure.exists_baseChange_algEquiv`: Dirac and convolution properties over `ℤ_[p]`.
* `AbstractMeasure.toCompletedGroupAlgebra_baseChange`,
  `AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree`,
  `AbstractMeasure.compactSpace_measures_weak_of_finiteFree`: compatibility with the completed
  group algebra and weak-topology consequences.
* `AbstractMeasure.extendCoefficients_baseChange_tmul`,
  `AbstractMeasure.extendCoefficients_completedGroupAlgebraBaseChange_tmul`,
  `AbstractMeasure.amiceTransform_completedGroupAlgebraBaseChange_tmul`: compatibility with
  unit-ball coefficient extension and the Amice transform.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, Proposition 3.16 and Remark 3.28.
-/

public noncomputable section

open ContinuousMap Filter Topology TauCeti
open scoped AbstractMeasure PowerSeries TensorProduct

namespace AbstractMeasure

@[simp]
private theorem zero_measure_apply {X R E : Type*} [TopologicalSpace X] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [Module R E] [ContinuousSMul R E] (f : C(X, R)) :
    (0 : AbstractMeasure X R E) f = 0 := by
  rw [← coe_toCLMEquiv, map_zero, _root_.zero_apply]

private theorem sum_measure_apply {ι X R E : Type*} [TopologicalSpace X] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [Module R E] [ContinuousSMul R E] (s : Finset ι)
    (μ : ι → AbstractMeasure X R E) (f : C(X, R)) :
    (∑ i ∈ s, μ i) f = ∑ i ∈ s, μ i f := by
  rw [← coe_toCLMEquiv, map_sum, FunLike.coe_sum, Finset.sum_apply]
  simp_rw [coe_toCLMEquiv]

section ModuleTopology

section TopologicalSpace

variable {X Y A R : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

section MapAdd

variable {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O]

/-- `algebraMap R O` bundled as a continuous map when `O` carries the `R`-module topology. -/
private def algebraMapContinuousMap (R O : Type*) [CommRing R] [TopologicalSpace R]
    [CommRing O] [TopologicalSpace O] [Algebra R O] [ContinuousSMul R O] : C(R, O) :=
  ⟨algebraMap R O, continuous_algebraMap R O⟩

omit [IsTopologicalRing R] [IsTopologicalRing O] in
@[simp]
private theorem algebraMapContinuousMap_apply (r : R) :
    algebraMapContinuousMap R O r = algebraMap R O r :=
  (rfl)

omit [IsTopologicalRing O] in
/-- An `R`-linear functional `φ : O →ₗ[R] R` bundled as a continuous map when `O` carries the
`R`-module topology. -/
private def linearContinuousMap (φ : O →ₗ[R] R) : C(O, R) :=
  ⟨φ, IsModuleTopology.continuous_of_linearMap φ⟩

omit [IsTopologicalRing O] in
@[simp]
private theorem linearContinuousMap_apply (φ : O →ₗ[R] R) (a : O) :
    linearContinuousMap φ a = φ a :=
  (rfl)

/-- **Coordinate extraction on measures.** Given `φ : O →ₗ[R] R` on an `R`-algebra `O` carrying the
`R`-module topology, `mapAdd φ` sends `ν ∈ D(X, O)` to the `R`-valued measure
`g ↦ φ (ν (algebraMap R O ∘ g))`. -/
def mapAdd (φ : O →ₗ[R] R) : D(X, O) →+ D(X, R) where
  toFun ν := toCLMEquiv.symm
    { toFun g := φ (ν ((algebraMapContinuousMap R O).comp g))
      map_add' g₁ g₂ := by
        have hcomp : (algebraMapContinuousMap R O).comp (g₁ + g₂) =
            (algebraMapContinuousMap R O).comp g₁ + (algebraMapContinuousMap R O).comp g₂ := by
          ext x
          simp
        rw [hcomp, map_add, map_add]
      map_smul' r g := by
        have hcomp : (algebraMapContinuousMap R O).comp (r • g) =
            algebraMap R O r • (algebraMapContinuousMap R O).comp g := by
          ext x
          simp [Algebra.smul_def]
        rw [hcomp, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, RingHom.id_apply]
      cont := (IsModuleTopology.continuous_of_linearMap φ).comp
        (ν.continuous.comp (continuous_postcomp (algebraMapContinuousMap R O))) }
  map_zero' := ext fun _ ↦ by simp
  map_add' _ _ := ext fun _ ↦ by simp

/-- Evaluating `mapAdd φ ν` on `g : C(X, R)` pushes `g` to `C(X, O)` via `algebraMap R O`, applies
`ν`, and applies `φ`. -/
@[simp]
theorem mapAdd_apply (φ : O →ₗ[R] R) (ν : D(X, O)) (g : C(X, R)) :
    mapAdd φ ν g = φ (ν ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp g)) := by
  simp [mapAdd, algebraMapContinuousMap]

/-- `mapAdd φ` intertwines scalar multiplication by `algebraMap R O r` with `r`. -/
theorem mapAdd_algebraMap_smul (φ : O →ₗ[R] R) (r : R) (ν : D(X, O)) :
    mapAdd φ (algebraMap R O r • ν) = r • mapAdd φ ν := by
  ext g
  simp only [mapAdd_apply, _root_.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- On `a • dirac O x`, `mapAdd φ` extracts `φ a • dirac R x`. -/
@[simp]
theorem mapAdd_smul_dirac (φ : O →ₗ[R] R) (a : O) (x : X) :
    mapAdd φ (a • dirac O x) = φ a • dirac R x := by
  ext g
  rw [mapAdd_apply, _root_.smul_apply, dirac_apply, comp_apply, ContinuousMap.coe_mk,
    _root_.smul_apply, dirac_apply, smul_eq_mul, mul_comm, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm, ← smul_eq_mul]

/-- On `dirac O x`, `mapAdd φ` evaluates to `φ 1 • dirac R x`. -/
@[simp]
theorem mapAdd_dirac (φ : O →ₗ[R] R) (x : X) :
    mapAdd φ (dirac O x) = φ 1 • dirac R x := by
  simpa using mapAdd_smul_dirac φ (1 : O) x

/-- Finite projections of `mapAdd φ ν` are obtained by applying `φ` to the coefficients of `ν`. -/
@[simp]
theorem finiteProjection_mapAdd [Finite A] [DiscreteTopology A] (φ : O →ₗ[R] R) (q : C(X, A))
    (ν : D(X, O)) :
    finiteProjection q (mapAdd φ ν) = (finiteProjection q ν).mapRange φ (map_zero φ) := by
  classical
  ext a
  rw [finiteProjection_apply, Finsupp.mapRange_apply, finiteProjection_apply, mapAdd_apply]
  congr 2
  ext x
  by_cases hx : q x = a <;> simp [fiberIndicator_apply, hx]

end MapAdd

section ScalarExtend

variable (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Free R O] [Module.Finite R O]

private def scalarExtendVal (μ : D(X, R)) (f : C(X, O)) : O :=
  let b := Module.Free.chooseBasis R O
  ∑ i, μ ((linearContinuousMap (b.coord i)).comp f) • b i

omit [IsTopologicalRing O] in
private theorem map_scalarExtendVal (φ : O →ₗ[R] R) (μ : D(X, R)) (f : C(X, O)) :
    φ (scalarExtendVal O μ f) = μ ((linearContinuousMap φ).comp f) := by
  let b := Module.Free.chooseBasis R O
  have hfun : (linearContinuousMap φ).comp f =
      ∑ i, φ (b i) • (linearContinuousMap (b.coord i)).comp f := by
    ext x
    simp only [comp_apply, linearContinuousMap_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, b.coord_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr (f x)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [scalarExtendVal, map_sum, hfun, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

private def scalarExtendCLM (μ : D(X, R)) : C(X, O) →L[O] O where
  toFun := scalarExtendVal O μ
  map_add' f g :=
    let b := Module.Free.chooseBasis R O
    b.repr.injective <| by
      ext i
      have hcomp : (linearContinuousMap (b.coord i)).comp (f + g) =
          (linearContinuousMap (b.coord i)).comp f +
            (linearContinuousMap (b.coord i)).comp g := by
        ext x
        simp
      simp [← b.coord_apply, map_scalarExtendVal, hcomp]
  map_smul' a f :=
    let b := Module.Free.chooseBasis R O
    b.repr.injective <| by
      ext i
      let ψ : O →ₗ[R] R := (b.coord i).comp (LinearMap.mulLeft R a)
      have hcomp : (linearContinuousMap (b.coord i)).comp (a • f) =
          (linearContinuousMap ψ).comp f := by
        ext x
        rfl
      rw [RingHom.id_apply, ← b.coord_apply, ← b.coord_apply, map_scalarExtendVal, hcomp]
      exact (map_scalarExtendVal O ψ μ f).symm
  cont :=
    let b := Module.Free.chooseBasis R O
    continuous_finsetSum _ fun i _ ↦
      (μ.continuous.comp (continuous_postcomp (linearContinuousMap (b.coord i)))).smul
        continuous_const

@[simp]
private theorem scalarExtendCLM_apply (μ : D(X, R)) (f : C(X, O)) :
    scalarExtendCLM O μ f = scalarExtendVal O μ f :=
  (rfl)

/-- **Scalar extension of measures.** When `O` is finite and free over `R` and carries the
`R`-module topology, `scalarExtend O` extends every `μ ∈ D(X, R)` to the `O`-valued measure
characterised by `φ (scalarExtend O μ f) = μ (φ ∘ f)` for all `φ : O →ₗ[R] R`
(`map_scalarExtend_apply`). -/
def scalarExtend : D(X, R) →+ D(X, O) where
  toFun μ := toCLMEquiv.symm (scalarExtendCLM O μ)
  map_zero' := ext fun _ ↦ by simp [scalarExtendVal]
  map_add' _ _ := ext fun _ ↦ by simp [scalarExtendVal, add_smul, Finset.sum_add_distrib]

variable {O}

private theorem scalarExtend_apply_val (μ : D(X, R)) (f : C(X, O)) :
    scalarExtend O μ f = scalarExtendVal O μ f := by
  simp [scalarExtend]

/-- **Basis-free characterisation of `scalarExtend`.** Every `R`-linear functional `φ : O →ₗ[R] R`
commutes with integration against `scalarExtend O μ`. -/
@[simp]
theorem map_scalarExtend_apply (φ : O →ₗ[R] R) (μ : D(X, R)) (f : C(X, O)) :
    φ (scalarExtend O μ f) =
      μ ((⟨φ, IsModuleTopology.continuous_of_linearMap φ⟩ : C(O, R)).comp f) := by
  rw [scalarExtend_apply_val]
  exact map_scalarExtendVal O φ μ f

/-- Along any finite `R`-basis `b` of `O`, `scalarExtend O μ f` expands as the sum of the integrals
of the `b`-coordinates of `f` against `μ`. -/
theorem scalarExtend_apply_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (μ : D(X, R)) (f : C(X, O)) :
    scalarExtend O μ f =
      ∑ i, μ ((⟨b.coord i, IsModuleTopology.continuous_of_linearMap (b.coord i)⟩ :
        C(O, R)).comp f) • b i := by
  conv_lhs => rw [← b.sum_repr (scalarExtend O μ f)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← b.coord_apply, map_scalarExtend_apply]

/-- On an `R`-valued test function pushed into `O` via `algebraMap R O`, `scalarExtend O μ`
evaluates to `algebraMap R O (μ g)`. -/
@[simp]
theorem scalarExtend_apply_comp_algebraMap (μ : D(X, R)) (g : C(X, R)) :
    scalarExtend O μ ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp g) =
      algebraMap R O (μ g) := by
  let b := Module.Free.chooseBasis R O
  apply b.repr.injective
  ext i
  have hcomp :
      (⟨b.coord i, IsModuleTopology.continuous_of_linearMap (b.coord i)⟩ : C(O, R)).comp
        ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp g) = b.coord i 1 • g := by
    ext x
    rw [comp_apply, comp_apply, ContinuousMap.coe_mk, ContinuousMap.coe_mk,
      Algebra.algebraMap_eq_smul_one, map_smul, ContinuousMap.smul_apply, smul_eq_mul,
      smul_eq_mul, mul_comm]
  rw [← b.coord_apply, ← b.coord_apply, map_scalarExtend_apply, hcomp, map_smul, smul_eq_mul,
    Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

/-- `scalarExtend O` intertwines `R`-scalar multiplication with `algebraMap R O`. -/
theorem scalarExtend_smul (r : R) (μ : D(X, R)) :
    scalarExtend O (r • μ) = algebraMap R O r • scalarExtend O μ := by
  let b := Module.Free.chooseBasis R O
  ext f
  apply b.repr.injective
  ext i
  simp only [← b.coord_apply, map_scalarExtend_apply, _root_.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def, map_smul, map_scalarExtend_apply, smul_eq_mul]

/-- `scalarExtend O` maps `dirac R x` to `dirac O x`. -/
@[simp]
theorem scalarExtend_dirac (x : X) :
    scalarExtend O (dirac R x) = dirac O x := by
  let b := Module.Free.chooseBasis R O
  ext f
  simp [scalarExtend_apply_eq_sum_basis b, b.coord_apply]

/-- `scalarExtend O` commutes with pushforward along continuous maps. -/
@[simp]
theorem scalarExtend_map (q : C(X, Y)) (μ : D(X, R)) :
    scalarExtend O (map q μ) = map q (scalarExtend O μ) := by
  let b := Module.Free.chooseBasis R O
  ext f
  simp [scalarExtend_apply_eq_sum_basis b, ContinuousMap.comp_assoc]

/-- Finite projections of `scalarExtend O μ` are obtained by applying `algebraMap R O` to the
coefficients of `μ`. -/
@[simp]
theorem finiteProjection_scalarExtend [Finite A] [DiscreteTopology A] (q : C(X, A)) (μ : D(X, R)) :
    finiteProjection q (scalarExtend O μ) =
      (finiteProjection q μ).mapRange (algebraMap R O) (map_zero _) := by
  classical
  ext a
  rw [finiteProjection_apply, Finsupp.mapRange_apply, finiteProjection_apply,
    ← scalarExtend_apply_comp_algebraMap]
  congr 1
  ext x
  by_cases hx : q x = a <;> simp [fiberIndicator_apply, hx]

/-- Applying `mapAdd φ` to `a • scalarExtend O μ` recovers `φ a • μ`. -/
@[simp]
theorem mapAdd_smul_scalarExtend (φ : O →ₗ[R] R) (a : O) (μ : D(X, R)) :
    mapAdd φ (a • scalarExtend O μ) = φ a • μ := by
  ext g
  rw [mapAdd_apply, _root_.smul_apply, scalarExtend_apply_comp_algebraMap, _root_.smul_apply,
    smul_eq_mul, mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm, ← smul_eq_mul]

/-- Every `O`-valued measure `ν` decomposes along a finite `R`-basis `b` of `O` into the
`b`-coordinate measures `mapAdd (b.coord i) ν`. -/
theorem sum_basis_smul_scalarExtend_mapAdd {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (ν : D(X, O)) :
    ∑ i, b i • scalarExtend O (mapAdd (b.coord i) ν) = ν := by
  ext f
  have hf : f = ∑ j, b j • (algebraMapContinuousMap R O).comp
      ((linearContinuousMap (b.coord j)).comp f) := by
    ext x
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, comp_apply,
      algebraMapContinuousMap_apply, linearContinuousMap_apply, smul_eq_mul, mul_comm (b _),
      ← Algebra.smul_def, b.coord_apply]
    exact (b.sum_repr (f x)).symm
  have hcomm : ∀ (i j : ι) (r : R), b i * (r • b j) = b j * (r • b i) := fun i j r ↦ by
    simp only [Algebra.smul_def]
    ring
  calc
    (∑ i, b i • scalarExtend O (mapAdd (b.coord i) ν)) f
        = ∑ i, ∑ j, b i *
            (mapAdd (b.coord i) ν ((linearContinuousMap (b.coord j)).comp f) • b j) := by
          rw [sum_measure_apply]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [_root_.smul_apply, smul_eq_mul, scalarExtend_apply_eq_sum_basis b, Finset.mul_sum]
          rfl
    _ = ∑ j, ∑ i, b j * (b.coord i (ν ((algebraMapContinuousMap R O).comp
          ((linearContinuousMap (b.coord j)).comp f))) • b i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hcomm, mapAdd_apply]
          rfl
    _ = ∑ j, b j * ν ((algebraMapContinuousMap R O).comp
          ((linearContinuousMap (b.coord j)).comp f)) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← Finset.mul_sum]
          congr 1
          simp [b.coord_apply]
    _ = ν f := by
          conv_rhs => rw [hf]
          simp [map_sum]

end ScalarExtend

section BaseChange

variable (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Free R O] [Module.Finite R O]

/-- The canonical `O`-linear map `O ⊗[R] D(X, R) →ₗ[O] D(X, O)` sending `a ⊗ₜ μ` to
`a • scalarExtend O μ`. -/
private def baseChangeLinearMap : O ⊗[R] D(X, R) →ₗ[O] D(X, O) := by
  letI : Module R D(X, O) := Module.compHom D(X, O) (algebraMap R O)
  have hsmul : ∀ (r : R) (ν : D(X, O)), r • ν = algebraMap R O r • ν := fun _ _ ↦ rfl
  let bil : O →ₗ[R] D(X, R) →ₗ[R] D(X, O) :=
    { toFun a :=
        { toFun μ := a • scalarExtend O μ
          map_add' μ₁ μ₂ := by rw [map_add, smul_add]
          map_smul' r μ := by
            rw [scalarExtend_smul, RingHom.id_apply, hsmul, smul_comm] }
      map_add' a₁ a₂ := LinearMap.ext fun μ ↦ add_smul a₁ a₂ (scalarExtend O μ)
      map_smul' r a := LinearMap.ext fun μ ↦ by
        rw [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
          LinearMap.coe_mk, AddHom.coe_mk, hsmul, Algebra.smul_def, mul_smul] }
  exact
    { toFun := TensorProduct.lift bil
      map_add' := map_add (TensorProduct.lift bil)
      map_smul' c z := by
        rw [RingHom.id_apply]
        induction z using TensorProduct.inductionOn with
        | tmul a μ =>
          simp [TensorProduct.smul_tmul', bil, mul_smul]
        | add u v hu hv =>
          rw [smul_add, map_add, map_add, smul_add, hu, hv] }

private theorem baseChangeLinearMap_tmul (a : O) (μ : D(X, R)) :
    baseChangeLinearMap O (a ⊗ₜ[R] μ) = a • scalarExtend O μ :=
  (rfl)

/-- **Finite free base change of abstract measures.** When `O` is finite and free over `R` and
carries the `R`-module topology, `O ⊗[R] D(X, R)` is canonically isomorphic to `D(X, O)` as an
`O`-module via `a ⊗ₜ μ ↦ a • scalarExtend O μ`. -/
def baseChange : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O) :=
  let b := Module.Free.chooseBasis R O
  LinearEquiv.ofBijective (baseChangeLinearMap O) <| by
    let inv (ν : D(X, O)) : O ⊗[R] D(X, R) := ∑ i, b i ⊗ₜ[R] mapAdd (b.coord i) ν
    have hleft : ∀ z : O ⊗[R] D(X, R), inv (baseChangeLinearMap O z) = z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a μ =>
        simp only [inv, baseChangeLinearMap_tmul, mapAdd_smul_scalarExtend,
          ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.coord_apply]
        rw [b.sum_repr]
      | add u v hu hv =>
        dsimp only [inv]
        rw [map_add]
        simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
        exact congrArg₂ (· + ·) hu hv
    refine ⟨Function.HasLeftInverse.injective ⟨inv, hleft⟩, fun ν ↦ ⟨inv ν, ?_⟩⟩
    simpa [inv, map_sum, baseChangeLinearMap_tmul] using sum_basis_smul_scalarExtend_mapAdd b ν

variable {O}

/-- On a pure tensor `a ⊗ₜ μ`, `baseChange O` evaluates to `a • scalarExtend O μ`. -/
@[simp]
theorem baseChange_tmul (a : O) (μ : D(X, R)) :
    baseChange O (a ⊗ₜ[R] μ) = a • scalarExtend O μ :=
  (rfl)

/-- On `a ⊗ₜ dirac R x`, `baseChange O` produces `a • dirac O x`. -/
theorem baseChange_tmul_dirac (a : O) (x : X) :
    baseChange O (a ⊗ₜ[R] dirac R x) = a • dirac O x := by
  simp

/-- Along any finite `R`-basis `b` of `O`, `(baseChange O).symm` decomposes `ν ∈ D(X, O)` into its
coordinate measures `mapAdd (b.coord i) ν`. -/
theorem baseChange_symm_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (ν : D(X, O)) :
    (baseChange O).symm ν = ∑ i, b i ⊗ₜ[R] mapAdd (b.coord i) ν := by
  apply (baseChange O).injective
  rw [LinearEquiv.apply_symm_apply, map_sum]
  simpa using (sum_basis_smul_scalarExtend_mapAdd b ν).symm

end BaseChange

end TopologicalSpace

section Monoid

variable {G R : Type*} [TopologicalSpace G] [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Free R O] [Module.Finite R O]

omit [ContinuousMul G] [LocallyCompactSpace G] in
variable {O} in
/-- `scalarExtend O` preserves the convolution identity `1 = dirac · 1`. -/
@[simp]
theorem scalarExtend_one : scalarExtend O (1 : D(G, R)) = 1 := by
  simp [one_def]

variable {O} in
/-- `scalarExtend O` preserves convolution of measures on any locally compact topological monoid. -/
@[simp]
theorem scalarExtend_mul (μ ν : D(G, R)) :
    scalarExtend O (μ * ν) = scalarExtend O μ * scalarExtend O ν := by
  let b := Module.Free.chooseBasis R O
  ext f
  apply b.repr.injective
  ext i
  rw [← b.coord_apply, ← b.coord_apply, map_scalarExtend_apply, mul_apply, mul_apply,
    map_scalarExtend_apply]
  congr 1
  ext x
  simp only [comp_apply, convolveFunRight_apply]
  exact (map_scalarExtend_apply (b.coord i) ν ⟨fun y ↦ f (x * y), by fun_prop⟩).symm

/-- `scalarExtend O` bundled as a ring homomorphism of convolution algebras. -/
def scalarExtendRingHom : D(G, R) →+* D(G, O) :=
  { scalarExtend O with
    map_one' := scalarExtend_one
    map_mul' := scalarExtend_mul }

variable {O} in
@[simp]
theorem coe_scalarExtendRingHom : ⇑(scalarExtendRingHom (G := G) (R := R) O) = scalarExtend O :=
  (rfl)

variable {O} in
/-- `baseChange O` preserves the multiplicative identity `1`. -/
@[simp]
theorem baseChange_one : baseChange O (1 : O ⊗[R] D(G, R)) = 1 := by
  rw [Algebra.TensorProduct.one_def, baseChange_tmul, scalarExtend_one, one_smul]

variable {O} in
/-- `baseChange O` preserves the convolution product on `O ⊗[R] D(G, R)`. -/
@[simp]
theorem baseChange_mul (u v : O ⊗[R] D(G, R)) :
    baseChange O (u * v) = baseChange O u * baseChange O v := by
  induction u using TensorProduct.inductionOn with
  | tmul a μ =>
    induction v using TensorProduct.inductionOn with
    | tmul c ν =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, baseChange_tmul, baseChange_tmul, baseChange_tmul,
        scalarExtend_mul, smul_mul_smul_comm]
    | add v₁ v₂ hv₁ hv₂ =>
      rw [mul_add, map_add, hv₁, hv₂, map_add, mul_add]
  | add u₁ u₂ hu₁ hu₂ =>
    rw [add_mul, map_add, hu₁, hu₂, map_add, add_mul]

/-- **Finite free base change of convolution algebras.** On any locally compact topological monoid
`G` with continuous multiplication, `O ⊗[R] D(G, R)` is canonically isomorphic to `D(G, O)` as an
`O`-algebra. -/
def baseChangeAlgEquiv : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O) :=
  AlgEquiv.ofLinearEquiv (baseChange O) baseChange_one baseChange_mul

variable {O}

@[simp]
theorem coe_baseChangeAlgEquiv :
    ⇑(baseChangeAlgEquiv (G := G) (R := R) O) = baseChange O :=
  (rfl)

@[simp]
theorem baseChangeAlgEquiv_tmul (a : O) (μ : D(G, R)) :
    baseChangeAlgEquiv O (a ⊗ₜ[R] μ) = a • scalarExtend O μ :=
  (rfl)

theorem baseChangeAlgEquiv_tmul_dirac (a : O) (x : G) :
    baseChangeAlgEquiv O (a ⊗ₜ[R] dirac R x) = a • dirac O x :=
  baseChange_tmul_dirac a x

@[simp]
theorem coe_baseChangeAlgEquiv_symm :
    ⇑(baseChangeAlgEquiv (G := G) (R := R) O).symm = (baseChange O).symm :=
  (rfl)

end Monoid

section CompletedGroupAlgebraComparison

variable {Γ R : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [ContinuousMul Γ]
  [LocallyCompactSpace Γ] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O]

/-- `toCompletedGroupAlgebra` intertwines `mapAdd φ` on measures with
`completedGroupAlgebra.mapAddMonoidHom` on the completed group algebra. -/
@[simp]
theorem toCompletedGroupAlgebra_mapAdd (φ : O →ₗ[R] R) (ν : D(Γ, O)) :
    toCompletedGroupAlgebra (mapAdd φ ν) =
      completedGroupAlgebra.mapAddMonoidHom Γ φ.toAddMonoidHom (toCompletedGroupAlgebra ν) := by
  ext U : 1
  apply MonoidAlgebra.coeff_injective
  ext g
  simp

section FiniteFree

variable [Module.Free R O] [Module.Finite R O]

/-- `toCompletedGroupAlgebra` intertwines `scalarExtend O` on measures with
`completedGroupAlgebra.mapRingHom Γ (algebraMap R O)`. -/
@[simp]
theorem toCompletedGroupAlgebra_scalarExtend (μ : D(Γ, R)) :
    toCompletedGroupAlgebra (scalarExtend O μ) =
      completedGroupAlgebra.mapRingHom Γ (algebraMap R O) (toCompletedGroupAlgebra μ) := by
  ext U : 1
  apply MonoidAlgebra.coeff_injective
  ext g
  simp

/-- **Compatibility of measure base change with `completedGroupAlgebra.baseChange`.** The diagram
relating `O ⊗[R] D(Γ, R) → D(Γ, O)` and `O ⊗[R] R[[Γ]] → O[[Γ]]` via `toCompletedGroupAlgebra`
commutes. -/
theorem toCompletedGroupAlgebra_baseChange (z : O ⊗[R] D(Γ, R)) :
    toCompletedGroupAlgebra (baseChange O z) =
      completedGroupAlgebra.baseChange R O Γ
        (Algebra.TensorProduct.map (AlgHom.id O O) toCompletedGroupAlgebra z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a μ =>
    simp
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv, ← map_add, ← map_add]

end FiniteFree

end CompletedGroupAlgebraComparison

section ExtendCoefficients

variable {X R O K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O] [IsModuleTopology R O]
  [Module.Free R O] [Module.Finite R O] [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Extending coefficients of `scalarExtend O μ` along `j : O →+* K` agrees with extending `μ`
directly along `j.comp (algebraMap R O)`. -/
@[simp]
theorem extendCoefficients_scalarExtend (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (μ : D(X, R)) :
    extendCoefficients j hj (scalarExtend O μ) =
      extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ :=
  finiteProjection_ext _ _ fun q ↦ by
    ext a
    simp

/-- **Compatibility of `extendCoefficients` with `baseChange`.** Extending a pure tensor `a ⊗ₜ μ`
along `j : O →+* K` scales the extension of `μ` along `j ∘ algebraMap R O` by `j a`. -/
theorem extendCoefficients_baseChange_tmul (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O)
    (μ : D(X, R)) :
    extendCoefficients j hj (baseChange O (a ⊗ₜ[R] μ)) =
      j a • extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ := by
  rw [baseChange_tmul, extendCoefficients_smul, extendCoefficients_scalarExtend]

/-- Along any finite `R`-basis `b` of `O`, `extendCoefficients j hj ν` expands into the extensions
of the coordinate measures `mapAdd (b.coord i) ν`. -/
theorem extendCoefficients_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (ν : D(X, O)) :
    extendCoefficients j hj ν =
      ∑ i, j (b i) • extendCoefficients (j.comp (algebraMap R O))
        (fun r ↦ hj (algebraMap R O r)) (mapAdd (b.coord i) ν) := by
  conv_lhs => rw [← sum_basis_smul_scalarExtend_mapAdd b ν]
  simp [map_sum]

end ExtendCoefficients

end ModuleTopology

/-! ### Specialisation over `ℤ_[p]` -/

section PadicInt

variable {p : ℕ} [Fact p.Prime]

section TopologicalSpace

variable {X : Type*} [TopologicalSpace X] (O : Type*) [CommRing O] [TopologicalSpace O]
  [IsTopologicalRing O] [T2Space O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
  [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]

/-- **Finite free `ℤ_[p]`-base change of measures.** For any Hausdorff topological `ℤ_[p]`-algebra
`O` with continuous `ℤ_[p]`-scalar action that is finite and free over `ℤ_[p]` (in particular any
such `NormedCommRing`), `O ⊗[ℤ_[p]] D(X, ℤ_[p])` is canonically isomorphic to `D(X, O)` as an
`O`-module. -/
def completedGroupAlgebraBaseChange : O ⊗[ℤ_[p]] D(X, ℤ_[p]) ≃ₗ[O] D(X, O) :=
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  baseChange O

variable {O}

private theorem completedGroupAlgebraBaseChange_tmul [IsModuleTopology ℤ_[p] O]
    (a : O) (μ : D(X, ℤ_[p])) :
    completedGroupAlgebraBaseChange O (a ⊗ₜ[ℤ_[p]] μ) = a • scalarExtend O μ :=
  (rfl)

/-- On `a ⊗ₜ dirac ℤ_[p] x`, `completedGroupAlgebraBaseChange O` evaluates to `a • dirac O x`. -/
@[simp]
theorem completedGroupAlgebraBaseChange_tmul_dirac (a : O) (x : X) :
    completedGroupAlgebraBaseChange O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = a • dirac O x := by
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  exact baseChange_tmul_dirac a x

end TopologicalSpace

section Monoid

variable {G : Type*} [TopologicalSpace G] [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]
  (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]

variable {O} in
/-- `completedGroupAlgebraBaseChange O` preserves the convolution identity `1`. -/
@[simp]
theorem completedGroupAlgebraBaseChange_one :
    completedGroupAlgebraBaseChange O (1 : O ⊗[ℤ_[p]] D(G, ℤ_[p])) = 1 := by
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  exact baseChange_one

variable {O} in
/-- `completedGroupAlgebraBaseChange O` preserves the convolution product. -/
@[simp]
theorem completedGroupAlgebraBaseChange_mul (u v : O ⊗[ℤ_[p]] D(G, ℤ_[p])) :
    completedGroupAlgebraBaseChange O (u * v) =
      completedGroupAlgebraBaseChange O u * completedGroupAlgebraBaseChange O v := by
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  exact baseChange_mul u v

/-- **Finite free `ℤ_[p]`-base change of convolution algebras.** The canonical `O`-algebra
isomorphism `O ⊗[ℤ_[p]] D(G, ℤ_[p]) ≃ₐ[O] D(G, O)`. -/
def completedGroupAlgebraBaseChangeAlgEquiv : O ⊗[ℤ_[p]] D(G, ℤ_[p]) ≃ₐ[O] D(G, O) :=
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  baseChangeAlgEquiv O

variable {O}

@[simp]
theorem coe_completedGroupAlgebraBaseChangeAlgEquiv :
    ⇑(completedGroupAlgebraBaseChangeAlgEquiv (G := G) (p := p) O) =
      completedGroupAlgebraBaseChange O :=
  (rfl)

@[simp]
theorem completedGroupAlgebraBaseChangeAlgEquiv_tmul_dirac (a : O) (x : G) :
    completedGroupAlgebraBaseChangeAlgEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = a • dirac O x :=
  completedGroupAlgebraBaseChange_tmul_dirac a x

/-- Existence of an `O`-algebra isomorphism `O ⊗[ℤ_[p]] D(G, ℤ_[p]) ≃ₐ[O] D(G, O)` sending
`a ⊗ₜ dirac ℤ_[p] x` to `a • dirac O x` for any normed `ℤ_[p]`-algebra `O` that is finite and free
over `ℤ_[p]` with continuous scalar action. -/
theorem exists_baseChange_algEquiv (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O]
    [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    ∃ e : O ⊗[ℤ_[p]] D(G, ℤ_[p]) ≃ₐ[O] D(G, O),
      ∀ (a : O) (x : G), e (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = a • dirac O x :=
  ⟨completedGroupAlgebraBaseChangeAlgEquiv O, completedGroupAlgebraBaseChangeAlgEquiv_tmul_dirac⟩

end Monoid

section ProfiniteGroup

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ]

section TopologicalRing

omit [TotallyDisconnectedSpace Γ] in
/-- `toCompletedGroupAlgebra` intertwines `completedGroupAlgebraBaseChange O` with
`completedGroupAlgebra.baseChange ℤ_[p] O Γ`. -/
theorem toCompletedGroupAlgebra_completedGroupAlgebraBaseChange
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (z : O ⊗[ℤ_[p]] D(Γ, ℤ_[p])) :
    toCompletedGroupAlgebra (completedGroupAlgebraBaseChange O z) =
      completedGroupAlgebra.baseChange ℤ_[p] O Γ
        (Algebra.TensorProduct.map (AlgHom.id O O) toCompletedGroupAlgebra z) := by
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  exact toCompletedGroupAlgebra_baseChange z

/-- **Bijectivity of `toCompletedGroupAlgebra` over finite free `ℤ_[p]`-algebras.** On a profinite
group `Γ`, `toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is bijective whenever `O` is Hausdorff,
finite and free over `ℤ_[p]`, and has continuous `ℤ_[p]`-scalar multiplication. -/
theorem toCompletedGroupAlgebra_bijective_of_finiteFree (p : ℕ) [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    Function.Bijective (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  refine ⟨toCompletedGroupAlgebra_injective, fun y ↦ ?_⟩
  let eTensor : O ⊗[ℤ_[p]] D(Γ, ℤ_[p]) ≃ₐ[O] O ⊗[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ :=
    Algebra.TensorProduct.congr AlgEquiv.refl completedGroupAlgebraEquiv
  let z := eTensor.symm ((completedGroupAlgebra.baseChange ℤ_[p] O Γ).symm y)
  refine ⟨completedGroupAlgebraBaseChange O z, ?_⟩
  rw [toCompletedGroupAlgebra_completedGroupAlgebraBaseChange]
  have hmap : Algebra.TensorProduct.map (AlgHom.id O O) toCompletedGroupAlgebra z = eTensor z := by
    induction z using TensorProduct.inductionOn with
    | tmul a μ => simp [eTensor]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  rw [hmap]
  simp [z]

/-- **Measures over a finite free `ℤ_[p]`-algebra are the completed group algebra.** The canonical
`O`-algebra equivalence `D(Γ, O) ≃ₐ[O] O[[Γ]]` on a profinite group `Γ`. -/
def completedGroupAlgebraEquivOfFiniteFree (p : ℕ) [Fact p.Prime]
    (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective toCompletedGroupAlgebra (toCompletedGroupAlgebra_bijective_of_finiteFree p)

@[simp]
theorem completedGroupAlgebraEquivOfFiniteFree_apply
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (ν : D(Γ, O)) :
    completedGroupAlgebraEquivOfFiniteFree p O ν = toCompletedGroupAlgebra ν :=
  AlgEquiv.ofBijective_apply _ _ _

/-- `completedGroupAlgebraEquivOfFiniteFree p O` maps `dirac O γ` to
`completedGroupAlgebra.of O Γ γ`. -/
theorem completedGroupAlgebraEquivOfFiniteFree_dirac
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (γ : Γ) :
    completedGroupAlgebraEquivOfFiniteFree p O (dirac O γ) = completedGroupAlgebra.of O Γ γ := by
  simp

/-- Along a finite `ℤ_[p]`-basis `b` of `O`, `(completedGroupAlgebraEquivOfFiniteFree p O).symm y`
reconstructs the measure from the integral coordinate measures attached to
`completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y`. -/
theorem completedGroupAlgebraEquivOfFiniteFree_symm_eq_sum_basis {ι O : Type*} [Fintype ι]
    [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O] [Algebra ℤ_[p] O]
    [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (b : Module.Basis ι ℤ_[p] O) (y : completedGroupAlgebra O Γ) :
    (completedGroupAlgebraEquivOfFiniteFree p O).symm y =
      ∑ i, completedGroupAlgebraBaseChange O (b i ⊗ₜ[ℤ_[p]]
        completedGroupAlgebraEquiv.symm
          (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) := by
  apply (completedGroupAlgebraEquivOfFiniteFree p O).injective
  rw [AlgEquiv.apply_symm_apply, completedGroupAlgebraEquivOfFiniteFree_apply]
  have h := completedGroupAlgebra.baseChange_symm_eq_sum_basis b y
  apply (completedGroupAlgebra.baseChange ℤ_[p] O Γ).symm.injective
  rw [h, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [toCompletedGroupAlgebra_completedGroupAlgebraBaseChange, Algebra.TensorProduct.map_tmul,
    AlgHom.coe_id, id_eq]
  have heq : toCompletedGroupAlgebra (completedGroupAlgebraEquiv.symm
      (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) =
      completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y := by
    rw [← completedGroupAlgebraEquiv_apply, AlgEquiv.apply_symm_apply]
  rw [heq, AlgEquiv.symm_apply_apply]

end TopologicalRing

section Normed

/-- **Homeomorphism with `O[[Γ]]` in the weak topology.** For a profinite group `Γ` and a normed
commutative `ℤ_[p]`-algebra `O` that is finite and free over `ℤ_[p]` with continuous `ℤ_[p]`-scalar
action, `toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is a homeomorphism from the weak topology
on measures to the inverse-limit topology on `O[[Γ]]`. -/
theorem isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree (p : ℕ) [Fact p.Prime]
    {O : Type*} [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := O) (E := O)) _
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  let b := Module.Free.chooseBasis ℤ_[p] O
  let τO : TopologicalSpace D(Γ, O) := WeakTopology (X := Γ) (R := O) (E := O)
  let τZ : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology (X := Γ) (R := ℤ_[p]) (E := ℤ_[p])
  let hHomeoZ := (isHomeomorph_toCompletedGroupAlgebra_weak (Γ := Γ) (p := p)).homeomorph _
  have hsymmZ : ∀ x : completedGroupAlgebra ℤ_[p] Γ,
      completedGroupAlgebraEquiv.symm x = hHomeoZ.symm x := fun x ↦
    toCompletedGroupAlgebra_injective <| by
      have h1 : toCompletedGroupAlgebra (completedGroupAlgebraEquiv.symm x) = x := by
        rw [← completedGroupAlgebraEquiv_apply, AlgEquiv.apply_symm_apply]
      have h2 : toCompletedGroupAlgebra (hHomeoZ.symm x) = x :=
        hHomeoZ.apply_symm_apply x
      exact h1.trans h2.symm
  have hcont_inv : @Continuous (completedGroupAlgebra O Γ) D(Γ, O) _ τO
      (completedGroupAlgebraEquivOfFiniteFree p O).symm := by
    let : TopologicalSpace D(Γ, O) := τO
    let : TopologicalSpace D(Γ, ℤ_[p]) := τZ
    rw [continuous_induced_rng, continuous_pi_iff]
    intro f
    simp_rw [Function.comp_apply, completedGroupAlgebraEquivOfFiniteFree_symm_eq_sum_basis b,
      sum_measure_apply, completedGroupAlgebraBaseChange_tmul, _root_.smul_apply]
    refine continuous_finsetSum _ fun i _ ↦ ?_
    simp_rw [scalarExtend_apply_eq_sum_basis b, hsymmZ]
    refine (continuous_const (y := b i)).smul (continuous_finsetSum _ fun j _ ↦ ?_)
    have hcoord : Continuous (completedGroupAlgebra.mapAddMonoidHom Γ
        (b.coord i).toAddMonoidHom) :=
      completedGroupAlgebra.continuous_mapAddMonoidHom
        (IsModuleTopology.continuous_of_linearMap (b.coord i))
    have heval : Continuous fun μ : D(Γ, ℤ_[p]) ↦
        μ ((⟨b.coord j, IsModuleTopology.continuous_of_linearMap (b.coord j)⟩ :
          C(O, ℤ_[p])).comp f) :=
      (continuous_apply _).comp continuous_induced_dom
    exact (heval.comp (hHomeoZ.symm.continuous.comp hcoord)).smul continuous_const
  let : TopologicalSpace D(Γ, O) := τO
  exact
    { continuous := continuous_toCompletedGroupAlgebra
      isOpenMap := Homeomorph.isOpenMap
        { toEquiv := (completedGroupAlgebraEquivOfFiniteFree p O).toEquiv
          continuous_toFun := continuous_toCompletedGroupAlgebra
          continuous_invFun := hcont_inv }
      bijective := toCompletedGroupAlgebra_bijective_of_finiteFree p }

/-- `O`-valued measures on a profinite group form a topological ring for convolution and the weak
topology when `O` is finite and free over `ℤ_[p]` with continuous scalar action. -/
theorem isTopologicalRing_measures_weak_of_finiteFree (p : ℕ) [Fact p.Prime]
    {O : Type*} [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @IsTopologicalRing D(Γ, O) (WeakTopology (X := Γ) (R := O) (E := O)) _ := by
  let : TopologicalSpace D(Γ, O) := WeakTopology
  have h := (isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree p
    (Γ := Γ) (O := O)).isEmbedding.isInducing
  let : IsTopologicalAddGroup D(Γ, O) :=
    h.isTopologicalAddGroup (toCompletedGroupAlgebra (Γ := Γ) (R := O)).toAddMonoidHom
  let : ContinuousMul D(Γ, O) :=
    h.continuousMul (toCompletedGroupAlgebra (Γ := Γ) (R := O))
  exact
    { continuous_add := continuous_add
      continuous_mul := continuous_mul
      continuous_neg := continuous_neg }

/-- **Weak compactness of `O`-valued measures.** On a profinite group `Γ`, `D(Γ, O)` is compact in
the weak topology whenever `O` is a normed commutative `ℤ_[p]`-algebra finite and free over `ℤ_[p]`
with continuous `ℤ_[p]`-scalar action. -/
theorem compactSpace_measures_weak_of_finiteFree (p : ℕ) [Fact p.Prime]
    {O : Type*} [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @CompactSpace D(Γ, O) (WeakTopology (X := Γ) (R := O) (E := O)) := by
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  have : CompactSpace O := by
    rw [eq_moduleTopology ℤ_[p] O]
    exact TauCeti.compactSpace_moduleTopology (A := ℤ_[p]) (M := O)
  let : TopologicalSpace D(Γ, O) := WeakTopology
  exact ((isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree p
    (Γ := Γ) (O := O)).homeomorph _).symm.compactSpace

end Normed

end ProfiniteGroup

section ExtendAndAmice

variable {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]

/-- **Compatibility of `extendCoefficients` with `completedGroupAlgebraBaseChange`.** Extending a
pure tensor `a ⊗ₜ μ ∈ O ⊗[ℤ_[p]] D(X, ℤ_[p])` along `j : O →+* K` scales the extension of `μ` along
`j ∘ algebraMap ℤ_[p] O` by `j a`. -/
@[simp]
theorem extendCoefficients_completedGroupAlgebraBaseChange_tmul {X K : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (μ : D(X, ℤ_[p])) :
    extendCoefficients j hj (completedGroupAlgebraBaseChange O (a ⊗ₜ[ℤ_[p]] μ)) =
      j a • extendCoefficients (j.comp (algebraMap ℤ_[p] O))
        (fun r ↦ hj (algebraMap ℤ_[p] O r)) μ := by
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  exact extendCoefficients_baseChange_tmul j hj a μ

/-- **Compatibility of the Amice transform with `completedGroupAlgebraBaseChange`.** On `ℤ_[p]`,
the Amice transform of `completedGroupAlgebraBaseChange O (a ⊗ₜ μ)` is `a` times `μ.amiceTransform`
mapped along `algebraMap ℤ_[p] O`. -/
@[simp]
theorem amiceTransform_completedGroupAlgebraBaseChange_tmul (a : O) (μ : D(ℤ_[p], ℤ_[p])) :
    (completedGroupAlgebraBaseChange O (a ⊗ₜ[ℤ_[p]] μ)).amiceTransform =
      a • PowerSeries.map (algebraMap ℤ_[p] O) μ.amiceTransform := by
  have : IsModuleTopology ℤ_[p] O := IsModuleTopology.of_compactSpace ℤ_[p] O
  rw [completedGroupAlgebraBaseChange_tmul, map_smul]
  congr 1
  ext n
  rw [coeff_amiceTransform, PowerSeries.coeff_map, coeff_amiceTransform,
    ← scalarExtend_apply_comp_algebraMap]
  congr 1
  ext x
  simp [Algebra.algebraMap_eq_smul_one]

/-- Combining `completedGroupAlgebraBaseChange` with `extendCoefficients` along a continuous
`ℤ_[p]`-algebra homomorphism `j : O →ₐ[ℤ_[p]] K` into the unit ball maps the Amice transform of `μ`
along `algebraMap ℤ_[p] K` and scales by `j a`. -/
theorem amiceTransform_extendCoefficients_completedGroupAlgebraBaseChange_tmul {K : Type*}
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra ℤ_[p] K]
    [ContinuousSMul ℤ_[p] K] (j : O →ₐ[ℤ_[p]] K) (hjc : Continuous j) (hj : ∀ a, ‖j a‖ ≤ 1)
    (a : O) (μ : D(ℤ_[p], ℤ_[p])) :
    (extendCoefficients (j : O →+* K) hj
        (completedGroupAlgebraBaseChange O (a ⊗ₜ[ℤ_[p]] μ))).amiceTransform =
      j a • PowerSeries.map (algebraMap ℤ_[p] K) μ.amiceTransform := by
  rw [amiceTransform_extendCoefficients j hjc hj,
    amiceTransform_completedGroupAlgebraBaseChange_tmul]
  ext n
  simp [PowerSeries.coeff_map]

end ExtendAndAmice

end PadicInt

/-! ### Checks -/

section Checks

variable {p : ℕ} [Fact p.Prime]

-- Over `O = ℤ_[p]`, `completedGroupAlgebraBaseChange ℤ_[p]` is the canonical left unit.
example (X : Type*) [TopologicalSpace X] :
    completedGroupAlgebraBaseChange (X := X) ℤ_[p] = TensorProduct.lid ℤ_[p] D(X, ℤ_[p]) := by
  apply LinearEquiv.toLinearMap_inj.mp
  apply TensorProduct.ext'
  intro r μ
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, TensorProduct.lid_tmul,
    completedGroupAlgebraBaseChange_tmul]
  congr 1
  refine AbstractMeasure.ext fun f ↦ ?_
  have hf : ((⟨algebraMap ℤ_[p] ℤ_[p], continuous_algebraMap ℤ_[p] ℤ_[p]⟩ :
      C(ℤ_[p], ℤ_[p])).comp f) = f := by
    ext x
    simp
  conv_lhs => rw [← hf]
  exact scalarExtend_apply_comp_algebraMap (R := ℤ_[p]) (O := ℤ_[p]) μ f

-- `1 ⊗ₜ dirac ℤ_[p] x` maps to `dirac O x`.
example {X O : Type*} [TopologicalSpace X] [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [T2Space O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] (x : X) :
    completedGroupAlgebraBaseChange O ((1 : O) ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = dirac O x := by
  simp

-- Distinct scalars produce distinct measures on `a ⊗ₜ dirac ℤ_[p] x`.
example {X O : Type*} [TopologicalSpace X] [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [T2Space O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] {a b : O} (hab : a ≠ b) (x : X) :
    completedGroupAlgebraBaseChange O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) ≠
      completedGroupAlgebraBaseChange O (b ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) := by
  intro h
  have h1 := congrArg (fun ν : D(X, O) ↦ ν 1) h
  simp only [completedGroupAlgebraBaseChange_tmul_dirac, _root_.smul_apply,
    dirac_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one] at h1
  exact hab h1

-- Negative control for the topology hypothesis: if `(p ^ n : ℤ_[p]) • (1 : O)` fails to tend to
-- `0` (for instance when `O` carries an archimedean norm induced by an abstract field embedding
-- `ℚ_p → ℂ`), then `ContinuousSMul ℤ_[p] O` fails.
example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O]
    (h : ¬ Tendsto (fun n : ℕ ↦ ((p : ℤ_[p]) ^ n) • (1 : O)) atTop (𝓝 0)) :
    ¬ ContinuousSMul ℤ_[p] O := by
  intro hsmul
  apply h
  have hp : Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_pow, PadicInt.norm_p]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
  simpa using hp.smul_const (1 : O)

end Checks

end AbstractMeasure
