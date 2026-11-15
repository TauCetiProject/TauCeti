/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Monoid
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.Measure.Dirac
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.BaseChange
public import TauCeti.Topology.Algebra.Module.AutomaticContinuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.LinearAlgebra.Dual.FiniteProjective
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Finite projective base change of abstract measures

Let `X` be a topological space, `R` a topological commutative ring, and `O` a topological
commutative `R`-algebra that carries the `R`-module topology (`IsModuleTopology R O`) and is
finitely generated and projective over `R`. Every `R`-linear functional `O →ₗ[R] R` is then
continuous, so choosing a finite dual pair `(b_i, φ_i)` for `O` over `R` from
`TauCeti.exists_sum_dual_smul_eq` decomposes every continuous test function `F ∈ C(X, O)` as
`Σ_i b_i • (algebraMap R O ∘ φ_i ∘ F)`. Integrating each coordinate `φ_i ∘ F ∈ C(X, R)` against a
measure `μ ∈ D(X, R)` defines an `O`-valued measure `extendScalars R O μ ∈ D(X, O)`.

Although the construction uses a finite dual pair, the resulting measure is independent of that
choice: it is uniquely characterised by
`extendScalars R O μ (algebraMap R O ∘ f) = algebraMap R O (μ f)` for all `f ∈ C(X, R)`
(`extendScalars_apply_comp`, `eq_extendScalars_of_apply_comp`). Pushing `O`-valued measures back
along `φ_i` supplies the two-sided inverse to the induced map from `O ⊗[R] D(X, R)`, yielding an
`O`-linear isomorphism `baseChange R O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.

When `G` is a locally compact topological monoid, `extendScalars R O` respects Dirac units and
convolution (`extendScalars_one`, `extendScalars_mul`), upgrading `baseChange R O` to an `O`-algebra
isomorphism `baseChangeAlgEquiv R O : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)`. Over a compact base ring `R`
(such as `ℤ_[p]`), any Hausdorff `R`-algebra `O` with continuous `R`-scalar multiplication that is
finitely generated over `R` automatically carries the `R`-module topology
(`TauCeti.isModuleTopology_of_finite_of_compactSpace`), giving `exists_baseChange_algEquiv`.

Every hypothesis on `O` is necessary:
* `ContinuousSMul R O` / `IsModuleTopology R O` cannot be dropped: if `r_n → 0` in `R` while
  `r_n • (1 : O)` does not tend to `0` in `O` (for instance `R = ℤ_[p]` with its `p`-adic topology
  and `O = ℤ_[p]` equipped with an archimedean valuation `|σ(·)|_∞`), scalar multiplication is
  discontinuous and `R`-valued measures need not extend to `O`.
* `Module.Finite R O` cannot be dropped: for discrete `R = 𝔽_p`, discrete `O = 𝔽_p[T]`, and
  `X = ℤ_[p]`, elements of `O ⊗[R] D(X, R)` have bounded `T`-degree whereas `D(X, O)` contains
  measures whose clopen values have unbounded `T`-degree.
* `Module.Projective R O` cannot be dropped: for `R = 𝔽_p⟦x_0, x_1, …⟧` with the product topology,
  discrete `O = 𝔽_p`, and `X = ℤ_[p]`, `z = Σ_{n ≥ 1} x_n (δ_{p^n} - δ_0)` satisfies `1 ⊗ₜ z ≠ 0`
  in `O ⊗[R] D(X, R)` while mapping to `0` in `D(X, O)`.

On a compact group `Γ`, `baseChangeAlgEquiv` intertwines `toCompletedGroupAlgebra` with
`completedGroupAlgebra.scalarTensorEquiv`, transferring surjectivity, bijectivity, and the
weak-topology homeomorphism from `R` to `O`. On a profinite space `X`, `baseChange` also commutes
with `extendCoefficients` into the unit ball of a complete ultrametric field
(`extendCoefficients_baseChange_tmul`).

## Main definitions

* `AbstractMeasure.extendScalars`: the semilinear extension `D(X, R) →ₛₗ[algebraMap R O] D(X, O)`.
* `AbstractMeasure.mapCoeff`: the additive pushforward `D(X, O) →+ D(X, R)` along an `R`-linear
  functional `O →ₗ[R] R`.
* `AbstractMeasure.baseChange`: the `O`-linear isomorphism `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.
* `AbstractMeasure.extendScalarsRingHom`: `extendScalars` on a locally compact monoid as a ring
  homomorphism `D(G, R) →+* D(G, O)`.
* `AbstractMeasure.baseChangeAlgEquiv`: the `O`-algebra isomorphism
  `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` for convolution algebras on a locally compact monoid `G`.
* `AbstractMeasure.completedGroupAlgebraEquivOfBijective`: the `O`-algebra isomorphism
  `D(Γ, O) ≃ₐ[O] O[[Γ]]` transferred from bijectivity of `toCompletedGroupAlgebra` over `R`.

## Main results

* `AbstractMeasure.ext_comp_algebraMap`, `AbstractMeasure.ext_of_basis`: an `O`-valued measure is
  determined by its values on `(algebraMapCLM R O : C(R, O)).comp f` (`f ∈ C(X, R)`), or by its
  basis-coordinate measures in `D(X, R)`.
* `AbstractMeasure.extendScalars_apply_comp`, `AbstractMeasure.eq_extendScalars_of_apply_comp`,
  `AbstractMeasure.existsUnique_apply_comp_algebraMap`: defining evaluation and uniqueness of
  `extendScalars`.
* `AbstractMeasure.eq_sum_smul_extendScalars_of_basis`: expansion of any `ν ∈ D(X, O)` in terms of
  a finite `R`-basis of `O` and `mapCoeff`.
* `AbstractMeasure.exists_baseChange_algEquiv`: existence of the convolution `O`-algebra base
  change isomorphism over a compact base ring `R` for Hausdorff `O` with `ContinuousSMul R O`.
* `AbstractMeasure.toCompletedGroupAlgebra_surjective_of_surjective`,
  `AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak_of_isHomeomorph`: transfer of
  surjectivity and weak-topology homeomorphism for `toCompletedGroupAlgebra`.
* `AbstractMeasure.extendCoefficients_extendScalars`,
  `AbstractMeasure.extendCoefficients_baseChange_tmul`,
  `AbstractMeasure.extendCoefficients_eq_sum_of_basis`: compatibility with `extendCoefficients` on
  extended measures, pure tensors, and arbitrary measures via a finite basis.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, Proposition 3.16 and Remark 3.28.
-/

public noncomputable section

open ContinuousMap TensorProduct Topology TauCeti

namespace AbstractMeasure

section TopologicalSpace

variable {X : Type*} [TopologicalSpace X]
  (R O : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

omit [Module.Projective R O] [Module.Finite R O] in
private theorem continuousMap_eq_sum_of_dual {n : ℕ} {b : Fin n → O}
    {φ : Fin n → Module.Dual R O} (hsum : ∀ a : O, ∑ i, φ i a • b i = a) (F : C(X, O)) :
    F = ∑ i : Fin n,
      b i • ((algebraMapCLM R O : C(R, O)).comp
        ((⟨φ i, IsModuleTopology.continuous_of_linearMap (φ i)⟩ : C(O, R)).comp F)) := by
  ext x
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.comp_apply, algebraMapCLM_apply, ContinuousMap.coe_mk,
    smul_eq_mul]
  have hcomm : ∀ c : O, ∀ r : R, c * algebraMap R O r = r • c :=
    fun c r ↦ by rw [Algebra.smul_def, mul_comm]
  simp_rw [hcomm]
  exact (hsum (F x)).symm

/-- Two `O`-valued measures agreeing on every test function of the form `algebraMap R O ∘ f`
(`f ∈ C(X, R)`) are equal. -/
theorem ext_comp_algebraMap {ν₁ ν₂ : D(X, O)}
    (h : ∀ f : C(X, R),
      ν₁ ((algebraMapCLM R O : C(R, O)).comp f) = ν₂ ((algebraMapCLM R O : C(R, O)).comp f)) :
    ν₁ = ν₂ := by
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  ext F
  rw [continuousMap_eq_sum_of_dual R O hsum F, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, map_smul, h]

private theorem exists_apply_comp_algebraMap (μ : D(X, R)) :
    ∃ ν : D(X, O),
      ∀ f : C(X, R), ν ((algebraMapCLM R O : C(R, O)).comp f) = algebraMap R O (μ f) := by
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  let cAdd (i : Fin n) : C(X, O) →+ C(X, R) :=
    (φ i).toAddMonoidHom.compLeftContinuous X (IsModuleTopology.continuous_of_linearMap (φ i))
  have hcAdd (i : Fin n) (F : C(X, O)) :
      cAdd i F = (⟨φ i, IsModuleTopology.continuous_of_linearMap (φ i)⟩ : C(O, R)).comp F :=
    (rfl)
  have hcoord (i : Fin n) (a : O) (F : C(X, O)) :
      cAdd i (a • F) = ∑ j : Fin n, φ i (a * b j) • cAdd j F := by
    ext x
    simp only [hcAdd, ContinuousMap.comp_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply]
    conv_lhs => rw [← hsum (F x)]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  refine ⟨toCLMEquiv.symm
    { toFun := fun F ↦ ∑ i : Fin n, μ (cAdd i F) • b i
      map_add' := fun F₁ F₂ ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a F ↦ by
        simp only [RingHom.id_apply, hcoord, map_sum, map_smul, smul_eq_mul, Finset.sum_smul]
        simp_rw [mul_comm (φ _ _) _, ← smul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.smul_sum, hsum, Finset.mul_sum, Algebra.mul_smul_comm]
      cont := continuous_finsetSum _ fun i _ ↦
        ((map_continuous μ).comp
          (ContinuousMap.continuous_postcomp
            ⟨φ i, IsModuleTopology.continuous_of_linearMap (φ i)⟩)).smul continuous_const },
    fun f ↦ ?_⟩
  have hcomp (i : Fin n) : cAdd i ((algebraMapCLM R O : C(R, O)).comp f) = φ i 1 • f := by
    ext x
    simp only [hcAdd, ContinuousMap.comp_apply, algebraMapCLM_apply,
      ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]
  simp only [coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    hcomp, map_smul, smul_eq_mul]
  simp_rw [mul_comm (φ _ 1) (μ f), ← smul_smul, ← Finset.smul_sum]
  rw [hsum 1, ← Algebra.algebraMap_eq_smul_one]

/-- **Scalar extension of abstract measures.** When `O` carries the `R`-module topology and is
finitely generated and projective over `R`, `extendScalars R O` extends every `R`-valued measure
`μ ∈ D(X, R)` to the unique `O`-valued measure sending `algebraMap R O ∘ f` to
`algebraMap R O (μ f)` for all `f ∈ C(X, R)` (`extendScalars_apply_comp`,
`eq_extendScalars_of_apply_comp`). -/
def extendScalars : D(X, R) →ₛₗ[algebraMap R O] D(X, O) where
  toFun μ := (exists_apply_comp_algebraMap R O μ).choose
  map_add' μ₁ μ₂ := ext_comp_algebraMap R O fun f ↦ by
    have h := fun μ ↦ (exists_apply_comp_algebraMap R O μ).choose_spec f
    rw [_root_.add_apply, h, h, h, _root_.add_apply, map_add]
  map_smul' r μ := ext_comp_algebraMap R O fun f ↦ by
    have h := fun μ ↦ (exists_apply_comp_algebraMap R O μ).choose_spec f
    rw [_root_.smul_apply, h, h, _root_.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]

/-- Extending scalars of `μ` integrates `algebraMap R O ∘ f` to `algebraMap R O (μ f)`. -/
@[simp]
theorem extendScalars_apply_comp (μ : D(X, R)) (f : C(X, R)) :
    extendScalars R O μ ((algebraMapCLM R O : C(R, O)).comp f) = algebraMap R O (μ f) :=
  (exists_apply_comp_algebraMap R O μ).choose_spec f

variable {R O}

/-- Any `O`-valued measure sending `algebraMap R O ∘ f` to `algebraMap R O (μ f)` for all
`f ∈ C(X, R)` equals `extendScalars R O μ`. -/
theorem eq_extendScalars_of_apply_comp {μ : D(X, R)} {ν : D(X, O)}
    (hν : ∀ f : C(X, R), ν ((algebraMapCLM R O : C(R, O)).comp f) = algebraMap R O (μ f)) :
    ν = extendScalars R O μ :=
  ext_comp_algebraMap R O fun f ↦ (hν f).trans (extendScalars_apply_comp R O μ f).symm

/-- For every `μ ∈ D(X, R)` there is a unique `O`-valued measure integrating `algebraMap R O ∘ f` to
`algebraMap R O (μ f)` for all `f ∈ C(X, R)`. -/
theorem existsUnique_apply_comp_algebraMap (μ : D(X, R)) :
    ∃! ν : D(X, O),
      ∀ f : C(X, R), ν ((algebraMapCLM R O : C(R, O)).comp f) = algebraMap R O (μ f) :=
  ⟨extendScalars R O μ, extendScalars_apply_comp R O μ,
    fun _ hν ↦ eq_extendScalars_of_apply_comp hν⟩

/-- Scalar extension sends Dirac measures to Dirac measures. -/
@[simp]
theorem extendScalars_dirac (x : X) :
    extendScalars R O (dirac R x) = dirac O x :=
  (eq_extendScalars_of_apply_comp fun _ ↦ by simp).symm

/-- Extending scalars from `R` to `R` itself is the identity map. -/
@[simp]
theorem extendScalars_self :
    extendScalars R R (X := X) = LinearMap.id :=
  LinearMap.ext fun μ ↦ (eq_extendScalars_of_apply_comp fun f ↦ by
    have hf : (algebraMapCLM R R : C(R, R)).comp f = f := by ext; simp
    simp [hf]).symm

/-- Scalar extension commutes with pushforward along continuous maps. -/
@[simp]
theorem extendScalars_map {Y : Type*} [TopologicalSpace Y] (φ : C(X, Y)) (μ : D(X, R)) :
    extendScalars R O (map φ μ) = map φ (extendScalars R O μ) :=
  (eq_extendScalars_of_apply_comp fun f ↦ by
    simp only [map_apply]
    rw [ContinuousMap.comp_assoc, extendScalars_apply_comp]).symm

/-- The finite projections of `extendScalars R O μ` are obtained from those of `μ` by applying
`algebraMap R O` to each fibre coefficient. -/
@[simp]
theorem finiteProjection_extendScalars {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] (q : C(X, A)) (μ : D(X, R)) :
    finiteProjection q (extendScalars R O μ) =
      (finiteProjection q μ).mapRange (algebraMap R O) (map_zero _) := by
  ext a
  rw [finiteProjection_apply, Finsupp.mapRange_apply, finiteProjection_apply]
  have hfib : fiberIndicator (R := O) q a =
      (algebraMapCLM R O : C(R, O)).comp (fiberIndicator (R := R) q a) := by
    ext x
    classical
    by_cases hx : q x = a <;> simp [fiberIndicator_apply, hx]
  rw [hfib, extendScalars_apply_comp]

/-! ### Coefficient functionals and module base change `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)` -/

omit [Module.Projective R O] [Module.Finite R O] in
/-- Push an `O`-valued measure along an `R`-linear functional `ℓ : O →ₗ[R] R` on coefficients,
sending `f ∈ C(X, R)` to `ℓ (ν (algebraMap R O ∘ f))`. Continuity holds automatically when `O`
carries the `R`-module topology. -/
def mapCoeff (ℓ : O →ₗ[R] R) : D(X, O) →+ D(X, R) where
  toFun ν := toCLMEquiv.symm <|
    (⟨ℓ, IsModuleTopology.continuous_of_linearMap ℓ⟩ : O →L[R] R).comp <|
      ((toCLMEquiv ν).restrictScalars R).comp ((algebraMapCLM R O).compLeftContinuous R X)
  map_zero' := ext fun f ↦ by simp [← coe_toCLMEquiv]
  map_add' ν₁ ν₂ := ext fun f ↦ by simp

omit [Module.Projective R O] [Module.Finite R O] in
@[simp]
theorem mapCoeff_apply (ℓ : O →ₗ[R] R) (ν : D(X, O)) (f : C(X, R)) :
    mapCoeff ℓ ν f = ℓ (ν ((algebraMapCLM R O : C(R, O)).comp f)) := by
  rw [mapCoeff, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coe_symm_toCLMEquiv]
  exact congrArg ℓ (by rw [← coe_toCLMEquiv]; rfl)

@[simp]
theorem mapCoeff_smul_extendScalars (ℓ : O →ₗ[R] R) (a : O) (μ : D(X, R)) :
    mapCoeff ℓ (a • extendScalars R O μ) = ℓ a • μ := by
  ext f
  rw [mapCoeff_apply, _root_.smul_apply, extendScalars_apply_comp, smul_eq_mul, mul_comm,
    ← Algebra.smul_def, map_smul, _root_.smul_apply, smul_eq_mul, mul_comm, ← smul_eq_mul]

@[simp]
theorem mapCoeff_extendScalars (ℓ : O →ₗ[R] R) (μ : D(X, R)) :
    mapCoeff ℓ (extendScalars R O μ) = ℓ 1 • μ := by
  simpa using mapCoeff_smul_extendScalars ℓ 1 μ

omit [Module.Projective R O] [Module.Finite R O] in
@[simp]
theorem mapCoeff_smul_dirac (ℓ : O →ₗ[R] R) (a : O) (x : X) :
    mapCoeff ℓ (a • dirac O x) = ℓ a • dirac R x := by
  ext f
  simp only [mapCoeff_apply, _root_.smul_apply, dirac_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_ofClass, algebraMapCLM_apply, smul_eq_mul]
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

omit [Module.Projective R O] [Module.Finite R O] in
@[simp]
theorem mapCoeff_dirac (ℓ : O →ₗ[R] R) (x : X) :
    mapCoeff ℓ (dirac O x) = ℓ 1 • dirac R x := by
  simpa using mapCoeff_smul_dirac ℓ 1 x

omit [Module.Projective R O] [Module.Finite R O] in
@[simp]
theorem mapCoeff_map {Y : Type*} [TopologicalSpace Y] (ℓ : O →ₗ[R] R) (φ : C(X, Y))
    (ν : D(X, O)) :
    mapCoeff ℓ (map φ ν) = map φ (mapCoeff ℓ ν) := by
  ext f
  simp [ContinuousMap.comp_assoc]

omit [Module.Projective R O] [Module.Finite R O] in
@[simp]
theorem finiteProjection_mapCoeff {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (q : C(X, A)) (ℓ : O →ₗ[R] R) (ν : D(X, O)) :
    finiteProjection q (mapCoeff ℓ ν) = (finiteProjection q ν).mapRange ℓ ℓ.map_zero := by
  ext a
  rw [finiteProjection_apply, Finsupp.mapRange_apply, finiteProjection_apply, mapCoeff_apply]
  congr 2
  ext x
  classical
  by_cases hx : q x = a <;> simp [fiberIndicator_apply, hx]

/-- Given a finite `R`-basis `b` of `O`, every `O`-valued measure `ν` decomposes in terms of `b` and
its `R`-valued coordinate measures `mapCoeff (b.coord i) ν`. -/
theorem eq_sum_smul_extendScalars_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (ν : D(X, O)) :
    ν = ∑ i : ι, b i • extendScalars R O (mapCoeff (b.coord i) ν) := by
  refine ext_comp_algebraMap R O fun f ↦ ?_
  rw [← coe_toCLMEquiv (∑ i : ι, _), map_sum, _root_.sum_apply]
  simp_rw [coe_toCLMEquiv, _root_.smul_apply, extendScalars_apply_comp, mapCoeff_apply,
    Module.Basis.coord_apply, smul_eq_mul, mul_comm (b _), ← Algebra.smul_def]
  exact (b.sum_repr (ν ((algebraMapCLM R O : C(R, O)).comp f))).symm

omit [Module.Projective R O] [Module.Finite R O] in
/-- Given a finite `R`-basis `b` of `O`, two `O`-valued measures are equal whenever all of their
`b`-coordinate measures in `D(X, R)` agree. -/
theorem ext_of_basis {ι : Type*} [Finite ι] (b : Module.Basis ι R O) {ν₁ ν₂ : D(X, O)}
    (h : ∀ i : ι, mapCoeff (b.coord i) ν₁ = mapCoeff (b.coord i) ν₂) :
    ν₁ = ν₂ := by
  let _ := Fintype.ofFinite ι
  have := Module.Projective.of_basis b
  have := Module.Finite.of_basis b
  rw [eq_sum_smul_extendScalars_of_basis b ν₁, eq_sum_smul_extendScalars_of_basis b ν₂]
  simp_rw [h]

variable (R O) in
/-- The forward `O`-linear map `O ⊗[R] D(X, R) →ₗ[O] D(X, O)` sending `a ⊗ₜ μ` to
`a • extendScalars R O μ`. -/
private def baseChangeLinearMap : O ⊗[R] D(X, R) →ₗ[O] D(X, O) :=
  letI : Module R D(X, O) := Module.compHom D(X, O) (algebraMap R O)
  letI : IsScalarTower R O D(X, O) := IsScalarTower.of_compHom R O D(X, O)
  LinearMap.liftBaseChange O
    { toFun := extendScalars R O
      map_add' := map_add _
      map_smul' := fun r μ ↦ map_smulₛₗ (extendScalars R O) r μ }

private theorem baseChangeLinearMap_tmul (a : O) (μ : D(X, R)) :
    baseChangeLinearMap R O (a ⊗ₜ[R] μ) = a • extendScalars R O μ :=
  letI : Module R D(X, O) := Module.compHom D(X, O) (algebraMap R O)
  letI : IsScalarTower R O D(X, O) := IsScalarTower.of_compHom R O D(X, O)
  LinearMap.liftBaseChange_tmul O _ a μ

private theorem baseChangeLinearMap_bijective :
    Function.Bijective (baseChangeLinearMap R O (X := X)) := by
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  let inv (ν : D(X, O)) : O ⊗[R] D(X, R) :=
    ∑ i : Fin n, b i ⊗ₜ[R] mapCoeff (φ i) ν
  refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
  · have hadd : ∀ u v : D(X, O), inv (u + v) = inv u + inv v :=
      fun u v ↦ by simp [inv, tmul_add, Finset.sum_add_distrib]
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a μ =>
      rw [baseChangeLinearMap_tmul]
      simp only [inv, mapCoeff_smul_extendScalars, ← smul_tmul, ← sum_tmul]
      exact congrArg (· ⊗ₜ[R] μ) (hsum a)
    | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, hadd, hz₁, hz₂]
  · intro ν
    dsimp only [inv]
    refine ext_comp_algebraMap R O fun f ↦ ?_
    rw [map_sum, ← coe_toCLMEquiv, map_sum, _root_.sum_apply]
    simp_rw [coe_toCLMEquiv, baseChangeLinearMap_tmul, _root_.smul_apply,
      extendScalars_apply_comp, mapCoeff_apply, smul_eq_mul, mul_comm (b _), ← Algebra.smul_def]
    exact hsum (ν ((algebraMapCLM R O : C(R, O)).comp f))

variable (R O) in
/-- **Base change of abstract measures.** When `O` carries the `R`-module topology and is finitely
generated and projective over `R`, `baseChange R O` identifies `O ⊗[R] D(X, R)` with `D(X, O)` as an
`O`-module, sending `a ⊗ₜ μ` to `a • extendScalars R O μ`. -/
def baseChange : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O) :=
  LinearEquiv.ofBijective (baseChangeLinearMap R O) baseChangeLinearMap_bijective

@[simp]
theorem baseChange_tmul (a : O) (μ : D(X, R)) :
    baseChange R O (a ⊗ₜ[R] μ) = a • extendScalars R O μ :=
  baseChangeLinearMap_tmul a μ

theorem baseChange_tmul_dirac (a : O) (x : X) :
    baseChange R O (a ⊗ₜ[R] dirac R x) = a • dirac O x := by
  simp

@[simp]
theorem baseChange_symm_extendScalars (μ : D(X, R)) :
    (baseChange R O).symm (extendScalars R O μ) = 1 ⊗ₜ[R] μ := by
  apply (baseChange R O).injective
  simp

@[simp]
theorem baseChange_symm_dirac (x : X) :
    (baseChange R O).symm (dirac O x) = 1 ⊗ₜ[R] dirac R x := by
  rw [← extendScalars_dirac (R := R) (O := O), baseChange_symm_extendScalars]

/-- Base change from `R` to `R` itself recovers `TensorProduct.lid`. -/
@[simp]
theorem baseChange_self :
    baseChange R R (X := X) = TensorProduct.lid R D(X, R) := by
  apply LinearEquiv.toLinearMap_injective
  ext μ
  simp

/-- Distinct scalar multiples of a Dirac measure remain distinct after base change. -/
theorem baseChange_tmul_dirac_ne {a b : O} (hab : a ≠ b) (x : X) :
    baseChange R O (a ⊗ₜ[R] dirac R x) ≠ baseChange R O (b ⊗ₜ[R] dirac R x) := by
  simpa using hab

end TopologicalSpace

section Monoid

variable {G : Type*} [Monoid G] [TopologicalSpace G]

section ModuleTopology

variable {R O : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

@[simp]
theorem extendScalars_one :
    extendScalars R O (1 : D(G, R)) = 1 :=
  extendScalars_dirac 1

omit [Module.Projective R O] [Module.Finite R O] in
@[simp]
theorem mapCoeff_one (ℓ : O →ₗ[R] R) :
    mapCoeff ℓ (1 : D(G, O)) = ℓ 1 • 1 :=
  mapCoeff_dirac ℓ 1

variable [ContinuousMul G]

/-- Scalar extension commutes with right convolution of test functions. -/
theorem convolveFunRight_extendScalars_comp (ν : D(G, R)) (f : C(G, R)) :
    convolveFunRight (extendScalars R O ν) ((algebraMapCLM R O : C(R, O)).comp f) =
      (algebraMapCLM R O : C(R, O)).comp (convolveFunRight ν f) := by
  ext x
  rw [convolveFunRight_apply, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass,
    algebraMapCLM_apply, convolveFunRight_apply]
  exact extendScalars_apply_comp R O ν ⟨fun y ↦ f (x * y), by fun_prop⟩

variable [LocallyCompactSpace G]

omit [Module.Projective R O] [Module.Finite R O] in
@[simp]
theorem mapCoeff_algebraMap (ℓ : O →ₗ[R] R) (a : O) :
    mapCoeff ℓ (algebraMap O D(G, O) a) = algebraMap R D(G, R) (ℓ a) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact mapCoeff_smul_dirac ℓ a 1

/-- Scalar extension preserves convolution of measures on a locally compact topological monoid. -/
@[simp]
theorem extendScalars_mul (μ ν : D(G, R)) :
    extendScalars R O (μ * ν) = extendScalars R O μ * extendScalars R O ν :=
  (eq_extendScalars_of_apply_comp fun f ↦ by
    rw [mul_apply, convolveFunRight_extendScalars_comp, extendScalars_apply_comp, mul_apply]).symm

variable (R O) in
/-- Scalar extension on a locally compact monoid, bundled as a ring homomorphism
`D(G, R) →+* D(G, O)`. -/
def extendScalarsRingHom : D(G, R) →+* D(G, O) where
  toFun := extendScalars R O
  map_one' := extendScalars_one
  map_mul' := extendScalars_mul
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
theorem coe_extendScalarsRingHom :
    ⇑(extendScalarsRingHom R O (G := G)) = extendScalars R O :=
  (rfl)

@[simp]
theorem extendScalarsRingHom_algebraMap (r : R) :
    extendScalarsRingHom R O (algebraMap R D(G, R) r) =
      algebraMap O D(G, O) (algebraMap R O r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, coe_extendScalarsRingHom,
    map_smulₛₗ, extendScalars_one]

variable (R O) in
/-- **Convolution-algebra base change of abstract measures.** On a locally compact topological
monoid `G`, when `O` carries the `R`-module topology and is finitely generated and projective over
`R`, `baseChangeAlgEquiv R O` identifies `O ⊗[R] D(G, R)` with `D(G, O)` as an `O`-algebra. -/
def baseChangeAlgEquiv : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (baseChange R O)
    (fun a₁ a₂ μ₁ μ₂ ↦ by
      simp only [baseChange_tmul]
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, extendScalars_mul, map_mul]
      simp only [mul_assoc]
      congr 1
      rw [← mul_assoc, Algebra.commutes a₂, mul_assoc])
    (by simp)

@[simp]
theorem toLinearEquiv_baseChangeAlgEquiv :
    (baseChangeAlgEquiv R O (G := G)).toLinearEquiv = baseChange R O :=
  (rfl)

@[simp]
theorem coe_baseChangeAlgEquiv :
    ⇑(baseChangeAlgEquiv R O (G := G)) = baseChange R O :=
  (rfl)

@[simp]
theorem baseChangeAlgEquiv_tmul (a : O) (μ : D(G, R)) :
    baseChangeAlgEquiv R O (a ⊗ₜ[R] μ) = a • extendScalars R O μ :=
  baseChange_tmul a μ

theorem baseChangeAlgEquiv_tmul_dirac (a : O) (x : G) :
    baseChangeAlgEquiv R O (a ⊗ₜ[R] dirac R x) = a • dirac O x :=
  baseChange_tmul_dirac a x

@[simp]
theorem baseChangeAlgEquiv_symm_extendScalars (μ : D(G, R)) :
    (baseChangeAlgEquiv R O).symm (extendScalars R O μ) = 1 ⊗ₜ[R] μ :=
  baseChange_symm_extendScalars μ

@[simp]
theorem baseChangeAlgEquiv_symm_dirac (x : G) :
    (baseChangeAlgEquiv R O).symm (dirac O x) = 1 ⊗ₜ[R] dirac R x :=
  baseChange_symm_dirac x

/-- Convolution-algebra base change from `R` to `R` itself recovers `Algebra.TensorProduct.lid`. -/
@[simp]
theorem baseChangeAlgEquiv_self :
    baseChangeAlgEquiv R R (G := G) = Algebra.TensorProduct.lid R D(G, R) := by
  apply AlgEquiv.coe_toAlgHom_injective
  ext μ
  simp

end ModuleTopology

variable [ContinuousMul G] [LocallyCompactSpace G] in
/-- For any compact topological commutative ring `R` and any Hausdorff topological commutative
`R`-algebra `O` with continuous `R`-scalar multiplication that is finitely generated and projective
over `R`, there exists an `O`-algebra isomorphism `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` sending
`a ⊗ₜ dirac R x` to `a • dirac O x`. -/
theorem exists_baseChange_algEquiv {R O : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [T2Space O] [Algebra R O] [ContinuousSMul R O]
    [Module.Projective R O] [Module.Finite R O] :
    ∃ e : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O),
      ∀ (a : O) (x : G), e (a ⊗ₜ[R] dirac R x) = a • dirac O x := by
  have := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := R) (M := O)
  exact ⟨baseChangeAlgEquiv R O, baseChangeAlgEquiv_tmul_dirac⟩

end Monoid

section CompletedGroupAlgebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
  [ContinuousMul Γ] [LocallyCompactSpace Γ]

section ModuleTopology

variable {R O : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

/-- `toCompletedGroupAlgebra` intertwines `extendScalars R O` on measures with
`completedGroupAlgebra.mapRingHom Γ (algebraMap R O)`. -/
@[simp]
theorem toCompletedGroupAlgebra_extendScalars (μ : D(Γ, R)) :
    toCompletedGroupAlgebra (extendScalars R O μ) =
      completedGroupAlgebra.mapRingHom Γ (algebraMap R O) (toCompletedGroupAlgebra μ) := by
  ext U q
  simp

/-- `toCompletedGroupAlgebra` intertwines `baseChangeAlgEquiv R O` with
`completedGroupAlgebra.scalarTensorEquiv R O Γ`. -/
theorem toCompletedGroupAlgebra_baseChangeAlgEquiv (z : O ⊗[R] D(Γ, R)) :
    toCompletedGroupAlgebra (baseChangeAlgEquiv R O z) =
      completedGroupAlgebra.scalarTensorEquiv R O Γ
        (Algebra.TensorProduct.map (AlgHom.id O O) toCompletedGroupAlgebra z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a μ => simp
  | add z₁ z₂ hz₁ hz₂ =>
    rw [map_add, map_add, map_add, map_add, hz₁, hz₂]

/-- If `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` is surjective, then so is
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` for any finite projective `R`-algebra `O` carrying
the `R`-module topology. -/
theorem toCompletedGroupAlgebra_surjective_of_surjective
    (hs : Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  intro y
  obtain ⟨z, hz⟩ := Algebra.TensorProduct.map_surjective (AlgHom.id O O)
    (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ) Function.surjective_id hs
    ((completedGroupAlgebra.scalarTensorEquiv R O Γ).symm y)
  refine ⟨baseChangeAlgEquiv R O z, ?_⟩
  rw [toCompletedGroupAlgebra_baseChangeAlgEquiv, hz, AlgEquiv.apply_symm_apply]

/-- If `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` is bijective, then
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is an `O`-algebra isomorphism. -/
def completedGroupAlgebraEquivOfBijective
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective toCompletedGroupAlgebra
    ⟨fun μ₁ μ₂ h ↦ (baseChangeAlgEquiv R O).symm.injective <| by
        let eO : O ⊗[R] D(Γ, R) ≃ₐ[O] O ⊗[R] completedGroupAlgebra R Γ :=
          Algebra.TensorProduct.congr (.refl : O ≃ₐ[O] O)
            (AlgEquiv.ofBijective toCompletedGroupAlgebra hb)
        have heO : ⇑(Algebra.TensorProduct.map (AlgHom.id O O)
            (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) = ⇑eO :=
          funext fun z ↦ by simp [eO]
        apply eO.injective
        apply (completedGroupAlgebra.scalarTensorEquiv R O Γ).injective
        rw [← congrFun heO, ← congrFun heO, ← toCompletedGroupAlgebra_baseChangeAlgEquiv,
          ← toCompletedGroupAlgebra_baseChangeAlgEquiv, AlgEquiv.apply_symm_apply,
          AlgEquiv.apply_symm_apply, h],
      toCompletedGroupAlgebra_surjective_of_surjective hb.2⟩

@[simp]
theorem completedGroupAlgebraEquivOfBijective_apply
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ))
    (μ : D(Γ, O)) :
    completedGroupAlgebraEquivOfBijective hb μ = toCompletedGroupAlgebra μ :=
  AlgEquiv.ofBijective_apply _ _ _

omit [Module.Projective R O] [Module.Finite R O] in
/-- `toCompletedGroupAlgebra` intertwines `mapCoeff ℓ` on measures with
`completedGroupAlgebra.mapAddMonoidHom` along `ℓ`. -/
@[simp]
theorem toCompletedGroupAlgebra_mapCoeff (ℓ : O →ₗ[R] R) (ν : D(Γ, O)) :
    toCompletedGroupAlgebra (mapCoeff ℓ ν) =
      completedGroupAlgebra.mapAddMonoidHom Γ ℓ.toAddMonoidHom (toCompletedGroupAlgebra ν) := by
  ext U q
  simp

omit [Module.Projective R O] [Module.Finite R O] in
private theorem apply_eq_sum_of_dual_of_leftInverse
    {n : ℕ} {b : Fin n → O} {φ : Fin n → Module.Dual R O}
    (hsum : ∀ a : O, ∑ i, φ i a • b i = a)
    (inv : completedGroupAlgebra R Γ → D(Γ, R))
    (hinv : Function.LeftInverse inv toCompletedGroupAlgebra)
    (F : C(Γ, O)) (ν : D(Γ, O)) :
    ν F = ∑ j : Fin n, b j *
      ∑ i : Fin n,
        (inv (completedGroupAlgebra.mapAddMonoidHom Γ
          (φ i).toAddMonoidHom (toCompletedGroupAlgebra ν))
            ((⟨φ j, IsModuleTopology.continuous_of_linearMap (φ j)⟩ : C(O, R)).comp F)) • b i := by
  conv_lhs => rw [continuousMap_eq_sum_of_dual R O hsum F]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  conv_lhs =>
    rw [← hsum (ν ((algebraMapCLM R O : C(R, O)).comp
      ((⟨φ j, IsModuleTopology.continuous_of_linearMap (φ j)⟩ : C(O, R)).comp F)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [← mapCoeff_apply (φ i), ← toCompletedGroupAlgebra_mapCoeff, hinv _]

end ModuleTopology

section Normed

/-- If `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` is a homeomorphism from the weak topology to
the inverse-limit topology, then so is `toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` for any
normed `R`-algebra `O` carrying the `R`-module topology that is finitely generated and projective
over `R`. -/
theorem isHomeomorph_toCompletedGroupAlgebra_weak_of_isHomeomorph
    {R O : Type*} [NormedCommRing R] [NormedCommRing O] [Algebra R O]
    [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]
    (hh : @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := R) (E := R)) _
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := O) (E := O)) _
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  have := IsModuleTopology.toContinuousSMul R O
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  let tDR : TopologicalSpace D(Γ, R) := WeakTopology (X := Γ) (R := R) (E := R)
  let eR : completedGroupAlgebra R Γ ≃ₜ D(Γ, R) :=
    (@IsHomeomorph.homeomorph _ _ tDR _ _ hh).symm
  have heR : Function.LeftInverse eR toCompletedGroupAlgebra :=
    (@IsHomeomorph.homeomorph _ _ tDR _ _ hh).left_inv
  have heval (F : C(Γ, O)) :
      Continuous[.induced toCompletedGroupAlgebra inferInstance, _]
        fun ν : D(Γ, O) ↦ ν F := by
    let : TopologicalSpace D(Γ, O) := .induced toCompletedGroupAlgebra inferInstance
    simp_rw [apply_eq_sum_of_dual_of_leftInverse hsum eR heR F]
    refine continuous_finsetSum _ fun j _ ↦ continuous_const.mul <|
      continuous_finsetSum _ fun i _ ↦ ?_
    have hmap : Continuous fun ν : D(Γ, O) ↦
        eR (completedGroupAlgebra.mapAddMonoidHom Γ
          (φ i).toAddMonoidHom (toCompletedGroupAlgebra ν)) :=
      eR.continuous.comp <|
        (completedGroupAlgebra.continuous_mapAddMonoidHom
          (IsModuleTopology.continuous_of_linearMap (φ i))).comp continuous_induced_dom
    let cF : C(Γ, R) :=
      (⟨φ j, IsModuleTopology.continuous_of_linearMap (φ j)⟩ : C(O, R)).comp F
    have hevR : @Continuous D(Γ, R) R tDR _ (fun μ : D(Γ, R) ↦ μ cF) :=
      (continuous_apply cF).comp continuous_induced_dom
    exact (hevR.comp hmap).smul continuous_const
  have hle : .induced toCompletedGroupAlgebra inferInstance ≤
      WeakTopology (X := Γ) (R := O) (E := O) := by
    let : TopologicalSpace D(Γ, O) := .induced toCompletedGroupAlgebra inferInstance
    exact continuous_iff_le_induced.mp (continuous_pi heval)
  let : TopologicalSpace D(Γ, O) := WeakTopology (X := Γ) (R := O) (E := O)
  have hind : IsInducing
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) :=
    ⟨le_antisymm (continuous_iff_le_induced.mp continuous_toCompletedGroupAlgebra) hle⟩
  have hbij := (completedGroupAlgebraEquivOfBijective (R := R) (O := O) hh.bijective).bijective
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hind, hbij.1⟩, hbij.2⟩

end Normed

end CompletedGroupAlgebra

section ExtendCoefficients

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
  {R O K : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]
  [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Extending coefficients from `O` to `K` after `extendScalars R O` agrees with extending
coefficients directly from `R` to `K` along `j.comp (algebraMap R O)`. No continuity assumption on
`j` is needed. -/
@[simp]
theorem extendCoefficients_extendScalars (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (μ : D(X, R)) :
    extendCoefficients j hj (extendScalars R O μ) =
      extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ :=
  finiteProjection_ext _ _ fun q ↦ by
    ext b
    simp

/-- Extending coefficients of a base-changed pure tensor `a ⊗ₜ μ` scales the coefficient extension
of `μ` by `j a`. -/
theorem extendCoefficients_baseChange_tmul (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O)
    (μ : D(X, R)) :
    extendCoefficients j hj (baseChange R O (a ⊗ₜ[R] μ)) =
      j a • extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ := by
  rw [baseChange_tmul, extendCoefficients_smul, extendCoefficients_extendScalars]

omit [Module.Projective R O] [Module.Finite R O] in
/-- Given a finite `R`-basis `b` of `O`, extending coefficients of any `ν ∈ D(X, O)` along
`j : O →+* K` decomposes as the `j (b i)`-linear combination of the extensions of its `R`-valued
coordinate measures `mapCoeff (b.coord i) ν`. -/
theorem extendCoefficients_eq_sum_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (ν : D(X, O)) :
    extendCoefficients j hj ν =
      ∑ i : ι, j (b i) • extendCoefficients (j.comp (algebraMap R O))
        (fun r ↦ hj (algebraMap R O r)) (mapCoeff (b.coord i) ν) := by
  have := Module.Projective.of_basis b
  have := Module.Finite.of_basis b
  conv_lhs => rw [eq_sum_smul_extendScalars_of_basis b ν]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [extendCoefficients_smul, extendCoefficients_extendScalars]

end ExtendCoefficients

section Examples

variable {p : ℕ} [Fact p.Prime]
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ]

/-! ### Arithmetic instantiations over `ℤ_[p]` -/

-- Convolution-algebra base change over `ℤ_[p]` for a finite free normed `ℤ_[p]`-algebra `O`.
example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    ∃ e : O ⊗[ℤ_[p]] D(Γ, ℤ_[p]) ≃ₐ[O] D(Γ, O),
      ∀ (a : O) (x : Γ), e (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = a • dirac O x :=
  exists_baseChange_algEquiv

-- Base change from `ℤ_[p]` to `ℤ_[p]` recovers `Algebra.TensorProduct.lid`.
example : baseChangeAlgEquiv ℤ_[p] ℤ_[p] (G := Γ) = Algebra.TensorProduct.lid ℤ_[p] D(Γ, ℤ_[p]) :=
  baseChangeAlgEquiv_self

-- `1 ⊗ₜ dirac ℤ_[p] x` maps to `dirac O x`, and distinct scalars yield distinct Dirac multiples.
example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] {a b : O} (hab : a ≠ b) (x : Γ) :
    let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
    baseChangeAlgEquiv ℤ_[p] O (1 ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = dirac O x ∧
      baseChangeAlgEquiv ℤ_[p] O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) ≠
        baseChangeAlgEquiv ℤ_[p] O (b ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  exact ⟨by simp, baseChange_tmul_dirac_ne hab x⟩

-- Comparison `D(Γ, O) ≃ₐ[O] O[[Γ]]` and weak-topology homeomorphism for profinite `Γ` over `ℤ_[p]`.
example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    Nonempty (D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ) ∧
      @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := O) (E := O)) _
        (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  exact ⟨⟨completedGroupAlgebraEquivOfBijective (R := ℤ_[p]) (O := O)
      ⟨toCompletedGroupAlgebra_injective, toCompletedGroupAlgebra_surjective⟩⟩,
    isHomeomorph_toCompletedGroupAlgebra_weak_of_isHomeomorph
      (isHomeomorph_toCompletedGroupAlgebra_weak (Γ := Γ) (p := p))⟩

-- Negative control: without `p ^ n • 1 → 0`, `ContinuousSMul ℤ_[p] O` fails.
example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O]
    (h : ¬ Filter.Tendsto (fun n : ℕ ↦ ((p : ℤ_[p]) ^ n) • (1 : O)) Filter.atTop (nhds 0)) :
    ¬ ContinuousSMul ℤ_[p] O :=
  fun _ ↦ h <| by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (PadicInt.norm_p_lt_one (p := p))).smul_const (1 : O)

end Examples

end AbstractMeasure
