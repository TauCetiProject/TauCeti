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
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.BaseChange
public import TauCeti.Topology.Algebra.Module.AutomaticContinuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Finite projective base change of abstract measures

Let `X` be a topological space, `R` a topological commutative ring, and `O` a topological
commutative `R`-algebra that carries the `R`-module topology (`IsModuleTopology R O`) and is
finitely generated and projective over `R`. Every `R`-linear functional `O →ₗ[R] R` is then
continuous, so choosing a finite dual pair `(b_i, c_i)` for `O` over `R` decomposes every continuous
test function `F ∈ C(X, O)` as `Σ_i b_i • (algebraMap R O ∘ c_i ∘ F)`. Integrating each coordinate
`c_i ∘ F ∈ C(X, R)` against a measure `μ ∈ D(X, R)` defines an `O`-valued measure
`scalarExtend R O μ ∈ D(X, O)`.

Although the construction chooses a finite dual pair, the resulting measure is independent of that
choice: it is uniquely characterised by `scalarExtend R O μ (algebraMap R O ∘ f) =
algebraMap R O (μ f)` for all `f ∈ C(X, R)` (`scalarExtend_apply_comp`,
`eq_scalarExtend_of_apply_comp`). Pushing `O`-valued measures back along `c_i` supplies the
two-sided inverse to the induced map from `O ⊗[R] D(X, R)`, yielding an `O`-linear isomorphism
`baseChange R O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.

When `G` is a locally compact topological monoid, `scalarExtend R O` respects Dirac units and
convolution (`scalarExtend_one`, `scalarExtend_mul`), upgrading `baseChange R O` to an `O`-algebra
isomorphism `baseChangeAlgEquiv R O : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)`. Over a compact base ring `R`
(such as `ℤ_[p]`), any Hausdorff `R`-algebra `O` with continuous `R`-scalar multiplication that is
finitely generated over `R` automatically carries the `R`-module topology
(`TauCeti.isModuleTopology_of_finite_of_compactSpace`), giving `exists_baseChange_algEquiv`.

Every hypothesis on `O` is necessary:
* `ContinuousSMul R O` / `IsModuleTopology R O` cannot be dropped: if `r_n → 0` in `R` while
  `r_n • (1 : O)` does not tend to `0` in `O` (for instance `R = ℤ_[p]` and `O = ℤ_[p]` equipped
  with an archimedean valuation `|σ(·)|_∞`), scalar multiplication is discontinuous
  (`not_continuousSMul_of_not_tendsto_smul_one`) and `R`-valued measures need not extend to `O`.
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

* `AbstractMeasure.algebraMapContinuousMap`: `algebraMap R O` bundled as an element of `C(R, O)`.
* `AbstractMeasure.scalarExtend`: the semilinear extension `D(X, R) →ₛₗ[algebraMap R O] D(X, O)`.
* `AbstractMeasure.mapCoeff`: the additive pushforward `D(X, O) →+ D(X, R)` along an `R`-linear
  functional `O →ₗ[R] R`.
* `AbstractMeasure.baseChange`: the `O`-linear isomorphism `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.
* `AbstractMeasure.scalarExtendRingHom`: `scalarExtend` on a locally compact monoid as a ring
  homomorphism `D(G, R) →+* D(G, O)`.
* `AbstractMeasure.baseChangeAlgEquiv`: the `O`-algebra isomorphism
  `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` for convolution algebras on a locally compact monoid `G`.
* `AbstractMeasure.completedGroupAlgebraEquivOfProjective`: the `O`-algebra isomorphism
  `D(Γ, O) ≃ₐ[O] O[[Γ]]` transferred from bijectivity of `toCompletedGroupAlgebra` over `R`.

## Main results

* `AbstractMeasure.ext_comp_algebraMap`, `AbstractMeasure.ext_of_basis`: an `O`-valued measure is
  determined by its values on `algebraMap R O ∘ f` (`f ∈ C(X, R)`), or by its basis-coordinate
  measures in `D(X, R)`.
* `AbstractMeasure.scalarExtend_apply_comp`, `AbstractMeasure.eq_scalarExtend_of_apply_comp`,
  `AbstractMeasure.existsUnique_apply_comp_algebraMap`: defining evaluation and uniqueness of
  `scalarExtend`.
* `AbstractMeasure.eq_sum_smul_scalarExtend_of_basis`: expansion of any `ν ∈ D(X, O)` in terms of a
  finite `R`-basis of `O` and `mapCoeff`.
* `AbstractMeasure.exists_baseChange_algEquiv`: existence of the convolution `O`-algebra base
  change isomorphism over a compact base ring `R` for Hausdorff `O` with `ContinuousSMul R O`.
* `AbstractMeasure.toCompletedGroupAlgebra_surjective_of_projective`,
  `AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak_of_projective`: transfer of
  surjectivity and weak-topology homeomorphism for `toCompletedGroupAlgebra`.
* `AbstractMeasure.extendCoefficients_scalarExtend`,
  `AbstractMeasure.extendCoefficients_baseChange_tmul`,
  `AbstractMeasure.extendCoefficients_eq_sum_of_basis`: compatibility with `extendCoefficients` on
  extended measures, pure tensors, and arbitrary measures via a finite basis.
* `AbstractMeasure.not_continuousSMul_of_not_tendsto_smul_one`: topological obstruction to
  `ContinuousSMul R O` when sequences tending to `0` in `R` fail to send `1 : O` to `0`.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, Proposition 3.16 and Remark 3.28.
-/

public noncomputable section

open ContinuousMap TensorProduct Topology TauCeti

namespace AbstractMeasure

section AlgebraMap

variable (R O : Type*) [CommSemiring R] [TopologicalSpace R]
  [Semiring O] [TopologicalSpace O] [Algebra R O] [ContinuousSMul R O]

/-- `algebraMap R O` bundled as a continuous map `C(R, O)` whenever `O` has continuous `R`-scalar
multiplication. -/
def algebraMapContinuousMap : C(R, O) :=
  ⟨algebraMap R O, continuous_algebraMap R O⟩

@[simp]
theorem algebraMapContinuousMap_apply (r : R) :
    algebraMapContinuousMap R O r = algebraMap R O r :=
  (rfl)

end AlgebraMap

section TopologicalSpace

variable {X : Type*} [TopologicalSpace X]
  (R O : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace O] [IsTopologicalRing O]
  [IsModuleTopology R O] in
private def projDualN : ℕ :=
  (Module.Finite.exists_comp_eq_id_of_projective R O).choose

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace O] [IsTopologicalRing O]
  [IsModuleTopology R O] in
private def projDualF : (Fin (projDualN R O) → R) →ₗ[R] O :=
  (Module.Finite.exists_comp_eq_id_of_projective R O).choose_spec.choose

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace O] [IsTopologicalRing O]
  [IsModuleTopology R O] in
private def projDualG : O →ₗ[R] Fin (projDualN R O) → R :=
  (Module.Finite.exists_comp_eq_id_of_projective R O).choose_spec.choose_spec.choose

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace O] [IsTopologicalRing O]
  [IsModuleTopology R O] in
private theorem projDual_sum (a : O) :
    ∑ i : Fin (projDualN R O), projDualG R O a i • projDualF R O (Pi.single i 1) = a := by
  have ha := LinearMap.congr_fun
    (Module.Finite.exists_comp_eq_id_of_projective R O).choose_spec.choose_spec.choose_spec.2.2 a
  change projDualF R O (projDualG R O a) = a at ha
  have hsingle : projDualG R O a =
      ∑ i : Fin (projDualN R O), projDualG R O a i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  rw [hsingle, map_sum] at ha
  simpa only [map_smul] using ha

omit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace O] [IsTopologicalRing O]
  [IsModuleTopology R O] in
private def projCoordLinearMap (i : Fin (projDualN R O)) : O →ₗ[R] R :=
  (LinearMap.proj i).comp (projDualG R O)

omit [IsTopologicalRing O] in
private def projCoordContinuousMap (i : Fin (projDualN R O)) : C(O, R) :=
  ⟨projCoordLinearMap R O i, IsModuleTopology.continuous_of_linearMap (projCoordLinearMap R O i)⟩

omit [IsTopologicalRing O] in
private theorem projCoordContinuousMap_apply (i : Fin (projDualN R O)) (a : O) :
    projCoordContinuousMap R O i a = projDualG R O a i :=
  (rfl)

private theorem continuousMap_eq_sum_projCoord (F : C(X, O)) :
    F = ∑ i : Fin (projDualN R O),
      projDualF R O (Pi.single i 1) •
        ((algebraMapContinuousMap R O).comp ((projCoordContinuousMap R O i).comp F)) := by
  ext x
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.comp_apply, algebraMapContinuousMap_apply, projCoordContinuousMap_apply,
    smul_eq_mul]
  have hcomm : ∀ b : O, ∀ r : R, b * algebraMap R O r = r • b :=
    fun b r ↦ by rw [Algebra.smul_def, mul_comm]
  simp_rw [hcomm]
  exact (projDual_sum R O (F x)).symm

/-- Two `O`-valued measures agreeing on every test function of the form `algebraMap R O ∘ f`
(`f ∈ C(X, R)`) are equal. -/
theorem ext_comp_algebraMap {ν₁ ν₂ : D(X, O)}
    (h : ∀ f : C(X, R),
      ν₁ ((algebraMapContinuousMap R O).comp f) = ν₂ ((algebraMapContinuousMap R O).comp f)) :
    ν₁ = ν₂ := by
  ext F
  rw [continuousMap_eq_sum_projCoord R O F, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, map_smul, h]

private theorem projCoord_comp_smul (i : Fin (projDualN R O)) (a : O) (F : C(X, O)) :
    (projCoordContinuousMap R O i).comp (a • F) =
      ∑ j : Fin (projDualN R O),
        projCoordLinearMap R O i (a * projDualF R O (Pi.single j 1)) •
          ((projCoordContinuousMap R O j).comp F) := by
  ext x
  simp only [ContinuousMap.comp_apply, ContinuousMap.smul_apply, smul_eq_mul,
    projCoordContinuousMap_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  change projCoordLinearMap R O i (a * F x) = _
  conv_lhs => rw [← projDual_sum R O (F x)]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

private def scalarExtendCLM (μ : D(X, R)) : C(X, O) →L[O] O where
  toFun F := ∑ i : Fin (projDualN R O),
    μ ((projCoordContinuousMap R O i).comp F) • projDualF R O (Pi.single i 1)
  map_add' F₁ F₂ := by
    have hcomp : ∀ i, (projCoordContinuousMap R O i).comp (F₁ + F₂) =
        (projCoordContinuousMap R O i).comp F₁ + (projCoordContinuousMap R O i).comp F₂ :=
      fun i ↦ by ext x; exact map_add (projCoordLinearMap R O i) (F₁ x) (F₂ x)
    simp [hcomp, add_smul, Finset.sum_add_distrib]
  map_smul' a F := by
    simp only [RingHom.id_apply, projCoord_comp_smul, map_sum, map_smul, smul_eq_mul,
      Finset.sum_smul]
    simp_rw [mul_comm (projCoordLinearMap R O _ _) _, ← smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum]
    have hsum : ∀ j : Fin (projDualN R O),
        ∑ x : Fin (projDualN R O),
          projCoordLinearMap R O x (a * projDualF R O (Pi.single j 1)) •
            projDualF R O (Pi.single x 1) =
          a * projDualF R O (Pi.single j 1) :=
      fun j ↦ projDual_sum R O (a * projDualF R O (Pi.single j 1))
    simp_rw [hsum, Finset.mul_sum, Algebra.mul_smul_comm]
  cont := continuous_finsetSum _ fun i _ ↦
    ((map_continuous μ).comp
      (ContinuousMap.continuous_postcomp (projCoordContinuousMap R O i))).smul
      continuous_const

/-- **Scalar extension of abstract measures.** When `O` carries the `R`-module topology and is
finitely generated and projective over `R`, `scalarExtend R O` extends every `R`-valued measure
`μ ∈ D(X, R)` to the unique `O`-valued measure sending `algebraMap R O ∘ f` to
`algebraMap R O (μ f)` for all `f ∈ C(X, R)` (`scalarExtend_apply_comp`,
`eq_scalarExtend_of_apply_comp`). -/
def scalarExtend : D(X, R) →ₛₗ[algebraMap R O] D(X, O) where
  toFun μ := toCLMEquiv.symm (scalarExtendCLM R O μ)
  map_add' μ₁ μ₂ := ext fun F ↦ by
    simp [scalarExtendCLM, add_smul, Finset.sum_add_distrib]
  map_smul' r μ := ext fun F ↦ by
    simp only [coe_symm_toCLMEquiv, scalarExtendCLM, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul]

/-- Extending scalars of `μ` integrates `algebraMap R O ∘ f` to `algebraMap R O (μ f)`. -/
@[simp]
theorem scalarExtend_apply_comp (μ : D(X, R)) (f : C(X, R)) :
    scalarExtend R O μ ((algebraMapContinuousMap R O).comp f) = algebraMap R O (μ f) := by
  have hcomp : ∀ i : Fin (projDualN R O),
      (projCoordContinuousMap R O i).comp ((algebraMapContinuousMap R O).comp f) =
        projDualG R O 1 i • f := fun i ↦ by
    ext x
    simp only [ContinuousMap.comp_apply, algebraMapContinuousMap_apply,
      projCoordContinuousMap_apply, ContinuousMap.smul_apply, smul_eq_mul]
    change projCoordLinearMap R O i (algebraMap R O (f x)) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]
    rfl
  simp only [scalarExtend, LinearMap.coe_mk, AddHom.coe_mk, coe_symm_toCLMEquiv, scalarExtendCLM,
    ContinuousLinearMap.coe_mk', hcomp, map_smul, smul_eq_mul]
  simp_rw [mul_comm (projDualG R O 1 _) (μ f), ← smul_smul, ← Finset.smul_sum]
  rw [projDual_sum R O 1, ← Algebra.algebraMap_eq_smul_one]

variable {R O}

/-- Any `O`-valued measure sending `algebraMap R O ∘ f` to `algebraMap R O (μ f)` for all
`f ∈ C(X, R)` equals `scalarExtend R O μ`. -/
theorem eq_scalarExtend_of_apply_comp {μ : D(X, R)} {ν : D(X, O)}
    (hν : ∀ f : C(X, R), ν ((algebraMapContinuousMap R O).comp f) = algebraMap R O (μ f)) :
    ν = scalarExtend R O μ :=
  ext_comp_algebraMap R O fun f ↦ (hν f).trans (scalarExtend_apply_comp R O μ f).symm

/-- For every `μ ∈ D(X, R)` there is a unique `O`-valued measure integrating `algebraMap R O ∘ f` to
`algebraMap R O (μ f)` for all `f ∈ C(X, R)`. -/
theorem existsUnique_apply_comp_algebraMap (μ : D(X, R)) :
    ∃! ν : D(X, O),
      ∀ f : C(X, R), ν ((algebraMapContinuousMap R O).comp f) = algebraMap R O (μ f) :=
  ⟨scalarExtend R O μ, scalarExtend_apply_comp R O μ, fun _ hν ↦ eq_scalarExtend_of_apply_comp hν⟩

/-- Scalar extension sends Dirac measures to Dirac measures. -/
@[simp]
theorem scalarExtend_dirac (x : X) :
    scalarExtend R O (dirac R x) = dirac O x :=
  (eq_scalarExtend_of_apply_comp fun _ ↦ by simp).symm

/-- Extending scalars from `R` to `R` itself is the identity map. -/
@[simp]
theorem scalarExtend_self :
    scalarExtend R R (X := X) = LinearMap.id :=
  LinearMap.ext fun μ ↦ (eq_scalarExtend_of_apply_comp fun f ↦ by
    change μ f = RingHom.id R (μ f)
    rfl).symm

/-- Scalar extension commutes with pushforward along continuous maps. -/
@[simp]
theorem scalarExtend_map {Y : Type*} [TopologicalSpace Y] (φ : C(X, Y)) (μ : D(X, R)) :
    scalarExtend R O (map φ μ) = map φ (scalarExtend R O μ) :=
  (eq_scalarExtend_of_apply_comp fun f ↦ by
    simp only [map_apply]
    rw [ContinuousMap.comp_assoc, scalarExtend_apply_comp]).symm

/-- The finite projections of `scalarExtend R O μ` are obtained from those of `μ` by applying
`algebraMap R O` to each fibre coefficient. -/
@[simp]
theorem finiteProjection_scalarExtend {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] (q : C(X, A)) (μ : D(X, R)) :
    finiteProjection q (scalarExtend R O μ) =
      (finiteProjection q μ).mapRange (algebraMap R O) (map_zero _) := by
  ext a
  rw [finiteProjection_apply, Finsupp.mapRange_apply, finiteProjection_apply]
  have hfib : fiberIndicator (R := O) q a =
      (algebraMapContinuousMap R O).comp (fiberIndicator (R := R) q a) := by
    ext x
    classical
    by_cases hx : q x = a <;> simp [fiberIndicator_apply, hx]
  rw [hfib, scalarExtend_apply_comp]

/-! ### Coefficient functionals and module base change `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)` -/

omit [Module.Projective R O] [Module.Finite R O] in
/-- Push an `O`-valued measure along an `R`-linear functional `ℓ : O →ₗ[R] R` on coefficients,
sending `f ∈ C(X, R)` to `ℓ (ν (algebraMap R O ∘ f))`. Continuity holds automatically when `O`
carries the `R`-module topology. -/
def mapCoeff (ℓ : O →ₗ[R] R) : D(X, O) →+ D(X, R) where
  toFun ν := toCLMEquiv.symm
    { toFun := fun f ↦ ℓ (ν ((algebraMapContinuousMap R O).comp f))
      map_add' := fun f₁ f₂ ↦ by
        have hcomp : (algebraMapContinuousMap R O).comp (f₁ + f₂) =
            (algebraMapContinuousMap R O).comp f₁ + (algebraMapContinuousMap R O).comp f₂ := by
          ext x
          simp
        rw [hcomp, map_add, map_add]
      map_smul' := fun r f ↦ by
        have hcomp : (algebraMapContinuousMap R O).comp (r • f) =
            algebraMap R O r • (algebraMapContinuousMap R O).comp f := by
          ext x
          simp [Algebra.smul_def]
        rw [hcomp, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, RingHom.id_apply]
      cont := (IsModuleTopology.continuous_of_linearMap ℓ).comp
        ((map_continuous ν).comp
          (ContinuousMap.continuous_postcomp (algebraMapContinuousMap R O))) }
  map_zero' := ext fun f ↦ by simp [← coe_toCLMEquiv]
  map_add' ν₁ ν₂ := ext fun f ↦ by simp

omit [Module.Projective R O] [Module.Finite R O] in
@[simp]
theorem mapCoeff_apply (ℓ : O →ₗ[R] R) (ν : D(X, O)) (f : C(X, R)) :
    mapCoeff ℓ ν f = ℓ (ν ((algebraMapContinuousMap R O).comp f)) := by
  simp [mapCoeff]

@[simp]
theorem mapCoeff_smul_scalarExtend (ℓ : O →ₗ[R] R) (a : O) (μ : D(X, R)) :
    mapCoeff ℓ (a • scalarExtend R O μ) = ℓ a • μ := by
  ext f
  rw [mapCoeff_apply, _root_.smul_apply, scalarExtend_apply_comp, smul_eq_mul, mul_comm,
    ← Algebra.smul_def, map_smul, _root_.smul_apply, smul_eq_mul, mul_comm, ← smul_eq_mul]

/-- Given a finite `R`-basis `b` of `O`, every `O`-valued measure `ν` decomposes uniquely into its
`R`-valued coordinate measures `mapCoeff (b.coord i) ν`. -/
theorem eq_sum_smul_scalarExtend_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (ν : D(X, O)) :
    ν = ∑ i : ι, b i • scalarExtend R O (mapCoeff (b.coord i) ν) := by
  refine ext_comp_algebraMap R O fun f ↦ ?_
  rw [← coe_toCLMEquiv (∑ i : ι, _), map_sum, _root_.sum_apply]
  simp_rw [coe_toCLMEquiv, _root_.smul_apply, scalarExtend_apply_comp, mapCoeff_apply,
    Module.Basis.coord_apply, smul_eq_mul, mul_comm (b _), ← Algebra.smul_def]
  exact (b.sum_repr (ν ((algebraMapContinuousMap R O).comp f))).symm

omit [Module.Projective R O] [Module.Finite R O] in
/-- Given a finite `R`-basis `b` of `O`, two `O`-valued measures are equal whenever all of their
`b`-coordinate measures in `D(X, R)` agree. -/
theorem ext_of_basis {ι : Type*} [Finite ι] (b : Module.Basis ι R O) {ν₁ ν₂ : D(X, O)}
    (h : ∀ i : ι, mapCoeff (b.coord i) ν₁ = mapCoeff (b.coord i) ν₂) :
    ν₁ = ν₂ := by
  let _ := Fintype.ofFinite ι
  have := Module.Projective.of_basis b
  have := Module.Finite.of_basis b
  rw [eq_sum_smul_scalarExtend_of_basis b ν₁, eq_sum_smul_scalarExtend_of_basis b ν₂]
  simp_rw [h]

variable (R O) in
/-- The forward `O`-linear map `O ⊗[R] D(X, R) →ₗ[O] D(X, O)` sending `a ⊗ₜ μ` to
`a • scalarExtend R O μ`. -/
private def baseChangeLinearMap : O ⊗[R] D(X, R) →ₗ[O] D(X, O) :=
  letI : Module R D(X, O) := Module.compHom D(X, O) (algebraMap R O)
  letI : IsScalarTower R O D(X, O) := IsScalarTower.of_compHom R O D(X, O)
  LinearMap.liftBaseChange O
    { toFun := scalarExtend R O
      map_add' := map_add _
      map_smul' := fun r μ ↦ map_smulₛₗ (scalarExtend R O) r μ }

private def baseChangeInvFun (ν : D(X, O)) : O ⊗[R] D(X, R) :=
  ∑ i : Fin (projDualN R O),
    projDualF R O (Pi.single i 1) ⊗ₜ[R] mapCoeff (projCoordLinearMap R O i) ν

private theorem baseChangeInvFun_leftInverse :
    Function.LeftInverse (baseChangeInvFun (X := X) (R := R) (O := O))
      (baseChangeLinearMap R O) := by
  have hadd : ∀ u v : D(X, O),
      baseChangeInvFun (R := R) (u + v) = baseChangeInvFun u + baseChangeInvFun v :=
    fun u v ↦ by simp [baseChangeInvFun, tmul_add, Finset.sum_add_distrib]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a μ =>
    change baseChangeInvFun (a • scalarExtend R O μ) = a ⊗ₜ[R] μ
    simp only [baseChangeInvFun, mapCoeff_smul_scalarExtend, ← smul_tmul, ← sum_tmul]
    exact congrArg (· ⊗ₜ[R] μ) (projDual_sum R O a)
  | add z₁ z₂ hz₁ hz₂ =>
    rw [map_add, hadd, hz₁, hz₂]

private theorem baseChangeInvFun_rightInverse :
    Function.RightInverse (baseChangeInvFun (X := X) (R := R) (O := O))
      (baseChangeLinearMap R O) := by
  intro ν
  refine ext_comp_algebraMap R O fun f ↦ ?_
  rw [← coe_toCLMEquiv, baseChangeInvFun, map_sum, map_sum, _root_.sum_apply]
  simp_rw [coe_toCLMEquiv]
  have hterm : ∀ i : Fin (projDualN R O),
      baseChangeLinearMap R O
          (projDualF R O (Pi.single i 1) ⊗ₜ[R] mapCoeff (projCoordLinearMap R O i) ν)
          ((algebraMapContinuousMap R O).comp f) =
        projDualG R O (ν ((algebraMapContinuousMap R O).comp f)) i •
          projDualF R O (Pi.single i 1) := fun i ↦ by
    change (projDualF R O (Pi.single i 1) •
      scalarExtend R O (mapCoeff (projCoordLinearMap R O i) ν))
        ((algebraMapContinuousMap R O).comp f) = _
    rw [_root_.smul_apply, scalarExtend_apply_comp, mapCoeff_apply, smul_eq_mul, mul_comm,
      ← Algebra.smul_def]
    rfl
  simp_rw [hterm]
  exact projDual_sum R O _

variable (R O) in
/-- **Base change of abstract measures.** When `O` carries the `R`-module topology and is finitely
generated and projective over `R`, `baseChange R O` identifies `O ⊗[R] D(X, R)` with `D(X, O)` as an
`O`-module, sending `a ⊗ₜ μ` to `a • scalarExtend R O μ`. -/
def baseChange : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O) :=
  { baseChangeLinearMap R O with
    invFun := baseChangeInvFun
    left_inv := baseChangeInvFun_leftInverse
    right_inv := baseChangeInvFun_rightInverse }

@[simp]
theorem baseChange_tmul (a : O) (μ : D(X, R)) :
    baseChange R O (a ⊗ₜ[R] μ) = a • scalarExtend R O μ :=
  (rfl)

theorem baseChange_tmul_dirac (a : O) (x : X) :
    baseChange R O (a ⊗ₜ[R] dirac R x) = a • dirac O x := by
  simp

@[simp]
theorem baseChange_symm_scalarExtend (μ : D(X, R)) :
    (baseChange R O).symm (scalarExtend R O μ) = 1 ⊗ₜ[R] μ := by
  apply (baseChange R O).injective
  simp

@[simp]
theorem baseChange_symm_dirac (x : X) :
    (baseChange R O).symm (dirac O x) = 1 ⊗ₜ[R] dirac R x := by
  rw [← scalarExtend_dirac (R := R) (O := O), baseChange_symm_scalarExtend]

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
  intro h
  apply hab
  have h1 := congrArg (fun ν : D(X, O) ↦ ν 1) h
  simpa using h1

end TopologicalSpace

section Monoid

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] [LocallyCompactSpace G]
  {R O : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

omit [ContinuousMul G] [LocallyCompactSpace G] in
@[simp]
theorem scalarExtend_one :
    scalarExtend R O (1 : D(G, R)) = 1 :=
  scalarExtend_dirac 1

omit [LocallyCompactSpace G] in
/-- Scalar extension commutes with right convolution of test functions. -/
theorem convolveFunRight_scalarExtend_comp (ν : D(G, R)) (f : C(G, R)) :
    convolveFunRight (scalarExtend R O ν) ((algebraMapContinuousMap R O).comp f) =
      (algebraMapContinuousMap R O).comp (convolveFunRight ν f) := by
  ext x
  rw [convolveFunRight_apply, ContinuousMap.comp_apply, algebraMapContinuousMap_apply,
    convolveFunRight_apply]
  exact scalarExtend_apply_comp R O ν ⟨fun y ↦ f (x * y), by fun_prop⟩

/-- Scalar extension preserves convolution of measures on a locally compact topological monoid. -/
@[simp]
theorem scalarExtend_mul (μ ν : D(G, R)) :
    scalarExtend R O (μ * ν) = scalarExtend R O μ * scalarExtend R O ν :=
  (eq_scalarExtend_of_apply_comp fun f ↦ by
    rw [mul_apply, convolveFunRight_scalarExtend_comp, scalarExtend_apply_comp, mul_apply]).symm

variable (R O) in
/-- Scalar extension on a locally compact monoid, bundled as a ring homomorphism
`D(G, R) →+* D(G, O)`. -/
def scalarExtendRingHom : D(G, R) →+* D(G, O) where
  toFun := scalarExtend R O
  map_one' := scalarExtend_one
  map_mul' := scalarExtend_mul
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
theorem coe_scalarExtendRingHom :
    ⇑(scalarExtendRingHom R O (G := G)) = scalarExtend R O :=
  (rfl)

@[simp]
theorem scalarExtendRingHom_algebraMap (r : R) :
    scalarExtendRingHom R O (algebraMap R D(G, R) r) = algebraMap O D(G, O) (algebraMap R O r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, coe_scalarExtendRingHom,
    map_smulₛₗ, scalarExtend_one]

variable (R O) in
/-- **Convolution-algebra base change of abstract measures.** On a locally compact topological
monoid `G`, when `O` carries the `R`-module topology and is finitely generated and projective over
`R`, `baseChangeAlgEquiv R O` identifies `O ⊗[R] D(G, R)` with `D(G, O)` as an `O`-algebra. -/
def baseChangeAlgEquiv : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (baseChange R O)
    (fun a₁ a₂ μ₁ μ₂ ↦ by
      simp only [baseChange_tmul]
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, scalarExtend_mul, map_mul]
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
    baseChangeAlgEquiv R O (a ⊗ₜ[R] μ) = a • scalarExtend R O μ :=
  (rfl)

theorem baseChangeAlgEquiv_tmul_dirac (a : O) (x : G) :
    baseChangeAlgEquiv R O (a ⊗ₜ[R] dirac R x) = a • dirac O x :=
  baseChange_tmul_dirac a x

@[simp]
theorem baseChangeAlgEquiv_symm_scalarExtend (μ : D(G, R)) :
    (baseChangeAlgEquiv R O).symm (scalarExtend R O μ) = 1 ⊗ₜ[R] μ :=
  baseChange_symm_scalarExtend μ

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

/-- Over a compact base ring `R`, any Hausdorff topological `R`-algebra `O` with continuous
`R`-scalar multiplication that is finitely generated and projective over `R` automatically carries
the `R`-module topology, giving the `O`-algebra isomorphism `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` sending
`a ⊗ₜ dirac R x` to `a • dirac O x`. -/
theorem exists_baseChange_algEquiv {R' O' : Type*} [CommRing R'] [TopologicalSpace R']
    [IsTopologicalRing R'] [CompactSpace R'] [CommRing O'] [TopologicalSpace O']
    [IsTopologicalRing O'] [T2Space O'] [Algebra R' O'] [ContinuousSMul R' O']
    [Module.Projective R' O'] [Module.Finite R' O'] :
    ∃ e : O' ⊗[R'] D(G, R') ≃ₐ[O'] D(G, O'),
      ∀ (a : O') (x : G), e (a ⊗ₜ[R'] dirac R' x) = a • dirac O' x := by
  have := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := R') (M := O')
  exact ⟨baseChangeAlgEquiv R' O', baseChangeAlgEquiv_tmul_dirac⟩

end Monoid

section CompletedGroupAlgebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
  {R O : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

section ContinuousMul

variable [ContinuousMul Γ] [LocallyCompactSpace Γ]

/-- `toCompletedGroupAlgebra` intertwines `scalarExtend R O` on measures with
`completedGroupAlgebra.mapRingHom Γ (algebraMap R O)`. -/
@[simp]
theorem toCompletedGroupAlgebra_scalarExtend (μ : D(Γ, R)) :
    toCompletedGroupAlgebra (scalarExtend R O μ) =
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
theorem toCompletedGroupAlgebra_surjective_of_projective
    (hs : Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  have hmap : Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id O O)
        (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a x =>
      obtain ⟨μ, rfl⟩ := hs x
      exact ⟨a ⊗ₜ[R] μ, by simp⟩
    | add w₁ w₂ hw₁ hw₂ =>
      obtain ⟨z₁, hz₁⟩ := hw₁
      obtain ⟨z₂, hz₂⟩ := hw₂
      exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂]⟩
  intro y
  obtain ⟨z, hz⟩ := hmap ((completedGroupAlgebra.scalarTensorEquiv R O Γ).symm y)
  refine ⟨baseChangeAlgEquiv R O z, ?_⟩
  rw [toCompletedGroupAlgebra_baseChangeAlgEquiv, hz, AlgEquiv.apply_symm_apply]

/-- If `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` is bijective, then
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is an `O`-algebra isomorphism. -/
def completedGroupAlgebraEquivOfProjective
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) :
    D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective toCompletedGroupAlgebra
    ⟨fun μ₁ μ₂ h ↦ (baseChangeAlgEquiv R O).symm.injective <| by
        have hinj : Function.Injective
            (Algebra.TensorProduct.map (AlgHom.id O O)
              (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ)) := by
          let eR : D(Γ, R) ≃ₗ[R] completedGroupAlgebra R Γ :=
            LinearEquiv.ofBijective toCompletedGroupAlgebra.toLinearMap hb
          exact (LinearEquiv.lTensor (M := O) eR).injective
        apply hinj
        apply (completedGroupAlgebra.scalarTensorEquiv R O Γ).injective
        rw [← toCompletedGroupAlgebra_baseChangeAlgEquiv,
          ← toCompletedGroupAlgebra_baseChangeAlgEquiv,
          AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, h],
      toCompletedGroupAlgebra_surjective_of_projective hb.2⟩

@[simp]
theorem completedGroupAlgebraEquivOfProjective_apply
    (hb : Function.Bijective
      (toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] completedGroupAlgebra R Γ))
    (μ : D(Γ, O)) :
    completedGroupAlgebraEquivOfProjective hb μ = toCompletedGroupAlgebra μ :=
  AlgEquiv.ofBijective_apply _ _ _

omit [Module.Projective R O] [Module.Finite R O] in
/-- `toCompletedGroupAlgebra` intertwines `mapCoeff ℓ` on measures with
`completedGroupAlgebra.mapAddMonoidHom` along `ℓ`. -/
@[simp]
theorem toCompletedGroupAlgebra_mapCoeff (ℓ : O →ₗ[R] R) (ν : D(Γ, O)) :
    toCompletedGroupAlgebra (mapCoeff ℓ ν) =
      completedGroupAlgebra.mapAddMonoidHom Γ ℓ.toAddMonoidHom (toCompletedGroupAlgebra ν) := by
  ext U q
  simp only [proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_coeff,
    finiteProjection_apply, mapCoeff_apply, completedGroupAlgebra.coeff_proj_mapAddMonoidHom,
    LinearMap.toAddMonoidHom_coe]
  congr 2
  ext x
  classical
  by_cases hx : (x : Γ ⧸ U.toSubgroup) = q <;> simp [fiberIndicator_apply, hx]

private theorem apply_eq_sum_projDual_of_leftInverse
    (inv : completedGroupAlgebra R Γ → D(Γ, R))
    (hinv : Function.LeftInverse inv toCompletedGroupAlgebra)
    (F : C(Γ, O)) (ν : D(Γ, O)) :
    ν F = ∑ j : Fin (projDualN R O), projDualF R O (Pi.single j 1) *
      ∑ i : Fin (projDualN R O),
        (inv (completedGroupAlgebra.mapAddMonoidHom Γ
          (projCoordLinearMap R O i).toAddMonoidHom (toCompletedGroupAlgebra ν))
            ((projCoordContinuousMap R O j).comp F)) •
          projDualF R O (Pi.single i 1) := by
  conv_lhs => rw [continuousMap_eq_sum_projCoord R O F]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  conv_lhs =>
    rw [← projDual_sum R O
      (ν ((algebraMapContinuousMap R O).comp ((projCoordContinuousMap R O j).comp F)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  change projCoordLinearMap R O i _ = _
  rw [← mapCoeff_apply (projCoordLinearMap R O i), ← toCompletedGroupAlgebra_mapCoeff, hinv _]

end ContinuousMul

section Normed

/-- If `toCompletedGroupAlgebra : D(Γ, R) →ₐ[R] R[[Γ]]` is a homeomorphism from the weak topology to
the inverse-limit topology, then so is `toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` for any
normed `R`-algebra `O` carrying the `R`-module topology that is finitely generated and projective
over `R`. -/
theorem isHomeomorph_toCompletedGroupAlgebra_weak_of_projective
    [ContinuousMul Γ] [LocallyCompactSpace Γ]
    {R' O' : Type*} [NormedCommRing R'] [NormedCommRing O'] [Algebra R' O']
    [IsModuleTopology R' O'] [Module.Projective R' O'] [Module.Finite R' O']
    (hh : @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := R') (E := R')) _
      (toCompletedGroupAlgebra : D(Γ, R') →ₐ[R'] completedGroupAlgebra R' Γ)) :
    @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := O') (E := O')) _
      (toCompletedGroupAlgebra : D(Γ, O') →ₐ[O'] completedGroupAlgebra O' Γ) := by
  have := IsModuleTopology.toContinuousSMul R' O'
  let tDR : TopologicalSpace D(Γ, R') := WeakTopology (X := Γ) (R := R') (E := R')
  let eR : completedGroupAlgebra R' Γ ≃ₜ D(Γ, R') :=
    (@IsHomeomorph.homeomorph _ _ tDR _ _ hh).symm
  have heR : Function.LeftInverse eR toCompletedGroupAlgebra :=
    (@IsHomeomorph.homeomorph _ _ tDR _ _ hh).left_inv
  have heval (F : C(Γ, O')) :
      Continuous[.induced toCompletedGroupAlgebra inferInstance, _]
        fun ν : D(Γ, O') ↦ ν F := by
    let : TopologicalSpace D(Γ, O') := .induced toCompletedGroupAlgebra inferInstance
    simp_rw [apply_eq_sum_projDual_of_leftInverse eR heR F]
    refine continuous_finsetSum _ fun j _ ↦ continuous_const.mul <|
      continuous_finsetSum _ fun i _ ↦ ?_
    have hmap : Continuous fun ν : D(Γ, O') ↦
        eR (completedGroupAlgebra.mapAddMonoidHom Γ
          (projCoordLinearMap R' O' i).toAddMonoidHom (toCompletedGroupAlgebra ν)) :=
      eR.continuous.comp <|
        (completedGroupAlgebra.continuous_mapAddMonoidHom
          (IsModuleTopology.continuous_of_linearMap (projCoordLinearMap R' O' i))).comp
          continuous_induced_dom
    have hevR : @Continuous D(Γ, R') R' tDR _
        (fun μ : D(Γ, R') ↦ μ ((projCoordContinuousMap R' O' j).comp F)) :=
      (continuous_apply ((projCoordContinuousMap R' O' j).comp F)).comp continuous_induced_dom
    exact (hevR.comp hmap).smul continuous_const
  have hle : .induced toCompletedGroupAlgebra inferInstance ≤
      WeakTopology (X := Γ) (R := O') (E := O') := by
    let : TopologicalSpace D(Γ, O') := .induced toCompletedGroupAlgebra inferInstance
    exact continuous_iff_le_induced.mp (continuous_pi heval)
  let : TopologicalSpace D(Γ, O') := WeakTopology (X := Γ) (R := O') (E := O')
  have hind : IsInducing
      (toCompletedGroupAlgebra : D(Γ, O') →ₐ[O'] completedGroupAlgebra O' Γ) :=
    ⟨le_antisymm (continuous_iff_le_induced.mp continuous_toCompletedGroupAlgebra) hle⟩
  have hbij := (completedGroupAlgebraEquivOfProjective (R := R') (O := O') hh.bijective).bijective
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hind, hbij.1⟩, hbij.2⟩

end Normed

end CompletedGroupAlgebra

section ExtendCoefficients

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
  {R O K : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]
  [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Extending coefficients from `O` to `K` after `scalarExtend R O` agrees with extending
coefficients directly from `R` to `K` along `j.comp (algebraMap R O)`. No continuity assumption on
`j` is needed. -/
@[simp]
theorem extendCoefficients_scalarExtend (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (μ : D(X, R)) :
    extendCoefficients j hj (scalarExtend R O μ) =
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
  rw [baseChange_tmul, extendCoefficients_smul, extendCoefficients_scalarExtend]

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
  conv_lhs => rw [eq_sum_smul_scalarExtend_of_basis b ν]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [extendCoefficients_smul, extendCoefficients_scalarExtend]

end ExtendCoefficients

section ContinuousSMulObstruction

/-- If a sequence `r : ℕ → R` tends to `0` in `R` while `r n • (1 : O)` does not tend to `0` in `O`,
then `O` cannot have continuous `R`-scalar multiplication. In particular, equipping `ℤ_[p]` with an
archimedean topology in which `p ^ n` does not tend to `0` prevents `ContinuousSMul ℤ_[p] O`. -/
theorem not_continuousSMul_of_not_tendsto_smul_one {R O : Type*} [Semiring R] [TopologicalSpace R]
    [Semiring O] [TopologicalSpace O] [Module R O] {r : ℕ → R}
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (h1 : ¬ Filter.Tendsto (fun n : ℕ ↦ r n • (1 : O)) Filter.atTop (nhds 0)) :
    ¬ ContinuousSMul R O := by
  intro hsmul
  apply h1
  have hcont : Continuous (fun c : R ↦ c • (1 : O)) := continuous_id.smul continuous_const
  exact zero_smul R (1 : O) ▸ (hcont.tendsto 0).comp hr

end ContinuousSMulObstruction

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
  exact ⟨⟨completedGroupAlgebraEquivOfProjective (R := ℤ_[p]) (O := O)
      ⟨toCompletedGroupAlgebra_injective, toCompletedGroupAlgebra_surjective⟩⟩,
    isHomeomorph_toCompletedGroupAlgebra_weak_of_projective
      (isHomeomorph_toCompletedGroupAlgebra_weak (Γ := Γ) (p := p))⟩

-- Negative control: without `p ^ n • 1 → 0`, `ContinuousSMul ℤ_[p] O` fails.
example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O]
    (h : ¬ Filter.Tendsto (fun n : ℕ ↦ ((p : ℤ_[p]) ^ n) • (1 : O)) Filter.atTop (nhds 0)) :
    ¬ ContinuousSMul ℤ_[p] O :=
  not_continuousSMul_of_not_tendsto_smul_one
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      ((PadicInt.norm_p (p := p)).trans_lt
        (Padic.norm_p (p := p) ▸ Padic.norm_p_lt_one (p := p)))) h

end Examples

end AbstractMeasure
