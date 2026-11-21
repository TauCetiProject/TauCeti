/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.NumberTheory.Padics.Measure.FiniteProjection
public import TauCeti.Topology.Algebra.Module.AutomaticContinuity
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.LinearAlgebra.Dual.FiniteProjective
import TauCeti.NumberTheory.Padics.Measure.Dirac
import TauCeti.Topology.ContinuousMap.AutomaticContinuity

/-!
# Finite projective base change of abstract measures

Let `X` be a topological space, `R` a topological commutative ring, and `O` a topological
commutative `R`-algebra carrying the `R`-module topology (`IsModuleTopology R O`). Every
`R`-linear functional `l : O →ₗ[R] R` is then continuous
(`IsModuleTopology.continuous_of_linearMap`), inducing a basis-free scalar-retraction map
`mapScalars l : D(X, O) →+ D(X, R)` sending `ν` to `g ↦ l (ν (algebraMap R O ∘ g))`.

When `O` is finitely generated and projective over `R`, choosing a finite dual pair `(b_i, φ_i)`
for `O` over `R` from `TauCeti.exists_sum_dual_smul_eq` decomposes every continuous test function
`f ∈ C(X, O)` into `Σ_i b_i • (algebraMap R O ∘ φ_i ∘ f)`, allowing any `R`-valued measure
`μ ∈ D(X, R)` to be extended to an `O`-valued measure `extendScalars O μ ∈ D(X, O)`. Although
constructed via a dual pair, `extendScalars O μ` is uniquely determined by the identity
`extendScalars O μ (algebraMap R O ∘ g) = algebraMap R O (μ g)` for `g ∈ C(X, R)`
(`extendScalars_apply_comp_algebraMap`, `eq_extendScalars_iff`,
`existsUnique_apply_comp_algebraMap`). Pushing `O`-valued measures back along `φ_i` supplies the
two-sided inverse to the induced map from `O ⊗[R] D(X, R)`, yielding an `O`-linear isomorphism
`baseChangeLinearEquiv O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.

When `G` is a locally compact topological monoid (not necessarily commutative or compact),
`extendScalars O` respects Dirac units and right convolution, upgrading `baseChangeLinearEquiv O`
to an `O`-algebra isomorphism `baseChangeAlgEquiv O : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` sending
`a ⊗ₜ dirac R x` to `a • dirac O x`. Over a compact base ring `R` (such as `ℤ_p`), any Hausdorff
`R`-algebra `O` with continuous `R`-scalar multiplication that is finitely generated over `R`
automatically carries the `R`-module topology
(`TauCeti.isModuleTopology_of_finite_of_compactSpace`), giving `exists_baseChange_algEquiv`. On
`ℤ_p`, `mapScalars l` and `extendScalars O` act coefficientwise on the Amice transform
(`coeff_amiceTransform_mapScalars`, `amiceTransform_extendScalars`). The comparison with the
completed group algebra `O[[Γ]]` of a profinite group `Γ` is developed in
`TauCeti.NumberTheory.Padics.Measure.BaseChange.CompletedGroupAlgebra`.

Every hypothesis on `O` is necessary:
* `ContinuousSMul R O` / `IsModuleTopology R O` cannot be dropped: equipping `O = ℤ_p` with an
  archimedean norm `|ι(·)|` via an abstract field embedding `ι : ℚ_p → ℂ` produces a free rank-one
  normed `ℤ_p`-algebra on which the `ℤ_p`-measure `μ = ∑_{n ≥ 1} p^n δ_{p^n}` cannot extend to a
  continuous linear functional on `C(ℤ_p, O)`, because the indicator multiples
  `(p^m + 1)⁻¹ • 1_{p^m + p^{m + 1} ℤ_p}` tend uniformly to `0` in `C(ℤ_p, O)` while their putative
  integrals `p^m / (p^m + 1)` tend to `1`.
* `Module.Finite R O` cannot be dropped: for discrete `R = 𝔽_p`, discrete `O = 𝔽_p[T]`, and
  `X = ℤ_p`, elements of `O ⊗[R] D(X, R)` have bounded `T`-degree whereas `D(X, O)` contains
  measures whose clopen values have unbounded `T`-degree.
* `Module.Projective R O` cannot be dropped: for `R = 𝔽_p⟦x_0, x_1, …⟧` with the product topology,
  discrete `O = 𝔽_p`, and `X = ℤ_p`, `z = Σ_{n ≥ 1} x_n (δ_{p^n} - δ_0)` satisfies `1 ⊗ₜ z ≠ 0`
  in `O ⊗[R] D(X, R)` while mapping to `0` in `D(X, O)`.

## Main definitions

* `AbstractMeasure.mapScalars l`: the additive retraction `D(X, O) →+ D(X, R)` along `l : O →ₗ[R] R`
  when `O` carries the `R`-module topology.
* `AbstractMeasure.extendScalars O`: the `algebraMap R O`-semilinear extension map
  `D(X, R) →ₛₗ[algebraMap R O] D(X, O)`.
* `AbstractMeasure.baseChangeLinearEquiv O`: the `O`-linear isomorphism
  `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.
* `AbstractMeasure.extendScalarsRingHom O`: `extendScalars O` bundled as a ring homomorphism
  `D(G, R) →+* D(G, O)` on a locally compact topological monoid `G`.
* `AbstractMeasure.baseChangeAlgEquiv O`: the `O`-algebra isomorphism
  `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` on a locally compact topological monoid `G`.

## Main results

* `AbstractMeasure.ext_of_apply_comp_algebraMap`, `AbstractMeasure.ext_of_basis`: an `O`-valued
  measure is determined by its values on `algebraMap R O ∘ g` (`g ∈ C(X, R)`), or by its
  basis-coordinate measures in `D(X, R)`.
* `AbstractMeasure.mapScalars_smul_dirac`, `AbstractMeasure.mapScalars_mapScalars`,
  `AbstractMeasure.extendScalars_apply_comp_algebraMap`,
  `AbstractMeasure.existsUnique_apply_comp_algebraMap`,
  `AbstractMeasure.extendScalars_apply_eq_sum_of_dual`,
  `AbstractMeasure.extendScalars_apply_eq_sum`, `AbstractMeasure.extendScalars_self`,
  `AbstractMeasure.extendScalars_apply_one`, `AbstractMeasure.extendScalars_extendScalars`,
  `AbstractMeasure.extendScalars_injective`, `AbstractMeasure.extendScalars_dirac`,
  `AbstractMeasure.extendScalars_map`, `AbstractMeasure.finiteProjection_extendScalars`,
  `AbstractMeasure.eq_sum_smul_extendScalars_of_dual`,
  `AbstractMeasure.eq_sum_smul_extendScalars_of_basis`,
  `AbstractMeasure.baseChangeLinearEquiv_symm_extendScalars`,
  `AbstractMeasure.baseChangeLinearEquiv_symm_dirac`,
  `AbstractMeasure.baseChangeLinearEquiv_symm_apply_of_dual`,
  `AbstractMeasure.baseChangeLinearEquiv_symm_apply`,
  `AbstractMeasure.baseChangeLinearEquiv_self`,
  `AbstractMeasure.extendScalarsRingHom_self`,
  `AbstractMeasure.baseChangeAlgEquiv_self`,
  `AbstractMeasure.exists_baseChange_algEquiv`.
* `AbstractMeasure.coeff_amiceTransform_mapScalars`, `AbstractMeasure.amiceTransform_extendScalars`:
  Amice-transform formulas for `mapScalars` and `extendScalars` on `ℤ_p`.
* `AbstractMeasure.continuous_mapScalars_weak`, `AbstractMeasure.continuous_extendScalars_weak`:
  weak-topology continuity of `mapScalars` and `extendScalars` over normed commutative rings.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, §3.3, Proposition 3.16 and Remark 3.28.
-/

public noncomputable section

open ContinuousMap TauCeti
open scoped PowerSeries TensorProduct

namespace AbstractMeasure

section TopologicalSpace

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

section ModuleTopology

variable {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [Algebra R O] [IsModuleTopology R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

/-- **Scalar retraction of abstract measures along an `R`-linear form.** For `l : O →ₗ[R] R` on a
topological `R`-algebra `O` carrying the `R`-module topology, `mapScalars l` sends `ν ∈ D(X, O)` to
the `R`-valued measure `g ↦ l (ν (algebraMap R O ∘ g))`. -/
def mapScalars (l : O →ₗ[R] R) : D(X, O) →+ D(X, R) where
  toFun ν := toCLMEquiv.symm
    ((⟨l, IsModuleTopology.continuous_of_linearMap l⟩ : O →L[R] R).comp
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
    ContinuousLinearMap.coe_mk', coe_toCLMEquiv, ContinuousLinearMap.compLeftContinuous_apply]
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
theorem mapScalars_mapScalars
    {O' : Type*} [CommRing O'] [TopologicalSpace O'] [IsTopologicalRing O']
    [Algebra R O'] [Algebra O O'] [IsScalarTower R O O']
    [IsModuleTopology R O'] [IsModuleTopology O O']
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

end ModuleTopology

/-- Retracting along `LinearMap.id` is the identity on `D(X, R)`. -/
@[simp]
theorem mapScalars_id (μ : D(X, R)) :
    mapScalars (LinearMap.id : R →ₗ[R] R) μ = μ := by
  ext g
  have hg : (algebraMapCLM R R : C(R, R)).comp g = g := by ext x; simp
  simp [hg]

section FiniteProjective

variable (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [Algebra R O] [IsModuleTopology R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

variable (R) {O} in
/-- **Scalar-test extensionality for `O`-valued measures.** When `O` carries the `R`-module topology
and is finitely generated and projective over `R`, two `O`-valued measures on `X` agree if they
agree on all test functions of the form `algebraMap R O ∘ g` with `g ∈ C(X, R)`. -/
theorem ext_of_apply_comp_algebraMap [Module.Projective R O] [Module.Finite R O] {ν₁ ν₂ : D(X, O)}
    (h : ∀ g : C(X, R),
      ν₁ ((algebraMapCLM R O : C(R, O)).comp g) = ν₂ ((algebraMapCLM R O : C(R, O)).comp g)) :
    ν₁ = ν₂ := by
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  ext f
  rw [ContinuousMap.eq_sum_smul_algebraMapCLM_comp_of_dual hsum f, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, map_smul, h]

private theorem exists_apply_comp_algebraMap [Module.Projective R O] [Module.Finite R O]
    (μ : D(X, R)) :
    ∃ ν : D(X, O),
      ∀ g : C(X, R), ν ((algebraMapCLM R O : C(R, O)).comp g) = algebraMap R O (μ g) := by
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  let cAdd (i : Fin n) : C(X, O) →+ C(X, R) :=
    (φ i).toAddMonoidHom.compLeftContinuous X (IsModuleTopology.continuous_of_linearMap (φ i))
  have hcAdd (i : Fin n) (f : C(X, O)) :
      cAdd i f = (⟨φ i, IsModuleTopology.continuous_of_linearMap (φ i)⟩ : C(O, R)).comp f :=
    (rfl)
  have hcoord (i : Fin n) (a : O) (f : C(X, O)) :
      cAdd i (a • f) = ∑ j : Fin n, φ i (a * b j) • cAdd j f := by
    ext x
    simp only [hcAdd, ContinuousMap.comp_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply]
    conv_lhs => rw [← hsum (f x)]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  refine ⟨toCLMEquiv.symm
    { toFun := fun f ↦ ∑ i : Fin n, μ (cAdd i f) • b i
      map_add' := fun f₁ f₂ ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a f ↦ by
        simp only [RingHom.id_apply, hcoord, map_sum, map_smul, smul_eq_mul, Finset.sum_smul]
        simp_rw [mul_comm (φ _ _) _, ← smul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.smul_sum, hsum, Finset.mul_sum, Algebra.mul_smul_comm]
      cont := continuous_finsetSum _ fun i _ ↦
        ((map_continuous μ).comp
          (ContinuousMap.continuous_postcomp
            ⟨φ i, IsModuleTopology.continuous_of_linearMap (φ i)⟩)).smul continuous_const },
    fun g ↦ ?_⟩
  have hcomp (i : Fin n) : cAdd i ((algebraMapCLM R O : C(R, O)).comp g) = φ i 1 • g := by
    ext x
    simp only [hcAdd, ContinuousMap.comp_apply, algebraMapCLM_apply,
      ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]
  simp only [coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    hcomp, map_smul, smul_eq_mul]
  simp_rw [mul_comm (φ _ 1) (μ g), ← smul_smul, ← Finset.smul_sum]
  rw [hsum 1, ← Algebra.algebraMap_eq_smul_one]

variable [Module.Projective R O] [Module.Finite R O]

/-- **Scalar extension of abstract measures.** When `O` carries the `R`-module topology and is
finitely generated and projective over `R`, `extendScalars O` extends `R`-valued measures on `X`
semilinearly along `algebraMap R O` to `O`-valued measures on `X`, uniquely determined by
`extendScalars_apply_comp_algebraMap`. -/
def extendScalars : D(X, R) →ₛₗ[algebraMap R O] D(X, O) where
  toFun μ := (exists_apply_comp_algebraMap O μ).choose
  map_add' μ₁ μ₂ := ext_of_apply_comp_algebraMap R fun g ↦ by
    have h := fun μ ↦ (exists_apply_comp_algebraMap O μ).choose_spec g
    rw [_root_.add_apply, h, h, h, _root_.add_apply, map_add]
  map_smul' r μ := ext_of_apply_comp_algebraMap R fun g ↦ by
    have h := fun μ ↦ (exists_apply_comp_algebraMap O μ).choose_spec g
    rw [_root_.smul_apply, h, h, _root_.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]

variable {O}

/-- On scalar-valued test functions `algebraMap R O ∘ g`, `extendScalars O μ` applies
`algebraMap R O` to `μ g`. -/
@[simp]
theorem extendScalars_apply_comp_algebraMap (μ : D(X, R)) (g : C(X, R)) :
    extendScalars O μ ((algebraMapCLM R O : C(R, O)).comp g) = algebraMap R O (μ g) :=
  (exists_apply_comp_algebraMap O μ).choose_spec g

/-- An `O`-valued measure equals `extendScalars O μ` if and only if it takes the value
`algebraMap R O (μ g)` on `algebraMap R O ∘ g` for every `g ∈ C(X, R)`. -/
theorem eq_extendScalars_iff {ν : D(X, O)} {μ : D(X, R)} :
    ν = extendScalars O μ ↔
      ∀ g : C(X, R), ν ((algebraMapCLM R O : C(R, O)).comp g) = algebraMap R O (μ g) :=
  ⟨fun h g ↦ h ▸ extendScalars_apply_comp_algebraMap μ g,
    fun h ↦ ext_of_apply_comp_algebraMap R fun g ↦
      (h g).trans (extendScalars_apply_comp_algebraMap μ g).symm⟩

/-- For every `μ ∈ D(X, R)` there is a unique `O`-valued measure integrating `algebraMap R O ∘ g` to
`algebraMap R O (μ g)` for all `g ∈ C(X, R)`. -/
theorem existsUnique_apply_comp_algebraMap (μ : D(X, R)) :
    ∃! ν : D(X, O),
      ∀ g : C(X, R), ν ((algebraMapCLM R O : C(R, O)).comp g) = algebraMap R O (μ g) :=
  ⟨extendScalars O μ, extendScalars_apply_comp_algebraMap μ,
    fun _ hν ↦ eq_extendScalars_iff.mpr hν⟩

/-- Explicit coordinate formula for `extendScalars O μ f` with respect to any finite dual
family `(b, φ)` satisfying `∀ a, ∑ i, φ i a • b i = a`. -/
theorem extendScalars_apply_eq_sum_of_dual {ι : Type*} [Fintype ι]
    {b : ι → O} {φ : ι → Module.Dual R O} (hsum : ∀ a : O, ∑ i, φ i a • b i = a)
    (μ : D(X, R)) (f : C(X, O)) :
    extendScalars O μ f =
      ∑ i : ι,
        μ ((⟨φ i, IsModuleTopology.continuous_of_linearMap (φ i)⟩ : C(O, R)).comp f) • b i := by
  conv_lhs => rw [ContinuousMap.eq_sum_smul_algebraMapCLM_comp_of_dual hsum f]
  simp only [map_sum, map_smul, extendScalars_apply_comp_algebraMap, smul_eq_mul,
    mul_comm (b _), ← Algebra.smul_def]

/-- Explicit coordinate formula for `extendScalars O μ f` in any finite `R`-basis `b` of `O`. -/
theorem extendScalars_apply_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι R O) (μ : D(X, R))
    (f : C(X, O)) :
    extendScalars O μ f =
      ∑ i : ι,
        μ ((⟨b.coord i, IsModuleTopology.continuous_of_linearMap (b.coord i)⟩ : C(O, R)).comp f) •
          b i :=
  extendScalars_apply_eq_sum_of_dual (b := b) (φ := b.coord) (fun a ↦ b.sum_repr a) μ f

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
theorem extendScalars_extendScalars
    {O' : Type*} [CommRing O'] [TopologicalSpace O'] [IsTopologicalRing O']
    [Algebra R O'] [Algebra O O'] [IsScalarTower R O O']
    [IsModuleTopology R O'] [IsModuleTopology O O']
    [Module.Projective O O'] [Module.Finite O O']
    [Module.Projective R O'] [Module.Finite R O']
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

/-- Given a finite dual family `(b, φ)` for `O` over `R` satisfying
`∀ a, ∑ i, φ i a • b i = a`, every `O`-valued measure `ν` decomposes in terms of `b` and
its `R`-valued coordinate measures `mapScalars (φ i) ν`. -/
theorem eq_sum_smul_extendScalars_of_dual {ι : Type*} [Fintype ι]
    {b : ι → O} {φ : ι → Module.Dual R O} (hsum : ∀ a : O, ∑ i, φ i a • b i = a)
    (ν : D(X, O)) :
    ν = ∑ i : ι, b i • extendScalars O (mapScalars (φ i) ν) := by
  refine ext_of_apply_comp_algebraMap R fun g ↦ ?_
  rw [← coe_toCLMEquiv (∑ i : ι, _), map_sum, _root_.sum_apply]
  simp_rw [coe_toCLMEquiv, _root_.smul_apply, extendScalars_apply_comp_algebraMap, mapScalars_apply,
    smul_eq_mul, mul_comm (b _), ← Algebra.smul_def]
  exact (hsum (ν ((algebraMapCLM R O : C(R, O)).comp g))).symm

/-- Given a finite `R`-basis `b` of `O`, every `O`-valued measure `ν` decomposes in terms of `b` and
its `R`-valued coordinate measures `mapScalars (b.coord i) ν`. -/
theorem eq_sum_smul_extendScalars_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (ν : D(X, O)) :
    ν = ∑ i : ι, b i • extendScalars O (mapScalars (b.coord i) ν) :=
  eq_sum_smul_extendScalars_of_dual (b := b) (φ := b.coord) (fun a ↦ b.sum_repr a) ν

omit [Module.Projective R O] [Module.Finite R O] in
/-- Given a finite `R`-basis `b` of `O`, two `O`-valued measures are equal whenever all of their
`b`-coordinate measures in `D(X, R)` agree. -/
theorem ext_of_basis {ι : Type*} [Finite ι] (b : Module.Basis ι R O) {ν₁ ν₂ : D(X, O)}
    (h : ∀ i : ι, mapScalars (b.coord i) ν₁ = mapScalars (b.coord i) ν₂) :
    ν₁ = ν₂ := by
  let _ := Fintype.ofFinite ι
  have := Module.Projective.of_basis b
  have := Module.Finite.of_basis b
  rw [eq_sum_smul_extendScalars_of_basis b ν₁, eq_sum_smul_extendScalars_of_basis b ν₂]
  simp_rw [h]

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

private theorem baseChangeLinearMap_bijective :
    Function.Bijective (baseChangeLinearMap O (X := X) (R := R)) := by
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  let inv (ν : D(X, O)) : O ⊗[R] D(X, R) :=
    ∑ i : Fin n, b i ⊗ₜ[R] mapScalars (φ i) ν
  refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
  · have hadd : ∀ u v : D(X, O), inv (u + v) = inv u + inv v :=
      fun u v ↦ by simp [inv, TensorProduct.tmul_add, Finset.sum_add_distrib]
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a μ =>
      rw [baseChangeLinearMap_tmul]
      simp only [inv, mapScalars_smul_extendScalars, ← TensorProduct.smul_tmul,
        ← TensorProduct.sum_tmul]
      exact congrArg (· ⊗ₜ[R] μ) (hsum a)
    | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, hadd, hz₁, hz₂]
  · intro ν
    dsimp only [inv]
    refine ext_of_apply_comp_algebraMap R fun g ↦ ?_
    rw [map_sum, ← coe_toCLMEquiv, map_sum, _root_.sum_apply]
    simp_rw [coe_toCLMEquiv, baseChangeLinearMap_tmul, _root_.smul_apply,
      extendScalars_apply_comp_algebraMap, mapScalars_apply, smul_eq_mul, mul_comm (b _),
      ← Algebra.smul_def]
    exact hsum (ν ((algebraMapCLM R O : C(R, O)).comp g))

/-- **Finite projective base change of abstract measures.** When `O` carries the `R`-module
topology and is finitely generated and projective over `R`, `O ⊗[R] D(X, R)` is canonically
isomorphic as an `O`-module to `D(X, O)`. -/
def baseChangeLinearEquiv : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O) :=
  LinearEquiv.ofBijective (baseChangeLinearMap O) (baseChangeLinearMap_bijective O)

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

/-- Given a finite dual family `(b, φ)` for `O` over `R` satisfying
`∀ a, ∑ i, φ i a • b i = a`, `(baseChangeLinearEquiv O).symm ν` decomposes as
`∑ i, b i ⊗ₜ mapScalars (φ i) ν`. -/
theorem baseChangeLinearEquiv_symm_apply_of_dual {ι : Type*} [Fintype ι]
    {b : ι → O} {φ : ι → Module.Dual R O} (hsum : ∀ a : O, ∑ i, φ i a • b i = a)
    (ν : D(X, O)) :
    (baseChangeLinearEquiv O).symm ν = ∑ i : ι, b i ⊗ₜ[R] mapScalars (φ i) ν := by
  apply (baseChangeLinearEquiv O).injective
  rw [LinearEquiv.apply_symm_apply, map_sum]
  simpa only [baseChangeLinearEquiv_tmul] using
    eq_sum_smul_extendScalars_of_dual hsum ν

/-- In any finite `R`-basis `b` of `O`, `(baseChangeLinearEquiv O).symm ν` decomposes as
`∑ i, b i ⊗ₜ mapScalars (b.coord i) ν`. -/
theorem baseChangeLinearEquiv_symm_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (ν : D(X, O)) :
    (baseChangeLinearEquiv O).symm ν = ∑ i : ι, b i ⊗ₜ[R] mapScalars (b.coord i) ν :=
  baseChangeLinearEquiv_symm_apply_of_dual (b := b) (φ := b.coord) (fun a ↦ b.sum_repr a) ν

end FiniteProjective

/-- Extending scalars from `R` to `R` itself is the identity map on `D(X, R)`. -/
@[simp]
theorem extendScalars_self :
    extendScalars (X := X) R = LinearMap.id :=
  LinearMap.ext fun μ ↦ ext_of_apply_comp_algebraMap R fun g ↦ by
    have hg : (algebraMapCLM R R : C(R, R)).comp g = g := by ext x; simp
    rw [extendScalars_apply_comp_algebraMap, hg]
    simp

/-- Base change from `R` to `R` itself recovers `TensorProduct.lid`. -/
@[simp]
theorem baseChangeLinearEquiv_self :
    baseChangeLinearEquiv (X := X) R = TensorProduct.lid R D(X, R) := by
  apply LinearEquiv.toLinearMap_injective
  ext μ
  simp

end TopologicalSpace

section WeakTopology

variable {X R O : Type*} [TopologicalSpace X]
  [NormedCommRing R] [NormedCommRing O] [Algebra R O] [IsModuleTopology R O]

/-- `mapScalars l : D(X, O) → D(X, R)` is continuous for the weak topologies whenever `O` carries
the `R`-module topology. -/
theorem continuous_mapScalars_weak (l : O →ₗ[R] R) :
    @Continuous _ _ (WeakTopology (X := X) (R := O) (E := O))
      (WeakTopology (X := X) (R := R) (E := R)) (mapScalars l) := by
  have := IsModuleTopology.toContinuousSMul R O
  let _ : TopologicalSpace D(X, O) := WeakTopology
  let _ : TopologicalSpace D(X, R) := WeakTopology
  refine continuous_induced_rng.mpr (continuous_pi fun g : C(X, R) ↦ ?_)
  simp only [Function.comp_apply, mapScalars_apply]
  exact (IsModuleTopology.continuous_of_linearMap l).comp
    ((continuous_apply ((algebraMapCLM R O : C(R, O)).comp g)).comp continuous_induced_dom)

/-- `extendScalars O : D(X, R) → D(X, O)` is continuous for the weak topologies whenever `O`
carries the `R`-module topology and is finitely generated and projective over `R`. -/
theorem continuous_extendScalars_weak [Module.Projective R O] [Module.Finite R O] :
    @Continuous _ _ (WeakTopology (X := X) (R := R) (E := R))
      (WeakTopology (X := X) (R := O) (E := O)) (extendScalars O) := by
  have := IsModuleTopology.toContinuousSMul R O
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := O)
  let _ : TopologicalSpace D(X, R) := WeakTopology
  let _ : TopologicalSpace D(X, O) := WeakTopology
  refine continuous_induced_rng.mpr (continuous_pi fun f : C(X, O) ↦ ?_)
  simp only [Function.comp_apply, extendScalars_apply_eq_sum_of_dual hsum _ f]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  have heval : Continuous (fun μ : D(X, R) ↦
      μ ((⟨φ i, IsModuleTopology.continuous_of_linearMap (φ i)⟩ : C(O, R)).comp f)) :=
    (continuous_apply _).comp continuous_induced_dom
  exact heval.smul continuous_const

end WeakTopology

section Monoid

variable {G : Type*} [Monoid G] [TopologicalSpace G]

section ModuleTopology

variable {R O : Type*}
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [Algebra R O] [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]

local instance : ContinuousSMul R O := IsModuleTopology.toContinuousSMul R O

section ContinuousMul

variable [ContinuousMul G]

/-- Right convolution of `extendScalars O ν` with `algebraMap R O ∘ g` is `algebraMap R O`
postcomposed with `convolveFunRight ν g`. -/
theorem convolveFunRight_extendScalars_comp_algebraMap (ν : D(G, R)) (g : C(G, R)) :
    convolveFunRight (extendScalars O ν) ((algebraMapCLM R O : C(R, O)).comp g) =
      (algebraMapCLM R O : C(R, O)).comp (convolveFunRight ν g) := by
  ext x
  simp only [convolveFunRight_apply, comp_apply, ContinuousMap.coe_ofClass, algebraMapCLM_apply]
  exact extendScalars_apply_comp_algebraMap ν ⟨fun y ↦ g (x * y), by fun_prop⟩

end ContinuousMul

omit [Module.Projective R O] [Module.Finite R O] in
/-- Retracting the multiplicative identity `1 = dirac 1` along `l : O →ₗ[R] R` scales `1` by
`l 1`. -/
@[simp]
theorem mapScalars_one (l : O →ₗ[R] R) :
    mapScalars l (1 : D(G, O)) = l 1 • (1 : D(G, R)) := by
  simp [one_def]

omit [Module.Projective R O] [Module.Finite R O] in
/-- Retracting `a • 1` along `l : O →ₗ[R] R` gives `l a • 1`. -/
@[simp]
theorem mapScalars_smul_one (l : O →ₗ[R] R) (a : O) :
    mapScalars l (a • (1 : D(G, O))) = l a • (1 : D(G, R)) := by
  simp [one_def]

/-- Extending scalars preserves the multiplicative identity `1 = dirac 1`. -/
@[simp]
theorem extendScalars_one : extendScalars O (1 : D(G, R)) = 1 := by
  simp [one_def]

section LocallyCompact

variable [ContinuousMul G] [LocallyCompactSpace G]

/-- Extending scalars preserves convolution of measures on any locally compact topological
monoid. -/
@[simp]
theorem extendScalars_mul (μ ν : D(G, R)) :
    extendScalars O (μ * ν) = extendScalars O μ * extendScalars O ν :=
  ext_of_apply_comp_algebraMap R fun g ↦ by
    rw [extendScalars_apply_comp_algebraMap, mul_apply, mul_apply,
      convolveFunRight_extendScalars_comp_algebraMap, extendScalars_apply_comp_algebraMap]

omit [Module.Projective R O] [Module.Finite R O] in
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

/-- Extending scalars from `R` to `R` itself is the identity ring homomorphism. -/
@[simp]
theorem extendScalarsRingHom_self :
    extendScalarsRingHom (G := G) R = RingHom.id D(G, R) :=
  RingHom.ext fun _ ↦ by simp

variable (O) in
/-- **Finite projective base-change algebra equivalence for measures.** On a locally compact
topological monoid `G` (not necessarily commutative), `O ⊗[R] D(G, R)` is canonically isomorphic as
an `O`-algebra to `D(G, O)`. -/
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

/-- Convolution-algebra base change from `R` to `R` itself recovers `Algebra.TensorProduct.lid`. -/
@[simp]
theorem baseChangeAlgEquiv_self :
    baseChangeAlgEquiv (G := G) R = Algebra.TensorProduct.lid R D(G, R) := by
  apply AlgEquiv.coe_toAlgHom_injective
  ext μ
  simp

end LocallyCompact

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
  exact ⟨baseChangeAlgEquiv O, fun a x ↦ by simp⟩

end Monoid

section Amice

variable {p : ℕ} [Fact p.Prime]
  {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [Algebra ℤ_[p] O] [IsModuleTopology ℤ_[p] O]

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
theorem amiceTransform_extendScalars [Module.Projective ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (μ : D(ℤ_[p], ℤ_[p])) :
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
  baseChangeAlgEquiv_self

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] (x : G) :
    let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
    baseChangeAlgEquiv O ((1 : O) ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = dirac O x := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  simp

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] {a b : O} (hab : a ≠ b) (x : G) :
    let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
    baseChangeAlgEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) ≠
      baseChangeAlgEquiv O (b ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  simpa using hab

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O]
    (h : ¬ Filter.Tendsto (fun n : ℕ ↦ ((p : ℤ_[p]) ^ n) • (1 : O)) Filter.atTop (nhds 0)) :
    ¬ ContinuousSMul ℤ_[p] O := by
  intro hc
  apply h
  have hp : ‖(p : ℤ_[p])‖ < 1 := by simpa using Padic.norm_p_lt_one (p := p)
  simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).smul_const (1 : O)

end Examples

end AbstractMeasure
