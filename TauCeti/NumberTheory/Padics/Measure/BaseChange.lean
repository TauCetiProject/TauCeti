/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Algebra
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.BaseChange
public import TauCeti.Topology.Algebra.Module.AutomaticContinuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.Compact

/-!
# Finite free base change of abstract measures and completed group algebras

Let `R` be a compact topological commutative ring and `O` a Hausdorff topological commutative
`R`-algebra that is finite and free as an `R`-module and has continuous `R`-scalar action
(`ContinuousSMul R O`). The main arithmetic case is `R = ℤ_p` and `O` the valuation ring of a
finite extension of `ℚ_p` (or any normed commutative ring that is finite and free over `ℤ_p` with
continuous `ℤ_p`-action).

Because `R` is compact and `O` is finitely generated and Hausdorff over `R`, every `R`-linear
functional `O →ₗ[R] R` is automatically continuous
(`LinearMap.continuous_of_finite_of_compactSpace`). Choosing a finite `R`-basis `(b_i)` of `O`
decomposes every test function `f ∈ C(X, O)` into continuous `R`-valued coordinate functions
`(b.coord i) ∘ f ∈ C(X, R)`, allowing an `R`-valued measure `μ ∈ D(X, R)` on any topological space
`X` to be extended to an `O`-valued measure `extendScalars O μ ∈ D(X, O)`. Although defined via a
basis, `extendScalars O μ` is uniquely determined by the basis-free identity
`extendScalars O μ (algebraMap R O ∘ g) = algebraMap R O (μ g)` for `g ∈ C(X, R)`. Assembling
scalar multiplication on the left with `extendScalars O` produces a canonical `O`-linear
equivalence `baseChangeLinearEquiv O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.

When `G` is a locally compact topological monoid (not necessarily commutative or compact),
`extendScalars O` respects right convolution, upgrading `baseChangeLinearEquiv O` to an `O`-algebra
isomorphism `baseChangeAlgEquiv O : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` sending `a ⊗ₜ dirac R x` to
`a • dirac O x`.

On a profinite group `Γ` over `ℤ_p`, comparing `baseChangeAlgEquiv O` with
`completedGroupAlgebra.baseChangeEquiv ℤ_[p] O Γ` and the integral-measure isomorphism
`completedGroupAlgebraEquiv : D(Γ, ℤ_[p]) ≃ₐ[ℤ_[p]] ℤ_[p][[Γ]]` shows that
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is an isomorphism of `O`-algebras
(`completedGroupAlgebraEquivOfFiniteFree`). When `O` is a normed commutative ring, this isomorphism
is moreover a homeomorphism from the weak topology on `D(Γ, O)` to the inverse-limit topology on
`O[[Γ]]`, making `(D(Γ, O), WeakTopology)` a compact topological ring.

The continuity assumption `ContinuousSMul ℤ_p O` is essential: equipping `ℤ_p` with an
archimedean norm via an abstract field embedding `ℚ_p → ℂ` produces a free rank-one normed
`ℤ_p`-algebra in which `p^n • 1` does not tend to `0`, violating `ContinuousSMul ℤ_p O` (recorded as
a negative-control `example` at the end of the file).

## Main definitions

* `AbstractMeasure.extendScalars O`: the `algebraMap R O`-semilinear extension map
  `D(X, R) →ₛₗ[algebraMap R O] D(X, O)`.
* `AbstractMeasure.baseChangeLinearEquiv O`: the `O`-linear isomorphism
  `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.
* `AbstractMeasure.extendScalarsRingHom O`: `extendScalars O` bundled as a ring homomorphism
  `D(G, R) →+* D(G, O)` on a locally compact topological monoid `G`.
* `AbstractMeasure.baseChangeAlgEquiv O`: the `O`-algebra isomorphism
  `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` on a locally compact topological monoid `G`.
* `AbstractMeasure.completedGroupAlgebraEquivOfFiniteFree p O`: the `O`-algebra isomorphism
  `D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ` for a profinite group `Γ` and finite free Hausdorff
  topological `ℤ_p`-algebra `O`.

## Main results

* `AbstractMeasure.ext_of_apply_comp_algebraMap`: two `O`-valued measures agree if and only if they
  agree on test functions of the form `algebraMap R O ∘ g` with `g ∈ C(X, R)`.
* `AbstractMeasure.extendScalars_apply_comp_algebraMap`,
  `AbstractMeasure.extendScalars_apply_basis`, `AbstractMeasure.extendScalars_dirac`,
  `AbstractMeasure.extendScalars_map`, `AbstractMeasure.finiteProjection_extendScalars`.
* `AbstractMeasure.toCompletedGroupAlgebra_baseChangeAlgEquiv`: compatibility of measure base change
  with `toCompletedGroupAlgebra` and `completedGroupAlgebra.baseChangeEquiv`.
* `AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree`,
  `AbstractMeasure.isTopologicalRing_weak_of_finiteFree`,
  `AbstractMeasure.compactSpace_weak_of_finiteFree`.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, §3.3, Proposition 3.16.
-/

public noncomputable section

open ContinuousMap TauCeti
open scoped TensorProduct

namespace AbstractMeasure

section TopologicalSpace

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]

section FiniteFree

variable (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O]

/-- Coordinate linear form `b.coord i : O →ₗ[R] R` of a finite `R`-basis `b` of `O`, bundled as a
continuous map `C(O, R)` via automatic continuity over the compact ring `R`. -/
private def basisCoordContinuousMap {ι : Type*} [Fintype ι] (b : Module.Basis ι R O) (i : ι) :
    C(O, R) :=
  have : Module.Finite R O := Module.Finite.of_basis b
  ⟨b.coord i, (b.coord i).continuous_of_finite_of_compactSpace⟩

@[simp]
private theorem basisCoordContinuousMap_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (i : ι) (a : O) :
    basisCoordContinuousMap O b i a = b.coord i a :=
  (rfl)

/-- Every continuous `O`-valued function decomposes along a finite `R`-basis `b` of `O` into a
linear combination of `R`-valued continuous coordinate functions pushed into `O`. -/
private theorem eq_sum_basisCoordContinuousMap {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (f : C(X, O)) :
    f = ∑ i : ι, b i •
      (algebraMapCLM R O : C(R, O)).comp ((basisCoordContinuousMap O b i).comp f) := by
  ext x
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
    comp_apply, ContinuousMap.coe_ofClass, algebraMapCLM_apply, basisCoordContinuousMap_apply,
    Module.Basis.coord_apply, smul_eq_mul, mul_comm (b _), ← Algebra.smul_def]
  exact (b.sum_repr (f x)).symm

variable (R) {O} in
/-- **Scalar-test extensionality for `O`-valued measures.** When `O` is finite and free over a
compact ring `R` with continuous `R`-action, two `O`-valued measures on `X` agree if and only if
they agree on all test functions of the form `algebraMap R O ∘ g` with `g ∈ C(X, R)`. -/
theorem ext_of_apply_comp_algebraMap [Module.Free R O] [Module.Finite R O] {ν₁ ν₂ : D(X, O)}
    (h : ∀ g : C(X, R),
      ν₁ ((algebraMapCLM R O : C(R, O)).comp g) = ν₂ ((algebraMapCLM R O : C(R, O)).comp g)) :
    ν₁ = ν₂ := by
  let b := Module.Free.chooseBasis R O
  ext f
  rw [eq_sum_basisCoordContinuousMap O b f]
  simp only [map_sum, map_smul, h]

/-- Auxiliary `O`-measure attached to `μ : D(X, R)` using an explicit finite `R`-basis `b` of
`O`. -/
private def extendScalarsWithBasis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (μ : D(X, R)) : D(X, O) :=
  toCLMEquiv.symm
    { toFun f := ∑ i : ι, μ ((basisCoordContinuousMap O b i).comp f) • b i
      map_add' f g := by
        have hcomp (i : ι) :
            (basisCoordContinuousMap O b i).comp (f + g) =
              (basisCoordContinuousMap O b i).comp f +
                (basisCoordContinuousMap O b i).comp g := by
          ext x
          simp
        simp [hcomp, add_smul, Finset.sum_add_distrib]
      map_smul' c f := by
        have hcomp (i : ι) :
            (basisCoordContinuousMap O b i).comp (c • f) =
              ∑ j : ι, b.coord i (c * b j) • ((basisCoordContinuousMap O b j).comp f) := by
          ext x
          simp only [comp_apply, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
            basisCoordContinuousMap_apply, ContinuousMap.coe_sum, Finset.sum_apply]
          conv_lhs => rw [← b.sum_repr (f x)]
          simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Module.Basis.coord_apply,
            smul_eq_mul, mul_comm]
        simp only [RingHom.id_apply]
        calc
          ∑ i : ι, μ ((basisCoordContinuousMap O b i).comp (c • f)) • b i
              = ∑ i : ι, ∑ j : ι,
                  (b.coord i (c * b j) * μ ((basisCoordContinuousMap O b j).comp f)) • b i := by
                refine Finset.sum_congr rfl fun i _ ↦ ?_
                rw [hcomp i, map_sum, Finset.sum_smul]
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                rw [map_smul, smul_eq_mul]
          _ = ∑ j : ι, μ ((basisCoordContinuousMap O b j).comp f) •
                ∑ i : ι, b.coord i (c * b j) • b i := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun i _ ↦ ?_
                rw [mul_comm, mul_smul]
          _ = c • ∑ j : ι, μ ((basisCoordContinuousMap O b j).comp f) • b j := by
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                simp_rw [Module.Basis.coord_apply]
                rw [b.sum_repr, ← smul_eq_mul c, smul_comm]
      cont := by
        refine continuous_finsetSum _ fun i _ ↦ ?_
        exact ((map_continuous μ).comp
          (ContinuousMap.continuous_postcomp (basisCoordContinuousMap O b i))).smul
          continuous_const }

private theorem extendScalarsWithBasis_apply_comp_algebraMap {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (μ : D(X, R)) (g : C(X, R)) :
    extendScalarsWithBasis O b μ ((algebraMapCLM R O : C(R, O)).comp g) =
      algebraMap R O (μ g) := by
  have hcomp (i : ι) :
      (basisCoordContinuousMap O b i).comp ((algebraMapCLM R O : C(R, O)).comp g) =
        b.coord i 1 • g := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
  simp only [extendScalarsWithBasis, coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, hcomp, map_smul, smul_eq_mul]
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

/-- Extending scalars from a Hausdorff compact commutative ring `R` to itself is the identity map
on `D(X, R)`. -/
theorem extendScalars_self [T2Space R] (μ : D(X, R)) :
    extendScalars R μ = μ :=
  ext_of_apply_comp_algebraMap R fun g ↦ by
    have hg : (algebraMapCLM R R : C(R, R)).comp g = g := by ext x; simp
    rw [extendScalars_apply_comp_algebraMap, hg]
    simp

/-- Explicit coordinate formula for `extendScalars O μ f` in any finite `R`-basis `b` of `O`. -/
theorem extendScalars_apply_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O) (μ : D(X, R))
    (f : C(X, O)) :
    extendScalars O μ f =
      ∑ i : ι,
        μ (⟨b.coord i ∘ f,
          (b.coord i).continuous_of_finite_of_compactSpace.comp f.continuous⟩) • b i := by
  conv_lhs => rw [eq_sum_basisCoordContinuousMap O b f]
  simp only [map_sum, map_smul, extendScalars_apply_comp_algebraMap, smul_eq_mul,
    mul_comm (b _), ← Algebra.smul_def]
  rfl

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
        (algebraMapCLM R O : C(R, O)).comp (g.comp φ) := rfl
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

variable (O)

/-- Additive bilinear lift underlying `baseChangeLinearEquiv`. -/
private def baseChangeAddHom : O ⊗[R] D(X, R) →+ D(X, O) :=
  TensorProduct.liftAddHom
    { toFun a :=
        { toFun μ := a • extendScalars O μ
          map_zero' := by simp
          map_add' μ ν := by simp [smul_add] }
      map_zero' := by ext μ f; simp [← coe_toCLMEquiv]
      map_add' a b := by ext μ f; simp [add_smul] }
    fun r a μ ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smulₛₗ]
      rw [Algebra.smul_def, mul_comm, smul_smul]

/-- Forward `O`-linear map `O ⊗[R] D(X, R) →ₗ[O] D(X, O)` sending `a ⊗ₜ μ` to
`a • extendScalars O μ`. -/
private def baseChangeLinearMap : O ⊗[R] D(X, R) →ₗ[O] D(X, O) where
  toFun := baseChangeAddHom O
  map_add' := (baseChangeAddHom O).map_add
  map_smul' c z := by
    refine TensorProduct.inductionOn z ?_ fun z₁ z₂ hz₁ hz₂ ↦ by
      simp only [RingHom.id_apply, smul_add, map_add] at hz₁ hz₂ ⊢
      rw [hz₁, hz₂]
    intro a μ
    simp [baseChangeAddHom, TensorProduct.smul_tmul', smul_smul]

/-- Coordinate measure `g ↦ b.coord i (ν (algebraMap R O ∘ g))` extracting the `i`-th `R`-component
of `ν : D(X, O)` with respect to an `R`-basis `b` of `O`. -/
private def coordMeasure {ι : Type*} (b : Module.Basis ι R O) (i : ι) :
    D(X, O) →+ D(X, R) where
  toFun ν := toCLMEquiv.symm
    { toFun g := b.coord i (ν ((algebraMapCLM R O : C(R, O)).comp g))
      map_add' g₁ g₂ := by
        have hcomp : (algebraMapCLM R O : C(R, O)).comp (g₁ + g₂) =
            (algebraMapCLM R O : C(R, O)).comp g₁ + (algebraMapCLM R O : C(R, O)).comp g₂ := by
          ext x; simp
        simp [hcomp]
      map_smul' r g := by
        have hcomp : (algebraMapCLM R O : C(R, O)).comp (r • g) =
            algebraMap R O r • (algebraMapCLM R O : C(R, O)).comp g := by
          ext x; simp [Algebra.smul_def]
        rw [RingHom.id_apply, hcomp, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul]
      cont := ((b.coord i).continuous_of_finite_of_compactSpace.comp
        ((map_continuous ν).comp (ContinuousMap.continuous_postcomp
          (algebraMapCLM R O : C(R, O))))) }
  map_zero' := by ext g; simp [← coe_toCLMEquiv]
  map_add' ν₁ ν₂ := by ext g; simp [← coe_toCLMEquiv]

omit [Module.Free R O] in
@[simp]
private theorem coordMeasure_apply {ι : Type*} (b : Module.Basis ι R O)
    (i : ι) (ν : D(X, O)) (g : C(X, R)) :
    coordMeasure O b i ν g = b.coord i (ν ((algebraMapCLM R O : C(R, O)).comp g)) := by
  simp [coordMeasure]

private theorem coordMeasure_smul_extendScalars {ι : Type*} (b : Module.Basis ι R O)
    (i : ι) (a : O) (μ : D(X, R)) :
    coordMeasure O b i (a • extendScalars O μ) = b.coord i a • μ := by
  ext g
  simp only [coordMeasure_apply, _root_.smul_apply, extendScalars_apply_comp_algebraMap,
    smul_eq_mul]
  rw [mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

private def baseChangeInvAux {ι : Type*} [Fintype ι] (b : Module.Basis ι R O) :
    D(X, O) →+ O ⊗[R] D(X, R) where
  toFun ν := ∑ i : ι, b i ⊗ₜ[R] coordMeasure O b i ν
  map_zero' := by simp
  map_add' ν₁ ν₂ := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

private theorem baseChangeInvAux_comp_baseChangeLinearMap {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (z : O ⊗[R] D(X, R)) :
    baseChangeInvAux O b (baseChangeLinearMap O z) = z := by
  refine TensorProduct.inductionOn z ?_ fun z₁ z₂ hz₁ hz₂ ↦ by
    rw [map_add, map_add, hz₁, hz₂]
  intro a μ
  simp only [baseChangeLinearMap, LinearMap.coe_mk, AddHom.coe_mk, baseChangeAddHom,
    TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, baseChangeInvAux,
    coordMeasure_smul_extendScalars]
  simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, Module.Basis.coord_apply,
    b.sum_repr]

private theorem baseChangeLinearMap_comp_baseChangeInvAux {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (ν : D(X, O)) :
    baseChangeLinearMap O (baseChangeInvAux O b ν) = ν := by
  apply ext_of_apply_comp_algebraMap R
  intro g
  rw [← coe_toCLMEquiv]
  simp only [baseChangeInvAux, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum,
    baseChangeLinearMap, LinearMap.coe_mk, AddHom.coe_mk, baseChangeAddHom,
    TensorProduct.liftAddHom_tmul, _root_.sum_apply, coe_toCLMEquiv,
    _root_.smul_apply, extendScalars_apply_comp_algebraMap, coordMeasure_apply, smul_eq_mul,
    mul_comm (b _), ← Algebra.smul_def, Module.Basis.coord_apply]
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

/-- `baseChangeLinearEquiv O` sends `1 ⊗ₜ μ` to `extendScalars O μ`. -/
theorem baseChangeLinearEquiv_one_tmul (μ : D(X, R)) :
    baseChangeLinearEquiv O ((1 : O) ⊗ₜ[R] μ) = extendScalars O μ := by
  simp

/-- `baseChangeLinearEquiv O` sends `a ⊗ₜ dirac R x` to `a • dirac O x`. -/
theorem baseChangeLinearEquiv_tmul_dirac (a : O) (x : X) :
    baseChangeLinearEquiv O (a ⊗ₜ[R] dirac R x) = a • dirac O x := by
  simp

/-- Explicit decomposition of `(baseChangeLinearEquiv O).symm ν` in any finite `R`-basis `b` of
`O`: each `R`-coordinate measure sends `g ∈ C(X, R)` to `b.coord i (ν (algebraMap R O ∘ g))`. -/
theorem baseChangeLinearEquiv_symm_apply_comp_algebraMap {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R O) (ν : D(X, O)) :
    ∃ c : ι → D(X, R),
      (baseChangeLinearEquiv O).symm ν = ∑ i : ι, b i ⊗ₜ[R] c i ∧
        ∀ i (g : C(X, R)), c i g = b.coord i (ν ((algebraMapCLM R O : C(R, O)).comp g)) := by
  refine ⟨fun i ↦ coordMeasure O b i ν, ?_, fun i g ↦ coordMeasure_apply O b i ν g⟩
  apply (baseChangeLinearEquiv O).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (baseChangeLinearMap_comp_baseChangeInvAux O b ν).symm

end FiniteFree

end TopologicalSpace

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

/-- `baseChangeLinearEquiv O` preserves the convolution identity. -/
@[simp]
theorem baseChangeLinearEquiv_one :
    baseChangeLinearEquiv O (1 : O ⊗[R] D(G, R)) = 1 := by
  rw [Algebra.TensorProduct.one_def]
  simp

/-- `baseChangeLinearEquiv O` preserves convolution multiplication. -/
@[simp]
theorem baseChangeLinearEquiv_mul (z w : O ⊗[R] D(G, R)) :
    baseChangeLinearEquiv O (z * w) =
      baseChangeLinearEquiv O z * baseChangeLinearEquiv O w := by
  refine TensorProduct.inductionOn z ?_ fun z₁ z₂ hz₁ hz₂ ↦ by
    rw [add_mul, map_add, map_add, add_mul, hz₁, hz₂]
  intro a₁ μ₁
  refine TensorProduct.inductionOn w ?_ fun w₁ w₂ hw₁ hw₂ ↦ by
    rw [mul_add, map_add, map_add, mul_add, hw₁, hw₂]
  intro a₂ μ₂
  simp [smul_smul, mul_comm a₁ a₂]

variable (O) in
/-- **Finite free base-change algebra equivalence for measures.** On a locally compact topological
monoid `G` (not necessarily commutative), `O ⊗[R] D(G, R)` is canonically isomorphic as an
`O`-algebra to `D(G, O)`. -/
def baseChangeAlgEquiv : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O) :=
  AlgEquiv.ofLinearEquiv (baseChangeLinearEquiv O)
    baseChangeLinearEquiv_one baseChangeLinearEquiv_mul

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

/-- `baseChangeAlgEquiv O` sends `a ⊗ₜ μ` to `a • extendScalars O μ`. -/
@[simp]
theorem baseChangeAlgEquiv_tmul (a : O) (μ : D(G, R)) :
    baseChangeAlgEquiv O (a ⊗ₜ[R] μ) = a • extendScalars O μ :=
  (rfl)

/-- `baseChangeAlgEquiv O` sends `1 ⊗ₜ μ` to `extendScalars O μ`. -/
theorem baseChangeAlgEquiv_one_tmul (μ : D(G, R)) :
    baseChangeAlgEquiv O ((1 : O) ⊗ₜ[R] μ) = extendScalars O μ := by
  simp

/-- `baseChangeAlgEquiv O` sends `a ⊗ₜ dirac R x` to `a • dirac O x`. -/
theorem baseChangeAlgEquiv_tmul_dirac (a : O) (x : G) :
    baseChangeAlgEquiv O (a ⊗ₜ[R] dirac R x) = a • dirac O x := by
  simp

end LocallyCompact

end Monoid

section CompletedGroupAlgebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]

section CompactGroup

variable {R O : Type*} [ContinuousMul Γ] [LocallyCompactSpace Γ]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O] [Module.Free R O] [Module.Finite R O]

/-- `toCompletedGroupAlgebra` intertwines `extendScalars O` on measures with
`completedGroupAlgebra.mapRingHom` along `algebraMap R O`. -/
@[simp]
theorem toCompletedGroupAlgebra_extendScalars (μ : D(Γ, R)) :
    toCompletedGroupAlgebra (extendScalars O μ) =
      completedGroupAlgebra.mapRingHom Γ (algebraMap R O) (toCompletedGroupAlgebra μ) := by
  ext U a
  rw [completedGroupAlgebra.coeff_proj_mapRingHom, proj_toCompletedGroupAlgebra,
    proj_toCompletedGroupAlgebra, ContinuousMonoidHom.finiteProjectionAlgHom_coeff,
    ContinuousMonoidHom.finiteProjectionAlgHom_coeff, finiteProjection_extendScalars,
    Finsupp.mapRange_apply]

/-- `toCompletedGroupAlgebra` intertwines `baseChangeAlgEquiv O` on `O ⊗[R] D(Γ, R)` with
`completedGroupAlgebra.baseChangeEquiv R O Γ` on `O ⊗[R] R[[Γ]]`. -/
theorem toCompletedGroupAlgebra_baseChangeAlgEquiv (z : O ⊗[R] D(Γ, R)) :
    toCompletedGroupAlgebra (baseChangeAlgEquiv O z) =
      completedGroupAlgebra.baseChangeEquiv R O Γ
        (Algebra.TensorProduct.map (AlgHom.id O O) toCompletedGroupAlgebra z) := by
  refine TensorProduct.inductionOn z ?_ fun z₁ z₂ hz₁ hz₂ ↦ by
    rw [map_add, map_add, map_add, map_add, hz₁, hz₂]
  intro a μ
  simp

end CompactGroup

section ProfinitePadicInt

variable [IsTopologicalGroup Γ] [TotallyDisconnectedSpace Γ]

/-- **Surjectivity of `toCompletedGroupAlgebra` for finite free `ℤ_p`-algebras.** Every element of
`O[[Γ]]` arises from an `O`-valued measure on `Γ`. -/
theorem toCompletedGroupAlgebra_surjective_of_finiteFree (p : ℕ) [Fact p.Prime]
    (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  intro y
  let e : O ⊗[ℤ_[p]] D(Γ, ℤ_[p]) ≃ₐ[O] O ⊗[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : O ≃ₐ[O] O)
      (completedGroupAlgebraEquiv (Γ := Γ) (p := p))
  let z : O ⊗[ℤ_[p]] D(Γ, ℤ_[p]) :=
    e.symm ((completedGroupAlgebra.baseChangeEquiv ℤ_[p] O Γ).symm y)
  refine ⟨baseChangeAlgEquiv O z, ?_⟩
  rw [toCompletedGroupAlgebra_baseChangeAlgEquiv]
  have hz : Algebra.TensorProduct.map (AlgHom.id O O)
      (toCompletedGroupAlgebra : D(Γ, ℤ_[p]) →ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ) z =
        (completedGroupAlgebra.baseChangeEquiv ℤ_[p] O Γ).symm y := by
    have hmap : Algebra.TensorProduct.map (AlgHom.id O O)
        (toCompletedGroupAlgebra : D(Γ, ℤ_[p]) →ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ) =
        e.toAlgHom := by
      ext x
      simp [e]
    rw [hmap]
    exact e.apply_symm_apply _
  rw [hz, AlgEquiv.apply_symm_apply]

/-- **`O`-valued measures are the completed group algebra (Rodrigues Jacinto–Williams,
Proposition 3.16).** For a profinite group `Γ` and a Hausdorff topological commutative
`ℤ_p`-algebra `O` that is finite and free over `ℤ_p` with continuous `ℤ_p`-action, `D(Γ, O)` is
canonically isomorphic as an `O`-algebra to `O[[Γ]]`. -/
def completedGroupAlgebraEquivOfFiniteFree (p : ℕ) [Fact p.Prime]
    (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective toCompletedGroupAlgebra
    ⟨toCompletedGroupAlgebra_injective, toCompletedGroupAlgebra_surjective_of_finiteFree p O⟩

/-- The forward map of `completedGroupAlgebraEquivOfFiniteFree p O` is
`toCompletedGroupAlgebra`. -/
@[simp]
theorem completedGroupAlgebraEquivOfFiniteFree_apply {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (ν : D(Γ, O)) :
    completedGroupAlgebraEquivOfFiniteFree p O ν = toCompletedGroupAlgebra ν :=
  AlgEquiv.ofBijective_apply _ _ _

/-- In any finite `ℤ_p`-basis `b` of `O`, `(completedGroupAlgebraEquivOfFiniteFree p O).symm`
extracts each scalar coordinate in `ℤ_p[[Γ]]`, converts it to an integral measure, and recombines
in `D(Γ, O)`. -/
theorem completedGroupAlgebraEquivOfFiniteFree_symm_apply {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
    [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ_[p] O) (y : completedGroupAlgebra O Γ) :
    (completedGroupAlgebraEquivOfFiniteFree p O).symm y =
      ∑ i : ι, b i • extendScalars O
        (completedGroupAlgebraEquiv.symm
          (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) := by
  apply (completedGroupAlgebraEquivOfFiniteFree p O).injective
  rw [AlgEquiv.apply_symm_apply, completedGroupAlgebraEquivOfFiniteFree_apply]
  have hsum : ∑ i : ι, b i • extendScalars O
      (completedGroupAlgebraEquiv.symm
        (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) =
      baseChangeAlgEquiv O (∑ i : ι, b i ⊗ₜ[ℤ_[p]]
        completedGroupAlgebraEquiv.symm
          (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)) := by
    simp [map_sum]
  rw [hsum, toCompletedGroupAlgebra_baseChangeAlgEquiv]
  simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    ← completedGroupAlgebraEquiv_apply, AlgEquiv.apply_symm_apply]
  rw [← map_sum, ← completedGroupAlgebra.baseChangeEquiv_symm_apply b y,
    AlgEquiv.apply_symm_apply]

open Topology in
/-- **Weak-topology homeomorphism for finite free normed `ℤ_p`-algebras.** The comparison
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is a homeomorphism from the weak topology on
measures to the inverse-limit topology on the completed group algebra. -/
theorem isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree (p : ℕ) [Fact p.Prime]
    (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := O) (E := O)) _
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  let tO : TopologicalSpace D(Γ, O) := WeakTopology
  let tZp : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  let b := Module.Free.chooseBasis ℤ_[p] O
  let hZp := (isHomeomorph_toCompletedGroupAlgebra_weak (Γ := Γ) (p := p)).homeomorph
    (toCompletedGroupAlgebra : D(Γ, ℤ_[p]) →ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ)
  have hhZp_symm (x : completedGroupAlgebra ℤ_[p] Γ) :
      hZp.symm x = (completedGroupAlgebraEquiv (Γ := Γ) (p := p)).symm x := by
    apply (completedGroupAlgebraEquiv (Γ := Γ) (p := p)).injective
    rw [AlgEquiv.apply_symm_apply, completedGroupAlgebraEquiv_apply]
    exact hZp.apply_symm_apply x
  have hsymm_cont :
      Continuous (⇑(completedGroupAlgebraEquivOfFiniteFree (Γ := Γ) p O).symm) := by
    refine continuous_induced_rng.mpr (continuous_pi fun f : C(Γ, O) ↦ ?_)
    simp only [Function.comp_apply]
    have hfun : (fun y : completedGroupAlgebra O Γ ↦
        (completedGroupAlgebraEquivOfFiniteFree p O).symm y f) =
        fun y ↦ ∑ i, b i * ∑ j,
          (hZp.symm (completedGroupAlgebra.mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y)
            ((basisCoordContinuousMap O b j).comp f)) • b j := by
      ext y
      rw [← coe_toCLMEquiv, completedGroupAlgebraEquivOfFiniteFree_symm_apply b y, map_sum,
        _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [coe_toCLMEquiv, _root_.smul_apply, smul_eq_mul, ← hhZp_symm]
      rw [extendScalars_apply_basis b]
      rfl
    rw [hfun]
    refine continuous_finsetSum _ fun i _ ↦ continuous_const.mul ?_
    refine continuous_finsetSum _ fun j _ ↦ ?_
    have hcoord_cont : Continuous (completedGroupAlgebra.mapAddMonoidHom Γ
        (b.coord i).toAddMonoidHom) :=
      completedGroupAlgebra.continuous_mapAddMonoidHom
        (b.coord i).continuous_of_finite_of_compactSpace
    have heval_Zp : Continuous (fun μ : D(Γ, ℤ_[p]) ↦
        μ ((basisCoordContinuousMap O b j).comp f)) :=
      (continuous_apply _).comp continuous_induced_dom
    exact (heval_Zp.comp (hZp.symm.continuous.comp hcoord_cont)).smul continuous_const
  let H : D(Γ, O) ≃ₜ completedGroupAlgebra O Γ :=
    { (completedGroupAlgebraEquivOfFiniteFree (Γ := Γ) p O).toEquiv with
      continuous_toFun := continuous_toCompletedGroupAlgebra
      continuous_invFun := hsymm_cont }
  exact H.isHomeomorph

open Topology in
/-- For a profinite group `Γ` and a finite free normed `ℤ_p`-algebra `O` with continuous
`ℤ_p`-action, `D(Γ, O)` is a topological ring for convolution and the weak topology. -/
theorem isTopologicalRing_weak_of_finiteFree (p : ℕ) [Fact p.Prime]
    (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @IsTopologicalRing D(Γ, O) WeakTopology _ := by
  let : TopologicalSpace D(Γ, O) := WeakTopology
  have h := (isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree (Γ := Γ) p O)
    |>.isEmbedding.isInducing
  let : IsTopologicalAddGroup D(Γ, O) :=
    h.isTopologicalAddGroup (toCompletedGroupAlgebra (Γ := Γ) (R := O)).toAddMonoidHom
  let : ContinuousMul D(Γ, O) :=
    h.continuousMul (toCompletedGroupAlgebra (Γ := Γ) (R := O))
  exact
    { continuous_add := continuous_add
      continuous_mul := continuous_mul
      continuous_neg := continuous_neg }

/-- **Weak compactness of `O`-valued measures.** For a profinite group `Γ` and a finite free normed
`ℤ_p`-algebra `O` with continuous `ℤ_p`-action, `D(Γ, O)` is compact for the weak topology. -/
theorem compactSpace_weak_of_finiteFree (p : ℕ) [Fact p.Prime]
    (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    @CompactSpace D(Γ, O) (WeakTopology (X := Γ) (R := O) (E := O)) := by
  let : TopologicalSpace D(Γ, O) := WeakTopology
  have : CompactSpace O := Module.Finite.compactSpace ℤ_[p] O
  exact ((isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree (Γ := Γ) p O).homeomorph
    _).symm.compactSpace

end ProfinitePadicInt

end CompletedGroupAlgebra

section Examples

variable {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]

/-! Sanity checks:
* for `O = ℤ_p`, `baseChangeAlgEquiv ℤ_[p]` is the canonical left-unit equivalence
  `Algebra.TensorProduct.lid`;
* `1 ⊗ₜ dirac ℤ_[p] x` maps to `dirac O x`;
* distinct scalars `a ≠ b` in `O` give distinct measures `a ⊗ₜ dirac ℤ_[p] x ≠ b ⊗ₜ dirac ℤ_[p] x`;
* negative control for `ContinuousSMul ℤ_[p] O`: if `p^n • (1 : O)` does not tend to `0` (as happens
  for `ℤ_p` equipped with an archimedean norm via an abstract field embedding `ℚ_p → ℂ`), the
  `ℤ_p`-action cannot be continuous. -/

example :
    baseChangeAlgEquiv (G := Γ) (R := ℤ_[p]) ℤ_[p] =
      Algebra.TensorProduct.lid ℤ_[p] D(Γ, ℤ_[p]) :=
  AlgEquiv.ext fun z ↦
    TensorProduct.inductionOn z
      (fun r μ ↦ by
        rw [baseChangeAlgEquiv_tmul, extendScalars_self, Algebra.TensorProduct.lid_tmul])
      fun z₁ z₂ hz₁ hz₂ ↦ by rw [map_add, map_add, hz₁, hz₂]

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] (x : Γ) :
    baseChangeAlgEquiv O ((1 : O) ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = dirac O x := by
  simp

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] {a b : O} (hab : a ≠ b) (x : Γ) :
    baseChangeAlgEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) ≠
      baseChangeAlgEquiv O (b ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) := by
  intro h
  apply hab
  have h1 := congrArg (fun ν : D(Γ, O) ↦ ν 1) h
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
