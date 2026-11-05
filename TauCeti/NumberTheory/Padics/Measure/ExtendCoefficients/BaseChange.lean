/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.NumberTheory.Padics.Measure.Basic
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Algebra
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.BaseChange
public import TauCeti.Topology.Algebra.Module.AutomaticContinuity
public import TauCeti.Topology.ContinuousMap.ModuleTopology
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.LinearAlgebra.Basis.Algebra
import TauCeti.RingTheory.TensorProduct.Free

/-!
# Finite-free base change of measures and the completed group algebra

Let `X` be a topological space and `O` a commutative topological `R`-algebra that is finite and
free as an `R`-module and carries the `R`-module topology (`IsModuleTopology R O`). Choosing a
finite `R`-basis of `O` with continuous `R`-linear coordinate functionals decomposes every
continuous test function `F : C(X, O)` as a finite `O`-linear combination of `R`-valued coordinate
functions composed with `algebraMap R O`. Integrating coordinatewise extends each `R`-valued
measure `μ ∈ D(X, R)` to a unique `O`-valued measure `AbstractMeasure.scalarExtend R O μ ∈ D(X, O)`
satisfying `(scalarExtend R O μ) (algebraMap R O ∘ f) = algebraMap R O (μ f)` for all
`f ∈ C(X, R)`. Neither `scalarExtend` nor the resulting `O`-linear isomorphism
`AbstractMeasure.baseChange R O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)` depends on the chosen basis.

On a locally compact topological monoid `G`, scalar extension preserves convolution and upgrades
`baseChange R O` to the `O`-algebra isomorphism
`AbstractMeasure.baseChangeAlgEquiv R O : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)`. On a profinite space `X`,
composing `baseChange R O` with unit-ball coefficient extension `extendCoefficients j hj` into a
complete ultrametric field `K` sends `a ⊗ μ` to `j a` times the extension of `μ` along
`j.comp (algebraMap R O)`.

Over `R = ℤ_[p]`, every finite Hausdorff topological `ℤ_[p]`-algebra `O` with continuous scalar
action (`ContinuousSMul ℤ_[p] O`) automatically carries the `ℤ_[p]`-module topology by
`TauCeti.isModuleTopology_of_finite_of_compactSpace`. Combining `baseChangeAlgEquiv ℤ_[p] O`,
`completedGroupAlgebraEquiv` over `ℤ_[p]`, and `completedGroupAlgebra.baseChangeEquiv ℤ_[p] O Γ`
shows that for any profinite group `Γ`, the comparison map
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is an `O`-algebra isomorphism
(`AbstractMeasure.completedGroupAlgebraEquivOfFiniteFree`), and when `O` is normed it is a
homeomorphism from the weak topology on `D(Γ, O)` to the inverse-limit topology on `O[[Γ]]`.

## Main definitions

* `AbstractMeasure.scalarExtend R O`: the `algebraMap R O`-semilinear extension `D(X, R) → D(X, O)`.
* `AbstractMeasure.scalarExtendRingHom R O`: scalar extension as a ring homomorphism of convolution
  algebras `D(G, R) →+* D(G, O)`.
* `AbstractMeasure.baseChange R O`: the `O`-linear isomorphism `O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`.
* `AbstractMeasure.baseChangeAlgEquiv R O`: the `O`-algebra isomorphism
  `O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)` for a locally compact topological monoid `G`.
* `AbstractMeasure.completedGroupAlgebraEquivOfFiniteFree p O`: the `O`-algebra isomorphism
  `D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ` for a profinite group `Γ` and a finite free Hausdorff
  topological `ℤ_[p]`-algebra `O` with continuous `ℤ_[p]`-action.

## Main results

* `AbstractMeasure.ext_of_apply_comp`, `AbstractMeasure.scalarExtend_apply_comp`,
  `AbstractMeasure.eq_scalarExtend_of_apply_comp`: `O`-valued measures are determined by test
  functions coming from `C(X, R)`, and `scalarExtend R O μ` is characterised by its values on them.
* `AbstractMeasure.extendCoefficients_baseChange_tmul`,
  `AbstractMeasure.eq_extendCoefficients_of_baseChange_tmul`: compatibility of unit-ball
  coefficient extension with finite-free base change on pure tensors, which uniquely determines the
  extension on all `O`-valued measures.
* `AbstractMeasure.toCompletedGroupAlgebra_surjective_of_finiteFree`,
  `AbstractMeasure.compactSpace_measures_weak_of_finiteFree`,
  `AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree`,
  `TauCeti.isTopologicalRing_measures_weak_of_finiteFree`: algebraic and weak-topological
  identification of `D(Γ, O)` with `O[[Γ]]`.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, Section 3.3, Proposition 3.16 and
  Remark 3.28.
-/

public noncomputable section

open ContinuousMap Filter TauCeti Topology
open scoped TensorProduct

namespace AbstractMeasure

section ModuleTopology

variable {X Y G Γ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (R O : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [Algebra R O]
  [IsModuleTopology R O]

section Span

variable [Module.Free R O] [Module.Finite R O]

/-- Two `O`-valued measures on `X` are equal if they agree on all test functions of the form
`algebraMap R O ∘ f` for `f ∈ C(X, R)`. -/
theorem ext_of_apply_comp {ν₁ ν₂ : D(X, O)}
    (h : ∀ f : C(X, R),
      ν₁ ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp f) =
        ν₂ ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp f)) :
    ν₁ = ν₂ := by
  let b := Module.Free.chooseBasis R O
  ext F
  rw [F.eq_sum_smul_algebraMap_comp_coordCLM b, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_smul, h]

end Span

section ScalarExtend

variable [Module.Free R O] [Module.Finite R O]

/-- Extend a single `R`-valued measure to an `O`-valued measure by integrating the coordinates of
each test function in a chosen finite `R`-basis of `O`. -/
private def scalarExtendAux (μ : D(X, R)) : D(X, O) :=
  let b := Module.Free.chooseBasis R O
  let L : C(X, O) →ₗ[O] O :=
    { toFun F := ∑ i, b i * algebraMap R O (μ ((b.coordCLM i : C(O, R)).comp F))
      map_add' F G := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hcomp : (b.coordCLM i : C(O, R)).comp (F + G) =
            (b.coordCLM i : C(O, R)).comp F + (b.coordCLM i : C(O, R)).comp G := by
          ext x
          simp
        rw [hcomp, map_add, map_add, mul_add]
      map_smul' c F := by
        dsimp only [RingHom.id_apply, smul_eq_mul]
        simp_rw [F.coordCLM_comp_smul b _ c, map_sum, map_smul, smul_eq_mul, map_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp_rw [← mul_assoc, ← Finset.sum_mul, b.sum_mul_algebraMap_coord] }
  have hL : Continuous L := continuous_finsetSum _ fun i _ ↦
    continuous_const.mul ((continuous_algebraMap R O).comp
      (μ.continuous.comp (ContinuousMap.continuous_postcomp (b.coordCLM i : C(O, R)))))
  toCLMEquiv.symm ⟨L, hL⟩

private theorem scalarExtendAux_apply_comp (μ : D(X, R)) (f : C(X, R)) :
    scalarExtendAux R O μ ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp f) =
      algebraMap R O (μ f) := by
  simp only [scalarExtendAux, coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, coordCLM_comp_algebraMap_comp, map_smul, smul_eq_mul, map_mul]
  simp_rw [← mul_assoc, ← Finset.sum_mul,
    (Module.Free.chooseBasis R O).sum_mul_algebraMap_coord, one_mul]

/-- **Scalar extension of measures.** When `O` is finite and free over `R` and carries the
`R`-module topology, every `R`-valued measure `μ ∈ D(X, R)` extends uniquely to an `O`-valued
measure `scalarExtend R O μ ∈ D(X, O)` taking the value `algebraMap R O (μ f)` on
`algebraMap R O ∘ f` for every `f ∈ C(X, R)` (`scalarExtend_apply_comp`,
`eq_scalarExtend_of_apply_comp`). -/
def scalarExtend : D(X, R) →ₛₗ[algebraMap R O] D(X, O) where
  toFun := scalarExtendAux R O
  map_add' μ ν := ext_of_apply_comp R O fun f ↦ by
    simp [scalarExtendAux_apply_comp]
  map_smul' r μ := ext_of_apply_comp R O fun f ↦ by
    simp [scalarExtendAux_apply_comp]

/-- Scalar extension of `μ` integrates `algebraMap R O ∘ f` to `algebraMap R O (μ f)`. -/
@[simp]
theorem scalarExtend_apply_comp (μ : D(X, R)) (f : C(X, R)) :
    scalarExtend R O μ ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp f) =
      algebraMap R O (μ f) :=
  scalarExtendAux_apply_comp R O μ f

/-- Any `O`-valued measure taking the value `algebraMap R O (μ f)` on `algebraMap R O ∘ f` for
every `f ∈ C(X, R)` is equal to `scalarExtend R O μ`. -/
theorem eq_scalarExtend_of_apply_comp (μ : D(X, R)) {ν : D(X, O)}
    (hν : ∀ f : C(X, R),
      ν ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp f) =
        algebraMap R O (μ f)) :
    ν = scalarExtend R O μ :=
  ext_of_apply_comp R O fun f ↦ (hν f).trans (scalarExtend_apply_comp R O μ f).symm

/-- Scalar extension from `R` to `R` is the identity map. -/
@[simp]
theorem scalarExtend_self :
    scalarExtend R R = (LinearMap.id : D(X, R) →ₗ[R] D(X, R)) :=
  LinearMap.ext fun μ ↦ (eq_scalarExtend_of_apply_comp R R μ fun _ ↦ rfl).symm

/-- Scalar extension sends Dirac measures to Dirac measures. -/
@[simp]
theorem scalarExtend_dirac (x : X) :
    scalarExtend R O (dirac R x) = dirac O x :=
  (eq_scalarExtend_of_apply_comp R O (dirac R x) fun _ ↦ by simp).symm

/-- Scalar extension commutes with pushforward along continuous maps. -/
@[simp]
theorem scalarExtend_map (φ : C(X, Y)) (μ : D(X, R)) :
    scalarExtend R O (map φ μ) = map φ (scalarExtend R O μ) :=
  (eq_scalarExtend_of_apply_comp R O (map φ μ) fun f ↦ by
    rw [map_apply, map_apply, ContinuousMap.comp_assoc, scalarExtend_apply_comp]).symm

/-- The finite projections of `scalarExtend R O μ` are obtained by applying `algebraMap R O` to the
coefficients of the finite projections of `μ`. -/
@[simp]
theorem finiteProjection_scalarExtend {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] (q : C(X, A)) (μ : D(X, R)) :
    finiteProjection q (scalarExtend R O μ) =
      (finiteProjection q μ).mapRange (algebraMap R O) (map_zero _) := by
  ext a
  rw [finiteProjection_apply, Finsupp.mapRange_apply, finiteProjection_apply,
    ← scalarExtend_apply_comp R O μ (q.fiberIndicator a)]
  congr 1
  ext x
  classical
  by_cases h : q x = a <;> simp [fiberIndicator_apply, h]

end ScalarExtend

section BaseChangeLinear

/-- Apply an `R`-linear functional `φ : O →ₗ[R] R` (automatically continuous under
`IsModuleTopology R O`) to the values of an `O`-valued measure on `R`-valued tests. -/
private def mapCoord (φ : O →ₗ[R] R) : D(X, O) →+ D(X, R) where
  toFun ν :=
    let J : C(R, O) := ⟨algebraMap R O, continuous_algebraMap R O⟩
    let L : C(X, R) →ₗ[R] R :=
      { toFun f := φ (ν (J.comp f))
        map_add' f g := by
          have hcomp : J.comp (f + g) = J.comp f + J.comp g := by
            ext x
            exact map_add (algebraMap R O) (f x) (g x)
          rw [hcomp, map_add, map_add]
        map_smul' r f := by
          have hcomp : J.comp (r • f) = algebraMap R O r • J.comp f := by
            ext x
            simp [J, Algebra.smul_def]
          have hν : ν (algebraMap R O r • J.comp f) = r • ν (J.comp f) := by
            rw [map_smul, smul_eq_mul, ← Algebra.smul_def]
          rw [RingHom.id_apply, hcomp, hν, map_smul] }
    have hL : Continuous L :=
      (IsModuleTopology.continuous_of_linearMap φ).comp
        (ν.continuous.comp (ContinuousMap.continuous_postcomp J))
    toCLMEquiv.symm ⟨L, hL⟩
  map_zero' := ext fun f ↦ by
    simp only [coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    exact map_zero φ
  map_add' ν₁ ν₂ := ext fun f ↦ by simp [_root_.add_apply]

@[simp]
private theorem mapCoord_apply (φ : O →ₗ[R] R) (ν : D(X, O)) (f : C(X, R)) :
    mapCoord R O φ ν f =
      φ (ν ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp f)) := by
  simp [mapCoord]

variable [Module.Free R O] [Module.Finite R O]

@[simp]
private theorem mapCoord_smul_scalarExtend (φ : O →ₗ[R] R) (a : O) (μ : D(X, R)) :
    mapCoord R O φ (a • scalarExtend R O μ) = φ a • μ :=
  ext fun f ↦ by
    simp [LinearMap.map_mul_algebraMap, smul_eq_mul]

private theorem sum_smul_scalarExtend_mapCoord {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (ν : D(X, O)) :
    ∑ i, b i • scalarExtend R O (mapCoord R O (b.coord i) ν) = ν :=
  ext_of_apply_comp R O fun f ↦ by
    simpa [smul_eq_mul] using b.sum_mul_algebraMap_coord _

/-- **Finite-free base change of measures.** When `O` is finite and free as an `R`-module and
carries the `R`-module topology, `O ⊗[R] D(X, R)` is canonically isomorphic as an `O`-module to
`D(X, O)`, sending `a ⊗ μ` to `a • scalarExtend R O μ`. -/
def baseChange : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O) :=
  letI : Module R D(X, O) := Module.compHom D(X, O) (algebraMap R O)
  letI : IsScalarTower R O D(X, O) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let b := Module.Free.chooseBasis R O
  let l : D(X, R) →ₗ[R] D(X, O) :=
    { toFun := scalarExtend R O
      map_add' := map_add (scalarExtend R O)
      map_smul' r μ := map_smulₛₗ (scalarExtend R O) r μ }
  (IsBaseChange.of_basis_coord l b (fun i ↦ mapCoord R O (b.coord i))
    (fun i ↦ mapCoord_smul_scalarExtend R O (b.coord i))
    (sum_smul_scalarExtend_mapCoord R O b)).equiv

/-- On a pure tensor `a ⊗ μ`, `baseChange R O` scales `scalarExtend R O μ` by `a`. -/
@[simp]
theorem baseChange_tmul (a : O) (μ : D(X, R)) :
    baseChange R O (a ⊗ₜ[R] μ) = a • scalarExtend R O μ := by
  let _ : Module R D(X, O) := Module.compHom D(X, O) (algebraMap R O)
  let _ : IsScalarTower R O D(X, O) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact IsBaseChange.equiv_tmul _ a μ

/-- `baseChange R O` sends `a ⊗ dirac R x` to `a • dirac O x`. -/
theorem baseChange_tmul_dirac (a : O) (x : X) :
    baseChange R O (a ⊗ₜ[R] dirac R x) = a • dirac O x := by
  simp

/-- The inverse of `baseChange R O` sends `scalarExtend R O μ` to `1 ⊗ μ`. -/
@[simp]
theorem baseChange_symm_scalarExtend (μ : D(X, R)) :
    (baseChange R O).symm (scalarExtend R O μ) = 1 ⊗ₜ[R] μ := by
  apply (baseChange R O).injective
  simp

/-- The inverse of `baseChange R O` sends `a • scalarExtend R O μ` to `a ⊗ μ`. -/
theorem baseChange_symm_smul_scalarExtend (a : O) (μ : D(X, R)) :
    (baseChange R O).symm (a • scalarExtend R O μ) = a ⊗ₜ[R] μ := by
  apply (baseChange R O).injective
  simp

/-- The inverse of `baseChange R O` sends `dirac O x` to `1 ⊗ dirac R x`. -/
@[simp]
theorem baseChange_symm_dirac (x : X) :
    (baseChange R O).symm (dirac O x) = 1 ⊗ₜ[R] dirac R x := by
  rw [← scalarExtend_dirac R O x, baseChange_symm_scalarExtend]

/-- Over `O = R`, `baseChange R R` is the canonical left unit isomorphism
`R ⊗[R] D(X, R) ≃ₗ[R] D(X, R)`. -/
@[simp]
theorem baseChange_self :
    baseChange R R = TensorProduct.lid R D(X, R) := by
  refine LinearEquiv.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul a μ => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end BaseChangeLinear

section Monoid

variable [TopologicalSpace G] [Monoid G] [ContinuousMul G] [Module.Free R O] [Module.Finite R O]

/-- Right convolution of `scalarExtend R O ν` with `algebraMap R O ∘ f` equals `algebraMap R O`
composed with the right convolution of `ν` with `f`. -/
theorem convolveFunRight_scalarExtend_comp (ν : D(G, R)) (f : C(G, R)) :
    convolveFunRight (scalarExtend R O ν)
        ((⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp f) =
      (⟨algebraMap R O, continuous_algebraMap R O⟩ : C(R, O)).comp (convolveFunRight ν f) := by
  ext x
  simp only [convolveFunRight_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  exact scalarExtend_apply_comp R O ν ⟨fun y ↦ f (x * y), by fun_prop⟩

omit [ContinuousMul G] in
/-- Scalar extension preserves the convolution identity `1 = dirac 1`. -/
@[simp]
theorem scalarExtend_one : scalarExtend R O (1 : D(G, R)) = 1 := by
  simp [one_def]

variable [LocallyCompactSpace G]

/-- Scalar extension preserves convolution of measures on any locally compact topological monoid. -/
@[simp]
theorem scalarExtend_mul (μ ν : D(G, R)) :
    scalarExtend R O (μ * ν) = scalarExtend R O μ * scalarExtend R O ν :=
  ext_of_apply_comp R O fun f ↦ by
    rw [scalarExtend_apply_comp, mul_apply, mul_apply, convolveFunRight_scalarExtend_comp,
      scalarExtend_apply_comp]

/-- Scalar extension of measures as a unital ring homomorphism of convolution algebras. -/
def scalarExtendRingHom : D(G, R) →+* D(G, O) where
  toFun := scalarExtend R O
  map_one' := scalarExtend_one R O
  map_mul' := scalarExtend_mul R O
  map_zero' := map_zero (scalarExtend R O)
  map_add' := map_add (scalarExtend R O)

/-- The ring homomorphism `scalarExtendRingHom` has `scalarExtend` as its underlying function. -/
@[simp]
theorem coe_scalarExtendRingHom :
    ⇑(scalarExtendRingHom (G := G) R O) = scalarExtend R O :=
  (rfl)

/-- **Finite-free base change of the convolution algebra of measures.** On a locally compact
topological monoid `G`, `baseChange R O` is an `O`-algebra isomorphism
`O ⊗[R] D(G, R) ≃ₐ[O] D(G, O)`. -/
def baseChangeAlgEquiv : O ⊗[R] D(G, R) ≃ₐ[O] D(G, O) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (baseChange R O)
    (fun a₁ a₂ μ₁ μ₂ ↦ by
      simp [scalarExtend_mul, smul_smul, mul_comm])
    (by simp)

/-- The forward map of `baseChangeAlgEquiv` is `baseChange`. -/
@[simp]
theorem coe_baseChangeAlgEquiv :
    ⇑(baseChangeAlgEquiv (G := G) R O) = baseChange R O :=
  (rfl)

/-- Applying `baseChangeAlgEquiv` evaluates `baseChange`. -/
theorem baseChangeAlgEquiv_apply (z : O ⊗[R] D(G, R)) :
    baseChangeAlgEquiv R O z = baseChange R O z :=
  (rfl)

/-- The inverse of `baseChangeAlgEquiv` has `(baseChange R O).symm` as its underlying function. -/
@[simp]
theorem coe_baseChangeAlgEquiv_symm :
    ⇑(baseChangeAlgEquiv (G := G) R O).symm = (baseChange R O).symm :=
  (rfl)

/-- `baseChange R O` preserves the multiplicative identity of the convolution algebra. -/
@[simp]
theorem baseChange_one : baseChange R O (1 : O ⊗[R] D(G, R)) = 1 :=
  (baseChangeAlgEquiv (G := G) R O).map_one

/-- `baseChange R O` is multiplicative for the convolution product on `O ⊗[R] D(G, R)` and
`D(G, O)`. -/
@[simp]
theorem baseChange_mul (z₁ z₂ : O ⊗[R] D(G, R)) :
    baseChange R O (z₁ * z₂) = baseChange R O z₁ * baseChange R O z₂ :=
  (baseChangeAlgEquiv R O).map_mul z₁ z₂

/-- Over `O = R`, `baseChangeAlgEquiv R R` is the canonical left unit algebra isomorphism. -/
@[simp]
theorem baseChangeAlgEquiv_self :
    baseChangeAlgEquiv R R = Algebra.TensorProduct.lid R D(G, R) := by
  refine AlgEquiv.ext fun z ↦ ?_
  exact LinearEquiv.congr_fun (baseChange_self (X := G) R) z

end Monoid

section CompletedGroupAlgebra

variable [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [ContinuousMul Γ] [LocallyCompactSpace Γ]
  [Module.Free R O] [Module.Finite R O]

/-- `toCompletedGroupAlgebra` intertwines `scalarExtend R O` on measures with
`completedGroupAlgebra.mapRingHom Γ (algebraMap R O)` on the completed group algebra. -/
@[simp]
theorem toCompletedGroupAlgebra_scalarExtend (μ : D(Γ, R)) :
    toCompletedGroupAlgebra (scalarExtend R O μ) =
      completedGroupAlgebra.mapRingHom Γ (algebraMap R O) (toCompletedGroupAlgebra μ) :=
  completedGroupAlgebra.ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ by
    simp

/-- `toCompletedGroupAlgebra` intertwines `baseChange R O` on measures with
`completedGroupAlgebra.baseChangeEquiv R O Γ` on the completed group algebra. -/
theorem toCompletedGroupAlgebra_baseChange (z : O ⊗[R] D(Γ, R)) :
    toCompletedGroupAlgebra (baseChange R O z) =
      completedGroupAlgebra.baseChangeEquiv R O Γ
        (Algebra.TensorProduct.map (AlgHom.id O O) toCompletedGroupAlgebra z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a μ => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end CompletedGroupAlgebra

section ExtendCoefficients

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
  [Module.Free R O] [Module.Finite R O]
  {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)

/-- Extending coefficients of `scalarExtend R O μ` along `j : O →+* K` agrees with extending `μ`
directly along `j.comp (algebraMap R O)`. -/
@[simp]
theorem extendCoefficients_scalarExtend (μ : D(X, R)) :
    extendCoefficients j hj (scalarExtend R O μ) =
      extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ :=
  finiteProjection_ext _ _ fun q ↦ by
    ext a
    simp

/-- **Compatibility of unit-ball coefficient extension with base change.** Extending the
base-changed pure tensor `a ⊗ μ` along `j : O →+* K` produces `j a` times the extension of `μ`
along `j.comp (algebraMap R O)`. -/
theorem extendCoefficients_baseChange_tmul (a : O) (μ : D(X, R)) :
    extendCoefficients j hj (baseChange R O (a ⊗ₜ[R] μ)) =
      j a • extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ := by
  simp

/-- Unit-ball coefficient extension on `D(X, O)` is uniquely determined as an additive map by its
formula on pure tensors `baseChange R O (a ⊗ μ)`. -/
theorem eq_extendCoefficients_of_baseChange_tmul (E : D(X, O) →+ D(X, K))
    (hE : ∀ (a : O) (μ : D(X, R)),
      E (baseChange R O (a ⊗ₜ[R] μ)) =
        j a • extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ) :
    E = extendCoefficients j hj := by
  refine AddMonoidHom.ext fun ν ↦ ?_
  obtain ⟨z, rfl⟩ := (baseChange (X := X) R O).surjective ν
  induction z using TensorProduct.inductionOn with
  | tmul a μ => exact (hE a μ).trans (extendCoefficients_baseChange_tmul R O j hj a μ).symm
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end ExtendCoefficients

end ModuleTopology

section WeakContinuity

variable {X : Type*} [TopologicalSpace X] (R O : Type*) [NormedCommRing R] [NormedCommRing O]
  [Algebra R O] [IsModuleTopology R O] [Module.Free R O] [Module.Finite R O]

/-- Scalar extension of measures is continuous from the weak topology on `D(X, R)` to the weak
topology on `D(X, O)`. -/
theorem continuous_scalarExtend_weak :
    @Continuous D(X, R) D(X, O)
      (WeakTopology (X := X) (R := R) (E := R))
      (WeakTopology (X := X) (R := O) (E := O))
      (scalarExtend R O) := by
  let _ : TopologicalSpace D(X, R) := WeakTopology
  let _ : TopologicalSpace D(X, O) := WeakTopology
  let b := Module.Free.chooseBasis R O
  refine continuous_induced_rng.mpr (continuous_pi fun F ↦ ?_)
  have hF (μ : D(X, R)) : scalarExtend R O μ F =
      ∑ i, b i * algebraMap R O (μ ((b.coordCLM i : C(O, R)).comp F)) := by
    conv_lhs => rw [F.eq_sum_smul_algebraMap_comp_coordCLM b]
    simp only [map_sum, map_smul, scalarExtend_apply_comp, smul_eq_mul]
  simp_rw [Function.comp_def, hF]
  exact continuous_finsetSum _ fun i _ ↦
    continuous_const.mul ((continuous_algebraMap R O).comp
      ((continuous_apply _).comp continuous_induced_dom))

end WeakContinuity

section PadicInt

section ProfiniteGroup

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  (p : ℕ) [Fact p.Prime]
include p

section TopologicalRing

variable (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]

/-- **Surjectivity of the completed group algebra comparison over a finite free `ℤ_[p]`-algebra.**
Every element of `O[[Γ]]` is represented by an `O`-valued measure on the profinite group `Γ`. -/
theorem toCompletedGroupAlgebra_surjective_of_finiteFree :
    Function.Surjective
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  have : IsModuleTopology ℤ_[p] O := TauCeti.isModuleTopology_of_finite_of_compactSpace
  intro y
  let z : O ⊗[ℤ_[p]] D(Γ, ℤ_[p]) :=
    Algebra.TensorProduct.map (AlgHom.id O O) completedGroupAlgebraEquiv.symm.toAlgHom
      ((completedGroupAlgebra.baseChangeEquiv ℤ_[p] O Γ).symm y)
  refine ⟨baseChange ℤ_[p] O z, ?_⟩
  rw [toCompletedGroupAlgebra_baseChange]
  have hmap : Algebra.TensorProduct.map (AlgHom.id O O) toCompletedGroupAlgebra z =
      (completedGroupAlgebra.baseChangeEquiv ℤ_[p] O Γ).symm y := by
    dsimp only [z]
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
    have hid : (toCompletedGroupAlgebra : D(Γ, ℤ_[p]) →ₐ[ℤ_[p]] _).comp
        completedGroupAlgebraEquiv.symm.toAlgHom = AlgHom.id ℤ_[p] _ :=
      AlgHom.ext fun x ↦ by simp [← completedGroupAlgebraEquiv_apply]
    rw [hid, AlgHom.id_comp, Algebra.TensorProduct.map_id, AlgHom.id_apply]
  rw [hmap, AlgEquiv.apply_symm_apply]

/-- **`O`-valued measures are the completed group algebra.** For a profinite group `Γ` and a
finite free Hausdorff topological `ℤ_[p]`-algebra `O` with continuous `ℤ_[p]`-action, `D(Γ, O)` is
canonically isomorphic as an `O`-algebra to `O[[Γ]]`. -/
def completedGroupAlgebraEquivOfFiniteFree :
    D(Γ, O) ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective toCompletedGroupAlgebra
    ⟨toCompletedGroupAlgebra_injective, toCompletedGroupAlgebra_surjective_of_finiteFree p O⟩

/-- `completedGroupAlgebraEquivOfFiniteFree` has `toCompletedGroupAlgebra` as its forward map. -/
@[simp]
theorem completedGroupAlgebraEquivOfFiniteFree_apply (μ : D(Γ, O)) :
    completedGroupAlgebraEquivOfFiniteFree p O μ = toCompletedGroupAlgebra μ :=
  AlgEquiv.ofBijective_apply _ _ _

/-- `completedGroupAlgebraEquivOfFiniteFree` sends `dirac O γ` to
`completedGroupAlgebra.of O Γ γ`. -/
theorem completedGroupAlgebraEquivOfFiniteFree_dirac (γ : Γ) :
    completedGroupAlgebraEquivOfFiniteFree p O (dirac O γ) = completedGroupAlgebra.of O Γ γ := by
  simp

end TopologicalRing

section NormedCommRing

variable (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
  [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]

/-- **Weak compactness of `O`-valued measures.** On a profinite group `Γ`, the space `D(Γ, O)` over
a finite free normed `ℤ_[p]`-algebra `O` with continuous `ℤ_[p]`-action is compact for the weak
topology. -/
theorem compactSpace_measures_weak_of_finiteFree :
    @CompactSpace D(Γ, O) (WeakTopology (X := Γ) (R := O) (E := O)) := by
  have : IsModuleTopology ℤ_[p] O := TauCeti.isModuleTopology_of_finite_of_compactSpace
  let _ : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  let _ : TopologicalSpace D(Γ, O) := WeakTopology
  have : CompactSpace D(Γ, ℤ_[p]) := compactSpace_integralMeasures_weak
  let b := Module.Free.chooseBasis ℤ_[p] O
  let Φ : (Module.Free.ChooseBasisIndex ℤ_[p] O → D(Γ, ℤ_[p])) → D(Γ, O) :=
    fun c ↦ ∑ i, b i • scalarExtend ℤ_[p] O (c i)
  have hΦ_cont : Continuous Φ := by
    refine continuous_induced_rng.mpr (continuous_pi fun F ↦ ?_)
    have hΦF (c : Module.Free.ChooseBasisIndex ℤ_[p] O → D(Γ, ℤ_[p])) :
        Φ c F = ∑ i, b i * scalarExtend ℤ_[p] O (c i) F := by
      simp only [Φ, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
    simp_rw [Function.comp_def, hΦF]
    refine continuous_finsetSum _ fun i _ ↦ continuous_const.mul ?_
    exact ((continuous_apply F).comp continuous_induced_dom).comp
      ((continuous_scalarExtend_weak ℤ_[p] O).comp (continuous_apply i))
  have hΦ_surj : Function.Surjective Φ :=
    fun ν ↦ ⟨fun i ↦ mapCoord ℤ_[p] O (b.coord i) ν, sum_smul_scalarExtend_mapCoord ℤ_[p] O b ν⟩
  exact hΦ_surj.compactSpace hΦ_cont

/-- **The completed group algebra comparison is a weak homeomorphism.** For a profinite group `Γ`
and a finite free normed `ℤ_[p]`-algebra `O` with continuous `ℤ_[p]`-action,
`toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] O[[Γ]]` is a homeomorphism from the weak topology on
measures to the inverse-limit topology. -/
theorem isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree :
    @IsHomeomorph D(Γ, O) (completedGroupAlgebra O Γ)
      (WeakTopology (X := Γ) (R := O) (E := O)) _
      (toCompletedGroupAlgebra : D(Γ, O) →ₐ[O] completedGroupAlgebra O Γ) := by
  let _ : TopologicalSpace D(Γ, O) := WeakTopology
  have : CompactSpace D(Γ, O) := compactSpace_measures_weak_of_finiteFree p O
  exact isHomeomorph_iff_continuous_bijective.mpr
    ⟨continuous_toCompletedGroupAlgebra, (completedGroupAlgebraEquivOfFiniteFree p O).bijective⟩

/-- Over a finite free normed `ℤ_[p]`-algebra `O` with continuous `ℤ_[p]`-action, `O`-valued
measures on a profinite group form a topological ring for convolution and the weak topology. -/
theorem _root_.TauCeti.isTopologicalRing_measures_weak_of_finiteFree :
    @IsTopologicalRing D(Γ, O) (WeakTopology (X := Γ) (R := O) (E := O)) _ := by
  let _ : TopologicalSpace D(Γ, O) := WeakTopology
  have h := (isHomeomorph_toCompletedGroupAlgebra_weak_of_finiteFree
    (Γ := Γ) p O).isEmbedding.isInducing
  let _ : IsTopologicalAddGroup D(Γ, O) :=
    h.isTopologicalAddGroup (toCompletedGroupAlgebra (Γ := Γ) (R := O)).toAddMonoidHom
  let _ : ContinuousMul D(Γ, O) :=
    h.continuousMul (toCompletedGroupAlgebra (Γ := Γ) (R := O))
  exact
    { continuous_add := continuous_add
      continuous_mul := continuous_mul
      continuous_neg := continuous_neg }

end NormedCommRing

end ProfiniteGroup

section Examples

variable {p : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]

/-! Checks on the base-change equivalence over `ℤ_[p]`: triviality at `O = ℤ_[p]`, preservation of
Dirac measures at `1 ⊗ δ_x`, separation of distinct scalar multiples `a ⊗ δ_x` and `b ⊗ δ_x`, and
failure of `ContinuousSMul ℤ_[p] O` when `p^n • 1` does not tend to zero. -/

example :
    baseChange (X := X) ℤ_[p] ℤ_[p] = TensorProduct.lid ℤ_[p] D(X, ℤ_[p]) := by
  simp

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [IsModuleTopology ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] (x : X) :
    baseChange ℤ_[p] O (1 ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) = dirac O x := by
  simp

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O] [IsModuleTopology ℤ_[p] O]
    [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O] {a b : O} (hab : a ≠ b) (x : X) :
    baseChange ℤ_[p] O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) ≠
      baseChange ℤ_[p] O (b ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x) := by
  intro h
  apply hab
  have heval := congrArg (fun ν : D(X, O) ↦ ν (ContinuousMap.const X 1)) h
  simpa [_root_.smul_apply] using heval

example (O : Type*) [NormedCommRing O] [Algebra ℤ_[p] O]
    (h : ¬ Tendsto (fun n : ℕ ↦ ((p : ℤ_[p]) ^ n) • (1 : O)) atTop (𝓝 0)) :
    ¬ ContinuousSMul ℤ_[p] O := by
  intro hsmul
  apply h
  have hp : Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simp [PadicInt.norm_p, ← Padic.norm_p])
  exact hp.zero_smul_const (1 : O)

end Examples

end PadicInt

end AbstractMeasure
