/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.Grassmannian.Chart.Basic

import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Transition maps between the standard charts of the Grassmannian

Let `M` be a module over a commutative ring `R` and let `x y : Fin k → M`. A point `N` of the
chart of `G(k, M; R)` at `x` is the kernel of a unique linear map `φ : M → R^k` with
`φ (x i) = eᵢ` (`Module.Grassmannian.chartEquiv`). Its **transition matrix** to `y`,
`Module.Grassmannian.chartMatrix N y`, has `j`-th column `φ (y j)`: the coordinates of the image of
`y j` in the basis of `M ⧸ N` given by the images of the `x i`. The point `N` lies in the chart at
`y` exactly when this matrix is invertible, that is, when its determinant is a unit
(`Module.Grassmannian.mem_chart_iff_isUnit_det_chartMatrix`), and then the linear maps attached to
`N` in the two charts are related by the transition matrix
(`Module.Grassmannian.chartEquiv_apply_eq_chartMatrix_mulVec`).

Applied to the universal point of the chart at `x`, this describes the overlap of two charts as a
basic open set. The determinant `Module.Grassmannian.ChartAlgebra.transitionDet R x y` of the
universal transition matrix lies in the coordinate ring `ChartAlgebra R x` of the chart at `x`, and
the point of the chart at `x` classified by `g : ChartAlgebra R x →ₐ[R] A` lies in the chart at `y`
exactly when `g (transitionDet R x y)` is a unit
(`Module.Grassmannian.chartHomEquiv_mem_chart_iff`). So inside `Spec (ChartAlgebra R x)` the chart
at `y` is the basic open set of `transitionDet R x y`: the overlap of the two charts is
corepresented by the localization `Module.Grassmannian.OverlapAlgebra R x y` of `ChartAlgebra R x`
away from `transitionDet R x y` (`Module.Grassmannian.overlapHomEquiv`,
`Module.Grassmannian.overlapCorepresentableBy`).

Since `OverlapAlgebra R x y` and `OverlapAlgebra R y x` corepresent the same points, they are
isomorphic. The **transition isomorphism**
`Module.Grassmannian.transitionAlgEquiv R x y : OverlapAlgebra R y x ≃ₐ[R] OverlapAlgebra R x y`
is the isomorphism compatible with the points
(`Module.Grassmannian.overlapHomEquiv_comp_transitionAlgEquiv`). On the universal points it is
given by the universal transition matrix
(`Module.Grassmannian.transitionMatrix_mulVec_transitionAlgEquiv`), its inverse is the transition
isomorphism in the other direction (`Module.Grassmannian.transitionAlgEquiv_symm`), and it is the
identity on the overlap of a chart with itself (`Module.Grassmannian.transitionAlgEquiv_self`).
Under `Spec`, these are the transition maps along which the charts glue to the Grassmannian
scheme.

## Main definitions

* `Module.Grassmannian.chartMatrix N y`: the transition matrix to `y` of a point `N` of a chart.
* `Module.Grassmannian.ChartAlgebra.transitionMatrix R x y` and
  `Module.Grassmannian.ChartAlgebra.transitionDet R x y`: the universal transition matrix from the
  chart at `x` to `y`, and its determinant.
* `Module.Grassmannian.OverlapAlgebra R x y`: the coordinate ring of the overlap of the charts at
  `x` and `y`, the localization of `ChartAlgebra R x` away from `transitionDet R x y`.
* `Module.Grassmannian.overlapHomEquiv R x y A`: `R`-algebra maps `OverlapAlgebra R x y → A` are the
  points over `A` lying in both charts.
* `Module.Grassmannian.transitionAlgEquiv R x y`: the transition isomorphism
  `OverlapAlgebra R y x ≃ₐ[R] OverlapAlgebra R x y`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open CategoryTheory TensorProduct Matrix

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

section ChartMatrix

/-- The **transition matrix** to `y : Fin k → M` of a point `N` of the chart at `x`: its `j`-th
column is `φ (y j)`, where `φ : M → R^k` is the linear map with kernel `N` and `φ (x i) = eᵢ`. These
are the coordinates of the image of `y j` in the basis of `M ⧸ N` given by the images of the
`x i`. -/
noncomputable def chartMatrix {x : Fin k → M} (N : chart R x) (y : Fin k → M) :
    Matrix (Fin k) (Fin k) R :=
  .of fun i j ↦ (chartEquiv R x N).1 (y j) i

@[simp]
theorem chartMatrix_apply {x : Fin k → M} (N : chart R x) (y : Fin k → M) (i j : Fin k) :
    chartMatrix N y i j = (chartEquiv R x N).1 (y j) i :=
  (rfl)

/-- The transition matrix of a point of the chart at `x` to `x` itself is the identity. -/
@[simp]
theorem chartMatrix_self {x : Fin k → M} (N : chart R x) : chartMatrix N x = 1 := by
  ext i j
  simp [Matrix.one_apply, Pi.single_apply]

/-- A point `N` of the chart at `x` lies in the chart at `y` exactly when its transition matrix to
`y` is invertible, that is, when the determinant of this matrix is a unit. -/
theorem mem_chart_iff_isUnit_det_chartMatrix {x : Fin k → M} (N : chart R x) (y : Fin k → M) :
    N.1 ∈ chart R y ↔ IsUnit (chartMatrix N y).det := by
  -- `R^k → M ⧸ N` given by `y` is `R^k ≃ M ⧸ N` after the endomorphism `φ ∘ y` of `R^k`
  have h : N.1.toSubmodule.mkQ ∘ₗ Fintype.linearCombination R y =
      (chartQuotEquiv N).toLinearMap ∘ₗ (chartEquiv R x N).1 ∘ₗ Fintype.linearCombination R y :=
    LinearMap.ext fun v ↦ (chartQuotEquiv_chartEquiv_apply x N _).symm
  have hmat : LinearMap.toMatrix' ((chartEquiv R x N).1 ∘ₗ Fintype.linearCombination R y) =
      chartMatrix N y := by
    ext i j
    simp [LinearMap.toMatrix'_apply, Fintype.linearCombination_apply_single]
  rw [mem_chart_iff, h, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
    ← Module.End.isUnit_iff, LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix', hmat]

/-- If `N` lies in the charts at `x` and at `y`, the linear map `M → R^k` attached to `N` in the
chart at `x` is the one attached to `N` in the chart at `y`, followed by the transition matrix of
`N` to `y`. -/
theorem chartEquiv_apply_eq_chartMatrix_mulVec {x y : Fin k → M} {N : G(k, M; R)}
    (hx : N ∈ chart R x) (hy : N ∈ chart R y) (m : M) :
    (chartEquiv R x ⟨N, hx⟩).1 m = chartMatrix ⟨N, hx⟩ y *ᵥ (chartEquiv R y ⟨N, hy⟩).1 m := by
  -- both sides are linear in `m` and agree on `N` and on the `y j`, which together span `M`
  have hspan : Submodule.span R ((N.toSubmodule : Set M) ∪ Set.range y) = ⊤ := by
    rw [Submodule.span_union, Submodule.span_eq, ← mem_chart_iff_sup_eq_top.1 hy]
  refine LinearMap.congr_fun (LinearMap.ext_on hspan (f := (chartEquiv R x ⟨N, hx⟩).1)
    (g := (chartMatrix ⟨N, hx⟩ y).mulVecLin ∘ₗ (chartEquiv R y ⟨N, hy⟩).1) ?_) m
  rintro m (hm | ⟨j, rfl⟩)
  · have hmx : m ∈ LinearMap.ker (chartEquiv R x ⟨N, hx⟩).1 := by
      rwa [ker_chartEquiv_apply]
    have hmy : m ∈ LinearMap.ker (chartEquiv R y ⟨N, hy⟩).1 := by
      rwa [ker_chartEquiv_apply]
    rw [LinearMap.mem_ker] at hmx hmy
    simp [hmx, hmy]
  · ext i
    simp

end ChartMatrix

section ChartAlgebra

variable (R)

namespace ChartAlgebra

/-- The **universal transition matrix** from the chart at `x` to `y`: the transition matrix to `y`
of the universal point of the chart at `x`, with entries in `ChartAlgebra R x`. -/
noncomputable def transitionMatrix (x y : Fin k → M) : Matrix (Fin k) (Fin k) (ChartAlgebra R x) :=
  .of fun i j ↦ universalLinearMap R x (y j) i

@[simp]
theorem transitionMatrix_apply (x y : Fin k → M) (i j : Fin k) :
    transitionMatrix R x y i j = universalLinearMap R x (y j) i :=
  (rfl)

/-- The determinant of the universal transition matrix from the chart at `x` to `y`. Inside
`Spec (ChartAlgebra R x)`, the chart at `y` is its basic open set
(`Module.Grassmannian.chartHomEquiv_mem_chart_iff`). -/
noncomputable def transitionDet (x y : Fin k → M) : ChartAlgebra R x :=
  (transitionMatrix R x y).det

theorem transitionDet_def (x y : Fin k → M) :
    transitionDet R x y = (transitionMatrix R x y).det :=
  (rfl)

@[simp]
theorem transitionMatrix_self (x : Fin k → M) : transitionMatrix R x x = 1 := by
  ext i j
  simp [Matrix.one_apply, Pi.single_apply]

@[simp]
theorem transitionDet_self (x : Fin k → M) : transitionDet R x x = 1 := by
  simp [transitionDet_def]

end ChartAlgebra

open ChartAlgebra

variable {R} {A : Type w} [CommRing A] [Algebra R A]

/-- The transition matrix to `y` of the point of the chart at `x` classified by `g` is the image
under `g` of the universal transition matrix. -/
@[simp]
theorem chartMatrix_chartHomEquiv (x y : Fin k → M) (g : ChartAlgebra R x →ₐ[R] A) :
    chartMatrix (chartHomEquiv R x A g) (fun i ↦ (1 : A) ⊗ₜ[R] y i) =
      g.mapMatrix (transitionMatrix R x y) := by
  ext i j
  simp

/-- **The overlap of two charts is a basic open set.** The point of the chart at `x` classified by
`g : ChartAlgebra R x →ₐ[R] A` lies in the chart at `y` exactly when `g (transitionDet R x y)` is a
unit. -/
theorem chartHomEquiv_mem_chart_iff (x y : Fin k → M) (g : ChartAlgebra R x →ₐ[R] A) :
    (chartHomEquiv R x A g).1 ∈ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i) ↔
      IsUnit (g (transitionDet R x y)) := by
  rw [mem_chart_iff_isUnit_det_chartMatrix, chartMatrix_chartHomEquiv, transitionDet_def,
    AlgHom.map_det]

end ChartAlgebra

section Overlap

open ChartAlgebra

variable (R)

/-- The coordinate ring of the overlap of the charts at `x` and at `y`: the localization of the
coordinate ring `ChartAlgebra R x` of the chart at `x` away from the determinant
`transitionDet R x y` of the universal transition matrix. Its `R`-algebra maps to `A` are the points
over `A` lying in both charts (`Module.Grassmannian.overlapHomEquiv`). -/
abbrev OverlapAlgebra (x y : Fin k → M) : Type (max u v) :=
  Localization.Away (transitionDet R x y)

variable {A : Type w} [CommRing A] [Algebra R A]

-- A point lying in the charts at `x` and at `y` is classified, in the chart at `x`, by a map
-- sending `transitionDet R x y` to a unit.
private lemma isUnit_chartHomEquiv_symm_transitionDet (x y : Fin k → M)
    (N : ↥(chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∩ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i))) :
    IsUnit ((chartHomEquiv R x A).symm ⟨N.1, Set.mem_of_mem_inter_left N.2⟩
      (transitionDet R x y)) :=
  (chartHomEquiv_mem_chart_iff x y _).1 <| by simpa using Set.mem_of_mem_inter_right N.2

/-- `R`-algebra maps `OverlapAlgebra R x y → A` are the points of `G(k, A ⊗[R] M; A)` lying in the
charts at `x` and at `y`: the point attached to `g` is the point of the chart at `x` classified by
the restriction of `g` to `ChartAlgebra R x`. -/
noncomputable def overlapHomEquiv (x y : Fin k → M) (A : Type w) [CommRing A] [Algebra R A] :
    (OverlapAlgebra R x y →ₐ[R] A) ≃
      ↥(chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∩ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i)) where
  toFun g := ⟨(chartHomEquiv R x A (g.comp (IsScalarTower.toAlgHom R _ _))).1, Subtype.prop _,
    (chartHomEquiv_mem_chart_iff x y _).2 <|
      (IsLocalization.Away.algebraMap_isUnit (transitionDet R x y)).map g⟩
  invFun N := IsLocalization.Away.liftAlgHom _ (isUnit_chartHomEquiv_symm_transitionDet R x y N)
  left_inv g := by
    refine IsLocalization.algHom_ext (Submonoid.powers (transitionDet R x y))
      (AlgHom.ext fun a ↦ ?_)
    simp [Algebra.algHom]
  right_inv N := Subtype.ext <| by
    -- the restriction of the lift to `ChartAlgebra R x` is the map classifying `N`
    have : (IsLocalization.Away.liftAlgHom _ (isUnit_chartHomEquiv_symm_transitionDet R x y N)).comp
        (IsScalarTower.toAlgHom R _ (OverlapAlgebra R x y)) =
          (chartHomEquiv R x A).symm ⟨N.1, Set.mem_of_mem_inter_left N.2⟩ :=
      AlgHom.ext fun a ↦ by simp
    simp [this]

variable {R}

@[simp]
theorem coe_overlapHomEquiv_apply (x y : Fin k → M) (g : OverlapAlgebra R x y →ₐ[R] A) :
    (overlapHomEquiv R x y A g : G(k, A ⊗[R] M; A)) =
      (chartHomEquiv R x A (g.comp (IsScalarTower.toAlgHom R _ _))).1 :=
  (rfl)

@[simp]
theorem overlapHomEquiv_symm_apply_algebraMap (x y : Fin k → M)
    (N : ↥(chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∩ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i)))
    (a : ChartAlgebra R x) :
    (overlapHomEquiv R x y A).symm N (algebraMap _ _ a) =
      (chartHomEquiv R x A).symm ⟨N.1, (Set.mem_of_mem_inter_left N.2)⟩ a := by
  simp [overlapHomEquiv]

/-- The linear map `A ⊗[R] M → A^k` attached in the chart at `x` to the point classified by
`g : OverlapAlgebra R x y →ₐ[R] A` sends `1 ⊗ₜ m` to the image under `g` of the universal point at
`m`. -/
theorem chartEquiv_overlapHomEquiv_apply_tmul (x y : Fin k → M) (g : OverlapAlgebra R x y →ₐ[R] A)
    (m : M) (j : Fin k) :
    (chartEquiv A _ ⟨(overlapHomEquiv R x y A g).1,
      (Set.mem_of_mem_inter_left (overlapHomEquiv R x y A g).2)⟩).1 (1 ⊗ₜ m) j =
      g (algebraMap _ _ (universalLinearMap R x m j)) :=
  chartEquiv_chartHomEquiv_apply_tmul x _ m j

/-- `overlapHomEquiv` is natural: composing with `f : A → B` corresponds to base change of points
along `f`. -/
theorem overlapHomEquiv_comp (x y : Fin k → M) {B : Type w} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (g : OverlapAlgebra R x y →ₐ[R] A) :
    (overlapHomEquiv R x y B (f.comp g)).1 = map f (overlapHomEquiv R x y A g).1 := by
  simpa [AlgHom.comp_assoc] using chartHomEquiv_comp x f (g.comp (IsScalarTower.toAlgHom R _ _))

/-- The overlap of the chart subfunctors at `x` and at `y` is corepresented by
`OverlapAlgebra R x y`. -/
noncomputable def overlapCorepresentableBy (x y : Fin k → M) :
    (chartFunctor.{u, v, max u v} R x ⊓ chartFunctor R y).toFunctor.CorepresentableBy
      (CommAlgCat.of R (OverlapAlgebra R x y)) where
  homEquiv {A} := ConcreteCategory.homEquiv.trans <|
    (overlapHomEquiv R x y A.carrier).trans <| Equiv.subtypeEquivRight fun N ↦
      (and_congr (mem_chartFunctor_obj_iff x A N) (mem_chartFunctor_obj_iff y A N)).symm
  homEquiv_comp f g := Subtype.ext <| by exact overlapHomEquiv_comp x y f.hom g.hom

end Overlap

section Transition

open ChartAlgebra

variable (R)

-- The universal transition matrix from `x` to `y`, moved to `OverlapAlgebra R x y`, where its
-- determinant is a unit.
private lemma isUnit_det_map_transitionMatrix (x y : Fin k → M) :
    IsUnit ((algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)).mapMatrix
      (transitionMatrix R x y)).det := by
  rw [← RingHom.map_det, ← transitionDet_def]
  exact IsLocalization.Away.algebraMap_isUnit _

-- The linear map `M → (OverlapAlgebra R x y)^k` attached in the chart at `y` to the universal point
-- of the overlap: the universal point of the chart at `x`, multiplied by the inverse of the
-- universal transition matrix.
private noncomputable def transitionLinearMap (x y : Fin k → M) :
    M →ₗ[R] Fin k → OverlapAlgebra R x y :=
  ((algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)).mapMatrix
      (transitionMatrix R x y))⁻¹.mulVecLin.restrictScalars R ∘ₗ
    (IsScalarTower.toAlgHom R (ChartAlgebra R x) (OverlapAlgebra R x y)).toLinearMap.compLeft
      (Fin k) ∘ₗ universalLinearMap R x

private lemma transitionLinearMap_apply (x y : Fin k → M) (m : M) :
    transitionLinearMap R x y m = ((algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)).mapMatrix
      (transitionMatrix R x y))⁻¹ *ᵥ fun i ↦ algebraMap _ _ (universalLinearMap R x m i) :=
  rfl

-- The universal point of the chart at `x`, moved to `OverlapAlgebra R x y`, sends `y j` to the
-- `j`-th column of the universal transition matrix and `x j` to the `j`-th basis vector.
private lemma algebraMap_universalLinearMap_eq_mulVec (x y : Fin k → M) (j : Fin k) :
    (fun i ↦ algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)
      (universalLinearMap R x (y j) i)) =
      (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)).mapMatrix (transitionMatrix R x y) *ᵥ
        Pi.single j 1 := by
  ext i
  simp

private lemma transitionLinearMap_apply_right (x y : Fin k → M) (j : Fin k) :
    transitionLinearMap R x y (y j) = Pi.single j 1 := by
  rw [transitionLinearMap_apply, algebraMap_universalLinearMap_eq_mulVec, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_det_map_transitionMatrix R x y), one_mulVec]

private lemma mulVec_transitionLinearMap (x y : Fin k → M) (m : M) :
    (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)).mapMatrix (transitionMatrix R x y) *ᵥ
      transitionLinearMap R x y m = fun i ↦ algebraMap _ _ (universalLinearMap R x m i) := by
  rw [transitionLinearMap_apply, mulVec_mulVec,
    mul_nonsing_inv _ (isUnit_det_map_transitionMatrix R x y), one_mulVec]

private lemma transitionLinearMap_apply_left (x y : Fin k → M) (j : Fin k) :
    transitionLinearMap R x y (x j) =
      ((algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)).mapMatrix
        (transitionMatrix R x y))⁻¹ *ᵥ Pi.single j 1 := by
  rw [transitionLinearMap_apply]
  congr 1
  ext i
  simp [Pi.single_apply, apply_ite (algebraMap _ _)]

-- The map `ChartAlgebra R y → OverlapAlgebra R x y` classifying the universal point of the overlap
-- in the chart at `y`.
private noncomputable def transitionChartHom (x y : Fin k → M) :
    ChartAlgebra R y →ₐ[R] OverlapAlgebra R x y :=
  (ChartAlgebra.homEquiv R y).symm
    ⟨transitionLinearMap R x y, transitionLinearMap_apply_right R x y⟩

private lemma transitionChartHom_universalLinearMap (x y : Fin k → M) (m : M) (j : Fin k) :
    transitionChartHom R x y (universalLinearMap R y m j) = transitionLinearMap R x y m j :=
  homEquiv_symm_apply_universalLinearMap R y _ m j

private lemma isUnit_transitionChartHom_transitionDet (x y : Fin k → M) :
    IsUnit (transitionChartHom R x y (transitionDet R y x)) := by
  -- the image of the universal transition matrix from `y` to `x` is the inverse of the one from
  -- `x` to `y`
  have h : (transitionChartHom R x y).mapMatrix (transitionMatrix R y x) =
      ((algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)).mapMatrix
        (transitionMatrix R x y))⁻¹ := by
    ext i j
    simp [transitionChartHom_universalLinearMap, transitionLinearMap_apply_left]
  rw [transitionDet_def R y x, AlgHom.map_det, h]
  exact isUnit_nonsing_inv_det _ (isUnit_det_map_transitionMatrix R x y)

-- The transition map, before it is shown to be an isomorphism.
private noncomputable def transitionAlgHom (x y : Fin k → M) :
    OverlapAlgebra R y x →ₐ[R] OverlapAlgebra R x y :=
  IsLocalization.Away.liftAlgHom (transitionDet R y x)
    (isUnit_transitionChartHom_transitionDet R x y)

private lemma transitionAlgHom_algebraMap (x y : Fin k → M) (m : M) (j : Fin k) :
    transitionAlgHom R x y (algebraMap _ _ (universalLinearMap R y m j)) =
      transitionLinearMap R x y m j := by
  simp [transitionAlgHom, transitionChartHom_universalLinearMap]

variable {R}

-- The transition map is compatible with the points of the two overlaps.
private lemma overlapHomEquiv_comp_transitionAlgHom (x y : Fin k → M) {A : Type w} [CommRing A]
    [Algebra R A] (g : OverlapAlgebra R x y →ₐ[R] A) :
    (overlapHomEquiv R y x A (g.comp (transitionAlgHom R x y))).1 =
      (overlapHomEquiv R x y A g).1 := by
  have hx := Set.mem_of_mem_inter_left (overlapHomEquiv R x y A g).2
  have hy := Set.mem_of_mem_inter_right (overlapHomEquiv R x y A g).2
  -- both points lie in the chart at `y`; compare the linear maps attached to them there
  refine congrArg Subtype.val ((chartBaseChangeEquiv R A y).injective (a₁ :=
    ⟨_, Set.mem_of_mem_inter_left (overlapHomEquiv R y x A (g.comp (transitionAlgHom R x y))).2⟩)
    (a₂ := ⟨_, hy⟩) (Subtype.ext <| LinearMap.ext fun m ↦ ?_))
  rw [chartBaseChangeEquiv_apply_apply, chartBaseChangeEquiv_apply_apply]
  -- the transition matrix `D` of the point classified by `g` is invertible, and multiplying by it
  -- carries the linear maps attached to the two points in the chart at `y` to the same linear map
  have hD := (mem_chart_iff_isUnit_det_chartMatrix ⟨_, hx⟩ _).1 hy
  refine (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hD)).eq_iff.1 ?_
  rw [← chartEquiv_apply_eq_chartMatrix_mulVec hx hy]
  have hQ : (chartEquiv A _ ⟨_, Set.mem_of_mem_inter_left
      (overlapHomEquiv R y x A (g.comp (transitionAlgHom R x y))).2⟩).1 (1 ⊗ₜ m) =
        g ∘ transitionLinearMap R x y m := funext fun j ↦ by
    rw [chartEquiv_overlapHomEquiv_apply_tmul, AlgHom.comp_apply, transitionAlgHom_algebraMap,
      Function.comp_apply]
  ext i
  rw [hQ, chartEquiv_overlapHomEquiv_apply_tmul, ← congrFun (mulVec_transitionLinearMap R x y m) i,
    ← AlgHom.coe_toRingHom, RingHom.map_mulVec]
  simp only [AlgHom.coe_toRingHom]
  congr 2
  ext
  simp

variable (R)

/-- The **transition isomorphism** from the overlap of the charts at `y` and `x` to the overlap of
the charts at `x` and `y`: the `R`-algebra isomorphism
`OverlapAlgebra R y x ≃ₐ[R] OverlapAlgebra R x y` compatible with the points of the two overlaps
(`Module.Grassmannian.overlapHomEquiv_comp_transitionAlgEquiv`). Under `Spec`, it is the transition
map from the overlap inside the chart at `x` to the overlap inside the chart at `y`. -/
noncomputable def transitionAlgEquiv (x y : Fin k → M) :
    OverlapAlgebra R y x ≃ₐ[R] OverlapAlgebra R x y :=
  AlgEquiv.ofAlgHom (transitionAlgHom R x y) (transitionAlgHom R y x)
    ((overlapHomEquiv R x y _).injective <| Subtype.ext <|
      (overlapHomEquiv_comp_transitionAlgHom y x _).trans <| by
        simpa using overlapHomEquiv_comp_transitionAlgHom x y (AlgHom.id R _))
    ((overlapHomEquiv R y x _).injective <| Subtype.ext <|
      (overlapHomEquiv_comp_transitionAlgHom x y _).trans <| by
        simpa using overlapHomEquiv_comp_transitionAlgHom y x (AlgHom.id R _))

variable {R}

/-- The transition isomorphism is compatible with the points of the two overlaps: precomposing
`g : OverlapAlgebra R x y →ₐ[R] A` with it gives the map classifying the same point of
`G(k, A ⊗[R] M; A)`, now as a point of the overlap of the charts at `y` and `x`. -/
theorem overlapHomEquiv_comp_transitionAlgEquiv (x y : Fin k → M) {A : Type w} [CommRing A]
    [Algebra R A] (g : OverlapAlgebra R x y →ₐ[R] A) :
    (overlapHomEquiv R y x A
        (g.comp (transitionAlgEquiv R x y : OverlapAlgebra R y x →ₐ[R] OverlapAlgebra R x y))).1 =
      (overlapHomEquiv R x y A g).1 :=
  overlapHomEquiv_comp_transitionAlgHom x y g

/-- The transition isomorphism on the universal points: the universal point of the chart at `y`,
moved along the transition isomorphism and multiplied by the universal transition matrix from `x`
to `y`, is the universal point of the chart at `x`. -/
theorem transitionMatrix_mulVec_transitionAlgEquiv (x y : Fin k → M) (m : M) :
    (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)).mapMatrix (transitionMatrix R x y) *ᵥ
        (fun j ↦ transitionAlgEquiv R x y (algebraMap _ _ (universalLinearMap R y m j))) =
      fun i ↦ algebraMap _ _ (universalLinearMap R x m i) := by
  simpa [transitionAlgEquiv, transitionAlgHom_algebraMap] using mulVec_transitionLinearMap R x y m

/-- The inverse of the transition isomorphism from `y` to `x` is the transition isomorphism from
`x` to `y`. -/
@[simp]
theorem transitionAlgEquiv_symm (x y : Fin k → M) :
    (transitionAlgEquiv R x y).symm = transitionAlgEquiv R y x :=
  (rfl)

/-- The transition isomorphism from a chart to itself is the identity. -/
@[simp]
theorem transitionAlgEquiv_self (x : Fin k → M) : transitionAlgEquiv R x x = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective <| (overlapHomEquiv R x x _).injective <| Subtype.ext <| by
    simpa using overlapHomEquiv_comp_transitionAlgEquiv x x (AlgHom.id R _)

end Transition

end Module.Grassmannian
