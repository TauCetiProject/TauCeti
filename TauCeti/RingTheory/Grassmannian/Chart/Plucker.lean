/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.Chart.Basic
public import TauCeti.RingTheory.Grassmannian.Plucker

import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The Plücker map on the standard charts

Let `M` be a module over a commutative ring `R`, `k` a natural number and `x : Fin k → M`. This file
describes the Plücker map `G(k, M) → G(1, ⋀ᵏ M)` (`Module.Grassmannian.pluckerBaseChange`) on the
standard charts: it sends the chart at `x` into the chart at the wedge `x₁ ∧ ⋯ ∧ xₖ`, through an
explicit map of coordinate rings.

Write `C_x` for `Module.Grassmannian.ChartAlgebra R x` and `u_x : M → C_x^k` for its universal point
(`Module.Grassmannian.ChartAlgebra.universalLinearMap`). The **Plücker form**
`Module.Grassmannian.ChartAlgebra.pluckerForm R x : ⋀ᵏ M → C_x` sends `m₁ ∧ ⋯ ∧ mₖ` to the
determinant of the matrix with rows `u_x(m₁), …, u_x(mₖ)`
(`Module.Grassmannian.ChartAlgebra.pluckerForm_ιMulti`); it takes the value `1` at
`x₁ ∧ ⋯ ∧ xₖ`, so it classifies an `R`-algebra map
`Module.Grassmannian.ChartAlgebra.pluckerChartHom R x : C_{x₁ ∧ ⋯ ∧ xₖ} → C_x`.

## Main definitions

* `Module.Grassmannian.ChartAlgebra.pluckerForm R x`: the Plücker form `⋀ᵏ M → C_x`.
* `Module.Grassmannian.ChartAlgebra.pluckerChartHom R x`: the Plücker map on charts
  `C_{x₁ ∧ ⋯ ∧ xₖ} → C_x`.

## Main results

* `Module.Grassmannian.ChartAlgebra.pluckerForm_update`: the coordinate `u_x(m)ᵢ` is the Plücker
  form of `x` with `xᵢ` replaced by `m`.
* `Module.Grassmannian.ChartAlgebra.pluckerChartHom_surjective`: the Plücker map on charts is
  surjective.
* `Module.Grassmannian.pluckerBaseChange_chartHomEquiv_id`: the Plücker point of the universal
  point of the chart at `x` is the point classified by `pluckerChartHom R x`.
* `Module.Grassmannian.pluckerBaseChange_mem_chart_iff`: over a field, the Plücker point of `N`
  lies in the chart at `x₁ ∧ ⋯ ∧ xₖ` exactly when `N` lies in the chart at `x`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7, for
  the Grassmannian and its Plücker embedding.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
* U. Görtz, T. Wedhorn, *Algebraic Geometry I* (Vieweg+Teubner, 2010), Chapter 8, for the
  standard charts of the Grassmannian and the Plücker embedding.
-/

public section

universe u v

open TensorProduct

namespace Module.Grassmannian

variable (R : Type u) [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

namespace ChartAlgebra

/-- **The Plücker form** of the chart at `x`: the linear map `⋀ᵏ M → C_x` sending
`m₁ ∧ ⋯ ∧ mₖ` to the determinant of the matrix with rows `u_x(m₁), …, u_x(mₖ)`, where `u_x` is the
universal point of the chart. -/
noncomputable def pluckerForm (x : Fin k → M) : ⋀[R]^k M →ₗ[R] ChartAlgebra R x :=
  exteriorPower.alternatingMapLinearEquiv
    { toMultilinearMap :=
        ((Matrix.detRowAlternating (R := ChartAlgebra R x) (n := Fin k)).toMultilinearMap
          |>.restrictScalars R).compLinearMap fun _ ↦ universalLinearMap R x
      map_eq_zero_of_eq' := fun v i j hv hij ↦
        Matrix.detRowAlternating.map_eq_zero_of_eq (fun l ↦ universalLinearMap R x (v l))
          (by simp [hv]) hij }

/-- The Plücker form of `m₁ ∧ ⋯ ∧ mₖ` is the determinant of the matrix with rows `u_x(mⱼ)`. -/
theorem pluckerForm_ιMulti (x m : Fin k → M) :
    pluckerForm R x (exteriorPower.ιMulti R k m) =
      (Matrix.of fun j i ↦ universalLinearMap R x (m j) i).det := by
  rw [pluckerForm, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact Matrix.detRowAlternating_apply fun j ↦ universalLinearMap R x (m j)

/-- The Plücker form of the chart at `x` takes the value `1` at `x₁ ∧ ⋯ ∧ xₖ`. -/
@[simp]
theorem pluckerForm_self (x : Fin k → M) :
    pluckerForm R x (exteriorPower.ιMulti R k x) = 1 := by
  rw [pluckerForm_ιMulti, ← Matrix.det_one (R := ChartAlgebra R x) (n := Fin k)]
  congr 1
  ext j i
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

/-- **The Plücker map on charts**: the `R`-algebra map from the coordinate ring of the chart of
`G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ` to the coordinate ring of the chart of `G(k, M)` at `x` classified by
the Plücker form. -/
noncomputable def pluckerChartHom (x : Fin k → M) :
    ChartAlgebra R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) →ₐ[R] ChartAlgebra R x :=
  (homEquiv R _).symm ⟨LinearMap.pi fun _ ↦ pluckerForm R x, fun i ↦ by
    ext j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp⟩

/-- `pluckerChartHom R x` sends the universal linear form of the rank-one chart to the Plücker
form. -/
@[simp]
theorem pluckerChartHom_universalLinearMap (x : Fin k → M) (w : ⋀[R]^k M) (j : Fin 1) :
    pluckerChartHom R x (universalLinearMap R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) w j) =
      pluckerForm R x w := by
  simp [pluckerChartHom]

/-- **Coordinates are Plücker coordinates.** The coordinate `u_x(m)ᵢ` of the chart at `x` is the
Plücker form of `x` with `xᵢ` replaced by `m`. -/
@[simp]
theorem pluckerForm_update (x : Fin k → M) (i : Fin k) (m : M) :
    pluckerForm R x (exteriorPower.ιMulti R k (Function.update x i m)) =
      universalLinearMap R x m i := by
  have hrow : (Matrix.of fun j l ↦ universalLinearMap R x (Function.update x i m j) l) =
      (1 : Matrix (Fin k) (Fin k) (ChartAlgebra R x)).updateRow i (universalLinearMap R x m) := by
    ext j l
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [Function.update_of_ne hj, Matrix.updateRow_ne hj, Matrix.one_apply, Pi.single_apply,
        eq_comm]
  have hsum : ∑ l, universalLinearMap R x m l • (1 : Matrix (Fin k) (Fin k) (ChartAlgebra R x)) l =
      universalLinearMap R x m := by
    ext l
    simp [Finset.sum_apply, Matrix.one_apply]
  have := Matrix.det_updateRow_sum (1 : Matrix (Fin k) (Fin k) (ChartAlgebra R x)) i
    (universalLinearMap R x m)
  rw [hsum, Matrix.det_one, smul_eq_mul, mul_one] at this
  rw [pluckerForm_ιMulti, hrow, this]

/-- **The Plücker map on charts is surjective**: every coordinate `u_x(m)ᵢ` is a Plücker
coordinate (`Module.Grassmannian.ChartAlgebra.pluckerForm_update`). -/
theorem pluckerChartHom_surjective (x : Fin k → M) :
    Function.Surjective (pluckerChartHom R x) :=
  surjective_of_forall_mem_range R x fun m i ↦
    ⟨universalLinearMap R _ (exteriorPower.ιMulti R k (Function.update x i m)) 0,
      (pluckerChartHom_universalLinearMap R x _ 0).trans (pluckerForm_update R x i m)⟩

end ChartAlgebra

open ChartAlgebra

/-- The base change to `C_x` of the Plücker form, read on `⋀ᵏ (C_x ⊗ M)`, is the determinant of the
universal surjection `C_x ⊗ M → C_x^k`. -/
private theorem liftBaseChange_pluckerChartHom_comp_equivBaseChange (x : Fin k → M) :
    ((pluckerChartHom R x).toLinearMap.compLeft (Fin 1) ∘ₗ
        universalLinearMap R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x)).liftBaseChange
          (ChartAlgebra R x) ∘ₗ
      (TauCeti.exteriorPower.equivBaseChange (ChartAlgebra R x) k).toLinearMap =
    (LinearMap.pi fun _ ↦ exteriorPower.alternatingMapLinearEquiv Matrix.detRowAlternating) ∘ₗ
      exteriorPower.map k
        (((AlgHom.id R _).toLinearMap.compLeft (Fin k) ∘ₗ universalLinearMap R x).liftBaseChange
          (ChartAlgebra R x)) := by
  have hspan : Submodule.span (ChartAlgebra R x)
      (Set.range (TensorProduct.mk R (ChartAlgebra R x) M 1)) = ⊤ := by
    rw [← LinearMap.coe_range, LinearMap.range_eq_map, ← Submodule.baseChange_eq_span,
      Submodule.baseChange_top]
  refine LinearMap.ext_on (exteriorPower.ιMulti_span_of_span _ k _ hspan) ?_
  rintro _ ⟨v, hv, rfl⟩
  choose m hm using fun i ↦ hv ⟨i, rfl⟩
  obtain rfl : v = fun i ↦ (1 : ChartAlgebra R x) ⊗ₜ[R] m i := funext fun i ↦ (hm i).symm
  have hA := TauCeti.exteriorPower.equivBaseChange_ιMulti_tmul (R := R) (ChartAlgebra R x)
    (fun _ ↦ 1) m
  simp only [Finset.prod_const_one] at hA
  ext j
  have hid (y : Fin k → ChartAlgebra R x) : (LinearMap.id (R := R)).compLeft (Fin k) y = y := by
    ext; simp
  simp [hA, hid, pluckerForm_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Matrix.detRowAlternating_apply, Function.comp_def]

/-- **The Plücker map on the universal point of a chart.** The Plücker point of the universal point
of the chart of `G(k, M)` at `x` is the point of the chart of `G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ`
classified by `pluckerChartHom R x`. -/
theorem pluckerBaseChange_chartHomEquiv_id (x : Fin k → M) :
    pluckerBaseChange (chartHomEquiv R x (ChartAlgebra R x) (AlgHom.id R _)).val =
      (chartHomEquiv R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) (ChartAlgebra R x)
        (pluckerChartHom R x)).val := by
  -- The map `⋀ᵏ (C_x ⊗ M) → ⋀ᵏ (C_x^k) → C_x`, by the determinant, is the Plücker form, so it
  -- kills the kernel of `⋀ᵏ (C_x ⊗ M) → ⋀ᵏ (C_x^k)`; comparable points of a Grassmannian are equal.
  set A := ChartAlgebra R x
  let φ : A ⊗[R] M →ₗ[A] Fin k → A :=
    ((AlgHom.id R A).toLinearMap.compLeft (Fin k) ∘ₗ universalLinearMap R x).liftBaseChange A
  have hφ : Function.Surjective φ :=
    (TauCeti.leftInverse_fintypeLinearCombination (x := fun i ↦ (1 : A) ⊗ₜ[R] x i)
      (φ := φ) fun i ↦ by ext; simp [φ, universalLinearMap_apply_self]).surjective
  -- the universal point of the chart at `x` is the kernel of `φ`
  have hN : (chartHomEquiv R x A (AlgHom.id R A)).val = ofSurjective φ hφ (rankAtStalk_fin_fun k) :=
    Grassmannian.ext (by rw [toSubmodule_chartHomEquiv_apply, toSubmodule_ofSurjective])
  let Ψ : A ⊗[R] ⋀[R]^k M →ₗ[A] Fin 1 → A :=
    ((pluckerChartHom R x).toLinearMap.compLeft (Fin 1) ∘ₗ
      universalLinearMap R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x)).liftBaseChange A
  let D : ⋀[A]^k (Fin k → A) →ₗ[A] Fin 1 → A :=
    LinearMap.pi fun _ ↦ exteriorPower.alternatingMapLinearEquiv Matrix.detRowAlternating
  have key : Ψ ∘ₗ (TauCeti.exteriorPower.equivBaseChange A k).toLinearMap =
      D ∘ₗ exteriorPower.map k φ :=
    liftBaseChange_pluckerChartHom_comp_equivBaseChange R x
  refine eq_of_le ?_
  rw [toSubmodule_pluckerBaseChange, ← toSubmodule_plucker, hN,
    toSubmodule_plucker_ofSurjective φ hφ (rankAtStalk_fin_fun k)]
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hy
  rw [toSubmodule_chartHomEquiv_apply, LinearMap.mem_ker]
  exact (LinearMap.congr_fun key y).trans (by rw [LinearMap.comp_apply, hy, map_zero])

end Module.Grassmannian

/-! ### Charts of the Plücker point over a field -/

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
  {K : Type*} [Field K] [Algebra R K]

/-- **The Plücker point and the charts, over a field.** For a point `N` of `G(k, K ⊗[R] M; K)` over
a field `K` and `x : Fin k → M`, the Plücker point of `N` lies in the chart of `G(1, ⋀ᵏ M)` at the
wedge `x₁ ∧ ⋯ ∧ xₖ` exactly when `N` lies in the chart at `x`: the images of the `xᵢ` span the
quotient exactly when their wedge spans its top exterior power. -/
theorem pluckerBaseChange_mem_chart_iff (N : G(k, K ⊗[R] M; K)) (x : Fin k → M) :
    pluckerBaseChange N ∈
        chart K (fun _ : Fin 1 ↦ (1 : K) ⊗ₜ[R] _root_.exteriorPower.ιMulti R k x) ↔
      N ∈ chart K (fun i ↦ (1 : K) ⊗ₜ[R] x i) := by
  set q := N.toSubmodule.mkQ
  set F := _root_.exteriorPower.map k q
  set e := TauCeti.exteriorPower.equivBaseChange (R := R) (M := M) K k
  set y : Fin k → K ⊗[R] M := fun i ↦ (1 : K) ⊗ₜ[R] x i
  set w := _root_.exteriorPower.ιMulti K k y
  have hF : LinearMap.range F = ⊤ :=
    LinearMap.range_eq_top.2 (_root_.exteriorPower.map_surjective N.toSubmodule.mkQ_surjective)
  have he : e.symm ((1 : K) ⊗ₜ[R] _root_.exteriorPower.ιMulti R k x) = w := by
    rw [TauCeti.exteriorPower.equivBaseChange_symm_tmul_ιMulti, one_smul]
  -- transport the chart condition on the Plücker point along `e`
  have hsup : (pluckerBaseChange N).toSubmodule ⊔
      Submodule.span K (Set.range fun _ : Fin 1 ↦ (1 : K) ⊗ₜ[R]
        _root_.exteriorPower.ιMulti R k x) =
      (LinearMap.ker F ⊔ Submodule.span K {w}).map e.toLinearMap := by
    rw [toSubmodule_pluckerBaseChange, Submodule.map_sup, Submodule.map_span, Set.image_singleton,
      ← he, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Set.range_const]
  -- pass to the quotient by `ker F`, which is `⋀ᵏ` of the universal quotient
  have hker : LinearMap.ker F ⊔ Submodule.span K {w} = ⊤ ↔ Submodule.span K {F w} = ⊤ := by
    rw [sup_comm, ← LinearMap.map_eq_top_iff hF, Submodule.map_span, Set.image_singleton]
  -- pass to the universal quotient on the side of `N`
  have hN : N.toSubmodule ⊔ Submodule.span K (Set.range y) = ⊤ ↔
      Submodule.span K (Set.range (q ∘ y)) = ⊤ := by
    rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  rw [mem_chart_iff_sup_eq_top, mem_chart_iff_sup_eq_top, hsup, Submodule.map_eq_top_iff, hker,
    hN, _root_.exteriorPower.map_apply_ιMulti]
  exact TauCeti.exteriorPower.span_singleton_ιMulti_eq_top_iff (finrank_quotient N) _

end Module.Grassmannian
