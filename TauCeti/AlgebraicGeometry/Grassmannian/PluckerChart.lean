/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Plucker
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The Plücker morphism on the standard charts

Let `M` be a module over a commutative ring `R`, `k` a natural number and `x : Fin k → M`. The
Plücker morphism `Module.Grassmannian.pluckerHom R M k : G(k, M) ⟶ G(1, ⋀ᵏ M)` is defined on
points. This file describes it on the standard charts: it sends the chart of `G(k, M)` at `x` into
the chart of `G(1, ⋀ᵏ M)` at the wedge `x₁ ∧ ⋯ ∧ xₖ`, by `Spec` of an explicit ring map.

Write `u_x : M → C_x^k` for the universal point of the chart at `x`
(`Module.Grassmannian.ChartAlgebra.universalLinearMap`). The **Plücker form**
`Module.Grassmannian.ChartAlgebra.pluckerForm R x : ⋀ᵏ M → C_x` sends `m₁ ∧ ⋯ ∧ mₖ` to the
determinant of the matrix with rows `u_x(m₁), …, u_x(mₖ)`
(`Module.Grassmannian.ChartAlgebra.pluckerForm_ιMulti`); it takes the value `1` at
`x₁ ∧ ⋯ ∧ xₖ`, so it classifies an `R`-algebra map

`Module.Grassmannian.ChartAlgebra.pluckerChartHom R x : C_{x₁ ∧ ⋯ ∧ xₖ} → C_x`

from the coordinate ring of the rank-one chart. Then:

* `Spec` of `pluckerChartHom R x`, followed by the chart of `G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ`, is the
  chart of `G(k, M)` at `x` followed by `pluckerHom`
  (`Module.Grassmannian.specMap_pluckerChartHom_chartι`). On points this is
  `Module.Grassmannian.pluckerBaseChange_chartHomEquiv_id`: the Plücker point of the universal
  point of the chart at `x` is the point classified by `pluckerChartHom R x`, because the
  determinant `⋀ᵏ (C_x ⊗ M) → ⋀ᵏ (C_x^k) → C_x` agrees with the Plücker form.
* `pluckerChartHom R x` is surjective
  (`Module.Grassmannian.ChartAlgebra.pluckerChartHom_surjective`): the coordinate `u_x(m)ᵢ` is
  the Plücker form of `x` with `xᵢ` replaced by `m`
  (`Module.Grassmannian.ChartAlgebra.pluckerForm_update`). So `Spec` of it is a closed immersion
  (`Module.Grassmannian.isClosedImmersion_specMap_pluckerChartHom`).

These are the chart-level inputs for the Plücker closed immersion of the roadmap ModularCurves,
§0.7.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

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
  rfl

/-- The Plücker form of the chart at `x` takes the value `1` at `x₁ ∧ ⋯ ∧ xₖ`. -/
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
    simp [pluckerForm_self]⟩

/-- `pluckerChartHom R x` sends the universal linear form of the rank-one chart to the Plücker
form. -/
@[simp]
theorem pluckerChartHom_universalLinearMap (x : Fin k → M) (w : ⋀[R]^k M) (j : Fin 1) :
    pluckerChartHom R x (universalLinearMap R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) w j) =
      pluckerForm R x w := by
  simp [pluckerChartHom]

/-- **Coordinates are Plücker coordinates.** The coordinate `u_x(m)ᵢ` of the chart at `x` is the
Plücker form of `x` with `xᵢ` replaced by `m`. -/
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
    Function.Surjective (pluckerChartHom R x) := by
  have hgen (m : M) (i : Fin k) : universalLinearMap R x m i ∈ (pluckerChartHom R x).range :=
    ⟨universalLinearMap R _ (exteriorPower.ιMulti R k (Function.update x i m)) 0,
      (pluckerChartHom_universalLinearMap R x _ 0).trans (pluckerForm_update R x i m)⟩
  -- The universal point factors through the range `S`, and the induced map `C_x → S` is a
  -- section of the inclusion of `S`, by `hom_ext`.
  set S := (pluckerChartHom R x).range
  let ψ : {ψ : M →ₗ[R] Fin k → S // ∀ i, ψ (x i) = Pi.single i 1} :=
    ⟨{ toFun m i := ⟨universalLinearMap R x m i, hgen m i⟩
       map_add' m m' := funext fun i ↦ Subtype.ext (by simp)
       map_smul' r m := funext fun i ↦ Subtype.ext (by simp) },
      fun i ↦ funext fun j ↦ Subtype.ext (by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, universalLinearMap_apply_self, Pi.single_apply]
        split_ifs <;> rfl)⟩
  have hsec : S.val.comp ((homEquiv R x).symm ψ) = AlgHom.id R _ :=
    hom_ext R x fun m j ↦ by simp [ψ]
  intro c
  have hc : S.val ((homEquiv R x).symm ψ c) = c := DFunLike.congr_fun hsec c
  have : c ∈ S := hc ▸ ((homEquiv R x).symm ψ c).property
  exact this

end ChartAlgebra

open ChartAlgebra

/-- **The Plücker map on the universal point of a chart.** The Plücker point of the universal point
of the chart of `G(k, M)` at `x` is the point of the chart of `G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ`
classified by `pluckerChartHom R x`: the map `⋀ᵏ (C_x ⊗ M) → ⋀ᵏ (C_x^k) → C_x`, by the
determinant, is the Plücker form, so it kills the kernel of `⋀ᵏ (C_x ⊗ M) → ⋀ᵏ Q`, and comparable
points of a Grassmannian are equal. -/
theorem pluckerBaseChange_chartHomEquiv_id (x : Fin k → M) :
    pluckerBaseChange (chartHomEquiv R x (ChartAlgebra R x) (AlgHom.id R _)).val =
      (chartHomEquiv R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) (ChartAlgebra R x)
        (pluckerChartHom R x)).val := by
  set A := ChartAlgebra R x
  set N := (chartHomEquiv R x A (AlgHom.id R A)).val
  let φ : A ⊗[R] M →ₗ[A] Fin k → A :=
    ((AlgHom.id R A).toLinearMap.compLeft (Fin k) ∘ₗ universalLinearMap R x).liftBaseChange A
  have hN : N.toSubmodule = LinearMap.ker φ := toSubmodule_chartHomEquiv_apply x _
  let Ψ : A ⊗[R] ⋀[R]^k M →ₗ[A] Fin 1 → A :=
    ((pluckerChartHom R x).toLinearMap.compLeft (Fin 1) ∘ₗ
      universalLinearMap R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x)).liftBaseChange A
  let D : ⋀[A]^k (Fin k → A) →ₗ[A] Fin 1 → A :=
    LinearMap.pi fun _ ↦ exteriorPower.alternatingMapLinearEquiv Matrix.detRowAlternating
  have hspan : Submodule.span A (Set.range (TensorProduct.mk R A M 1)) = ⊤ := by
    rw [← LinearMap.coe_range, LinearMap.range_eq_map, ← Submodule.baseChange_eq_span,
      Submodule.baseChange_top]
  have key : Ψ ∘ₗ (TauCeti.exteriorPower.equivBaseChange A k).toLinearMap =
      D ∘ₗ exteriorPower.map k φ := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span_of_span A k (A ⊗[R] M) hspan) ?_
    rintro _ ⟨v, hv, rfl⟩
    choose m hm using fun i ↦ hv ⟨i, rfl⟩
    obtain rfl : v = fun i ↦ (1 : A) ⊗ₜ[R] m i := funext fun i ↦ (hm i).symm
    have hA := TauCeti.exteriorPower.equivBaseChange_ιMulti_tmul (R := R) A (fun _ ↦ (1 : A)) m
    simp only [Finset.prod_const_one] at hA
    ext j
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hA,
      LinearMap.liftBaseChange_tmul, one_smul, LinearMap.compLeft_apply, AlgHom.toLinearMap_apply,
      pluckerChartHom_universalLinearMap, pluckerForm_ιMulti, exteriorPower.map_apply_ιMulti,
      LinearMap.pi_apply, D, Ψ, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change _ = Matrix.det (Matrix.of _)
    congr 1
    ext j i
    simp
  refine eq_of_le ?_
  rw [toSubmodule_pluckerBaseChange]
  rintro _ ⟨y, hy, rfl⟩
  rw [toSubmodule_chartHomEquiv_apply, LinearMap.mem_ker]
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hy
  have hφ : φ = (N.toSubmodule.liftQ φ hN.le) ∘ₗ N.toSubmodule.mkQ :=
    (Submodule.liftQ_mkQ _ _ _).symm
  have h0 : exteriorPower.map k φ y = 0 := by
    rw [hφ, exteriorPower.map_comp, LinearMap.comp_apply, hy, map_zero]
  change (Ψ ∘ₗ (TauCeti.exteriorPower.equivBaseChange A k).toLinearMap) y = 0
  rw [key, LinearMap.comp_apply, h0, map_zero]

/-- **The Plücker morphism on charts.** On the chart of `G(k, M)` at `x`, the Plücker morphism is
`Spec` of `pluckerChartHom R x` followed by the chart of `G(1, ⋀ᵏ M)` at `x₁ ∧ ⋯ ∧ xₖ`. -/
theorem specMap_pluckerChartHom_chartι (x : Fin k → M) :
    Spec.map (CommRingCat.ofHom (pluckerChartHom R x :
        ChartAlgebra R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) →+* ChartAlgebra R x)) ≫
      chartι R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) =
    chartι R x ≫ pluckerHom R M k := by
  rw [← toSchemeHom_chartHomEquiv_id x, toSchemeHom_comp_pluckerHom,
    pluckerBaseChange_chartHomEquiv_id, ← toSchemeHom_chartHomEquiv_id, ← toSchemeHom_map,
    ← chartHomEquiv_comp, AlgHom.comp_id]

/-- `Spec` of the Plücker map on charts is a closed immersion. -/
theorem isClosedImmersion_specMap_pluckerChartHom (x : Fin k → M) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (pluckerChartHom R x :
      ChartAlgebra R (fun _ : Fin 1 ↦ exteriorPower.ιMulti R k x) →+* ChartAlgebra R x))) :=
  IsClosedImmersion.spec_of_surjective _ (pluckerChartHom_surjective R x)

end Module.Grassmannian
