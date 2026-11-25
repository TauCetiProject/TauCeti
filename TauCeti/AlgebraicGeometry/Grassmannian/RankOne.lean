/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.RingTheory.Grassmannian.Chart.RankOne

/-!
# The charts of the rank-one Grassmannian as standard opens of `Proj (Sym M)`

Let `M` be a module over a commutative ring `R`. The rank-one Grassmannian `G(1, M)` over `Spec R`
(`Module.Grassmannian.scheme R M 1`) is glued from the charts `Spec C_x`, `x ∈ M`, where
`C_x = ChartAlgebra R (fun _ : Fin 1 ↦ x)`, and the projective spectrum `Proj (Sym M)` of the
symmetric algebra is covered by the standard opens `D₊(x)` of the linear forms `x ∈ M`
(`TauCeti.SymmetricAlgebra.iSup_basicOpen_ι_eq_top`). This file identifies the two covers chart by
chart, over `Spec R`: the open immersion

`Module.Grassmannian.chartToProj R x : Spec C_x ⟶ Proj (Sym M)`

is `Spec` of the inverse of the ring isomorphism
`Module.Grassmannian.ChartAlgebra.awayEquiv R x : C_x ≃ₐ[R] Sym(M)_(x)` followed by
the standard chart `Proj.awayι` of `D₊(x)`. Its image is `D₊(x)`
(`Module.Grassmannian.opensRange_chartToProj`), it lies over `Spec R`
(`Module.Grassmannian.chartToProj_projToSpec`), and the images of the charts cover
`Proj (Sym M)` (`Module.Grassmannian.iSup_opensRange_chartToProj`).

The charts agree on overlaps. For `x y ∈ M`, the overlap `Spec O_xy` of the charts at `x` and `y`
(`O_xy = Module.Grassmannian.OverlapAlgebra`, the localization of `C_x` away from the rank-one
transition determinant `u_x(y)`, `Module.Grassmannian.ChartAlgebra.transitionDet_rankOne`) maps to
the standard open `D₊(xy)` of `Proj (Sym M)` through the ring map
`Module.Grassmannian.ChartAlgebra.mulAwayToOverlap R x y : Sym(M)_(xy) → O_xy`, which restricts on
`Sym(M)_(x)` (along Mathlib's `HomogeneousLocalization.awayMap`) to `awayEquiv R x` and on
`Sym(M)_(y)` to `awayEquiv R y` followed by the transition isomorphism
(`Module.Grassmannian.ChartAlgebra.mulAwayToOverlap_awayMap`,
`Module.Grassmannian.ChartAlgebra.mulAwayToOverlap_awayMap_swap`). With Mathlib's
`Proj.SpecMap_awayMap_awayι`, the chart maps at `x` and at `y` agree on the overlap, across the
transition isomorphism (`Module.Grassmannian.chartToProj_transition`). So they glue to a morphism

`Module.Grassmannian.toProj R : G(1, M) ⟶ Proj (Sym M)`

over `Spec R`, which is `chartToProj R x` on the chart at `x` (`Module.Grassmannian.chartι_toProj`,
`Module.Grassmannian.toProj_projToSpec`). This is the morphism of the rank-one identification
`G(1, M) ≅ Proj (Sym M)` of the roadmap ModularCurves, §0.7.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TauCeti.SymmetricAlgebra HomogeneousLocalization

namespace Module.Grassmannian

variable (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The chart of the rank-one Grassmannian `G(1, M)` at `x ∈ M`, as the standard open `D₊(x)` of
`Proj (Sym M)`: `Spec` of the inverse of `ChartAlgebra.awayEquiv R x` followed by the standard
chart `Proj.awayι`. -/
noncomputable def chartToProj (x : M) :
    Spec (.of (ChartAlgebra R (fun _ : Fin 1 ↦ x))) ⟶ Proj (homogeneousSubmodule R M) :=
  Spec.map (ChartAlgebra.awayEquiv R x).toRingEquiv.toCommRingCatIso.inv ≫
    Proj.awayι (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x)
      (ι_mem_homogeneousSubmodule R M x) one_pos

theorem chartToProj_def (x : M) :
    chartToProj R x = Spec.map (ChartAlgebra.awayEquiv R x).toRingEquiv.toCommRingCatIso.inv ≫
      Proj.awayι (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x)
        (ι_mem_homogeneousSubmodule R M x) one_pos :=
  (rfl)

instance (x : M) : IsOpenImmersion (chartToProj R x) := by
  rw [chartToProj_def]
  infer_instance

/-- The image of the chart of `G(1, M)` at `x` in `Proj (Sym M)` is the standard open `D₊(x)`. -/
theorem opensRange_chartToProj (x : M) :
    (chartToProj R x).opensRange =
      Proj.basicOpen (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x) := by
  simp only [chartToProj_def, Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The chart of `G(1, M)` at `x`, mapped to `Proj (Sym M)`, lies over `Spec R`: followed by the
structure morphism of `Proj (Sym M)` it is the structure morphism of the chart. -/
@[reassoc (attr := simp)]
theorem chartToProj_projToSpec (x : M) :
    chartToProj R x ≫ projToSpec R M =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartAlgebra R (fun _ : Fin 1 ↦ x)))) := by
  rw [chartToProj_def, Category.assoc, awayι_projToSpec, ← Spec.map_comp]
  congr 1
  ext r
  exact (ChartAlgebra.awayEquiv R x).symm.commutes r

/-- The images of the charts of `G(1, M)` cover `Proj (Sym M)`. -/
theorem iSup_opensRange_chartToProj :
    ⨆ x : M, (chartToProj R x).opensRange = ⊤ := by
  simp_rw [opensRange_chartToProj]
  exact iSup_basicOpen_ι_eq_top R M id (by simp)

namespace ChartAlgebra

/-- In rank one, the transition determinant from the chart at `x` to `y` is the value `u_x(y)` of
the universal linear form of the chart at `x`. -/
theorem transitionDet_rankOne (x y : M) :
    transitionDet R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y) =
      universalLinearMap R (fun _ : Fin 1 ↦ x) y 0 := by
  rw [transitionDet_def, Matrix.det_fin_one, transitionMatrix_apply]

/-- The inverse of `awayEquiv R x` sends `y / x`, the element inverted in passing from
`Sym(M)_(x)` to `Sym(M)_(xy)`, to `u_x(y)`. -/
theorem awayEquiv_symm_isLocalizationElem (x y : M) :
    (awayEquiv R x).symm (Away.isLocalizationElem (ι_mem_homogeneousSubmodule R M x)
      (ι_mem_homogeneousSubmodule R M y)) = universalLinearMap R (fun _ : Fin 1 ↦ x) y 0 := by
  rw [Away.isLocalizationElem, awayEquiv_symm_mk, pow_one, evalUniversal_ι]

-- The ring map `Sym(M)_(x) → O_xy`: `awayEquiv R x` followed by the localization map.
private noncomputable abbrev awayToOverlap (x y : M) :
    Away (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x) →+*
      OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y) :=
  (algebraMap _ _).comp (awayEquiv R x).symm.toRingHom

private theorem isUnit_awayToOverlap (x y : M) :
    IsUnit (awayToOverlap R x y (Away.isLocalizationElem (ι_mem_homogeneousSubmodule R M x)
      (ι_mem_homogeneousSubmodule R M y))) := by
  change IsUnit (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ x))
    (OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y)) ((awayEquiv R x).symm _))
  rw [awayEquiv_symm_isLocalizationElem, ← transitionDet_rankOne]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The ring map `Sym(M)_(xy) → O_xy` from the coordinate ring of the standard open `D₊(xy)` of
`Proj (Sym M)` to the coordinate ring of the overlap of the charts of `G(1, M)` at `x` and `y`:
the extension of `awayEquiv R x` from `Sym(M)_(x)` to its localization away from `y / x`
(Mathlib's `HomogeneousLocalization.Away.isLocalization_mul`), which is sent to the unit
`u_x(y)`. -/
noncomputable def mulAwayToOverlap (x y : M) :
    Away (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x * SymmetricAlgebra.ι R M y) →+*
      OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y) :=
  letI := (awayMap (homogeneousSubmodule R M) (ι_mem_homogeneousSubmodule R M y)
    (rfl : SymmetricAlgebra.ι R M x * SymmetricAlgebra.ι R M y = _)).toAlgebra
  haveI := Away.isLocalization_mul (ι_mem_homogeneousSubmodule R M x)
    (ι_mem_homogeneousSubmodule R M y) rfl one_ne_zero
  IsLocalization.Away.lift _ (isUnit_awayToOverlap R x y)

private theorem mulAwayToOverlap_comp_awayMap (x y : M) :
    (mulAwayToOverlap R x y).comp (awayMap (homogeneousSubmodule R M)
      (ι_mem_homogeneousSubmodule R M y) rfl) = awayToOverlap R x y := by
  let := (awayMap (homogeneousSubmodule R M) (ι_mem_homogeneousSubmodule R M y)
    (rfl : SymmetricAlgebra.ι R M x * SymmetricAlgebra.ι R M y = _)).toAlgebra
  have := Away.isLocalization_mul (ι_mem_homogeneousSubmodule R M x)
    (ι_mem_homogeneousSubmodule R M y) rfl one_ne_zero
  exact IsLocalization.Away.lift_comp _ (isUnit_awayToOverlap R x y)

/-- On `Sym(M)_(x)`, `mulAwayToOverlap R x y` is `awayEquiv R x` followed by the localization
map. -/
theorem mulAwayToOverlap_awayMap (x y : M) (a) :
    mulAwayToOverlap R x y (awayMap (homogeneousSubmodule R M)
      (ι_mem_homogeneousSubmodule R M y) rfl a) = algebraMap _ _ ((awayEquiv R x).symm a) :=
  DFunLike.congr_fun (mulAwayToOverlap_comp_awayMap R x y) a

/-- `mulAwayToOverlap R x y` is `R`-linear. -/
theorem mulAwayToOverlap_algebraMap (x y : M) (r : R) :
    mulAwayToOverlap R x y (algebraMap R _ r) = algebraMap R _ r := by
  rw [← awayMap_algebraMap (ι_mem_homogeneousSubmodule R M y)
      (rfl : SymmetricAlgebra.ι R M x * SymmetricAlgebra.ι R M y = _),
    mulAwayToOverlap_awayMap, AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply _ _ _ r).symm

-- `(y² / xy) · (m x / xy) = m y / xy` in `Sym(M)_(xy)`.
private theorem isLocalizationElem_mul_awayMap (x y m : M) :
    awayMap (homogeneousSubmodule R M) (ι_mem_homogeneousSubmodule R M y)
        (rfl : SymmetricAlgebra.ι R M x * SymmetricAlgebra.ι R M y = _)
        (Away.isLocalizationElem (ι_mem_homogeneousSubmodule R M x)
          (ι_mem_homogeneousSubmodule R M y)) *
      awayMap (homogeneousSubmodule R M) (ι_mem_homogeneousSubmodule R M x)
        (mul_comm (SymmetricAlgebra.ι R M x) (SymmetricAlgebra.ι R M y))
        (Away.mk _ (ι_mem_homogeneousSubmodule R M y) 1 (SymmetricAlgebra.ι R M m)
          (ι_mem_homogeneousSubmodule_one_smul R M m)) =
      awayMap (homogeneousSubmodule R M) (ι_mem_homogeneousSubmodule R M y) rfl
        (Away.mk _ (ι_mem_homogeneousSubmodule R M x) 1 (SymmetricAlgebra.ι R M m)
          (ι_mem_homogeneousSubmodule_one_smul R M m)) := by
  apply val_injective
  simp only [Away.isLocalizationElem, awayMap_mk, val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]; ring⟩

-- In rank one, the transition isomorphism multiplies the universal linear form by `u_x(y)`.
private theorem algebraMap_mul_transitionAlgEquiv (x y m : M) :
    algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ x))
        (OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y))
        (universalLinearMap R (fun _ : Fin 1 ↦ x) y 0) *
      transitionAlgEquiv R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y)
        (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ y))
          (OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x))
          (universalLinearMap R (fun _ : Fin 1 ↦ y) m 0)) =
      algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ x))
        (OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y))
        (universalLinearMap R (fun _ : Fin 1 ↦ x) m 0) := by
  have := congrFun (transitionMatrix_mulVec_transitionAlgEquiv (R := R) (fun _ : Fin 1 ↦ x)
    (fun _ : Fin 1 ↦ y) m) 0
  simpa [Matrix.mulVec, dotProduct] using this

/-- On `Sym(M)_(y)`, `mulAwayToOverlap R x y` is `awayEquiv R y` followed by the localization map
and the transition isomorphism `O_yx ≃ O_xy`. Both sides, after multiplication by the unit
`u_x(y)`, send `m / y` to `u_x(m)`. -/
theorem mulAwayToOverlap_awayMap_swap (x y : M) (a) :
    mulAwayToOverlap R x y (awayMap (homogeneousSubmodule R M) (ι_mem_homogeneousSubmodule R M x)
        (mul_comm (SymmetricAlgebra.ι R M x) (SymmetricAlgebra.ι R M y)) a) =
      transitionAlgEquiv R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y)
        (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ y))
          (OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x)) ((awayEquiv R y).symm a)) := by
  obtain ⟨c, rfl⟩ := (awayEquiv R y).surjective a
  rw [AlgEquiv.symm_apply_apply]
  let F₁ : ChartAlgebra R (fun _ : Fin 1 ↦ y) →ₐ[R]
      OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y) :=
    (AlgHom.mk (mulAwayToOverlap R x y) (mulAwayToOverlap_algebraMap R x y)).comp
      ((AlgHom.mk (awayMap (homogeneousSubmodule R M) (ι_mem_homogeneousSubmodule R M x)
        (mul_comm (SymmetricAlgebra.ι R M x) (SymmetricAlgebra.ι R M y)))
        (awayMap_algebraMap _ _)).comp (awayEquiv R y).toAlgHom)
  let F₂ : ChartAlgebra R (fun _ : Fin 1 ↦ y) →ₐ[R]
      OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y) :=
    (transitionAlgEquiv R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y)).toAlgHom.comp
      (IsScalarTower.toAlgHom R _ _)
  suffices F₁ = F₂ from DFunLike.congr_fun this c
  refine hom_ext R _ fun m j ↦ ?_
  rw [Subsingleton.elim j 0]
  have hU : IsUnit (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ x))
      (OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y))
      (universalLinearMap R (fun _ : Fin 1 ↦ x) y 0)) := by
    rw [← transitionDet_rankOne]
    exact IsLocalization.Away.algebraMap_isUnit _
  refine hU.mul_left_cancel ?_
  change _ * mulAwayToOverlap R x y (awayMap (homogeneousSubmodule R M)
      (ι_mem_homogeneousSubmodule R M x)
      (mul_comm (SymmetricAlgebra.ι R M x) (SymmetricAlgebra.ι R M y))
      (awayEquiv R y (universalLinearMap R (fun _ : Fin 1 ↦ y) m 0))) =
    _ * transitionAlgEquiv R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y)
      (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ y))
        (OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x))
        (universalLinearMap R (fun _ : Fin 1 ↦ y) m 0))
  rw [algebraMap_mul_transitionAlgEquiv, awayEquiv_universalLinearMap,
    ← awayEquiv_symm_isLocalizationElem, ← mulAwayToOverlap_awayMap, ← map_mul,
    isLocalizationElem_mul_awayMap, mulAwayToOverlap_awayMap, awayEquiv_symm_mk, evalUniversal_ι]

end ChartAlgebra

open ChartAlgebra CategoryTheory.Limits

-- The chart map at `x` on the overlap with `y` factors through `D₊(xy)`.
private theorem algebraMap_chartToProj (x y : M) :
    Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ x))
        (OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y)))) ≫ chartToProj R x =
      Spec.map (CommRingCat.ofHom (mulAwayToOverlap R x y)) ≫
        Spec.map (CommRingCat.ofHom (awayMap (homogeneousSubmodule R M)
          (ι_mem_homogeneousSubmodule R M y) rfl)) ≫
        Proj.awayι (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x)
          (ι_mem_homogeneousSubmodule R M x) one_pos := by
  rw [chartToProj_def, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  exact (mulAwayToOverlap_awayMap R x y a).symm

/-- **The rank-one charts agree on overlaps.** On the overlap of the charts of `G(1, M)` at `x`
and `y`, the chart map to `Proj (Sym M)` at `x` is the chart map at `y` composed with the
transition isomorphism. Both factor through the standard open `D₊(xy)` along
`mulAwayToOverlap R x y`. -/
theorem chartToProj_transition (x y : M) :
    Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ x))
        (OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y)))) ≫ chartToProj R x =
      Spec.map (CommRingCat.ofHom (transitionAlgEquiv R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y) :
          OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x) →+*
            OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ y))
          (OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x)))) ≫ chartToProj R y := by
  have h : Spec.map (CommRingCat.ofHom (transitionAlgEquiv R (fun _ : Fin 1 ↦ x)
        (fun _ : Fin 1 ↦ y) : OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x) →+*
          OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ y))
          (OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x)))) ≫ chartToProj R y =
      Spec.map (CommRingCat.ofHom (mulAwayToOverlap R x y)) ≫
        Spec.map (CommRingCat.ofHom (awayMap (homogeneousSubmodule R M)
          (ι_mem_homogeneousSubmodule R M x)
          (mul_comm (SymmetricAlgebra.ι R M x) (SymmetricAlgebra.ι R M y)))) ≫
        Proj.awayι (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M y)
          (ι_mem_homogeneousSubmodule R M y) one_pos := by
    rw [chartToProj_def]
    simp only [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact (mulAwayToOverlap_awayMap_swap R x y a).symm
  rw [h, algebraMap_chartToProj, Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-- The chart map `chartToProj R (x 0)` of `G(1, M)` read on the chart indexed by
`x : Fin 1 → M`, which is `fun _ ↦ x 0`. The gluing data of the Grassmannian are indexed by such
functions. -/
noncomputable def chartToProjOfFun (x : Fin 1 → M) :
    Spec (.of (ChartAlgebra R x)) ⟶ Proj (homogeneousSubmodule R M) :=
  (funext fun i ↦ congrArg x (Subsingleton.elim 0 i) : (fun _ : Fin 1 ↦ x 0) = x) ▸
    chartToProj R (x 0)

/-- On a constant index, `chartToProjOfFun` is `chartToProj`. -/
theorem chartToProjOfFun_const (m : M) :
    chartToProjOfFun R (fun _ : Fin 1 ↦ m) = chartToProj R m :=
  (rfl)

omit [AddCommGroup M] [Module R M] in
private theorem exists_eq_const (x : Fin 1 → M) : ∃ m : M, x = fun _ ↦ m :=
  ⟨x 0, funext fun i ↦ congrArg x (Subsingleton.elim i 0)⟩

/-- **The rank-one Grassmannian maps to `Proj (Sym M)`**, by the chart maps `chartToProj`, which
agree on overlaps (`Module.Grassmannian.chartToProj_transition`). -/
noncomputable def toProj : scheme R M 1 ⟶ Proj (homogeneousSubmodule R M) :=
  (chartOpenCover R M 1).glueMorphisms (fun x ↦ chartToProjOfFun R x) fun x y ↦ by
    -- The pullback of the charts at `x` and `y` is their overlap (`isPullback_chartι`).
    have h := isPullback_chartι (R := R) x y
    rw [← cancel_epi h.isoPullback.hom, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      ← Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc]
    obtain ⟨a, rfl⟩ := exists_eq_const x
    obtain ⟨b, rfl⟩ := exists_eq_const y
    exact chartToProj_transition R a b

/-- On the chart at `m`, `toProj R` is `chartToProj R m`. -/
@[reassoc (attr := simp)]
theorem chartι_toProj (m : M) :
    chartι R (fun _ : Fin 1 ↦ m) ≫ toProj R = chartToProj R m :=
  (chartOpenCover R M 1).ι_glueMorphisms _ _ (fun _ : Fin 1 ↦ m)

/-- `toProj R` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem toProj_projToSpec : toProj R ≫ projToSpec R M = toSpec R M 1 := by
  refine (chartOpenCover R M 1).hom_ext _ _ fun x ↦ ?_
  obtain ⟨a, rfl⟩ := exists_eq_const x
  exact (chartι_toProj_assoc R a _).trans ((chartToProj_projToSpec R a).trans
    (chartι_toSpec _).symm)

end Module.Grassmannian
