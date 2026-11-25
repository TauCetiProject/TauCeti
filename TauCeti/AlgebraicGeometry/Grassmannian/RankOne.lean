/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
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

The charts agree on overlaps. A morphism `Spec S ⟶ Spec C_x` given by a ring map `ψ : C_x → S`,
followed by the chart map at `x`, is the point of `Proj (Sym M)` with homogeneous coordinates
`ψ` composed with the evaluation at the universal linear form, read on `D₊(x)`
(`Module.Grassmannian.SpecMap_chartToProj`). On the overlap of the charts at `x` and `y`, the
homogeneous coordinates coming from the chart at `y` through the transition isomorphism are those
coming from the chart at `x`, rescaled by the unit `u_x(y)`
(`Module.Grassmannian.ChartAlgebra.algebraMap_evalUniversal_eq_pow_mul_transitionAlgEquiv`). So
the chart maps agree on the overlap, across the transition isomorphism
(`Module.Grassmannian.chartToProj_transition`), and glue to a morphism

`Module.Grassmannian.toProj R : G(1, M) ⟶ Proj (Sym M)`

over `Spec R`, which is `chartToProj R x` on the chart at `x` (`Module.Grassmannian.chartι_toProj`,
`Module.Grassmannian.toProj_projToSpec`). This is the morphism of the rank-one identification
`G(1, M) ≅ Proj (Sym M)`.
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

open ChartAlgebra CategoryTheory.Limits

/-- A morphism to the chart of `G(1, M)` at `x` given by a ring map `ψ : C_x → S`, followed by
`chartToProj R x`, is the point of `Proj (Sym M)` on the standard open `D₊(x)` with homogeneous
coordinates `ψ` composed with the evaluation at the universal linear form. -/
theorem SpecMap_chartToProj (x : M) {S : Type u} [CommRing S]
    (ψ : ChartAlgebra R (fun _ : Fin 1 ↦ x) →+* S) :
    Spec.map (CommRingCat.ofHom ψ) ≫ chartToProj R x =
      Spec.map (CommRingCat.ofHom (Away.lift (homogeneousSubmodule R M)
        (ψ.comp (evalUniversal R x).toRingHom) (by simp))) ≫
        Proj.awayι (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x)
          (ι_mem_homogeneousSubmodule R M x) one_pos := by
  rw [chartToProj_def, ← Category.assoc, ← Spec.map_comp,
    ← RingHom.comp_homogeneousLocalizationAwayLift ψ _ (by simp), ← awayEquiv_symm_toRingHom]
  -- the inverse of the isomorphism `awayEquiv R x` in `CommRingCat` is `ofHom` of its inverse
  rfl

/-- **The rank-one charts agree on overlaps.** On the overlap of the charts of `G(1, M)` at `x`
and `y`, the chart map to `Proj (Sym M)` at `x` is the chart map at `y` composed with the
transition isomorphism. -/
theorem chartToProj_transition (x y : M) :
    Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ x))
        (OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y)))) ≫ chartToProj R x =
      Spec.map (CommRingCat.ofHom (transitionAlgEquiv R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y) :
          OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x) →+*
            OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ y))
          (OverlapAlgebra R (fun _ : Fin 1 ↦ y) (fun _ : Fin 1 ↦ x)))) ≫ chartToProj R y := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, SpecMap_chartToProj,
    SpecMap_chartToProj]
  -- Both are points of `Proj (Sym M)` whose homogeneous coordinates differ by the unit `u_x(y)`.
  have hy : IsUnit (((algebraMap (ChartAlgebra R (fun _ : Fin 1 ↦ x))
      (OverlapAlgebra R (fun _ : Fin 1 ↦ x) (fun _ : Fin 1 ↦ y))).comp
        (evalUniversal R x).toRingHom) (SymmetricAlgebra.ι R M y)) := by
    simpa using isUnit_algebraMap_universalLinearMap R x y
  rw [Proj.SpecMap_awayLift_awayι_eq _ _ one_pos (ι_mem_homogeneousSubmodule R M y) one_pos _ hy]
  congr 3
  exact Away.lift_eq_of_forall_mem (𝒜 := homogeneousSubmodule R M) _ _
    (isUnit_algebraMap_universalLinearMap R x y).unit
    (fun n a ha ↦ algebraMap_evalUniversal_eq_pow_mul_transitionAlgEquiv R x y ha)
    (ι_mem_homogeneousSubmodule R M y) _ _

/-- The chart map `chartToProj R (x 0)` of `G(1, M)` read on the chart indexed by
`x : Fin 1 → M`, which is `fun _ ↦ x 0`. The gluing data of the Grassmannian are indexed by such
functions. -/
noncomputable def chartToProjOfFun (x : Fin 1 → M) :
    Spec (.of (ChartAlgebra R x)) ⟶ Proj (homogeneousSubmodule R M) :=
  ((eq_const_of_unique x).symm : (fun _ : Fin 1 ↦ x 0) = x) ▸ chartToProj R (x 0)

/-- On a constant index, `chartToProjOfFun` is `chartToProj`. -/
@[simp]
theorem chartToProjOfFun_const (m : M) :
    chartToProjOfFun R (fun _ : Fin 1 ↦ m) = chartToProj R m :=
  (rfl)

/-- **The rank-one Grassmannian maps to `Proj (Sym M)`**, by the chart maps `chartToProj`, which
agree on overlaps (`Module.Grassmannian.chartToProj_transition`). -/
noncomputable def toProj : scheme R M 1 ⟶ Proj (homogeneousSubmodule R M) :=
  (chartOpenCover R M 1).glueMorphisms (fun x ↦ chartToProjOfFun R x) fun x y ↦ by
    -- The pullback of the charts at `x` and `y` is their overlap (`isPullback_chartι`).
    have h := isPullback_chartι (R := R) x y
    rw [← cancel_epi h.isoPullback.hom, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      ← Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc]
    obtain ⟨a, rfl⟩ : ∃ a, x = fun _ ↦ a := ⟨_, eq_const_of_unique x⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = fun _ ↦ b := ⟨_, eq_const_of_unique y⟩
    exact chartToProj_transition R a b

/-- On the chart indexed by `x : Fin 1 → M`, `toProj R` is `chartToProjOfFun R x`. -/
@[reassoc (attr := simp)]
theorem chartι_toProjOfFun (x : Fin 1 → M) :
    chartι R x ≫ toProj R = chartToProjOfFun R x :=
  (chartOpenCover R M 1).ι_glueMorphisms _ _ x

/-- On the chart at `m`, `toProj R` is `chartToProj R m`. -/
@[reassoc]
theorem chartι_toProj (m : M) :
    chartι R (fun _ : Fin 1 ↦ m) ≫ toProj R = chartToProj R m :=
  chartι_toProjOfFun R _

/-- `toProj R` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem toProj_projToSpec : toProj R ≫ projToSpec R M = toSpec R M 1 := by
  refine (chartOpenCover R M 1).hom_ext _ _ fun x ↦ ?_
  obtain ⟨a, rfl⟩ : ∃ a, x = fun _ ↦ a := ⟨_, eq_const_of_unique x⟩
  exact (chartι_toProj_assoc R a _).trans ((chartToProj_projToSpec R a).trans
    (chartι_toSpec _).symm)

end Module.Grassmannian
