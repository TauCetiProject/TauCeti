/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.CategoryTheory.Abelian.Ext
import TauCeti.Algebra.Module.Torsion.QuotientLinearMap

/-!
# Local cohomology in degree zero

Mathlib defines the local cohomology module `H^i_J(M) = (localCohomology J i).obj M` of a module
`M` over a commutative ring `R` as the colimit over `n` of `Extⁱ(R ⧸ Jⁿ, M)`, where `Ext` is the
left derived functor `Ext R (ModuleCat R) i` of `Hom(-, M)`. This file computes the degree-zero
group for an arbitrary commutative ring: `H⁰_J(M)` is the `J`-power torsion of `M`, the union of
the annihilators `{m | Jⁿ m = 0}` of the powers of `J`, which is Mathlib's `J`-primary component
`Ideal.primaryComponent M J`.

The comparison is the canonical map `localCohomology.degreeZeroToModule J M : H⁰_J(M) ⟶ M`.
On the term of index `n` of the colimit it identifies `Ext⁰(R ⧸ Jⁿ, M)` with `Hom(R ⧸ Jⁿ, M)`
(`CategoryTheory.extZeroIso`) and evaluates at `1`; these maps are compatible along the
quotient maps `R ⧸ Jⁿ⁺¹ ⟶ R ⧸ Jⁿ`, which send `1` to `1`. Evaluation at `1` identifies
`Hom(R ⧸ Jⁿ, M)` with the annihilator of `Jⁿ` in `M` (`Ideal.quotientLinearMapEquivTorsionBySet`),
and the colimit is filtered, so the induced map is injective with image the union of these
annihilators.

## Main definitions

* `localCohomology.degreeZeroToModule J M`: the canonical map `H⁰_J(M) ⟶ M`, natural in `M`
  (`localCohomology.degreeZeroToModule_naturality`).

## Main results

* `localCohomology.degreeZeroToModule_ι`: on the term of index `n` it is evaluation at `1`.
* `localCohomology.degreeZeroToModule_injective`: the map `H⁰_J(M) ⟶ M` is injective.
* `localCohomology.range_degreeZeroToModule` and `localCohomology.range_hom_degreeZeroToModule`:
  its image is the `J`-primary component `⨆ n, torsionBySet R M (Jⁿ)`, the union of the
  annihilators of the powers of `J`.

## References

* [Stacks Project, Lemma 47.8.2](https://stacks.math.columbia.edu/tag/0954): for a finitely
  generated ideal, the degree-zero part of the comparison of local cohomology with derived
  `J`-power torsion.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace localCohomology

variable {R : Type u} [CommRing R] (J : Ideal R) (M : ModuleCat.{u} R)

section EvalOne

variable (I : Ideal R)

/-- Evaluation at `1`, the `R`-linear map `Hom(R ⧸ I, M) → M`: the identification of
`Hom(R ⧸ I, M)` with the annihilator of `I` in `M`, followed by the inclusion into `M`. -/
private noncomputable def evalOne : ModuleCat.of R (ModuleCat.of R (R ⧸ I) ⟶ M) ⟶ M :=
  ModuleCat.ofHom ((Submodule.torsionBySet R M I).subtype ∘ₗ
    (I.quotientLinearMapEquivTorsionBySet M).toLinearMap ∘ₗ ModuleCat.homLinearEquiv.toLinearMap)

private theorem evalOne_apply (f : ModuleCat.of R (R ⧸ I) ⟶ M) :
    evalOne M I f = f (1 : R ⧸ I) :=
  I.coe_quotientLinearMapEquivTorsionBySet_apply M f.hom

private theorem evalOne_injective : Function.Injective (evalOne M I) :=
  Subtype.val_injective.comp
    ((I.quotientLinearMapEquivTorsionBySet M).injective.comp ModuleCat.homLinearEquiv.injective)

private theorem range_evalOne :
    Set.range (evalOne M I) = Submodule.torsionBySet R M (I : Set R) := by
  simp only [evalOne, ModuleCat.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Submodule.coe_subtype]
  rw [((I.quotientLinearMapEquivTorsionBySet M).surjective.comp
    ModuleCat.homLinearEquiv.surjective).range_comp, Subtype.range_coe]

/-- Evaluation at `1` is natural in the module. -/
private theorem evalOne_naturality {N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((linearCoyoneda R (ModuleCat R)).obj (op (ModuleCat.of R (R ⧸ I)))).map f ≫ evalOne N I =
      evalOne M I ≫ f := by
  ext g
  -- `Hom(R ⧸ I, -)` acts on `g` by postcomposition, `g ≫ f`, by definition
  -- (`linearCoyoneda_obj_map`). The domain of `evalOne` is `Hom(R ⧸ I, M)` only after unfolding
  -- `linearCoyoneda`, so the goal is not type-correct at reducible transparency and cannot be
  -- rewritten; the steps are chained with `Eq.trans`.
  exact (evalOne_apply N I (((linearCoyoneda R (ModuleCat R)).obj _).map f g)).trans
    ((ConcreteCategory.comp_apply g f _).trans (congrArg f (evalOne_apply M I g)).symm)

/-- Evaluation at `1` is compatible with the quotient maps `R ⧸ I ⟶ R ⧸ I'` for `I ≤ I'`, which
send `1` to `1`. -/
private theorem evalOne_precomp {I' : Ideal R} (h : I ≤ I') :
    ((linearYoneda R (ModuleCat R)).obj M).map
        (ModuleCat.ofHom (Submodule.mapQ I I' LinearMap.id h)).op ≫ evalOne M I = evalOne M I' := by
  have h1 : Submodule.mapQ I I' LinearMap.id h (1 : R ⧸ I) = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), ← Ideal.Quotient.mk_eq_mk, Submodule.mapQ_apply,
      LinearMap.id_apply, Ideal.Quotient.mk_eq_mk, map_one]
  ext (g : ModuleCat.of R (R ⧸ I') ⟶ M)
  -- `Hom(-, M)` acts on `g` by precomposition with the quotient map, by definition
  -- (`linearYoneda_obj_map`), and the quotient map sends `1` to `1` (`h1`). As in
  -- `evalOne_naturality`, the goal is only type-correct up to unfolding `linearYoneda`, so the
  -- steps are chained with `Eq.trans`.
  exact (evalOne_apply M I _).trans ((congrArg g h1).trans (evalOne_apply M I' g).symm)

end EvalOne

/-- The cocone with vertex `M` on the diagram `n ↦ Ext⁰(R ⧸ Jⁿ, M)` defining `H⁰_J(M)`, whose leg
of index `n` is `Ext⁰(R ⧸ Jⁿ, M) ≅ Hom(R ⧸ Jⁿ, M)` followed by evaluation at `1`. -/
private noncomputable def degreeZeroCocone :
    Cocone (diagram (idealPowersDiagram J) 0 ⋙ (evaluation _ _).obj M) where
  pt := M
  ι :=
    { app t := (extZeroIso _ M).hom ≫ evalOne M _
      naturality t t' w := by
        dsimp
        rw [Category.comp_id, extZeroIso_hom_naturality_left_assoc]
        exact (extZeroIso _ M).hom ≫= evalOne_precomp M _ _ }

/-- The leg of `degreeZeroCocone` of index `n` is injective. -/
private theorem degreeZeroCocone_ι_app_injective (t : ℕᵒᵖᵒᵖ) :
    Function.Injective ((degreeZeroCocone J M).ι.app t) :=
  (evalOne_injective M _).comp (ConcreteCategory.bijective_of_isIso (extZeroIso _ M).hom).1

/-- The image of the leg of `degreeZeroCocone` of index `n` is the annihilator of `Jⁿ`. -/
private theorem range_degreeZeroCocone_ι_app (t : ℕᵒᵖᵒᵖ) :
    Set.range ((degreeZeroCocone J M).ι.app t) =
      (Submodule.torsionBySet R M ((J ^ t.unop.unop : Ideal R) : Set R) : Set M) :=
  ((ConcreteCategory.bijective_of_isIso (extZeroIso _ M).hom).2.range_comp (evalOne M _)).trans
    (range_evalOne M _)

/-- The forgetful functor of `R`-modules preserves colimits indexed by `ℕᵒᵖᵒᵖ`, which is
filtered; the shape lives in `Type`, below the universe of `R`. -/
private instance : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
  preservesFilteredColimitsOfSize_shrink.{0, u, 0, u} _

/-- The colimit cocone defining local cohomology, evaluated at `M`, is a colimit cocone. -/
private noncomputable def isColimitEvaluation :
    IsColimit (((evaluation _ _).obj M).mapCocone
      (colimit.cocone (diagram (idealPowersDiagram J) 0))) :=
  isColimitOfPreserves _ (colimit.isColimit _)

/-- The canonical map `H⁰_J(M) ⟶ M` from the degree-zero local cohomology module: on the term of
index `n` of the colimit, it identifies `Ext⁰(R ⧸ Jⁿ, M)` with `Hom(R ⧸ Jⁿ, M)` and evaluates at
`1` (`degreeZeroToModule_ι`). -/
noncomputable def degreeZeroToModule : (localCohomology J 0).obj M ⟶ M :=
  (isColimitEvaluation J M).desc (degreeZeroCocone J M)

@[reassoc]
private theorem ι_app_degreeZeroToModule (t : ℕᵒᵖᵒᵖ) :
    (colimit.ι (diagram (idealPowersDiagram J) 0) t).app M ≫ degreeZeroToModule J M =
      (degreeZeroCocone J M).ι.app t :=
  (isColimitEvaluation J M).fac (degreeZeroCocone J M) t

private theorem degreeZeroToModule_ι_app_apply (t : ℕᵒᵖᵒᵖ)
    (x : ((diagram (idealPowersDiagram J) 0).obj t).obj M) :
    degreeZeroToModule J M ((((evaluation _ _).obj M).mapCocone
        (colimit.cocone (diagram (idealPowersDiagram J) 0))).ι.app t x) =
      (degreeZeroCocone J M).ι.app t x :=
  ConcreteCategory.congr_hom (ι_app_degreeZeroToModule J M t) x

/-- On the term of index `n` of the colimit defining `H⁰_J(M)`, the map `degreeZeroToModule` is
evaluation at `1` of the morphism `R ⧸ Jⁿ ⟶ M` corresponding to an element of
`Ext⁰(R ⧸ Jⁿ, M)`. -/
theorem degreeZeroToModule_ι (t : ℕᵒᵖᵒᵖ)
    (x : ((diagram (idealPowersDiagram J) 0).obj t).obj M) :
    degreeZeroToModule J M ((colimit.ι (diagram (idealPowersDiagram J) 0) t).app M x) =
      (extZeroIso _ M).hom x (1 : R ⧸ J ^ t.unop.unop) :=
  (degreeZeroToModule_ι_app_apply J M t x).trans (evalOne_apply M _ _)

/-- The map `H⁰_J(M) ⟶ M` is natural in `M`. -/
@[reassoc]
theorem degreeZeroToModule_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (localCohomology J 0).map f ≫ degreeZeroToModule J N = degreeZeroToModule J M ≫ f := by
  -- `localCohomology J 0` is by definition the colimit of `diagram (idealPowersDiagram J) 0`, and
  -- the legs of the evaluated colimit cocone are the components `(colimit.ι _ t).app M`. The
  -- composites below are only type-correct up to this unfolding, so `rw` cannot be used for the
  -- first and last steps and they are chained with `Eq.trans`: the naturality of the colimit leg,
  -- the leg of `degreeZeroToModule` at `N` (`ι_app_degreeZeroToModule`), the naturality of
  -- `extZeroIso` and of evaluation at `1` in the module, and the leg of `degreeZeroToModule` at
  -- `M`.
  refine (isColimitEvaluation J M).hom_ext fun t ↦
    ((colimit.ι (diagram (idealPowersDiagram J) 0) t).naturality_assoc f _).symm.trans ?_
  rw [ι_app_degreeZeroToModule]
  exact (extZeroIso_hom_naturality_right_assoc _ f _).trans
    (((extZeroIso _ M).hom ≫= evalOne_naturality M _ f).trans
      ((Category.assoc _ _ _).symm.trans (ι_app_degreeZeroToModule_assoc J M t f).symm))

/-- **Local cohomology in degree zero is torsion, injectivity.** For any commutative ring `R`,
ideal `J` and module `M`, the canonical map `H⁰_J(M) ⟶ M` is injective. -/
theorem degreeZeroToModule_injective : Function.Injective (degreeZeroToModule J M) := by
  intro a b h
  obtain ⟨i, x, rfl⟩ := Concrete.isColimit_exists_rep _ (isColimitEvaluation J M) a
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep _ (isColimitEvaluation J M) b
  -- Push both representatives to a common index, where the leg of the cocone is injective.
  refine Concrete.isColimit_rep_eq_of_exists _ x y ⟨IsFiltered.max i j,
    IsFiltered.leftToMax i j, IsFiltered.rightToMax i j,
    degreeZeroCocone_ι_app_injective J M _ ?_⟩
  rw [Cocone.w_apply, Cocone.w_apply, ← degreeZeroToModule_ι_app_apply,
    ← degreeZeroToModule_ι_app_apply]
  exact h

/-- The canonical map `H⁰_J(M) ⟶ M` is a monomorphism. -/
instance : Mono (degreeZeroToModule J M) :=
  (ModuleCat.mono_iff_injective _).2 (degreeZeroToModule_injective J M)

/-- **Local cohomology in degree zero is torsion, image.** For any commutative ring `R`, ideal `J`
and module `M`, the image of the canonical map `H⁰_J(M) ⟶ M` is the `J`-primary component of
`M`, the union of the annihilators of the powers `Jⁿ`. -/
theorem range_degreeZeroToModule :
    Set.range (degreeZeroToModule J M) = Ideal.primaryComponent M J := by
  ext m
  rw [SetLike.mem_coe, Ideal.primaryComponent_mem]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨i, x, rfl⟩ := Concrete.isColimit_exists_rep _ (isColimitEvaluation J M) a
    have hx : (degreeZeroCocone J M).ι.app i x ∈ Set.range ((degreeZeroCocone J M).ι.app i) :=
      Set.mem_range_self x
    rw [range_degreeZeroCocone_ι_app] at hx
    rw [degreeZeroToModule_ι_app_apply]
    exact ⟨i.unop.unop, hx⟩
  · rintro ⟨n, hn⟩
    rw [← SetLike.mem_coe, ← range_degreeZeroCocone_ι_app J M (op (op n))] at hn
    obtain ⟨x, rfl⟩ := hn
    exact ⟨_, degreeZeroToModule_ι_app_apply J M _ x⟩

/-- The image of the canonical map `H⁰_J(M) ⟶ M`, as a submodule of `M`, is the `J`-primary
component of `M`. -/
theorem range_hom_degreeZeroToModule :
    LinearMap.range (degreeZeroToModule J M).hom = Ideal.primaryComponent M J :=
  SetLike.coe_injective ((LinearMap.coe_range _).trans (range_degreeZeroToModule J M))

end localCohomology
