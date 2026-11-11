/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Local cohomology in degree zero

Mathlib defines the local cohomology module `H^i_J(M) = (localCohomology J i).obj M` of a module
`M` over a commutative ring `R` as the colimit over `n` of `Extⁱ(R ⧸ Jⁿ, M)`, where `Ext` is the
left derived functor `Ext R (ModuleCat R) i` of `Hom(-, M)`. This file computes the degree-zero
group for an arbitrary commutative ring: `H⁰_J(M)` is the `J`-power torsion of `M`, the union of
the annihilators `{m | Jⁿ m = 0}` of the powers of `J`.

The comparison is the canonical map `localCohomology.degreeZeroToModule J M : H⁰_J(M) ⟶ M`.
On the term of index `n` of the colimit it identifies `Ext⁰(R ⧸ Jⁿ, M)` with `Hom(R ⧸ Jⁿ, M)`
(`CategoryTheory.extZeroIso`) and evaluates at `1`; these maps are compatible along the
quotient maps `R ⧸ Jⁿ⁺¹ ⟶ R ⧸ Jⁿ`, which send `1` to `1`. Evaluation at `1` identifies
`Hom(R ⧸ Jⁿ, M)` with the annihilator of `Jⁿ` in `M`, and the colimit is filtered, so the
induced map is injective with image the union of these annihilators.

The identification `Ext⁰(X, Y) ≅ Hom(X, Y)` holds in any abelian category with enough
projectives: `Hom(-, Y)` sends finite colimits to finite limits, so the zeroth left derived
functor of `Hom(-, Y)`, read in the opposite category, is `Hom(-, Y)` itself
(`CategoryTheory.Functor.leftDerivedZeroIsoSelf`).

## Main definitions

* `CategoryTheory.extZeroIso`: the isomorphism `Ext⁰(X, Y) ≅ Hom(X, Y)`, natural in `X`
  (`CategoryTheory.extZeroIso_hom_naturality`).
* `localCohomology.degreeZeroToModule J M`: the canonical map `H⁰_J(M) ⟶ M`.

## Main results

* `localCohomology.degreeZeroToModule_ι`: on the term of index `n` it is evaluation at `1`.
* `localCohomology.degreeZeroToModule_injective`: the map `H⁰_J(M) ⟶ M` is injective.
* `localCohomology.range_degreeZeroToModule`: its image is `⨆ n, torsionBySet R M (Jⁿ)`, the
  union of the annihilators of the powers of `J`.

## References

* [Stacks Project, Lemma 47.8.2](https://stacks.math.columbia.edu/tag/0954): for a finitely
  generated ideal, the degree-zero part of the comparison of local cohomology with derived
  `J`-power torsion.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

section ExtZero

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  (k : Type w) [Ring k] [Linear k C]

/-- `Hom(-, Y)` sends finite colimits in `C` to finite limits of `k`-modules. -/
instance preservesFiniteLimits_linearYoneda_obj (Y : C) :
    PreservesFiniteLimits ((linearYoneda k C).obj Y) := by
  have hforget : (linearYoneda k C).obj Y ⋙ forget (ModuleCat.{v} k) = yoneda.obj Y :=
    Functor.congr_obj (whiskering_linearYoneda k C) Y
  have : PreservesFiniteLimits ((linearYoneda k C).obj Y ⋙ forget (ModuleCat.{v} k)) :=
    hforget ▸ inferInstance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget (ModuleCat.{v} k))

/-- `Hom(-, Y)`, read as a functor to the opposite category of `k`-modules, is right exact. -/
instance preservesFiniteColimits_linearYoneda_obj_rightOp (Y : C) :
    PreservesFiniteColimits ((linearYoneda k C).obj Y).rightOp :=
  preservesFiniteColimits_rightOp _

variable {k}

/-- The isomorphism `Ext⁰(X, Y) ≅ Hom(X, Y)` for the left derived functor `Ext k C 0` of
`Hom(-, Y)`: the zeroth left derived functor of the right exact functor `Hom(-, Y)`, read in the
opposite category of `k`-modules, is `Hom(-, Y)` itself. -/
noncomputable def extZeroIso (X Y : C) :
    ((Ext k C 0).obj (op X)).obj Y ≅ ModuleCat.of k (X ⟶ Y) :=
  (((linearYoneda k C).obj Y).rightOp.leftDerivedZeroIsoSelf.app X).unop.symm

/-- The isomorphism `Ext⁰(X, Y) ≅ Hom(X, Y)` is natural in `X`: precomposition with `f : X' ⟶ X`
on `Hom(-, Y)` corresponds to the action of `Ext k C 0` on `f`. -/
@[reassoc]
theorem extZeroIso_hom_naturality {X X' : C} (f : X' ⟶ X) (Y : C) :
    ((Ext k C 0).map f.op).app Y ≫ (extZeroIso X' Y).hom =
      (extZeroIso X Y).hom ≫ ((linearYoneda k C).obj Y).map f.op :=
  Quiver.Hom.op_inj
    (((linearYoneda k C).obj Y).rightOp.leftDerivedZeroIsoSelf.inv.naturality f).symm

end ExtZero

end CategoryTheory

namespace localCohomology

variable {R : Type u} [CommRing R] (J : Ideal R) (M : ModuleCat.{u} R)

section EvalOne

variable (I : Ideal R)

/-- Evaluation at `1`, the `R`-linear map `Hom(R ⧸ I, M) → M`. -/
@[expose]
def evalOne : ModuleCat.of R (ModuleCat.of R (R ⧸ I) ⟶ M) ⟶ M :=
  ModuleCat.ofHom
    { toFun f := f (Submodule.Quotient.mk 1)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

@[simp]
theorem evalOne_apply (f : ModuleCat.of R (R ⧸ I) ⟶ M) :
    evalOne M I f = f (Submodule.Quotient.mk 1) :=
  rfl

/-- A morphism out of the cyclic module `R ⧸ I` is determined by its value at `1`. -/
theorem evalOne_injective : Function.Injective (evalOne M I) := fun _ _ h ↦
  ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext_ring h))

/-- The values at `1` of the morphisms `R ⧸ I ⟶ M` are the elements of `M` killed by `I`. -/
theorem range_evalOne :
    Set.range (evalOne M I) = Submodule.torsionBySet R M (I : Set R) := by
  ext m
  refine ⟨?_, fun hm ↦ ?_⟩
  · rintro ⟨f, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_torsionBySet_iff]
    rintro ⟨a, ha⟩
    rw [evalOne_apply, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero I).mpr ha, map_zero]
  · rw [SetLike.mem_coe, Submodule.mem_torsionBySet_iff] at hm
    exact ⟨ModuleCat.ofHom (I.liftQ (LinearMap.toSpanSingleton R M m) fun a ha ↦ hm ⟨a, ha⟩),
      one_smul R m⟩

end EvalOne

/-- The cocone with vertex `M` on the diagram `n ↦ Ext⁰(R ⧸ Jⁿ, M)` defining `H⁰_J(M)`, whose leg
of index `n` is `Ext⁰(R ⧸ Jⁿ, M) ≅ Hom(R ⧸ Jⁿ, M)` followed by evaluation at `1`. -/
@[expose]
noncomputable def degreeZeroCocone :
    Cocone (diagram (idealPowersDiagram J) 0 ⋙ (evaluation _ _).obj M) where
  pt := M
  ι :=
    { app t := (extZeroIso _ M).hom ≫ evalOne M _
      naturality t t' w := by
        dsimp
        rw [Category.comp_id, extZeroIso_hom_naturality_assoc]
        -- The quotient map `R ⧸ Jⁿ⁺ᵐ ⟶ R ⧸ Jⁿ` sends `1` to `1`.
        rfl }

/-- The leg of `degreeZeroCocone` of index `n` is injective. -/
theorem degreeZeroCocone_ι_app_injective (t : ℕᵒᵖᵒᵖ) :
    Function.Injective ((degreeZeroCocone J M).ι.app t) :=
  (evalOne_injective M _).comp (ConcreteCategory.bijective_of_isIso (extZeroIso _ M).hom).1

/-- The image of the leg of `degreeZeroCocone` of index `n` is the annihilator of `Jⁿ`. -/
theorem range_degreeZeroCocone_ι_app (t : ℕᵒᵖᵒᵖ) :
    Set.range ((degreeZeroCocone J M).ι.app t) =
      (Submodule.torsionBySet R M ((J ^ t.unop.unop : Ideal R) : Set R) : Set M) := by
  rw [← range_evalOne]
  change Set.range (evalOne M _ ∘ (extZeroIso _ M).hom) = _
  exact (ConcreteCategory.bijective_of_isIso (extZeroIso _ M).hom).2.range_comp _

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

/-- On the term of index `n` of the colimit defining `H⁰_J(M)`, the map `degreeZeroToModule` is
evaluation at `1` of the morphism `R ⧸ Jⁿ ⟶ M` corresponding to an element of
`Ext⁰(R ⧸ Jⁿ, M)`. -/
theorem degreeZeroToModule_ι (n : ℕ)
    (x : ((Ext R (ModuleCat.{u} R) 0).obj (op (ModuleCat.of R (R ⧸ J ^ n)))).obj M) :
    degreeZeroToModule J M ((colimit.ι (diagram (idealPowersDiagram J) 0) (op (op n))).app M x) =
      (extZeroIso _ M).hom x (Submodule.Quotient.mk 1) :=
  ConcreteCategory.congr_hom ((isColimitEvaluation J M).fac (degreeZeroCocone J M) (op (op n))) x

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
  have hx := ConcreteCategory.congr_hom
    ((isColimitEvaluation J M).fac (degreeZeroCocone J M) i) x
  have hy := ConcreteCategory.congr_hom
    ((isColimitEvaluation J M).fac (degreeZeroCocone J M) j) y
  have hx' := ConcreteCategory.congr_hom ((degreeZeroCocone J M).w (IsFiltered.leftToMax i j)) x
  have hy' := ConcreteCategory.congr_hom ((degreeZeroCocone J M).w (IsFiltered.rightToMax i j)) y
  rw [ConcreteCategory.comp_apply] at hx' hy' hx hy
  rw [hx', hy', ← hx, ← hy]
  exact h

/-- **Local cohomology in degree zero is torsion, image.** For any commutative ring `R`, ideal `J`
and module `M`, the image of the canonical map `H⁰_J(M) ⟶ M` is the `J`-power torsion of `M`,
the union of the annihilators of the powers `Jⁿ`. -/
theorem range_degreeZeroToModule :
    Set.range (degreeZeroToModule J M) =
      (⨆ n : ℕ, Submodule.torsionBySet R M ((J ^ n : Ideal R) : Set R) : Submodule R M) := by
  have hmono : Monotone fun n : ℕ ↦ Submodule.torsionBySet R M ((J ^ n : Ideal R) : Set R) :=
    fun _ _ hmn ↦ Submodule.torsionBySet_le_torsionBySet_of_subset
      (Ideal.pow_le_pow_right hmn)
  ext m
  rw [SetLike.mem_coe, Submodule.mem_iSup_of_directed _ hmono.directed_le]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨i, x, rfl⟩ := Concrete.isColimit_exists_rep _ (isColimitEvaluation J M) a
    have hx := ConcreteCategory.congr_hom
      ((isColimitEvaluation J M).fac (degreeZeroCocone J M) i) x
    rw [ConcreteCategory.comp_apply] at hx
    exact ⟨i.unop.unop, hx ▸ (range_degreeZeroCocone_ι_app J M i ▸ Set.mem_range_self x :
      (degreeZeroCocone J M).ι.app i x ∈
        (Submodule.torsionBySet R M ((J ^ i.unop.unop : Ideal R) : Set R) : Set M))⟩
  · rintro ⟨n, hn⟩
    rw [← SetLike.mem_coe, ← range_degreeZeroCocone_ι_app J M (op (op n))] at hn
    obtain ⟨x, rfl⟩ := hn
    exact ⟨_, ConcreteCategory.congr_hom
      ((isColimitEvaluation J M).fac (degreeZeroCocone J M) (op (op n))) x⟩

end localCohomology
