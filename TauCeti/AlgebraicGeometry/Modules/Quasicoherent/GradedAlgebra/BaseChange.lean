/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback
public import TauCeti.RingTheory.IsTensorProduct.Pushout

/-!
# Graded rings of sections under base change

Let `f : Y ⟶ X` be a morphism of schemes and `A = ⨁ₙ Aₙ` a graded quasicoherent algebra on `X`,
with pullback `f^* A = ⨁ₙ f^* Aₙ` (`GradedQuasicoherentAlgebra.pullback`). Pulling back sections
degree by degree is a homomorphism of graded rings

`⨁ n, Γ(Aₙ, U) → ⨁ n, Γ(f^* Aₙ, f⁻¹ U)`

over `f^♯ : Γ(X, U) → Γ(Y, f⁻¹ U)`, for every open `U` of `X`
(`GradedQuasicoherentAlgebra.pullbackGradedSections`). When `U` and `f⁻¹ U` are affine, it
exhibits the graded ring of sections of `f^* A` as the base change of that of `A`: the square of
commutative rings

```
Γ(X, U) ──────→ ⨁ n, Γ(Aₙ, U)
   │                   │
   ↓                   ↓
Γ(Y, f⁻¹ U) ──→ ⨁ n, Γ(f^* Aₙ, f⁻¹ U)
```

is a pushout (`GradedQuasicoherentAlgebra.isPushout_pullbackGradedSections`). In each degree this
is base change of the sections of a quasicoherent module (`Scheme.Hom.pullbackSectionsEquiv`),
and base change commutes with direct sums. Multiplicativity comes from the compatibility of
pullback of sections with the tensor comparison of pullback
(`Scheme.Hom.δ_app_pullbackSections_μ`).

So the affine graded charts of `A` are compatible with arbitrary base change, in the same way as
they are with restriction to smaller affine opens
(`CategoryTheory.CommMon.isPushout_restrictGradedSections`). As consequences, base change
preserves finite generation of the graded ring of sections over the ring of regular functions,
and generation in degree one. These are the affine inputs for base change of relative spectra and
relative `Proj` of graded quasicoherent algebras.

## Main statements

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.pullbackGradedSections`: pullback of
  sections, as a ring homomorphism between graded rings of sections, with
  `pullbackGradedSections_of`, `pullbackGradedSections_apply`,
  `pullbackGradedSections_algebraMap` and compatibility with restriction
  `pullbackGradedSections_restrictGradedSections`; its graded form is
  `pullbackGradedSectionsGradedHom`.
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isPushout_pullbackGradedSections`: for
  affine `U` and `f⁻¹ U`, the square above is a pushout of commutative rings.
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.finiteType_gradedSections_pullback` and
  `adjoin_gradedSectionsGrading_zero_union_one_eq_top_pullback`: finite generation and
  generation in degree one pass to `f^* A`.

## References

* [The Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9) (pullback of
  quasicoherent sheaves on affine schemes) and
  [Section 27.15, Relative Proj](https://stacks.math.columbia.edu/tag/01NS).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2.
-/

public section

open CategoryTheory MonoidalCategory DirectSum AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (A : GradedQuasicoherentAlgebra X)

/-- The identification of the degree-`n` component of `f^* A` with the pullback of the
degree-`n` component of `A`, as a morphism. -/
private abbrev pullbackComponentHom (n : ℕ) :
    (Scheme.Modules.pullback f).obj (A.obj.X n) ⟶ ((pullback f).obj A).obj.X n :=
  eqToHom (pullback_obj_obj_X f A n).symm

/-- The identifications of the components of `f^* A` cancel in pairs. -/
private lemma pullbackComponentHom_tensorHom_eqToHom (i j : ℕ) :
    (pullbackComponentHom f A i ⊗ₘ pullbackComponentHom f A j) ≫
        (eqToHom (pullback_obj_obj_X f A i) ⊗ₘ eqToHom (pullback_obj_obj_X f A j)) = 𝟙 _ := by
  rw [tensorHom_comp_tensorHom, eqToHom_trans, eqToHom_trans, eqToHom_refl, eqToHom_refl,
    id_tensorHom_id]

variable (U : X.Opens)

/-- Pulling back sections of the degree-`n` component of `A` to sections of the degree-`n`
component of `f^* A`, semilinearly over `f^♯ : Γ(X, U) → Γ(Y, f⁻¹ U)`. -/
private def pullbackSectionsDegree (n : ℕ) :
    Γ(A.obj.X n, U) →ₛₗ[(f.app U).hom] Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.sectionsFunctor (f ⁻¹ᵁ U)).map (pullbackComponentHom f A n)).hom.comp
    (f.pullbackSections (A.obj.X n) U)

/-- Pullback of sections preserves the homogeneous multiplication. -/
private lemma pullbackSectionsDegree_gMul {i j : ℕ} (x : Γ(A.obj.X i, U))
    (y : Γ(A.obj.X j, U)) :
    pullbackSectionsDegree f A U (i + j)
        (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.obj.X n, U)) x y) =
      GradedMonoid.GMul.mul (A := fun n ↦ Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U))
        (pullbackSectionsDegree f A U i x) (pullbackSectionsDegree f A U j y) := by
  set δ := Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) (A.obj.X i) (A.obj.X j)
  set z := Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y)
  set w := Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor (f ⁻¹ᵁ U)) _ _
    (f.pullbackSections (A.obj.X i) U x ⊗ₜ f.pullbackSections (A.obj.X j) U y)
  -- The tensor comparison of pullback sends the pullback of `x ⊗ y` to `w`, so its inverse sends
  -- `w` back to the pullback of `x ⊗ y`.
  have hδ := congr($(IsIso.hom_inv_id δ).app (f ⁻¹ᵁ U)
    (f.pullbackSections (A.obj.X i ⊗ A.obj.X j) U z))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] at hδ
  -- The tensor map of sections commutes with the identifications of the components.
  have hn := congr($(Functor.LaxMonoidal.μ_natural (Scheme.Modules.sectionsFunctor (f ⁻¹ᵁ U))
    (pullbackComponentHom f A i) (pullbackComponentHom f A j))
      (f.pullbackSections (A.obj.X i) U x ⊗ₜ f.pullbackSections (A.obj.X j) U y))
  simp only [ConcreteCategory.comp_apply] at hn
  have hid := congr($(pullbackComponentHom_tensorHom_eqToHom f A i j).app (f ⁻¹ᵁ U) w)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at hid
  have hm := congr($(pullback_obj_mul f A i j).app (f ⁻¹ᵁ U)
    ((pullbackComponentHom f A i ⊗ₘ pullbackComponentHom f A j).app (f ⁻¹ᵁ U) w))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hm
  -- Chain the steps from the product of the pullbacks back to the pullback of the product; the
  -- degree maps are by definition the transported pullbacks of sections.
  let mul' := (((pullback f).obj A).obj.toMon.mul i j).app (f ⁻¹ᵁ U)
  let mulPull := ((Scheme.Modules.pullback f).map (A.obj.toMon.mul i j)).app (f ⁻¹ᵁ U)
  let e : Γ((Scheme.Modules.pullback f).obj (A.obj.X (i + j)), f ⁻¹ᵁ U) →
      Γ(((pullback f).obj A).obj.toMon.X (i + j), f ⁻¹ᵁ U) :=
    (pullbackComponentHom f A (i + j)).app (f ⁻¹ᵁ U)
  let δinv := (inv δ).app (f ⁻¹ᵁ U)
  rw [CommMon.sections_gMul_def, CommMon.sections_gMul_def]
  symm
  calc _ = mul' ((pullbackComponentHom f A i ⊗ₘ pullbackComponentHom f A j).app (f ⁻¹ᵁ U) w) :=
        congrArg mul' hn
    _ = e (mulPull (δinv w)) := hm.trans (congrArg (fun t ↦ e (mulPull (δinv t))) hid)
    _ = e (mulPull (δinv (δ.app (f ⁻¹ᵁ U)
          (f.pullbackSections (A.obj.X i ⊗ A.obj.X j) U z)))) := by
        rw [Scheme.Hom.δ_app_pullbackSections_μ]
    _ = e (mulPull (f.pullbackSections (A.obj.X i ⊗ A.obj.X j) U z)) :=
        congrArg (fun t ↦ e (mulPull t)) hδ
    _ = _ := congrArg e (f.pullbackSections_naturality _ U (A.obj.toMon.mul i j) z)

/-- Pullback of sections commutes with the structure maps `Γ(X, U) → Γ(A₀, U)` and
`Γ(Y, f⁻¹ U) → Γ(f^* A₀, f⁻¹ U)`. -/
private lemma pullbackSectionsDegree_toFun (r : Γ(X, U)) :
    pullbackSectionsDegree f A U 0
        (GAlgebra.toFun (R := Γ(X, U)) (A := fun n ↦ Γ(A.obj.X n, U)) r) =
      GAlgebra.toFun (R := Γ(Y, f ⁻¹ᵁ U))
        (A := fun n ↦ Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) (f.app U r) := by
  rw [CommMon.gAlgebraSections_toFun, CommMon.gAlgebraSections_toFun]
  set v := f.pullbackSections (𝟙_ X.Modules) U
    (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r)
  -- The identification `f^* 𝒪_X ≅ 𝒪_Y` sends `v` to `f^♯ r`, so its inverse sends `f^♯ r` to `v`.
  have hu := congr($((Scheme.Modules.pullbackObjUnitIso f).hom_inv_id).app (f ⁻¹ᵁ U) v)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply] at hu
  have ho := congr($(pullback_obj_one f A).app (f ⁻¹ᵁ U)
    (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor (f ⁻¹ᵁ U)) (f.app U r)))
  simp only [Scheme.Modules.Hom.comp_app] at ho
  -- The degree-zero map is by definition the transported pullback of sections.
  let e : Γ((Scheme.Modules.pullback f).obj (A.obj.X 0), f ⁻¹ᵁ U) →
      Γ(((pullback f).obj A).obj.toMon.X 0, f ⁻¹ᵁ U) :=
    (pullbackComponentHom f A 0).app (f ⁻¹ᵁ U)
  let onePull := ((Scheme.Modules.pullback f).map A.obj.toMon.one).app (f ⁻¹ᵁ U)
  let unitInv := (Scheme.Modules.pullbackObjUnitIso f).inv.app (f ⁻¹ᵁ U)
  symm
  calc _ = e (onePull (unitInv
        (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor (f ⁻¹ᵁ U)) (f.app U r)))) := ho
    _ = e (onePull (unitInv ((Scheme.Modules.pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U) v))) := by
        rw [Scheme.Hom.pullbackObjUnitIso_hom_app_pullbackSections_ε]
    _ = e (onePull v) := congrArg (fun t ↦ e (onePull t)) hu
    _ = _ := congrArg e (f.pullbackSections_naturality (𝟙_ X.Modules) U A.obj.toMon.one _)

/-- Pullback of sections preserves the unit. -/
private lemma pullbackSectionsDegree_gOne :
    pullbackSectionsDegree f A U 0 (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.obj.X n, U))) =
      GradedMonoid.GOne.one (A := fun n ↦ Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) := by
  have h := pullbackSectionsDegree_toFun f A U 1
  rw [map_one (f.app U).hom, CommMon.gAlgebraSections_toFun, CommMon.gAlgebraSections_toFun] at h
  rw [CommMon.sections_gOne_def, CommMon.sections_gOne_def]
  exact h

/-- **Pullback of graded sections.** For a morphism of schemes `f : Y ⟶ X`, a graded
quasicoherent algebra `A` on `X` and an open `U` of `X`, pulling back sections degree by degree is
a ring homomorphism from the graded ring of sections of `A` over `U` to that of `f^* A` over
`f⁻¹ U`. It sends each homogeneous section to its pullback, in the same degree
(`pullbackGradedSections_of`), and lies over `f^♯ : Γ(X, U) → Γ(Y, f⁻¹ U)`
(`pullbackGradedSections_algebraMap`). -/
def pullbackGradedSections :
    (⨁ n, Γ(A.obj.X n, U)) →+* ⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U) :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (fun n ↦ Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) n).comp
      (pullbackSectionsDegree f A U n).toAddMonoidHom)
    ((congrArg _ (pullbackSectionsDegree_gOne f A U)).trans (DirectSum.of_zero_one _))
    (fun x y ↦ (congrArg _ (pullbackSectionsDegree_gMul f A U x y)).trans
      (DirectSum.of_mul_of _ _).symm)

/-- Pullback of graded sections sends a homogeneous section to its pullback, in the same degree,
transported along the identification of the components of `f^* A` with the pullbacks of the
components of `A`. -/
@[simp]
lemma pullbackGradedSections_of (n : ℕ) (x : Γ(A.obj.X n, U)) :
    pullbackGradedSections f A U (DirectSum.of _ n x) =
      DirectSum.of _ n ((eqToHom (pullback_obj_obj_X f A n).symm).app (f ⁻¹ᵁ U)
        (f.pullbackSections (A.obj.X n) U x)) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- Pullback of graded sections pulls back each homogeneous component, transported along the
identification of the components of `f^* A` with the pullbacks of the components of `A`. -/
@[simp]
lemma pullbackGradedSections_apply (x : ⨁ n, Γ(A.obj.X n, U)) (n : ℕ) :
    pullbackGradedSections f A U x n =
      (eqToHom (pullback_obj_obj_X f A n).symm).app (f ⁻¹ᵁ U)
        (f.pullbackSections (A.obj.X n) U (x n)) := by
  have h : (pullbackGradedSections f A U).toAddMonoidHom =
      DirectSum.map fun n ↦ (pullbackSectionsDegree f A U n).toAddMonoidHom :=
    DirectSum.addHom_ext fun n y ↦ by simp; rfl
  exact congrArg (· n) (DFunLike.congr_fun h x)

/-- Pullback of graded sections lies over `f^♯ : Γ(X, U) → Γ(Y, f⁻¹ U)`. -/
@[simp]
lemma pullbackGradedSections_algebraMap (r : Γ(X, U)) :
    pullbackGradedSections f A U (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(Y, f ⁻¹ᵁ U) (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) (f.app U r) := by
  rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply, pullbackGradedSections_of]
  exact congrArg _ (pullbackSectionsDegree_toFun f A U r)

/-- Pullback of sections, as a graded ring homomorphism between the graded rings of sections.
Its underlying ring homomorphism is `pullbackGradedSections`
(`pullbackGradedSectionsGradedHom_toRingHom`). -/
def pullbackGradedSectionsGradedHom :
    A.obj.gradedSectionsGrading U →+*ᵍ
      ((pullback f).obj A).obj.gradedSectionsGrading (f ⁻¹ᵁ U) where
  __ := pullbackGradedSections f A U
  map_mem {n x} hx := by
    obtain ⟨x, rfl⟩ := DirectSum.mem_summand.mp hx
    simpa using ((pullback f).obj A).obj.of_mem_gradedSectionsGrading n _

/-- The underlying ring homomorphism of the graded pullback of sections is the pullback of
sections. -/
@[simp]
theorem pullbackGradedSectionsGradedHom_toRingHom :
    (pullbackGradedSectionsGradedHom f A U).toRingHom = pullbackGradedSections f A U :=
  (rfl)

/-- The graded pullback of sections is the pullback of sections. -/
@[simp]
theorem pullbackGradedSectionsGradedHom_apply (x : ⨁ n, Γ(A.obj.X n, U)) :
    pullbackGradedSectionsGradedHom f A U x = pullbackGradedSections f A U x :=
  (rfl)

/-- Pullback of graded sections commutes with restriction to smaller opens. -/
lemma pullbackGradedSections_restrictGradedSections {V : X.Opens} (i : V ⟶ U)
    (x : ⨁ n, Γ(A.obj.X n, U)) :
    pullbackGradedSections f A V (A.obj.restrictGradedSections i x) =
      ((pullback f).obj A).obj.restrictGradedSections ((TopologicalSpace.Opens.map f.base).map i)
        (pullbackGradedSections f A U x) := by
  refine DFinsupp.ext fun n ↦ ?_
  rw [pullbackGradedSections_apply, CommMon.restrictGradedSections_apply,
    CommMon.restrictGradedSections_apply, pullbackGradedSections_apply,
    ← Scheme.Hom.pullbackSections_restrict]
  exact congr($((eqToHom (pullback_obj_obj_X f A n).symm).mapPresheaf.naturality
    ((TopologicalSpace.Opens.map f.base).map i).op) (f.pullbackSections (A.obj.X n) U (x n)))

/-- The graded pullback of sections commutes with restriction to smaller opens. -/
theorem pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom {V : X.Opens}
    (i : V ⟶ U) :
    (pullbackGradedSectionsGradedHom f A V).comp (A.obj.restrictGradedSectionsGradedHom i) =
      (((pullback f).obj A).obj.restrictGradedSectionsGradedHom
        ((TopologicalSpace.Opens.map f.base).map i)).comp (pullbackGradedSectionsGradedHom f A U) :=
  GradedRingHom.ext fun x ↦ by simp [pullbackGradedSections_restrictGradedSections]

variable {U}

/-- **Graded rings of sections under base change.** For a morphism of schemes `f : Y ⟶ X`, a
graded quasicoherent algebra `A` on `X` and an affine open `U` of `X` whose inverse image `f⁻¹ U`
is affine, pullback of sections exhibits `⨁ n, Γ(f^* Aₙ, f⁻¹ U)` as the base change of
`⨁ n, Γ(Aₙ, U)` along `f^♯ : Γ(X, U) → Γ(Y, f⁻¹ U)`. -/
theorem isPushout_pullbackGradedSections (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) :
    IsPushout (f.app U) (CommRingCat.ofHom (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U))))
      (CommRingCat.ofHom
        (algebraMap Γ(Y, f ⁻¹ᵁ U) (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U))))
      (CommRingCat.ofHom (pullbackGradedSections f A U)) := by
  let := (f.app U).hom.toAlgebra
  -- Each `Γ(f^* Aₙ, f⁻¹ U)` is a `Γ(X, U)`-module by restriction of scalars, and pullback of
  -- sections is a base change in each degree.
  let _ (n : ℕ) : Module Γ(X, U) Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U))
  -- By definition of `Module.compHom`, `r` acts through `f^♯ r`.
  have _ (n : ℕ) : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U)
      Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U) := .of_algebraMap_smul fun _ _ ↦ rfl
  let ρ (n : ℕ) : Γ(A.obj.X n, U) →ₗ[Γ(X, U)] Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U) :=
    { toFun := pullbackSectionsDegree f A U n
      map_add' := map_add _
      map_smul' := (pullbackSectionsDegree f A U n).map_smulₛₗ }
  have hρ (n : ℕ) : IsBaseChange Γ(Y, f ⁻¹ᵁ U) (ρ n) :=
    IsBaseChange.of_equiv ((f.pullbackSectionsEquiv (A.obj.X n) hU hV).trans
      ((Scheme.Modules.sectionsFunctor (f ⁻¹ᵁ U)).mapIso
        (eqToIso (pullback_obj_obj_X f A n).symm)).toLinearEquiv) fun x ↦
      congrArg ((pullbackComponentHom f A n).app (f ⁻¹ᵁ U))
        (f.pullbackSectionsEquiv_one_tmul (A.obj.X n) hU hV x)
  -- The `Γ(X, U)`-algebra structure on `⨁ n, Γ(f^* Aₙ, f⁻¹ U)` whose module structure is the
  -- direct sum of the restrictions of scalars.
  let : Algebra Γ(X, U) (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) := Algebra.ofModule
    (fun r x y ↦ by
      rw [← algebraMap_smul Γ(Y, f ⁻¹ᵁ U) r, ← algebraMap_smul Γ(Y, f ⁻¹ᵁ U) r, smul_mul_assoc])
    (fun r x y ↦ by
      rw [← algebraMap_smul Γ(Y, f ⁻¹ᵁ U) r, ← algebraMap_smul Γ(Y, f ⁻¹ᵁ U) r, mul_smul_comm])
  let := (pullbackGradedSections f A U).toAlgebra
  have : IsScalarTower Γ(X, U) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ by
      rw [RingHom.algebraMap_toAlgebra, pullbackGradedSections_algebraMap,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      exact (algebraMap_smul Γ(Y, f ⁻¹ᵁ U) r
        (1 : ⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U))).symm
  have : Algebra.IsPushout Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) := by
    refine ⟨?_⟩
    convert IsBaseChange.directSum hρ using 1
    refine DirectSum.linearMap_ext _ fun n ↦ LinearMap.ext fun x ↦ ?_
    exact (pullbackGradedSections_of f A U n x).trans (DirectSum.lmap_lof ρ n x).symm
  exact CommRingCat.isPushout_iff_isPushout.mpr this

/-- Finite generation of the graded ring of sections over the ring of regular functions passes
to the pullback: the graded ring of `f^* A` over `f⁻¹ U` is the base change of that of `A` over `U`
(`isPushout_pullbackGradedSections`). -/
theorem finiteType_gradedSections_pullback (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    [Algebra.FiniteType Γ(X, U) (⨁ n, Γ(A.obj.X n, U))] :
    Algebra.FiniteType Γ(Y, f ⁻¹ᵁ U) (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) := by
  rw [← RingHom.finiteType_algebraMap]
  exact (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
    RingHom.finiteType_isStableUnderBaseChange).of_isPushout
      (isPushout_pullbackGradedSections f A hU hV)
      (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- **Generation in degree one passes to the pullback.** If the graded ring of sections
`⨁ n, Γ(Aₙ, U)` over an affine open `U` is generated by its homogeneous elements of degrees `0`
and `1`, and `f⁻¹ U` is affine, then the graded ring of sections `⨁ n, Γ(f^* Aₙ, f⁻¹ U)` is
generated by its homogeneous elements of degrees `0` and `1`. -/
theorem adjoin_gradedSectionsGrading_zero_union_one_eq_top_pullback (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (h : Algebra.adjoin Γ(X, U) ((A.obj.gradedSectionsGrading U 0 : Set (⨁ n, Γ(A.obj.X n, U))) ∪
      A.obj.gradedSectionsGrading U 1) = ⊤) :
    Algebra.adjoin Γ(Y, f ⁻¹ᵁ U)
      ((((pullback f).obj A).obj.gradedSectionsGrading (f ⁻¹ᵁ U) 0 :
          Set (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U))) ∪
        ((pullback f).obj A).obj.gradedSectionsGrading (f ⁻¹ᵁ U) 1) = ⊤ := by
  let := (f.app U).hom.toAlgebra
  let := (pullbackGradedSections f A U).toAlgebra
  let : Algebra Γ(X, U) (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) :=
    ((algebraMap Γ(Y, f ⁻¹ᵁ U) (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U))).comp
      (algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U))).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U)
      (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(X, U) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (pullbackGradedSections_algebraMap f A U r).symm
  have : Algebra.IsPushout Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) Γ(Y, f ⁻¹ᵁ U)
      (⨁ n, Γ(((pullback f).obj A).obj.X n, f ⁻¹ᵁ U)) :=
    (CommRingCat.isPushout_iff_isPushout.mp (isPushout_pullbackGradedSections f A hU hV)).symm
  exact Algebra.IsPushout.adjoin_zero_union_one_eq_top (pullbackGradedSectionsGradedHom f A U)
    (pullbackGradedSectionsGradedHom_apply f A U) h

end GradedQuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
