/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.AcyclicResolution
public import TauCeti.Algebra.Homology.HomologicalComplex.FunctorCategory
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

/-!
# Sections of acyclic resolutions compute sheaf cohomology

Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of a sheaf of abelian groups `F` on a site, and let
`V` be an object of the site over which every term `Kʲ` has no cohomology in positive degrees,
for instance because each `Kʲ` is injective, or flasque on a topological space. Then the complex
of sections `K⁰(V) ⟶ K¹(V) ⟶ ⋯` computes the cohomology `Hⁿ(V, F)`: every section `s` of `Kⁿ`
over `V` killed by the differential has a class `[s]` in `Hⁿ(V, F)`, additive in `s`
(`CategoryTheory.Sheaf.H'.resolutionClass_add`, `CategoryTheory.Sheaf.H'.resolutionClass_zero`,
`CategoryTheory.Sheaf.H'.resolutionClass_neg` and `CategoryTheory.Sheaf.H'.resolutionClass_sub`),
every class is of this form
(`CategoryTheory.Sheaf.H'.resolutionClass_surjective`), and `[s] = 0` exactly when `s` is the
image of a section of `Kⁿ⁻¹` over `V`, respectively when `s = 0` in degree `0`
(`CategoryTheory.Sheaf.H'.resolutionClass_succ_eq_zero_iff` and
`CategoryTheory.Sheaf.H'.resolutionClass_zero_eq_zero_iff`). Classes are compatible with
restriction (`CategoryTheory.Sheaf.H'.cohomologyPresheaf_map_resolutionClass`). So when the terms
of `K` are acyclic over every object, the homology of the complex of presheaves `K⁰ ⟶ K¹ ⟶ ⋯` is
the cohomology presheaf `V ↦ Hⁿ(V, F)` (`CategoryTheory.Sheaf.H'.homologyIsoCohomologyPresheaf`).
This is how higher direct images are computed from injective resolutions, and from resolutions of
sheaves of modules, whose injective resolutions are flasque but not injective as abelian
sheaves.

Here `Hⁿ(V, F)` is Mathlib's `CategoryTheory.Sheaf.H'`, the group `Extⁿ(ℤ_V, F)` out of the free
abelian sheaf `ℤ_V` on `V`, and morphisms `ℤ_V ⟶ G` are the sections of `G` over `V`
(`TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv`). So the complex of sections is the complex
`Hom(ℤ_V, K)`, and the statement is the case `P = ℤ_V` of `CochainComplex.extMk`, which computes
`Extⁿ(P, F)` from a resolution of `F` acyclic for `Hom(P, -)` by dimension shifting along the short
exact sequences `0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0` of cycles. In particular, if `Hⁿ⁺¹(V, F) = 0`, then the
complex of sections is exact in degree `n + 1`
(`CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution`), which is how derived functors are
shown to vanish.

## Main declarations

* `CategoryTheory.Sheaf.H'.resolutionClass`: the class in `Hⁿ(V, F)` of a section of `Kⁿ` over `V`
  killed by the differential.
* `CategoryTheory.Sheaf.H'.resolutionClass_surjective`,
  `CategoryTheory.Sheaf.H'.resolutionClass_zero_eq_zero_iff` and
  `CategoryTheory.Sheaf.H'.resolutionClass_succ_eq_zero_iff`: the classes of sections exhaust
  `Hⁿ(V, F)`, and the sections with zero class are exactly the boundaries.
* `CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution`: if `Hⁿ⁺¹(V, F) = 0` and the terms
  of a resolution `K` of `F` are acyclic over `V`, then every cycle of `K(V)` in degree `n + 1` is
  a boundary.
* `CategoryTheory.Sheaf.H'.homologyIsoCohomologyPresheaf`: for a resolution `K` of `F` whose terms
  are acyclic over every object, the homology of the underlying complex of presheaves is the
  cohomology presheaf of `F`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A.
* The Stacks Project, Cohomology of Sheaves, Lemma 20.12.3 (tag 09SY), for flasque resolutions.
-/

public section

open CategoryTheory Limits Opposite Abelian TauCeti.CategoryTheory

universe w v u

namespace CategoryTheory

namespace Sheaf

namespace H'

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
  {F : Sheaf J AddCommGrpCat.{v}} {K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1)) (V : C)
  (hKV : ∀ j k, Subsingleton ((K.X j).H' (k + 1) V))

/-- The class `[s]` in `Hⁿ(V, F)` of a section `s` of `Kⁿ` over `V` killed by the differential,
for a resolution `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯`. It is `CochainComplex.extMk` applied to the morphism
from the free abelian sheaf on `V` corresponding to `s`, transported to `Hⁿ(V, F)` along
`CategoryTheory.Sheaf.H'AddEquivExt`. -/
noncomputable def resolutionClass {n : ℕ} (s : (K.X n).obj.obj (op V))
    (hs : (K.d n (n + 1)).hom.app (op V) s = 0) : F.H' n V :=
  (F.H'AddEquivExt n V).symm <| K.extMk ι hι hι' hK
    ((freeYonedaSheafSectionsEquiv J V (K.X n)).symm s)
    (by rw [freeYonedaSheafSectionsEquiv_symm_naturality_right, hs, map_zero])

/-- `resolutionClass` is `CochainComplex.extMk` applied to the morphism from the free abelian sheaf
on `V` corresponding to the section, transported along `CategoryTheory.Sheaf.H'AddEquivExt`. -/
lemma resolutionClass_def {n : ℕ} (s : (K.X n).obj.obj (op V))
    (hs : (K.d n (n + 1)).hom.app (op V) s = 0) :
    resolutionClass ι hι hι' hK V s hs =
      (F.H'AddEquivExt n V).symm (K.extMk ι hι hι' hK
        ((freeYonedaSheafSectionsEquiv J V (K.X n)).symm s)
        (by rw [freeYonedaSheafSectionsEquiv_symm_naturality_right, hs, map_zero])) :=
  (rfl)

/-- The class of a sum of sections is the sum of their classes. -/
theorem resolutionClass_add {n : ℕ} (s t : (K.X n).obj.obj (op V))
    (hs : (K.d n (n + 1)).hom.app (op V) s = 0) (ht : (K.d n (n + 1)).hom.app (op V) t = 0) :
    resolutionClass ι hι hι' hK V (s + t) (by rw [map_add, hs, ht, add_zero]) =
      resolutionClass ι hι hι' hK V s hs + resolutionClass ι hι hι' hK V t ht := by
  rw [resolutionClass_def, resolutionClass_def, resolutionClass_def, ← map_add, ← K.extMk_add]
  congr 2
  exact map_add _ s t

/-- The zero section has class zero. -/
@[simp]
theorem resolutionClass_zero {n : ℕ} :
    resolutionClass ι hι hι' hK V (0 : (K.X n).obj.obj (op V)) (map_zero _) = 0 := by
  simp [resolutionClass_def]

/-- The class of the negative of a section is the negative of its class. -/
theorem resolutionClass_neg {n : ℕ} (s : (K.X n).obj.obj (op V))
    (hs : (K.d n (n + 1)).hom.app (op V) s = 0) :
    resolutionClass ι hι hι' hK V (-s) (by rw [map_neg, hs, neg_zero]) =
      -resolutionClass ι hι hι' hK V s hs := by
  rw [resolutionClass_def, resolutionClass_def, ← map_neg, ← K.extMk_neg]
  congr 2
  exact map_neg _ s

/-- The class of a difference of sections is the difference of their classes. -/
theorem resolutionClass_sub {n : ℕ} (s t : (K.X n).obj.obj (op V))
    (hs : (K.d n (n + 1)).hom.app (op V) s = 0) (ht : (K.d n (n + 1)).hom.app (op V) t = 0) :
    resolutionClass ι hι hι' hK V (s - t) (by rw [map_sub, hs, ht, sub_zero]) =
      resolutionClass ι hι hι' hK V s hs - resolutionClass ι hι hι' hK V t ht := by
  rw [resolutionClass_def, resolutionClass_def, resolutionClass_def, ← map_sub, ← K.extMk_sub]
  congr 2
  exact map_sub _ s t

include hKV in
/-- **Every class in `Hⁿ(V, F)` is the class of a section** of `Kⁿ` over `V` killed by the
differential, when the terms of the resolution `K` of `F` have no cohomology over `V` in positive
degrees. -/
theorem resolutionClass_surjective {n : ℕ} (x : F.H' n V) :
    ∃ (s : (K.X n).obj.obj (op V)) (hs : (K.d n (n + 1)).hom.app (op V) s = 0),
      resolutionClass ι hι hι' hK V s hs = x := by
  obtain ⟨f, hf, hx⟩ := K.extMk_surjective ι hι hι' hK
    (by simpa only [sheafH'_eq] using hKV) (F.H'AddEquivExt n V x)
  refine ⟨freeYonedaSheafSectionsEquiv J V (K.X n) f,
    by rw [← freeYonedaSheafSectionsEquiv_naturality_right, hf, map_zero], ?_⟩
  rw [resolutionClass_def, AddEquiv.symm_apply_eq, ← hx]
  congr 1
  exact AddEquiv.symm_apply_apply _ f

/-- In degree `0` a section of `K⁰` over `V` killed by the differential has zero class only if it
is zero. -/
theorem resolutionClass_zero_eq_zero_iff (s : (K.X 0).obj.obj (op V))
    (hs : (K.d 0 (0 + 1)).hom.app (op V) s = 0) :
    resolutionClass ι hι hι' hK V s hs = 0 ↔ s = 0 := by
  rw [resolutionClass_def, map_eq_zero_iff _ (F.H'AddEquivExt 0 V).symm.injective,
    CochainComplex.extMk_zero_eq_zero_iff, ← map_eq_zero_iff _
    (freeYonedaSheafSectionsEquiv J V (K.X 0)).injective, AddEquiv.apply_symm_apply]

include hKV in
/-- **A section has zero class exactly when it is a boundary**: for a resolution `K` of `F`
whose terms have no cohomology over `V` in positive degrees, the class in `Hⁿ⁺¹(V, F)` of a
section `s` of `Kⁿ⁺¹` over `V` killed by the differential vanishes exactly when `s` is the image of
a section of `Kⁿ` over `V`. -/
theorem resolutionClass_succ_eq_zero_iff {n : ℕ} (s : (K.X (n + 1)).obj.obj (op V))
    (hs : (K.d (n + 1) (n + 1 + 1)).hom.app (op V) s = 0) :
    resolutionClass ι hι hι' hK V s hs = 0 ↔
      ∃ t : (K.X n).obj.obj (op V), (K.d n (n + 1)).hom.app (op V) t = s := by
  rw [resolutionClass_def, map_eq_zero_iff _ (F.H'AddEquivExt (n + 1) V).symm.injective,
    K.extMk_succ_eq_zero_iff ι hι hι' hK
    (by simpa only [sheafH'_eq] using hKV)]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨freeYonedaSheafSectionsEquiv J V (K.X n) g, ?_⟩,
    fun ⟨t, ht⟩ ↦ ⟨(freeYonedaSheafSectionsEquiv J V (K.X n)).symm t, ?_⟩⟩
  · rw [← freeYonedaSheafSectionsEquiv_naturality_right, hg, AddEquiv.apply_symm_apply]
  · rw [freeYonedaSheafSectionsEquiv_symm_naturality_right, ht]

include hι' hK hKV in
/-- **Exactness of sections of an acyclic resolution**, in the form used to show that derived
functors vanish. Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of a sheaf of abelian groups `F`
whose terms have no cohomology in positive degrees over an object `V` of the site. If
`Hⁿ⁺¹(V, F) = 0`, then every section of `Kⁿ⁺¹` over `V` killed by the differential is the image
of a section of `Kⁿ` over `V`: the complex of sections `K(V)` is exact in degree `n + 1`. -/
theorem exists_d_hom_app_eq_of_resolution (n : ℕ) (hF : Subsingleton (F.H' (n + 1) V))
    (s : (K.X (n + 1)).obj.obj (op V)) (hs : (K.d (n + 1) (n + 2)).hom.app (op V) s = 0) :
    ∃ t : (K.X n).obj.obj (op V), (K.d n (n + 1)).hom.app (op V) t = s :=
  (resolutionClass_succ_eq_zero_iff ι hι hι' hK V hKV s hs).1 (Subsingleton.elim _ _)

/-- **Classes of sections are compatible with restriction**: restricting the class of a section
`s` of `Kⁿ` over `V` along `i : U ⟶ V` gives the class of the restricted section. -/
@[simp]
theorem cohomologyPresheaf_map_resolutionClass {U : C} (i : U ⟶ V) {n : ℕ}
    (s : (K.X n).obj.obj (op V)) (hs : (K.d n (n + 1)).hom.app (op V) s = 0) :
    (F.cohomologyPresheaf n).map i.op (resolutionClass ι hι hι' hK V s hs) =
      resolutionClass ι hι hι' hK U ((K.X n).obj.map i.op s)
        (by rw [NatTrans.naturality_apply, hs, map_zero]) := by
  refine (F.H'AddEquivExt n U).injective ?_
  rw [cohomologyPresheaf_map_apply, resolutionClass_def, resolutionClass_def,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, K.mk₀_comp_extMk]
  congr 1
  apply (freeYonedaSheafSectionsEquiv J U (K.X n)).injective
  rw [freeYonedaSheafSectionsEquiv_naturality_left, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

end

section Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  {F : Sheaf J AddCommGrpCat.{v}} {K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}
  (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1))
  (hKV : ∀ V j k, Subsingleton ((K.X j).H' (k + 1) V)) (n : ℕ)

/-- The complex of presheaves of abelian groups underlying a complex of sheaves. -/
private abbrev sectionsComplex (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) :
    CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  ((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj K

omit [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] in
/-- A cycle in degree `n` of the complex of sections over `U` of a complex of sheaves `K` is a
section of `Kⁿ` over `U` killed by the differential. -/
lemma d_hom_app_iCycles_app {U : Cᵒᵖ}
    (z : ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj K).cycles n).obj
      U) :
    (K.d n (n + 1)).hom.app U
      (((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj K).iCycles n).app
        U z) = 0 := by
  have h := congrArg (fun φ ↦ φ.app U z)
    ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj K).iCycles_d n (n + 1))
  simpa using h

/-- The class in `Hⁿ(U, F)` of a cycle of the complex of sections over `U`. -/
private noncomputable def cyclesToH' (U : Cᵒᵖ) :
    ((sectionsComplex K).cycles n).obj U →+ F.H' n U.unop :=
  AddMonoidHom.mk' (fun z ↦ resolutionClass ι hι hι' hK U.unop
      (((sectionsComplex K).iCycles n).app U z) (d_hom_app_iCycles_app n z))
    (fun z w ↦ by
      simp only [map_add]
      exact resolutionClass_add ι hι hι' hK U.unop _ _ _ _)

private lemma cyclesToH'_naturality {U V : Cᵒᵖ} (g : U ⟶ V)
    (z : ((sectionsComplex K).cycles n).obj U) :
    cyclesToH' ι hι hι' hK n V (((sectionsComplex K).cycles n).map g z) =
      (F.cohomologyPresheaf n).map g (cyclesToH' ι hι hι' hK n U z) := by
  have h := cohomologyPresheaf_map_resolutionClass ι hι hι' hK U.unop g.unop _
    (d_hom_app_iCycles_app n z)
  simp only [Quiver.Hom.op_unop] at h
  simp only [cyclesToH', AddMonoidHom.mk'_apply]
  rw [h]
  congr 1
  exact NatTrans.naturality_apply ((sectionsComplex K).iCycles n) g z

/-- The classes of cycles, as a morphism from the presheaf of cycles to the cohomology presheaf. -/
private noncomputable def cyclesToCohomologyPresheaf :
    (sectionsComplex K).cycles n ⟶ F.cohomologyPresheaf n where
  app U := AddCommGrpCat.ofHom (cyclesToH' ι hι hι' hK n U)
  naturality U V g := by
    ext z
    exact cyclesToH'_naturality ι hι hι' hK n g z

include hKV in
/-- Boundaries have zero class. -/
private lemma toCycles_comp_cyclesToCohomologyPresheaf (i : ℕ) :
    (sectionsComplex K).toCycles i n ≫ cyclesToCohomologyPresheaf ι hι hι' hK n = 0 := by
  by_cases hi : (ComplexShape.up ℕ).Rel i n
  · obtain rfl : i + 1 = n := hi
    ext U x
    refine ((resolutionClass_succ_eq_zero_iff ι hι hι' hK U.unop (hKV U.unop) _
      (d_hom_app_iCycles_app _ _)).2 ⟨x, ?_⟩)
    exact ((sectionsComplex K).iCycles_app_toCycles_app i (i + 1) x).symm
  · rw [(sectionsComplex K).toCycles_eq_zero hi, zero_comp]

/-- The comparison map from the homology of the complex of sections to the cohomology presheaf,
induced by the classes of cycles. -/
private noncomputable def homologyToCohomologyPresheaf :
    (sectionsComplex K).homology n ⟶ F.cohomologyPresheaf n :=
  ((sectionsComplex K).homologyIsCokernel _ n rfl).desc
    (CokernelCofork.ofπ _ (toCycles_comp_cyclesToCohomologyPresheaf ι hι hι' hK hKV n _))

private lemma homologyπ_comp_homologyToCohomologyPresheaf :
    (sectionsComplex K).homologyπ n ≫ homologyToCohomologyPresheaf ι hι hι' hK hKV n =
      cyclesToCohomologyPresheaf ι hι hι' hK n :=
  Cofork.IsColimit.π_desc ((sectionsComplex K).homologyIsCokernel _ n rfl)

private lemma isIso_homologyToCohomologyPresheaf :
    IsIso (homologyToCohomologyPresheaf ι hι hι' hK hKV n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have hπ : Function.Surjective (((sectionsComplex K).homologyπ n).app U) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  have hi : Function.Injective (((sectionsComplex K).iCycles n).app U) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hfac (z : ((sectionsComplex K).cycles n).obj U) :
      (homologyToCohomologyPresheaf ι hι hι' hK hKV n).app U
        (((sectionsComplex K).homologyπ n).app U z) = cyclesToH' ι hι hι' hK n U z := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (homologyπ_comp_homologyToCohomologyPresheaf ι hι hι' hK hKV n) U) z
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    exact h
  refine ⟨(injective_iff_map_eq_zero
    ((homologyToCohomologyPresheaf ι hι hι' hK hKV n).app U).hom).2 ?_, fun x ↦ ?_⟩
  · intro h hh
    obtain ⟨z, rfl⟩ := hπ h
    rw [hfac] at hh
    cases n with
    | zero =>
      rw [cyclesToH', AddMonoidHom.mk'_apply, resolutionClass_zero_eq_zero_iff] at hh
      rw [hi (hh.trans (map_zero _).symm), map_zero]
    | succ p =>
      obtain ⟨t, ht⟩ := (resolutionClass_succ_eq_zero_iff ι hι hι' hK U.unop (hKV U.unop) _
        (d_hom_app_iCycles_app _ z)).1 hh
      have hz : z = ((sectionsComplex K).toCycles p (p + 1)).app U t :=
        hi (by rw [HomologicalComplex.iCycles_app_toCycles_app]; exact ht.symm)
      rw [hz, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        HomologicalComplex.toCycles_comp_homologyπ, NatTrans.app_zero]
      rfl
  · obtain ⟨s, hs, rfl⟩ := resolutionClass_surjective ι hι hι' hK U.unop (hKV U.unop) x
    obtain ⟨z, rfl⟩ := (sectionsComplex K).exists_iCycles_app_eq (n + 1) (by simp) s hs
    exact ⟨((sectionsComplex K).homologyπ n).app U z, hfac z⟩

/-- **The sections of an acyclic resolution compute sheaf cohomology.** For a resolution
`0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` of an abelian sheaf `F` whose terms have no cohomology in positive degrees
over any object of the site, the homology in degree `n` of the complex of presheaves
`K⁰ ⟶ K¹ ⟶ ⋯` is the cohomology presheaf `U ↦ Hⁿ(U, F)`. -/
noncomputable def homologyIsoCohomologyPresheaf :
    (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj K).homology n ≅
      F.cohomologyPresheaf n :=
  haveI := isIso_homologyToCohomologyPresheaf ι hι hι' hK hKV n
  asIso (homologyToCohomologyPresheaf ι hι hι' hK hKV n)

/-- Under `homologyIsoCohomologyPresheaf`, the homology class of a cycle `s ∈ Kⁿ(U)` is its class
`resolutionClass` in `Hⁿ(U, F)`. -/
@[simp]
lemma homologyIsoCohomologyPresheaf_hom_app_homologyπ_apply (U : Cᵒᵖ)
    (z : ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj K).cycles n).obj
      U) :
    (homologyIsoCohomologyPresheaf ι hι hι' hK hKV n).hom.app U
        (((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj K).homologyπ
          n).app U z) =
      resolutionClass ι hι hι' hK U.unop
        (((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj K).iCycles n).app
          U z) (d_hom_app_iCycles_app n z) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (homologyπ_comp_homologyToCohomologyPresheaf ι hι hι' hK hKV n) U) z
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  exact h

end Presheaf

end H'

end Sheaf

end CategoryTheory
