/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.AcyclicResolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

/-!
# Sections of acyclic resolutions compute sheaf cohomology

Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of a sheaf of abelian groups `F` on a site, and let
`V` be an object of the site over which every term `Kʲ` has no cohomology in positive degrees,
for instance because each `Kʲ` is injective, or flasque on a topological space. Then the complex
of sections `K⁰(V) ⟶ K¹(V) ⟶ ⋯` computes the cohomology `Hⁿ(V, F)`: every section `s` of `Kⁿ`
over `V` killed by the differential has a class `[s]` in `Hⁿ(V, F)`, additive in `s`
(`CategoryTheory.Sheaf.H'.resolutionClass_add`), every class is of this form
(`CategoryTheory.Sheaf.H'.resolutionClass_surjective`), and `[s] = 0` exactly when `s` is the
image of a section of `Kⁿ⁻¹` over `V`, respectively when `s = 0` in degree `0`
(`CategoryTheory.Sheaf.H'.resolutionClass_succ_eq_zero_iff` and
`CategoryTheory.Sheaf.H'.resolutionClass_zero_eq_zero_iff`).

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

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
  {F : Sheaf J AddCommGrpCat.{v}} {K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1)) (V : C)
  (hKV : ∀ j k, Subsingleton ((K.X j).H' (k + 1) V))

omit [HasExt (Sheaf J AddCommGrpCat)] in
/-- A section of `Kⁿ` over `V` is killed by the differential exactly when the corresponding
morphism from the free abelian sheaf on `V` is. -/
private lemma symm_comp_d_eq_zero_iff {n m : ℕ} (s : (K.X n).obj.obj (op V)) :
    (freeYonedaSheafSectionsEquiv J V (K.X n)).symm s ≫ K.d n m = 0 ↔
      (K.d n m).hom.app (op V) s = 0 := by
  rw [← (freeYonedaSheafSectionsEquiv J V (K.X m)).injective.eq_iff,
    freeYonedaSheafSectionsEquiv_naturality_right, AddEquiv.apply_symm_apply, map_zero]

/-- The class `[s]` in `Hⁿ(V, F)` of a section `s` of `Kⁿ` over `V` killed by the differential,
for a resolution `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯`. It is `CochainComplex.extMk` applied to the morphism
from the free abelian sheaf on `V` corresponding to `s`. -/
noncomputable def resolutionClass {n : ℕ} (s : (K.X n).obj.obj (op V))
    (hs : (K.d n (n + 1)).hom.app (op V) s = 0) :
    Ext.{w} ((freeYonedaSheafFunctor J).obj V) F n :=
  K.extMk ι hι hι' hK ((freeYonedaSheafSectionsEquiv J V (K.X n)).symm s)
    ((symm_comp_d_eq_zero_iff V s).2 hs)

/-- The class of a sum of sections is the sum of their classes. -/
theorem resolutionClass_add {n : ℕ} (s t : (K.X n).obj.obj (op V))
    (hs : (K.d n (n + 1)).hom.app (op V) s = 0) (ht : (K.d n (n + 1)).hom.app (op V) t = 0) :
    resolutionClass ι hι hι' hK V (s + t) (by rw [map_add, hs, ht, add_zero]) =
      resolutionClass ι hι hι' hK V s hs + resolutionClass ι hι hι' hK V t ht := by
  rw [resolutionClass, resolutionClass, resolutionClass, ← K.extMk_add]
  congr 1
  exact map_add _ s t

include hKV in
/-- **Every class in `Hⁿ(V, F)` is the class of a section** of `Kⁿ` over `V` killed by the
differential, when the terms of the resolution `K` of `F` have no cohomology over `V` in positive
degrees. -/
theorem resolutionClass_surjective {n : ℕ}
    (x : Ext.{w} ((freeYonedaSheafFunctor J).obj V) F n) :
    ∃ (s : (K.X n).obj.obj (op V)) (hs : (K.d n (n + 1)).hom.app (op V) s = 0),
      resolutionClass ι hι hι' hK V s hs = x := by
  obtain ⟨f, hf, rfl⟩ := K.extMk_surjective ι hι hι' hK
    (by simpa only [sheafH'_eq] using hKV) x
  refine ⟨freeYonedaSheafSectionsEquiv J V (K.X n) f,
    (symm_comp_d_eq_zero_iff V _).1 (by rwa [AddEquiv.symm_apply_apply]), ?_⟩
  rw [resolutionClass]
  congr 1
  exact AddEquiv.symm_apply_apply _ f

/-- In degree `0` a section of `K⁰` over `V` killed by the differential has zero class only if it
is zero. -/
theorem resolutionClass_zero_eq_zero_iff (s : (K.X 0).obj.obj (op V))
    (hs : (K.d 0 (0 + 1)).hom.app (op V) s = 0) :
    resolutionClass ι hι hι' hK V s hs = 0 ↔ s = 0 := by
  rw [resolutionClass, CochainComplex.extMk_zero_eq_zero_iff, ← map_eq_zero_iff _
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
  rw [resolutionClass, K.extMk_succ_eq_zero_iff ι hι hι' hK
    (by simpa only [sheafH'_eq] using hKV)]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨freeYonedaSheafSectionsEquiv J V (K.X n) g, ?_⟩,
    fun ⟨t, ht⟩ ↦ ⟨(freeYonedaSheafSectionsEquiv J V (K.X n)).symm t, ?_⟩⟩
  · rw [← freeYonedaSheafSectionsEquiv_naturality_right, hg, AddEquiv.apply_symm_apply]
  · rw [← (freeYonedaSheafSectionsEquiv J V (K.X (n + 1))).injective.eq_iff,
      freeYonedaSheafSectionsEquiv_naturality_right, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, ht]

include hι' hK hKV in
/-- **Exactness of sections of an acyclic resolution**, in the form used to show that derived
functors vanish. Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of a sheaf of abelian groups `F`
whose terms have no cohomology in positive degrees over an object `V` of the site. If
`Hⁿ⁺¹(V, F) = 0`, then every section of `Kⁿ⁺¹` over `V` killed by the differential is the image
of a section of `Kⁿ` over `V`: the complex of sections `K(V)` is exact in degree `n + 1`. -/
theorem exists_d_hom_app_eq_of_resolution (n : ℕ) (hF : Subsingleton (F.H' (n + 1) V))
    (s : (K.X (n + 1)).obj.obj (op V)) (hs : (K.d (n + 1) (n + 2)).hom.app (op V) s = 0) :
    ∃ t : (K.X n).obj.obj (op V), (K.d n (n + 1)).hom.app (op V) t = s :=
  have : Subsingleton (Ext.{w} ((freeYonedaSheafFunctor J).obj V) F (n + 1)) := by
    simpa only [sheafH'_eq] using hF
  (resolutionClass_succ_eq_zero_iff ι hι hι' hK V hKV s hs).1 (Subsingleton.elim _ _)

end H'

end Sheaf

end CategoryTheory
