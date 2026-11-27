/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import TauCeti.CategoryTheory.Sites.ShortExact

/-!
# Exact sequences of abelian sheaves lift kernel sections locally

Let `F₁ ⟶ F₂ ⟶ F₃` be an exact sequence of sheaves of abelian groups on a site `(C, J)` admitting
sheafification. A section of `F₂` over `U` killed by `F₂ ⟶ F₃` comes from `F₁` locally: the
sieve of morphisms `V ⟶ U` along which its restriction lies in the image of `F₁` covers `U`.
The proof factors `F₁ ⟶ F₂` through the kernel of `F₂ ⟶ F₃`, which is computed on sections, and
uses that the epimorphism `F₁ ⟶ ker (F₂ ⟶ F₃)` of sheaves is locally surjective.

## Main declarations

* `CategoryTheory.ShortComplex.Exact.imageSieve_mem`: for an exact short complex of abelian
  sheaves, the image sieve of a section of the middle term killed by the second map is covering.
-/

public section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Exact sequences of sheaves lift kernel sections locally.** For an exact short complex
`F₁ ⟶ F₂ ⟶ F₃` of sheaves of abelian groups, a section `x` of `F₂` over `U` with image zero in
`F₃` lifts to `F₁` locally on `U`: its image sieve under `F₁ ⟶ F₂` is a covering sieve. -/
theorem Exact.imageSieve_mem {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.Exact)
    {U : C} (x : S.X₂.obj.obj (Opposite.op U)) (hx : S.g.hom.app (Opposite.op U) x = 0) :
    Presheaf.imageSieve S.f.hom x ∈ J U := by
  have : Epi S.toCycles := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.toCycles)).mpr inferInstance
  -- The kernel of `S.g` is computed on sections, so `x` is a section of `S.cycles`.
  obtain ⟨y, rfl⟩ := exists_app_eq_of_isLimit (S := ShortComplex.mk S.iCycles S.g S.iCycles_g)
    S.cyclesIsKernel (Opposite.op U) x hx
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J S.toCycles.hom y)
  rintro V f ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [← S.toCycles_i, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, hz]
  exact NatTrans.naturality_apply S.iCycles.hom (Quiver.Hom.op f) y

end CategoryTheory.ShortComplex
