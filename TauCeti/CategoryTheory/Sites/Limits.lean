/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Limits and the functor induced on sheaves

If a functor `F : A ⥤ B` preserves limits of shape `K`, then so does the induced functor
`sheafCompose J F : Sheaf J A ⥤ Sheaf J B`
(`CategoryTheory.Sheaf.preservesLimitsOfShape_sheafCompose`), since limits of sheaves are computed
on the underlying presheaves (Mathlib's `CategoryTheory.Sites.Limits`).

Sheafifying sectionwise composition also preserves finite limits when the coefficient functor
does (`CategoryTheory.Sheaf.preservesFiniteLimits_composeAndSheafify`), and so does the constant
sheaf functor when sheafification is left exact
(`CategoryTheory.Sheaf.preservesFiniteLimits_constantSheaf`). The constant sheaf functor
preserves all colimits (`CategoryTheory.Sheaf.preservesColimitsOfSize_constantSheaf`).

For sheaves of types, the sections of a binary product `F ⨯ G` over `W` are pairs of sections:
any sections `a` of `F` and `b` of `G` over `W` are the projections of a section of `F ⨯ G`
(`CategoryTheory.Sheaf.exists_fst_eq_snd_eq`). For sheaves of abelian groups, the sections of the
point of a limit fan over `U` are the families of sections of the factors over `U`, through the
projections of the fan (`CategoryTheory.Sheaf.fanSectionsAddEquiv`).
-/

public section

open CategoryTheory Limits Opposite

universe w w' w'' t

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)

/-- If `F` preserves limits of shape `K`, then so does the induced functor on sheaves, since limits
of sheaves are computed on the underlying presheaves. -/
instance preservesLimitsOfShape_sheafCompose {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [J.HasSheafCompose F] (K : Type*) [Category* K] [HasLimitsOfShape K A]
    [PreservesLimitsOfShape K F] :
    PreservesLimitsOfShape K (sheafCompose J F) := by
  -- `sheafCompose J F` is defined as `ObjectProperty.lift` of the composite
  -- `sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F`, so composing it with
  -- `sheafToPresheaf J B` gives that composite definitionally, as in Mathlib's
  -- `CategoryTheory.Sites.Whiskering`.
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) :=
    inferInstanceAs
      (PreservesLimitsOfShape K (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J B)

/-- Sheafifying sectionwise composition with a finite-limit-preserving coefficient functor
preserves finite limits. -/
instance preservesFiniteLimits_composeAndSheafify {A B : Type*} [Category* A] [Category* B]
    [HasFiniteLimits A] (F : A ⥤ B) [PreservesFiniteLimits F] [HasSheafify J B] :
    PreservesFiniteLimits (composeAndSheafify J F) where
  preservesFiniteLimits K _ _ :=
    inferInstanceAs (PreservesLimitsOfShape K
      (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B))

/-- The constant sheaf functor preserves finite limits when sheafification is left exact. -/
instance preservesFiniteLimits_constantSheaf (A : Type*) [Category* A] [HasSheafify J A] :
    PreservesFiniteLimits (constantSheaf J A) :=
  comp_preservesFiniteLimits _ _

/-- The constant sheaf functor preserves all colimits: it is the constant presheaf functor, which
preserves colimits, followed by sheafification, which is a left adjoint. -/
instance preservesColimitsOfSize_constantSheaf (A : Type*) [Category* A] [HasWeakSheafify J A] :
    PreservesColimitsOfSize.{w', w''} (constantSheaf J A) :=
  inferInstanceAs (PreservesColimitsOfSize (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A))

variable {J} in
/-- Sections `a` of `F` and `b` of `G` over `W` are the projections of a section of `F ⨯ G`. -/
theorem exists_fst_eq_snd_eq {F G : Sheaf J (Type w)} {W : C} (a : F.obj.obj (op W))
    (b : G.obj.obj (op W)) : ∃ e : (F ⨯ G).obj.obj (op W),
      (prod.fst : F ⨯ G ⟶ F).hom.app (op W) e = a ∧
        (prod.snd : F ⨯ G ⟶ G).hom.app (op W) e = b := by
  let E := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj (op W)
  let e₀ := (Types.binaryProductIso _ _).inv (a, b)
  refine ⟨(PreservesLimitPair.iso E F G).inv e₀, ?_, ?_⟩
  · exact (ConcreteCategory.congr_hom (PreservesLimitPair.iso_inv_fst E F G) e₀).trans
      (Types.binaryProductIso_inv_comp_fst_apply _ _ _)
  · exact (ConcreteCategory.congr_hom (PreservesLimitPair.iso_inv_snd E F G) e₀).trans
      (Types.binaryProductIso_inv_comp_snd_apply _ _ _)

section fanSections

variable {J} {I : Type w} {A : I → Sheaf J AddCommGrpCat.{max w t}} {c : Fan A}

/-- The sections over `U` of the point of a limit fan `c` of sheaves of abelian groups are the
families of sections of the factors over `U`: a section goes to the family of its images under the
projections of `c`. -/
noncomputable def fanSectionsAddEquiv (hc : IsLimit c) (U : Cᵒᵖ) :
    c.pt.obj.obj U ≃+ ∀ i, (A i).obj.obj U :=
  AddEquiv.ofBijective (AddMonoidHom.pi fun i ↦ ((c.proj i).hom.app U).hom) (by
    -- Evaluation at `U` preserves the limit and the forgetful functor of `AddCommGrpCat` preserves
    -- limits, so the projections are jointly injective, and every family of sections is the image
    -- of the section lifted from the cone on the product of the sections.
    let hU := isLimitOfPreserves (sheafToPresheaf J _ ⋙ (evaluation _ _).obj U) hc
    refine ⟨fun s s' h ↦ Concrete.isLimit_ext _ hU s s' fun ⟨i⟩ ↦ congrFun h i, fun a ↦ ?_⟩
    let P : Cone (Discrete.functor A ⋙ sheafToPresheaf J _ ⋙ (evaluation _ _).obj U) :=
      ⟨AddCommGrpCat.of (∀ i, (A i).obj.obj U),
        Discrete.natTrans fun i ↦ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ i.as)⟩
    exact ⟨hU.lift P a, funext fun i ↦ ConcreteCategory.congr_hom (hU.fac P ⟨i⟩) a⟩)

/-- The components of the family of sections of a section are its projections. -/
@[simp]
lemma fanSectionsAddEquiv_apply (hc : IsLimit c) (U : Cᵒᵖ) (s : c.pt.obj.obj U) (i : I) :
    fanSectionsAddEquiv hc U s i = (c.proj i).hom.app U s :=
  (rfl)

/-- The projections of the section with a given family of sections are the members of the
family. -/
@[simp]
lemma proj_app_fanSectionsAddEquiv_symm (hc : IsLimit c) (U : Cᵒᵖ) (a : ∀ i, (A i).obj.obj U)
    (i : I) : (c.proj i).hom.app U ((fanSectionsAddEquiv hc U).symm a) = a i := by
  rw [← fanSectionsAddEquiv_apply, AddEquiv.apply_symm_apply]

end fanSections

end CategoryTheory.Sheaf
