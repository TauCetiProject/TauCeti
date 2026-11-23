/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The sheaf of linear morphisms

For a presheaf of modules and a sheaf of modules over a sheaf of rings, local linear morphisms
from the first to the second form a sheaf of sets; only the target has to be a sheaf. This is
the gluing input for the dual sheaf: take the target to be the structure sheaf.
The construction works over any site and does not require commutativity of the rings.

Over an object `U`, a section is an additive morphism between the restrictions of the source
and the target to the slice over `U`, whose components are linear over the restricted structure
sheaf. Restriction pulls such morphisms back along arrows. Linearity is local because
equality of target sections can be checked on a covering sieve, so compatible local linear
morphisms glue uniquely.

The resulting sheaf `PresheafOfModules.linearHom` has local sections over `U` equivalent to
morphisms between the restricted presheaves of modules (`PresheafOfModules.linearHomObjEquiv`).
When the source is a sheaf as well, they are equivalent to morphisms between the restricted
module sheaves, and global sections are equivalent to morphisms of the original module sheaves.
The declarations `SheafOfModules.linearHomObjEquiv`, `SheafOfModules.linearHomSectionsEquiv`,
and `SheafOfModules.linearHomObjEquiv_map_app` expose these identifications and their behavior
under restriction. They support dot notation directly, for example `M.val.linearHom N` and
`M.linearHomObjEquiv N U`.

## Sources

The construction builds on Mathlib's `presheafHom`. Its gluing proof uses the sheaf result
`Presheaf.IsSheaf.hom` together with the subfunctor criterion `Subfunctor.isSheaf_iff`.

This file constructs the underlying sheaf of sets; it does not equip it with a module
structure or identify it with a categorical internal Hom.
-/

public section

open CategoryTheory Opposite

noncomputable section

namespace PresheafOfModules

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : PresheafOfModules.{w'} R.obj) (N : SheafOfModules.{w'} R)

/-- The subpresheaf of additive local morphisms that commute with scalar multiplication. -/
private def linearHomSubfunctor : Subfunctor (presheafHom M.presheaf N.val.presheaf) where
  obj U := {φ | ∀ (V : Over U.unop) (r : R.obj.obj (op V.left)) (m : M.obj (op V.left)),
    φ.app (op V) (r • m) =
      (r • · : N.val.obj (op V.left) → N.val.obj (op V.left)) (φ.app (op V) m)}
  map f _ h V r m := h ((Over.map f.unop).obj V) r m

/-- Linearity of a local additive morphism can be checked on a covering sieve. -/
private theorem mem_linearHomSubfunctor_of_cover {U : Cᵒᵖ}
    (φ : (presheafHom M.presheaf N.val.presheaf).obj U)
    (S : Sieve U.unop) (hS : S ∈ J U.unop)
    (hφ : ∀ ⦃V⦄ (f : V ⟶ U.unop), S f →
      (presheafHom M.presheaf N.val.presheaf).map f.op φ ∈
        (linearHomSubfunctor M N).obj (op V)) :
    φ ∈ (linearHomSubfunctor M N).obj U := by
  intro V r m
  have hN := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf J N.val.presheaf (CategoryTheory.forget _) N.isSheaf)
  refine (hN _ (J.pullback_stable V.hom hS)).isSeparatedFor.ext fun W f hf ↦ ?_
  -- Naturality along `f`, seen as a slice morphism to `V` from the object where `hφ` applies.
  have hnat (s : M.obj (op V.left)) :
      φ.app (op ((Over.map (f ≫ V.hom)).obj (Over.mk (𝟙 W)))) (M.presheaf.map f.op s) =
        N.val.presheaf.map f.op (φ.app (op V) s) :=
    congrArg (fun g ↦ g s)
      (φ.naturality (Over.homMk f : (Over.map (f ≫ V.hom)).obj (Over.mk (𝟙 W)) ⟶ V).op)
  exact (hnat (r • m)).symm.trans <|
    (congrArg (φ.app _) (M.map_smul f.op r m)).trans <|
      (hφ (f ≫ V.hom) hf (Over.mk (𝟙 W)) _ _).trans <|
        (congrArg (fun s : N.val.obj (op W) ↦ R.obj.map f.op r • s) (hnat m)).trans
          (N.val.map_smul f.op r _).symm

/-- Local linear morphisms satisfy the sheaf condition. -/
private theorem isSheaf_linearHomSubfunctor :
    Presheaf.IsSheaf J (linearHomSubfunctor M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact ((linearHomSubfunctor M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).1 (N.isSheaf.hom M.presheaf))).2
    fun _ φ hφ ↦ mem_linearHomSubfunctor_of_cover M N φ _ hφ fun _ _ hf ↦ hf

/-- The sheaf of sets of local linear morphisms from a presheaf of modules to a sheaf of
modules. Only the target has to be a sheaf. -/
def linearHom : Sheaf J (Type (max u v w')) where
  obj := (linearHomSubfunctor M N).toFunctor
  property := isSheaf_linearHomSubfunctor M N

/-- Sections over `U` of the sheaf of local linear morphisms from a presheaf of modules are
precisely the morphisms between the restrictions to the slice over `U`. -/
def linearHomObjEquiv (U : C) :
    (M.linearHom N).obj.obj (op U) ≃
      ((pushforward₀ (Over.forget U) R.obj).obj M ⟶
        (pushforward₀ (Over.forget U) R.obj).obj N.val) where
  toFun φ := homMk φ.val fun V ↦ φ.property V.unop
  invFun φ := ⟨(toPresheaf _).map φ, fun V r m ↦ (φ.app (op V)).hom.map_smul r m⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Evaluate a local linear Hom section at a slice object and a source section. -/
def linearHomApp (U : C) (φ : (M.linearHom N).obj.obj (op U))
    (V : Over U) (m : M.obj (op V.left)) : N.val.obj (op V.left) :=
  φ.val.app (op V) m

-- This is not a simp lemma: `Over.forget_obj` rewrites the dependent module structure in its
-- left-hand side.
/-- The morphism associated to a local linear Hom section evaluates to the section's component. -/
theorem linearHomObjEquiv_app (U : C)
    (φ : (M.linearHom N).obj.obj (op U)) (V : Over U) (m : M.obj (op V.left)) :
    ((M.linearHomObjEquiv N U φ).app (op V)) m = M.linearHomApp N U φ V m :=
  (rfl)

/-- The local linear Hom section associated to a morphism evaluates to the morphism's component. -/
@[simp]
theorem linearHomObjEquiv_symm_app (U : C)
    (φ : (pushforward₀ (Over.forget U) R.obj).obj M ⟶
      (pushforward₀ (Over.forget U) R.obj).obj N.val)
    (V : Over U) (m : M.obj (op V.left)) :
    M.linearHomApp N U ((M.linearHomObjEquiv N U).symm φ) V m = φ.app (op V) m :=
  (rfl)

-- This is not a simp lemma: `Over.forget_obj` and `Over.mk_left` rewrite the slice object
-- `Over.mk g` inside the implicit arguments of the coercion on its left-hand side.
/-- Restriction of a local linear morphism restricts its component linear maps. -/
theorem linearHomObjEquiv_map_app {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (φ : (M.linearHom N).obj.obj (op U)) (m : M.obj (op W)) :
    ((M.linearHomObjEquiv N V ((M.linearHom N).obj.map f.op φ)).app (op (Over.mk g))) m =
      ((M.linearHomObjEquiv N U φ).app (op (Over.mk (g ≫ f)))) m :=
  ConcreteCategory.congr_hom (presheafHom_map_app g f (g ≫ f) rfl φ.val) m

end PresheafOfModules

namespace SheafOfModules

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M N : SheafOfModules.{w'} R)

/-- Sections of the linear Hom sheaf over an object are precisely morphisms between the
restricted sheaves of modules.

The lemmas `linearHomObjEquiv_app` and `linearHomObjEquiv_symm_app` give the componentwise
evaluation formulas in both directions. -/
def linearHomObjEquiv (U : C) :
    (M.val.linearHom N).obj.obj (op U) ≃ (M.over U ⟶ N.over U) :=
  (M.val.linearHomObjEquiv N U).trans
    ((fullyFaithfulForget _).homEquiv (X := M.over U) (Y := N.over U)).symm

/-- The morphism associated to a local linear Hom section evaluates to the section's component. -/
theorem linearHomObjEquiv_app (U : C)
    (φ : (M.val.linearHom N).obj.obj (op U)) (V : Over U) (m : M.val.obj (op V.left)) :
    ((linearHomObjEquiv M N U φ).val.app (op V)) m = M.val.linearHomApp N U φ V m :=
  (rfl)

/-- The local linear Hom section associated to a morphism evaluates to the morphism's component. -/
@[simp]
theorem linearHomObjEquiv_symm_app (U : C) (φ : M.over U ⟶ N.over U)
    (V : Over U) (m : M.val.obj (op V.left)) :
    M.val.linearHomApp N U ((linearHomObjEquiv M N U).symm φ) V m = φ.val.app (op V) m :=
  (rfl)

/-- Restriction of a Hom section restricts its component linear maps. -/
@[simp]
theorem linearHomObjEquiv_map_app {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (φ : (M.val.linearHom N).obj.obj (op U)) (m : M.val.obj (op W)) :
    ((linearHomObjEquiv M N V ((M.val.linearHom N).obj.map f.op φ)).val.app
      (op (Over.mk g))) m =
        ((linearHomObjEquiv M N U φ).val.app (op (Over.mk (g ≫ f)))) m :=
  M.val.linearHomObjEquiv_map_app N f g φ m

/-- The local section attached to the restriction `φ.over U` is the section of `presheafHom`
that Mathlib's `presheafHomSectionsEquiv` attaches to `φ`, read over `U`. -/
private theorem val_linearHomObjEquiv_symm_over (φ : M ⟶ N) (U : Cᵒᵖ) :
    ((linearHomObjEquiv M N U.unop).symm (φ.over U.unop)).val =
      ((presheafHomSectionsEquiv M.val.presheaf N.val.presheaf).symm
        ((PresheafOfModules.toPresheaf _).map φ.val)).val U :=
  rfl

/-- Global sections of the linear Hom sheaf are morphisms of sheaves of modules. -/
def linearHomSectionsEquiv : (M.val.linearHom N).obj.sections ≃ (M ⟶ N) where
  toFun s := ⟨PresheafOfModules.homMk
    (presheafHomSectionsEquiv M.val.presheaf N.val.presheaf
      ⟨fun U ↦ (s.val U).val, fun f ↦ congrArg Subtype.val (s.property f)⟩)
    (fun U ↦ (s.val U).property (Over.mk (𝟙 U.unop)))⟩
  invFun φ := ⟨fun U ↦ (linearHomObjEquiv M N U.unop).symm (φ.over U.unop), fun {U V} f ↦
    Subtype.ext <|
      (congrArg ((presheafHom M.val.presheaf N.val.presheaf).map f)
        (val_linearHomObjEquiv_symm_over M N φ U)).trans <|
        (((presheafHomSectionsEquiv M.val.presheaf N.val.presheaf).symm
          ((PresheafOfModules.toPresheaf _).map φ.val)).property f).trans
          (val_linearHomObjEquiv_symm_over M N φ V).symm⟩
  left_inv s := Subtype.ext <| funext fun U ↦ Subtype.ext <|
    (val_linearHomObjEquiv_symm_over M N _ U).trans <| congrArg (·.val U)
      ((presheafHomSectionsEquiv M.val.presheaf N.val.presheaf).left_inv
        ⟨fun U ↦ (s.val U).val, fun f ↦ congrArg Subtype.val (s.property f)⟩)
  right_inv φ := by
    ext U m
    -- `toFun` reads the section attached to `φ` at the identity slice; by the identification
    -- lemma that section is Mathlib's, so this is Mathlib's inverse law.
    exact (congrArg (fun ψ ↦ ψ.app (op (Over.mk (𝟙 U.unop))) m)
      (val_linearHomObjEquiv_symm_over M N φ U)).trans <| congrArg (fun ψ ↦ ψ.app U m)
        ((presheafHomSectionsEquiv M.val.presheaf N.val.presheaf).right_inv
          ((PresheafOfModules.toPresheaf _).map φ.val))

/-- The morphism associated to a global Hom section is read at the identity of each slice. -/
@[simp]
theorem linearHomSectionsEquiv_app (s : (M.val.linearHom N).obj.sections) (U : Cᵒᵖ)
    (m : M.val.obj U) :
    ((linearHomSectionsEquiv M N s).val.app U) m =
      ((linearHomObjEquiv M N U.unop (s.val U)).val.app
        (op (Over.mk (𝟙 U.unop)))) m :=
  (rfl)

/-- The global Hom section associated to a morphism restricts to that morphism on each slice. -/
@[simp]
theorem linearHomSectionsEquiv_symm_apply (φ : M ⟶ N) (U : Cᵒᵖ) :
    ((linearHomSectionsEquiv M N).symm φ).val U =
      (linearHomObjEquiv M N U.unop).symm (φ.over U.unop) :=
  (rfl)

end SheafOfModules

namespace SheafOfModules

section OpenCoverGluing

universe u₀ v₀ w₀ w₁

variable {X : TopCat.{u₀}} {R : TopCat.Sheaf RingCat.{w₀} X}
  (M N : SheafOfModules.{w₁} R) {ι : Type v₀} (U : ι → TopologicalSpace.Opens X)
  (hU : ⨆ i, U i = ⊤) (φ : ∀ i, M.over (U i) ⟶ N.over (U i))
  (hφ : ∀ i j (V : TopologicalSpace.Opens X) (hi : V ≤ U i) (hj : V ≤ U j)
    (m : M.val.obj (op V)),
      (φ i).val.app (op (Over.mk (homOfLE hi))) m =
        (φ j).val.app (op (Over.mk (homOfLE hj))) m)

private def localHomSection (i : ι) : (M.val.linearHom N).obj.obj (op (U i)) :=
  (M.linearHomObjEquiv N (U i)).symm (φ i)

include hφ in
private lemma localHomSection_compatible :
    TopCat.Presheaf.IsCompatible (M.val.linearHom N).obj U
      (localHomSection M N U φ) := by
  intro i j
  apply (M.linearHomObjEquiv N (U i ⊓ U j)).injective
  ext V m
  rcases V with ⟨V, ⟨⟨⟩⟩, hV⟩
  -- Unpacking the slice object is the remaining definitional reduction from the public
  -- Hom-section evaluation law to its component at `Over.mk hV`.
  change (M.linearHomObjEquiv N (U i ⊓ U j)
      ((M.val.linearHom N).obj.map (homOfLE inf_le_left).op
        (localHomSection M N U φ i))).val.app (op (Over.mk hV)) m = _
  refine (SheafOfModules.linearHomObjEquiv_map_app M N (homOfLE inf_le_left)
    hV (localHomSection M N U φ i) m).trans ?_
  refine Eq.trans ?_ (SheafOfModules.linearHomObjEquiv_map_app M N
    (homOfLE inf_le_right) hV (localHomSection M N U φ j) m).symm
  have hi : hV ≫ homOfLE inf_le_left =
      homOfLE (hV.le.trans inf_le_left) := Subsingleton.elim _ _
  have hj : hV ≫ homOfLE inf_le_right =
      homOfLE (hV.le.trans inf_le_right) := Subsingleton.elim _ _
  rw [hi, hj]
  simp only [localHomSection, Equiv.apply_symm_apply]
  -- Each restricted module has the same value on `V`; only its slice index differs.
  change (φ i).val.app (op (Over.mk (homOfLE (hV.le.trans inf_le_left)))) m =
    (φ j).val.app (op (Over.mk (homOfLE (hV.le.trans inf_le_right)))) m
  exact hφ i j V (hV.le.trans inf_le_left) (hV.le.trans inf_le_right) m

include hU hφ in
private lemma gluingExists : ∃! s : (M.val.linearHom N).obj.obj (op ⊤),
    ∀ i, (M.val.linearHom N).obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op s =
      localHomSection M N U φ i :=
  TopCat.Sheaf.existsUnique_gluing' (M.val.linearHom N) U ⊤
    (fun _ ↦ homOfLE le_top) (fun x _ ↦ by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩)
    (localHomSection M N U φ) (localHomSection_compatible M N U φ hφ)

private def gluedHomTop : (M.val.linearHom N).obj.obj (op ⊤) :=
  Classical.choose (gluingExists M N U hU φ hφ)

/-- Glue compatible morphisms of module sheaves on an open cover. -/
def glueOfOpenCover : M ⟶ N :=
  M.linearHomSectionsEquiv N
    ⟨fun V ↦ (M.val.linearHom N).obj.map V.unop.leTop.op (gluedHomTop M N U hU φ hφ),
      fun {V W} f ↦ by
        rw [← Functor.map_comp_apply]
        rfl⟩

private lemma gluedHomTop_restrict (i : ι) :
    (M.val.linearHom N).obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op
      (gluedHomTop M N U hU φ hφ) = localHomSection M N U φ i := by
  exact (Classical.choose_spec (gluingExists M N U hU φ hφ)).1 i

/-- The glued morphism agrees with each local morphism on every smaller open. -/
lemma glueOfOpenCover_app (i : ι) (V : TopologicalSpace.Opens X) (hi : V ≤ U i)
    (m : M.val.obj (op V)) :
    (glueOfOpenCover M N U hU φ hφ).val.app (op V) m =
      (φ i).val.app (op (Over.mk (homOfLE hi))) m := by
  have hsec : (M.val.linearHom N).obj.map V.leTop.op (gluedHomTop M N U hU φ hφ) =
      (M.val.linearHom N).obj.map (homOfLE hi).op (localHomSection M N U φ i) := by
    rw [← gluedHomTop_restrict M N U hU φ hφ i, ← Functor.map_comp_apply]
    rfl
  rw [glueOfOpenCover, linearHomSectionsEquiv_app]
  dsimp only
  rw [hsec]
  exact (SheafOfModules.linearHomObjEquiv_map_app M N (homOfLE hi) (𝟙 V)
    (localHomSection M N U φ i) m).trans (by
      simp only [localHomSection, Equiv.apply_symm_apply]
      -- The two slice objects differ by the identity-composition presentation of their arrow.
      change (φ i).val.app (op (Over.mk (𝟙 V ≫ homOfLE hi))) m = _
      erw [Category.id_comp])

/-- A morphism agreeing with the prescribed local morphisms is the glued morphism. -/
lemma glueOfOpenCover_unique (ψ : M ⟶ N)
    (hψ : ∀ i (V : TopologicalSpace.Opens X) (hi : V ≤ U i) (m : M.val.obj (op V)),
      ψ.val.app (op V) m = (φ i).val.app (op (Over.mk (homOfLE hi))) m) :
    ψ = glueOfOpenCover M N U hU φ hφ := by
  have htop : ((M.linearHomSectionsEquiv N).symm ψ).val (op ⊤) =
      gluedHomTop M N U hU φ hφ := by
    apply (Classical.choose_spec (gluingExists M N U hU φ hφ)).2
    intro i
    apply (M.linearHomObjEquiv N (U i)).injective
    ext V m
    rcases V with ⟨V, ⟨⟨⟩⟩, hV⟩
    -- The inverse global equivalence attaches the restriction of `ψ` to the top slice.
    -- Its restriction along `hV` is evaluated through the public local Hom map law.
    change (M.linearHomObjEquiv N (U i)
        ((M.val.linearHom N).obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op
          (((M.linearHomSectionsEquiv N).symm ψ).val (op ⊤)))).val.app
            (op (Over.mk hV)) m = _
    refine (linearHomObjEquiv_map_app M N (homOfLE (show U i ≤ ⊤ from le_top))
      hV (((M.linearHomSectionsEquiv N).symm ψ).val (op ⊤)) m).trans ?_
    simp only [linearHomSectionsEquiv_symm_apply, localHomSection, Equiv.apply_symm_apply]
    -- Restriction of a module morphism retains its component at the underlying open `V`.
    change ψ.val.app (op V) m = (φ i).val.app (op (Over.mk hV)) m
    exact hψ i V hV.le m
  apply (M.linearHomSectionsEquiv N).symm.injective
  apply Subtype.ext
  funext V
  calc
    ((M.linearHomSectionsEquiv N).symm ψ).val V =
        (M.val.linearHom N).obj.map V.unop.leTop.op
          (((M.linearHomSectionsEquiv N).symm ψ).val (op ⊤)) :=
      (((M.linearHomSectionsEquiv N).symm ψ).property V.unop.leTop.op).symm
    _ = (M.val.linearHom N).obj.map V.unop.leTop.op (gluedHomTop M N U hU φ hφ) :=
      congrArg _ htop
    _ = ((M.linearHomSectionsEquiv N).symm (glueOfOpenCover M N U hU φ hφ)).val V := by
      rw [glueOfOpenCover, Equiv.symm_apply_apply]

end OpenCoverGluing

end SheafOfModules
