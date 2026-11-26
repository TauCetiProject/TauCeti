/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Category.Grp.TensorProduct
public import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory

/-!
# Objectwise tensor products of functors to abelian groups

For functors `M, N : C ⥤ AddCommGrpCat`, `CategoryTheory.objectwiseTensor` gives their objectwise
tensor product `M ⊗ N : c ↦ M(c) ⊗[ℤ] N(c)`, as a bifunctor, additive in each variable. Its
action on pure tensors is computed by `CategoryTheory.objectwiseTensor.obj_obj_map_tmul`,
`CategoryTheory.objectwiseTensor.obj_map_app_tmul` and
`CategoryTheory.objectwiseTensor.map_app_app_tmul`, and it commutes with restriction along a
functor `φ : C' ⥤ C` (`CategoryTheory.objectwiseTensor.comp_obj_obj`,
`CategoryTheory.objectwiseTensor.obj_comp_whiskeringLeft` and
`CategoryTheory.objectwiseTensor.flip_obj_comp_whiskeringLeft`).

A functor *has flat values* (`CategoryTheory.Functor.HasFlatValues`) if all its values are flat
`ℤ`-modules, that is, torsion-free abelian groups. This is stable under restriction, and tensoring
with such a functor, on either side, is exact.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Hodge/CupProduct.lean` (declarations `New.Variety.abTensor`,
  `New.Variety.HasFlatValues`); Apache 2.0, Copyright 2026 Anthropic, PBC. The definitions and
  the exactness of tensoring with flat values are adapted from these declarations.
-/

public section

open CategoryTheory Limits TensorProduct

universe w v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The objectwise tensor product over `ℤ` of functors to abelian groups, as a bifunctor:
`(M ⊗ N)(c) = M(c) ⊗[ℤ] N(c)`. -/
@[expose] noncomputable def objectwiseTensor :
    (C ⥤ AddCommGrpCat.{w}) ⥤ (C ⥤ AddCommGrpCat.{w}) ⥤ C ⥤ AddCommGrpCat.{w} :=
  Functor.curryObj
    { obj p :=
        { obj c := AddCommGrpCat.of (p.1.obj c ⊗[ℤ] p.2.obj c)
          map f := AddCommGrpCat.ofHom
            (TensorProduct.map (p.1.map f).hom.toIntLinearMap (p.2.map f).hom.toIntLinearMap)
          map_id _ := AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp
          map_comp _ _ := AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp }
      map f :=
        { app c := AddCommGrpCat.ofHom
            (TensorProduct.map (f.1.app c).hom.toIntLinearMap (f.2.app c).hom.toIntLinearMap)
          naturality _ _ _ := AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp }
      map_id _ := NatTrans.ext <| funext fun _ ↦ AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp
      map_comp _ _ :=
        NatTrans.ext <| funext fun _ ↦ AddCommGrpCat.tensor_hom_ext fun _ _ ↦ by simp }

namespace objectwiseTensor

variable {M M' N N' K : C ⥤ AddCommGrpCat.{w}}

@[simp]
lemma obj_obj_obj (M N : C ⥤ AddCommGrpCat.{w}) (c : C) :
    (((objectwiseTensor C).obj M).obj N).obj c = AddCommGrpCat.of (M.obj c ⊗[ℤ] N.obj c) :=
  (rfl)

/-- Tensoring with a map on the right acts on pure tensors. -/
@[simp]
lemma obj_map_app_tmul (M : C ⥤ AddCommGrpCat.{w}) (β : N ⟶ N') (c : C) (m : M.obj c)
    (n : N.obj c) :
    ((((objectwiseTensor C).obj M).map β).app c)
      (show (((objectwiseTensor C).obj M).obj N).obj c from m ⊗ₜ n) = m ⊗ₜ β.app c n :=
  (rfl)

/-- Tensoring with a map on the left acts on pure tensors. -/
@[simp]
lemma map_app_app_tmul (α : M ⟶ M') (N : C ⥤ AddCommGrpCat.{w}) (c : C) (m : M.obj c)
    (n : N.obj c) :
    ((((objectwiseTensor C).map α).app N).app c)
      (show (((objectwiseTensor C).obj M).obj N).obj c from m ⊗ₜ n) = α.app c m ⊗ₜ n :=
  (rfl)

/-- Two maps out of an objectwise tensor product agree if they agree on pure tensors. -/
lemma hom_ext {f g : ((objectwiseTensor C).obj M).obj N ⟶ K}
    (h : ∀ (c : C) (m : M.obj c) (n : N.obj c),
      f.app c (show (((objectwiseTensor C).obj M).obj N).obj c from m ⊗ₜ n) =
        g.app c (m ⊗ₜ n)) :
    f = g :=
  NatTrans.ext (funext fun c ↦ AddCommGrpCat.tensor_hom_ext (h c))

/-- The two ways of tensoring a pair of maps agree. -/
lemma map_app_comp_map (α : M ⟶ M') (β : N ⟶ N') :
    ((objectwiseTensor C).map α).app N ≫ ((objectwiseTensor C).obj M').map β =
      ((objectwiseTensor C).obj M).map β ≫ ((objectwiseTensor C).map α).app N' :=
  (((objectwiseTensor C).map α).naturality β).symm

/-- The objectwise tensor product acts on a morphism `f : c ⟶ c'` by `M.map f ⊗ N.map f`. -/
@[simp]
lemma obj_obj_map_tmul (M N : C ⥤ AddCommGrpCat.{w}) {c c' : C} (f : c ⟶ c') (m : M.obj c)
    (n : N.obj c) :
    (((objectwiseTensor C).obj M).obj N).map f
        (show (((objectwiseTensor C).obj M).obj N).obj c from m ⊗ₜ n) =
      M.map f m ⊗ₜ N.map f n :=
  (rfl)

section Restriction

variable {C' : Type u'} [Category.{v'} C'] (φ : C' ⥤ C)

/-- Restricting an objectwise tensor product along `φ` is the objectwise tensor product of the
restrictions. -/
lemma comp_obj_obj (M N : C ⥤ AddCommGrpCat.{w}) :
    φ ⋙ ((objectwiseTensor C).obj M).obj N =
      ((objectwiseTensor C').obj (φ ⋙ M)).obj (φ ⋙ N) :=
  rfl

/-- Restricting `M ⊗ β` along `φ` is `(φ ⋙ M) ⊗ φ.whiskerLeft β`. -/
lemma whiskerLeft_obj_map (M : C ⥤ AddCommGrpCat.{w}) (β : N ⟶ N') :
    φ.whiskerLeft (((objectwiseTensor C).obj M).map β) =
      ((objectwiseTensor C').obj (φ ⋙ M)).map (φ.whiskerLeft β) :=
  rfl

/-- Restricting `α ⊗ N` along `φ` is `φ.whiskerLeft α ⊗ (φ ⋙ N)`. -/
lemma whiskerLeft_map_app (α : M ⟶ M') (N : C ⥤ AddCommGrpCat.{w}) :
    φ.whiskerLeft (((objectwiseTensor C).map α).app N) =
      ((objectwiseTensor C').map (φ.whiskerLeft α)).app (φ ⋙ N) :=
  rfl

/-- Tensoring on the left with `M` and then restricting along `φ` is restricting along `φ` and then
tensoring on the left with `φ ⋙ M`. -/
lemma obj_comp_whiskeringLeft (M : C ⥤ AddCommGrpCat.{w}) :
    (objectwiseTensor C).obj M ⋙ (Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ =
      (Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ ⋙
        (objectwiseTensor C').obj (φ ⋙ M) :=
  rfl

/-- Tensoring on the right with `N` and then restricting along `φ` is restricting along `φ` and
then tensoring on the right with `φ ⋙ N`. -/
lemma flip_obj_comp_whiskeringLeft (N : C ⥤ AddCommGrpCat.{w}) :
    (objectwiseTensor C).flip.obj N ⋙ (Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ =
      (Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ ⋙
        (objectwiseTensor C').flip.obj (φ ⋙ N) :=
  rfl

end Restriction

-- In both instances `change` unfolds `objectwiseTensor` on a pure tensor to `TensorProduct.map`,
-- that is, to the form of `obj_map_app_tmul` and `map_app_app_tmul`; `simp` does not rewrite with
-- these lemmas here because the sum of maps is applied before the tensor is evaluated.
instance (M : C ⥤ AddCommGrpCat.{w}) : ((objectwiseTensor C).obj M).Additive :=
  ⟨fun {_ _ f g} ↦ hom_ext fun c m n ↦ by
    change m ⊗ₜ[ℤ] (f + g).app c n = m ⊗ₜ[ℤ] f.app c n + m ⊗ₜ[ℤ] g.app c n
    simp [tmul_add]⟩

instance (N : C ⥤ AddCommGrpCat.{w}) : ((objectwiseTensor C).flip.obj N).Additive :=
  ⟨fun {_ _ f g} ↦ hom_ext fun c m n ↦ by
    change (f + g).app c m ⊗ₜ[ℤ] n = f.app c m ⊗ₜ[ℤ] n + g.app c m ⊗ₜ[ℤ] n
    simp [add_tmul]⟩

end objectwiseTensor

/-- A functor to abelian groups *has flat values* if each of its values is a flat `ℤ`-module. -/
class Functor.HasFlatValues (F : C ⥤ AddCommGrpCat.{w}) : Prop where
  /-- Each value of `F` is a flat `ℤ`-module. -/
  flat (c : C) : Module.Flat ℤ (F.obj c)

instance {C' : Type u'} [Category.{v'} C'] (φ : C' ⥤ C) (F : C ⥤ AddCommGrpCat.{w})
    [F.HasFlatValues] : (φ ⋙ F).HasFlatValues :=
  ⟨fun c ↦ Functor.HasFlatValues.flat (F := F) (φ.obj c)⟩

instance {C' : Type u'} [Category.{v'} C'] (φ : C' ⥤ C) (F : C ⥤ AddCommGrpCat.{w})
    [F.HasFlatValues] :
    (((Functor.whiskeringLeft C' C AddCommGrpCat.{w}).obj φ).obj F).HasFlatValues :=
  inferInstanceAs (φ ⋙ F).HasFlatValues

/-- Tensoring on the left with a functor of flat values is exact. -/
private lemma exact_tensorLeft (M : C ⥤ AddCommGrpCat.{w}) [M.HasFlatValues] :
    PreservesFiniteLimits ((objectwiseTensor C).obj M) ∧
      PreservesFiniteColimits ((objectwiseTensor C).obj M) := by
  refine Functor.preservesFiniteLimits_and_preservesFiniteColimits_of_function_exact _
    fun S hS c ↦ ?_
  have := Functor.HasFlatValues.flat (F := M) c
  exact Module.Flat.lTensor_exact (M.obj c)
    ((ShortComplex.exact_iff_forall_function_exact S).1 hS c)

/-- Tensoring on the right with a functor of flat values is exact. -/
private lemma exact_tensorRight (N : C ⥤ AddCommGrpCat.{w}) [N.HasFlatValues] :
    PreservesFiniteLimits ((objectwiseTensor C).flip.obj N) ∧
      PreservesFiniteColimits ((objectwiseTensor C).flip.obj N) := by
  refine Functor.preservesFiniteLimits_and_preservesFiniteColimits_of_function_exact _
    fun S hS c ↦ ?_
  have := Functor.HasFlatValues.flat (F := N) c
  exact Module.Flat.rTensor_exact (N.obj c)
    ((ShortComplex.exact_iff_forall_function_exact S).1 hS c)

instance (M : C ⥤ AddCommGrpCat.{w}) [M.HasFlatValues] :
    PreservesFiniteLimits ((objectwiseTensor C).obj M) := (exact_tensorLeft M).1

instance (M : C ⥤ AddCommGrpCat.{w}) [M.HasFlatValues] :
    PreservesFiniteColimits ((objectwiseTensor C).obj M) := (exact_tensorLeft M).2

instance (N : C ⥤ AddCommGrpCat.{w}) [N.HasFlatValues] :
    PreservesFiniteLimits ((objectwiseTensor C).flip.obj N) := (exact_tensorRight N).1

instance (N : C ⥤ AddCommGrpCat.{w}) [N.HasFlatValues] :
    PreservesFiniteColimits ((objectwiseTensor C).flip.obj N) := (exact_tensorRight N).2

end CategoryTheory
