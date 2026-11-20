/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.Geometry.Manifold.Sheaf.Smooth.Restrict

/-!
# Scalar multiplication on sheaves of smooth vector-valued functions

Pointwise multiplication by a global smooth scalar function `g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯` defines a
sheaf endomorphism `TauCeti.smoothSheafAddCommGroup.smulEnd IM V g` of the abelian sheaf
`smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V` of smooth `V`-valued functions on a manifold `M`.

## Main definitions

* `TauCeti.smoothSheafAddCommGroup.smulEnd`: pointwise scalar multiplication of smooth
  vector-valued sections by a global smooth scalar function.

## Main results

* `TauCeti.smoothSheafAddCommGroup.smulEnd_hom_app_apply` and
  `TauCeti.smoothSheafAddCommGroup.smulEnd_hom_app_eq_of_eqOn`: sectionwise pointwise evaluation
  and locality of `smulEnd IM V g`.
* `TauCeti.smoothSheafAddCommGroup.smulEnd_add`,
  `TauCeti.smoothSheafAddCommGroup.smulEnd_zero`,
  `TauCeti.smoothSheafAddCommGroup.smulEnd_sum`, and
  `TauCeti.smoothSheafAddCommGroup.smulEnd_one`: `smulEnd` preserves addition, `0`, finite sums,
  and sends `1` to the identity endomorphism.

## References

* The smooth sheaf definitions are from `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`, by Heather
  Macbeth and Adam Topaz.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

universe u

namespace TauCeti.smoothSheafAddCommGroup

section ScalarField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]

/-- The inclusion of an open subset `W` of `M`, as a smooth map `C^∞⟮IM, W; IM, M⟯`. -/
private def subtypeValMap (W : Opens M) : C^∞⟮IM, W; IM, M⟯ :=
  ⟨Subtype.val, contMDiff_subtypeVal⟩

private theorem subtypeValMap_apply (W : Opens M) (x : W) :
    subtypeValMap IM W x = x.val :=
  rfl

variable (V : Type u) [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Pointwise multiplication on sections over `W` as an additive homomorphism from smooth scalar
functions on `W` to endomorphisms of `(smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)`. -/
private def smulAppHom (W : Opens (TopCat.of M)) :
    C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ →+
      ((smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W) ⟶
        (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)) :=
  (AddCommGrpCat.homAddEquiv
    (M := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))
    (N := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))).symm.toAddMonoidHom.comp
      (Module.toAddMonoidEnd C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ C^∞⟮IM, W; 𝓘(𝕜, V), V⟯).toAddMonoidHom

private theorem smulAppHom_apply (W : Opens (TopCat.of M)) (c : C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯)
    (f : C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) :
    smulAppHom IM V W c f = c • f :=
  rfl

private theorem smulAppHom_map_apply (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯)
    {U₁ U₂ : (Opens (TopCat.of M))ᵒᵖ} (h : U₁ ⟶ U₂) (f : C^∞⟮IM, U₁.unop; 𝓘(𝕜, V), V⟯) :
    smulAppHom IM V U₂.unop (ContMDiffMap.compRightAlgHom 𝕜 𝕜 (subtypeValMap IM U₂.unop) g)
        ((smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.map h f) =
      (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.map h
        (smulAppHom IM V U₁.unop (ContMDiffMap.compRightAlgHom 𝕜 𝕜 (subtypeValMap IM U₁.unop) g)
          f) := by
  rw [map_apply, smulAppHom_apply, smulAppHom_apply, map_apply]
  refine ContMDiffMap.ext fun x ↦ ?_
  simp [subtypeValMap_apply]

private theorem smulAppHom_one (W : Opens (TopCat.of M)) :
    smulAppHom IM V W 1 = 𝟙 ((smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)) :=
  congrArg
    (AddCommGrpCat.homAddEquiv
      (M := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))
      (N := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))).symm
    (map_one (Module.toAddMonoidEnd C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ C^∞⟮IM, W; 𝓘(𝕜, V), V⟯))

/-- Pointwise multiplication by a global smooth scalar function `g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯` as an
endomorphism of `smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V`. -/
def smulEnd (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V ⟶ smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V :=
  ObjectProperty.homMk
    { app U := smulAppHom IM V U.unop
        (ContMDiffMap.compRightAlgHom 𝕜 𝕜 (subtypeValMap IM U.unop) g)
      naturality {U₁ U₂} h := ConcreteCategory.hom_ext _ _ fun f ↦ by
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        exact smulAppHom_map_apply IM V g h f }

private theorem smulEnd_hom_app (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) (W : Opens (TopCat.of M)) :
    (smulEnd IM V g).hom.app (op W) =
      smulAppHom IM V W
        (ContMDiffMap.compRightAlgHom 𝕜 𝕜 (subtypeValMap IM W) g) :=
  rfl

/-- Evaluating `smulEnd IM V g` at a section over `W` multiplies pointwise by `g`. -/
@[simp]
theorem smulEnd_hom_app_apply (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) (W : Opens (TopCat.of M))
    (f : C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) (x : W) :
    @DFunLike.coe (no_index C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) (no_index ↥W) (fun _ ↦ V) _
        (no_index ((smulEnd IM V g).hom.app (op W) f)) x =
      g x.val • f x := by
  rw [smulEnd_hom_app, smulAppHom_apply]
  simp [subtypeValMap_apply]

/-- Two global smooth scalar functions that agree on an open set `W` induce the same action on
sections over `W`. -/
theorem smulEnd_hom_app_eq_of_eqOn {g₁ g₂ : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯} {W : Opens (TopCat.of M)}
    (h : Set.EqOn g₁ g₂ W) :
    (smulEnd IM V g₁).hom.app (op W) = (smulEnd IM V g₂).hom.app (op W) := by
  rw [smulEnd_hom_app, smulEnd_hom_app]
  congr 1
  ext x
  simpa [subtypeValMap_apply] using h x.property

/-- Pointwise multiplication by `g₁ + g₂` is the sum of the corresponding sheaf endomorphisms. -/
theorem smulEnd_add (g₁ g₂ : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smulEnd IM V (g₁ + g₂) = smulEnd IM V g₁ + smulEnd IM V g₂ :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [Sheaf.Hom.add_app, smulEnd_hom_app, map_add, map_add, smulEnd_hom_app, smulEnd_hom_app]

/-- Multiplication by the zero smooth function is the zero sheaf endomorphism. -/
@[simp]
theorem smulEnd_zero :
    smulEnd IM V (0 : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) = 0 :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [smulEnd_hom_app, map_zero, map_zero]
    simp

/-- Pointwise multiplication by a finite sum of smooth scalar functions is the sum of the
corresponding sheaf endomorphisms. -/
theorem smulEnd_sum {ι : Type*} (s : Finset ι) (g : ι → C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smulEnd IM V (∑ i ∈ s, g i) = ∑ i ∈ s, smulEnd IM V (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, smulEnd_add, ih, Finset.sum_insert ha]

/-- Multiplication by the constant smooth function `1` is the identity sheaf endomorphism. -/
@[simp]
theorem smulEnd_one :
    smulEnd IM V (1 : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) = 𝟙 (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V) :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [smulEnd_hom_app, map_one, smulAppHom_one, TopCat.Sheaf.id_app]

end ScalarField

end TauCeti.smoothSheafAddCommGroup
