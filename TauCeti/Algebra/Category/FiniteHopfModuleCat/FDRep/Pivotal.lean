/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.GroupLike
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.FDRep
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Pivotal
public import TauCeti.Algebra.MonoidAlgebra.Antipode
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Basic
public import TauCeti.RepresentationTheory.FDRep.Pivotal

/-!
# Duals and the trivial pivot of finite-dimensional modules over a group algebra

For a field `k` and a group `G`, the category `FiniteHopfModuleCat k k[G]` of finite-dimensional
modules over the group algebra carries the rigid and pivotal structures that every Hopf algebra
with a suitable group-like element provides. Its right dual of `M` is the contragredient, on which
`k[G]` acts through the antipode `S(g) = g⁻¹`, and its left dual is the contragredient through
`S⁻¹`, which here is `S` again since `S² = id`. Because `S² = id` is conjugation by the group-like
unit `1`, the double dual comparison `m ↦ (φ ↦ φ(m))` is a pivotal structure, the *trivial
pivot*.

The category `FDRep k G` of finite-dimensional representations is rigid with the algebraic dual
on both sides, through Mathlib's rigid structures on `Action` over `FGModuleCat k` (the left duals
of `FGModuleCat k` come from Tau Ceti's `FGModuleCat.leftRigidCategory`). It carries the canonical
pivotal structure `TauCeti.symmetricPivotalCategory` of a symmetric rigid category, whose pivotal
isomorphism is the double dual evaluation map. This file shows that the monoidal
equivalence `equivalenceFDRep k G` matches these structures with the ones above.

* The functor `ofFDRep k G` carries right duals to right duals: its comparison
  `(ofFDRep k G).mapRightDualIso V` between the image of the dual and the dual of the image is the
  identity on functionals.
* It carries left duals to the inverse-antipode contragredients: the comparison
  `(ofFDRep k G).mapLeftDualIso V` is also the identity on functionals.
* It is a pivotal functor from the canonical pivotal structure of `FDRep k G` to the trivial
  pivot.

In particular `ofFDRep k G` preserves left and right traces and dimensions
(`CategoryTheory.Functor.rightTrace_map` and its companions).

## Main declarations

* `TauCeti.FiniteHopfModuleCat.monoidAlgebraRigidCategory`: the rigid structure on
  finite-dimensional `k[G]`-modules.
* `TauCeti.FiniteHopfModuleCat.monoidAlgebraPivotalCategory`: the trivial pivot, described by
  `TauCeti.FiniteHopfModuleCat.dualEquiv_monoidAlgebra_pivotalIsoApp_hom_apply`.
* `FDRep.dualEquiv_ofFDRep_mapRightDualIso_hom_apply` and
  `FDRep.leftDualEquiv_ofFDRep_mapLeftDualIso_hom_apply`: the comparisons of right and left duals
  are the identity on functionals.
* `TauCeti.FiniteHopfModuleCat.isPivotal_ofFDRep`: the functor `ofFDRep k G` is pivotal.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs 205, Sections 2.10 and 4.7, for duals and pivotal structures of modules over a Hopf
  algebra and of representations of a group.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonoidAlgebra

open TauCeti TauCeti.BialgebraModule

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]

namespace TauCeti.FiniteHopfModuleCat

variable (k G)

/-- The rigid structure on finite-dimensional modules over a group algebra: the right dual of a
module is its contragredient through the antipode, and its left dual is its contragredient
through the inverse of the antipode. -/
abbrev monoidAlgebraRigidCategory : RigidCategory (FiniteHopfModuleCat k k[G]) :=
  rigidCategory MonoidAlgebra.antipode_bijective

/-- The trivial pivot on finite-dimensional modules over a group algebra: the pivotal structure
given by the group-like unit `1`, whose components are the double dual comparisons
`m ↦ (φ ↦ φ(m))`. -/
abbrev monoidAlgebraPivotalCategory :
    letI := monoidAlgebraRigidCategory k G
    PivotalCategory (FiniteHopfModuleCat k k[G]) :=
  pivotalCategory (g := 1) (fun a => by simp) IsGroupLikeElem.one

variable {k G}

/-- The trivial pivot sends `m` to the functional `φ ↦ φ(m)` on the contragredient. -/
theorem dualEquiv_monoidAlgebra_pivotalIsoApp_hom_apply (M : FiniteHopfModuleCat k k[G]) (m : M)
    (φ : (Mᘁ : FiniteHopfModuleCat k k[G])) :
    letI := monoidAlgebraRigidCategory k G
    letI := monoidAlgebraPivotalCategory k G
    dualEquiv k k[G] (Mᘁ : FiniteHopfModuleCat k k[G]) ((pivotalIsoApp M).hom.hom.hom m) φ =
      dualEquiv k k[G] M φ m := by
  rw [pivotalIsoApp_pivotalCategory, dualEquiv_unitEvalIso_hom_apply, Units.val_one, one_smul]

end TauCeti.FiniteHopfModuleCat

namespace FDRep

open TauCeti (FiniteHopfModuleCat)
open TauCeti.FiniteHopfModuleCat

/-- A pairing `A ⊗ B ⟶ 𝟙_` of representations, carried to `k[G]`-modules by `ofFDRep k G` and its
tensor and unit comparisons, is the same bilinear map on underlying vector spaces. -/
private theorem trivialEquiv_μ_comp_map_comp_η_tmul {A B : FDRep k G} (f : A ⊗ B ⟶ 𝟙_ (FDRep k G))
    (a : (ofFDRep k G).obj A) (b : (ofFDRep k G).obj B) :
    trivialEquiv k k[G]
        ((μ (ofFDRep k G) A B ≫ (ofFDRep k G).map f ≫ η (ofFDRep k G)).hom.hom (tmul k k[G] a b)) =
      f.hom.hom.hom (ofFDRepLinearEquiv A a ⊗ₜ ofFDRepLinearEquiv B b) := by
  simp only [hom_hom_comp, LinearMap.comp_apply, ofFDRep_η_hom_hom, ofFDRep_μ_hom_hom,
    LinearEquiv.coe_coe, ofFDRepUnitEquiv_symm_apply, LinearEquiv.apply_symm_apply]
  rw [ofFDRepLinearEquiv_ofFDRep_map_apply, ofFDRepLinearEquiv_ofFDRepTensorEquiv_tmul]

/-- The comparison `(ofFDRep k G).obj Vᘁ ≅ ((ofFDRep k G).obj V)ᘁ` between the image of the dual
of a representation and the contragredient of its image is the identity on functionals. -/
theorem dualEquiv_ofFDRep_mapRightDualIso_hom_apply (V : FDRep k G)
    (φ : (ofFDRep k G).obj Vᘁ) (x : (ofFDRep k G).obj V) :
    dualEquiv k k[G] ((ofFDRep k G).obj V) (((ofFDRep k G).mapRightDualIso V).hom.hom.hom φ) x =
      (ofFDRepLinearEquiv Vᘁ φ).toFun (ofFDRepLinearEquiv V x) := by
  -- Evaluate the characterizing identity of the comparison at `φ ⊗ x`.
  have h := LinearMap.congr_fun (congrArg (fun u => u.hom.hom)
    ((ofFDRep k G).mapRightDualIso_hom_whiskerRight_evaluation V)) (tmul k k[G] φ x)
  apply_fun trivialEquiv k k[G] at h
  rw [trivialEquiv_μ_comp_map_comp_η_tmul, Action.evaluation_hom, hom_hom_comp,
    LinearMap.comp_apply, whiskerRight_tmul, evaluation_tmul, LinearEquiv.apply_symm_apply] at h
  exact h.trans (contractLeft_apply _ _)

/-- The comparison `(ofFDRep k G).obj (ᘁV) ≅ ᘁ((ofFDRep k G).obj V)` between the image of the left
dual of a representation and the inverse-antipode contragredient of its image is the identity on
functionals. -/
theorem leftDualEquiv_ofFDRep_mapLeftDualIso_hom_apply (V : FDRep k G)
    (φ : (ofFDRep k G).obj (ᘁV)) (x : (ofFDRep k G).obj V) :
    letI := monoidAlgebraRigidCategory k G
    leftDualEquiv k k[G] ((ofFDRep k G).obj V) MonoidAlgebra.antipode_bijective
        (((ofFDRep k G).mapLeftDualIso V).hom.hom.hom φ) x =
      (ofFDRepLinearEquiv (ᘁV) φ).toFun (ofFDRepLinearEquiv V x) := by
  let := monoidAlgebraRigidCategory k G
  -- As for right duals, evaluate the characterizing identity of the comparison at `x ⊗ φ`.
  have h := LinearMap.congr_fun (congrArg (fun u => u.hom.hom)
    ((ofFDRep k G).whiskerLeft_mapLeftDualIso_hom_evaluation V)) (tmul k k[G] x φ)
  apply_fun trivialEquiv k k[G] at h
  rw [trivialEquiv_μ_comp_map_comp_η_tmul, Action.leftEvaluation_hom, hom_hom_comp,
    LinearMap.comp_apply, whiskerLeft_tmul, rigidCategory_evaluation, leftDualEvaluation_tmul,
    LinearEquiv.apply_symm_apply] at h
  exact h.trans (FGModuleCat.leftEvaluation_apply _ _ _)

end FDRep

namespace TauCeti.FiniteHopfModuleCat

open FDRep (ofFDRepLinearEquiv dualEquiv_ofFDRep_mapRightDualIso_hom_apply)

/-- **The equivalence of `FDRep k G` with finite-dimensional `k[G]`-modules is pivotal.** The
functor `ofFDRep k G` carries the canonical pivotal structure of the symmetric rigid category
`FDRep k G`, the double dual evaluation, to the trivial pivot of `k[G]`-modules. -/
theorem isPivotal_ofFDRep :
    letI := monoidAlgebraRigidCategory k G
    letI := monoidAlgebraPivotalCategory k G
    (ofFDRep k G).IsPivotal := by
  let := monoidAlgebraRigidCategory k G
  let := monoidAlgebraPivotalCategory k G
  refine Functor.IsPivotal.mk' fun V => ?_
  -- Both sides send `x` to the functional `φ ↦ φ(x)` on the image of `Vᘁ`.
  ext x
  apply (dualEquiv k k[G] _).injective
  ext φ
  simp only [hom_hom_comp, LinearMap.comp_apply]
  rw [dualEquiv_ofFDRep_mapRightDualIso_hom_apply, dualEquiv_rightAdjointMate_apply,
    dualEquiv_monoidAlgebra_pivotalIsoApp_hom_apply, dualEquiv_ofFDRep_mapRightDualIso_hom_apply,
    ofFDRepLinearEquiv_ofFDRep_map_apply, pivotalIsoApp_eq_drinfeldIso,
    FDRep.drinfeldIso_hom_hom_hom_hom]
  -- The double dual evaluation map applies the functional to the vector. The carrier of the
  -- `FDRep` dual `Vᘁ` is definitionally `Module.Dual k V`, but not syntactically.
  exact Module.Dual.eval_apply (R := k) (M := V.V) _ _

end TauCeti.FiniteHopfModuleCat
