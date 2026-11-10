/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange

import TauCeti.RingTheory.GradedAlgebra.DegreeOne

/-!
# Sections of the pullback of a graded quasicoherent algebra

Let `g : Y ⟶ X` be a morphism of schemes, `A = ⨁ₙ Aₙ` a graded quasicoherent algebra on `X` and
`U` an open of `X`. Pulling back sections along `g` in each degree is a homomorphism of graded
rings

`⨁ n, Γ(Aₙ, U) → ⨁ n, Γ((g^* A)ₙ, g⁻¹ U)`

from the graded ring of sections of `A` (`CategoryTheory.CommMon.gradedSectionsGrading`) to that
of its pullback `g^* A` (`GradedQuasicoherentAlgebra.pullback`), over `g.app U`. It is
constructed in `GradedAlgebra/BaseChange.lean`. Here we restrict these canonical maps to an
arbitrary smaller open of the source, as needed for affine charts of relative `Proj`.

Restricting to an open `V ⊆ g⁻¹ U` gives `pullbackGradedSectionsLE`, over `g.appLE U V`. If `U`
and `V` are affine, pulling back the sections of each quasicoherent `Aₙ` from `U` to `V` is the
extension of scalars along `Γ(X, U) → Γ(Y, V)` (the square `g ≫ 𝟙 = 𝟙 ≫ g` case of
`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear`), so the graded ring of sections of `g^* A`
over `V` is the base change of that of `A` over `U`. By
`AlgebraicGeometry.Proj.isPullback_map_of_isBaseChange`, `Proj` of the sections of `g^* A` over
`V` is then the fibre product of `Proj` of the sections of `A` over `U` with `Spec Γ(Y, V)` over
`Spec Γ(X, U)`. This is the affine-local input for base change of relative `Proj` along an
arbitrary morphism of the base. Since the pulled-back sections span the sections over `V`
(`span_range_pullbackGradedSectionsLE`), generation in degree one, finite type and finiteness in
degree zero pass from `U` to `V`.

## Main declarations

* `GradedQuasicoherentAlgebra.pullbackGradedSectionsLE` and `pullbackGradedSectionsLEGradedHom`:
  the same followed by restriction to an open `V ⊆ g⁻¹ U`;
* `GradedQuasicoherentAlgebra.isPushout_pullbackGradedSectionsLE`: the pushout property of
  graded section rings over affine opens;
* `GradedQuasicoherentAlgebra.isPullback_proj_map_pullbackGradedSectionsLEGradedHom`: for affine
  `U` and `V`, `Proj` of the pulled-back graded sections over `V` is the base change of `Proj` of
  the graded sections over `U` along `Spec Γ(Y, V) ⟶ Spec Γ(X, U)`;
* `GradedQuasicoherentAlgebra.adjoin_gradedSectionsGrading_pullback_eq_top`,
  `finiteType_pullback_sections` and `finite_pullback_sections_zero`: generation in degree one,
  finite type and finiteness of the degree-zero part pass from the sections over `U` to the
  pulled-back sections over `V`.

## References

* The Stacks Project, [Section 27.15, Relative Proj](https://stacks.math.columbia.edu/tag/01NS).
* The formalization is adapted from `Modules/Quasicoherent/GradedAlgebra/PullbackSections.lean`
  on [the Tau Ceti lookahead branch](https://github.com/roed-math/TauCeti-w2-fresh/tree/efa6fc8f3735429eb3c763c1304db4db05ff5394).
-/

public section

open CategoryTheory MonoidalCategory CategoryTheory.Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry
open scoped _root_.DirectSum TensorProduct

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (A : GradedQuasicoherentAlgebra X) (U : X.Opens)

section Restriction

variable {g U} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U)

/-- **Pullback of graded sections to an open `V ⊆ g⁻¹ U`.** Pulling back sections along `g` and
restricting them to `V`, as a ring homomorphism from the graded ring of sections of `A` over `U`
to the graded ring of sections of `g^* A` over `V`. -/
def pullbackGradedSectionsLE :
    (⨁ n, Γ(A.obj.X n, U)) →+* ⨁ n, Γ(((pullback g).obj A).obj.X n, V) :=
  (((pullback g).obj A).obj.restrictGradedSections (homOfLE hV)).comp
    (pullbackGradedSections g A U)

/-- The pullback of a homogeneous section to `V` is the restriction of its pullback, in the same
degree. -/
@[simp]
lemma pullbackGradedSectionsLE_of (n : ℕ) (x : Γ(A.obj.X n, U)) :
    pullbackGradedSectionsLE A hV (DirectSum.of _ n x) =
      DirectSum.of _ n ((((pullback g).obj A).obj.X n).presheaf.map (homOfLE hV).op
        ((eqToHom (pullback_obj_obj_X g A n).symm).app (g ⁻¹ᵁ U)
          (g.pullbackSections (A.obj.X n) U x))) := by
  simp [pullbackGradedSectionsLE]

/-- Pullback of graded sections to `V` is compatible with the structure maps, along
`g.appLE U V hV : Γ(X, U) → Γ(Y, V)`. -/
@[simp]
lemma pullbackGradedSectionsLE_algebraMap (r : Γ(X, U)) :
    pullbackGradedSectionsLE A hV (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) (g.appLE U V hV r) := by
  rw [pullbackGradedSectionsLE, RingHom.comp_apply, pullbackGradedSections_algebraMap,
    CommMon.restrictGradedSections_algebraMap]
  rfl

/-- Pullback of graded sections to `V` as a graded ring homomorphism. Its underlying ring
homomorphism is `pullbackGradedSectionsLE`. -/
def pullbackGradedSectionsLEGradedHom :
    A.obj.gradedSectionsGrading U →+*ᵍ ((pullback g).obj A).obj.gradedSectionsGrading V :=
  (((pullback g).obj A).obj.restrictGradedSectionsGradedHom (homOfLE hV)).comp
    (pullbackGradedSectionsGradedHom g A U)

/-- The graded pullback of sections to `V` is `pullbackGradedSectionsLE`. -/
@[simp]
lemma pullbackGradedSectionsLEGradedHom_apply (x : ⨁ n, Γ(A.obj.X n, U)) :
    pullbackGradedSectionsLEGradedHom A hV x = pullbackGradedSectionsLE A hV x := by
  rw [pullbackGradedSectionsLEGradedHom, GradedRingHom.comp_apply,
    CommMon.restrictGradedSectionsGradedHom_apply, pullbackGradedSectionsGradedHom_apply]
  rfl

/-- Pulling back graded sections to `V` and restricting them to `W ⊆ V` is pulling them back to
`W`. -/
lemma restrictGradedSections_comp_pullbackGradedSectionsLE {W : Y.Opens} (i : W ⟶ V) :
    (((pullback g).obj A).obj.restrictGradedSections i).comp (pullbackGradedSectionsLE A hV) =
      pullbackGradedSectionsLE A ((leOfHom i).trans hV) := by
  rw [pullbackGradedSectionsLE, pullbackGradedSectionsLE, ← RingHom.comp_assoc,
    ← CommMon.restrictGradedSections_comp]
  rfl

/-- Restricting graded sections from `U` to `U' ⊆ U` and pulling them back to `V ⊆ g⁻¹ U'` is
pulling them back from `U` to `V`. -/
lemma pullbackGradedSectionsLE_comp_restrictGradedSections {U' : X.Opens} (j : U' ⟶ U)
    (hV' : V ≤ g ⁻¹ᵁ U') :
    (pullbackGradedSectionsLE A hV').comp (A.obj.restrictGradedSections j) =
      pullbackGradedSectionsLE A hV := by
  refine DirectSum.ringHom_ext fun n x ↦ ?_
  simp only [RingHom.comp_apply, CommMon.restrictGradedSections_of, pullbackGradedSectionsLE_of]
  congr 1
  -- both sides are the image of the pulled-back section to `V` under the identification
  -- `(g^* A)ₙ = g^* Aₙ`, which commutes with restriction
  refine (PresheafOfModules.naturality_apply (eqToHom (pullback_obj_obj_X g A n).symm).val
    (homOfLE hV').op _).symm.trans (Eq.trans ?_ (PresheafOfModules.naturality_apply
      (eqToHom (pullback_obj_obj_X g A n).symm).val (homOfLE hV).op _))
  congr 1
  exact (Scheme.Hom.pullbackSectionsLE_apply ..).symm.trans
    ((Scheme.Hom.pullbackSectionsLE_map g _ U V hV j hV' x).trans
      (Scheme.Hom.pullbackSectionsLE_apply ..))

end Restriction

variable {g U} in
/-- Over affine opens `U` and `V ⊆ g⁻¹ U`, the graded ring of sections of `g^* A` over `V`
is the pushout of the graded ring of sections of `A` over `U` along `g.appLE U V`. -/
theorem isPushout_pullbackGradedSectionsLE (hU : IsAffineOpen U) {V : Y.Opens}
    (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U) :
    IsPushout (g.appLE U V hV)
      (CommRingCat.ofHom (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U))))
      (CommRingCat.ofHom (algebraMap Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V))))
      (CommRingCat.ofHom (pullbackGradedSectionsLE A hV)) := by
  let : Algebra Γ(X, U) Γ(Y, V) := (g.appLE U V hV).hom.toAlgebra
  let : Algebra Γ(X, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    ((algebraMap Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V))).comp
      (g.appLE U V hV).hom).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    .of_algebraMap_eq' rfl
  have hfR (r : Γ(X, U)) : pullbackGradedSectionsLE A hV
      (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(X, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) r :=
    pullbackGradedSectionsLE_algebraMap A hV r
  -- The degree-`n` component of `g^* A` is `g^* Aₙ`, up to an `eqToHom`.
  let eqv (n : ℕ) : Γ((Scheme.Modules.pullback g).obj (A.obj.X n), V) ≃ₗ[Γ(Y, V)]
      Γ(((pullback g).obj A).obj.X n, V) :=
    ((Scheme.Modules.sectionsFunctor V).mapIso
      (eqToIso (pullback_obj_obj_X g A n).symm)).toLinearEquiv
  choose e he using fun n ↦ Scheme.Hom.exists_pullbackSectionsLE_equiv g (A.obj.X n) hU hV' hV
  have hf : IsBaseChange Γ(Y, V)
      (AlgHom.mk (pullbackGradedSectionsLE A hV) hfR).toLinearMap := by
    refine IsBaseChange.of_equiv ((TensorProduct.directSumRight _ _ _ _).trans
      (DirectSum.congrLinearEquiv fun n ↦ (e n).trans (eqv n))) fun x ↦ ?_
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n m =>
      rw [← DirectSum.lof_eq_of Γ(X, U), LinearEquiv.trans_apply,
        TensorProduct.directSumRight_tmul_lof, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
      erw [LinearEquiv.trans_apply, he]
      rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
      -- The linear map of the bundled algebra homomorphism evaluates by the ring map.
      change _ = pullbackGradedSectionsLE A hV (DirectSum.of _ n m)
      rw [pullbackGradedSectionsLE_of]
      congr 1
      -- Restriction commutes with the identification `(g^* A)ₙ = g^* Aₙ`.
      rw [Scheme.Hom.pullbackSectionsLE_apply]
      exact congr($((eqToHom (pullback_obj_obj_X g A n).symm).mapPresheaf.naturality
        (homOfLE hV).op) (g.pullbackSections (A.obj.X n) U m))
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]
  let := (pullbackGradedSectionsLE A hV).toAlgebra
  have : IsScalarTower Γ(X, U) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    .of_algebraMap_eq fun r ↦ (pullbackGradedSectionsLE_algebraMap A hV r).symm
  have hpush : Algebra.IsPushout Γ(X, U) Γ(Y, V) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) := ⟨hf⟩
  exact CommRingCat.isPushout_iff_isPushout.mpr hpush

variable {g U} {V : Y.Opens}

/-- The irrelevant-ideal condition, cartesian Proj square, and spanning statement obtained
from the pushout of graded section rings. -/
private theorem exists_isPullback_proj_map (hU : IsAffineOpen U) (hV' : IsAffineOpen V)
    (hV : V ≤ g ⁻¹ᵁ U) :
    ∃ h : HomogeneousIdeal.irrelevant (((pullback g).obj A).obj.gradedSectionsGrading V) ≤
        (HomogeneousIdeal.irrelevant (A.obj.gradedSectionsGrading U)).map
          (pullbackGradedSectionsLEGradedHom A hV),
      IsPullback (Proj.map (pullbackGradedSectionsLEGradedHom A hV) h)
        (Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V))
        (Proj.toSpecCoeff (A.obj.gradedSectionsGrading U)) (Spec.map (g.appLE U V hV)) ∧
      Submodule.span Γ(Y, V) (Set.range (pullbackGradedSectionsLE A hV)) = ⊤ := by
  let : Algebra Γ(X, U) Γ(Y, V) := (g.appLE U V hV).hom.toAlgebra
  let := (pullbackGradedSectionsLE A hV).toAlgebra
  let : Algebra Γ(X, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    ((algebraMap Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V))).comp
      (g.appLE U V hV).hom).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    .of_algebraMap_eq fun r ↦ (pullbackGradedSectionsLE_algebraMap A hV r).symm
  have hfR (r : Γ(X, U)) : pullbackGradedSectionsLEGradedHom A hV
      (algebraMap Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) r) =
      algebraMap Γ(X, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) r :=
    (pullbackGradedSectionsLEGradedHom_apply A hV _).trans
      (pullbackGradedSectionsLE_algebraMap A hV r)
  have hpush : Algebra.IsPushout Γ(X, U) Γ(Y, V) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_pullbackGradedSectionsLE A hU hV' hV)
  have he : (IsScalarTower.toAlgHom Γ(X, U) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback g).obj A).obj.X n, V))).toLinearMap =
      (AlgHom.mk (pullbackGradedSectionsLEGradedHom A hV).toRingHom hfR).toLinearMap :=
    LinearMap.ext fun x ↦ (pullbackGradedSectionsLEGradedHom_apply A hV x).symm
  have hf := hpush.out
  have hgraded := he ▸ hf
  refine ⟨_, Proj.isPullback_map_of_isBaseChange _ _ hfR hgraded,
    Submodule.eq_top_iff'.mpr fun w ↦ ?_⟩
  induction w using hf.inductionOn with
  | tmul a => exact Submodule.subset_span ⟨a, rfl⟩
  | smul r x hx => exact Submodule.smul_mem _ r hx
  | add x y hx hy => exact add_mem hx hy

/-- Over affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`, the irrelevant ideal of the
pulled-back graded sections over `V` is generated by the pullback of the irrelevant ideal of the
graded sections of `A` over `U`. This is the condition for `Proj.map` along
`pullbackGradedSectionsLEGradedHom`. -/
theorem irrelevant_le_map_pullbackGradedSectionsLEGradedHom (hU : IsAffineOpen U)
    (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U) :
    HomogeneousIdeal.irrelevant (((pullback g).obj A).obj.gradedSectionsGrading V) ≤
      (HomogeneousIdeal.irrelevant (A.obj.gradedSectionsGrading U)).map
        (pullbackGradedSectionsLEGradedHom A hV) :=
  (exists_isPullback_proj_map A hU hV' hV).1

/-- **`Proj` of graded sections commutes with pullback.** For a morphism of schemes `g : Y ⟶ X`,
affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`, and a graded quasicoherent algebra `A` on `X`,
the square

`Proj (⨁ n, Γ((g^* A)ₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))`, `Spec Γ(Y, V) ⟶ Spec Γ(X, U)`

formed by `Proj.map` of the pullback of graded sections and the coefficient projections is
cartesian. This is the affine-local step of base change for relative `Proj`. -/
theorem isPullback_proj_map_pullbackGradedSectionsLEGradedHom (hU : IsAffineOpen U)
    (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U) :
    IsPullback (Proj.map (pullbackGradedSectionsLEGradedHom A hV)
        (irrelevant_le_map_pullbackGradedSectionsLEGradedHom A hU hV' hV))
      (Proj.toSpecCoeff (((pullback g).obj A).obj.gradedSectionsGrading V))
      (Proj.toSpecCoeff (A.obj.gradedSectionsGrading U)) (Spec.map (g.appLE U V hV)) :=
  (exists_isPullback_proj_map A hU hV' hV).2.1

/-- Over affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`, the graded sections of `g^* A` over `V`
are spanned over `Γ(Y, V)` by the pullbacks of the graded sections of `A` over `U`. -/
theorem span_range_pullbackGradedSectionsLE (hU : IsAffineOpen U) (hV' : IsAffineOpen V)
    (hV : V ≤ g ⁻¹ᵁ U) :
    Submodule.span Γ(Y, V) (Set.range (pullbackGradedSectionsLE A hV)) = ⊤ :=
  (exists_isPullback_proj_map A hU hV' hV).2.2

/-- **Generation in degree one pulls back**: over affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`,
if the graded sections of `A` over `U` are generated by the degree-one sections over the
degree-zero sections, so are the graded sections of `g^* A` over `V`. -/
theorem adjoin_gradedSectionsGrading_pullback_eq_top (hU : IsAffineOpen U)
    (hV' : IsAffineOpen V) (hV : V ≤ g ⁻¹ᵁ U)
    (h : Algebra.adjoin (A.obj.gradedSectionsGrading U 0)
      (A.obj.gradedSectionsGrading U 1 : Set (⨁ n, Γ(A.obj.X n, U))) = ⊤) :
    Algebra.adjoin (((pullback g).obj A).obj.gradedSectionsGrading V 0)
      (((pullback g).obj A).obj.gradedSectionsGrading V 1 :
        Set (⨁ n, Γ(((pullback g).obj A).obj.X n, V))) = ⊤ := by
  let : Algebra Γ(X, U) Γ(Y, V) := (g.appLE U V hV).hom.toAlgebra
  let := (pullbackGradedSectionsLE A hV).toAlgebra
  let : Algebra Γ(X, U) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    ((algebraMap Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V))).comp
      (g.appLE U V hV).hom).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, U) (⨁ n, Γ(A.obj.X n, U))
      (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    .of_algebraMap_eq fun r ↦ (pullbackGradedSectionsLE_algebraMap A hV r).symm
  have : Algebra.IsPushout Γ(X, U) (⨁ n, Γ(A.obj.X n, U)) Γ(Y, V)
      (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) :=
    (CommRingCat.isPushout_iff_isPushout.mp (isPushout_pullbackGradedSectionsLE A hU hV' hV)).symm
  rw [← GradedAlgebra.adjoin_grade_zero_union_grade_one_eq_top_iff (R := Γ(Y, V))]
  exact Algebra.IsPushout.adjoin_zero_union_one_eq_top (pullbackGradedSectionsLEGradedHom A hV)
    (pullbackGradedSectionsLEGradedHom_apply A hV)
    ((GradedAlgebra.adjoin_grade_zero_union_grade_one_eq_top_iff
      (R := Γ(X, U)) (A.obj.gradedSectionsGrading U)).mpr h)

/-- **Finite type pulls back**: over affine opens `U` of `X` and `V ⊆ g⁻¹ U` of `Y`, if the graded
sections of `A` over `U` form a finitely generated `Γ(X, U)`-algebra, then the graded sections of
`g^* A` over `V` form a finitely generated `Γ(Y, V)`-algebra. -/
theorem finiteType_pullback_sections (hU : IsAffineOpen U) (hV' : IsAffineOpen V)
    (hV : V ≤ g ⁻¹ᵁ U) [Algebra.FiniteType Γ(X, U) (⨁ n, Γ(A.obj.X n, U))] :
    Algebra.FiniteType Γ(Y, V) (⨁ n, Γ(((pullback g).obj A).obj.X n, V)) := by
  rw [← RingHom.finiteType_algebraMap]
  exact (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
    RingHom.finiteType_isStableUnderBaseChange).of_isPushout
      (isPushout_pullbackGradedSectionsLE A hU hV' hV)
      (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- **Finiteness of the degree-zero sections pulls back**: over affine opens `U` of `X` and
`V ⊆ g⁻¹ U` of `Y`, if the degree-zero sections of `A` over `U` form a finite `Γ(X, U)`-module, then
the degree-zero sections of `g^* A` over `V` form a finite `Γ(Y, V)`-module. -/
theorem finite_pullback_sections_zero (hU : IsAffineOpen U) (hV' : IsAffineOpen V)
    (hV : V ≤ g ⁻¹ᵁ U) [Module.Finite Γ(X, U) Γ(A.obj.X 0, U)] :
    Module.Finite Γ(Y, V) Γ(((pullback g).obj A).obj.X 0, V) := by
  let : Algebra Γ(X, U) Γ(Y, V) := (g.appLE U V hV).hom.toAlgebra
  obtain ⟨e, -⟩ := Scheme.Hom.exists_pullbackSectionsLE_equiv g (A.obj.X 0) hU hV' hV
  rw [pullback_obj_obj_X]
  exact Module.Finite.equiv e

end GradedQuasicoherentAlgebra

end

end AlgebraicGeometry

end TauCeti
