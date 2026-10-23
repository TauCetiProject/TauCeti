/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.DirectSum

/-!
# Sections of the direct-sum algebra of a graded quasicoherent algebra

Let `A = (Aₙ)ₙ` be a graded quasicoherent algebra on a scheme `X` and let `U` be an open of `X`.
There are two rings attached to `A` over `U`: the graded ring `⨁ n, Γ(Aₙ, U)` of sections of the
homogeneous components, with its native graded multiplication
(`CategoryTheory.CommMon.gCommRingSections`), and the ring `Γ(⨁ₙ Aₙ, U)` of sections of the
direct-sum algebra (`GradedQuasicoherentAlgebra.toQuasicoherentAlgebra`). The inclusions of the
summands `Aₙ ⟶ ⨁ₙ Aₙ` induce a `Γ(X, U)`-algebra homomorphism

`⨁ n, Γ(Aₙ, U) → Γ(⨁ₙ Aₙ, U)`,

compatible with restriction and with morphisms of graded algebras. When `U` is affine it is an
isomorphism, because sections over an affine open commute with direct sums of quasicoherent
sheaves. So over an affine open the coordinate ring of the direct-sum algebra, which is the ring
of an affine chart of its relative spectrum, is the graded ring of sections of `A`, with its
grading.

## Main declarations

* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.gradedSectionsHom`: the algebra
  homomorphism `⨁ n, Γ(Aₙ, U) → Γ(⨁ₙ Aₙ, U)`, which sends a homogeneous section to its image in
  the direct sum (`gradedSectionsHom_of`);
* `GradedQuasicoherentAlgebra.restrictSections_gradedSectionsHom` and
  `GradedQuasicoherentAlgebra.toQuasicoherentAlgebra_map_app_gradedSectionsHom`: its
  compatibility with restriction and with morphisms of graded quasicoherent algebras;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.gradedSectionsHom_bijective` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.gradedSectionsEquiv`: over an affine
  open it is an isomorphism of `Γ(X, U)`-algebras.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 and Exercise II.5.17.
-/

public section

open CategoryTheory MonoidalCategory MonObj DirectSum

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace GradedQuasicoherentAlgebra

variable {X : Scheme.{u}} (A : GradedQuasicoherentAlgebra X) (U : X.Opens)

/-- The inclusion of the summand `A₀` sends the unit of the graded ring of sections to the unit
of the sections of the direct-sum algebra. -/
private lemma ιTotal_app_gOne :
    (ιTotal A 0).app U (GradedMonoid.GOne.one (A := fun n ↦ Γ(A.obj.X n, U))) = 1 := by
  have h : A.obj.toMon.one ≫ ιTotal A 0 = η[(toQuasicoherentAlgebra.obj A).obj.X] :=
    (congrArg (· ≫ ιTotal A 0) (Mon.one_eq A.obj.toMon)).trans
      ((Category.assoc _ _ _).trans (one_toQuasicoherentAlgebra A).symm)
  rw [← map_one (algebraMap Γ(X, U) Γ((toQuasicoherentAlgebra.obj A).obj.X, U)),
    CommMon.sections_algebraMap_def, CommMon.sections_gOne_def]
  exact ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · U) h) _

/-- The inclusions of the summands send the homogeneous product of sections to the product of
their images in the sections of the direct-sum algebra. -/
private lemma ιTotal_app_gMul {i j : ℕ} (x : Γ(A.obj.X i, U)) (y : Γ(A.obj.X j, U)) :
    (ιTotal A (i + j)).app U (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.obj.X n, U)) x y) =
      (ιTotal A i).app U x * (ιTotal A j).app U y := by
  have h : A.obj.toMon.mul i j ≫ ιTotal A (i + j) =
      (ιTotal A i ⊗ₘ ιTotal A j) ≫ μ[(toQuasicoherentAlgebra.obj A).obj.X] :=
    (congrArg (· ≫ ιTotal A (i + j)) (Mon.mul_eq A.obj.toMon i j)).trans
      ((Category.assoc _ _ _).trans (ιTotal_tensorHom_ιTotal_mul A i j).symm)
  -- Both products are computed through the tensor map of the sections functor, which is
  -- natural in the two factors.
  have hμ := ConcreteCategory.congr_hom (Functor.LaxMonoidal.μ_natural
    (Scheme.Modules.sectionsFunctor U) (ιTotal A i) (ιTotal A j)) (x ⊗ₜ y)
  rw [CommMon.sections_mul_def, CommMon.sections_gMul_def]
  exact (ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · U) h) _).trans
    (congrArg (μ[(toQuasicoherentAlgebra.obj A).obj.X].app U) hμ.symm)

/-- The `Γ(X, U)`-algebra homomorphism `⨁ n, Γ(Aₙ, U) → Γ(⨁ₙ Aₙ, U)` from the graded ring of
sections of a graded quasicoherent algebra to the sections of its direct-sum algebra, induced by
the inclusions of the homogeneous summands. -/
def gradedSectionsHom :
    (⨁ n, Γ(A.obj.X n, U)) →ₐ[Γ(X, U)] Γ((toQuasicoherentAlgebra.obj A).obj.X, U) :=
  DirectSum.toAlgebra _ _ (fun n ↦ ((Scheme.Modules.sectionsFunctor U).map (ιTotal A n)).hom)
    (ιTotal_app_gOne A U) (ιTotal_app_gMul A U)

/-- A homogeneous section of degree `n` is sent to its image under the inclusion of the summand
`Aₙ` into the direct-sum algebra. -/
@[simp]
lemma gradedSectionsHom_of (n : ℕ) (x : Γ(A.obj.X n, U)) :
    gradedSectionsHom A U (DirectSum.of _ n x) = (ιTotal A n).app U x :=
  (DirectSum.toAlgebra_apply _ _ _ _ _ _).trans (DirectSum.toSemiring_of _ _ _ _ _)

/-- The comparison of sections commutes with restriction along an inclusion of opens `V ≤ U`. -/
lemma restrictSections_gradedSectionsHom {V : X.Opens} (i : V ⟶ U)
    (x : ⨁ n, Γ(A.obj.X n, U)) :
    (toQuasicoherentAlgebra.obj A).obj.restrictSections i (gradedSectionsHom A U x) =
      gradedSectionsHom A V (A.obj.restrictGradedSections i x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n x =>
    rw [gradedSectionsHom_of, CommMon.restrictGradedSections_of, gradedSectionsHom_of,
      CommMon.restrictSections_apply]
    exact (PresheafOfModules.naturality_apply (ιTotal A n).val i.op x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The comparison of sections is natural in the graded quasicoherent algebra: the algebra
morphism induced on direct sums by a graded morphism `f` corresponds to the map induced by `f` on
graded rings of sections. -/
lemma toQuasicoherentAlgebra_map_app_gradedSectionsHom {B : GradedQuasicoherentAlgebra X}
    (f : A ⟶ B) (x : ⨁ n, Γ(A.obj.X n, U)) :
    (toQuasicoherentAlgebra.map f).hom.hom.hom.app U (gradedSectionsHom A U x) =
      gradedSectionsHom B U (CommMon.gradedSectionsMap f.hom U x) := by
  -- The three cases are stated as term-mode equalities: rewriting under the component of
  -- `toQuasicoherentAlgebra.map f` produces motives that are not type-correct at instance
  -- transparency, as in the proofs about `ιTotal` in the direct-sum module.
  induction x using DirectSum.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)).symm)
  | of n x =>
    exact (congrArg _ (gradedSectionsHom_of A U n x)).trans
      ((ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · U)
        (ιTotal_toQuasicoherentAlgebra_map f n)) x).trans
      ((congrArg _ (CommMon.gradedSectionsMap_of f.hom U n x)).trans
        (gradedSectionsHom_of B U n _)).symm)
  | add x y hx hy =>
    exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans ((congrArg _ (map_add _ x y)).trans (map_add _ _ _)).symm))

/-- Over an affine open, the comparison `⨁ n, Γ(Aₙ, U) → Γ(⨁ₙ Aₙ, U)` is bijective: sections over
an affine open commute with direct sums of quasicoherent sheaves. -/
theorem gradedSectionsHom_bijective (hU : IsAffineOpen U) :
    Function.Bijective (gradedSectionsHom A U) := by
  let F := Scheme.Modules.sectionsFunctor U
  have h : ∀ x, gradedSectionsHom A U x =
      DirectSum.toModule Γ(X, U) ℕ (F.obj (toQuasicoherentAlgebra.obj A).obj.X)
        (fun n ↦ (F.map (ιTotal A n)).hom) x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | of n x =>
      rw [gradedSectionsHom_of, ← DirectSum.lof_eq_of Γ(X, U)]
      exact (DirectSum.toModule_lof (R := Γ(X, U)) (φ := fun n ↦ (F.map (ιTotal A n)).hom)
        n x).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ _ hx hy).trans (map_add _ x y).symm)
  exact (congrArg Function.Bijective (funext h)).mpr
    (toModule_sectionsFunctor_map_bijective (isColimitιTotal A) hU)

/-- Over an affine open `U`, the graded ring of sections `⨁ n, Γ(Aₙ, U)` of a graded
quasicoherent algebra is isomorphic, as a `Γ(X, U)`-algebra, to the sections of its direct-sum
algebra. -/
def gradedSectionsEquiv (hU : IsAffineOpen U) :
    (⨁ n, Γ(A.obj.X n, U)) ≃ₐ[Γ(X, U)] Γ((toQuasicoherentAlgebra.obj A).obj.X, U) :=
  AlgEquiv.ofBijective (gradedSectionsHom A U) (gradedSectionsHom_bijective A U hU)

/-- The isomorphism of sections over an affine open is the comparison `gradedSectionsHom`. -/
@[simp]
lemma gradedSectionsEquiv_apply (hU : IsAffineOpen U) (x : ⨁ n, Γ(A.obj.X n, U)) :
    gradedSectionsEquiv A U hU x = gradedSectionsHom A U x :=
  (rfl)

/-- The inverse isomorphism sends the image of a section of `Aₙ` in the direct-sum algebra back
to the homogeneous section of degree `n`. -/
@[simp]
lemma gradedSectionsEquiv_symm_ιTotal_app (hU : IsAffineOpen U) (n : ℕ)
    (x : Γ(A.obj.X n, U)) :
    (gradedSectionsEquiv A U hU).symm ((ιTotal A n).app U x) = DirectSum.of _ n x :=
  (AlgEquiv.symm_apply_eq _).mpr (gradedSectionsHom_of A U n x).symm

end GradedQuasicoherentAlgebra

end

end TauCeti.AlgebraicGeometry
