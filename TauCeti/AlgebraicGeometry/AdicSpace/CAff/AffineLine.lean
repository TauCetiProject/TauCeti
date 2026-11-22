/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import TauCeti.AlgebraicGeometry.AdicSpace.CAff.Basic

import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import TauCeti.RingTheory.Polynomial.IsIntegral

/-!
# The affine line in `CAff` and representability of global sections

This file constructs the discrete Huber pair `CAff.affineLine = (ℤ[T], ℤ)` in `CAff.{u}` and
proves that `op CAff.affineLine` represents the global-ring presheaf `CAff.globalSections` on
`CAff.{u}ᵒᵖ`.

## Main definitions

* `TauCeti.CAff.affineLine`: the discrete Huber pair `(ℤ[T], ℤ)` in `CAff.{u}`.
* `TauCeti.CAff.affineLineRingEquiv`: the canonical ring isomorphism
  `(ULift ℤ)[X] ≃+* affineLine.ring`.
* `TauCeti.CAff.affineLineVar`: the coordinate `T` in `CAff.affineLine.ring`.
* `TauCeti.CAff.eval` and `TauCeti.CAff.evalEquiv`: evaluation morphisms `CAff.affineLine ⟶ X`
  corresponding bijectively to elements of `X.ring`.
* `TauCeti.CAff.globalSectionsRepresentableBy` and `TauCeti.CAff.globalSectionsIsoYoneda`:
  representability of `CAff.globalSections` by `op CAff.affineLine`.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343v3, §2–3.
* P. Scholze and J. Weinstein, *Berkeley Lectures on `p`-adic Geometry*, Annals of Mathematics
  Studies 207, Princeton University Press (2020), Lectures 2–4.
-/

public section

open CategoryTheory Opposite Polynomial TauCeti.Huber

universe u

namespace TauCeti.CAff

/-- Underlying pair `(ℤ[T], ℤ)` in universe `u` with the discrete topology on `(ULift ℤ)[X]`. -/
private noncomputable def affineLinePair :
    letI : UniformSpace (ULift.{u} ℤ)[X] := ⊥
    haveI : DiscreteTopology (ULift.{u} ℤ)[X] := ⟨rfl⟩
    Pair (ULift.{u} ℤ)[X] :=
  letI : UniformSpace (ULift.{u} ℤ)[X] := ⊥
  haveI : DiscreteTopology (ULift.{u} ℤ)[X] := ⟨rfl⟩
  haveI : IsDomain (ULift.{u} ℤ) :=
    Function.Injective.isDomain ULift.ringEquiv.toRingHom ULift.ringEquiv.injective
  { plus := (Polynomial.C (R := ULift.{u} ℤ)).range
    isRingOfIntegralElements :=
      { isOpen := isOpen_discrete _
        isIntegrallyClosedIn := TauCeti.isIntegrallyClosedIn_range_C
        le_powerBoundedSubring := by simp } }

/-- The discrete polynomial ring `ℤ[T]` in universe `u` paired with the constant subring `ℤ` as its
ring of integral elements. Morphisms `(ℤ[T], ℤ) ⟶ (A, A⁺)` in `CAff` correspond bijectively to
elements of `A` (`CAff.evalEquiv`), since `ℤ[T]` is discrete and `ℤ` maps into every subring
`A⁺`. -/
noncomputable def affineLine : CAff.{u} :=
  letI : UniformSpace (ULift.{u} ℤ)[X] := ⊥
  haveI : DiscreteUniformity (ULift.{u} ℤ)[X] := ⟨rfl⟩
  haveI : DiscreteTopology (ULift.{u} ℤ)[X] := ⟨rfl⟩
  { ring := (ULift.{u} ℤ)[X]
    pair := affineLinePair.{u} }

/-- Canonical ring isomorphism identifying `CAff.affineLine.ring` with `(ULift ℤ)[X]`. -/
noncomputable def affineLineRingEquiv : (ULift.{u} ℤ)[X] ≃+* affineLine.{u}.ring :=
  RingEquiv.refl _

/-- The indeterminate `T` in `CAff.affineLine.ring`. -/
noncomputable def affineLineVar : affineLine.{u}.ring :=
  affineLineRingEquiv Polynomial.X

@[simp]
theorem affineLineRingEquiv_X :
    affineLineRingEquiv.{u} Polynomial.X = affineLineVar.{u} := by
  rfl

@[simp]
theorem mem_affineLine_plus_iff (p : (ULift.{u} ℤ)[X]) :
    affineLineRingEquiv p ∈ affineLine.{u}.pair.plus ↔
      p ∈ (Polynomial.C (R := ULift.{u} ℤ)).range := by
  rfl

/-- The indeterminate `T` does not lie in the plus ring `ℤ` of `CAff.affineLine = (ℤ[T], ℤ)`,
reflecting that morphisms `(ℤ[T], ℤ) ⟶ (A, A⁺)` may evaluate `T` at arbitrary (not necessarily
power-bounded) elements of `A`. -/
theorem affineLineVar_notMem_plus : affineLineVar.{u} ∉ affineLine.{u}.pair.plus := by
  rw [← affineLineRingEquiv_X, mem_affineLine_plus_iff]
  rintro ⟨c, hc⟩
  simpa using congrArg (fun p : (ULift.{u} ℤ)[X] ↦ p.coeff 1) hc

/-- Evaluate `(ℤ[T], ℤ)` at an arbitrary element `a : X.ring` to obtain a morphism
`CAff.affineLine ⟶ X` in `CAff`. Continuity is automatic because `ℤ[T]` carries the discrete
topology, and plus-ring compatibility holds because `ℤ` maps into every subring `X.pair.plus`. -/
noncomputable def eval (X : CAff.{u}) (a : X.ring) : affineLine.{u} ⟶ X :=
  letI : DiscreteTopology affineLine.{u}.ring := ⟨rfl⟩
  { toRingHom :=
      (Polynomial.eval₂RingHom ((Int.castRingHom X.ring).comp ULift.ringEquiv.toRingHom) a).comp
        affineLineRingEquiv.symm.toRingHom
    continuous_toRingHom := continuous_of_discreteTopology
    map_mem_plus := by
      intro p hp
      rw [← affineLineRingEquiv.apply_symm_apply p, mem_affineLine_plus_iff] at hp
      obtain ⟨c, hc⟩ := hp
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, ← hc, coe_eval₂RingHom, eval₂_C, eq_intCast]
      exact intCast_mem X.pair.plus _ }

theorem eval_toRingHom_apply_affineLineRingEquiv (X : CAff.{u}) (a : X.ring)
    (p : (ULift.{u} ℤ)[X]) :
    (eval X a).toRingHom (affineLineRingEquiv p) =
      eval₂ ((Int.castRingHom X.ring).comp ULift.ringEquiv.toRingHom) a p := by
  simp [eval]

theorem eval_toRingHom_comp_affineLineRingEquiv (X : CAff.{u}) (a : X.ring) :
    (eval X a).toRingHom.comp affineLineRingEquiv.toRingHom =
      Polynomial.eval₂RingHom ((Int.castRingHom X.ring).comp ULift.ringEquiv.toRingHom) a :=
  RingHom.ext fun p ↦ eval_toRingHom_apply_affineLineRingEquiv X a p

@[simp]
theorem eval_affineLineVar (X : CAff.{u}) (a : X.ring) :
    (eval X a).toRingHom affineLineVar = a := by
  rw [← affineLineRingEquiv_X, eval_toRingHom_apply_affineLineRingEquiv]
  exact eval₂_X _ a

@[simp]
theorem eval_comp {X Y : CAff.{u}} (a : X.ring) (f : X ⟶ Y) :
    eval X a ≫ f = eval Y (f.toRingHom a) := by
  apply Pair.Hom.ext
  refine (RingHom.cancel_right (f := affineLineRingEquiv.toRingHom)
    affineLineRingEquiv.surjective).mp ?_
  refine RingHom.ext fun p ↦ ?_
  have hcomp : f.toRingHom.comp ((Int.castRingHom X.ring).comp ULift.ringEquiv.toRingHom) =
      (Int.castRingHom Y.ring).comp ULift.ringEquiv.toRingHom := by
    ext ⟨n⟩
    simp
  simp only [comp_toRingHom, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, eval_toRingHom_apply_affineLineRingEquiv]
  rw [Polynomial.hom_eval₂, ← RingEquiv.toRingHom_eq_coe, hcomp]

/-- Morphisms `CAff.affineLine ⟶ X` in `CAff` correspond bijectively to elements of `X.ring` via
evaluation at `CAff.affineLineVar`. -/
noncomputable def evalEquiv (X : CAff.{u}) : X.ring ≃ (affineLine.{u} ⟶ X) where
  toFun := eval X
  invFun f := f.toRingHom affineLineVar
  left_inv a := eval_affineLineVar X a
  right_inv f := by
    apply Pair.Hom.ext
    refine (RingHom.cancel_right (f := affineLineRingEquiv.toRingHom)
      affineLineRingEquiv.surjective).mp ?_
    let _ : Algebra (ULift.{u} ℤ) X.ring :=
      RingHom.toAlgebra ((Int.castRingHom X.ring).comp ULift.ringEquiv.toRingHom)
    let φ : (ULift.{u} ℤ)[X] →ₐ[ULift.{u} ℤ] X.ring :=
      { toRingHom := f.toRingHom.comp affineLineRingEquiv.toRingHom
        commutes' r := by
          rcases r with ⟨n⟩
          have hn : (Polynomial.C (⟨n⟩ : ULift.{u} ℤ)) = (n : (ULift.{u} ℤ)[X]) := by
            rw [← Polynomial.C_eq_intCast]
            rfl
          change f.toRingHom (affineLineRingEquiv (Polynomial.C ⟨n⟩)) = (n : X.ring)
          rw [hn, map_intCast, map_intCast] }
    have h := congrArg AlgHom.toRingHom
      ((Polynomial.aevalEquiv (ULift.{u} ℤ) X.ring).right_inv φ)
    refine (eval_toRingHom_comp_affineLineRingEquiv X (f.toRingHom affineLineVar)).trans ?_
    exact h

@[simp]
theorem evalEquiv_apply (X : CAff.{u}) (a : X.ring) : evalEquiv X a = eval X a := (rfl)

@[simp]
theorem evalEquiv_symm_apply (X : CAff.{u}) (f : affineLine.{u} ⟶ X) :
    (evalEquiv X).symm f = f.toRingHom affineLineVar := (rfl)

/-- `CAff.eval X : X.ring → (CAff.affineLine ⟶ X)` is bijective. -/
theorem eval_bijective (X : CAff.{u}) : Function.Bijective (eval X) :=
  (evalEquiv X).bijective

/-- `op CAff.affineLine` represents the global-ring presheaf `CAff.globalSections` on `CAffᵒᵖ`. -/
noncomputable def globalSectionsRepresentableBy :
    globalSections.{u}.RepresentableBy (op affineLine.{u}) where
  homEquiv {Z} := Quiver.Hom.opEquiv.symm.trans (evalEquiv (unop Z)).symm
  homEquiv_comp g f :=
    -- `globalSections` is `@[expose]`, so both sides reduce definitionally via
    -- `evalEquiv_symm_apply` and `globalSections_map_apply` to `comp_toRingHom` at `affineLineVar`.
    RingHom.congr_fun (comp_toRingHom f.unop g.unop) affineLineVar

/-- **Representability of the global-ring presheaf on `CAffᵒᵖ`.** Sending `a ∈ A` to the opposite of
the evaluation morphism `CAff.eval (A, A⁺) a : (ℤ[T], ℤ) ⟶ (A, A⁺)` defines a natural isomorphism
`CAff.globalSections ≅ yoneda.obj (op CAff.affineLine)`. -/
noncomputable def globalSectionsIsoYoneda : globalSections.{u} ≅ yoneda.obj (op affineLine.{u}) :=
  globalSectionsRepresentableBy.toIso.symm

@[simp]
theorem globalSectionsIsoYoneda_hom_app (X : CAff.{u}) (a : X.ring) :
    globalSectionsIsoYoneda.hom.app (op (op X)) a = (eval X a).op := (rfl)

@[simp]
theorem globalSectionsIsoYoneda_inv_app (X : CAff.{u}) (f : op X ⟶ op affineLine.{u}) :
    globalSectionsIsoYoneda.inv.app (op (op X)) f = f.unop.toRingHom affineLineVar := (rfl)

end TauCeti.CAff

end
