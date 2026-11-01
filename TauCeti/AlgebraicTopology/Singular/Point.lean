/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The singular chains of a point

The singular chain complex of a one-point space `X`, with coefficients in an object `R` of a
preadditive category, is chain homotopy equivalent to `R` placed in degree zero
(`TauCeti.pointSingularChainHomotopyEquiv`). The forward map is the augmentation, which sends
the unique singular vertex to the identity of `R`, and the inverse includes `R` as the summand of
that vertex.

Unlike the vanishing of positive-degree homology, a chain homotopy equivalence survives any
additive functor. Applying `Hom(-, M)` to it computes the singular cohomology of a point with
arbitrary coefficients (`TauCeti.pointSingularCochainHomotopyEquiv`), without projectivity or
injectivity assumptions.

The singular simplicial set of a point is the constant simplicial set on it
(Mathlib's `TopCat.toSSetIsoConst`), and the constant augmented simplicial object has an extra
degeneracy (`SimplicialObject.Augmented.ExtraDegeneracy.const`), whose alternating face map
complex therefore contracts onto its augmentation
(`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`). The construction of the
contraction, and of its cochain counterpart, follows the unmerged Tau Ceti pull request
https://github.com/TauCetiProject/TauCeti/pull/20882.

## Main declarations

* `TauCeti.pointSingularChainHomotopyEquiv`: the chain homotopy equivalence between the singular
  chains of a one-point space and the coefficients in degree zero.
* `TauCeti.ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero` and
  `TauCeti.pointSingularChainHomotopyEquiv_inv_f_zero`: the forward map is the augmentation and
  the inverse is the inclusion of the unique vertex.
* `TauCeti.pointSingularChainHomotopyEquiv_hom_naturality`: the augmentation is natural in the
  coefficients.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, the homology of a point.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] [HasZeroObject C]
  (R : C) (X : TopCat.{w}) [Unique X]

/-- **The singular chains of a point contract onto the coefficients.** For a one-point space `X`,
the singular chain complex with coefficients in `R` is chain homotopy equivalent to `R` in
degree zero. The forward map is the augmentation and the inverse is the inclusion of the unique
vertex. -/
def pointSingularChainHomotopyEquiv :
    HomotopyEquiv ((TopCat.toSSet.obj X).chainComplex R) ((ChainComplex.single₀ C).obj R) :=
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex C).mapIso
    (Functor.isoWhiskerRight (TopCat.toSSetIsoConst X) (sigmaConst.obj R) ≪≫
      Functor.constComp _ _ _))).trans
    ((SimplicialObject.Augmented.ExtraDegeneracy.const (∐ fun _ : X ↦ R)).homotopyEquiv.trans
      (HomotopyEquiv.ofIso ((ChainComplex.single₀ C).mapIso
        (coproductUniqueIso fun _ : X ↦ R))))

/-- The augmentation sends the summand of the unique singular vertex of a point identically to
the coefficients. -/
@[reassoc]
lemma ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (pointSingularChainHomotopyEquiv R X).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).inv := by
  simp [SimplicialObject.Augmented.const, pointSingularChainHomotopyEquiv,
    HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    SSet.ιChainComplex, sigmaConst, Sigma.map', Functor.constComp]

/-- The inverse of the contraction of the singular chains of a point includes the coefficients
as the summand of the unique singular vertex. -/
lemma pointSingularChainHomotopyEquiv_inv_f_zero (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (pointSingularChainHomotopyEquiv R X).inv.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).hom ≫
        (TopCat.toSSet.obj X).ιChainComplex σ := by
  have : Subsingleton ((TopCat.toSSet.obj X) _⦋0⦌) := (X.toSSetObjEquiv _).subsingleton
  -- In degree zero the augmentation is an isomorphism: the summand of the unique vertex is all
  -- of the zero-chains, and the augmentation maps it identically onto the coefficients.
  have : IsIso ((pointSingularChainHomotopyEquiv R X).hom.f 0) :=
    ⟨(HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).hom ≫
        (TopCat.toSSet.obj X).ιChainComplex σ, by
      ext τ
      rw [Subsingleton.elim τ σ, ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero_assoc]
      simp, by rw [Category.assoc, ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero,
        Iso.hom_inv_id]⟩
  -- The homotopy `inv ≫ hom ≃ 𝟙` has no room to act in degree zero of `R[0]`.
  have h := (pointSingularChainHomotopyEquiv R X).homotopyInvHomId.comm 0
  rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex] at h
  rw [← cancel_mono ((pointSingularChainHomotopyEquiv R X).hom.f 0), Category.assoc,
    ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero, Iso.hom_inv_id]
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, HomologicalComplex.single_obj_d,
    comp_zero, zero_add] using h

/-- The augmentation of the singular chains of a point is natural in the coefficients. -/
@[reassoc]
lemma pointSingularChainHomotopyEquiv_hom_naturality {S : C} (f : R ⟶ S) :
    ((SSet.chainComplexFunctor C).map f).app (TopCat.toSSet.obj X) ≫
        (pointSingularChainHomotopyEquiv S X).hom =
      (pointSingularChainHomotopyEquiv R X).hom ≫ (ChainComplex.single₀ C).map f := by
  apply HomologicalComplex.to_single_hom_ext
  ext σ
  simp only [HomologicalComplex.comp_f, SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc,
    ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero,
    ιChainComplex_pointSingularChainHomotopyEquiv_hom_f_zero_assoc]
  simp

end TauCeti
