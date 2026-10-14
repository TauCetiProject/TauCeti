/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic
public import TauCeti.AlgebraicTopology.Singular.IntervalGenerator

/-!
# Comparison of the two Hurewicz maps in degree one

Two Hurewicz maps are defined in degree one:

* `HomotopyGroup.hurewiczHom R 0` of `TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic`, sending
  the class of a generalized loop `p : (I¹, ∂I¹) ⟶ (X, {x})` to the image of the generator of
  `H₁(I¹, ∂I¹; R) ≅ R`, read in `H₁(X; R)`;
* `TauCeti.HurewiczOne.hurewicz₁` of `TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic`,
  sending a loop to the homology class of the singular `1`-simplex it traces.

They differ by a **sign**: the generator of `H₁(I¹, ∂I¹; R)`, transported from the generator
`[-e₀] - [e₀]` of reduced `H₀(S⁰)`, is minus the class of the standard simplex `t ↦ t`
(`TauCeti.singularHomologyCubeBoundaryPairIso_one_inv`). Hence the Hurewicz class of a loop is
minus the class of the simplex it traces (`GenLoop.hurewicz_eq_neg_ιHomology₁`), and with integer
coefficients `HomotopyGroup.hurewiczHom ℤ 0`, evaluated at `1`, is `-hurewicz₁` under the
identification `TauCeti.HurewiczOne.H₁AddEquivHomology` of `1`-cycles modulo boundaries with the
homology of the singular chain complex.

## Main results

* `GenLoop.hurewicz_eq_neg_ιHomology₁`: the Hurewicz class of a loop `p : I¹ → X` is minus the
  class of the singular `1`-simplex `GenLoop.simplex₁ p` it traces, for any coefficients.
* `HomotopyGroup.hurewiczHom_hom_one_eq_neg_hurewicz₁`: with integer coefficients,
  `hurewiczHom ℤ 0 a` evaluated at `1` is `-hurewicz₁ a`.
* `HomotopyGroup.hurewiczHom_hom_one_eq_neg_hurewiczHomologyAddEquiv`: the same, for a
  path-connected space, against the Hurewicz isomorphism
  `TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial TauCeti
open scoped unitInterval Topology Topology.Homotopy

universe w v u

namespace GenLoop

variable {X : Type w} [TopologicalSpace X] {x : X}

/-- The simplicial set of singular simplices of `X`, as the ambient simplicial set of the pair
`(X, {x})`. -/
abbrev pairSSet (x : X) : SSet.{w} :=
  (TopPair.toSSetPair.obj (TopPair.ofSubset ({x} : Set (TopCat.of X)))).right

/-- The singular `1`-simplex of `X` traced by a generalized loop `p : I¹ → X`: the image of the
standard simplex of the cube. -/
def simplex₁ (p : Ω^ (Fin 1) X x) : pairSSet x _⦋1⦌ :=
  (TopPair.toSSetPair.map (toCubeBoundaryPairHom.{w} p)).right.app _ cubeSimplex

/-- The two endpoints of the singular `1`-simplex traced by a loop agree: both are the base
point. -/
lemma δ_zero_simplex₁_eq_δ_one_simplex₁ (p : Ω^ (Fin 1) X x) :
    (pairSSet x).δ 0 (simplex₁ p) = (pairSSet x).δ 1 (simplex₁ p) := by
  have h₀ := SSetPair.δ_map_eq (Q := TopPair.toSSetPair.obj (cubeBoundaryPair.{w} 1))
    cubeSimplex (TopPair.toSSetPair.map (toCubeBoundaryPairHom.{w} p)) 0 _ δ_zero_cubeSimplex
  have h₁ := SSetPair.δ_map_eq (Q := TopPair.toSSetPair.obj (cubeBoundaryPair.{w} 1))
    cubeSimplex (TopPair.toSSetPair.map (toCubeBoundaryPairHom.{w} p)) 1 _ δ_one_cubeSimplex
  have hs : Subsingleton
      ((TopPair.toSSetPair.obj (TopPair.ofSubset ({x} : Set (TopCat.of X)))).left _⦋0⦌) :=
    @Equiv.subsingleton _ _ TopCat.toSSetObj₀Equiv (inferInstanceAs (Subsingleton ({x} : Set X)))
  exact h₀.trans ((congrArg _ (Subsingleton.elim _ _)).trans h₁.symm)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- The Hurewicz class of a loop in degree one, read in `H₁(X, {x}; R)`, is minus the image of the
class of the singular `1`-simplex it traces: the generator of `H₁(I¹, ∂I¹; R)` is minus the class
of the standard simplex (`TauCeti.singularHomologyCubeBoundaryPairIso_one_inv`). -/
lemma hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom_eq_neg (p : Ω^ (Fin 1) X x) :
    hurewicz R p ≫ (singularHomologyIsoOfSubsetSingleton R 0 x).hom =
      -(TauCeti.SSet.ιHomology₁ R (pairSSet x) (simplex₁ p) (δ_zero_simplex₁_eq_δ_one_simplex₁ p) ≫
        (TopPair.ofSubset ({x} : Set (TopCat.of X))).singularHomologyπ R 1) := by
  rw [hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom,
    singularHomologyCubeBoundaryPairIso_one_inv, Preadditive.neg_comp,
    cubeRelClass_singularHomologyMap]
  congr 1
  exact (SSetPair.ιHomology₁_homologyπ R _ _ _ _ _ _ _).symm

/-- **The Hurewicz class of a loop in degree one** is minus the homology class of the singular
`1`-simplex it traces. -/
theorem hurewicz_eq_neg_ιHomology₁ (p : Ω^ (Fin 1) X x) :
    hurewicz R p =
      -TauCeti.SSet.ιHomology₁ R (pairSSet x) (simplex₁ p) (δ_zero_simplex₁_eq_δ_one_simplex₁ p) :=
  (cancel_mono (singularHomologyIsoOfSubsetSingleton R 0 x).hom).1
    ((hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom_eq_neg R p).trans
      ((Preadditive.neg_comp _ _).symm.trans (congrArg (fun g ↦ (-TauCeti.SSet.ιHomology₁ R
        (pairSSet x) (simplex₁ p) (δ_zero_simplex₁_eq_δ_one_simplex₁ p)) ≫ g)
          (singularHomologyIsoOfSubsetSingleton_hom R 0 x).symm)))

/-- The singular `1`-simplex traced by a generalized loop is the singular `1`-simplex of the
corresponding loop (`TauCeti.TopCat.simplex₁`). -/
@[simp]
lemma simplex₁_eq_topCatSimplex₁ (p : Ω^ (Fin 1) X x) :
    simplex₁ p = TauCeti.TopCat.simplex₁ (genLoopEquivOfUnique (Fin 1) p).toContinuousMap := by
  apply ((TopCat.of X).toSSetObjEquiv _).injective
  refine ((TopCat.toSSetObjEquiv_toSSet_map_app
    (TopPair.Hom.fst (toCubeBoundaryPairHom.{w} p)) cubeSimplex).trans ?_).trans
      (TauCeti.TopCat.toSSetObjEquiv_simplex₁ _).symm
  ext a
  rw [ContinuousMap.comp_apply, toSSetObjEquiv_cubeSimplex_apply]
  exact (toCubeBoundaryPairHom_fst_apply p _).trans (congrArg p (cubePoint_down _))

section Integer

variable {X : Type} [TopologicalSpace X] {x : X}

/-- With integer coefficients, the class of the singular `1`-simplex traced by a generalized loop is
the homology class of the corresponding loop. -/
lemma ιHomology₁_hom_one_eq_H₁AddEquivHomology_loopClass (p : Ω^ (Fin 1) X x) :
    (TauCeti.SSet.ιHomology₁ (ModuleCat.of ℤ ℤ) (pairSSet x) (simplex₁ p)
      (δ_zero_simplex₁_eq_δ_one_simplex₁ p)).hom 1 =
      HurewiczOne.H₁AddEquivHomology (TopCat.of X)
        (HurewiczOne.loopClass (genLoopEquivOfUnique (Fin 1) p)) := by
  rw [TauCeti.SSet.ιHomology₁_eq]
  refine (HurewiczOne.H₁AddEquivHomology_loopClass _ _ ?_).symm
  refine (congr($(HomologicalComplex.liftCycles_i
    ((pairSSet x).chainComplex (ModuleCat.of ℤ ℤ)) ((pairSSet x).ιChainComplex (simplex₁ p)) 0
      (by simp) _).hom 1)).trans ?_
  exact congrArg (fun s ↦ ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (R := ModuleCat.of ℤ ℤ) s).hom 1) (simplex₁_eq_topCatSimplex₁ p)

/-- With integer coefficients, the Hurewicz class of a generalized loop, evaluated at `1`, is minus
the homology class of the corresponding loop. -/
theorem hurewicz_hom_one_eq_neg_loopClass (p : Ω^ (Fin 1) X x) :
    (hurewicz (ModuleCat.of ℤ ℤ) p).hom 1 =
      -HurewiczOne.H₁AddEquivHomology (TopCat.of X)
        (HurewiczOne.loopClass (genLoopEquivOfUnique (Fin 1) p)) :=
  (congrArg (fun f ↦ ModuleCat.Hom.hom f 1)
    (hurewicz_eq_neg_ιHomology₁ (ModuleCat.of ℤ ℤ) p)).trans
      (congrArg Neg.neg (ιHomology₁_hom_one_eq_H₁AddEquivHomology_loopClass p))

end Integer

end GenLoop

namespace HomotopyGroup

open TauCeti.HurewiczOne

variable {X : Type} [TopologicalSpace X] {x : X}

/-- **Comparison of the two Hurewicz maps in degree one**: on `π₁(X, x)`, the Hurewicz
homomorphism `HomotopyGroup.hurewiczHom` with integer coefficients, evaluated at `1 : ℤ`, is
**minus** the Hurewicz map `TauCeti.HurewiczOne.hurewicz₁` sending a loop to the homology class of
the singular `1`-simplex it traces. -/
theorem hurewiczHom_hom_one_eq_neg_hurewicz₁ (a : Additive (HomotopyGroup (Fin 1) X x)) :
    (hurewiczHom (ModuleCat.of ℤ ℤ) 0 a).hom 1 =
      -H₁AddEquivHomology (TopCat.of X) (Multiplicative.toAdd (hurewicz₁ (TopCat.of X) x
        (homotopyGroupOfUniqueMulEquivFundamentalGroup (Fin 1) a.toMul))) := by
  induction a using Additive.rec with | ofMul a =>
  induction a using Quotient.inductionOn with | h p =>
  refine (congrArg (fun f ↦ ModuleCat.Hom.hom f 1)
    ((hurewiczHom_apply _ 0 _).trans (hurewicz_mk _ 0 p))).trans
      ((GenLoop.hurewicz_hom_one_eq_neg_loopClass p).trans
        (congrArg (fun h ↦ -H₁AddEquivHomology _ h) ?_))
  exact (congrArg Multiplicative.toAdd
    (hurewicz₁_mk (X := TopCat.of X) (genLoopEquivOfUnique (Fin 1) p))).symm

/-- **Comparison of the two Hurewicz maps in degree one**, for a path-connected space: on
`π₁(X, x)`, the Hurewicz homomorphism `HomotopyGroup.hurewiczHom` with integer coefficients,
evaluated at `1 : ℤ`, is **minus** the Hurewicz isomorphism
`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv` on the abelianization. -/
theorem hurewiczHom_hom_one_eq_neg_hurewiczHomologyAddEquiv [PathConnectedSpace X]
    (a : Additive (HomotopyGroup (Fin 1) X x)) :
    (hurewiczHom (ModuleCat.of ℤ ℤ) 0 a).hom 1 =
      -hurewiczHomologyAddEquiv (X := TopCat.of X) x (Additive.ofMul (Abelianization.of
        (homotopyGroupOfUniqueMulEquivFundamentalGroup (Fin 1) a.toMul))) := by
  refine (hurewiczHom_hom_one_eq_neg_hurewicz₁ a).trans (congrArg Neg.neg ?_)
  exact (congrArg (H₁AddEquivHomology (TopCat.of X)) (hurewiczAb_ofMul_of x _).symm).trans
    (hurewiczHomologyAddEquiv_apply _).symm

end HomotopyGroup
