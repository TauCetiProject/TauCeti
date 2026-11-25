/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import TauCeti.CategoryTheory.Sites.Continuous
public import TauCeti.CategoryTheory.Sites.Limits
public import TauCeti.CategoryTheory.Sites.LocallyConstant.Basic

/-!
# Finite products of locally constant sheaves

Let `(C, J)` be a site and let `A` be a category with finite limits in which sheafification
exists and is left exact. For a property `P` of objects of `A` closed under binary products, the
sheaves which are locally constant with values in `P` are closed under binary products: over a
common refinement of the two covering sieves, `F ⨯ G` is the constant sheaf on `M ⨯ N`, since the
constant sheaf functor (`CategoryTheory.Sheaf.preservesFiniteLimits_constantSheaf`) and the
restriction functors to the slices `Over Y` preserve finite limits.
The terminal sheaf is the constant sheaf on the terminal object, so when `P` also holds for the
terminal object of `A`, locally constant sheaves with values in `P` are closed under all finite
products.

## Main declarations

* `CategoryTheory.Sheaf.IsLocallyConstantIn.prod`,
  `CategoryTheory.Sheaf.IsLocallyConstantIn.of_isTerminal`: binary products and terminal objects.
* The instances `IsClosedUnderBinaryProducts`, `IsClosedUnderLimitsOfShape (Discrete PEmpty)` and
  `IsClosedUnderFiniteProducts` for the object property `Sheaf.IsLocallyConstantIn J P`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
-/

public section

universe v u u' v'

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{v'} A] [HasSheafify J A] [HasFiniteLimits A] {P : ObjectProperty A}

/-- The restriction to `Over Y` of the constant sheaf on a binary product is the binary product
of the restrictions of the constant sheaves. -/
private noncomputable def overConstantSheafProdIso (M N : A) (Y : C) :
    ((constantSheaf J A).obj (M ⨯ N)).over Y ≅
      ((constantSheaf J A).obj M).over Y ⨯ ((constantSheaf J A).obj N).over Y :=
  (J.overPullback A Y).mapIso (PreservesLimitPair.iso (constantSheaf J A) M N) ≪≫
    PreservesLimitPair.iso (J.overPullback A Y) _ _

/-- **Binary products of locally constant sheaves.** If `P` is closed under binary products,
the product of two sheaves which are locally constant with values in `P` is locally constant
with values in `P`: over the members of the intersection of their sieves of local constancy,
`F ⨯ G` is constant on `M ⨯ N`. -/
theorem IsLocallyConstantIn.prod [P.IsClosedUnderBinaryProducts] {F G : Sheaf J A}
    (hF : F.IsLocallyConstantIn J P) (hG : G.IsLocallyConstantIn J P) :
    (F ⨯ G).IsLocallyConstantIn J P := by
  rw [isLocallyConstantIn_iff] at hF hG ⊢
  intro X
  refine J.superset_covering ?_ (J.intersection_covering (hF X) (hG X))
  intro Y f hf
  obtain ⟨M, hM, ⟨e⟩⟩ := (locallyConstantSieve_apply P F f).1 hf.1
  obtain ⟨N, hN, ⟨e'⟩⟩ := (locallyConstantSieve_apply P G f).1 hf.2
  exact (locallyConstantSieve_apply P _ f).2 ⟨M ⨯ N, P.prop_prod M N hM hN,
    ⟨PreservesLimitPair.iso (J.overPullback A Y) F G ≪≫ prod.mapIso e e' ≪≫
      (overConstantSheafProdIso M N Y).symm⟩⟩

/-- A terminal sheaf is locally constant with values in `P` when `P` holds for the terminal
object of `A`: it is the constant sheaf on the terminal object. -/
theorem IsLocallyConstantIn.of_isTerminal (hP : P (⊤_ A)) {F : Sheaf J A} (hF : IsTerminal F) :
    F.IsLocallyConstantIn J P :=
  (isLocallyConstantIn_constantSheaf hP).of_iso <|
    (IsTerminal.isTerminalObj (constantSheaf J A) _ terminalIsTerminal).uniqueUpToIso hF

instance isClosedUnderBinaryProducts_isLocallyConstantIn [P.IsClosedUnderBinaryProducts] :
    ObjectProperty.IsClosedUnderBinaryProducts (IsLocallyConstantIn J P) where
  limitsOfShape_le := by
    rintro F ⟨p⟩
    refine IsLocallyConstantIn.of_iso (p.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫
      HasLimit.isoOfNatIso (diagramIsoPair p.diag)).symm
      (IsLocallyConstantIn.prod (p.prop_diag_obj _) (p.prop_diag_obj _))

instance isClosedUnderLimitsOfShape_pEmpty_isLocallyConstantIn
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] :
    ObjectProperty.IsClosedUnderLimitsOfShape (IsLocallyConstantIn J P) (Discrete.{0} PEmpty) where
  limitsOfShape_le := by
    rintro F ⟨p⟩
    exact .of_isTerminal P.prop_terminal
      (isLimitChangeEmptyCone _ p.isLimit (asEmptyCone F) (Iso.refl _))

instance isClosedUnderFiniteProducts_isLocallyConstantIn [P.IsClosedUnderBinaryProducts]
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] :
    ObjectProperty.IsClosedUnderFiniteProducts (IsLocallyConstantIn J P) :=
  .mk'

end CategoryTheory.Sheaf
