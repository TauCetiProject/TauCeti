/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.DenseReplacement.BaseChange
public import TauCeti.AlgebraicGeometry.Compactification.Uniqueness

/-!
# Coherence of dense replacement under base change

The schematic closure of the interior commutes with relabelling the source by an
isomorphism. This comparison identifies the sources of the identity and composition laws
for `Compactification.denseReplacementBaseChange`: the pullback along an identity, or an
iterated pullback, has only a canonically isomorphic interior, not a definitionally equal one.

The composition law compares taking dense replacement after a composite base change with
the two successive dense-replacement comparisons. It holds for arbitrary base changes;
in particular the intermediate pulled-back interiors need not remain schematically dense.
For flat base changes it is also the composition law for the natural isomorphisms commuting
dense replacement with pullback. These laws let successive changes of base act coherently
on compactification diagrams used to define proper supports.

## References

* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RA).
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti.Compactification

noncomputable section

variable {X Y S T T' : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ S}

/-- Relabelling the source by an isomorphism commutes with dense replacement. The ambient
schemes are compared by the universal property of schematic closure, without reduction. -/
def denseReplacementPrecompIso (C : Compactification f) (e : Y ≅ X)
    (w : e.hom ≫ f = f') :
    (denseReplacement (C.precomp e.hom w)).obj ≅
      (denseReplacement C).obj.precomp e.hom w := by
  let D : DenseCompactification f' :=
    (DenseCompactification.sourceIsoEquivalence f f' e w).functor.obj (denseReplacement C)
  let h : D.obj ⟶ C.precomp e.hom w := (precompFunctor e.hom w).map (denseReplacementMap C)
  have : IsClosedImmersion h.hom.h := by
    -- Source relabelling leaves the ambient morphism unchanged.
    simpa only [h, precompFunctor_map_hom_h] using
      (inferInstance : IsClosedImmersion (denseReplacementMap C).hom.h)
  exact
    { hom := liftOfIsClosedImmersion h (denseReplacement (C.precomp e.hom w))
        (denseReplacementMap (C.precomp e.hom w))
      inv := (liftDenseReplacement (E := D) h).hom
      hom_inv_id := hom_unique _ _
      inv_hom_id := hom_unique _ _ }

/-- The source-relabelling comparison respects the canonical closed immersions back into
the original compactification. -/
@[reassoc (attr := simp)]
theorem denseReplacementPrecompIso_hom_comp (C : Compactification f) (e : Y ≅ X)
    (w : e.hom ≫ f = f') :
    (denseReplacementPrecompIso C e w).hom ≫
        (precompFunctor e.hom w).map (denseReplacementMap C) =
      denseReplacementMap (C.precomp e.hom w) :=
  hom_unique _ _

/-- The inverse source-relabelling comparison respects the canonical closed immersions. -/
@[reassoc (attr := simp)]
theorem denseReplacementPrecompIso_inv_comp (C : Compactification f) (e : Y ≅ X)
    (w : e.hom ≫ f = f') :
    (denseReplacementPrecompIso C e w).inv ≫ denseReplacementMap (C.precomp e.hom w) =
      (precompFunctor e.hom w).map (denseReplacementMap C) :=
  hom_unique _ _

/-- Relabelling the source commutes with dense replacement naturally in refinements. -/
@[reassoc]
theorem denseReplacementPrecompIso_naturality {C D : Compactification f} (h : C ⟶ D)
    (e : Y ≅ X) (w : e.hom ≫ f = f') :
    ((denseReplacementFunctor f').map ((precompFunctor e.hom w).map h)).hom ≫
        (denseReplacementPrecompIso D e w).hom =
      (denseReplacementPrecompIso C e w).hom ≫
        (precompFunctor e.hom w).map ((denseReplacementFunctor f).map h).hom :=
  hom_unique _ _

/-- Dense replacement under identity base change agrees with the identity pullback
comparison, after the canonical relabelling of the source. -/
@[reassoc]
theorem denseReplacementBaseChange_id (C : Compactification f) :
    denseReplacementBaseChange C (𝟙 S) ≫ (denseReplacement C).obj.baseChangeIdIso.hom =
      ((denseReplacementFunctor (pullback.snd f (𝟙 S))).map C.baseChangeIdIso.hom).hom ≫
        (denseReplacementPrecompIso C (asIso (pullback.fst f (𝟙 S)))
          (by simp [pullback.condition])).hom :=
  hom_unique _ _

/-- Dense replacement under a composite base change agrees with applying the two
successive comparisons. No flatness assumption is needed on either base change. -/
@[reassoc]
theorem denseReplacementBaseChange_comp_base (C : Compactification f)
    (g : T ⟶ S) (g' : T' ⟶ T) :
    denseReplacementBaseChange C (g' ≫ g) ≫
        ((denseReplacement C).obj.baseChangeCompIso g g').hom =
      ((denseReplacementFunctor (pullback.snd f (g' ≫ g))).map
        (C.baseChangeCompIso g g').hom).hom ≫
        (denseReplacementPrecompIso ((C.baseChange g).baseChange g')
          (pullbackLeftPullbackSndIso f g g').symm (by simp)).hom ≫
        (precompFunctor (pullbackLeftPullbackSndIso f g g').inv (by simp)).map
          (denseReplacementBaseChange (C.baseChange g) g' ≫
            baseChangeMap (denseReplacementBaseChange C g) g') :=
  hom_unique _ _

end

end TauCeti.Compactification
