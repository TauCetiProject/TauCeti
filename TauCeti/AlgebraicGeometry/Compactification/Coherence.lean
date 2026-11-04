/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.BaseChange

/-!
# Coherence of base change of compactifications

The comparison isomorphisms for base change satisfy both unit laws and the associativity
law. We state these as equalities of the underlying maps of ambient schemes: source
relabelling does not change these maps, and a morphism of compactifications is determined
by its ambient map. Thus the equations can be used without identifying differently
parenthesized interiors or unfolding the source-relabelling functors.

The `pullback.congrHom` terms retain the canonical identifications induced by the unit
and associativity equations of base maps. In particular, the associativity law compares
the two routes from base change along three composed maps to three successive base
changes, rather than treating the chosen fibre products as definitionally associative.
No density or flatness assumption is needed.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti.Compactification

noncomputable section

variable {X S T T' T'' : Scheme.{u}} {f : X ⟶ S}

/-- The composition comparison followed by the unit comparison on the new base is the
canonical identification coming from `𝟙 T ≫ g = g`. -/
@[reassoc]
theorem baseChangeCompIso_id_hom_hom_h (C : Compactification f) (g : T ⟶ S) :
    (C.baseChangeCompIso g (𝟙 T)).hom.hom.h ≫
        (C.baseChange g).baseChangeIdIso.hom.hom.h =
      (pullback.congrHom (rfl : C.p = C.p) (Category.id_comp g)).hom := by
  -- Source relabelling leaves the ambient proper map unchanged.
  apply pullback.hom_ext <;> simp [baseChange, precomp, Category.assoc]

/-- The composition comparison followed by the pullback of the unit comparison on the
old base is the canonical identification coming from `g ≫ 𝟙 S = g`. -/
@[reassoc]
theorem baseChangeCompIso_id_left_hom_hom_h (C : Compactification f) (g : T ⟶ S) :
    (C.baseChangeCompIso (𝟙 S) g).hom.hom.h ≫
        (baseChangeMap C.baseChangeIdIso.hom g).hom.h =
      (pullback.congrHom (rfl : C.p = C.p) (Category.comp_id g)).hom := by
  -- Normalize the proper maps of the relabelled pullbacks.
  apply pullback.hom_ext <;> simp [baseChange, precomp, Category.assoc]

/-- The two composition-comparison routes from a single base change to three iterated
base changes agree, with the canonical identification of the two composite base maps. -/
@[reassoc]
theorem baseChangeCompIso_assoc_hom_hom_h (C : Compactification f)
    (g : T ⟶ S) (g' : T' ⟶ T) (g'' : T'' ⟶ T') :
    (C.baseChangeCompIso g (g'' ≫ g')).hom.hom.h ≫
        ((C.baseChange g).baseChangeCompIso g' g'').hom.hom.h =
      (pullback.congrHom (rfl : C.p = C.p) (Category.assoc g'' g' g)).hom ≫
        (C.baseChangeCompIso (g' ≫ g) g'').hom.hom.h ≫
          (baseChangeMap (C.baseChangeCompIso g g').hom g'').hom.h := by
  -- The relabelled compactifications have the same ambient schemes and proper maps.
  -- Normalize only those proper maps so that the three pullback projections apply.
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [baseChange, precomp, Category.assoc]
    · simp [baseChange, precomp, Category.assoc]
  · simp [baseChange, precomp, Category.assoc]

end

end TauCeti.Compactification
