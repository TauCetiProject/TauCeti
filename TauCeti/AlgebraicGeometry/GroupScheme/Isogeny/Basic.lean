/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Isogenies of group schemes

For group schemes over a scheme, an isogeny is a homomorphism whose underlying scheme morphism is
finite, flat, and surjective. This file defines the corresponding morphism property and predicate,
and shows that isogenies contain the isomorphisms and are closed under composition.

## Main declarations

* `TauCeti.GroupScheme.isogenies`: the finite, flat, surjective morphism property on group schemes.
* `TauCeti.GroupScheme.IsIsogeny`: the corresponding predicate on a group-scheme morphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.
-/

-- The property-level isogeny API is adapted from
-- `TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny`.

public section

open CategoryTheory

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {G H K : Grp (Over X)}

/-- The morphism property of being an isogeny of group schemes over a scheme `X`: the
underlying scheme morphism is finite, flat, and surjective. -/
def isogenies (X : Scheme.{u}) : MorphismProperty (Grp (Over X)) :=
  (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme).inverseImage
    (Grp.forget _ ⋙ Over.forget _)

/-- A homomorphism of group schemes is an isogeny when its underlying scheme morphism is finite,
flat, and surjective. -/
abbrev IsIsogeny (f : G ⟶ H) : Prop :=
  isogenies X f

/-- A group-scheme morphism is an isogeny exactly when its underlying scheme morphism is finite,
flat, and surjective. -/
theorem isIsogeny_iff (f : G ⟶ H) :
    IsIsogeny f ↔
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left :=
  Iff.rfl

/-- Group-scheme isogenies contain identities and are closed under composition. -/
instance : (isogenies X).IsMultiplicative := by
  unfold isogenies
  let : (@Flat ⊓ @Surjective : MorphismProperty Scheme).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.inf
  let : (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.inf
  infer_instance

/-- Being a group-scheme isogeny is invariant under isomorphisms of arrows. -/
instance : (isogenies X).RespectsIso := by
  unfold isogenies
  let _ : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) ↦ inferInstance)
  let _ : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) ↦ inferInstance)
  let _ : MorphismProperty.RespectsIso
      (@Flat ⊓ @Surjective : MorphismProperty Scheme) :=
    MorphismProperty.RespectsIso.inf @Flat @Surjective
  let _ : MorphismProperty.RespectsIso
      (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme) :=
    MorphismProperty.RespectsIso.inf @IsFinite (@Flat ⊓ @Surjective)
  exact MorphismProperty.RespectsIso.inverseImage
    (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme)
    (Grp.forget (Over X) ⋙ Over.forget X)

/-- The identity of a group scheme is an isogeny. -/
@[simp]
theorem isIsogeny_id (G : Grp (Over X)) : IsIsogeny (𝟙 G) :=
  (isogenies X).id_mem G

/-- Every isomorphism of group schemes is an isogeny. -/
theorem isIsogeny_of_isIso (f : G ⟶ H) [IsIso f] : IsIsogeny f :=
  (isogenies X).of_isIso f

namespace IsIsogeny

/-- The underlying scheme morphism of a group-scheme isogeny is finite. -/
theorem isFinite {f : G ⟶ H} (hf : IsIsogeny f) : IsFinite f.hom.hom.left :=
  (isIsogeny_iff f).mp hf |>.1

/-- The underlying scheme morphism of a group-scheme isogeny is flat. -/
theorem flat {f : G ⟶ H} (hf : IsIsogeny f) : Flat f.hom.hom.left :=
  (isIsogeny_iff f).mp hf |>.2.1

/-- The underlying scheme morphism of a group-scheme isogeny is surjective. -/
theorem surjective {f : G ⟶ H} (hf : IsIsogeny f) : Surjective f.hom.hom.left :=
  (isIsogeny_iff f).mp hf |>.2.2

/-- A composite of group-scheme isogenies is an isogeny. -/
theorem comp {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsogeny f) (hg : IsIsogeny g) :
    IsIsogeny (f ≫ g) :=
  (isogenies X).comp_mem f g hf hg

end IsIsogeny

end TauCeti.GroupScheme
