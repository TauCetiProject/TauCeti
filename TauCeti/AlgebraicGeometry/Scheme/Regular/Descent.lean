/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
public import TauCeti.RingTheory.RegularLocalRing.Descent

/-!
# Faithfully flat descent of regularity

For a flat morphism `f : X ⟶ Y`, regularity of the local ring at `x` implies regularity of
the local ring at `f x`. Consequently, if `Y` is locally Noetherian and `f` is surjective,
regularity of `X` implies regularity of `Y`. This applies in particular to finite faithfully
flat covers; it needs neither étaleness nor a hypothesis on the fibre dimensions.

The dimension condition is separate from regularity. For finite faithfully flat covers, the
companion results in `TauCeti.AlgebraicGeometry.Morphisms.Flat.Dimension` descend the condition
that every nonempty open has a prescribed dimension.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7 (i).
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Notes Added in Proof,
  pp. 505–510, for descent along finite flat surjections.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Along a flat morphism, regularity of a source local ring implies regularity of the
corresponding target local ring. The target need not be locally Noetherian. -/
theorem isRegularLocalRing_stalk_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) := by
  have hflat := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact TauCeti.IsRegularLocalRing.of_flat_of_isLocalHom (S := X.presheaf.stalk x)

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.IsRegular

/-- Regularity descends along a flat surjective morphism to a locally Noetherian scheme.
In particular it descends along finite faithfully flat covers of such a scheme. -/
theorem of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsLocallyNoetherian Y] [IsRegular X] : IsRegular Y := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := f.surjective y
  exact f.isRegularLocalRing_stalk_of_flat x

end TauCeti.AlgebraicGeometry.IsRegular
