/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# Examples for the category of smooth representations

For a discrete group the inclusion `SmoothRep A G ⥤ Rep A G` is an equivalence and every counit
of the smooth-part adjunction is invertible. The counit sends a smooth vector to its underlying
vector, the smooth part of a morphism acts as the morphism itself, and the smooth part of the zero
representation is a zero object. The endomorphisms of the trivial smooth representation on `A` are
the scalars.
-/

public section

open CategoryTheory Limits Representation

namespace TauCeti

variable {A G : Type*} [Ring A] [Group G] [TopologicalSpace G]

example [DiscreteTopology G] : (SmoothRep.ι A G).IsEquivalence :=
  inferInstance

variable [SeparatelyContinuousMul G]

example [DiscreteTopology G] (W : Rep A G) :
    IsIso ((SmoothRep.smoothPartAdjunction A G).counit.app W) :=
  inferInstance

example (W : Rep A G) (v : W.ρ.smoothVectors.toSubmodule) :
    ((SmoothRep.smoothPartAdjunction A G).counit.app W).hom v = Subtype.val v := by
  simp

example {V W : Rep A G} (f : V ⟶ W) (v : V.ρ.smoothVectors.toSubmodule) :
    Subtype.val (((SmoothRep.smoothPart A G).map f).hom.hom v) = f.hom v := by
  simp

/-- The smooth part of the zero representation is a zero object. -/
example : IsZero ((SmoothRep.smoothPart A G).obj (Rep.trivial A G PUnit)) :=
  IsZero.of_full_of_faithful_of_isZero (SmoothRep.ι A G) _ <| (Rep.isZero_iff _).2 <|
    inferInstanceAs (Subsingleton (Rep.trivial A G PUnit).ρ.smoothVectors.toSubmodule)

/-- Every endomorphism of the trivial smooth representation on `A` is multiplication on the right
by a scalar, namely its value at `1`. -/
example (f : SmoothRep.of (trivial A G A) ⟶ SmoothRep.of (trivial A G A)) (a : A) :
    f.hom.hom a = a * f.hom.hom 1 := by
  simpa using f.hom.hom.toLinearMap.map_smul a 1

end TauCeti
