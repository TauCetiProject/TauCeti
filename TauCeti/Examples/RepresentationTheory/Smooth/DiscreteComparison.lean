/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.DiscreteComparison

/-!
# Examples for smooth representations as discrete continuous representations

The equivalence `SmoothRep A G ≌ SmoothDiscreteTopRep A G` sends a trivial representation to a
trivial one and a zero representation to a zero object. For a discrete group every representation
is smooth, so every object of `Rep A G` reaches `SmoothDiscreteTopRep A G`, and the comparison
identifies both the underlying module and the action through one linear equivalence.
-/

public section

open CategoryTheory Limits Representation

universe w

namespace TauCeti

variable {A G : Type*} [Ring A] [TopologicalSpace A] [DiscreteTopology A] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- The trivial object remains trivial: on the image of a trivial representation every operator
is the identity. -/
example {M : Type*} [AddCommGroup M] [Module A M] (g : G)
    (x : ((SmoothRep.equivSmoothDiscreteTopRep A G).functor.obj
      (SmoothRep.of (trivial A G M))).obj.V) :
    ((SmoothRep.equivSmoothDiscreteTopRep A G).functor.obj
      (SmoothRep.of (trivial A G M))).obj.ρ g x = x :=
  rfl

/-- The zero module remains zero. -/
example {V : SmoothRep A G} (hV : IsZero V) :
    IsZero ((SmoothRep.equivSmoothDiscreteTopRep A G).functor.obj V) :=
  Functor.map_isZero _ hV

/-- The image of the zero module has a single point. -/
example : Subsingleton ((SmoothRep.equivSmoothDiscreteTopRep A G).functor.obj
    (SmoothRep.of (trivial A G PUnit))).obj.V :=
  inferInstanceAs (Subsingleton PUnit)

/-- For a discrete group every representation is allowed: each `V : Rep A G` reaches
`SmoothDiscreteTopRep A G`, by a linear equivalence of underlying modules that carries the action
of `V` to the action of its image. -/
example [DiscreteTopology G] (V : Rep.{w} A G) :
    ∃ (X : SmoothDiscreteTopRep.{_, _, w} A G) (e : V ≃ₗ[A] X.obj.V),
      ∀ (g : G) (v : V), e (V.ρ g v) = X.obj.ρ g (e v) :=
  ⟨(SmoothRep.equivSmoothDiscreteTopRep A G).functor.obj ⟨V, inferInstance⟩, LinearEquiv.refl _ _,
    fun _ _ ↦ rfl⟩

end TauCeti
