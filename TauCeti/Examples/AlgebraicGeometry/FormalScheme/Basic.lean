/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Checks for the formal-scheme carrier

These examples use the affine-open basis, open restrictions, and the fully faithful
inclusion of schemes. Discrete nonreduced and zero rings are allowed; the construction
does not require noetherianity or nontriviality of a coordinate ring.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry TauCeti TauCeti.FormalScheme

noncomputable section

namespace TauCeti.Examples.FormalScheme.Basic

-- The isomorphism characterization can be used without unfolding the affine-open predicate.
example (X : FormalScheme) (U : Opens X) (hU : X.IsAffineOpen U) :
    ∃ (A : Type*) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A),
      Nonempty (X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A) :=
  (isAffineOpen_iff X U).mp hU

-- Even non-affine opens remain formal schemes, and the inclusion has the expected image.
example (X : FormalScheme) (U : Opens X) :
    Set.range (forgetToLocallyRingedSpace.map (X.ofRestrict U)).base = (U : Set X) :=
  range_ofRestrict X U

-- Every neighbourhood admits an affine formal refinement through its given point.
example (X : FormalScheme) (U : Opens X) (x : X) (hx : x ∈ U) :
    ∃ V : Opens X, X.IsAffineOpen V ∧ x ∈ V ∧ V ≤ U :=
  Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx

-- The inclusion of schemes is full and faithful on actual morphisms.
example (X Y : Scheme) :
    (ofScheme.obj X ⟶ ofScheme.obj Y) ≃ (X ⟶ Y) :=
  (fullyFaithfulOfScheme.homEquiv).symm

-- The forgetful maps and restriction comparisons are characterized without unfolding definitions.
example (X : FormalScheme) (U : Opens X) :
    forgetToLocallyRingedSpace.map (X.ofRestrict U) =
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding :=
  forgetToLocallyRingedSpace_map_ofRestrict X U

example (X : FormalScheme) : X.restrictTopIso.hom = X.ofRestrict ⊤ := by
  simp only [restrictTopIso_hom]

example {X Y : Scheme} (f : X ⟶ Y) :
    forgetToLocallyRingedSpace.map (ofScheme.map f) = f.toLRSHom :=
  forgetToLocallyRingedSpace_map_ofScheme_map f

example (X : Scheme) :
    forgetToLocallyRingedSpace.obj (ofScheme.obj X) = X.toLocallyRingedSpace := by
  simp

example (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] (f : A) :
    (restrictBasicOpenIso A f).inv ≫ (ofSpf A).ofRestrict (Spf.basicOpen f) =
      InducedCategory.homMk (Spf.basicOpenι f) := by
  simp only [restrictBasicOpenIso_inv_ofRestrict]

section Discrete

/-- The discrete topology used for the finite-ring checks. -/
local instance zmodTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
/-- Discreteness for the finite-ring checks. -/
local instance zmodDiscreteTopology (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

-- A nonreduced affine scheme is retained as a formal scheme, without passing to its reduction.
example : ofScheme.obj (Spec (CommRingCat.of (ZMod 4))) ≅ ofSpf (ZMod 4) :=
  ofSchemeSpecIso (ZMod 4)

-- The empty basic open is still affine, including for the zero coordinate ring.
example : IsAffineOpen (ofSpf (ZMod 1)) (Spf.basicOpen (0 : ZMod 1)) :=
  isAffineOpen_basicOpen (ZMod 1) 0

example :
    (ofSpf (ZMod 4)).restrict (Spf.basicOpen (2 : ZMod 4)) ≅
      ofSpf (AdicRing.CompletedAway (ZMod 4) 2) :=
  restrictBasicOpenIso (ZMod 4) 2

end Discrete

end TauCeti.Examples.FormalScheme.Basic
