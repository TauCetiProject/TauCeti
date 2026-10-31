/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Schemes regular of a given dimension, and étale morphisms

A scheme `X` is *regular of dimension `d`* (`TauCeti.AlgebraicGeometry.IsRegularOfDim X d`) when
it is nonempty, all of its local rings are regular, and every nonempty open subscheme of `X` has
Krull dimension `d`. This is the notion in which Katz and Mazur state the regularity of moduli
problems (KM 4.12), in the reading fixed by their Notes Added in Proof (p. 505): being of a given
dimension is not étale-local, so the dimension condition is imposed on every nonempty open, and
non-emptiness is required separately.

The point of this formulation is that it is invariant under étale surjective morphisms
(`TauCeti.AlgebraicGeometry.isRegularOfDim_iff_of_etale_of_surjective`). An étale morphism
`f : X ⟶ Y` preserves and reflects regularity of local rings, and preserves the Krull dimension of
Noetherian local rings (`TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etale`,
`TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale`). The Krull dimension of an open
subscheme `U` is the supremum of the Krull dimensions of the local rings at the points of `U`
(`TauCeti.AlgebraicGeometry.topologicalKrullDim_opens_eq_iSup_ringKrullDim_stalk`). Since `f` is
open, every nonempty open of `X` maps onto a nonempty open of `Y` with the same local dimensions,
and when `f` is surjective every nonempty open of `Y` is the image of its nonempty preimage.

## Main declarations

* `TauCeti.AlgebraicGeometry.IsRegularOfDim`: a scheme which is nonempty, has regular local rings,
  and all of whose nonempty opens have Krull dimension `d`.
* `TauCeti.AlgebraicGeometry.IsRegularOfDim.iSup_ringKrullDim_stalk_eq`: the dimension condition
  in terms of the local rings.
* `TauCeti.AlgebraicGeometry.IsRegularOfDim.of_etale`: the nonempty source of an étale morphism
  to a scheme regular of dimension `d` is regular of dimension `d`.
* `TauCeti.AlgebraicGeometry.IsRegularOfDim.of_etale_of_surjective`: the target of an étale
  surjective morphism from a scheme regular of dimension `d` is regular of dimension `d`.
* `TauCeti.AlgebraicGeometry.isRegularOfDim_iff_of_etale_of_surjective`: the two combined.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 4.12 and the Notes Added in Proof, p. 505.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A scheme `X` is **regular of dimension `d`** when it is nonempty, all of its local rings are
regular, and every nonempty open subscheme of `X` has Krull dimension `d`. This is the notion of
Katz and Mazur, *Arithmetic Moduli of Elliptic Curves*, 4.12, as corrected in their Notes Added in
Proof: since a given dimension is not an étale-local condition, it is imposed on every nonempty
open. -/
structure IsRegularOfDim (X : Scheme.{u}) (d : ℕ) : Prop where
  /-- The scheme is nonempty. -/
  nonempty : Nonempty X
  /-- Every local ring is regular. -/
  isRegularLocalRing_stalk (x : X) : IsRegularLocalRing (X.presheaf.stalk x)
  /-- Every nonempty open has Krull dimension `d`. -/
  topologicalKrullDim_eq (U : X.Opens) : (U : Set X).Nonempty → topologicalKrullDim U = d

variable {X Y : Scheme.{u}} {d : ℕ}

/-- The dimension condition of `IsRegularOfDim` in terms of local rings: every nonempty open has
local rings whose dimensions have supremum `d`. -/
theorem IsRegularOfDim.iSup_ringKrullDim_stalk_eq (h : IsRegularOfDim X d) (U : X.Opens)
    (hU : (U : Set X).Nonempty) : ⨆ x : U, ringKrullDim (X.presheaf.stalk x) = d := by
  rw [← topologicalKrullDim_opens_eq_iSup_ringKrullDim_stalk, h.topologicalKrullDim_eq U hU]

/-- **Regularity of dimension `d` ascends along étale morphisms.** If `f : X ⟶ Y` is étale, `X`
is nonempty and `Y` is regular of dimension `d`, then `X` is regular of dimension `d`. -/
theorem IsRegularOfDim.of_etale (f : X ⟶ Y) [Etale f] [Nonempty X] (h : IsRegularOfDim Y d) :
    IsRegularOfDim X d where
  nonempty := ‹_›
  isRegularLocalRing_stalk x :=
    (isRegularLocalRing_stalk_iff_of_etale f x).mp (h.isRegularLocalRing_stalk (f x))
  topologicalKrullDim_eq U hU := by
    -- the image of `U` is a nonempty open of `Y` with the same local dimensions as `U`
    rw [topologicalKrullDim_opens_eq_iSup_ringKrullDim_stalk,
      iSup_ringKrullDim_stalk_eq_of_etale f U ⟨f '' U, f.isOpenMap _ U.isOpen⟩ rfl fun x ↦ ?_]
    · exact h.iSup_ringKrullDim_stalk_eq _ (hU.image _)
    · have := h.isRegularLocalRing_stalk (f x)
      exact (isNoetherianRing_stalk_iff_of_flat_of_locallyOfFiniteType f x).mp inferInstance

/-- **Regularity of dimension `d` descends along étale surjective morphisms.** If `f : X ⟶ Y` is
étale and surjective and `X` is regular of dimension `d`, then `Y` is regular of dimension `d`. -/
theorem IsRegularOfDim.of_etale_of_surjective (f : X ⟶ Y) [Etale f] [Surjective f]
    (h : IsRegularOfDim X d) : IsRegularOfDim Y d where
  nonempty := h.nonempty.map f
  isRegularLocalRing_stalk y := by
    obtain ⟨x, rfl⟩ := f.surjective y
    exact (isRegularLocalRing_stalk_iff_of_etale f x).mpr (h.isRegularLocalRing_stalk x)
  topologicalKrullDim_eq V hV := by
    -- the preimage of `V` is a nonempty open of `X` with the same local dimensions as `V`
    have hV' : ((f ⁻¹ᵁ V : X.Opens) : Set X).Nonempty := by
      obtain ⟨y, hy⟩ := hV
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, hy⟩
    rw [topologicalKrullDim_opens_eq_iSup_ringKrullDim_stalk,
      ← iSup_ringKrullDim_stalk_eq_of_etale f (f ⁻¹ᵁ V) V (Set.image_preimage_eq _ f.surjective)
        fun x ↦ have := h.isRegularLocalRing_stalk x; inferInstance]
    exact h.iSup_ringKrullDim_stalk_eq _ hV'

/-- **Regularity of dimension `d` is invariant under étale surjective morphisms**: if
`f : X ⟶ Y` is étale and surjective, then `X` is regular of dimension `d` exactly when `Y` is. -/
theorem isRegularOfDim_iff_of_etale_of_surjective (f : X ⟶ Y) [Etale f] [Surjective f] :
    IsRegularOfDim X d ↔ IsRegularOfDim Y d := by
  refine ⟨IsRegularOfDim.of_etale_of_surjective f, fun h ↦ ?_⟩
  have : Nonempty X := h.nonempty.map fun y ↦ (f.surjective y).choose
  exact h.of_etale f

end TauCeti.AlgebraicGeometry
