/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticallyDominant

/-!
# Descent of geometric properties along surjective morphisms

A property of the geometric fibres of a morphism `g : Y ⟶ Z`, in the sense of Mathlib's
`AlgebraicGeometry.geometrically P`, can be checked after base change along any surjective
morphism `f : X ⟶ Z`, provided the property `P` of schemes descends along faithfully flat
quasi-compact morphisms. No flatness of `f` is needed: given a field point `Spec K ⟶ Z`, choose a
point of `X ×_Z Spec K`, with residue field `M`. The base change of `Y` to `M` is a geometric fibre
of `X ×_Z Y ⟶ X`, and it maps faithfully flatly onto the base change of `Y` to `K`.

Reducedness descends along flat surjective quasi-compact morphisms, which are scheme-theoretically
dominant, and irreducibility descends along every surjective continuous map. Hence geometric
reducedness, geometric irreducibility and geometric integrality descend along surjective
morphisms. For a field extension `K / k` this says that a `k`-scheme is geometrically integral
as soon as its base change to `K` is.

## Main declarations

* `AlgebraicGeometry.geometrically_descendsAlong_surjective`: `geometrically P` descends along
  surjective morphisms whenever `P` descends along faithfully flat quasi-compact morphisms.
* `AlgebraicGeometry.GeometricallyReduced.descendsAlong_surjective`,
  `AlgebraicGeometry.GeometricallyIrreducible.descendsAlong_surjective` and
  `AlgebraicGeometry.GeometricallyIntegral.descendsAlong_surjective`: the instances for geometric
  reducedness, irreducibility and integrality.

## References

* The Stacks Project, Chapter *Varieties*, Sections *Geometrically reduced schemes*,
  *Geometrically irreducible schemes* and *Geometrically integral schemes*, for the case of a
  field extension.
-/

public section

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

universe u

/-- **Geometric properties descend along surjective morphisms.** If a property `P` of schemes
descends along faithfully flat quasi-compact morphisms, then `geometrically P` descends along
surjective morphisms: for a surjective `f : X ⟶ Z` and any `g : Y ⟶ Z`, if the base change
`X ×_Z Y ⟶ X` has geometric fibres satisfying `P`, so does `g`. -/
theorem geometrically_descendsAlong_surjective (P : ObjectProperty Scheme.{u})
    (hP : ∀ {W V : Scheme.{u}} (p : W ⟶ V) [Flat p] [Surjective p] [QuasiCompact p], P W → P V) :
    (geometrically P).DescendsAlong @Surjective := by
  refine ⟨fun {A X Y Z fst snd f g} h (hf : Surjective f) hfst K _ y W a b hW ↦ ?_⟩
  -- A point of `X ×_Z Spec K`, with residue field `M`, gives a common extension of the residue
  -- fields of `X` and of `Spec K`.
  obtain ⟨t, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Spec (.of K)))
  let m := (pullback f y).fromSpecResidueField t
  let u := m ≫ pullback.snd f y
  let v := m ≫ pullback.fst f y
  have huv : u ≫ y = v ≫ f := by simp [u, v, pullback.condition]
  -- The base change of `W` to `M` is a geometric fibre of `fst`.
  have hW' : IsPullback (pullback.fst b u ≫ a) (pullback.snd b u) g (v ≫ f) :=
    huv ▸ (IsPullback.of_hasPullback b u).paste_horiz hW
  let k := h.flip.lift (pullback.fst b u ≫ a) (pullback.snd b u ≫ v) (by simp [hW'.w])
  have hk : IsPullback k (pullback.snd b u) fst v :=
    IsPullback.of_right (by simpa [k] using hW') (by simp [k]) h.flip
  -- It maps faithfully flatly onto `W`, by base change of `Spec M ⟶ Spec K`.
  exact hP (pullback.fst b u) (hfst _ _ _ hk)

/-- Geometric reducedness descends along surjective morphisms. -/
instance GeometricallyReduced.descendsAlong_surjective :
    DescendsAlong @GeometricallyReduced.{u} @Surjective := by
  rw [GeometricallyReduced.eq_geometrically]
  exact geometrically_descendsAlong_surjective _ fun p _ _ _ _ ↦
    IsSchemeTheoreticallyDominant.isReduced p

/-- Geometric irreducibility descends along surjective morphisms. -/
instance GeometricallyIrreducible.descendsAlong_surjective :
    DescendsAlong @GeometricallyIrreducible.{u} @Surjective := by
  rw [GeometricallyIrreducible.eq_geometrically]
  exact geometrically_descendsAlong_surjective _ fun p _ _ _ _ ↦
    p.surjective.irreducibleSpace p.continuous

/-- Geometric integrality descends along surjective morphisms. In particular a scheme over a
field `k` is geometrically integral if its base change to some extension field of `k` is. -/
instance GeometricallyIntegral.descendsAlong_surjective :
    DescendsAlong @GeometricallyIntegral.{u} @Surjective := by
  rw [GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible]
  exact DescendsAlong.inf

end AlgebraicGeometry
