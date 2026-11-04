/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Descending homotopies along quotient maps

Let `q : X → Y` be a quotient map. A continuous map out of `X` which is constant on the fibres of
`q` descends to a continuous map out of `Y` (`Topology.IsQuotientMap.lift`). The same holds for
homotopies: a homotopy `F : I × X → Z` which, at every time, is constant on the fibres of `q`
descends to a homotopy `I × Y → Z` (`Topology.IsQuotientMap.liftHomotopy`). The continuity of the
descended homotopy is the point: the product `I × q : I × X → I × Y` is again a quotient map,
because the unit interval is locally compact (`Topology.IsQuotientMap.continuous_lift_prod_right`).

This is how deformations of a space which preserve an equivalence relation are pushed down to
the quotient, for instance in the proof that collapsing a contractible subspace with the
homotopy extension property is a homotopy equivalence.

## Main declarations

* `Topology.IsQuotientMap.liftHomotopy`: a homotopy constant on the fibres of a quotient map
  descends to a homotopy between the descended end maps.
* `Topology.IsQuotientMap.liftHomotopy_apply`: the descended homotopy at `(t, q x)` is `F (t, x)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, proof of Proposition 0.17, where a deformation of `X` preserving a subspace `A` is
  passed to the quotient `X / A`.
-/

public section

noncomputable section

open ContinuousMap unitInterval

namespace Topology.IsQuotientMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {q : X → Y}

/-- A homotopy `F` between maps `f₀ f₁ : X → Z` which is constant on the fibres of a quotient map
`q : X → Y` at every time descends to a homotopy between maps `g₀ g₁ : Y → Z` with
`g₀ ∘ q = f₀` and `g₁ ∘ q = f₁`. Its value at `(t, q x)` is `F (t, x)`
(`Topology.IsQuotientMap.liftHomotopy_apply`). -/
def liftHomotopy (hq : IsQuotientMap q) {f₀ f₁ : C(X, Z)} (F : f₀.Homotopy f₁)
    (hF : ∀ (t : I) (x y : X), q x = q y → F (t, x) = F (t, y)) {g₀ g₁ : C(Y, Z)}
    (h₀ : ∀ x, g₀ (q x) = f₀ x) (h₁ : ∀ x, g₁ (q x) = f₁ x) : g₀.Homotopy g₁ where
  toFun p := F (p.1, Function.surjInv hq.surjective p.2)
  continuous_toFun := hq.continuous_lift_prod_right <| by
    refine F.continuous.congr fun p => hF _ _ _ ?_
    exact (Function.surjInv_eq hq.surjective (q p.2)).symm
  map_zero_left y := by
    simp only [Homotopy.apply_zero, ← h₀, Function.surjInv_eq hq.surjective y]
  map_one_left y := by
    simp only [Homotopy.apply_one, ← h₁, Function.surjInv_eq hq.surjective y]

@[simp]
theorem liftHomotopy_apply (hq : IsQuotientMap q) {f₀ f₁ : C(X, Z)} (F : f₀.Homotopy f₁)
    (hF : ∀ (t : I) (x y : X), q x = q y → F (t, x) = F (t, y)) {g₀ g₁ : C(Y, Z)}
    (h₀ : ∀ x, g₀ (q x) = f₀ x) (h₁ : ∀ x, g₁ (q x) = f₁ x) (t : I) (x : X) :
    hq.liftHomotopy F hF h₀ h₁ (t, q x) = F (t, x) :=
  hF t _ _ (Function.surjInv_eq hq.surjective (q x))

end Topology.IsQuotientMap
