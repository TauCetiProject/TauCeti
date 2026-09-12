/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Set

/-!
# Fibres of a map over a base

For `p : E → X`, the fibre of `p` over `x` is the set `p ⁻¹' {x}`. This file collects the two
elementary constructions on such fibres that the covering-space development uses, each stated at
the level where it is actually true: a bare function for the first, a bare equivalence for the
second.

* `Function.fiberMap`: a map `f : E → F` commuting with the projections to `X` restricts to the
  fibres over each point. It is `Set.MapsTo.restrict` for the fibre inclusion, so its application,
  identity and composition laws are the generic `Subtype.map` ones.
* `Equiv.compFiberEquiv`: relabelling the base along `h : X ≃ Y` identifies the fibre of `h ∘ p`
  over `y` with the fibre of `p` over `h.symm y`.

Together they cover the two ways the fibres of a map vary: `Function.fiberMap` moves along a map
over a fixed base and carries the identity and composition laws it inherits from `Subtype.map`,
while `Equiv.compFiberEquiv` transports fibres along a change of base and is pinned down on points
by its coercion lemmas. Neither uses a topology, so both are stated for a bare function and a bare
equivalence; a `ContinuousMap` or a `Homeomorph` is applied through its underlying function or
equivalence.

## Main declarations

* `Function.mapsTo_fiber`: a map over `X` sends each fibre into the corresponding fibre.
* `Function.fiberMap`: the restriction of a map over `X` to the fibre over `x`.
* `Equiv.compFiberEquiv`: the relabelling of fibres under an equivalence of bases.
-/

public section

namespace Function

variable {E F G X : Type*} {p : E → X} {q : F → X} {r : G → X}

/-- A map over `X` sends the fibre over `x` into the fibre over `x`. -/
theorem mapsTo_fiber (f : E → F) (hf : q ∘ f = p) (x : X) :
    Set.MapsTo f (p ⁻¹' {x}) (q ⁻¹' {x}) := fun e he ↦ by
  rw [Set.mem_preimage, Set.mem_singleton_iff]
  have hpe : p e = x := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using he
  simpa only [Function.comp_apply] using (congrFun hf e).trans hpe

/-- The restriction of a map over `X` to the fibre over `x`. -/
-- `@[expose]`, like the sibling `TauCeti.Deck.fiberMap`: the whole content of this definition is
-- that the underlying point of `fiberMap f hf x e` is `f e`, and consumers in other modules rely on
-- that reduction to line up path-lifting statements, which a non-exposed body cannot supply.
@[expose]
def fiberMap (f : E → F) (hf : q ∘ f = p) (x : X) : p ⁻¹' {x} → q ⁻¹' {x} :=
  (mapsTo_fiber f hf x).restrict f (p ⁻¹' {x}) (q ⁻¹' {x})

/-- On underlying points, restriction to a fibre applies the original map. -/
@[simp]
theorem fiberMap_apply_coe (f : E → F) (hf : q ∘ f = p) (x : X) (e : p ⁻¹' {x}) :
    (fiberMap f hf x e : F) = f e :=
  (mapsTo_fiber f hf x).val_restrict_apply e

/-- Restricting the identity map to a fibre gives the identity. -/
@[simp]
theorem fiberMap_id_apply (x : X) (e : p ⁻¹' {x}) :
    fiberMap (p := p) (q := p) id rfl x e = e :=
  congrFun (Subtype.map_id (h := mapsTo_fiber (q := p) id rfl x)) e

/-- Restriction to a fibre respects composition of maps over the base. -/
-- Not `@[simp]`: the left-hand side applies `fiberMap` to a compatibility proof built inline from
-- the composite, which is not in simp normal form, so `simpNF` rejects the annotation as a rule
-- that can never fire.
theorem fiberMap_comp_apply (f : E → F) (g : F → G) (hf : q ∘ f = p) (hg : r ∘ g = q) (x : X)
    (e : p ⁻¹' {x}) :
    fiberMap (g ∘ f) (by
      funext z
      exact (congrFun hg (f z)).trans (congrFun hf z)) x e =
      fiberMap g hg x (fiberMap f hf x e) :=
  (Subtype.map_comp f (mapsTo_fiber f hf x) g (mapsTo_fiber g hg x)).symm

end Function

namespace Equiv

variable {E X Y : Type*} {p : E → X}

/-- Postcomposing a map with an equivalence of the base relabels its fibres: the fibre of `h ∘ p`
over `y` is the fibre of `p` over `h.symm y`. -/
def compFiberEquiv (h : X ≃ Y) (y : Y) : (h ∘ p) ⁻¹' {y} ≃ p ⁻¹' {h.symm y} :=
  _root_.Set.equivOfEq <| Set.ext fun _ ↦ by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
    exact h.eq_symm_apply.symm

/-- On underlying points, the fibre equivalence for an equivalence of bases is the identity. -/
@[simp]
theorem compFiberEquiv_apply_coe (h : X ≃ Y) (y : Y) (e : (h ∘ p) ⁻¹' {y}) :
    (compFiberEquiv (p := p) h y e : E) = e :=
  (rfl)

/-- On underlying points, the inverse fibre equivalence for an equivalence of bases is the
identity. -/
@[simp]
theorem compFiberEquiv_symm_apply_coe (h : X ≃ Y) (y : Y) (e : p ⁻¹' {h.symm y}) :
    ((compFiberEquiv (p := p) h y).symm e : E) = e :=
  (rfl)

end Equiv
