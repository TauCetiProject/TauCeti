/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.EquivariantTransport
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Pullback.Basic

/-!
# Equivariant transport of a pulled-back lift

For an equivariant lift `L` over `Γ` and a functor `ψ : Λ ⥤ Γ`, the transport functors of the
pullback `L.pullback ψ` and their isomorphisms commuting with the actions are those of `L` along
the image of `ψ`. Consequently the equivariant transport of `L.pullback ψ` along an arrow `g` of
`Λ`, the strong transformation
`(L.pullback ψ).normalizedTransport.transportStrongTrans g : actions (ψ.obj l) ⟶ actions (ψ.obj l')`
of `TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.EquivariantTransport`, is the
equivariant transport of `L` along `ψ.map g`. This is the compatibility of the descended lift with
the prescribed fiber actions.

## Main statements

* `TauCeti.EquivariantGroupoidLift.pullback_normalizedTransport_transportStrongTrans`: the
  equivariant transport of `L.pullback ψ` along `g` is that of `L` along `ψ.map g`.

## References

* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007), §1.3: families of local categories over
  the groupoid of local Langlands parameters, with their loop group actions.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-- The equivariant transport of the pullback of a lift `L` along `ψ : Λ ⥤ Γ` is the equivariant
transport of `L` along the image of `ψ`. -/
@[simp]
lemma pullback_normalizedTransport_transportStrongTrans (L : EquivariantGroupoidLift Γ actions)
    {Λ : Type*} [Category Λ] (ψ : Λ ⥤ Γ) {l l' : Λ} (g : l ⟶ l') :
    (L.pullback ψ).normalizedTransport.transportStrongTrans g =
      L.normalizedTransport.transportStrongTrans (ψ.map g) := by
  -- The transport functors of the pullback are definitionally those of `L` along `ψ.map g`, so
  -- only the commuting isomorphisms need rewriting.
  simp only [NormalizedTransport.transportStrongTrans, normalizedTransport_transportCommIso,
    pullback_transportCommIso]
  rfl

end TauCeti.EquivariantGroupoidLift
