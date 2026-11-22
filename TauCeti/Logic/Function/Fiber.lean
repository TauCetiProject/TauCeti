/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Finite.Lattice

/-!
# Fibres of a map over a base

For `p : E → X`, the fibre of `p` over `x` is the set `p ⁻¹' {x}`. This file collects the
elementary constructions on such fibres that the covering-space development uses. None needs a
topology, so they are stated for bare functions and equivalences; a `ContinuousMap` or a
`Homeomorph` is applied through its underlying function or equivalence.

* `Function.fiberMap`: a map `f : E → F` commuting with the projections to `X` restricts to the
  fibres over each point. It is `Set.MapsTo.restrict` for the fibre inclusion, so its application,
  identity and composition laws are the generic `Subtype.map` ones.
* `Equiv.compFiberEquiv`: relabelling the base along `h : X ≃ Y` identifies the fibre of `h ∘ p`
  over `y` with the fibre of `p` over `h.symm y`. It is the identity on underlying points.

## Main declarations

* `Set.finite_preimage_of_subset_iUnion`: a finite target has finite preimage under a
  finite cover with injectivity only on the portions lying over that target.
* `Set.finite_fiber_of_subset_iUnion`: the single-target specialization.
* `Function.mapsTo_fiber`: a map over `X` sends each fibre into the corresponding fibre.
* `Function.fiberMap`: the restriction of a map over `X` to the fibre over `x`.
* `Equiv.compFiberEquiv`: the relabelling of fibres under an equivalence of bases.
* `Equiv.fiberEquivOfPreimage`: an equivalence onto the preimage of a subset, commuting with
  projections, identifies the fibres over points of that subset. This transfers sheet counts
  from local models to a map defined by gluing.
-/

public section

namespace Function

variable {E F G X : Type*} {p : E → X} {q : F → X} {r : G → X}

/-- A map over `X` sends the fibre over `x` into the fibre over `x`. -/
theorem mapsTo_fiber (f : E → F) (hf : q ∘ f = p) (x : X) :
    Set.MapsTo f (p ⁻¹' {x}) (q ⁻¹' {x}) := by
  rw [← hf, Set.preimage_comp]
  exact Set.mapsTo_preimage f _

/-- The restriction of a map over `X` to the fibre over `x`. -/
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
-- Not `@[simp]`: on the left-hand side the intermediate projection `q` and the hypotheses `hf`,
-- `hg` occur only inside the compatibility proof, which `simp` cannot use to instantiate them, so
-- `simpNF` rejects the annotation as a rule that never fires.
theorem fiberMap_comp_apply (f : E → F) (g : F → G) (hf : q ∘ f = p) (hg : r ∘ g = q) (x : X)
    (e : p ⁻¹' {x}) :
    fiberMap (g ∘ f) (by rw [← hf, ← hg, Function.comp_assoc]) x e =
      fiberMap g hg x (fiberMap f hf x e) :=
  (Subtype.map_comp f (mapsTo_fiber f hf x) g (mapsTo_fiber g hg x)).symm

/-- An involution over the base restricts to an involution of each fibre. -/
theorem fiberMap_fiberMap_of_involutive {f : E → E} (hff : Involutive f) (hf : p ∘ f = p)
    (x : X) (e : p ⁻¹' {x}) :
    fiberMap f hf x (fiberMap f hf x e) = e :=
  Subtype.ext (by simp only [fiberMap_apply_coe]; exact hff e)

/-- An involution over the base is injective on each fibre. -/
theorem injective_fiberMap_of_involutive {f : E → E} (hff : Involutive f) (hf : p ∘ f = p)
    (x : X) : Injective (fiberMap f hf x) :=
  LeftInverse.injective (fiberMap_fiberMap_of_involutive hff hf x)

/-- A map over the base without fixed points has no fixed points on any fibre. -/
theorem fiberMap_ne_self {f : E → E} (hfix : ∀ e, f e ≠ e) (hf : p ∘ f = p) (x : X)
    (e : p ⁻¹' {x}) : fiberMap f hf x e ≠ e :=
  fun h ↦ hfix e ((fiberMap_apply_coe f hf x e).symm.trans (congrArg Subtype.val h))

end Function

namespace Equiv

/-- An equivalence onto `p ⁻¹' U` that commutes with the projections identifies the fibres over
each `y ∈ U`. No topology or finiteness assumption is needed. -/
def fiberEquivOfPreimage {A X Y : Type*} {p : X → Y} {q : A → Y} {U : Set Y}
    (k : A ≃ p ⁻¹' U) (hk : ∀ a, p (k a).val = q a) {y : Y} (hy : y ∈ U) :
    q ⁻¹' {y} ≃ p ⁻¹' {y} :=
  (k.subtypeEquiv (p := fun a ↦ q a = y) (q := fun x ↦ p x.val = y)
    (fun a ↦ by rw [hk a])).trans
    (subtypeSubtypeEquivSubtype (p := fun x ↦ p x ∈ U) (q := fun x ↦ p x = y)
      fun hx ↦ hx.symm ▸ hy)

@[simp]
theorem fiberEquivOfPreimage_apply_coe {A X Y : Type*} {p : X → Y} {q : A → Y}
    {U : Set Y} (k : A ≃ p ⁻¹' U) (hk : ∀ a, p (k a).val = q a) {y : Y}
    (hy : y ∈ U) (a : q ⁻¹' {y}) :
    (k.fiberEquivOfPreimage hk hy a : X) = (k a).val :=
  (rfl)

@[simp]
theorem fiberEquivOfPreimage_symm_apply_coe {A X Y : Type*} {p : X → Y} {q : A → Y}
    {U : Set Y} (k : A ≃ p ⁻¹' U) (hk : ∀ a, p (k a).val = q a) {y : Y}
    (hy : y ∈ U) (x : p ⁻¹' {y}) :
    ((k.fiberEquivOfPreimage hk hy).symm x : A) =
      k.symm ⟨x, by
        have hx : p x = y := x.property
        rw [Set.mem_preimage, hx]
        exact hy⟩ :=
  (rfl)

variable {E X Y : Type*} {p : E → X}

/-- Postcomposing a map with an equivalence of the base relabels its fibres: the fibre of `h ∘ p`
over `y` is the fibre of `p` over `h.symm y`. -/
def compFiberEquiv (h : X ≃ Y) (y : Y) : (h ∘ p) ⁻¹' {y} ≃ p ⁻¹' {h.symm y} :=
  Set.equivOfEq <| by ext; simp [h.eq_symm_apply]

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

/-- A finite target has finite preimage if that preimage is covered by finitely many
pieces on whose portions over the target the function is injective. -/
theorem Set.finite_preimage_of_subset_iUnion {α β κ : Type*} [Finite κ] {f : α → β}
    {t : Set β} (ht : t.Finite) {S : κ → Set α} (hS : f ⁻¹' t ⊆ ⋃ k, S k)
    (hf : ∀ k, Set.InjOn f (S k ∩ f ⁻¹' t)) : (f ⁻¹' t).Finite := by
  have hpiece (k : κ) : (S k ∩ f ⁻¹' t).Finite :=
    Set.Finite.of_injOn (f := f) (fun _ hx => hx.2) (hf k) ht
  apply (Set.finite_iUnion hpiece).subset
  rw [← Set.iUnion_inter]
  exact fun x hx => ⟨hS hx, hx⟩

/-- A fiber covered by finitely many pieces is finite when the function is injective
on the part of each piece lying in that fiber. No condition is imposed elsewhere. -/
theorem Set.finite_fiber_of_subset_iUnion {α β κ : Type*} [Finite κ] {f : α → β}
    {S : κ → Set α} (w : β) (hS : f ⁻¹' {w} ⊆ ⋃ k, S k)
    (hf : ∀ k, Set.InjOn f (S k ∩ f ⁻¹' {w})) : Finite {x : α // f x = w} :=
  (Set.finite_preimage_of_subset_iUnion (Set.finite_singleton w) hS hf).to_subtype
