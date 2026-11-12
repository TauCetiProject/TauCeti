/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.NAry
public import Mathlib.Logic.Equiv.Prod
public import TauCeti.Geometry.Neuromanifold.Transport

/-!
# Composition of realization maps

Two supplied realization maps `f : W → X → Y` and `g : V → Y → Z` compose to the model
`compose f g : W × V → X → Z`, whose parameters are pairs and which realizes `g v ∘ f w`.
This is the layer-by-layer reading of a network: each layer is itself a realization map, and
the network realizes the composite of the functions realized by its layers. No architecture
record is involved; the parameter space of the composite is the full product, and distinct
parameter pairs may realize the same function.

The realized functions of a composite are the pairwise composites of realized functions
(`realizedFunctions_compose`); more generally, so are those of any model whose parameters
are identified with pairs realizing such composites, possibly joined by a fixed map
(`realizedFunctions_eq_image2_of_equiv`). Composition is associative up to the canonical
reassociation `Equiv.prodAssoc` of parameter products, and the parameter-free identity
model `Function.const PUnit id` is a unit on both sides up to the product projections.

The composite follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
-/

public section

namespace TauCeti.Neuromanifold

universe u v w z t

variable {W : Type u} {X : Type v} {Y : Type w} {Z : Type z} {V U T : Type*}

/-- The composite of two realization maps: a parameter pair `(w, v)` realizes the function
`g v ∘ f w`, so that `f` is applied first. -/
def compose (f : W → X → Y) (g : V → Y → Z) : W × V → X → Z := fun p => g p.2 ∘ f p.1

/-- A parameter pair of the composite realizes the composite of the realized functions. -/
@[simp] theorem compose_apply (f : W → X → Y) (g : V → Y → Z) (p : W × V) :
    compose f g p = g p.2 ∘ f p.1 := (rfl)

/-- Evaluation of the composite model at an input. -/
@[simp] theorem compose_apply_apply (f : W → X → Y) (g : V → Y → Z) (p : W × V) (x : X) :
    compose f g p x = g p.2 (f p.1 x) := (rfl)

/-- The functions realized by a composite model are exactly the composites `b ∘ a` of a
function `a` realized by the first model and a function `b` realized by the second. -/
theorem realizedFunctions_compose (f : W → X → Y) (g : V → Y → Z) :
    realizedFunctions (compose f g) =
      Set.image2 (fun a b => b ∘ a) (realizedFunctions f) (realizedFunctions g) := by
  simp only [realizedFunctions_def, Set.image2_range, ← compose_apply]

/-- A model that, after an identification of its parameters with pairs, realizes the composites
`g p₂ ∘ a ∘ f p₁` realizes the composites of functions realized by `f` and `g` joined by `a`. This
is `realizedFunctions_compose` for the composite of `f` with `g` precomposed with `a`. -/
theorem realizedFunctions_eq_image2_of_equiv {P Y' : Type*} {F : P → X → Z} (e : P ≃ W × V)
    {f : W → X → Y} {g : V → Y' → Z} (a : Y → Y')
    (h : ∀ p₁ p₂, F (e.symm (p₁, p₂)) = g p₂ ∘ a ∘ f p₁) :
    realizedFunctions F =
      Set.image2 (fun f' g' => g' ∘ a ∘ f') (realizedFunctions f) (realizedFunctions g) := by
  have hc : F ∘ e.symm = compose f fun p₂ => g p₂ ∘ a := funext fun p =>
    (h p.1 p.2).trans (compose_apply f (fun p₂ => g p₂ ∘ a) p).symm
  rw [realizedFunctions_def, ← e.symm.surjective.range_comp, hc, ← realizedFunctions_def,
    realizedFunctions_compose, realizedFunctions_precomp, Set.image2_image_right]
  simp only [Function.comp_assoc]

/-- Composition of models is associative up to the canonical reassociation of parameter
products. -/
theorem compose_assoc (f : W → X → Y) (g : V → Y → Z) (h : U → Z → T) :
    compose (compose f g) h = compose f (compose g h) ∘ Equiv.prodAssoc W V U := (rfl)

/-- The two bracketings of a threefold composite realize the same functions. -/
theorem realizedFunctions_compose_assoc (f : W → X → Y) (g : V → Y → Z) (h : U → Z → T) :
    realizedFunctions (compose (compose f g) h) = realizedFunctions (compose f (compose g h)) := by
  rw [compose_assoc, realizedFunctions_def, realizedFunctions_def,
    (Equiv.prodAssoc W V U).surjective.range_comp]

/-- Precomposing with the parameter-free identity model forgets its trivial parameter. -/
@[simp] theorem const_id_compose (g : V → X → Y) :
    compose (Function.const PUnit.{t + 1} (id : X → X)) g = g ∘ Prod.snd := (rfl)

/-- Postcomposing with the parameter-free identity model forgets its trivial parameter. -/
@[simp] theorem compose_const_id (f : W → X → Y) :
    compose f (Function.const PUnit.{t + 1} (id : Y → Y)) = f ∘ Prod.fst := (rfl)

/-- Precomposing with the identity model does not change the realized functions. -/
theorem realizedFunctions_const_id_compose (g : V → X → Y) :
    realizedFunctions (compose (Function.const PUnit.{t + 1} (id : X → X)) g) =
      realizedFunctions g := by
  rw [const_id_compose, realizedFunctions_def, realizedFunctions_def,
    Prod.snd_surjective.range_comp]

/-- Postcomposing with the identity model does not change the realized functions. -/
theorem realizedFunctions_compose_const_id (f : W → X → Y) :
    realizedFunctions (compose f (Function.const PUnit.{t + 1} (id : Y → Y))) =
      realizedFunctions f := by
  rw [compose_const_id, realizedFunctions_def, realizedFunctions_def,
    Prod.fst_surjective.range_comp]

end TauCeti.Neuromanifold
