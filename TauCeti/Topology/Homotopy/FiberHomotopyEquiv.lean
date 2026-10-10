/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv

/-!
# Fibre homotopy equivalences

For maps `p : E → B` and `q : E' → B`, a **fibre homotopy equivalence** from `p` to `q` is a pair
of maps `f : E → E'` and `g : E' → E` over `B` (`q ∘ f = p`, `p ∘ g = q`) whose two composites are
homotopic to the identities through maps over `B` (`ContinuousMap.HomotopicWith` with the predicate
"over `B`").  Since every stage of such a homotopy maps each fibre into itself, a fibre homotopy
equivalence restricts to a homotopy equivalence of the fibres over each point
(`TauCeti.FiberHomotopyEquiv.fiber`).

## Main definitions

* `TauCeti.FiberHomotopyEquiv p q`: fibre homotopy equivalences from `p` to `q`.
* `TauCeti.fiberMap`: the map of fibres induced by a map over `B`.
* `TauCeti.FiberHomotopyEquiv.fiber`: the homotopy equivalence of the fibres over a point.
-/

public section

open ContinuousMap unitInterval

universe u u' u'' v

namespace TauCeti

variable {E : Type u} {E' : Type u'} {E'' : Type u''} {B : Type v} [TopologicalSpace E]
  [TopologicalSpace E'] [TopologicalSpace E''] [TopologicalSpace B]

/-- A **fibre homotopy equivalence** from `p : E → B` to `q : E' → B`: maps over `B` in both
directions whose composites are homotopic to the identities through maps over `B`. -/
structure FiberHomotopyEquiv (p : C(E, B)) (q : C(E', B)) where
  /-- The forward map, over `B`. -/
  toFun : C(E, E')
  /-- The backward map, over `B`. -/
  invFun : C(E', E)
  /-- The forward map lies over `B`. -/
  comp_toFun : q.comp toFun = p
  /-- The backward map lies over `B`. -/
  comp_invFun : p.comp invFun = q
  /-- The composite on `E` is homotopic to the identity through maps over `B`. -/
  left_inv : (invFun.comp toFun).HomotopicWith (.id E) fun f ↦ p.comp f = p
  /-- The composite on `E'` is homotopic to the identity through maps over `B`. -/
  right_inv : (toFun.comp invFun).HomotopicWith (.id E') fun f ↦ q.comp f = q

theorem apply_of_comp_eq {p : C(E, B)} {q : C(E', B)} {f : C(E, E')} (hf : q.comp f = p)
    {b : B} (e : {e // p e = b}) : q (f e) = b := by
  rw [← ContinuousMap.comp_apply, hf, e.2]

/-- The map of fibres over `b` induced by a map `f` over `B`. -/
def fiberMap {p : C(E, B)} {q : C(E', B)} (f : C(E, E')) (hf : q.comp f = p) (b : B) :
    C({e // p e = b}, {e' // q e' = b}) :=
  ⟨fun e ↦ ⟨f e, apply_of_comp_eq hf e⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp]
theorem coe_fiberMap {p : C(E, B)} {q : C(E', B)} (f : C(E, E')) (hf : q.comp f = p) (b : B)
    (e : {e // p e = b}) : (fiberMap f hf b e : E') = f e :=
  (rfl)

theorem fiberMap_comp {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)} (f : C(E, E'))
    (g : C(E', E'')) (hf : q.comp f = p) (hg : r.comp g = q) (b : B) :
    (fiberMap g hg b).comp (fiberMap f hf b) =
      fiberMap (g.comp f) (by rw [← ContinuousMap.comp_assoc, hg, hf]) b :=
  (rfl)

theorem fiberMap_id {p : C(E, B)} (b : B) :
    fiberMap (.id E) (ContinuousMap.comp_id p) b = .id _ :=
  (rfl)

theorem apply_homotopyWith {p : C(E, B)} {f₀ f₁ : C(E, E)}
    (H : HomotopyWith f₀ f₁ fun f ↦ p.comp f = p) (t : I) (e : E) : p (H (t, e)) = p e :=
  congr($(H.prop' t) e)

/-- A homotopy through maps over `B` restricts to a homotopy of the induced maps of the fibres. -/
def fiberHomotopy {p : C(E, B)} {f₀ f₁ : C(E, E)}
    (H : HomotopyWith f₀ f₁ fun f ↦ p.comp f = p) (h₀ : p.comp f₀ = p) (h₁ : p.comp f₁ = p)
    (b : B) : Homotopy (fiberMap f₀ h₀ b) (fiberMap f₁ h₁ b) where
  toFun y := ⟨H (y.1, y.2), (apply_homotopyWith H y.1 y.2).trans y.2.2⟩
  continuous_toFun := (H.continuous.comp (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left e := Subtype.ext (H.apply_zero e)
  map_one_left e := Subtype.ext (H.apply_one e)

namespace FiberHomotopyEquiv

variable {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q)

/-- A fibre homotopy equivalence restricts to a **homotopy equivalence of the fibres** over each
point of the base. -/
def fiber (b : B) : HomotopyEquiv {e // p e = b} {e' // q e' = b} where
  toFun := fiberMap Φ.toFun Φ.comp_toFun b
  invFun := fiberMap Φ.invFun Φ.comp_invFun b
  left_inv := by
    rw [fiberMap_comp, ← fiberMap_id b]
    exact Φ.left_inv.map fun H ↦ fiberHomotopy H _ _ b
  right_inv := by
    rw [fiberMap_comp, ← fiberMap_id b]
    exact Φ.right_inv.map fun H ↦ fiberHomotopy H _ _ b

@[simp]
theorem coe_fiber_apply (b : B) (e : {e // p e = b}) : (Φ.fiber b e : E') = Φ.toFun e :=
  (rfl)

end FiberHomotopyEquiv

end TauCeti
