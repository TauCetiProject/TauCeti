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
* `TauCeti.FiberHomotopyEquiv.refl`, `TauCeti.FiberHomotopyEquiv.symm`,
  `TauCeti.FiberHomotopyEquiv.trans`: identity, symmetry, and composition of fibre homotopy
  equivalences.
* `TauCeti.FiberHomotopyEquiv.ofHomeomorph`: a homeomorphism over `B` as a fibre homotopy
  equivalence.
* `TauCeti.FiberHomotopyEquiv.compBase`: postcomposing the base projections with `b : C(B, B')`.
* `TauCeti.FiberHomotopyEquiv.fiber`: the homotopy equivalence of the fibres over a point.
* `TauCeti.FiberHomotopyEquiv.toHomotopyEquiv`: the underlying homotopy equivalence of the total
  spaces.

## Main results

* `ContinuousMap.homotopic_of_fiber`: a homotopy of maps to the total space staying over one point
  is a homotopy of maps into the fiber.
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

section

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

@[simp]
theorem coe_fiber_symm_apply (b : B) (e' : {e' // q e' = b}) :
    ((Φ.fiber b).symm e' : E) = Φ.invFun e' :=
  (rfl)

/-- Forgetting that the maps and homotopies lie over `B`, a fibre homotopy equivalence is a
**homotopy equivalence of the total spaces**. -/
def toHomotopyEquiv : HomotopyEquiv E E' where
  toFun := Φ.toFun
  invFun := Φ.invFun
  left_inv := ⟨Φ.left_inv.some.toHomotopy⟩
  right_inv := ⟨Φ.right_inv.some.toHomotopy⟩

@[simp]
theorem toHomotopyEquiv_apply (e : E) : Φ.toHomotopyEquiv e = Φ.toFun e :=
  (rfl)

@[simp]
theorem toHomotopyEquiv_symm_apply (e' : E') : Φ.toHomotopyEquiv.symm e' = Φ.invFun e' :=
  (rfl)

end

/-- The identity fibre homotopy equivalence of `p : C(E, B)`. -/
def refl (p : C(E, B)) : FiberHomotopyEquiv p p where
  toFun := .id E
  invFun := .id E
  comp_toFun := p.comp_id
  comp_invFun := p.comp_id
  left_inv := ⟨(HomotopyWith.refl (.id E) p.comp_id).cast (ContinuousMap.comp_id _).symm rfl⟩
  right_inv := ⟨(HomotopyWith.refl (.id E) p.comp_id).cast (ContinuousMap.comp_id _).symm rfl⟩

@[simp]
theorem refl_toFun (p : C(E, B)) : (refl p).toFun = .id E :=
  (rfl)

@[simp]
theorem refl_invFun (p : C(E, B)) : (refl p).invFun = .id E :=
  (rfl)

/-- Symmetry of fibre homotopy equivalences. -/
@[symm]
def symm {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) : FiberHomotopyEquiv q p where
  toFun := Φ.invFun
  invFun := Φ.toFun
  comp_toFun := Φ.comp_invFun
  comp_invFun := Φ.comp_toFun
  left_inv := Φ.right_inv
  right_inv := Φ.left_inv

@[simp]
theorem symm_toFun {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) :
    Φ.symm.toFun = Φ.invFun :=
  (rfl)

@[simp]
theorem symm_invFun {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) :
    Φ.symm.invFun = Φ.toFun :=
  (rfl)

@[simp]
theorem symm_symm {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) :
    Φ.symm.symm = Φ :=
  (rfl)

/-- A homeomorphism `e : E ≃ₜ E'` commuting with the projections to `B` is a fibre homotopy
equivalence. -/
def ofHomeomorph {p : C(E, B)} {q : C(E', B)} (e : E ≃ₜ E')
    (he : q.comp (e : C(E, E')) = p) : FiberHomotopyEquiv p q where
  toFun := e
  invFun := e.symm
  comp_toFun := he
  comp_invFun := ContinuousMap.ext fun x ↦ by simp [← he]
  left_inv :=
    ⟨(HomotopyWith.refl (.id E) p.comp_id).cast
      (ContinuousMap.ext fun x ↦ (e.symm_apply_apply x).symm) rfl⟩
  right_inv :=
    ⟨(HomotopyWith.refl (.id E') q.comp_id).cast
      (ContinuousMap.ext fun x ↦ (e.apply_symm_apply x).symm) rfl⟩

@[simp]
theorem ofHomeomorph_toFun {p : C(E, B)} {q : C(E', B)} (e : E ≃ₜ E')
    (he : q.comp (e : C(E, E')) = p) : (ofHomeomorph e he).toFun = (e : C(E, E')) :=
  (rfl)

@[simp]
theorem ofHomeomorph_invFun {p : C(E, B)} {q : C(E', B)} (e : E ≃ₜ E')
    (he : q.comp (e : C(E, E')) = p) : (ofHomeomorph e he).invFun = (e.symm : C(E', E)) :=
  (rfl)

private theorem homotopicWith_comp_conj {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)}
    (Φ : FiberHomotopyEquiv p q) (Ψ : FiberHomotopyEquiv q r) :
    ((Φ.invFun.comp Ψ.invFun).comp (Ψ.toFun.comp Φ.toFun)).HomotopicWith (.id E)
      fun f ↦ p.comp f = p := by
  refine (?_ : HomotopicWith _ (Φ.invFun.comp Φ.toFun) _).trans Φ.left_inv
  obtain ⟨H⟩ := Ψ.left_inv
  exact ⟨{
    toFun := fun x ↦ Φ.invFun (H (x.1, Φ.toFun x.2))
    continuous_toFun := by fun_prop
    map_zero_left := fun _ ↦ by simp [ContinuousMap.comp_apply]
    map_one_left := fun _ ↦ by simp [ContinuousMap.comp_apply]
    prop' := fun t ↦ ContinuousMap.ext fun e ↦ by
      have h1 : p (Φ.invFun (H (t, Φ.toFun e))) = q (H (t, Φ.toFun e)) :=
        congr($(Φ.comp_invFun) (H (t, Φ.toFun e)))
      have h2 : q (H (t, Φ.toFun e)) = q (Φ.toFun e) := apply_homotopyWith H t (Φ.toFun e)
      have h3 : q (Φ.toFun e) = p e := congr($(Φ.comp_toFun) e)
      exact h1.trans (h2.trans h3) }⟩

/-- Composition of fibre homotopy equivalences over `B`. -/
@[trans]
def trans {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)}
    (Φ : FiberHomotopyEquiv p q) (Ψ : FiberHomotopyEquiv q r) : FiberHomotopyEquiv p r where
  toFun := Ψ.toFun.comp Φ.toFun
  invFun := Φ.invFun.comp Ψ.invFun
  comp_toFun := by rw [← ContinuousMap.comp_assoc, Ψ.comp_toFun, Φ.comp_toFun]
  comp_invFun := by rw [← ContinuousMap.comp_assoc, Φ.comp_invFun, Ψ.comp_invFun]
  left_inv := homotopicWith_comp_conj Φ Ψ
  right_inv := homotopicWith_comp_conj Ψ.symm Φ.symm

@[simp]
theorem trans_toFun {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)}
    (Φ : FiberHomotopyEquiv p q) (Ψ : FiberHomotopyEquiv q r) :
    (Φ.trans Ψ).toFun = Ψ.toFun.comp Φ.toFun :=
  (rfl)

@[simp]
theorem trans_invFun {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)}
    (Φ : FiberHomotopyEquiv p q) (Ψ : FiberHomotopyEquiv q r) :
    (Φ.trans Ψ).invFun = Φ.invFun.comp Ψ.invFun :=
  (rfl)

/-- Postcomposing both base projections with `b : C(B, B')` carries a fibre homotopy equivalence
over `B` to one over `B'`. -/
def compBase {B' : Type*} [TopologicalSpace B'] {p : C(E, B)} {q : C(E', B)}
    (b : C(B, B')) (Φ : FiberHomotopyEquiv p q) :
    FiberHomotopyEquiv (b.comp p) (b.comp q) where
  toFun := Φ.toFun
  invFun := Φ.invFun
  comp_toFun := by rw [ContinuousMap.comp_assoc, Φ.comp_toFun]
  comp_invFun := by rw [ContinuousMap.comp_assoc, Φ.comp_invFun]
  left_inv := Φ.left_inv.map fun H ↦
    { toHomotopy := H.toHomotopy
      prop' := fun t ↦ ContinuousMap.ext fun e ↦ congrArg b (apply_homotopyWith H t e) }
  right_inv := Φ.right_inv.map fun H ↦
    { toHomotopy := H.toHomotopy
      prop' := fun t ↦ ContinuousMap.ext fun e ↦ congrArg b (apply_homotopyWith H t e) }

@[simp]
theorem compBase_toFun {B' : Type*} [TopologicalSpace B'] {p : C(E, B)} {q : C(E', B)}
    (b : C(B, B')) (Φ : FiberHomotopyEquiv p q) :
    (Φ.compBase b).toFun = Φ.toFun :=
  (rfl)

@[simp]
theorem compBase_invFun {B' : Type*} [TopologicalSpace B'] {p : C(E, B)} {q : C(E', B)}
    (b : C(B, B')) (Φ : FiberHomotopyEquiv p q) :
    (Φ.compBase b).invFun = Φ.invFun :=
  (rfl)

end FiberHomotopyEquiv

end TauCeti

namespace ContinuousMap

/-- A homotopy of maps to the total space of a map `p`, staying over a fixed point `b`, gives a
homotopy of maps into the fiber over `b`. -/
theorem homotopic_of_fiber {E B Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Y] {p : E → B} {b : B} (f g : C(Y, p ⁻¹' {b}))
    (K : C(Y × I, E)) (h₀ : ∀ y, K (y, 0) = f y) (h₁ : ∀ y, K (y, 1) = g y)
    (hK : ∀ y s, p (K (y, s)) = b) : f.Homotopic g :=
  ⟨{ toFun := fun z ↦ ⟨K (z.2, z.1), hK z.2 z.1⟩
     continuous_toFun := by fun_prop
     map_zero_left := fun y ↦ Subtype.ext (h₀ y)
     map_one_left := fun y ↦ Subtype.ext (h₁ y) }⟩

end ContinuousMap

