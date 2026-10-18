/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.GenLoop.Map

/-!
# Homeomorphisms of spaces of generalized loops

Mathlib's bijection `genLoopEquivOfUnique` between the generalized loops indexed by a singleton and
the loop space `Ω X x` is continuous both ways for the compact-open topologies. A homeomorphism
`e : X ≃ₜ Y` with `e x = y` also induces, by postcomposition, a homeomorphism of the spaces of
generalized loops `Ω^ N X x ≃ₜ Ω^ N Y y`.

## Main declarations

* `GenLoop.homeomorphOfUnique`: `Ω^ N X x ≃ₜ Ω X x` for `N` a singleton.
* `Homeomorph.genLoopHomeomorph`: `Ω^ N X x ≃ₜ Ω^ N Y y` from `e : X ≃ₜ Y` with `e x = y`.
-/

public section

open scoped unitInterval Topology Topology.Homotopy

namespace GenLoop

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- Mathlib's bijection `genLoopEquivOfUnique` between the one-dimensional generalized loops at
`x` and the loop space `Ω X x`, upgraded to a homeomorphism for the compact-open topologies. -/
def homeomorphOfUnique (N : Type*) [Unique N] : Ω^ N X x ≃ₜ Ω X x where
  toEquiv := genLoopEquivOfUnique N
  continuous_toFun := Path.continuous_uncurry_iff.1 <|
    continuous_eval.comp (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd))
  continuous_invFun := by
    refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
    exact continuous_eval.comp
      (continuous_fst.prodMk ((continuous_apply default).comp continuous_snd))

@[simp]
theorem homeomorphOfUnique_apply (N : Type*) [Unique N] (p : Ω^ N X x) (t : I) :
    homeomorphOfUnique N p t = p fun _ => t :=
  by rw [homeomorphOfUnique.eq_1]; rfl

@[simp]
theorem homeomorphOfUnique_symm_apply (N : Type*) [Unique N] (γ : Ω X x) (t : I^N) :
    (homeomorphOfUnique N).symm γ t = γ (t default) :=
  by rw [homeomorphOfUnique.eq_1]; rfl

/-- The homeomorphism of `GenLoop.homeomorphOfUnique` is based: it carries the constant
generalized loop to the constant path. -/
@[simp]
theorem homeomorphOfUnique_const (N : Type*) [Unique N] :
    homeomorphOfUnique N (_root_.GenLoop.const : Ω^ N X x) = Path.refl x :=
  Path.ext (funext fun _ => rfl)

section Map

variable {Y : Type*} [TopologicalSpace Y] {y : Y}

/-- A homeomorphism `e : X ≃ₜ Y` with `e x = y` induces, by postcomposition, a homeomorphism of
the spaces of generalized loops `Ω^ N X x ≃ₜ Ω^ N Y y`. -/
def _root_.Homeomorph.genLoopHomeomorph (e : X ≃ₜ Y) (h : e x = y) : Ω^ N X x ≃ₜ Ω^ N Y y where
  toFun := map ⟨e, e.continuous⟩ h
  invFun := map ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm)
  left_inv p := _root_.GenLoop.ext _ _ fun t => by
    simp only [map_apply, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  right_inv p := _root_.GenLoop.ext _ _ fun t => by
    simp only [map_apply, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply]
  continuous_toFun := continuous_map _ h
  continuous_invFun := continuous_map _ _

/-- The inverse of `Homeomorph.genLoopHomeomorph e` is `Homeomorph.genLoopHomeomorph e.symm`. -/
theorem _root_.Homeomorph.genLoopHomeomorph_symm (e : X ≃ₜ Y) (h : e x = y) :
    (Homeomorph.genLoopHomeomorph e h : Ω^ N X x ≃ₜ Ω^ N Y y).symm =
      Homeomorph.genLoopHomeomorph e.symm (e.symm_apply_eq.mpr h.symm) := by
  rw [Homeomorph.genLoopHomeomorph, Homeomorph.genLoopHomeomorph]; rfl

@[simp]
theorem _root_.Homeomorph.genLoopHomeomorph_apply (e : X ≃ₜ Y) (h : e x = y) (p : Ω^ N X x)
    (t : I^N) :
    Homeomorph.genLoopHomeomorph e h p t = e (p t) :=
  map_apply ⟨e, e.continuous⟩ h p t

/-- The homeomorphism `Homeomorph.genLoopHomeomorph e` is based: it carries the constant
generalized loop to the constant generalized loop. -/
@[simp]
theorem _root_.Homeomorph.genLoopHomeomorph_const (e : X ≃ₜ Y) (h : e x = y) :
    Homeomorph.genLoopHomeomorph e h (_root_.GenLoop.const : Ω^ N X x) = _root_.GenLoop.const :=
  map_const ⟨e, e.continuous⟩ h

/-- The inverse of `Homeomorph.genLoopHomeomorph e` also carries the constant generalized loop to
the constant generalized loop. -/
@[simp]
theorem _root_.Homeomorph.genLoopHomeomorph_symm_const (e : X ≃ₜ Y) (h : e x = y) :
    (Homeomorph.genLoopHomeomorph e h).symm (_root_.GenLoop.const : Ω^ N Y y) =
      _root_.GenLoop.const :=
  ((Homeomorph.genLoopHomeomorph e h).symm_apply_eq.2
    (Homeomorph.genLoopHomeomorph_const e h).symm)

@[simp]
theorem _root_.Homeomorph.genLoopHomeomorph_symm_apply (e : X ≃ₜ Y) (h : e x = y)
    (p : Ω^ N Y y) (t : I^N) :
    (Homeomorph.genLoopHomeomorph e h).symm p t = e.symm (p t) :=
  map_apply ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_eq.mpr h.symm) p t

end Map

end GenLoop
