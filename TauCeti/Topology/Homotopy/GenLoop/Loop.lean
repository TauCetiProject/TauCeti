/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.GenLoop.Homeomorph

/-!
# Currying a loop direction of generalized loops

Mathlib's generalized loops `Ω^ N X x` are the maps `I^N → X` sending the cube boundary to `x`.
Reindexing the cube directions along `M ≃ N` is a homeomorphism `GenLoop.congr`, and Mathlib's
`GenLoop.genLoopGenLoopEquiv` curries `Ω^ M (Ω^ N X x) const ≃ₜ Ω^ (M ⊕ N) X x`. This file
specializes the latter to a single extra direction, which is the path parameter of the loop space
`Ω X x`: cube loops in the directions `M` of `Ω X x`, based at the constant loop, are cube loops of
`X` in the directions `M ⊕ Fin 1`, and, for `Fin k`, in `k + 1` directions. These are statements
about the topology of spaces of cube loops, and use no homotopy groups.

## Main declarations

* `GenLoop.genLoopLoopSumHomeomorph`: `Ω^ M (Ω X x) (refl x) ≃ₜ Ω^ (M ⊕ Fin 1) X x`.
* `GenLoop.genLoopLoopHomeomorph`: `Ω^ (Fin k) (Ω X x) (refl x) ≃ₜ Ω^ (Fin (k + 1)) X x`.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {M N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

@[simp]
theorem congr_apply (e : M ≃ N) (p : Ω^ M X x) (t : I^N) :
    _root_.GenLoop.congr x e p t = p fun m => t (e m) :=
  rfl

@[simp]
theorem genLoopGenLoopEquiv_apply (p : Ω^ M (Ω^ N X x) _root_.GenLoop.const) (y : I^(M ⊕ N)) :
    _root_.GenLoop.genLoopGenLoopEquiv x p y =
      p (fun m => y (Sum.inl m)) fun n => y (Sum.inr n) :=
  rfl

section Loop

variable (x) in
/-- Currying one extra cube direction: cube loops in the directions `M` of the loop space
`Ω X x`, based at the constant loop, are cube loops of `X` in the directions `M ⊕ Fin 1`. -/
def genLoopLoopSumHomeomorph (M : Type*) :
    Ω^ M (Ω X x) (Path.refl x) ≃ₜ Ω^ (M ⊕ Fin 1) X x :=
  (Homeomorph.genLoopHomeomorph (homeomorphOfUnique (Fin 1)).symm
      ((Homeomorph.symm_apply_eq _).mpr (homeomorphOfUnique_const (Fin 1)).symm)).trans
    (genLoopGenLoopEquiv x)

variable (x) in
/-- The extra cube direction of `genLoopLoopSumHomeomorph` is the path parameter. -/
@[simp]
theorem genLoopLoopSumHomeomorph_apply (M : Type*) (p : Ω^ M (Ω X x) (Path.refl x))
    (t : I^(M ⊕ Fin 1)) :
    genLoopLoopSumHomeomorph x M p t = p (fun i => t (Sum.inl i)) (t (Sum.inr 0)) := by
  rw [genLoopLoopSumHomeomorph, Homeomorph.trans_apply]
  simp

variable (x) in
/-- The homeomorphism `genLoopLoopSumHomeomorph` is based: it carries the constant cube loop to
the constant cube loop. -/
@[simp]
theorem genLoopLoopSumHomeomorph_const (M : Type*) :
    genLoopLoopSumHomeomorph x M (GenLoop.const : Ω^ M (Ω X x) (Path.refl x)) = GenLoop.const := by
  refine _root_.GenLoop.ext _ _ fun t => ?_
  simp [genLoopLoopSumHomeomorph_apply]

variable (x) in
/-- The inverse of `genLoopLoopSumHomeomorph` also carries the constant cube loop to the constant
cube loop. -/
@[simp]
theorem genLoopLoopSumHomeomorph_symm_const (M : Type*) :
    (genLoopLoopSumHomeomorph x M).symm (GenLoop.const : Ω^ (M ⊕ Fin 1) X x) =
      (GenLoop.const : Ω^ M (Ω X x) (Path.refl x)) :=
  (genLoopLoopSumHomeomorph x M).symm_apply_eq.2 (genLoopLoopSumHomeomorph_const x M).symm

variable (x) in
/-- The inverse of `genLoopLoopSumHomeomorph` evaluated at the cube coordinates `s` in the
directions `M` and the path parameter `u`. -/
@[simp]
theorem genLoopLoopSumHomeomorph_symm_apply (M : Type*) (q : Ω^ (M ⊕ Fin 1) X x)
    (s : I^M) (u : I) :
    (genLoopLoopSumHomeomorph x M).symm q s u = q (Sum.elim s fun _ => u) := by
  have h := genLoopLoopSumHomeomorph_apply x M ((genLoopLoopSumHomeomorph x M).symm q)
    (Sum.elim s fun _ => u)
  rw [Homeomorph.apply_symm_apply] at h
  simpa using h.symm

/-- **Naturality of the currying homeomorphism**: `genLoopLoopSumHomeomorph` commutes with the maps
induced on cube loops by a based continuous map `f : X → Y`, and by any map `F` of loop spaces
that postcomposes loops with `f`, for any index type of cube directions. -/
theorem genLoopLoopSumHomeomorph_map (f : C(X, Y)) (hf : f x = y) (F : C(Ω X x, Ω Y y))
    (hFf : ∀ γ t, F γ t = f (γ t)) (M : Type*) (p : Ω^ M (Ω X x) (Path.refl x)) :
    genLoopLoopSumHomeomorph y M
        (map F (Path.ext (funext fun t => (hFf _ t).trans hf)) p) =
      map f hf (genLoopLoopSumHomeomorph x M p) := by
  refine GenLoop.ext _ _ fun t => ?_
  rw [genLoopLoopSumHomeomorph_apply]
  exact (hFf _ _).trans (congrArg f (genLoopLoopSumHomeomorph_apply x M p t).symm)

variable (x) in
/-- Currying the last cube direction: cube loops in `k` directions of the loop space `Ω X x`,
based at the constant loop, are cube loops of `X` in `k + 1` directions. This is
`genLoopLoopSumHomeomorph` with the directions `Fin k ⊕ Fin 1` identified with `Fin (k + 1)`. -/
def genLoopLoopHomeomorph (k : ℕ) :
    Ω^ (Fin k) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin (k + 1)) X x :=
  (genLoopLoopSumHomeomorph x (Fin k)).trans (GenLoop.congr x finSumFinEquiv)

variable (x) in
/-- `genLoopLoopHomeomorph` is `genLoopLoopSumHomeomorph` followed by the reindexing of the cube
directions `Fin k ⊕ Fin 1 ≃ Fin (k + 1)`. -/
theorem genLoopLoopHomeomorph_apply_eq (k : ℕ) (p : Ω^ (Fin k) (Ω X x) (Path.refl x)) :
    genLoopLoopHomeomorph x k p =
      GenLoop.congr x finSumFinEquiv (genLoopLoopSumHomeomorph x _ p) := by
  rw [genLoopLoopHomeomorph, Homeomorph.trans_apply]

variable (x) in
/-- The last cube direction of `genLoopLoopHomeomorph` is the path parameter. -/
@[simp]
theorem genLoopLoopHomeomorph_apply (k : ℕ) (p : Ω^ (Fin k) (Ω X x) (Path.refl x))
    (t : I^(Fin (k + 1))) :
    genLoopLoopHomeomorph x k p t = p (fun i => t i.castSucc) (t (Fin.last k)) := by
  rw [genLoopLoopHomeomorph, Homeomorph.trans_apply, congr_apply,
    genLoopLoopSumHomeomorph_apply]
  have h' (i : Fin k) : finSumFinEquiv (Sum.inl i) = i.castSucc := rfl
  have h'' : finSumFinEquiv (Sum.inr (0 : Fin 1)) = Fin.last k := rfl
  rw [h'']
  simp only [h']

variable (x) in
/-- The homeomorphism `genLoopLoopHomeomorph` is based: it carries the constant cube loop to
the constant cube loop. -/
@[simp]
theorem genLoopLoopHomeomorph_const (k : ℕ) :
    genLoopLoopHomeomorph x k (GenLoop.const : Ω^ (Fin k) (Ω X x) (Path.refl x)) =
      GenLoop.const := by
  refine _root_.GenLoop.ext _ _ fun t => ?_
  simp [genLoopLoopHomeomorph_apply]

variable (x) in
/-- The inverse of `genLoopLoopHomeomorph` also carries the constant cube loop to the constant
cube loop. -/
@[simp]
theorem genLoopLoopHomeomorph_symm_const (k : ℕ) :
    (genLoopLoopHomeomorph x k).symm (GenLoop.const : Ω^ (Fin (k + 1)) X x) =
      (GenLoop.const : Ω^ (Fin k) (Ω X x) (Path.refl x)) :=
  (genLoopLoopHomeomorph x k).symm_apply_eq.2 (genLoopLoopHomeomorph_const x k).symm

variable (x) in
/-- The inverse of `genLoopLoopHomeomorph` evaluated at the first `k` coordinates `s` and the
path parameter `u`. -/
@[simp]
theorem genLoopLoopHomeomorph_symm_apply (k : ℕ) (q : Ω^ (Fin (k + 1)) X x)
    (s : I^(Fin k)) (u : I) :
    (genLoopLoopHomeomorph x k).symm q s u = q (Fin.snoc s u) := by
  have h := genLoopLoopHomeomorph_apply x k ((genLoopLoopHomeomorph x k).symm q) (Fin.snoc s u)
  rw [Homeomorph.apply_symm_apply] at h
  simpa using h.symm

end Loop

/-- **Naturality of the currying homeomorphism** for `k` cube directions: the specialization of
`genLoopLoopSumHomeomorph_map` to `Fin k`. -/
theorem genLoopLoopHomeomorph_map (f : C(X, Y)) (hf : f x = y) (F : C(Ω X x, Ω Y y))
    (hFf : ∀ γ t, F γ t = f (γ t)) (k : ℕ) (p : Ω^ (Fin k) (Ω X x) (Path.refl x)) :
    genLoopLoopHomeomorph y k (map F (Path.ext (funext fun t => (hFf _ t).trans hf)) p) =
      map f hf (genLoopLoopHomeomorph x k p) := by
  refine GenLoop.ext _ _ fun t => ?_
  rw [genLoopLoopHomeomorph_apply]
  exact (hFf _ _).trans (congrArg f (genLoopLoopHomeomorph_apply x k p t).symm)

end GenLoop
