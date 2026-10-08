/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ExtendByZero
public import TauCeti.Topology.PL.Map

/-!
# Piecewise-linear coordinate formulas under injective relabeling

An injective relabeling extends a coordinate vector by zero on unused vertices.
Conjugate a coordinate formula by extension on its output and restriction on its input.
The resulting formula is PL on the relabeled set exactly when the original formula is
PL. Both index types may be infinite: extension and restriction are continuous linear
maps for their product topologies.

This is the coordinate transport needed to compare PL maps of polyhedra described on
different ambient vertex sets, including a common enlarged set used for stellar moves.

Reference: Rourke–Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 1–2.
-/

public section

open Set Function

namespace TauCeti

variable {ι κ α β : Type*} (e : ι ↪ κ) (d : α ↪ β)
  {f : (ι → ℝ) → (α → ℝ)} {s : Set (ι → ℝ)}

/-- Extending output coordinates by zero and pulling input coordinates back along
injections preserves and reflects PL regularity on the relabeled domain. -/
theorem isPLOn_extendByZero_iff :
    IsPLOn (fun y : κ → ℝ => Function.extend d (f (y ∘ e)) 0)
      ((Function.ExtendByZero.continuousLinearMap ℝ e) '' s) ↔ IsPLOn f s := by
  let A := Function.ExtendByZero.continuousLinearMap ℝ e
  let B : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)
  let C := Function.ExtendByZero.continuousLinearMap ℝ d
  let D : (β → ℝ) →L[ℝ] (α → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (d i)
  have hBapply (y : κ → ℝ) : B y = y ∘ e := by
    ext i
    simp [B]
  have hCapply (x : α → ℝ) : C x = Function.extend d x 0 :=
    Function.ExtendByZero.continuousLinearMap_apply ℝ d x
  have hBA (x : ι → ℝ) : B (A x) = x := by
    ext i
    simp [A, B, e.injective]
  have hDC (x : α → ℝ) : D (C x) = x := by
    ext i
    simp [C, D, d.injective]
  have hB : IsPLOn (⇑B) (A '' s) :=
    isPLOn_continuousAffineMap B.toContinuousAffineMap _
  have hC : IsPLOn (⇑C) univ :=
    isPLOn_continuousAffineMap C.toContinuousAffineMap _
  constructor
  · intro h
    have hA : IsPLOn (⇑A) s :=
      isPLOn_continuousAffineMap A.toContinuousAffineMap _
    have hD : IsPLOn (⇑D) univ :=
      isPLOn_continuousAffineMap D.toContinuousAffineMap _
    have hcomp := hD.comp (h.comp hA (fun x hx => mem_image_of_mem A hx))
      (fun _ _ => mem_univ _)
    refine hcomp.congr ?_
    intro x _
    simp only [Function.comp_apply]
    rw [← hBapply, hBA, ← hCapply]
    exact (hDC (f x)).symm
  · intro h
    have hBs : A '' s ⊆ B ⁻¹' s := by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [mem_preimage, hBA] using hx
    refine (hC.comp (h.comp hB hBs) (fun _ _ => mem_univ _)).congr ?_
    intro y _
    simp only [Function.comp_apply, hBapply, hCapply]

end TauCeti
