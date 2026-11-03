/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of coordinate insertion and of homogeneous ratios

Inserting a coordinate into a tuple, `x ↦ Fin.insertNth i (f x) (g x)`, is as smooth as its
inputs; this is the differentiable counterpart of Mathlib's `Continuous.finInsertNth`.

As a consequence, the homogeneous-ratio maps
`z ↦ (Fin.insertNth i 1 z (j.succAbove k) / Fin.insertNth i 1 z j)_k` are smooth, indeed
analytic, wherever the denominator is nonzero. These are the transition maps between the
standard affine charts of projective space over a nontrivially normed field, so this file
supplies the smoothness of every atlas of projective space built from homogeneous ratios.
-/

public section

open scoped ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {n : ℕ} {r : ℕ∞ω}

/-- Inserting a coordinate into a tuple preserves smoothness: if `f` and `g` are `C^r`, then so
is `x ↦ Fin.insertNth i (f x) (g x)`. -/
theorem ContDiff.finInsertNth {F : Fin (n + 1) → Type*} [∀ j, NormedAddCommGroup (F j)]
    [∀ j, NormedSpace 𝕜 (F j)] (i : Fin (n + 1)) {f : E → F i}
    {g : E → ∀ j : Fin n, F (i.succAbove j)} (hf : ContDiff 𝕜 r f) (hg : ContDiff 𝕜 r g) :
    ContDiff 𝕜 r fun x ↦ i.insertNth (f x) (g x) := by
  refine contDiff_pi.2 fun j ↦ ?_
  induction j using i.succAboveCases with
  | x => simpa using hf
  | p j => simpa using contDiff_pi.1 hg j

namespace Fin

/-- The homogeneous-ratio map `z ↦ (w (j.succAbove k) / w j)_k`, where `w = Fin.insertNth i 1 z`
inserts the coordinate `1` in position `i`, is `C^r` on the set where `w j ≠ 0`. These maps are
the transition maps between the standard affine charts of projective space. -/
theorem contDiffOn_insertNth_one_div (i j : Fin (n + 1)) :
    ContDiffOn 𝕜 r
      (fun z : Fin n → 𝕜 ↦ fun k ↦
        Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z (j.succAbove k) /
          Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j)
      {z | Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z j ≠ 0} := by
  have hw (l : Fin (n + 1)) :
      ContDiff 𝕜 r fun z : Fin n → 𝕜 ↦ Fin.insertNth (α := fun _ ↦ 𝕜) i 1 z l :=
    contDiff_pi.1 ((contDiff_const (c := (1 : 𝕜))).finInsertNth (F := fun _ ↦ 𝕜) i contDiff_id) l
  exact contDiffOn_pi.2 fun k ↦ (hw _).contDiffOn.div (hw j).contDiffOn fun _ hz ↦ hz

end Fin
