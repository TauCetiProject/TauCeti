/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
-- Private: the composition and derivative rules for `ContDiffAt` are used only in the proofs.
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Iterated gradients of a scalar function

The gradient of a scalar function on a real inner product space `E` is an `E`-valued field; its
Fréchet derivative is an `E →L[ℝ] E`-valued field, and each further derivative adds one
continuous-linear direction on the left. This file names these basis-free target spaces and the
classical chain of derivative fields that lands in them.

`TauCeti.IteratedGradient E j` is the target after `j` derivatives of the gradient: `E` at
`j = 0` and `E →L[ℝ] IteratedGradient E j` at `j + 1`, with the operator norm.
`TauCeti.iteratedGradientChain f j` is the corresponding field of `f`: the gradient at `j = 0`
and the Fréchet derivative of the previous field at `j + 1`. Its order-one member is the
derivative of the gradient, which is the Hessian of `f` represented as an endomorphism of `E`.

## Implementation notes

The target spaces are produced by the reducible recursion `TauCeti.iteratedGradientModel`, which
bundles each space with its normed structure in a `TauCeti.IteratedGradientModel`. Both are public
because `TauCeti.IteratedGradient` is indexed by them: at a concrete order the space and its
normed, complete structures are recovered by unfolding the recursion rather than by transport.

## Main declarations

* `TauCeti.IteratedGradient`: the basis-free target of an iterated gradient.
* `TauCeti.iteratedGradientChain`: the classical derivative fields of a scalar function.
* `TauCeti.contDiffAt_iteratedGradientChain`: the `j`th field of a `Cⁿ` function is
  `Cᵐ` when `m + j + 1 ≤ n`.
* `TauCeti.hasCompactSupport_iteratedGradientChain`: every field of a compactly supported
  function is compactly supported.
-/

public section

noncomputable section

namespace TauCeti

open scoped ContDiff

universe u

/-- The normed-space data underlying an iterated gradient. -/
structure IteratedGradientModel : Type (u + 1) where
  /-- The carrier space for the iterated gradient. -/
  Space : Type u
  /-- The normed additive commutative group structure on `Space`. -/
  [normedAddCommGroup : NormedAddCommGroup Space]
  /-- The normed `ℝ`-space structure on `Space`. -/
  [normedSpace : NormedSpace ℝ Space]

/-- The recursively bundled target of an iterated gradient. -/
@[reducible, expose] noncomputable def iteratedGradientModel (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : ℕ → IteratedGradientModel.{u}
  | 0 => { Space := E }
  | j + 1 =>
      let S := iteratedGradientModel E j
      letI : NormedAddCommGroup S.Space := S.normedAddCommGroup
      letI : NormedSpace ℝ S.Space := S.normedSpace
      { Space := E →L[ℝ] S.Space }

/-- The target of an iterated gradient, indexed by the number of derivative directions added
beyond the gradient.  At `j = 0` this is the gradient vector `E`; each successor adds one
continuous-linear derivative direction on the left. -/
abbrev IteratedGradient (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ) : Type u :=
  (iteratedGradientModel E j).Space

section IteratedGradient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable instance (j : ℕ) : NormedAddCommGroup (IteratedGradient E j) :=
  (iteratedGradientModel E j).normedAddCommGroup

noncomputable instance (j : ℕ) : NormedSpace ℝ (IteratedGradient E j) :=
  (iteratedGradientModel E j).normedSpace

noncomputable instance [CompleteSpace E] (j : ℕ) : CompleteSpace (IteratedGradient E j) := by
  induction j with
  | zero => exact inferInstance
  | succ j ih =>
      let _ : CompleteSpace (IteratedGradient E j) := ih
      exact inferInstance

end IteratedGradient

section IteratedGradientChain

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The classical derivative fields of a scalar function, in the basis-free nested-linear-map
types `TauCeti.IteratedGradient`. Index zero is the gradient and each successor is the Fréchet
derivative of the preceding field. -/
noncomputable def iteratedGradientChain (f : F → ℝ) :
    (j : ℕ) → F → IteratedGradient F j
  | 0 => fun x => gradient f x
  | j + 1 => fderiv ℝ (iteratedGradientChain f j)

@[simp]
theorem iteratedGradientChain_zero (f : F → ℝ) :
    iteratedGradientChain f 0 = gradient f :=
  (rfl)

@[simp]
theorem iteratedGradientChain_succ (f : F → ℝ) (j : ℕ) :
    iteratedGradientChain f (j + 1) = fderiv ℝ (iteratedGradientChain f j) :=
  (rfl)

/-- The `j`th iterated-gradient field is `C^m` at a point whenever the scalar function
is `C^n` there with `m + j + 1 ≤ n`. -/
theorem contDiffAt_iteratedGradientChain {f : F → ℝ} {x : F} {m n : ℕ∞ω}
    (hf : ContDiffAt ℝ n f x) (j : ℕ) (h : m + j + 1 ≤ n) :
    ContDiffAt ℝ m (iteratedGradientChain f j) x := by
  induction j generalizing m with
  | zero =>
      rw [iteratedGradientChain_zero]
      exact (InnerProductSpace.toDual ℝ F).symm.contDiff.contDiffAt.comp x
        (hf.fderiv_right (by simpa using h))
  | succ j ih =>
      rw [iteratedGradientChain_succ]
      have hs := ih (m := m + 1) (by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h)
      exact hs.fderiv_right le_rfl

/-- Every field in the iterated-gradient chain of a compactly supported function has compact
support. -/
theorem hasCompactSupport_iteratedGradientChain {f : F → ℝ} (hf : HasCompactSupport f) :
    ∀ j, HasCompactSupport (iteratedGradientChain f j)
  | 0 => by
      rw [iteratedGradientChain_zero]
      exact (hf.fderiv ℝ).comp_left (map_zero _)
  | j + 1 => by
      rw [iteratedGradientChain_succ]
      exact (hasCompactSupport_iteratedGradientChain hf j).fderiv ℝ

end IteratedGradientChain

end TauCeti
