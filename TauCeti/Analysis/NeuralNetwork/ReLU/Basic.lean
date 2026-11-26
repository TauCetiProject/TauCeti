/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import Mathlib.Basic.Real.Basic

/-!
# ReLU networks

A ReLU network is a real multilayer perceptron with a rectifier at each hidden unit and
an affine output layer. Its depth counts affine layers. `ReLUNetComputes d f` fixes all
the widths, including those of the input and output, and allows arbitrary weights and biases.

This is the architecture of Arora, Basu, Mianjy and Mukherjee, *Understanding Deep Neural
Networks with Rectified Linear Units*, Definition 1, with a bias in the output layer.
-/

public noncomputable section

namespace TauCeti

open Neuromanifold

variable {L n : ℕ}

/-- The real MLP of widths `d` with each hidden activation given by the positive part.
The widths reduce to `d` in the dependent types of parameters and inputs. -/
@[expose] def reluSpec (d : Fin (L + 1) → ℕ) : MLPSpec ℝ L where
  width := d
  activation _ t := max 0 t

/-- The widths of a ReLU specification are the prescribed ones. -/
@[simp] theorem reluSpec_width (d : Fin (L + 1) → ℕ) : (reluSpec d).width = d := (rfl)

/-- Each hidden unit applies the scalar rectifier. -/
@[simp] theorem reluSpec_activation (d : Fin (L + 1) → ℕ) (i : Fin (L - 1)) :
    (reluSpec d).activation i = fun t => max 0 t := (rfl)

/-- Some parameters of a network of widths `d`, input width `n` and output width one,
realize the scalar function `f` on the entire input space. -/
structure ReLUNetComputes (d : Fin (L + 1) → ℕ) (f : (Fin n → ℝ) → ℝ) : Prop where
  /-- The first layer accepts an input with `n` coordinates. -/
  input_width : d 0 = n
  /-- The last layer has a single output coordinate. -/
  output_width : d (Fin.last L) = 1
  /-- The scalar output agrees with `f` at every input for one choice of parameters. -/
  exists_parameters : ∃ θ : (reluSpec d).Parameters, ∀ x,
    (reluSpec d).realize θ (x ∘ Fin.cast input_width) (Fin.cast output_width.symm 0) = f x

/-- For matching input and output widths, only the realizing parameters need to be supplied. -/
theorem reluNetComputes_iff {d : Fin (L + 1) → ℕ} {f : (Fin n → ℝ) → ℝ}
    (hin : d 0 = n) (hout : d (Fin.last L) = 1) :
    ReLUNetComputes d f ↔ ∃ θ : (reluSpec d).Parameters,
      ∀ x, (reluSpec d).realize θ (x ∘ Fin.cast hin) (Fin.cast hout.symm 0) = f x :=
  ⟨fun h => h.exists_parameters, fun ⟨θ, hθ⟩ => ⟨hin, hout, θ, hθ⟩⟩

end TauCeti
