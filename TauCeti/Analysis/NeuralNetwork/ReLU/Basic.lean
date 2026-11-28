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

A ReLU network is a real multilayer perceptron with a rectifier at each hidden unit.
Its depth counts affine layers. At positive depth the final layer is affine, and at
depth zero the network realizes the identity on its input space. `ReLUNetComputes d f`
fixes all widths, including input and output, and allows arbitrary weights and biases.

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
  /-- The input space has `n` coordinates. -/
  input_width : d 0 = n
  /-- The output space has a single coordinate. -/
  output_width : d (Fin.last L) = 1
  /-- The scalar output agrees with `f` at every input for one choice of parameters. -/
  exists_parameters : ∃ θ : (reluSpec d).Parameters, ∀ x,
    (reluSpec d).realize θ (x ∘ Fin.cast input_width) (Fin.cast output_width.symm 0) = f x

/-- A ReLU network computes `f` exactly when its endpoint widths match and some parameters
realize `f` pointwise. -/
theorem reluNetComputes_iff {d : Fin (L + 1) → ℕ} {f : (Fin n → ℝ) → ℝ} :
    ReLUNetComputes d f ↔ ∃ (hin : d 0 = n) (hout : d (Fin.last L) = 1)
      (θ : (reluSpec d).Parameters),
      ∀ x, (reluSpec d).realize θ (x ∘ Fin.cast hin) (Fin.cast hout.symm 0) = f x :=
  ⟨fun h => ⟨h.input_width, h.output_width, h.exists_parameters⟩,
    fun ⟨hin, hout, hθ⟩ => ⟨hin, hout, hθ⟩⟩

end TauCeti
