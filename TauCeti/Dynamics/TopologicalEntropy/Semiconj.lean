/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Lifting dynamical nets along a semiconjugacy

Let `h : X → Y` semiconjugate `T : X → X` to `S : Y → Y`, and let `g` be a right inverse of `h`.
The image under `g` of a dynamical net of `S` in `F` at the entourage `U` is a dynamical net of
`T` in `h ⁻¹' F` at the pulled-back entourage `Prod.map h h ⁻¹' U`
(`Dynamics.IsDynNetIn.image_of_semiconj`). This complements Mathlib's
`Function.Semiconj.preimage_dynEntourage`.
-/

public section

namespace Dynamics.IsDynNetIn

open Set Function

variable {X Y : Type*} {T : X → X} {S : Y → Y} {h : X → Y} {g : Y → X} {F : Set Y}
  {U : SetRel Y Y} {n : ℕ} {s : Set Y}

/-- If `h` semiconjugates `T` to `S` and `g` is a right inverse of `h`, the image under `g` of a
dynamical net of `S` in `F` at `U` is a dynamical net of `T` in `h ⁻¹' F` at the pulled-back
entourage `Prod.map h h ⁻¹' U`. -/
theorem image_of_semiconj (hsc : Semiconj h T S) (hg : RightInverse g h)
    (hs : IsDynNetIn S F U n s) : IsDynNetIn T (h ⁻¹' F) (Prod.map h h ⁻¹' U) n (g '' s) := by
  refine ⟨?_, fun x₁ hx₁ x₂ hx₂ hne ↦ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_preimage, hg y]
    exact hs.1 hy
  obtain ⟨y₁, hy₁, rfl⟩ := hx₁
  obtain ⟨y₂, hy₂, rfl⟩ := hx₂
  have hball (y : Y) : SetRel.ball (SetRel.inv (Prod.map h h ⁻¹' dynEntourage S U n)) (g y) =
      h ⁻¹' (dynEntourage S U n).inv.ball y := by
    ext z
    simp [SetRel.mem_ball, hg y]
  rw [onFun, ← hsc.preimage_dynEntourage, hball, hball]
  exact (hs.2 hy₁ hy₂ fun h' ↦ hne (congrArg g h')).preimage h

end Dynamics.IsDynNetIn
