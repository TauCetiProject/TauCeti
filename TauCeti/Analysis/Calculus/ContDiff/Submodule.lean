/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The submodule of `C^n` maps

For normed spaces `E` and `F` over a nontrivially normed field `𝕜` and a smoothness order
`n : ℕ∞ω`, the `C^n` maps `E → F` form a `𝕜`-submodule of `E → F` (`TauCeti.contDiffSubmodule`).
This submodule is antitone in `n` (`TauCeti.contDiffSubmodule_antitone`), and the `C^∞` maps are
the infimum over all finite orders `n : ℕ` (`TauCeti.contDiffSubmodule_infty`).

## Main declarations

* `TauCeti.contDiffSubmodule 𝕜 E F n`: the `𝕜`-submodule of `C^n` maps `E → F`.
* `TauCeti.mem_contDiffSubmodule`: membership characterization
  `u ∈ contDiffSubmodule 𝕜 E F n ↔ ContDiff 𝕜 n u`.
* `TauCeti.coe_contDiffSubmodule`: carrier characterization
  `(contDiffSubmodule 𝕜 E F n : Set (E → F)) = {u | ContDiff 𝕜 n u}`.
* `TauCeti.contDiffSubmodule_antitone`: higher smoothness gives a smaller submodule.
* `TauCeti.contDiffSubmodule_infty`:
  `contDiffSubmodule 𝕜 E F ∞ = ⨅ n : ℕ, contDiffSubmodule 𝕜 E F n`.
-/

public section

namespace TauCeti

open scoped ContDiff

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `𝕜`-submodule of `C^n` maps `E → F`. -/
def contDiffSubmodule (n : ℕ∞ω) : Submodule 𝕜 (E → F) where
  carrier := {u | ContDiff 𝕜 n u}
  add_mem' hu hv := hu.add hv
  zero_mem' := contDiff_zero_fun
  smul_mem' c _ hu := hu.const_smul c

variable {𝕜 E F} in
/-- A map belongs to `contDiffSubmodule 𝕜 E F n` if and only if it is `C^n`. -/
@[simp]
theorem mem_contDiffSubmodule {n : ℕ∞ω} {u : E → F} :
    u ∈ contDiffSubmodule 𝕜 E F n ↔ ContDiff 𝕜 n u :=
  Iff.rfl

/-- As a set, `contDiffSubmodule 𝕜 E F n` consists of the `C^n` maps `E → F`. -/
@[simp]
theorem coe_contDiffSubmodule (n : ℕ∞ω) :
    (contDiffSubmodule 𝕜 E F n : Set (E → F)) = {u | ContDiff 𝕜 n u} :=
  Set.ext fun _ ↦ mem_contDiffSubmodule

/-- Increasing the smoothness order decreases `contDiffSubmodule`. -/
theorem contDiffSubmodule_antitone : Antitone (contDiffSubmodule 𝕜 E F) :=
  fun _ _ hmn _ hu ↦ mem_contDiffSubmodule.2 ((mem_contDiffSubmodule.1 hu).of_le hmn)

/-- The submodule of `C^∞` maps is the intersection of the submodules of `C^n` maps for
`n : ℕ`. -/
theorem contDiffSubmodule_infty :
    contDiffSubmodule 𝕜 E F ∞ = ⨅ n : ℕ, contDiffSubmodule 𝕜 E F n := by
  ext u
  simp [contDiff_infty]

end TauCeti
