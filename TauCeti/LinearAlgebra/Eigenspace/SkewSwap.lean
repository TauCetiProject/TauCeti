/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvectors of the skew swap

The skew swap `LinearEquiv.skewSwap R M M : (x, y) ↦ (-y, x)` on `M × M` squares to `-1`; over
`ℂ` it is the standard complex structure on `M × M`. This file describes its eigenvectors in
coordinates: a `μ`-eigenvector `x` has second coordinate `-μ • x.1`, and when `μ * μ = -1` this
relation characterizes the `μ`-eigenspace. Over `ℂ` this applies to both `μ = i` and `μ = -i`.

## Main declarations

* `TauCeti.snd_eq_neg_smul_fst_of_mem_eigenspace_skewSwap`: a `μ`-eigenvector `x` of the skew
  swap satisfies `x.2 = -μ • x.1`.
* `TauCeti.mem_eigenspace_skewSwap_iff`: for `μ * μ = -1`, the `μ`-eigenspace of the skew swap is
  `{x | x.2 = -μ • x.1}`.
-/

public section

namespace TauCeti

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {μ : R} {x : M × M}

/-- A `μ`-eigenvector of the skew swap `(x, y) ↦ (-y, x)` has second coordinate `-μ` times its
first coordinate. -/
theorem snd_eq_neg_smul_fst_of_mem_eigenspace_skewSwap
    (hx : x ∈ Module.End.eigenspace (LinearEquiv.skewSwap R M M).toLinearMap μ) :
    x.2 = -μ • x.1 := by
  rw [Module.End.mem_eigenspace_iff, Prod.ext_iff] at hx
  simpa [neg_eq_iff_eq_neg] using hx.1

/-- If `μ * μ = -1`, a vector `x` is a `μ`-eigenvector of the skew swap `(x, y) ↦ (-y, x)` if and
only if its second coordinate is `-μ` times its first coordinate. -/
theorem mem_eigenspace_skewSwap_iff (hμ : μ * μ = -1) :
    x ∈ Module.End.eigenspace (LinearEquiv.skewSwap R M M).toLinearMap μ ↔ x.2 = -μ • x.1 := by
  refine ⟨snd_eq_neg_smul_fst_of_mem_eigenspace_skewSwap, fun hx => ?_⟩
  rw [Module.End.mem_eigenspace_iff]
  ext <;> simp [hx, smul_smul, hμ]

end TauCeti
