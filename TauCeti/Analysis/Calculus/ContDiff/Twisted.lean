/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth maps twisted along two translations

Let `p` and `q` be vectors of a normed space `E` and `ε₁`, `ε₂` scalars. The `C^n` maps
`u : E → F` with `u (z + p) = ε₁ • u z` and `u (z + q) = ε₂ • u z` form a submodule of `E → F`
(`TauCeti.doublyTwistedContDiff`). For `E = ℝ × ℝ`, generators `p`, `q` of a lattice and signs
`ε₁`, `ε₂`, these are the `C^n` maps on the plane that descend to sections of the flat line bundle
on the torus `E / (ℤ p + ℤ q)` twisted by the real sign character with values `ε₁`, `ε₂` on the
generators.

## Main declarations

* `TauCeti.doublyTwistedContDiff 𝕜 F n p q ε₁ ε₂`: the `C^n` maps twisted by `ε₁` along `p` and
  by `ε₂` along `q`.
-/

public section

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `C^n` maps `u : E → F` twisted by the scalar `ε₁` along `p` and by the scalar `ε₂` along
`q`: `u (z + p) = ε₁ • u z` and `u (z + q) = ε₂ • u z`. -/
def doublyTwistedContDiff (n : WithTop ℕ∞) (p q : E) (ε₁ ε₂ : 𝕜) : Submodule 𝕜 (E → F) where
  carrier := {u | ContDiff 𝕜 n u ∧ (∀ z, u (z + p) = ε₁ • u z) ∧ ∀ z, u (z + q) = ε₂ • u z}
  add_mem' {u v} hu hv := ⟨hu.1.add hv.1, fun z => by simp [hu.2.1 z, hv.2.1 z],
    fun z => by simp [hu.2.2 z, hv.2.2 z]⟩
  zero_mem' := ⟨contDiff_const, fun z => by simp, fun z => by simp⟩
  smul_mem' c u hu := ⟨hu.1.const_smul c, fun z => by simp [hu.2.1 z, smul_comm c ε₁],
    fun z => by simp [hu.2.2 z, smul_comm c ε₂]⟩

variable {𝕜 F}

@[simp]
theorem mem_doublyTwistedContDiff {n : WithTop ℕ∞} {p q : E} {ε₁ ε₂ : 𝕜} {u : E → F} :
    u ∈ doublyTwistedContDiff 𝕜 F n p q ε₁ ε₂ ↔
      ContDiff 𝕜 n u ∧ (∀ z, u (z + p) = ε₁ • u z) ∧ ∀ z, u (z + q) = ε₂ • u z :=
  Iff.rfl

end TauCeti
