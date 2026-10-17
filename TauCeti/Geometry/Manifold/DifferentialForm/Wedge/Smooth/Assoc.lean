/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Assoc
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Associativity of smooth differential-form wedges

The scalar wedge on smooth forms is associative after the canonical reassociation of its finite
argument tuple.  This specializes rough-form associativity to the smooth scalar product and gives
its pointwise reassociation law for products used in de Rham cohomology.
-/

public section

namespace TauCeti

open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [IsManifold I 1 M] {k l m : ℕ}

namespace SmoothForm

/-- The scalar wedge of smooth forms is associative, with the tuple degree reassociated. -/
theorem wedge_assoc_apply (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l)
    (χ : SmoothForm I M ℝ m) (x : M) (v : Fin (k + l + m) → TangentSpace I x) :
    (wedge (wedge φ ψ) χ).1 x v =
      (wedge φ (wedge ψ χ)).1 x (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  rw [coe_wedge, coe_wedge, coe_wedge, coe_wedge]
  exact RoughForm.wedge_assoc (φ := φ.1) (ψ := ψ.1) (χ := χ.1) x v

end SmoothForm

end TauCeti
