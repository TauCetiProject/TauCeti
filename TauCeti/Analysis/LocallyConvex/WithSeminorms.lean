/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Composition of seminorm-bounded maps

Semilinear maps bounded with respect to families of seminorms are closed under composition.
This supplies composite bounds without requiring topologies on the modules or directedness of
the seminorm families.
-/

public section

namespace Seminorm

variable {𝕜 𝕜₂ 𝕜₃ E F G ι ι' ι'' : Type*}
variable [SeminormedRing 𝕜] [SeminormedRing 𝕜₂] [SeminormedRing 𝕜₃]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- The composite of seminorm-bounded semilinear maps is seminorm-bounded. -/
theorem IsBounded.comp {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F}
    {r : ι'' → Seminorm 𝕜₃ G} {f : E →ₛₗ[σ₁₂] F} {g : F →ₛₗ[σ₂₃] G}
    (hg : IsBounded q r g) (hf : IsBounded p q f) : IsBounded p r (g.comp f) := by
  intro i
  obtain ⟨s, C, hs⟩ := hg i
  obtain ⟨D, t, ht⟩ := isBounded_sup hf s
  refine ⟨t, C * D, ?_⟩
  rw [comp_comp]
  calc
    _ ≤ (C • s.sup q).comp f := comp_mono f hs
    _ = C • (s.sup q).comp f := smul_comp _ _ _
    _ ≤ C • (D • t.sup p) := IsOrderedSMul.smul_le_smul_left _ _ ht C
    _ = _ := (mul_smul C D (t.sup p)).symm

end Seminorm
