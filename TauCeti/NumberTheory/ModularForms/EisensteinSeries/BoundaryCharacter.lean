/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Span

/-!
# Nebentypus from Eisenstein boundary values

The constant terms of a modular form with nebentypus `χ` transform by `χ` when a cusp
representative is multiplied on the left by an element of `Γ₀(N)`. On the congruence
Eisenstein subspace the converse holds: this transformation law for all cusp constant terms
determines the diamond eigencharacter, because a failure of the eigenvector equation would be
both Eisenstein and cuspidal.

This boundary characterization reduces the identification of the prescribed-character
Eisenstein span with the full Eisenstein complement to a spanning problem for its cusp
constant-term vectors.

## Main results

* `TauCeti.mem_modFormCharSpace_iff_constantTermAt_mul_left_of_mem_congruenceEisensteinSubspace`:
  the converse on the congruence Eisenstein subspace.
* `TauCeti.congruenceEisensteinSubspace_inf_modFormCharSpace`: the corresponding equality of
  subspaces, expressed as the pullback of the boundary transformation law.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 3.1 and 4.5.
-/

public noncomputable section

open Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ} (chi : (ZMod N)ˣ →* ℂˣ)

/-- On the congruence Eisenstein subspace of `M_k(Γ₁(N))`, the transformation law of the
cusp constant terms under `Γ₀(N)` characterizes membership in the nebentypus space.

Without the Eisenstein hypothesis the converse is false, since all cusp forms have zero
constant terms. -/
theorem mem_modFormCharSpace_iff_constantTermAt_mul_left_of_mem_congruenceEisensteinSubspace
    (hk : 3 ≤ k) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfE : f ∈ EisensteinSeries.congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk) :
    f ∈ modFormCharSpace k chi ↔
      ∀ (g : ↥(Gamma0 N)) (γ : SL(2, ℤ)),
        constantTermAt ((g : SL(2, ℤ)) * γ) f =
          (chi ((Gamma0Map N).toHomUnits g) : ℂ) * constantTermAt γ f := by
  constructor
  · exact fun hf g γ ↦ constantTermAt_mul_left_of_mem_modFormCharSpace chi hf g γ
  · intro h
    rw [mem_modFormCharSpace_iff]
    intro d
    rw [diamondOpHom_apply]
    obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
    apply sub_eq_zero.mp
    apply (Submodule.disjoint_def.mp
      (EisensteinSeries.disjoint_congruenceEisensteinSubspace_cuspFormSubmodule
        (Gamma_le_Gamma1 N) hk))
    · exact Submodule.sub_mem _
        (EisensteinSeries.diamondOp_mem_congruenceEisensteinSubspace hk d hfE)
        (Submodule.smul_mem _ _ hfE)
    · rw [mem_cuspFormSubmodule_iff_constantTermAt_eq_zero]
      intro γ
      rw [map_sub, constantTermAt_diamondOp k d g hg, map_smul, smul_eq_mul, ← hg,
        h g γ, sub_self]

/-- Intersecting the congruence Eisenstein subspace with a nebentypus space is equivalent to
pulling the boundary nebentypus condition back along the constant-term map. This is the
subspace-level form of
`mem_modFormCharSpace_iff_constantTermAt_mul_left_of_mem_congruenceEisensteinSubspace`. -/
theorem congruenceEisensteinSubspace_inf_modFormCharSpace (hk : 3 ≤ k) :
    EisensteinSeries.congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk ⊓
        modFormCharSpace k chi =
      EisensteinSeries.congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk ⊓
        (ModularForm.nebentypusConstantTermSubspace chi).comap ModularForm.constantTerms := by
  ext f
  simp only [Submodule.mem_inf, Submodule.mem_comap]
  constructor
  · rintro ⟨hfE, hfchi⟩
    exact ⟨hfE, ModularForm.constantTerms_mem_nebentypusConstantTermSubspace chi hfchi⟩
  · rintro ⟨hfE, hfboundary⟩
    refine ⟨hfE, ?_⟩
    apply
      (mem_modFormCharSpace_iff_constantTermAt_mul_left_of_mem_congruenceEisensteinSubspace
        chi hk hfE).mpr
    rw [ModularForm.mem_nebentypusConstantTermSubspace] at hfboundary
    simpa only [ModularForm.constantTerms_apply] using hfboundary

end TauCeti
