/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm

/-!
# Congruence with a varying reference form

For a jointly smooth family of symmetric bilinear forms `B (b, v)`, the reference form
`B (b, 0)` may itself vary with the base parameter `b`. Near a point where `B (a, 0)` is
invertible, `exists_parametric_congruence_of_symmetric_family` constructs jointly smooth
invertible operators `R (b, v)` such that

`B (b, 0) (R (b, v) w) (R (b, v) w') = B (b, v) w w'`.

Crucially, `R (b, 0) = 1` throughout the base neighbourhood, not just at `a`. This is the
linear normalization needed for a parameter-dependent Morse change of coordinates fixing
the zero section, with the Hessian along that section as the reference quadratic form.
The theorem works on Banach spaces and preserves the differentiability order, including
order zero.

The construction uses `TauCeti.exists_congruence_of_symmetric_family` to compare all the
forms to `B (a, 0)`, then divides by the resulting operator on the zero section. Inversion
is smooth after shrinking to a product neighbourhood of invertible operators.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1 (the Morse lemma with parameters).
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {P F E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Congruence with a varying reference form.** A jointly `C^n` symmetric family `B (b, v)`
whose value at `(a, 0)` is invertible is, on a product neighbourhood, congruent to `B (b, 0)`
by jointly `C^n` invertible operators. The operators are the identity on the entire zero
section in that neighbourhood, and their inverses are jointly `C^n` there as well.

The parameter spaces `P` and `F` need not be complete or finite-dimensional. No definiteness
or constant-signature hypothesis is required. -/
theorem exists_parametric_congruence_of_symmetric_family
    {n : ℕ∞ω} {a : P} {B : P × F → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiff ℝ n B) (hsymm : ∀ z w w', B z w w' = B z w' w)
    (hBa : (B (a, 0)).IsInvertible) :
    ∃ (R : P × F → E →L[ℝ] E) (U : Set P) (V : Set F),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : F) ∈ V ∧
      (∀ b ∈ U, R (b, 0) = 1) ∧ ContDiffOn ℝ n R (U ×ˢ V) ∧
      ContDiffOn ℝ n (fun z ↦ (R z).inverse) (U ×ˢ V) ∧
      (∀ z ∈ U ×ˢ V, (R z).IsInvertible) ∧
      ∀ z ∈ U ×ˢ V, ∀ w w', B (z.1, 0) (R z w) (R z w') = B z w w' := by
  obtain ⟨A, hA⟩ := hBa
  obtain ⟨T, W, hW, haW, hTa, hT, hspec⟩ :=
    exists_congruence_of_symmetric_family hB hsymm A hA
  -- Shrink to a product neighbourhood where the fixed-reference operators are invertible.
  have hTa_inv : (T (a, 0)).IsInvertible := by
    rw [hTa]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  have hnear : ∀ᶠ z in 𝓝 (a, (0 : F)), (T z).IsInvertible :=
    (hT.continuousOn.continuousAt (hW.mem_nhds haW)).eventually hTa_inv.eventually_nhds
  obtain ⟨U, V, hU, haU, hV, h0V, hUV⟩ :=
    mem_nhds_prod_iff'.mp (Filter.inter_mem (hW.mem_nhds haW) hnear)
  have hsub : U ×ˢ V ⊆ W := fun z hz ↦ (hUV hz).1
  have hTi (z : P × F) (hz : z ∈ U ×ˢ V) : (T z).IsInvertible := (hUV hz).2
  let S : P × F → E →L[ℝ] E := fun z ↦ T (z.1, 0)
  have hS : ContDiffOn ℝ n S (U ×ˢ V) :=
    hT.comp (contDiffOn_fst.prodMk contDiffOn_const)
      (fun z hz ↦ hsub ⟨hz.1, h0V⟩)
  have hSi (z : P × F) (hz : z ∈ U ×ˢ V) : (S z).IsInvertible :=
    hTi (z.1, 0) ⟨hz.1, h0V⟩
  have hSinv : ContDiffOn ℝ n (fun z ↦ (S z).inverse) (U ×ˢ V) := by
    intro z hz
    exact (hSi z hz).contDiffAt_map_inverse.comp_contDiffWithinAt z (hS z hz)
  let R : P × F → E →L[ℝ] E := fun z ↦ (S z).inverse.comp (T z)
  have hR : ContDiffOn ℝ n R (U ×ˢ V) := hSinv.clm_comp (hT.mono hsub)
  have hRi (z : P × F) (hz : z ∈ U ×ˢ V) : (R z).IsInvertible := by
    obtain ⟨e, he⟩ := hSi z hz
    have hinv : (S z).inverse.IsInvertible := by
      rw [← he, ContinuousLinearMap.inverse_equiv]
      exact ContinuousLinearMap.isInvertible_equiv
    exact hinv.comp (hTi z hz)
  refine ⟨R, U, V, hU, hV, haU, h0V, ?_, hR, ?_, hRi, ?_⟩
  · intro b hb
    exact (hTi (b, 0) ⟨hb, h0V⟩).inverse_comp_self
  · intro z hz
    exact (hRi z hz).contDiffAt_map_inverse.comp_contDiffWithinAt z (hR z hz)
  · intro z hz w w'
    -- Divide by the zero-section operator on both arguments of the reference form.
    calc
      B (z.1, 0) (R z w) (R z w') =
          A (S z (R z w)) (S z (R z w')) :=
        (hspec (z.1, 0) (hsub ⟨hz.1, h0V⟩) _ _).symm
      _ = A (T z w) (T z w') := by
        simp only [R, ContinuousLinearMap.comp_apply, (hSi z hz).self_apply_inverse]
      _ = B z w w' := hspec z (hsub hz) w w'

end TauCeti
