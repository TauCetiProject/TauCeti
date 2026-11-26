/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Values
import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.Character.Basic

/-!
# Polynomial expressions for finite-order character values

At an element of order dividing `n`, a character is the evaluation of an integer polynomial
at a primitive `n`-th root of unity. Evaluation of the same polynomial at `1` gives the
dimension. This keeps track of the dimension when specializing roots of unity to `1`.
-/

public section

open Polynomial

namespace Representation

/-- At an element killed by the `n`-th power, a character is a sum of powers of a primitive
`n`-th root. The polynomial recording those powers evaluates at `1` to the dimension. -/
theorem exists_aeval_eq_character_and_eval_one_eq_finrank {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {g : G} {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (hg : g ^ n = 1) :
    ∃ P : ℤ[X], aeval ζ P = ρ.character g ∧ P.eval 1 = Module.finrank k V := by
  classical
  by_cases hf : Module.Finite k V
  swap
  · exact ⟨0, by simp [ρ.character_eq_zero_of_not_finite hf, Module.finrank_of_not_finite hf]⟩
  let L := AlgebraicClosure k
  let f : k →ₐ[ℤ] L := IsScalarTower.toAlgHom ℤ k L
  have hζL : IsPrimitiveRoot (f ζ) n := hζ.map_of_injective (algebraMap k L).injective
  obtain ⟨s, hcard, hroot, hchar⟩ := (ρ.baseChange L).exists_multiset_rootsOfUnity_char_eq_sum hg
  choose e _ he using fun μ : {μ // μ ∈ s} ↦ hζL.eq_pow_of_pow_eq_one (hroot μ μ.property)
  refine ⟨(s.attach.map fun μ ↦ X ^ e μ).sum, ?_, ?_⟩
  · apply (algebraMap k L).injective
    rw [← ρ.character_baseChange (L := L) g, hchar]
    calc
      _ = aeval (f ζ) _ := (aeval_algHom_apply f ζ _).symm
      _ = s.sum := by
        rw [map_multiset_sum, Multiset.map_map]
        simp only [Function.comp_def, map_pow, aeval_X, he, Multiset.attach_map_val]
  · rw [← Module.finrank_baseChange (R := L), ← hcard, ← coe_evalRingHom,
      map_multiset_sum, Multiset.map_map]
    simp

end Representation
