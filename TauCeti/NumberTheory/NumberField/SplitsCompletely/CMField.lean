/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Splitting of finite primes in a CM extension

A prime of the maximal real subfield splits in the CM field if and only if complex
conjugation moves a prime above it. This expresses complete splitting using the only
nonidentity automorphism of the quadratic extension.
-/

public section

open NumberField NumberField.IsCMField
open scoped NumberField Pointwise

namespace Ideal

/-- A prime splits in a CM extension if and only if complex conjugation does not fix a prime
above it. -/
theorem ncard_primesOver_eq_two_iff_complexConj_notMem_stabilizer
    {E : Type*} [Field E] [NumberField E] [IsCMField E] (P : Ideal (𝓞 E)) [P.IsPrime] :
    ((P.under (𝓞 (maximalRealSubfield E))).primesOver (𝓞 E)).ncard = 2 ↔
      complexConj E ∉ MulAction.stabilizer (E ≃ₐ[maximalRealSubfield E] E) P := by
  have : P.LiesOver (P.under (𝓞 (maximalRealSubfield E))) := ⟨rfl⟩
  rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot _ _ _ P]
  refine ⟨fun h hc ↦ complexConj_ne_one E (Subgroup.mem_bot.mp (h ▸ hc)), fun h ↦ ?_⟩
  have hcard : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2 :=
    (IsGalois.card_aut_eq_finrank (maximalRealSubfield E) E).trans
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  have : Fact (Nat.card (E ≃ₐ[maximalRealSubfield E] E)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  exact (MulAction.stabilizer (E ≃ₐ[maximalRealSubfield E] E) P).eq_bot_or_eq_top_of_prime_card
    |>.resolve_right fun ht ↦ h (ht ▸ Subgroup.mem_top _)

end Ideal
