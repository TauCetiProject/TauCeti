/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Algebra.Lie.GeneralLinear.Carrier
public import TauCeti.Algebra.Lie.GeneralLinear.Casimir
public import TauCeti.Algebra.Lie.Sl2.Generated

/-!
# Rank-two highest-weight carriers

A dominant integral weight of `gl₂` has a natural-number difference between its two entries,
while the entries themselves need not be integral. Restriction of the actual highest-weight
carrier to `sl₂` identifies it with the corresponding standard module. This computes its
dimension and separates the semisimple weight difference from the unrestricted central scalar.
The two scalar examples also check the identity and trace-form Casimir on the same carrier.
-/

public section

open LieAlgebra LieModule

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [CharZero K] {mu : Fin 2 → K} {n : ℕ}

/-- The restriction of the rank-two highest-weight carrier to `sl₂` is `V(n)`, where `n` is
the difference of its highest weights. The central direction is unrestricted. -/
theorem nonempty_lieModuleEquiv_glIrreducible_two (hn : mu 0 - mu 1 = (n : K)) :
    Nonempty (glIrreducible 2 mu ≃ₗ⁅K, SpecialLinear.sl (Fin 2) K⁆ Sl2Std K n) := by
  have hmu : IsGlDominantIntegral mu := by
    rw [isGlDominantIntegral_iff]
    intro i j hij
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 1 := Fin.ext (by omega)
    exact ⟨n, by simpa only [hi, hj] using hn⟩
  let := isIrreducible_glIrreducible_restrict_sl hmu
  have hv := isGlHighestWeightVector_glIrreducibleGenerator hmu
  have hP : (isSl2Triple_single (R := K) (zero_ne_one : (0 : Fin 2) ≠ 1)).HasPrimitiveVectorWith
      (glIrreducibleGenerator 2 mu) (n : K) := by
    refine ⟨hv.ne_zero, ?_, ?_⟩
    · rw [LieSubalgebra.coe_bracket_of_module, SpecialLinear.val_singleSubSingle,
        sub_lie, hv.lie_single_self_eq_smul, hv.lie_single_self_eq_smul, ← sub_smul, hn]
    · rw [LieSubalgebra.coe_bracket_of_module, SpecialLinear.val_single]
      exact hv.lie_single_eq_zero (by decide)
  let p := LieSubmodule.lieSpan K (SpecialLinear.sl (Fin 2) K) {glIrreducibleGenerator 2 mu}
  obtain ⟨e⟩ : Nonempty (p ≃ₗ⁅K, SpecialLinear.sl (Fin 2) K⁆ Sl2Std K n) :=
    Sl2Std.nonempty_lieModuleEquiv_lieSpan_singleton hP
  have ht : p = ⊤ := lieSpan_singleton_eq_top_of_ne_zero hv.ne_zero
  rw [ht] at e
  exact ⟨(LieModuleEquiv.ofTop K (SpecialLinear.sl (Fin 2) K) _).symm.trans e⟩

/-- The dimension of the rank-two highest-weight carrier is one more than the weight difference. -/
theorem finrank_glIrreducible_two (hn : mu 0 - mu 1 = (n : K)) :
    Module.finrank K (glIrreducible 2 mu) = n + 1 := by
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_glIrreducible_two hn
  rw [e.toLinearEquiv.finrank_eq, Sl2Std.finrank_eq]

/-- The identity acts by the sum of the two weights. Neither weight is required to be integral. -/
example (hmu : IsGlDominantIntegral mu) (v : glIrreducible 2 mu) :
    ⁅(1 : Matrix (Fin 2) (Fin 2) K), v⁆ = (mu 0 + mu 1) • v := by
  simpa only [Fin.sum_univ_two] using one_lie_glIrreducible_eq_smul hmu v

/-- The trace-form Casimir on the carrier has the expected rank-two scalar. -/
example (hmu : IsGlDominantIntegral mu) (v : glIrreducible 2 mu) :
    UniversalEnvelopingAlgebra.representation K (Matrix (Fin 2) (Fin 2) K)
        (glIrreducible 2 mu) (glCasimir K (Fin 2)) v =
      (mu 0 * (mu 0 + 1) + mu 1 * (mu 1 - 1)) • v := by
  have h := glCasimir_smul_of_isGlHighestWeightVector_of_lieSpan_eq_top (K := K)
    (isGlHighestWeightVector_glIrreducibleGenerator hmu)
    (lieSpan_glIrreducibleGenerator_eq_top hmu) v
  convert h using 1
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  congr 1
  ring

end TauCeti
