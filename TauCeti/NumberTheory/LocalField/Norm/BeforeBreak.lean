/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Graded

/-!
# Frobenius coordinates for the norm before a ramification break

In a Galois extension `L/K` of prime degree `ℓ`, the norm on a positive unit-filtration
quotient strictly before the ramification break is `y ↦ y^ℓ` on the additive residue field.
The coordinates use a uniformizer `π` of `L` and its norm `N(π)` in `K`. The residue fields
are identified by their canonical algebra map. In this regime `ℓ` is the residue
characteristic, so this is the Frobenius map, not just an unspecified bijection.

The condition `G_{v+1} = Gal(L/K)` expresses that depth `v` lies strictly before the break.
It implies total ramification and `ψℕ(v) = v`. The trace terms in the prime-degree norm
expansion vanish modulo `𝓂[K]^(v+1)`, leaving the norm of the difference from one.
These coordinate formulas complement the bijectivity statements for `normGradedMap` and
allow calculations on particular residue classes.

## Main results

* `TauCeti.algebraMap_residue_eq_pow_of_norm_one_add_mul_pow_eq_before_break`: the residue
  formula `N(1 + a π^v) ≡ 1 + a^ℓ N(π)^v`.
* `algebraMap_unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_normGradedMap_mk_before_break`:
  the Frobenius coordinate of the graded norm of a representative.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3, Lemma 5 and Proposition 5.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing Module TauCeti.LocalFieldsRamification

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-- Let `π` be a uniformizer of `L` and let the depth `v` lie strictly before the
break of a prime-degree extension. If `N(1 + a π^v) = 1 + b N(π)^v`, then the residue of `b`,
viewed in the residue field of `L`, is the `ℓ`-th power of the residue of `a`. -/
theorem algebraMap_residue_eq_pow_of_norm_one_add_mul_pow_eq_before_break
    (hℓ : (finrank K L).Prime) {v : ℕ}
    (hG : lowerRamificationGroup K L (v + 1) = ⊤) {π : 𝒪[L]} (hπ : Irreducible π)
    {a : 𝒪[L]} {b : 𝒪[K]}
    (hab : Algebra.norm 𝒪[K] (1 + a * π ^ v) = 1 + b * Algebra.norm 𝒪[K] π ^ v) :
    algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] b) = residue 𝒪[L] a ^ finrank K L := by
  have h := isTotallyRamified_of_lowerRamificationGroup_eq_top (by omega) hG
  have hπK := h.irreducible_norm hπ
  have hz : a * π ^ v ∈ 𝓂[L] ^ v := Ideal.mul_mem_left _ a <|
    Ideal.pow_mem_pow ((mem_maximalIdeal π).2 hπ.not_isUnit) v
  have hrem := norm_one_add_sub_one_sub_norm_mem_maximalIdeal_pow_succ hℓ hG hz
  have heq : Algebra.norm 𝒪[K] (1 + a * π ^ v) - 1 -
      Algebra.norm 𝒪[K] (a * π ^ v) =
        (b - Algebra.norm 𝒪[K] a) * Algebra.norm 𝒪[K] π ^ v := by
    rw [hab, map_mul, map_pow]
    ring
  rw [heq] at hrem
  have hmem :=
    IsDiscreteValuationRing.mem_maximalIdeal_of_mul_pow_mem_maximalIdeal_pow_succ hπK hrem
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hmem
  rw [hmem, algebraMap_residue_norm_of_isTotallyRamified h]

/-- In uniformizer coordinates, the positive-depth graded norm strictly before a
prime-degree ramification break sends `y` to `y^ℓ`. The target uniformizer is the norm of
the source uniformizer. The source representative is written as `1 + a π^(v+1)`, so its
coordinate is the residue of `a`. -/
theorem
  algebraMap_unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_normGradedMap_mk_before_break
    (hℓ : (finrank K L).Prime) {v : ℕ}
    (hG : lowerRamificationGroup K L (v + 2) = ⊤) {π : 𝒪[L]} (hπ : Irreducible π)
    (hπK : Irreducible (Algebra.norm 𝒪[K] π))
    (x : unitFiltration L (psiNat K L (v + 1))) {a : 𝒪[L]}
    (hxa : ((x : Lˣ) : L) = 1 + a * π ^ (v + 1)) :
    algebraMap 𝓀[K] 𝓀[L] (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer v
        (Algebra.norm 𝒪[K] π) hπK
        (Additive.ofMul (normGradedMap K L (v + 1) (QuotientGroup.mk x)))) =
      residue 𝒪[L] a ^ finrank K L := by
  obtain ⟨b, hab, hb⟩ :=
    exists_unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_normGradedMap_mk_eq_residue
      hπK x hxa
  rw [hb]
  exact algebraMap_residue_eq_pow_of_norm_one_add_mul_pow_eq_before_break hℓ
    (by convert hG using 2; push_cast; ring) hπ hab

end TauCeti
