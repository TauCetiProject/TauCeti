/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Graded
import TauCeti.NumberTheory.LocalField.Norm.PrimeDegree

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

* `TauCeti.norm_one_add_sub_one_sub_norm_mem_maximalIdeal_pow_succ`: the norm expansion
  modulo the next filtration step.
* `TauCeti.algebraMap_residue_eq_pow_of_norm_one_add_mul_pow_eq_before_break`: the residue
  formula `N(1 + a π^v) ≡ 1 + a^ℓ N(π)^v`.
* `TauCeti.algebraMap_normGradedMap_coordinate_before_break`: the Frobenius coordinate of
  the graded norm of a representative.

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

/-- Before a ramification break in prime degree, the trace terms in `N(1 + z)` vanish
modulo the next power of the maximal ideal. -/
theorem norm_one_add_sub_one_sub_norm_mem_maximalIdeal_pow_succ
    (hℓ : (finrank K L).Prime) {v : ℕ}
    (hG : lowerRamificationGroup K L (v + 1) = ⊤) {z : 𝒪[L]} (hz : z ∈ 𝓂[L] ^ v) :
    Algebra.norm 𝒪[K] (1 + z) - 1 - Algebra.norm 𝒪[K] z ∈ 𝓂[K] ^ (v + 1) := by
  obtain ⟨w, hw, hN⟩ := exists_norm_one_add_eq_of_mem_maximalIdeal_pow hℓ hz
  have heq : Algebra.norm 𝒪[K] (1 + z) - 1 - Algebra.norm 𝒪[K] z =
      Algebra.trace 𝒪[K] 𝒪[L] z + Algebra.trace 𝒪[K] 𝒪[L] w := by
    rw [hN]
    ring
  rw [heq]
  exact add_mem (trace_mem_maximalIdeal_pow_succ hℓ.two_le hG hz)
    (trace_mem_maximalIdeal_pow_succ hℓ.two_le hG
      (Ideal.pow_le_pow_right (show v ≤ 2 * v by omega) hw))

/-- Let `π` be a uniformizer of `L` and let the depth `v` lie strictly before the
break of a prime-degree extension. If `N(1 + a π^v) = 1 + b N(π)^v`, then the residue of `b`,
viewed in the residue field of `L`, is the `ℓ`-th power of the residue of `a`. -/
theorem algebraMap_residue_eq_pow_of_norm_one_add_mul_pow_eq_before_break
    (hℓ : (finrank K L).Prime) {v : ℕ}
    (hG : lowerRamificationGroup K L (v + 1) = ⊤) {π : 𝒪[L]} (hπ : Irreducible π)
    {a : 𝒪[L]} {b : 𝒪[K]}
    (hab : Algebra.norm 𝒪[K] (1 + a * π ^ v) = 1 + b * Algebra.norm 𝒪[K] π ^ v) :
    algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] b) = residue 𝒪[L] a ^ finrank K L := by
  have h : IsTotallyRamified K L := (lowerRamificationGroup_zero_eq_top_iff K L).1 <|
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (by omega))
  have hπK : Irreducible (Algebra.norm 𝒪[K] π) :=
    (irreducible_norm_iff_inertiaDegree_eq_one_of_irreducible hπ).2 h.inertiaDegree_eq_one
  have hz : a * π ^ v ∈ 𝓂[L] ^ v := Ideal.mul_mem_left _ a <|
    Ideal.pow_mem_pow ((mem_maximalIdeal π).2 hπ.not_isUnit) v
  have hrem := norm_one_add_sub_one_sub_norm_mem_maximalIdeal_pow_succ hℓ hG hz
  have heq : Algebra.norm 𝒪[K] (1 + a * π ^ v) - 1 -
      Algebra.norm 𝒪[K] (a * π ^ v) =
        (b - Algebra.norm 𝒪[K] a) * Algebra.norm 𝒪[K] π ^ v := by
    rw [hab, map_mul, map_pow]
    ring
  rw [heq, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπK,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hrem
  obtain ⟨d, hd⟩ := hrem
  have hcoeff : b - Algebra.norm 𝒪[K] a = d * Algebra.norm 𝒪[K] π := by
    apply mul_right_cancel₀ (pow_ne_zero v hπK.ne_zero)
    rw [← hd]
    ring
  have hmem : b - Algebra.norm 𝒪[K] a ∈ 𝓂[K] := by
    rw [hcoeff]
    exact Ideal.mul_mem_left _ d ((mem_maximalIdeal _).2 hπK.not_isUnit)
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hmem
  rw [hmem, algebraMap_residue_norm_of_isTotallyRamified h]

/-- In uniformizer coordinates, the positive-depth graded norm strictly before a
prime-degree ramification break sends `y` to `y^ℓ`. The target uniformizer is the norm of
the source uniformizer. The source representative is written as `1 + a π^(v+1)`, so its
coordinate is the residue of `a`. -/
theorem algebraMap_normGradedMap_coordinate_before_break
    (hℓ : (finrank K L).Prime) {v : ℕ}
    (hG : lowerRamificationGroup K L (v + 2) = ⊤) {π : 𝒪[L]} (hπ : Irreducible π)
    (hπK : Irreducible (Algebra.norm 𝒪[K] π))
    (x : unitFiltration L (psiNat K L (v + 1))) {a : 𝒪[L]}
    (hxa : ((x : Lˣ) : L) = 1 + a * π ^ (v + 1)) :
    algebraMap 𝓀[K] 𝓀[L] (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer v
        (Algebra.norm 𝒪[K] π) hπK
        (Additive.ofMul (normGradedMap K L (v + 1) (QuotientGroup.mk x)))) =
      residue 𝒪[L] a ^ finrank K L := by
  rw [normGradedMap_mk]
  let y : unitFiltration K (v + 1) := ⟨Algebra.normUnits K (x : Lˣ),
    map_normUnits_unitFiltration_psiNat_le K L (v + 1) (Subgroup.mem_map_of_mem _ x.2)⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝒪[K], b * Algebra.norm 𝒪[K] π ^ (v + 1) =
      (unitFiltrationDifference v y : 𝒪[K]) := by
    have hspan : 𝓂[K] ^ (v + 1) = Ideal.span {Algebra.norm 𝒪[K] π ^ (v + 1)} := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπK,
        Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.1 (hspan ▸ (unitFiltrationDifference v y).2)
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue v _ hπK y b
    hb.symm]
  refine algebraMap_residue_eq_pow_of_norm_one_add_mul_pow_eq_before_break hℓ
    (by convert hG using 1; congr 1) hπ ?_
  apply Subtype.ext
  have hb' := congrArg (fun z : 𝒪[K] ↦ (z : K)) hb
  simp only [coe_coe_unitFiltrationDifference, y, Algebra.coe_normUnits] at hb'
  have hx : ((1 + a * π ^ (v + 1) : 𝒪[L]) : L) = ((x : Lˣ) : L) := by
    rw [hxa]
    simp
  push_cast
  rw [coe_norm_integerRing, coe_norm_integerRing, hx]
  push_cast at hb'
  rw [coe_norm_integerRing] at hb'
  linear_combination -hb'

end TauCeti
