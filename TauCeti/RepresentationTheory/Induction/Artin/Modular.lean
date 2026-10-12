/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Projection
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.PrimePower
public import TauCeti.GroupTheory.ArtinCoefficient
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Removing the prime part of cyclic induction in the exact Grothendieck ring

In characteristic `p`, let `D ≤ C ≤ G`, with `D` normal in `C` and `C/D` of `p`-power
exponent. The permutation-class identity
`TauCeti.indK0_of_trivial_eq_relIndex_nsmul` and the projection formula give

`Ind_D^G Res_D^G x = [C : D] • Ind_C^G Res_C^G x`

for every class `x` in `G₀(k[G])`. In particular, when `C` is cyclic, its subgroup `D` of
order prime to `p` replaces the term `|C| • Ind_C^G Res_C^G x` by
`|D| • Ind_D^G Res_D^G x`, including for nonsplit representations.

The final theorem rewrites the full Artin coefficient sum as a finite integral linear
combination of induction terms from cyclic subgroups of order prime to `p`. The coefficients
work simultaneously for all `x`. This is the prime-part removal in modular Artin induction;
the equality of the Artin sum with `|G| • x` is a separate input.

## Main results

* `TauCeti.indK0_resK0_eq_relIndex_nsmul`: removal across a normal quotient of `p`-power exponent.
* `Subgroup.exists_coprimePart_natCard_nsmul_indK0_resK0`: the coefficient identity for a cyclic
  subgroup and its prime-to-`p` part.
* `TauCeti.exists_linearCombination_indK0_resK0_eq_sum_artinCoeff`: the full Artin sum uses only
  cyclic subgroups of order prime to `p`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  §VII.3, (7.3.4).
* J.-P. Serre, *Linear Representations of Finite Groups*, Part II, §9.2.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G]
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Across a normal quotient of `p`-power exponent, inducing a restricted class from the
smaller subgroup multiplies induction from the larger subgroup by their relative index. -/
theorem indK0_resK0_eq_relIndex_nsmul {C D : Subgroup G} (h : D ≤ C)
    [(D.subgroupOf C).Normal] (hpow : ∀ c ∈ C, ∃ n : ℕ, c ^ p ^ n ∈ D)
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    indK0 k D (resK0 k D.subtype x) =
      D.relIndex C • indK0 k C (resK0 k C.subtype x) := by
  have hunit : indK0 k D 1 = D.relIndex C • indK0 k C 1 := by
    simpa only [← exactK0_one_eq_of_trivial] using
      indK0_of_trivial_eq_relIndex_nsmul (k := k) p h hpow
  simpa only [← indK0_mul_resK0, one_mul, smul_mul_assoc] using congrArg (· * x) hunit

variable {p} in
/-- For a finite cyclic subgroup `C`, its prime-to-`p` part `D` removes the `p`-part of the
coefficient `|C|` in every induced restriction, uniformly in the Grothendieck class. -/
theorem _root_.Subgroup.exists_coprimePart_natCard_nsmul_indK0_resK0 (C : Subgroup G) [IsCyclic C] :
    ∃ D : Subgroup G, D ≤ C ∧ IsCyclic D ∧ ¬ p ∣ Nat.card D ∧
      D.relIndex C = p ^ (Nat.card C).factorization p ∧
      ∀ x : ExactK0 (finiteModulesExactStructure k[G]),
        Nat.card C • indK0 k C (resK0 k C.subtype x) =
          Nat.card D • indK0 k D (resK0 k D.subtype x) := by
  obtain ⟨D, hDC, hDn, hDp, hpow, hindex⟩ :=
    exists_coprimePart_of_isCyclic (Fact.out : p.Prime) (C := C)
  let := hDn
  have hDcyc : IsCyclic D := Subgroup.isCyclic_of_le hDC
  refine ⟨D, hDC, hDcyc, hDp, hindex, fun x ↦ ?_⟩
  have hcard := D.relIndex_mul_card C
  rw [inf_eq_left.mpr hDC] at hcard
  rw [indK0_resK0_eq_relIndex_nsmul p hDC hpow, ← mul_nsmul, hcard]

/-- The Artin coefficient sum is an integral linear combination of induced restrictions from
cyclic subgroups of order prime to the characteristic. A single finitely supported coefficient
family gives the identity for every class in the exact Grothendieck ring. -/
theorem exists_linearCombination_indK0_resK0_eq_sum_artinCoeff :
    ∃ a : {D : Subgroup G // IsCyclic D ∧ ¬ p ∣ Nat.card D} →₀ ℤ,
      ∀ x : ExactK0 (finiteModulesExactStructure k[G]),
        Finsupp.linearCombination ℤ
            (fun D : {D : Subgroup G // IsCyclic D ∧ ¬ p ∣ Nat.card D} ↦
              indK0 k D.val (resK0 k D.val.subtype x)) a =
          ∑ᶠ C : Subgroup G,
            (C.artinCoeff * (Nat.card C : ℤ)) • indK0 k C (resK0 k C.subtype x) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  have hterm (C : Subgroup G) :
      ∃ D : {D : Subgroup G // IsCyclic D ∧ ¬ p ∣ Nat.card D},
        ∀ x : ExactK0 (finiteModulesExactStructure k[G]),
          (C.artinCoeff * (Nat.card D.val : ℤ)) •
              indK0 k D.val (resK0 k D.val.subtype x) =
            (C.artinCoeff * (Nat.card C : ℤ)) • indK0 k C (resK0 k C.subtype x) := by
    by_cases hC : IsCyclic C
    · let := hC
      obtain ⟨D, -, hDcyc, hDp, -, hD⟩ :=
        C.exists_coprimePart_natCard_nsmul_indK0_resK0 (k := k) (p := p)
      refine ⟨⟨D, hDcyc, hDp⟩, fun x ↦ ?_⟩
      simpa only [mul_smul, natCast_zsmul] using congrArg (C.artinCoeff • ·) (hD x).symm
    · refine ⟨⟨⊥, inferInstance, ?_⟩, fun x ↦ ?_⟩
      · simpa using (Fact.out : p.Prime).not_dvd_one
      · simp [C.artinCoeff_eq_zero_of_not_isCyclic hC]
  choose D hD using hterm
  refine ⟨∑ C : Subgroup G,
    Finsupp.single (D C) (C.artinCoeff * (Nat.card (D C).val : ℤ)), fun x ↦ ?_⟩
  simp only [map_sum, Finsupp.linearCombination_single, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun C _ ↦ hD C x

end TauCeti
