/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.RationalCompletion
public import TauCeti.RingTheory.Huber.Pair

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Proper
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Laurent.Basic

/-!
# Proper ideals on simple Laurent covers

For a simple Laurent cover `{|f| ≤ 1}`, `{|f| ≥ 1}` of `Spa(A, A⁺)`, every maximal ideal of `A`
contracts from a prime ideal of `B₁ × B₂` for any rational-completion models `B₁`, `B₂`.

## Main results

* `TauCeti.ValuationSpectrum.exists_prime_comap_eq_of_simpleLaurent`: maximal-ideal contraction for
  a simple Laurent cover.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.7, Proposition 2.7.5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 7.51.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [IsHuberRing A]

/-- Every maximal ideal of `A` contracts from a prime ideal of `B₁ × B₂` for models of a simple
Laurent cover `{|f| ≤ 1}`, `{|f| ≥ 1}` given a compatible pair of definition `P₀`. -/
theorem exists_prime_comap_eq_of_simpleLaurent [DecidableEq A] {P P₀ : PairOfDefinition A}
    (Aplus : Subring A) (hplus : IsRingOfIntegralElements Aplus)
    (hP₀ : P₀.ringOfDefinition ≤ Aplus) (f : A)
    {B₁ B₂ : Type*} [CommRing B₁] [CommRing B₂] [TopologicalSpace B₁] [TopologicalSpace B₂]
    [Algebra A B₁] [Algebra A B₂]
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂) (m : Ideal A) (hm : m.IsMaximal) :
    ∃ p : Ideal (B₁ × B₂), p.IsPrime ∧
      p.comap ((algebraMap A B₁).prod (algebraMap A B₂)) = m := by
  obtain ⟨v, hv, rfl⟩ := exists_mem_spa_supp_eq_of_isMaximal Aplus hplus m
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (spa_subset_iUnion_laurentCover Aplus f hv)
  cases b with
  | true =>
    obtain ⟨q, hq, hqm⟩ := exists_prime_comap_eq_of_mem_rationalSubset hP₀ h₁
      (by simpa [mem_rationalSubset_iff] using hb) hm
    exact ⟨q.comap (RingHom.fst B₁ B₂), hq.comap _, by rw [Ideal.comap_comap]; exact hqm⟩
  | false =>
    obtain ⟨q, hq, hqm⟩ := exists_prime_comap_eq_of_mem_rationalSubset hP₀ h₂
      (by simpa [mem_rationalSubset_iff] using hb) hm
    exact ⟨q.comap (RingHom.snd B₁ B₂), hq.comap _, by rw [Ideal.comap_comap]; exact hqm⟩

end TauCeti.ValuationSpectrum

end
