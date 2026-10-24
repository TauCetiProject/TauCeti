/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
import TauCeti.FieldTheory.IntermediateField.Card
import TauCeti.NumberTheory.LocalField.RootCount
import TauCeti.RingTheory.Polynomial.Approximation

/-!
# Countability of totally ramified extensions of fixed degree

For a nonarchimedean local field `K`, the family `totallyRamifiedOfDegree K n` inside its
separable closure is countable. This permits exchanging its sum with a nonnegative integral
in the mass formula, including in equal characteristic where the family can be infinite.

Finite coefficient quotients give a countable family of monic Eisenstein polynomials of degree
`n` approximating all such polynomials. The uniform root-count theorem
`TauCeti.exists_card_aroots_eq` implies that every counted extension contains a root of one of
the approximants. That root generates the extension, since its degree is `n`. Each approximant
has only finitely many roots in the separable closure, so these generated fields form a
countable cover. In particular, the argument does not use the mass formula or its convergence.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §§2–3.
-/

public section

open ValuativeRel Polynomial
open scoped IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The totally ramified degree-`n` subextensions of a separable closure of a nonarchimedean
local field form a countable set, also in equal characteristic. -/
theorem countable_totallyRamifiedOfDegree {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree K n).Countable := by
  classical
  -- Approximate within the Eisenstein locus itself, so every chosen polynomial still has
  -- the prescribed degree and its roots generate extensions of that degree.
  let S : Set 𝒪[K][X] := {f | f.Monic ∧ f.IsEisensteinAt 𝓂[K] ∧ f.natDegree = n}
  have hquot (k : ℕ) : Countable (𝒪[K] ⧸ 𝓂[K] ^ k) := by
    have : Finite (𝒪[K] ⧸ 𝓂[K] ^ k) := Ring.HasFiniteQuotients.finiteQuotient
      (pow_ne_zero k (IsDiscreteValuationRing.not_a_field 𝒪[K]))
    infer_instance
  obtain ⟨s, hsS, hs, happrox⟩ :=
    (𝓂[K]).exists_countable_polynomial_approximations
      hquot S (fun f hf ↦ hf.2.2.le)
  have hcover : (⋃ f ∈ s, {L : IntermediateField K (SeparableClosure K) |
      ∃ x ∈ (f.map (algebraMap 𝒪[K] K)).rootSet (SeparableClosure K), L = K⟮x⟯}).Countable :=
    hs.biUnion fun f _ ↦ (IntermediateField.finite_setOf_exists_mem_eq_adjoin_simple_of_finite
      ((f.map (algebraMap 𝒪[K] K)).rootSet_finite (SeparableClosure K))).countable
  refine hcover.mono fun L hL ↦ ?_
  have hL' := mem_totallyRamifiedOfDegree_iff.mp hL
  have := hL'.2.finite
  obtain ⟨f, x, hf, hfe, hdeg, hx, hgen⟩ :=
    exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hL
  -- The defining polynomial is separable because it is the minimal polynomial of a
  -- generator lying in the separable closure. This excludes inseparable Eisenstein examples.
  have hsep : (f.map (algebraMap 𝒪[K] K)).Separable := by
    have hirr : Irreducible f := hfe.irreducible
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).isPrime hf.isPrimitive (hdeg ▸ hn)
    have heq := minpoly.eq_of_irreducible_of_monic
      ((hf.irreducible_iff_irreducible_map_fraction_map).mp hirr) hx
      (hf.map (algebraMap 𝒪[K] K))
    rw [heq]
    exact Algebra.IsSeparable.isSeparable K x
  obtain ⟨T, -, hT⟩ := exists_card_aroots_eq (SeparableClosure K) hf hsep
  obtain ⟨g, hgs, hgf⟩ := happrox f ⟨hf, hfe, hdeg⟩ T
  obtain ⟨hg, hge, hgdeg⟩ := hsS hgs
  have hcount := hT L g hg hgf
  -- A root of `f` lies in `L`; constancy of the root count supplies a root of `g` there.
  let y : L := ⟨x, hgen ▸ IntermediateField.mem_adjoin_simple_self K x⟩
  have hy : aeval y (f.map (algebraMap 𝒪[K] K)) = 0 :=
    (aeval_algebraMap_eq_zero_iff_of_injective (x := y) L.val.injective).mp hx
  have hpos : 0 < ((g.map (algebraMap 𝒪[K] K)).aroots L).card := by
    rw [hcount]
    exact Multiset.card_pos_iff_exists_mem.mpr
      ⟨y, mem_aroots.mpr ⟨(hf.map _).ne_zero, hy⟩⟩
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  have hzroot : aeval (L.val z) (g.map (algebraMap 𝒪[K] K)) = 0 := by
    rw [aeval_algHom_apply, (mem_aroots.mp hz).2, map_zero]
  -- The root generates all of `L`, not just a subfield, by equality of the degrees.
  have hzdeg := (mem_totallyRamifiedOfDegree_iff.mp
    (adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hge hgdeg hzroot)).1
  have hzgen : K⟮L.val z⟯ = L :=
    IntermediateField.eq_of_le_of_finrank_eq
      (IntermediateField.adjoin_simple_le_iff.mpr z.property) (hzdeg.trans hL'.1.symm)
  refine Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hgs, ?_⟩⟩
  exact ⟨L.val z, (hg.map _).mem_rootSet.mpr hzroot, hzgen.symm⟩

end TauCeti
