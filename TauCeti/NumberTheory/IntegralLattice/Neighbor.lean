/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Basic
public import TauCeti.NumberTheory.IntegralLattice.Genus
public import TauCeti.NumberTheory.IntegralLattice.Localization.Sublattice

/-!
# Kneser neighbors lie in one genus

If `L` and `M` are `p`-neighbors and `p` is prime to `2 det L`, then `L` and `M` have the same
genus. They share their rational form, hence their signature. At a prime `q` not dividing `p`
both localizations agree with that of `L ∩ M`, which has index `p` in each. At a prime dividing
`p` both localizations are unimodular at an odd prime, of the same rank and determinant, hence
isometric by the odd-prime unimodular classification.

This is the statement that makes neighbor steps stay inside a genus. Nothing is claimed about
reaching every class of the genus.

## Main results

* `TauCeti.IntegralLattice.IsNeighbor.sameGenus`: `p`-neighbors with `p` prime to `2 det L` lie
  in one genus.

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
* J. Voight, *Kneser's method of neighbors*, arXiv:2308.11566, §3.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L M : IntegralLattice V} {p : ℕ}

/-- **Kneser neighbors lie in one genus.** If `L` and `M` are `p`-neighbors and `p` is coprime
to `2 det L`, then `L` and `M` have the same genus. -/
theorem IsNeighbor.sameGenus (h : L.IsNeighbor M p)
    (hp : p.Coprime (2 * L.determinant.natAbs)) : L.SameGenus M := by
  have hrad : L.radical = M.radical := by
    ext x
    simp only [mem_radical_iff, h.form_eq]
  have hsig : L.signature = M.signature := by
    simp only [signature, sigPos, sigNull, sigNeg, h.form_eq]
    rw [hrad]
  have hrank : Module.finrank ℤ L = Module.finrank ℤ M := by
    rw [L.finrank_carrier, M.finrank_carrier]
  refine (sameGenus_iff L M).mpr ⟨hsig, fun q _ ↦ ?_⟩
  by_cases hq : q ∣ p
  · -- At a prime dividing `p`, both localizations are unimodular of equal rank and determinant.
    refine L.localIntegralForm_equivalent_of_not_dvd M hrank h.determinant_eq fun hq' ↦ ?_
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hp hq hq')
  · -- Away from `p`, both localizations agree with that of the intersection.
    have hL := (L.inf M).localIntegralForm_equivalent_of_le L q (inf_form L M)
      ((inf_carrier L M).trans_le inf_le_left)
      (by rwa [inf_carrier, h.relIndex_inf_left])
    have hM := (L.inf M).localIntegralForm_equivalent_of_le M q ((inf_form L M).trans h.form_eq)
      ((inf_carrier L M).trans_le inf_le_right)
      (by rwa [inf_carrier, h.relIndex_inf_right])
    exact hL.symm.trans hM

end TauCeti.IntegralLattice
