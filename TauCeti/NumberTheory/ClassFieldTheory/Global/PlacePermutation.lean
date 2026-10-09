/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Permutation.Augmentation
public import TauCeti.RepresentationTheory.Rep.OfMulAction
public import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# Finite-place permutation lattices

For a finite Galois extension of number fields `L/K` and a finite set `S` of finite places of
`K`, the permutation lattice on the primes of `L` above `S` has Herbrand quotient
`∏ v ∈ S, [L_w : K_v]`. Each factor is independent of the choice of a prime `w` above `v`.
Cyclicity is not needed. This supplies the finite-place factors in the permutation lattice
used to compare the logarithmic `S`-unit lattice with the augmentation hyperplane.
For cyclic `L/K` and nonempty `S`, the sum-zero lattice on these finite places has quotient
`∏ v ∈ S, [L_w : K_v] / [L : K]`. Archimedean factors and the logarithmic comparison with
`S`-units are separate from this finite-place calculation.

The calculation combines
`TauCeti.TateCohomology.herbrandQuotient_ofMulAction_sigma_of_isPretransitive` with
`IsDedekindDomain.HeightOneSpectrum.card_stabilizer_eq_finrank_adicCompletion`.

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_ofMulAction_primesAbove`: the local-degree product
  on the canonical `HeightOneSpectrum.primesAbove` carrier.
* `TauCeti.ClassFieldTheory.herbrandQuotient_augmentationSubrepresentation_primesAbove`: the
  sum-zero lattice's quotient, with denominator the global degree.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §3.
* J. Tate, *Global class field theory*, in Cassels and Fröhlich, *Algebraic Number Theory*,
  Chapter VII.
-/

public noncomputable section

open IsDedekindDomain MulAction
open scoped NumberField Pointwise AdicCompletionExtension

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- The permutation lattice on the primes above a finite set of finite places has Herbrand
quotient the product of the corresponding local degrees. The primes above each place may
be chosen arbitrarily. -/
private theorem herbrandQuotient_ofMulAction_sigma_primesOver
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : ∀ v : S, {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal}) :
    TateCohomology.herbrandQuotient
      (Rep.ofMulAction ℤ (L ≃ₐ[K] L) (Σ v : S, v.1.asIdeal.primesOver (𝓞 L))) =
        ∏ v : S, (Module.finrank (v.1.adicCompletion K) ((w v).1.adicCompletion L) : ℚ) := by
  classical
  let x (v : S) := HeightOneSpectrum.liesOverEquivPrimesOver (𝓞 L) v.1 (w v)
  rw [TateCohomology.herbrandQuotient_ofMulAction_sigma_of_isPretransitive x]
  apply Finset.prod_congr rfl
  intro v _
  rw [stabilizer_primesOver_ringOfIntegers,
    HeightOneSpectrum.liesOverEquivPrimesOver_apply,
    HeightOneSpectrum.card_stabilizer_eq_finrank_adicCompletion v.1 (w v).1]

/-- The permutation lattice on the canonical carrier of primes above a finite set of finite
places has Herbrand quotient the product of their local degrees. The prime above each place
may be chosen arbitrarily. -/
theorem herbrandQuotient_ofMulAction_primesAbove
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : ∀ v : S, {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal}) :
    TateCohomology.herbrandQuotient
      (Rep.ofMulAction ℤ (L ≃ₐ[K] L) ↥(HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) ↑S)) =
        ∏ v : S, (Module.finrank (v.1.adicCompletion K) ((w v).1.adicCompletion L) : ℚ) := by
  let e := ofMulActionIsoCongr ℤ (sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) ↑S)
    (sigmaPrimesOverEquivPrimesAbove_smul K L ↑S)
  rw [← TateCohomology.herbrandQuotient_eq_of_iso e]
  exact herbrandQuotient_ofMulAction_sigma_primesOver S w

/-- For a cyclic extension and a nonempty finite set of finite places, the sum-zero lattice
on the primes above those places has Herbrand quotient the product of local degrees divided
by the global degree. This is the finite-place augmentation calculation, not yet the
Herbrand quotient of the `S`-units. -/
theorem herbrandQuotient_augmentationSubrepresentation_primesAbove
    [IsCyclic (L ≃ₐ[K] L)] (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : S.Nonempty)
    (w : ∀ v : S, {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal}) :
    TateCohomology.herbrandQuotient (Rep.of
      (augmentationSubrepresentation ℤ (L ≃ₐ[K] L)
        ↥(HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) ↑S)).toRepresentation) =
      (∏ v : S, (Module.finrank (v.1.adicCompletion K) ((w v).1.adicCompletion L) : ℚ)) /
        Module.finrank K L := by
  obtain ⟨v, hv⟩ := hS
  have : Nonempty ↥(HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) ↑S) :=
    ⟨sigmaPrimesOverEquivPrimesAbove (𝓞 K) (𝓞 L) ↑S
      ⟨⟨v, hv⟩, HeightOneSpectrum.liesOverEquivPrimesOver (𝓞 L) v (w ⟨v, hv⟩)⟩⟩
  rw [TateCohomology.herbrandQuotient_augmentationSubrepresentation_eq_div,
    herbrandQuotient_ofMulAction_primesAbove S w, IsGalois.card_aut_eq_finrank K L]

end TauCeti.ClassFieldTheory
