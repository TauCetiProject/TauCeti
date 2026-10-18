/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Heights of primes along integral extensions with going down

For an integral `R`-algebra `S` with going down, both rings Noetherian, contraction preserves the
height of every prime: `ht (P ∩ R) = ht P`. A prime `P` of `S` is minimal over the extension
`(P ∩ R) S` (incomparability), so the image of `P` in `S ⧸ (P ∩ R) S` has height zero, and the
dimension formula `ht P = ht (P ∩ R) + ht (P / (P ∩ R) S)` (Stacks, Lemma 10.112.7 (00ON);
Mathlib's `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`) has vanishing second term.

The hypotheses hold for an integral extension of a domain by an integrally closed domain, which
has going down (Stacks, Proposition 10.38.7 (00H8)), for instance a finite injective extension of
Noetherian domains with integrally closed base: the affine form of a finite dominant morphism of
integral schemes onto a normal scheme.

## Main results

* `Ideal.height_under_eq_of_isIntegral`: for an integral algebra with going down between
  Noetherian rings, contraction preserves heights of primes.

## References

* [Stacks Project, Proposition 10.38.7](https://stacks.math.columbia.edu/tag/00H8) and
  [Lemma 10.112.7](https://stacks.math.columbia.edu/tag/00ON).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/Divisors.lean`:
  `height_under_eq_of_isIntegral` generalizes its `Pcf.height_under_eq_of_finite_of_normal`,
  stated there for a finite injective extension of Noetherian domains with normal base.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- For an integral algebra `S` over `R` with going down, both Noetherian, contraction preserves the
height of every prime: `ht (P ∩ R) = ht P`. -/
theorem height_under_eq_of_isIntegral [Algebra.HasGoingDown R S] [Algebra.IsIntegral R S]
    [IsNoetherianRing R] [IsNoetherianRing S] (P : Ideal S) [P.IsPrime] :
    (P.under R).height = P.height := by
  let p : Ideal R := P.under R
  let I : Ideal S := p.map (algebraMap R S)
  -- `P` is minimal over `p S` (incomparability), so its image in `S ⧸ p S` has height zero.
  have hPmin : P ∈ I.minimalPrimes := IsIntegral.mem_minimalPrimes_map_under P
  have himage : P.map (Quotient.mk I) ∈ minimalPrimes (S ⧸ I) := by
    rw [minimalPrimes_eq_comap] at hPmin
    obtain ⟨Q, hQ, hQP⟩ := hPmin
    have hQ' : Q = P.map (Quotient.mk I) := by
      rw [← hQP, map_comap_of_surjective _ Quotient.mk_surjective]
    exact hQ' ▸ hQ
  have : (P.map (Quotient.mk I)).IsPrime := himage.1.1
  have hformula := height_eq_height_add_of_liesOver_of_hasGoingDown p P
  rw [height_eq_zero_iff.mpr himage, add_zero] at hformula
  exact hformula.symm

end Ideal
