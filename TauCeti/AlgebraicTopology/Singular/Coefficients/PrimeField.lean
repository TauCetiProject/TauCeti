/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence

import TauCeti.Algebra.Category.ModuleCat.AB
import TauCeti.Algebra.Module.Torsion.Int

/-!
# Integral singular homology from homology with prime field coefficients

Letting `m` run through the primes in the mod-`m` coefficient sequence
(`TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence`), integral homology is
controlled by homology with coefficients in the prime fields. If `Hₙ₊₁(X; 𝔽_p) = 0` for every
prime `p`, then `Hₙ(X; ℤ)` is torsion-free
(`TopCat.isTorsionFree_singularHomology_of_forall_isZero_zmod`), hence free when it is finitely
generated. If `Hₙ(X; 𝔽_p) = 0` for every prime `p` and `Hₙ(X; ℤ)` is finitely generated, then
`Hₙ(X; ℤ) = 0` (`TopCat.isZero_singularHomology_of_forall_isZero_zmod`). For instance, if a compact
manifold has vanishing odd-degree homology over every prime field, its integral homology vanishes
in odd degrees and is free in even degrees. Finite generation is essential for the second
statement: a Moore space with first integral homology the divisible torsion group `ℚ / ℤ` has
vanishing first homology over every prime field.

## Main results

* `TopCat.isTorsionFree_singularHomology_of_forall_isZero_zmod`: integral homology is torsion-free
  in the degree just below a degree in which homology over every prime field vanishes.
* `TopCat.isZero_singularHomology_of_forall_isZero_zmod`: finitely generated integral homology
  vanishes in a degree in which homology over every prime field vanishes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (change of coefficients and the universal coefficient theorem) and Section 3.E
  (Bockstein homomorphisms).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u

namespace TopCat

/-- **Integral homology is torsion-free one degree below vanishing prime field homology.** If
`Hₙ₊₁(X; 𝔽_p) = 0` for every prime `p`, with `𝔽_p` taken as the integer module `ℤ/p`, then
`Hₙ(X; ℤ)` is torsion-free. -/
theorem isTorsionFree_singularHomology_of_forall_isZero_zmod (X : TopCat.{u}) (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod p)))).obj X)) :
    Module.IsTorsionFree ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) := by
  have := TauCeti.hasUniqueDiv_of_forall_prime fun p hp x y hxy ↦ by
    have : NeZero p := ⟨hp.ne_zero⟩
    exact X.injective_lsmul_singularHomology_of_isZero_zmod p n (h p hp)
      (by simpa only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul] using hxy)
  -- the integer module structure of homology is that of the underlying abelian group
  convert Module.isTorsionFree_int_iff_hasUniqueDiv.2 this
  exact Subsingleton.elim _ _

/-- **Finitely generated integral homology vanishes with prime field homology.** If `Hₙ(X; ℤ)`
is finitely generated and `Hₙ(X; 𝔽_p) = 0` for every prime `p`, with `𝔽_p` taken as the integer
module `ℤ/p`, then `Hₙ(X; ℤ) = 0`. -/
theorem isZero_singularHomology_of_forall_isZero_zmod (X : TopCat.{u}) (n : ℕ)
    [Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X)]
    (h : ∀ p : ℕ, p.Prime → IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod p)))).obj X)) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) := by
  -- Nakayama's lemma over `ℤ`: a finitely generated abelian group on which every prime acts
  -- surjectively is zero
  have := TauCeti.subsingleton_of_forall_prime_surjective fun p hp ↦ by
    have : NeZero p := ⟨hp.ne_zero⟩
    exact fun x ↦ (X.surjective_lsmul_singularHomology_of_isZero_zmod p n (h p hp) x).imp
      fun y hy ↦ by simpa only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul] using hy
  exact ModuleCat.isZero_of_subsingleton _

end TopCat
