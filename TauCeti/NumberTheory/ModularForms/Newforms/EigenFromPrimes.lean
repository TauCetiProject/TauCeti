/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.EigenFromPrimes
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# Building a good Hecke eigenform from the prime eigenvalues

`EigenformAwayFromLevel` bundles a cusp form with an eigenvalue at every index coprime to the
level. Eigen-ness at those indices is already determined by the primes
(`exists_smul_heckeTCompositeGamma0_of_forall_prime_of_coprime`), so a nonzero cusp form of
nebentypus `χ` that is an eigenvector of the Hecke-ring generator at every prime `p ∤ N` bundles
into one. That is the shape in which eigenforms are produced: a coefficient recurrence, a
diagonalisation or a spectral argument gives the eigenvector equation one prime at a time.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.ofForallPrime`: the good Hecke eigenform carried by a
  nonzero cusp form eigen at every prime away from the level.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2.EigenformAwayFromLevel

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **A nonzero cusp form of nebentypus `χ`, eigen at every good prime, is a good Hecke
eigenform.** Its eigenvalue at a good index is the scalar by which the Hecke ring acts there,
supplied by `exists_smul_heckeTCompositeGamma0_of_forall_prime_of_coprime`. -/
noncomputable def ofForallPrime {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hχ : f ∈ cuspFormCharSpace k χ) (hf : f ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨f, hχ⟩ = c • ⟨f, hχ⟩) :
    EigenformAwayFromLevel N k where
  toCuspForm := f
  χ := χ
  mem_charSpace := hχ
  eigenvalue n hn :=
    (exists_smul_heckeTCompositeGamma0_of_forall_prime_of_coprime h n hn).choose
  isEigen n hn :=
    (exists_smul_heckeTCompositeGamma0_of_forall_prime_of_coprime h n hn).choose_spec
  ne_zero := hf

end HeckeRing.GL2.EigenformAwayFromLevel

end
