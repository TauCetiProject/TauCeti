/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MatlisDuality.Residue
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.LocalRing.Length
import TauCeti.Algebra.Module.Injective.TrivSqZeroExt
import TauCeti.RingTheory.MvPolynomial.FirstJet
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# The injective envelope of the residue field at a doubled point

The quotient of a polynomial ring in `n` variables over `k` by the square of its variable ideal
is the trivial square-zero extension of `k` by `kⁿ`. The `k`-linear dual of the regular module
is the injective envelope of the residue field. The envelope and the regular module have length
`n + 1` and are nonisomorphic if `n ≥ 2`. In particular, for `k[X,Y]/(X,Y)²` both have length
three.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation Theory of Artin Algebras*,
  Corollary II.3.2(a) and Proposition II.4.6.
-/

public section

open IsLocalRing MvPolynomial

namespace TauCeti

variable (k : Type*) (σ : Type*) [Field k] [Fintype σ]

local notation "B" => MvPolynomial σ k ⧸ (idealOfVars σ k ^ 2)

/-- The regular dual of the polynomial algebra modulo the square of the variable ideal is an
injective envelope of the residue field. Both it and the regular module have length equal to the
number of variables plus one. With at least two variables these modules are nonisomorphic. -/
theorem exists_isInjectiveEnvelope_idealOfVars_sq :
    ∃ ι : (B ⧸ Ring.jacobson B) →ₗ[B] MatlisDual k k B,
      IsInjectiveEnvelope ι ∧
      Module.length B B = Fintype.card σ + 1 ∧
      Module.length B (MatlisDual k k B) = Fintype.card σ + 1 ∧
      (1 < Fintype.card σ → ¬ Nonempty (B ≃ₗ[B] MatlisDual k k B)) := by
  classical
  have hker : RingHom.ker (jetAlgebra (0 : σ → k)) = idealOfVars σ k ^ 2 := by
    rw [ker_jetAlgebra, eval_zero, ker_constantCoeff]
  let e : B ≃ₐ[k] TrivSqZeroExt k (σ → k) :=
    (Ideal.quotientEquivAlgOfEq k hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (jetAlgebra_surjective (0 : σ → k)))
  have : IsLocalRing B := e.symm.toRingEquiv.isLocalRing
  have : Module.Finite k B := Module.Finite.equiv e.toLinearEquiv.symm
  have : Module.Finite k (MatlisDual k k B) :=
    Module.Finite.equiv (MatlisDual.equivLinearMap k k B).symm
  let ε : B →ₐ[k] k := (TrivSqZeroExt.fstHom k k (σ → k)).comp e.toAlgHom
  have hε : Function.Surjective ε := fun a ↦ ⟨algebraMap k B a, by simp⟩
  have hmax : RingHom.ker ε = maximalIdeal B := IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε
  have hJ : RingHom.ker ε = Ring.jacobson B := hmax.trans (ringJacobson_eq_maximalIdeal B).symm
  let residueEquiv : ResidueField B ≃ₐ[k] k :=
    (Ideal.quotientEquivAlgOfEq k hmax.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hε)
  have hres : Module.length (ResidueField k) (ResidueField B) = 1 := by
    rw [← Module.length_eq_of_surjective (M := ResidueField B) (residue_surjective (R := k)),
      residueEquiv.toLinearEquiv.length_eq, Module.length_eq_finrank, Module.finrank_self,
      Nat.cast_one]
  have hι := ε.isInjectiveEnvelope_quotientKerToMatlisDual
  have hdim : Module.finrank k B = Fintype.card σ + 1 := by
    rw [e.toLinearEquiv.finrank_eq, TrivSqZeroExt.finrank_eq_finrank_add_one]
    simp
  rw [← hJ]
  refine ⟨ε.quotientKerToMatlisDual, hι, ?_, ?_, ?_⟩
  · have hlen := IsLocalRing.length_restrictScalars k B B
    rw [hres, mul_one, Module.length_eq_finrank, hdim, Nat.cast_add, Nat.cast_one] at hlen
    exact hlen.symm
  · have hlen := IsLocalRing.length_restrictScalars k B (MatlisDual k k B)
    rw [hres, mul_one, Module.length_eq_finrank, (MatlisDual.equivLinearMap k k B).finrank_eq,
      Subspace.dual_finrank_eq, hdim, Nat.cast_add, Nat.cast_one] at hlen
    exact hlen.symm
  · rintro hcard ⟨f⟩
    have : Module.Injective B B :=
      ((Module.Baer.of_injective hι.moduleInjective).of_equiv f.symm).injective
    have hinj := Module.Injective.of_ringEquiv e.toRingEquiv e.toRingEquiv.toSemilinearEquiv
    exact TrivSqZeroExt.not_moduleInjective_self_of_one_lt_rank (k := k) (V := σ → k)
      (Module.one_lt_rank_of_one_lt_finrank (by simpa using hcard)) hinj

end TauCeti
