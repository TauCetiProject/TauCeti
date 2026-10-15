/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# Nonzero prime ideals lying over a prime

For an injective algebra map of commutative rings `R → B`, the nonzero prime ideals of `B`
lying over a nonzero prime `v` of `R` correspond to `Ideal.primesOver v.asIdeal B`.
The correspondence is `IsDedekindDomain.HeightOneSpectrum.liesOverEquivPrimesOver`.
It uses Mathlib's type of nonzero prime ideals, `IsDedekindDomain.HeightOneSpectrum`,
without requiring either ring to be Dedekind or the extension to be integral.
For an integral extension of domains, `TauCeti.sigmaPrimesOverEquivPrimesAbove` assembles these
fibres into the canonical carrier of primes above a set; its forward map keeps the top prime,
and its inverse indexes that prime by its contraction.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- A height one prime of `B` taken from the subtype of those lying over `v` lies over `v`. -/
instance liesOver_val {v : HeightOneSpectrum R}
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    w.1.asIdeal.LiesOver v.asIdeal :=
  w.2

variable (B) [FaithfulSMul R B]

/-- The nonzero prime ideals of `B` lying over a nonzero prime `v` of `R` are precisely
`Ideal.primesOver v.asIdeal B`. Injectivity of the algebra map ensures that an ideal lying
above `v` is nonzero; neither ring needs to be a Dedekind domain. -/
def liesOverEquivPrimesOver (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ≃ v.asIdeal.primesOver B where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun Q := ⟨⟨Q.1, Q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.1⟩, Q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem liesOverEquivPrimesOver_apply (v : HeightOneSpectrum R)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    (liesOverEquivPrimesOver B v w : Ideal B) = w.1.asIdeal :=
  (rfl)

@[simp]
theorem liesOverEquivPrimesOver_symm_apply (v : HeightOneSpectrum R)
    (Q : v.asIdeal.primesOver B) :
    ((liesOverEquivPrimesOver B v).symm Q).1.asIdeal = Q :=
  (rfl)

end IsDedekindDomain.HeightOneSpectrum

end

public section

namespace TauCeti

open IsDedekindDomain

variable (R B : Type*) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]

/-- Primes above a set correspond to the sigma family of primes over each member of that set.
The forward map keeps the top prime; the inverse indexes it by its contraction. -/
def sigmaPrimesOverEquivPrimesAbove (S : Set (HeightOneSpectrum R)) :
    (Σ v : S, v.1.asIdeal.primesOver B) ≃ ↥(HeightOneSpectrum.primesAbove R B S) :=
  (Equiv.sigmaCongrRight fun v : S ↦
    (HeightOneSpectrum.liesOverEquivPrimesOver B v.1).symm.trans
      (Equiv.subtypeEquivRight fun _ ↦
        ⟨fun h ↦ HeightOneSpectrum.asIdeal_injective h.over.symm,
          fun h ↦ ⟨congrArg HeightOneSpectrum.asIdeal h.symm⟩⟩)).trans
    (Equiv.sigmaSubtypeFiberEquivSubtype (HeightOneSpectrum.under R)
      (fun w ↦ HeightOneSpectrum.mem_primesAbove_iff R B S w))

/-- The sigma-to-primes-above equivalence preserves the underlying top ideal. -/
@[simp]
theorem sigmaPrimesOverEquivPrimesAbove_apply_asIdeal (S : Set (HeightOneSpectrum R))
    (p : Σ v : S, v.1.asIdeal.primesOver B) :
    (sigmaPrimesOverEquivPrimesAbove R B S p).1.asIdeal = p.2.1 :=
  (rfl)

/-- The inverse indexes a prime above the set by its contraction. -/
@[simp]
theorem sigmaPrimesOverEquivPrimesAbove_symm_apply_fst (S : Set (HeightOneSpectrum R))
    (w : ↥(HeightOneSpectrum.primesAbove R B S)) :
    ((sigmaPrimesOverEquivPrimesAbove R B S).symm w).1.1 = w.1.under R :=
  (rfl)

/-- The inverse preserves the underlying top ideal. -/
@[simp]
theorem sigmaPrimesOverEquivPrimesAbove_symm_apply_snd (S : Set (HeightOneSpectrum R))
    (w : ↥(HeightOneSpectrum.primesAbove R B S)) :
    ((sigmaPrimesOverEquivPrimesAbove R B S).symm w).2.1 = w.1.asIdeal :=
  (rfl)

end TauCeti
