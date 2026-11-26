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

An isomorphism of `R`-algebras `S ≃ₐ[R] T` matches the primes of `S` and of `T` above an ideal
of `R`, so the two have equally many: `Ideal.ncard_primesOver_congr`.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- A height one prime of `B` taken from the subtype of those lying over `v` lies over `v`. -/
instance liesOver_val {v : HeightOneSpectrum R}
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    w.val.asIdeal.LiesOver v.asIdeal :=
  w.property

variable (B) [FaithfulSMul R B]

/-- The nonzero prime ideals of `B` lying over a nonzero prime `v` of `R` are precisely
`Ideal.primesOver v.asIdeal B`. Injectivity of the algebra map ensures that an ideal lying
above `v` is nonzero; neither ring needs to be a Dedekind domain. -/
def liesOverEquivPrimesOver (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ≃ v.asIdeal.primesOver B where
  toFun w := ⟨w.val.asIdeal, w.val.isPrime, w.property⟩
  invFun Q := ⟨⟨Q.val, Q.property.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.val⟩,
      Q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem liesOverEquivPrimesOver_apply (v : HeightOneSpectrum R)
    (w : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
    (liesOverEquivPrimesOver B v w : Ideal B) = w.val.asIdeal :=
  (rfl)

@[simp]
theorem liesOverEquivPrimesOver_symm_apply (v : HeightOneSpectrum R)
    (Q : v.asIdeal.primesOver B) :
    ((liesOverEquivPrimesOver B v).symm Q).val.asIdeal = Q :=
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
    (Σ v : S, v.val.asIdeal.primesOver B) ≃ ↥(HeightOneSpectrum.primesAbove R B S) :=
  (Equiv.sigmaCongrRight fun v : S ↦
    (HeightOneSpectrum.liesOverEquivPrimesOver B v.val).symm.trans
      (Equiv.subtypeEquivRight fun _ ↦ HeightOneSpectrum.under_eq_iff_liesOver.symm)).trans
    (Equiv.sigmaSubtypeFiberEquivSubtype (HeightOneSpectrum.under R)
      (fun w ↦ HeightOneSpectrum.mem_primesAbove_iff R B S w))

/-- The sigma-to-primes-above equivalence preserves the underlying top ideal. -/
@[simp]
theorem sigmaPrimesOverEquivPrimesAbove_apply_asIdeal (S : Set (HeightOneSpectrum R))
    (p : Σ v : S, v.val.asIdeal.primesOver B) :
    (sigmaPrimesOverEquivPrimesAbove R B S p).val.asIdeal = p.2.val :=
  (rfl)

/-- The inverse indexes a prime above the set by its contraction. -/
@[simp]
theorem sigmaPrimesOverEquivPrimesAbove_symm_apply_fst (S : Set (HeightOneSpectrum R))
    (w : ↥(HeightOneSpectrum.primesAbove R B S)) :
    ((sigmaPrimesOverEquivPrimesAbove R B S).symm w).1.val = w.val.under R :=
  (rfl)

/-- The inverse preserves the underlying top ideal. -/
@[simp]
theorem sigmaPrimesOverEquivPrimesAbove_symm_apply_snd (S : Set (HeightOneSpectrum R))
    (w : ↥(HeightOneSpectrum.primesAbove R B S)) :
    ((sigmaPrimesOverEquivPrimesAbove R B S).symm w).2.val = w.val.asIdeal :=
  (rfl)

end TauCeti

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- An isomorphism of `R`-algebras `S ≃ₐ[R] T` matches the primes above an ideal `p` of `R`: there
are as many primes of `T` above `p` as there are of `S`. Pulling back along the isomorphism is
the bijection. -/
theorem ncard_primesOver_congr (e : S ≃ₐ[R] T) (p : Ideal R) :
    (p.primesOver T).ncard = (p.primesOver S).ncard := by
  refine Set.ncard_congr (fun Q _ ↦ Q.comap e) (fun Q hQ ↦ ?_) (fun Q Q' _ _ h ↦ ?_)
    fun Q hQ ↦ ⟨Q.comap e.symm, ?_, ?_⟩
  · have := hQ.1
    have := hQ.2
    exact ⟨inferInstance, inferInstance⟩
  · exact comap_injective_of_surjective e e.surjective h
  · have := hQ.1
    have := hQ.2
    exact ⟨inferInstance, inferInstance⟩
  · ext x
    simp

end Ideal
