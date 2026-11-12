/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisClosure
public import TauCeti.NumberTheory.RamificationInertia.HilbertTheory.Compositum
import TauCeti.NumberTheory.RamificationInertia.Galois
import TauCeti.RingTheory.IsGaloisGroup.Dedekind

/-!
# Complete splitting in the Galois closure over a Dedekind base

Let `A` be a Dedekind domain with fraction field `K`, let `M / K` be finite Galois, and let `B`
be the integral closure of `A` in `M`. For a subgroup `H ≤ Gal(M/K)`, the normal closure of the
fixed field `M ^ H` inside `M` is `M ^ (normalCore H)`
(`IntermediateField.normalClosure_fixedField`). A maximal ideal `p` of `A` splits completely in
the integral closure of `A` in `M ^ H` exactly when it splits completely in the integral closure
of `A` in this normal closure. In particular,
when `M` is itself the Galois closure of `M ^ H`, the prime `p` splits completely in `M ^ H`
exactly when it splits completely in `M`.

Complete splitting is the count equation `(p.primesOver C).ncard = Module.finrank A C`. By the
decomposition-group criterion
`Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure`, it says that
every decomposition group above `p` lies in `H`. The decomposition groups above `p` are stable
under conjugation, so they all lie in `H` exactly when they all lie in its normal core
(`Ideal.forall_stabilizer_le_normalCore_iff`). No hypothesis on the residue fields is needed:
they need be neither finite nor perfect.

## Main results

* `Ideal.ncard_primesOver_normalCore_eq_finrank_iff_of_isIntegralClosure`: complete splitting in
  `M ^ H` and in its normal closure `M ^ (normalCore H)`.
* `Ideal.ncard_primesOver_eq_finrank_iff_of_normalClosure_eq_top_of_isIntegralClosure`: when `M`
  is the Galois closure of `M ^ H`, complete splitting in `M ^ H` and in `M`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, Exercise 4.
-/

public section

open IntermediateField MulAction
open scoped Pointwise

namespace Ideal

variable {A K M B : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  [Algebra A M] [IsScalarTower A K M] [CommRing B] [Algebra A B] [Algebra B M]
  [IsScalarTower A B M] [IsIntegralClosure B A M]
  [MulSemiringAction Gal(M/K) B] [SMulDistribClass Gal(M/K) B M]

variable (H : Subgroup Gal(M/K)) [Algebra A (fixedField H)]
  [IsScalarTower A K (fixedField H)]
  (C : Type*) [CommRing C] [Algebra A C] [Algebra C (fixedField H)]
  [IsScalarTower A C (fixedField H)] [IsIntegralClosure C A (fixedField H)]
  [Algebra C B] [Algebra C M] [IsScalarTower A C B]
  [IsScalarTower C (fixedField H) M] [IsScalarTower C B M]

/-- **Complete splitting in a field and in its normal closure over a Dedekind base.** Let `C`
and `C'` be the integral closures of `A` in `M ^ H` and in `M ^ (normalCore H)`, the normal
closure of `M ^ H` in `M` (`IntermediateField.normalClosure_fixedField`). A maximal ideal `p` of
`A` splits completely in `C'` exactly when it splits completely in `C`. No hypothesis on the
residue fields is needed. -/
theorem ncard_primesOver_normalCore_eq_finrank_iff_of_isIntegralClosure
    [Algebra A (fixedField H.normalCore)] [IsScalarTower A K (fixedField H.normalCore)]
    (C' : Type*) [CommRing C'] [Algebra A C'] [Algebra C' (fixedField H.normalCore)]
    [IsScalarTower A C' (fixedField H.normalCore)]
    [IsIntegralClosure C' A (fixedField H.normalCore)] [Algebra C' B] [Algebra C' M]
    [IsScalarTower A C' B] [IsScalarTower C' (fixedField H.normalCore) M]
    [IsScalarTower C' B M] (p : Ideal A) [p.IsMaximal] :
    (p.primesOver C').ncard = Module.finrank A C' ↔
      (p.primesOver C).ncard = Module.finrank A C := by
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := A) (K := K) (M := M) (B := B)
  rw [ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) H.normalCore C' p,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) H C p,
    forall_stabilizer_le_normalCore_iff]

/-- **Complete splitting in a field and in its Galois closure over a Dedekind base.** If `M` is
the Galois closure of `M ^ H`, and `C` is the integral closure of `A` in `M ^ H`, then a maximal
ideal `p` of `A` splits completely in `C` exactly when it splits completely in `B`. No hypothesis
on the residue fields is needed. -/
theorem ncard_primesOver_eq_finrank_iff_of_normalClosure_eq_top_of_isIntegralClosure
    (p : Ideal A) [p.IsMaximal] (hH : normalClosure K (fixedField H) M = ⊤) :
    (p.primesOver C).ncard = Module.finrank A C ↔
      (p.primesOver B).ncard = Module.finrank A B := by
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := A) (K := K) (M := M) (B := B)
  have : FaithfulSMul A B := (Module.isTorsionFree_iff_faithfulSMul).1 inferInstance
  have hcore : H.normalCore = ⊥ := by
    rw [← fixingSubgroup_fixedField H.normalCore, ← normalClosure_fixedField, hH,
      fixingSubgroup_top]
  rw [ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) H C p, ← forall_stabilizer_le_normalCore_iff, hcore,
    ← IsGaloisGroup.card_eq_finrank' Gal(M/K) A B,
    ncard_primesOver_eq_natCard_iff_forall_stabilizer_eq_bot Gal(M/K) p]
  simp only [le_bot_iff]

end Ideal
