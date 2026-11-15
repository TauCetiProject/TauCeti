/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Basic
public import TauCeti.NumberTheory.RamificationInertia.HilbertTheory.Unramified
public import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.RamificationInertia.Splitting
import TauCeti.RingTheory.IsGaloisGroup.Dedekind

/-!
# Splitting and unramified primes in composita over a Dedekind base

Let `A` be a Dedekind domain with fraction field `K`, let `M / K` be finite Galois, and let `B`
be the integral closure of `A` in `M`. For a subgroup `H ≤ Gal(M/K)`, let `C` be the integral
closure of `A` in the fixed field `M ^ H`. A maximal ideal `p` of `A` splits completely in `C`
exactly when every decomposition group above `p` is contained in `H`, and is unramified in `C`
exactly when every inertia group above `p` is contained in `H`.

This criterion includes imperfect residue fields. It specializes the invariant-ring criterion
`TauCeti.RamificationInertia.isUnramifiedIn_iff_forall_inertia_le`, using the integral-closure
Galois actions and the finiteness and flatness supplied by a Dedekind base.

The fixed field of `H₁ ⊓ H₂` is the compositum of the fixed fields of `H₁` and `H₂`.
The subgroup criteria therefore prove that a maximal ideal splits completely, or is unramified,
in that compositum exactly when it has the corresponding property in both constituents. No
finiteness or separability assumption on the residue fields is needed.

## Main results

* `Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure`: the
  decomposition-group criterion for integral closures over a Dedekind base.
* `Ideal.isUnramifiedIn_iff_forall_inertia_le_of_isIntegralClosure`: the corresponding inertia
  criterion.
* `Ideal.ncard_primesOver_inf_eq_finrank_iff_of_isIntegralClosure` and
  `Ideal.isUnramifiedIn_inf_iff_of_isIntegralClosure`: complete splitting and unramifiedness in
  the compositum of two fixed fields are detected in each constituent.

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

/-- A maximal ideal of a Dedekind base splits completely in the integral closure inside `M ^ H`
exactly when every decomposition group above it is contained in `H`. No separability hypothesis
on residue fields is needed. -/
theorem ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure
    (p : Ideal A) [p.IsMaximal] :
    (p.primesOver C).ncard = Module.finrank A C ↔
      ∀ Q ∈ p.primesOver B, stabilizer Gal(M/K) Q ≤ H := by
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := A) (K := K) (M := M) (B := B)
  obtain ⟨_, _⟩ := TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul
    (A := A) (B := B) H C
  obtain ⟨_, _, _⟩ := TauCeti.IsIntegralClosure.isDedekindDomain_and_finite_and_flat_fixedField
    (A := A) (K := K) (M := M) H C
  have : Module.Finite C B := Module.Finite.right A C B
  rw [ncard_primesOver_eq_finrank_iff_forall_ramificationIdx_eq_one_and_inertiaDeg_eq_one]
  simp_rw [← mul_eq_one, ← Subgroup.relIndex_eq_one]
  refine ⟨fun h Q hQ ↦ ?_, fun h q hq ↦ ?_⟩
  · have : Q.IsPrime := hQ.1
    have : Q.LiesOver p := hQ.2
    have : Q.IsMaximal := IsMaximal.of_liesOver_isMaximal Q p
    rw [← Ideal.ramificationIdx_mul_inertiaDeg_under_eq_relIndex
      (A := A) (B := B) (G := Gal(M/K)) Q H C]
    exact h (Q.under C) ⟨inferInstance, ⟨by rw [under_under]; exact hQ.2.over⟩⟩
  · have : q.IsPrime := hq.1
    have : q.LiesOver p := hq.2
    obtain ⟨⟨Q, hQprime, hQover⟩⟩ := q.nonempty_primesOver (S := B)
    have : Q.IsPrime := hQprime
    have : Q.LiesOver q := hQover
    have : Q.LiesOver p := LiesOver.trans Q q p
    have : Q.IsMaximal := IsMaximal.of_liesOver_isMaximal Q p
    rw [← (over_def Q q).symm, Ideal.ramificationIdx_mul_inertiaDeg_under_eq_relIndex
      (A := A) (B := B) (G := Gal(M/K)) Q H C]
    exact h Q ⟨inferInstance, inferInstance⟩

/-- A maximal ideal of a Dedekind base is unramified in the integral closure inside `M ^ H`
exactly when every inertia group above it is contained in `H`. This statement does not assume
that any residue field is finite or perfect. -/
theorem isUnramifiedIn_iff_forall_inertia_le_of_isIntegralClosure
    (p : Ideal A) [p.IsMaximal] :
    Algebra.IsUnramifiedIn C p ↔
      ∀ Q ∈ p.primesOver B, Q.inertia Gal(M/K) ≤ H := by
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := A) (K := K) (M := M) (B := B)
  obtain ⟨_, _⟩ := TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul
    (A := A) (B := B) H C
  obtain ⟨_, _, _⟩ := TauCeti.IsIntegralClosure.isDedekindDomain_and_finite_and_flat_fixedField
    (A := A) (K := K) (M := M) H C
  exact TauCeti.RamificationInertia.isUnramifiedIn_iff_forall_inertia_le A C H p

section Compositum

variable (H₁ H₂ : Subgroup Gal(M/K))

variable (C₁ : Type*) [CommRing C₁] [Algebra A C₁] [Algebra C₁ (fixedField H₁)]
  [IsScalarTower A C₁ (fixedField H₁)] [IsIntegralClosure C₁ A (fixedField H₁)]
  [Algebra C₁ B] [Algebra C₁ M] [IsScalarTower A C₁ B]
  [IsScalarTower C₁ (fixedField H₁) M] [IsScalarTower C₁ B M]

variable (C₂ : Type*) [CommRing C₂] [Algebra A C₂] [Algebra C₂ (fixedField H₂)]
  [IsScalarTower A C₂ (fixedField H₂)] [IsIntegralClosure C₂ A (fixedField H₂)]
  [Algebra C₂ B] [Algebra C₂ M] [IsScalarTower A C₂ B]
  [IsScalarTower C₂ (fixedField H₂) M] [IsScalarTower C₂ B M]

variable (C₁₂ : Type*) [CommRing C₁₂] [Algebra A C₁₂]
  [Algebra C₁₂ (fixedField (H₁ ⊓ H₂))]
  [IsScalarTower A C₁₂ (fixedField (H₁ ⊓ H₂))]
  [IsIntegralClosure C₁₂ A (fixedField (H₁ ⊓ H₂))]
  [Algebra C₁₂ B] [Algebra C₁₂ M] [IsScalarTower A C₁₂ B]
  [IsScalarTower C₁₂ (fixedField (H₁ ⊓ H₂)) M] [IsScalarTower C₁₂ B M]

include K M B H₁ H₂ in
/-- **Complete splitting in a compositum over a Dedekind base.** With `C₁`, `C₂`, and `C₁₂`
as in `Ideal.isUnramifiedIn_inf_iff_of_isIntegralClosure`, a maximal ideal has the maximum
possible number of primes in `C₁₂` exactly when it has the maximum possible number in both
`C₁` and `C₂`. -/
theorem ncard_primesOver_inf_eq_finrank_iff_of_isIntegralClosure
    (p : Ideal A) [p.IsMaximal] :
    (p.primesOver C₁₂).ncard = Module.finrank A C₁₂ ↔
      (p.primesOver C₁).ncard = Module.finrank A C₁ ∧
        (p.primesOver C₂).ncard = Module.finrank A C₂ := by
  rw [ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) (H₁ ⊓ H₂) C₁₂ p,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) H₁ C₁ p,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) H₂ C₂ p]
  simp only [le_inf_iff, ← forall_and]

include K M B H₁ H₂ in
/-- **Unramifiedness in a compositum over a Dedekind base.** Let `C₁`, `C₂`, and `C₁₂` be
the integral closures of `A` in `M ^ H₁`, `M ^ H₂`, and `M ^ (H₁ ⊓ H₂)`, respectively.
Then a maximal ideal of `A` is unramified in `C₁₂` exactly when it is unramified in both
`C₁` and `C₂`. By `Subgroup.fixedField_inf`, the fraction field of `C₁₂` is the compositum
of the fraction fields of `C₁` and `C₂`. -/
theorem isUnramifiedIn_inf_iff_of_isIntegralClosure (p : Ideal A) [p.IsMaximal] :
    Algebra.IsUnramifiedIn C₁₂ p ↔
      Algebra.IsUnramifiedIn C₁ p ∧ Algebra.IsUnramifiedIn C₂ p := by
  rw [isUnramifiedIn_iff_forall_inertia_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) (H₁ ⊓ H₂) C₁₂ p,
    isUnramifiedIn_iff_forall_inertia_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) H₁ C₁ p,
    isUnramifiedIn_iff_forall_inertia_le_of_isIntegralClosure
      (A := A) (K := K) (M := M) (B := B) H₂ C₂ p]
  simp only [le_inf_iff, ← forall_and]

end Compositum

end Ideal
