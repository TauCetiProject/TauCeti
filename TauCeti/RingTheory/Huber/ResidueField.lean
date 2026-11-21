/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Infinite residue fields of complete Tate rings

Every nonzero ring admitting a homomorphism from a complete Hausdorff Tate ring is infinite.
In particular, every proper quotient and every residue field of such a Tate ring is infinite.
No continuity is required of the homomorphism, and no topology is imposed on the target.

The powers of a pseudouniformizer remain distinct under every such map: the difference of
two distinct powers is a unit, by convergence of the geometric series. This supplies the
infinite residue fields used when choosing primitive elements in finite étale fibres.

## References

* D. Hansen and K. S. Kedlaya, *Sheafiness criteria for Huber rings*, §4, proof of Corollary 4.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.38 (the geometric series).
-/

public section

namespace TauCeti.Huber

section Pseudouniformizer

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [NonarchimedeanAddGroup A] [CompleteSpace A] [T2Space A]
  {ϖ : A}

/-- Distinct powers of a pseudouniformizer have unit difference in a complete Hausdorff
nonarchimedean ring. -/
theorem IsPseudoUniformizer.isUnit_pow_sub_pow (hϖ : IsPseudoUniformizer ϖ)
    {m n : ℕ} (hmn : m ≠ n) : IsUnit (ϖ ^ m - ϖ ^ n) := by
  have hlt (i j : ℕ) (hij : i < j) : IsUnit (ϖ ^ i - ϖ ^ j) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have hu := (hϖ.isUnit.pow i).mul
      (hϖ.isTopologicallyNilpotent.pow (Nat.succ_ne_zero k)).isUnit_one_sub
    simpa only [pow_add, pow_succ, mul_sub, mul_one, mul_assoc] using hu
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · simpa only [neg_sub] using (hlt n m h).neg

/-- The images of the powers of a pseudouniformizer are distinct in every nonzero target
ring, even when the ring homomorphism is not continuous. -/
theorem IsPseudoUniformizer.injective_map_pow (hϖ : IsPseudoUniformizer ϖ)
    {B : Type*} [Ring B] [Nontrivial B] (f : A →+* B) :
    Function.Injective (fun n : ℕ ↦ f (ϖ ^ n)) := by
  intro m n hmn
  by_contra h
  have hu := (hϖ.isUnit_pow_sub_pow h).map f
  exact hu.ne_zero (by simpa only [map_sub, sub_eq_zero] using hmn)

end Pseudouniformizer

end TauCeti.Huber

section TateRing

open TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [IsTateRing A] [CompleteSpace A] [T2Space A]

/-- Every nonzero ring admitting a homomorphism from a complete Hausdorff Tate ring is
infinite. The homomorphism need not be continuous. -/
theorem RingHom.infinite_of_isTateRing {B : Type*} [Ring B] [Nontrivial B] (f : A →+* B) :
    Infinite B := by
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  exact Infinite.of_injective _ (hϖ.injective_map_pow f)

/-- Every proper quotient of a complete Hausdorff Tate ring is infinite, without any
closedness assumption on the ideal. -/
theorem Ideal.infinite_quotient_of_isTateRing (I : Ideal A) (hI : I ≠ ⊤) : Infinite (A ⧸ I) := by
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  exact (Ideal.Quotient.mk I).infinite_of_isTateRing

/-- The residue field at every prime of a complete Hausdorff Tate ring is infinite.
This is the algebraic residue field, not the residue field of a valuation ring. -/
theorem Ideal.infinite_residueField_of_isTateRing (I : Ideal A) [I.IsPrime] :
    Infinite I.ResidueField :=
  (algebraMap A I.ResidueField).infinite_of_isTateRing

end TateRing
