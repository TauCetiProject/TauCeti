/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Basic
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Commutant

/-!
# The crossed system of a Clifford section

A normalized section of the canonical Clifford extension determines a crossed system on the
full equivariant endomorphism algebra. Its coefficient automorphisms are the existing commutant
automorphisms, and its factors are the units measured by the group extension. Thus
`(cliffordCrossedSystem A s hs).Algebra` is the finite-support crossed-product algebra with
coefficients in `CategoryTheory.End A` and indices in the actual inertia quotient.

This construction retains noncommutative coefficients and does not assume that the section's
automorphisms form an action. No simplicity, scalar-Schur, semisimplicity, characteristic, or
finite-group assumption is required.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory TauCeti TauCeti.CliffordExtension TauCeti.GroupExtension

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)

/-- A normalized Clifford section gives a crossed system on the actual commutant algebra.
Its crossed product uses the commutant itself; the opposite and inverse system needed for
right-commutant multiplicities is a separate construction. -/
noncomputable def cliffordCrossedSystem (s : (groupExtension A).Section) (hs : s 1 = 1) :
    CrossedSystem k (End A) (Quotient A) where
  action q := commutantAction (s q)
  factor q r := factorSetFun s (q, r)
  action_one := by simp [hs]
  factor_one_left q := s.factorSetFun_one_left hs q
  factor_one_right q := s.factorSetFun_one_right hs q
  action_mul q r f := by
    rw [commutantAction_section_mul]
    simp [mul_assoc]
  factor_assoc q r t := by
    have h := congrArg (fun d : (End A)ˣ => (d : End A)) (s.factorSetFun_mul q r t)
    simpa [← commutantAction_units] using h

/-- The coefficient automorphisms are the given section's commutant automorphisms. -/
@[simp]
theorem cliffordCrossedSystem_action (s : (groupExtension A).Section) (hs : s 1 = 1)
    (q : Quotient A) :
    (cliffordCrossedSystem A s hs).action q = commutantAction (s q) := (rfl)

/-- The unit factors are those of the actual canonical Clifford extension. -/
@[simp]
theorem cliffordCrossedSystem_factor (s : (groupExtension A).Section) (hs : s 1 = 1)
    (q r : Quotient A) :
    (cliffordCrossedSystem A s hs).factor q r = factorSetFun s (q, r) := (rfl)

end FDRep
