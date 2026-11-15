/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Gauge
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Gauge

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

For any two normalized sections, `cliffordCrossedProductEquiv` compares the resulting algebras
by the actual section difference. It fixes the commutant and sends each basis element to the
corresponding section-difference multiple, giving independence of the chosen section up to
algebra isomorphism.

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
  factor_one_left q := s.factorSetFun_one_left hs q
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

/-- The section difference conjugates the coefficient automorphisms of the two
Clifford crossed systems. -/
theorem cliffordCrossedSystem_action_sectionDiff
    (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1)
    (q : Quotient A) (f : End A) :
    (cliffordCrossedSystem A t ht).action q f =
      (↑(sectionDiff t s q) : End A) * (cliffordCrossedSystem A s hs).action q f *
        (↑(sectionDiff t s q)⁻¹ : End A) := by
  simpa only [cliffordCrossedSystem_action, GroupExtension.Section.gauge_sectionDiff] using
    commutantAction_gauge A s (sectionDiff t s) q f

/-- The factors of two Clifford crossed systems are related by the section-difference
gauge formula, using the coefficient automorphism of the original section. -/
theorem cliffordCrossedSystem_factor_sectionDiff
    (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1)
    (q r : Quotient A) :
    ((cliffordCrossedSystem A t ht).factor q r : End A) =
      (↑(sectionDiff t s q) : End A) *
        (cliffordCrossedSystem A s hs).action q ↑(sectionDiff t s r) *
        (cliffordCrossedSystem A s hs).factor q r *
        (↑(sectionDiff t s (q * r))⁻¹ : End A) := by
  have h := congrArg (fun d : (End A)ˣ => (d : End A))
    (factorSetFun_clifford_gauge A s (sectionDiff t s) q r)
  simpa using h

/-- The crossed-product algebras of two normalized Clifford sections are isomorphic.
The map from the `t`-algebra to the `s`-algebra fixes the commutant and multiplies the
basis element at `q` by the actual section difference `t(q)s(q)⁻¹` in the kernel. -/
noncomputable def cliffordCrossedProductEquiv
    (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1) :
    CrossedSystem.Algebra (cliffordCrossedSystem A t ht) ≃ₐ[k]
      CrossedSystem.Algebra (cliffordCrossedSystem A s hs) :=
  CrossedSystem.Algebra.gaugeEquiv _ _ (sectionDiff t s)
    (t.sectionDiff_one s ht hs)
    (cliffordCrossedSystem_action_sectionDiff A s t hs ht)
    (cliffordCrossedSystem_factor_sectionDiff A s t hs ht)

/-- The section comparison fixes every coefficient in the commutant. -/
@[simp]
theorem cliffordCrossedProductEquiv_inc
    (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1) (f : End A) :
    cliffordCrossedProductEquiv A s t hs ht
      (CrossedSystem.Algebra.inc (cliffordCrossedSystem A t ht) f) =
        CrossedSystem.Algebra.inc (cliffordCrossedSystem A s hs) f := by
  simp [cliffordCrossedProductEquiv]

/-- The section comparison sends `[q]` to `sectionDiff t s q [q]`. -/
@[simp]
theorem cliffordCrossedProductEquiv_basis
    (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1) (q : Quotient A) :
    cliffordCrossedProductEquiv A s t hs ht
      (CrossedSystem.Algebra.basis (cliffordCrossedSystem A t ht) q) =
        (↑(sectionDiff t s q) : End A) •
          CrossedSystem.Algebra.basis (cliffordCrossedSystem A s hs) q := by
  simp [cliffordCrossedProductEquiv]

/-- The inverse section comparison fixes every coefficient in the commutant. -/
@[simp]
theorem cliffordCrossedProductEquiv_symm_inc
    (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1) (f : End A) :
    (cliffordCrossedProductEquiv A s t hs ht).symm
      (CrossedSystem.Algebra.inc (cliffordCrossedSystem A s hs) f) =
        CrossedSystem.Algebra.inc (cliffordCrossedSystem A t ht) f := by
  simp [cliffordCrossedProductEquiv]

/-- The inverse section comparison uses the inverse of the section difference. -/
@[simp]
theorem cliffordCrossedProductEquiv_symm_basis
    (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1) (q : Quotient A) :
    (cliffordCrossedProductEquiv A s t hs ht).symm
      (CrossedSystem.Algebra.basis (cliffordCrossedSystem A s hs) q) =
        (↑(sectionDiff t s q)⁻¹ : End A) •
          CrossedSystem.Algebra.basis (cliffordCrossedSystem A t ht) q := by
  simp [cliffordCrossedProductEquiv]

end FDRep
