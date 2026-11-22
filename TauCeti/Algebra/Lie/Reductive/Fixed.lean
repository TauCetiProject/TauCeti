/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Reductive.Basic
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
public import Mathlib.Algebra.Lie.Prod
import Mathlib.LinearAlgebra.Projection

/-!
# Central and derived parts of fixed reductive Lie algebras

Whenever a Lie algebra splits as the direct sum of its centre and derived ideal, every eigenvector
of an automorphism decomposes uniquely into a central eigenvector and a derived-ideal eigenvector
with the same eigenvalue (`LieEquiv.existsUnique_center_add_derivedSeries_of_apply_eq_smul`).
Specialising to eigenvalue `1` gives the unique decomposition of a fixed vector into a fixed
central vector and a fixed vector of the ambient derived ideal, and addition gives a Lie algebra
equivalence from the product of these two fixed subalgebras to the full fixed algebra
(`LieEquiv.fixedCenterDerivedEquiv`).

This keeps the fixed central summand separate from a presentation of the remaining fixed
algebra. The latter is the fixed part of the **ambient** derived ideal, not by definition the
derived ideal of the fixed algebra. No finite-order hypothesis on the automorphism is needed.

The construction uses Mathlib's `Submodule.prodEquivOfIsCompl` for the unique linear
decomposition.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §19.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Addition identifies the fixed algebra with the product of its fixed central part and the
fixed part of the ambient derived ideal, given a centre–derived complement. The factors are
subalgebras of the ambient algebra, so their elements retain their original central and derived
membership proofs. -/
noncomputable def fixedCenterDerivedEquiv (e : L ≃ₗ⁅R⁆ L)
    (hc : IsCompl (center R L) (derivedSeries R L 1)) :
    (↥(e.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ×
      ↥(e.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra)) ≃ₗ⁅R⁆
        e.toLieHom.fixedSubalgebra :=
  LieEquiv.ofBijective
    { toFun := fun p => ⟨(p.1 : L) + p.2, by
        simp only [LieHom.mem_fixedSubalgebra, map_add,
          LieHom.mem_fixedSubalgebra.mp p.1.property.1,
          LieHom.mem_fixedSubalgebra.mp p.2.property.1]⟩
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_add]
      map_lie' := by
        intro p q
        ext
        have hz (z : center R L) (y : L) : ⁅y, (z : L)⁆ = 0 :=
          (LieModule.mem_maxTrivSubmodule R L L z).mp z.property y
        have hcross : ⁅(p.1 : L), (q.2 : L)⁆ = 0 := by
          rw [← lie_skew, hz ⟨(p.1 : L), p.1.property.2⟩, neg_zero]
        simp [lie_add, add_lie, hz ⟨(q.1 : L), q.1.property.2⟩, hcross] }
    (by
      constructor
      · intro p q hpq
        have hc' := LieSubmodule.isCompl_toSubmodule.mpr hc
        have h : ((⟨(p.1 : L), p.1.property.2⟩ : center R L),
            (⟨(p.2 : L), p.2.property.2⟩ : derivedSeries R L 1)) =
            (⟨(q.1 : L), q.1.property.2⟩, ⟨(q.2 : L), q.2.property.2⟩) := by
          apply (Submodule.prodEquivOfIsCompl (center R L).toSubmodule
            (derivedSeries R L 1).toSubmodule hc').injective
          simp only [Submodule.coe_prodEquivOfIsCompl']
          exact congrArg Subtype.val hpq
        apply Prod.ext <;> apply Subtype.ext
        · exact congrArg (fun r => (r.1 : L)) h
        · exact congrArg (fun r => (r.2 : L)) h
      · intro x
        obtain ⟨p, hp, _⟩ := e.existsUnique_center_add_derivedSeries_of_apply_eq_smul
          hc (c := (1 : R))
          (by simpa only [one_smul, LieEquiv.coe_toLieHom] using
            LieHom.mem_fixedSubalgebra.mp x.property)
        simp only [one_smul] at hp
        exact ⟨(⟨p.1, LieHom.mem_fixedSubalgebra.mpr hp.1, p.1.property⟩,
          ⟨p.2, LieHom.mem_fixedSubalgebra.mpr hp.2.1, p.2.property⟩),
          Subtype.ext hp.2.2⟩)

/-- The fixed-part decomposition is addition in the ambient Lie algebra. -/
@[simp]
theorem fixedCenterDerivedEquiv_apply (e : L ≃ₗ⁅R⁆ L)
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (p : ↥(e.toLieHom.fixedSubalgebra ⊓ (center R L).toLieSubalgebra) ×
      ↥(e.toLieHom.fixedSubalgebra ⊓ (derivedSeries R L 1).toLieSubalgebra)) :
    (e.fixedCenterDerivedEquiv hc p : L) = (p.1 : L) + p.2 :=
  (rfl)

/-- The inverse decomposition recovers a fixed vector by adding its two components. -/
@[simp]
theorem fixedCenterDerivedEquiv_symm_add (e : L ≃ₗ⁅R⁆ L)
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (x : e.toLieHom.fixedSubalgebra) :
    (((e.fixedCenterDerivedEquiv hc).symm x).1 : L) +
      ((e.fixedCenterDerivedEquiv hc).symm x).2 = x := by
  rw [← fixedCenterDerivedEquiv_apply e hc, LieEquiv.apply_symm_apply]

end LieEquiv
