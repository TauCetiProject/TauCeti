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

An automorphism of a finite-dimensional reductive Lie algebra in characteristic zero preserves
its centre and derived ideal. Consequently a fixed vector has a unique decomposition into a
fixed central vector and a fixed vector of the ambient derived ideal. Addition gives a Lie
algebra equivalence from the product of these two fixed subalgebras to the full fixed algebra.

This keeps the fixed central summand separate from a presentation of the remaining fixed
algebra. The latter is the fixed part of the **ambient** derived ideal, not by definition the
derived ideal of the fixed algebra. No finite-order hypothesis on the automorphism is needed.

The construction uses `TauCeti.isCompl_center_derivedSeries` and Mathlib's
`Submodule.prodEquivOfIsCompl` for the unique linear decomposition.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §19.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

/-- Every fixed vector has a unique decomposition into a fixed central vector and a fixed
vector in the ambient derived ideal. -/
theorem existsUnique_fixed_center_add_fixed_derivedSeries (e : L ≃ₗ⁅K⁆ L)
    (x : e.toLieHom.fixedSubalgebra) :
    ∃! p : (center K L) × derivedSeries K L 1,
      e p.1 = p.1 ∧ e p.2 = p.2 ∧ (p.1 : L) + p.2 = x := by
  have hc := LieSubmodule.isCompl_toSubmodule.mpr
    (TauCeti.isCompl_center_derivedSeries K L)
  let a := Submodule.prodEquivOfIsCompl (center K L).toSubmodule
    (derivedSeries K L 1).toSubmodule hc
  obtain ⟨p, hp⟩ := a.surjective (x : L)
  have hsum : (p.1 : L) + p.2 = x := by
    simpa only [a, Submodule.coe_prodEquivOfIsCompl'] using hp
  -- Uniqueness of the centre/derived decomposition makes both components fixed.
  have hz : e p.1 ∈ center K L := by
    rw [LieModule.mem_maxTrivSubmodule]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simp only [coe_toLieHom]
    rw [← e.map_lie, (LieModule.mem_maxTrivSubmodule K L L p.1).mp p.1.property y,
      map_zero]
  have hd : e p.2 ∈ derivedSeries K L 1 :=
    (LieIdeal.derivedSeries_map_le (f := e.toLieHom) 1) (LieIdeal.mem_map p.2.property)
  have hfixed : (⟨e p.1, hz⟩, ⟨e p.2, hd⟩) = p := by
    apply a.injective
    calc
      a (⟨e p.1, hz⟩, ⟨e p.2, hd⟩) = e p.1 + e p.2 :=
        Submodule.coe_prodEquivOfIsCompl' _ _ _ _
      _ = e ((p.1 : L) + p.2) := (map_add e _ _).symm
      _ = x := by rw [hsum]; exact LieHom.mem_fixedSubalgebra.mp x.property
      _ = a p := hp.symm
  refine ⟨p, ⟨congrArg (fun q => (q.1 : L)) hfixed,
    congrArg (fun q => (q.2 : L)) hfixed, hsum⟩, ?_⟩
  intro q hq
  apply a.injective
  simpa only [a, Submodule.coe_prodEquivOfIsCompl'] using hq.2.2.trans hsum.symm

/-- Addition identifies the fixed algebra with the product of its fixed central part and the
fixed part of the ambient derived ideal. The factors are subalgebras of the ambient algebra,
so their elements retain their original central and derived membership proofs. -/
noncomputable def fixedCenterDerivedEquiv (e : L ≃ₗ⁅K⁆ L) :
    (↥(e.toLieHom.fixedSubalgebra ⊓ (center K L).toLieSubalgebra) ×
      ↥(e.toLieHom.fixedSubalgebra ⊓ (derivedSeries K L 1).toLieSubalgebra)) ≃ₗ⁅K⁆
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
        have hz (z : center K L) (y : L) : ⁅y, (z : L)⁆ = 0 :=
          (LieModule.mem_maxTrivSubmodule K L L z).mp z.property y
        have hcross : ⁅(p.1 : L), (q.2 : L)⁆ = 0 := by
          rw [← lie_skew, hz ⟨(p.1 : L), p.1.property.2⟩, neg_zero]
        simp [lie_add, add_lie, hz ⟨(q.1 : L), q.1.property.2⟩, hcross] }
    (by
      constructor
      · intro p q hpq
        have hc := LieSubmodule.isCompl_toSubmodule.mpr
          (TauCeti.isCompl_center_derivedSeries K L)
        have h : ((⟨(p.1 : L), p.1.property.2⟩ : center K L),
            (⟨(p.2 : L), p.2.property.2⟩ : derivedSeries K L 1)) =
            (⟨(q.1 : L), q.1.property.2⟩, ⟨(q.2 : L), q.2.property.2⟩) := by
          apply (Submodule.prodEquivOfIsCompl (center K L).toSubmodule
            (derivedSeries K L 1).toSubmodule hc).injective
          simp only [Submodule.coe_prodEquivOfIsCompl']
          exact congrArg Subtype.val hpq
        apply Prod.ext <;> apply Subtype.ext
        · exact congrArg (fun r => (r.1 : L)) h
        · exact congrArg (fun r => (r.2 : L)) h
      · intro x
        obtain ⟨p, hp, _⟩ := e.existsUnique_fixed_center_add_fixed_derivedSeries x
        exact ⟨(⟨p.1, LieHom.mem_fixedSubalgebra.mpr hp.1, p.1.property⟩,
          ⟨p.2, LieHom.mem_fixedSubalgebra.mpr hp.2.1, p.2.property⟩),
          Subtype.ext hp.2.2⟩)

/-- The fixed-part decomposition is addition in the ambient Lie algebra. -/
@[simp]
theorem fixedCenterDerivedEquiv_apply (e : L ≃ₗ⁅K⁆ L)
    (p : ↥(e.toLieHom.fixedSubalgebra ⊓ (center K L).toLieSubalgebra) ×
      ↥(e.toLieHom.fixedSubalgebra ⊓ (derivedSeries K L 1).toLieSubalgebra)) :
    (e.fixedCenterDerivedEquiv p : L) = (p.1 : L) + p.2 :=
  (rfl)

/-- The inverse decomposition recovers a fixed vector by adding its two components. -/
@[simp]
theorem fixedCenterDerivedEquiv_symm_add (e : L ≃ₗ⁅K⁆ L)
    (x : e.toLieHom.fixedSubalgebra) :
    ((e.fixedCenterDerivedEquiv.symm x).1 : L) +
      (e.fixedCenterDerivedEquiv.symm x).2 = x := by
  rw [← fixedCenterDerivedEquiv_apply, LieEquiv.apply_symm_apply]

end LieEquiv
