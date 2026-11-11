/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.RestrictScalars
public import TauCeti.Algebra.Lie.Graded.Truncation
public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.RestrictScalars
public import TauCeti.Algebra.PositiveDegrees.RestrictScalars

/-!
# Restriction of scalars for graded Lie algebras

A grading of a Lie algebra remains a grading after restricting scalars in its
homogeneous pieces. Its homogeneous components have the same underlying values
by `DirectSum.coe_decompose_restrictScalars`, without freeness or flatness
assumptions. The bracket compatibility is unchanged. For a positive grading, degree
ideals and finite truncations commute with scalar restriction. The Lie equivalence
preserves quotient representatives, homogeneous pieces and projections, and commutes
with transitions between cutoffs.

Adapted from `Mei/Algebra/Lie/Graded/RestrictScalars.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

variable {R S L ι : Type*} [CommRing R] [CommRing S] [LieRing L]
  [LieAlgebra S L] [LieAlgebra R L] [SMul R S] [IsScalarTower R S L]
  [DecidableEq ι] [AddCommMonoid ι] (ℒ : ι → Submodule S L)

/-- Restricting scalars preserves a bracket-compatible internal grading. -/
instance GradedLieAlgebra.restrictScalars [GradedLieAlgebra ℒ] :
    GradedLieAlgebra (fun i => (ℒ i).restrictScalars R) where
  toDecomposition := inferInstance
  bracket_mem := SetLike.GradedBracket.bracket_mem (ℒ := ℒ) (ℳ := ℒ)

namespace TauCeti.PositiveDegrees

variable {ι : Type} [DecidableEq ι] [AddCommMonoid ι]
  (ℒ : ι → Submodule S L) (d : TauCeti.PositiveDegrees ι)
  [GradedLieAlgebra ℒ] [TauCeti.IsPositiveGrading d ℒ]

/-- The degree ideal of the restricted grading is the restriction of the degree ideal. -/
@[simp]
theorem degreeIdeal_restrictScalars (k : ℕ) :
    d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k =
      (d.degreeIdeal ℒ k).restrictScalars R := by
  apply LieSubmodule.toSubmodule_injective
  simp

/-- Restricting scalars commutes with finite Lie truncation. -/
def truncatedRestrictScalarsEquiv (k : ℕ) :
    d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ⁅R⁆
      d.truncatedLie ℒ k :=
  (LieIdeal.quotEquivOfEq _ _ (d.degreeIdeal_restrictScalars ℒ k)).trans
    ((d.degreeIdeal ℒ k).quotientRestrictScalarsEquiv R)

/-- The truncation comparison preserves representatives. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_mk (k : ℕ) (x : L) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  simp [truncatedRestrictScalarsEquiv]

/-- The inverse comparison preserves quotient representatives. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_symm_mk (k : ℕ) (x : L) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  apply (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).injective
  simp

/-- The comparison intertwines the restricted quotient projection and the quotient projection
of the restricted grading. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_comp_mkQ (k : ℕ) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.comp
        (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).mkQ =
      (d.degreeIdeal ℒ k).mkQ.restrictScalars R := by
  ext x
  simp [LieIdeal.mkQ_apply]

/-- The comparison identifies homogeneous pieces with their restrictions of scalars. -/
theorem map_truncatedGrading_restrictScalars (k : ℕ) (n : ι) :
    (d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k n).map
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLinearMap =
      (d.truncatedGrading ℒ k n).restrictScalars R := by
  simp only [truncatedGrading_eq, ← Submodule.map_comp, Submodule.restrictScalars_map]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact d.truncatedRestrictScalarsEquiv_mk (R := R) ℒ k x

/-- The comparison identifies the homogeneous pieces in the two truncations. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_mem_iff (k : ℕ) (n : ι)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k x ∈ d.truncatedGrading ℒ k n ↔
      x ∈ d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k n := by
  rw [← Submodule.restrictScalars_mem R, ← d.map_truncatedGrading_restrictScalars ℒ k n]
  constructor
  · rintro ⟨y, hy, h⟩
    exact (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).injective h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Homogeneous projection commutes with the scalar-restriction comparison. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_decompose (k : ℕ) (n : ι)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k
        (DirectSum.decompose (d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k) x n :
          d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) =
      (DirectSum.decompose (d.truncatedGrading ℒ k)
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ k x) n : d.truncatedLie ℒ k) := by
  induction x using Submodule.Quotient.induction_on with | _ x
  simp

/-- The finite-order comparisons commute with transitions to smaller cutoffs. -/
theorem truncatedRestrictScalarsEquiv_comp_truncationMap {k l : ℕ} (h : k ≤ l) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.comp
        (d.truncationMap (fun n => (ℒ n).restrictScalars R) h) =
      ((d.truncationMap ℒ h).restrictScalars R).comp
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ l).toLieHom := by
  ext x
  simp [LieIdeal.mkQ_apply]

end TauCeti.PositiveDegrees
