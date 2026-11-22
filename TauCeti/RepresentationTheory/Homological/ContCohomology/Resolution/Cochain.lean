/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded.Basic

/-!
# Homogeneous cochains in the total coinduced resolution

The homogeneous cochains are invariant elements of individual resolution terms. Their linear
inclusions into the total resolution retain their degree and invariance and commute with the
differential. This lets constructions on the total resolution, such as diagonal tensor powers,
accept canonical cochains and coboundaries directly.
-/

public section

namespace TopRep

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

/-- Include a canonical homogeneous cochain into its degree of the total coinduced resolution. -/
noncomputable def cochainToGradedResolution (n : ℕ) :
    (homogeneousCochains X).X n →ₗ[R] X.gradedResolutionModule :=
  (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n).comp
    (resolutionX X (n + 1)).ρ.invariants.subtype

/-- The inclusion of a cochain is its underlying resolution element in the indicated summand. -/
theorem cochainToGradedResolution_apply (n : ℕ) (z : (homogeneousCochains X).X n) :
    X.cochainToGradedResolution n z =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n z.val := (rfl)

/-- The included cochain is homogeneous of its original degree. -/
@[simp↓]
theorem cochainToGradedResolution_mem (n : ℕ) (z : (homogeneousCochains X).X n) :
    X.cochainToGradedResolution n z ∈ X.gradedResolutionPiece n :=
  X.lof_mem_gradedResolutionPiece n z.val

/-- The inclusion of homogeneous cochains into the total resolution is injective. -/
theorem cochainToGradedResolution_injective (n : ℕ) :
    Function.Injective (X.cochainToGradedResolution n) := fun _ _ h ↦
  Subtype.ext (DirectSum.of_injective (β := fun n ↦ (resolutionX X (n + 1)).V) n h)

variable [DiscreteTopology R]

/-- The included cochain is invariant under the group action on the total resolution. -/
@[simp↓]
theorem cochainToGradedResolution_invariant (n : ℕ) (z : (homogeneousCochains X).X n)
    (g : G) :
    X.gradedResolutionTopRep.ρ g (X.cochainToGradedResolution n z) =
      X.cochainToGradedResolution n z := by
  rw [cochainToGradedResolution_apply, gradedResolutionTopRep_ρ_lof,
    (ContRepresentation.mem_invariants _).1 z.property g]

omit [DiscreteTopology R] in
/-- Inclusion of homogeneous cochains commutes with the differential. -/
@[simp↓]
theorem gradedResolutionDifferential_cochainToGradedResolution (n : ℕ)
    (z : (homogeneousCochains X).X n) :
    X.gradedResolutionDifferential (X.cochainToGradedResolution n z) =
      X.cochainToGradedResolution (n + 1)
        (((homogeneousCochains X).d n (n + 1)).hom z) := by
  rw [cochainToGradedResolution_apply, gradedResolutionDifferential_lof,
    cochainToGradedResolution_apply, homogeneousCochains.d_apply]

omit [DiscreteTopology R] in
/-- A homogeneous cochain is a cocycle exactly when its inclusion into the total resolution is
annihilated by the total differential. -/
theorem gradedResolutionDifferential_cochainToGradedResolution_eq_zero_iff (n : ℕ)
    (z : (homogeneousCochains X).X n) :
    X.gradedResolutionDifferential (X.cochainToGradedResolution n z) = 0 ↔
      ((homogeneousCochains X).d n (n + 1)).hom z = 0 := by
  rw [gradedResolutionDifferential_cochainToGradedResolution,
    ← map_zero (X.cochainToGradedResolution (n + 1)),
    (X.cochainToGradedResolution_injective (n + 1)).eq_iff]

/-- Every element of the total resolution that is homogeneous of degree `n` and invariant under the
group is the inclusion of a homogeneous `n`-cochain. -/
theorem exists_cochainToGradedResolution_eq {n : ℕ} {w : X.gradedResolutionModule}
    (hw : w ∈ X.gradedResolutionPiece n) (hinv : ∀ g, X.gradedResolutionTopRep.ρ g w = w) :
    ∃ z : (homogeneousCochains X).X n, X.cochainToGradedResolution n z = w := by
  obtain ⟨F, rfl⟩ := (SetLike.ext_iff.1 (X.gradedResolutionPiece_natCast n) w).1 hw
  exact ⟨⟨F, fun g ↦ DirectSum.of_injective (β := fun n ↦ (resolutionX X (n + 1)).V) n
      ((gradedResolutionTopRep_ρ_lof _ n g F).symm.trans (hinv g))⟩,
    cochainToGradedResolution_apply _ n _⟩

end TopRep
