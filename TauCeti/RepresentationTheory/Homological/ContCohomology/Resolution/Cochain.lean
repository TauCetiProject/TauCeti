/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded

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
theorem cochainToGradedResolution_mem (n : ℕ) (z : (homogeneousCochains X).X n) :
    X.cochainToGradedResolution n z ∈ X.gradedResolutionPiece n :=
  X.lof_mem_gradedResolutionPiece n z.val

variable [DiscreteTopology R]

/-- The included cochain is invariant under the group action on the total resolution. -/
theorem cochainToGradedResolution_invariant (n : ℕ) (z : (homogeneousCochains X).X n)
    (g : G) :
    X.gradedResolutionTopRep.ρ g (X.cochainToGradedResolution n z) =
      X.cochainToGradedResolution n z := by
  rw [cochainToGradedResolution_apply, gradedResolutionTopRep_ρ_lof,
    (ContRepresentation.mem_invariants _).1 z.property g]

omit [DiscreteTopology R] in
/-- Inclusion of homogeneous cochains commutes with the differential. -/
theorem gradedResolutionDifferential_cochainToGradedResolution (n : ℕ)
    (z : (homogeneousCochains X).X n) :
    X.gradedResolutionDifferential (X.cochainToGradedResolution n z) =
      X.cochainToGradedResolution (n + 1)
        (((homogeneousCochains X).d n (n + 1)).hom z) := by
  rw [cochainToGradedResolution_apply, gradedResolutionDifferential_lof,
    cochainToGradedResolution_apply, homogeneousCochains.d_apply]

end TopRep
