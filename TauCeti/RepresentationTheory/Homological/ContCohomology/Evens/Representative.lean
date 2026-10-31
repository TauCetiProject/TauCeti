/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.Character
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded

/-!
# Character representatives in the total coinduced resolution

A continuous character with values in `𝔽₂` determines a homogeneous degree-one cocycle.
Including it in the total coinduced resolution gives the input for tensor induction in the
Evens norm. The defining equation records this inclusion, and the membership, invariance and
closedness lemmas supply the three hypotheses needed by the tensor-induced diagonal class.

The representative is the homogeneous cocycle used by `homClass`, with no choice of a
cohomologous cochain. For trivial coefficients, degree-one classes have unique character
representatives.

The tensor-resolution construction follows L. Evens, *A generalization of the transfer map
in the cohomology of groups*, Trans. Amer. Math. Soc. **108** (1963), Sections 2–5.
-/

public section

namespace TauCeti.ContCohomology

universe u

variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (α : H →* Multiplicative (ZMod 2)) (hα : Continuous α)

/-- The homogeneous cocycle of a continuous `𝔽₂` character, included in degree one of the
total coinduced resolution. -/
noncomputable def evensCharacterRepresentative : (trivialF2 H).gradedResolutionModule :=
  DirectSum.lof ℤ ℕ (fun n ↦ (TopRep.resolutionX (trivialF2 H) (n + 1)).V) 1
    (inhomogeneousCochain1 (fun x ↦ Multiplicative.toAdd (α x)) (continuous_toAdd.comp hα)).val

/-- The character representative includes its homogeneous cochain in degree one. -/
theorem evensCharacterRepresentative_def :
    evensCharacterRepresentative H α hα =
      DirectSum.lof ℤ ℕ (fun n ↦ (TopRep.resolutionX (trivialF2 H) (n + 1)).V) 1
        (inhomogeneousCochain1 (fun x ↦ Multiplicative.toAdd (α x))
          (continuous_toAdd.comp hα)).val := (rfl)

/-- A character representative is homogeneous of degree one. -/
@[simp]
theorem evensCharacterRepresentative_mem :
    evensCharacterRepresentative H α hα ∈ (trivialF2 H).gradedResolutionPiece 1 :=
  (trivialF2 H).lof_mem_gradedResolutionPiece 1 _

/-- A character representative is fixed by the group action. -/
@[simp]
theorem evensCharacterRepresentative_invariant (x : H) :
    (trivialF2 H).gradedResolutionTopRep.ρ x (evensCharacterRepresentative H α hα) =
      evensCharacterRepresentative H α hα := by
  rw [evensCharacterRepresentative_def]
  exact ((trivialF2 H).gradedResolutionTopRep_ρ_lof 1 x _).trans
    (congrArg (DirectSum.lof ℤ ℕ
      (fun n ↦ (TopRep.resolutionX (trivialF2 H) (n + 1)).V) 1)
        ((inhomogeneousCochain1 (fun x ↦ Multiplicative.toAdd (α x))
          (continuous_toAdd.comp hα)).property x))

/-- The differential of a character representative vanishes. -/
@[simp]
theorem evensCharacterRepresentative_d_eq_zero :
    (trivialF2 H).gradedResolutionDifferential (evensCharacterRepresentative H α hα) = 0 := by
  have hc := inhomogeneousCochain1_d_eq_zero
    (fun x ↦ Multiplicative.toAdd (α x)) (continuous_toAdd.comp hα)
    (fun g h ↦ by simp [map_mul, toAdd_mul])
  have hd := congrArg Subtype.val hc
  rw [TopRep.homogeneousCochains.d_apply] at hd
  exact ((trivialF2 H).gradedResolutionDifferential_lof 1
    (inhomogeneousCochain1 (fun x ↦ Multiplicative.toAdd (α x))
      (continuous_toAdd.comp hα)).val).trans
    ((congrArg (DirectSum.lof ℤ ℕ
      (fun n ↦ (TopRep.resolutionX (trivialF2 H) (n + 1)).V) 2) hd).trans (map_zero _))

/-- The trivial character has the zero representative in the total resolution. -/
@[simp]
theorem evensCharacterRepresentative_one :
    evensCharacterRepresentative H (1 : H →* Multiplicative (ZMod 2)) continuous_const = 0 := by
  rw [evensCharacterRepresentative_def]
  have hf : (inhomogeneousCochain1
      (fun x : H ↦ Multiplicative.toAdd ((1 : H →* Multiplicative (ZMod 2)) x))
      (continuous_toAdd.comp continuous_const)).val = 0 := by
    ext g h
    exact (inhomogeneousCochain1_apply _ _ g h).trans (map_zero (trivialF2Equiv H).symm)
  rw [hf, map_zero]

end TauCeti.ContCohomology
