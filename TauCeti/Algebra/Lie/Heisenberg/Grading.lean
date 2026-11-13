/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Truncation
public import TauCeti.Algebra.Lie.Heisenberg.Basic

/-!
# The positive grading of the Heisenberg Lie algebra

The standard Heisenberg generators `X` and `Y` have degree one, and their
bracket `Z` has degree two. The other integer-graded pieces vanish. This gives
a positive `GradedLieAlgebra` over every commutative ring, with explicit
homogeneous projections and degree ideals.

We use Tau Ceti's `heisenbergBasis` and bracket table on the existing strictly
upper triangular matrix Lie algebra. The internal decomposition is obtained by
collecting the basis lines using `DirectSum.IsInternal.iSup_fiber`.

Adapted from `Mei/Algebra/Lie/Heisenberg/Grading.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

/-- The Heisenberg grading: `R X + R Y` in degree one and `R Z` in degree two. -/
def heisenbergGrading (n : ℤ) : Submodule R (heisenberg R) :=
  if n = 1 then R ∙ heisenbergX R ⊔ R ∙ heisenbergY R
  else if n = 2 then R ∙ heisenbergZ R else ⊥

/-- The defining pieces of the Heisenberg grading. -/
theorem heisenbergGrading_def (n : ℤ) :
    heisenbergGrading R n =
      if n = 1 then R ∙ heisenbergX R ⊔ R ∙ heisenbergY R
      else if n = 2 then R ∙ heisenbergZ R else ⊥ := (rfl)

/-- The degree-one piece is spanned by the standard generators `X` and `Y`. -/
@[simp]
theorem heisenbergGrading_one :
    heisenbergGrading R 1 = R ∙ heisenbergX R ⊔ R ∙ heisenbergY R := by
  simp [heisenbergGrading_def]

/-- The degree-two piece is the central line. -/
@[simp]
theorem heisenbergGrading_two : heisenbergGrading R 2 = R ∙ heisenbergZ R := by
  simp [heisenbergGrading_def]

/-- All pieces other than degrees one and two vanish. -/
@[simp]
theorem heisenbergGrading_eq_bot {n : ℤ} (h₁ : n ≠ 1) (h₂ : n ≠ 2) :
    heisenbergGrading R n = ⊥ := by
  simp [heisenbergGrading_def, h₁, h₂]

/-- The standard generator `X` is homogeneous of degree one. -/
theorem heisenbergX_mem_grading : heisenbergX R ∈ heisenbergGrading R 1 := by
  rw [heisenbergGrading_one]
  exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)

/-- The standard generator `Y` is homogeneous of degree one. -/
theorem heisenbergY_mem_grading : heisenbergY R ∈ heisenbergGrading R 1 := by
  rw [heisenbergGrading_one]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/-- The central generator `Z` is homogeneous of degree two. -/
theorem heisenbergZ_mem_grading : heisenbergZ R ∈ heisenbergGrading R 2 := by
  simp [Submodule.mem_span_singleton_self]

/-- The Heisenberg pieces form an internal Lie grading. -/
noncomputable instance instGradedLieAlgebraHeisenbergGrading :
    GradedLieAlgebra (heisenbergGrading R) where
  toDecomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    have h : DirectSum.IsInternal (fun i : Fin 3 => R ∙ heisenbergBasis R i) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
        (heisenbergBasis R).linearIndependent.iSupIndep_span_singleton
        (by rw [← Submodule.span_range_eq_iSup, (heisenbergBasis R).span_eq])
    convert h.iSup_fiber (fun i : Fin 3 => if i = 2 then (2 : ℤ) else 1) using 1
    funext n
    simp only [iSup_fin_three, heisenbergBasis_zero, heisenbergBasis_one,
      heisenbergBasis_two]
    by_cases h₁ : n = 1 <;> by_cases h₂ : n = 2 <;>
      simp [heisenbergGrading_def, h₁, h₂, eq_comm]
  bracket_mem := by
    intro n m x y hx hy
    by_cases hn : n = 1
    · subst n
      by_cases hm : m = 1
      · subst m
        rw [lie_eq_smul_heisenbergZ]
        exact Submodule.smul_mem _ _ (heisenbergZ_mem_grading R)
      · by_cases hm₂ : m = 2
        · subst m
          rw [heisenbergGrading_two, Submodule.mem_span_singleton] at hy
          obtain ⟨c, rfl⟩ := hy
          simp
        · rw [heisenbergGrading_eq_bot R hm hm₂, Submodule.mem_bot] at hy
          simp [hy]
    · by_cases hn₂ : n = 2
      · subst n
        rw [heisenbergGrading_two, Submodule.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        simp
      · rw [heisenbergGrading_eq_bot R hn hn₂, Submodule.mem_bot] at hx
        simp [hx]

/-- The Heisenberg grading is supported on strictly positive integer degrees. -/
instance heisenbergGrading_isPositiveGrading :
    IsPositiveGrading PositiveDegrees.nonnegIntegers (heisenbergGrading R) where
  eq_bot n hn := by
    simp only [PositiveDegrees.mem_nonnegIntegers_monoid] at hn
    exact heisenbergGrading_eq_bot R (by omega) (by omega)

/-- Homogeneous projection keeps the two superdiagonal entries in degree one and
the corner entry in degree two. -/
@[simp]
theorem decompose_heisenbergGrading (x : heisenberg R) (n : ℤ) :
    (DirectSum.decompose (heisenbergGrading R) x n : heisenberg R) =
      if n = 1 then
        (x : Matrix (Fin 3) (Fin 3) R) 0 1 • heisenbergX R +
          (x : Matrix (Fin 3) (Fin 3) R) 1 2 • heisenbergY R
      else if n = 2 then (x : Matrix (Fin 3) (Fin 3) R) 0 2 • heisenbergZ R else 0 := by
  conv_lhs => rw [eq_smul_heisenbergX_add_smul_heisenbergY_add_smul_heisenbergZ x]
  simp only [DirectSum.decompose_add, DirectSum.decompose_smul,
    DirectSum.add_apply, DirectSum.smul_apply, Submodule.coe_add, Submodule.coe_smul_of_tower]
  by_cases h₁ : n = 1
  · subst n
    simp [DirectSum.decompose_of_mem_same _ (heisenbergX_mem_grading R),
      DirectSum.decompose_of_mem_same _ (heisenbergY_mem_grading R),
      DirectSum.decompose_of_mem_ne _ (heisenbergZ_mem_grading R) (by decide : (2 : ℤ) ≠ 1)]
  · by_cases h₂ : n = 2
    · subst n
      simp [DirectSum.decompose_of_mem_same _ (heisenbergZ_mem_grading R),
        DirectSum.decompose_of_mem_ne _ (heisenbergX_mem_grading R) (by decide : (1 : ℤ) ≠ 2),
        DirectSum.decompose_of_mem_ne _ (heisenbergY_mem_grading R) (by decide : (1 : ℤ) ≠ 2)]
    · simp [h₁, h₂,
        DirectSum.decompose_of_mem_ne _ (heisenbergX_mem_grading R) (Ne.symm h₁),
        DirectSum.decompose_of_mem_ne _ (heisenbergY_mem_grading R) (Ne.symm h₁),
        DirectSum.decompose_of_mem_ne _ (heisenbergZ_mem_grading R) (Ne.symm h₂)]

/-- The Heisenberg terms strictly above degree one form its center. -/
@[simp]
theorem degreeIdeal_heisenbergGrading_one :
    PositiveDegrees.nonnegIntegers.degreeIdeal (heisenbergGrading R) 1 =
      LieAlgebra.center R (heisenberg R) := by
  apply LieSubmodule.toSubmodule_injective
  rw [PositiveDegrees.degreeIdeal_toSubmodule,
    center_heisenberg_toSubmodule_eq_span_heisenbergZ,
    PositiveDegrees.degreeSubmodule_def]
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · by_cases h : n.val = 2
    · simp [h]
    · rw [heisenbergGrading_eq_bot R (by have := n.property; simp at this; omega) h]
      exact bot_le
  · exact (heisenbergGrading_two R) ▸
      le_iSup_of_le ⟨2, by simp⟩ le_rfl

/-- The Heisenberg degree ideal vanishes from order two onwards. -/
@[simp]
theorem degreeIdeal_heisenbergGrading_eq_bot {k : ℕ} (hk : 2 ≤ k) :
    PositiveDegrees.nonnegIntegers.degreeIdeal (heisenbergGrading R) k = ⊥ := by
  apply LieSubmodule.toSubmodule_injective
  rw [PositiveDegrees.degreeIdeal_toSubmodule, PositiveDegrees.degreeSubmodule_def]
  apply eq_bot_iff.mpr
  refine iSup_le fun n => ?_
  have hn := n.property
  simp only [PositiveDegrees.nonnegIntegers_degree] at hn
  rw [heisenbergGrading_eq_bot R (by omega) (by omega)]

end TauCeti
