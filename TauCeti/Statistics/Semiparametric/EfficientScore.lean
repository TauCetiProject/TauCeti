/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.Statistics.Semiparametric.TangentSpace

/-!
# Efficient scores and information matrices

Given a score `ℓ ∈ L²(P)` and a set `N ⊆ L²(P)` of nuisance scores, the efficient score
`efficientScore P N ℓ` is the residual `ℓ - Π_N ℓ` after orthogonal projection onto the nuisance
tangent space `tangentSpace P N`. For an indexed family of scores `ℓ : ι → Lp ℝ 2 P`, the
information matrix `informationMatrix P ℓ` and efficient information matrix
`efficientInformationMatrix P N ℓ` are the Gram matrices of `ℓ` and of the efficient scores
(van der Vaart, *Asymptotic Statistics*, 1998, §25.4, pp. 369–370).

## Main definitions

* `TauCeti.efficientScore`: the residual `ℓ - Π_N ℓ` orthogonal to the nuisance tangent space.
* `TauCeti.informationMatrix`: the Gram matrix `Iᵢⱼ = ⟪ℓᵢ, ℓⱼ⟫` of a family of scores.
* `TauCeti.efficientInformationMatrix`: the Gram matrix of the efficient scores
  `efficientScore P N (ℓ i)`.

## Main results

* `TauCeti.efficientScore_mem_orthogonal`, `TauCeti.inner_efficientScore_eq_zero`,
  `TauCeti.efficientScore_eq_self_iff`: orthogonality and adaptation of the efficient score.
* `TauCeti.posSemidef_informationMatrix`, `TauCeti.posDef_informationMatrix_iff`,
  `TauCeti.posSemidef_efficientInformationMatrix`,
  `TauCeti.posDef_efficientInformationMatrix_iff`: positive semidefiniteness and the linear
  independence criterion for positive definiteness.
* `TauCeti.efficientInformationMatrix_sub_eq_gram_of_subset`,
  `TauCeti.posSemidef_efficientInformationMatrix_sub_of_subset`,
  `TauCeti.efficientInformationMatrix_eq_of_subset_iff`: enlarging the nuisance set `N ⊆ N'` lowers
  the efficient information matrix by the Gram matrix of `(Π_{N'} - Π_N) ℓ`.
* `TauCeti.informationMatrix_sub_efficientInformationMatrix_eq_gram`,
  `TauCeti.posSemidef_informationMatrix_sub_efficient`,
  `TauCeti.efficientInformationMatrix_eq_informationMatrix_iff`: information loss
  `informationMatrix P ℓ - efficientInformationMatrix P N ℓ` is positive semidefinite and vanishes
  if and only if every score is orthogonal to `N`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] (P : Measure X)

/-! ### Efficient scores -/

/-- The efficient score: the residual `ℓ - Π_N ℓ` after orthogonal projection onto the nuisance
tangent space `tangentSpace P N`. -/
def efficientScore (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) : Lp ℝ 2 P :=
  ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ

/-- Definitional restatement of `efficientScore P N ℓ`. -/
theorem efficientScore_def (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ :=
  (rfl)

/-- The efficient score is the orthogonal projection of `ℓ` onto `(tangentSpace P N)ᗮ`. -/
theorem efficientScore_eq_starProjection_orthogonal (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = (tangentSpace P N).toSubmoduleᗮ.starProjection ℓ :=
  (Submodule.starProjection_orthogonal_val ℓ).symm

/-- The efficient score of `0` is `0`. -/
@[simp]
theorem efficientScore_zero (N : Set (Lp ℝ 2 P)) : efficientScore P N 0 = 0 := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_zero]

/-- The efficient score is additive in the score. -/
theorem efficientScore_add (N : Set (Lp ℝ 2 P)) (ℓ₁ ℓ₂ : Lp ℝ 2 P) :
    efficientScore P N (ℓ₁ + ℓ₂) = efficientScore P N ℓ₁ + efficientScore P N ℓ₂ := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_add]

/-- The efficient score preserves subtraction in the score. -/
theorem efficientScore_sub (N : Set (Lp ℝ 2 P)) (ℓ₁ ℓ₂ : Lp ℝ 2 P) :
    efficientScore P N (ℓ₁ - ℓ₂) = efficientScore P N ℓ₁ - efficientScore P N ℓ₂ := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_sub]

/-- The efficient score preserves negation in the score. -/
theorem efficientScore_neg (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (-ℓ) = -efficientScore P N ℓ := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_neg]

/-- The efficient score is homogeneous in the score. -/
theorem efficientScore_smul (N : Set (Lp ℝ 2 P)) (c : ℝ) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (c • ℓ) = c • efficientScore P N ℓ := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_smul]

/-- The efficient score lies in the orthogonal complement of the nuisance tangent space. -/
theorem efficientScore_mem_orthogonal (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ ∈ (tangentSpace P N).toSubmoduleᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

/-- The efficient score is orthogonal to every nuisance score in `N`. -/
theorem inner_efficientScore_eq_zero {N : Set (Lp ℝ 2 P)} {ℓ g : Lp ℝ 2 P} (hg : g ∈ N) :
    inner ℝ g (efficientScore P N ℓ) = 0 :=
  (mem_orthogonal_tangentSpace_iff P).1 (efficientScore_mem_orthogonal P N ℓ) g hg

/-- The efficient score equals `ℓ` if and only if `ℓ` is orthogonal to every nuisance score in
`N`. -/
theorem efficientScore_eq_self_iff {N : Set (Lp ℝ 2 P)} {ℓ : Lp ℝ 2 P} :
    efficientScore P N ℓ = ℓ ↔ ∀ g ∈ N, inner ℝ g ℓ = 0 := by
  rw [efficientScore, sub_eq_self, Submodule.starProjection_apply_eq_zero_iff,
    mem_orthogonal_tangentSpace_iff]

/-- The efficient score vanishes if and only if `ℓ` lies in the nuisance tangent space. -/
theorem efficientScore_eq_zero_iff {N : Set (Lp ℝ 2 P)} {ℓ : Lp ℝ 2 P} :
    efficientScore P N ℓ = 0 ↔ ℓ ∈ tangentSpace P N := by
  rw [efficientScore, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff,
    ClosedSubmodule.mem_toSubmodule_iff]

/-- With no nuisance scores, the efficient score is `ℓ` itself. -/
@[simp]
theorem efficientScore_empty (ℓ : Lp ℝ 2 P) : efficientScore P ∅ ℓ = ℓ :=
  (efficientScore_eq_self_iff P).2 fun _ h ↦ h.elim

/-- If `ℓ` and every nuisance score in `N` have mean zero, then `efficientScore P N ℓ` has mean
zero. -/
theorem efficientScore_mem_meanZeroL2 [IsFiniteMeasure P] {N : Set (Lp ℝ 2 P)}
    (hN : N ⊆ meanZeroL2 P) {ℓ : Lp ℝ 2 P} (hℓ : ℓ ∈ meanZeroL2 P) :
    efficientScore P N ℓ ∈ meanZeroL2 P :=
  (meanZeroL2 P).sub_mem hℓ
    (tangentSpace_le_meanZeroL2 P hN (Submodule.starProjection_apply_mem _ _))

/-- Pythagoras for a score split into its efficient score and its projection onto the nuisance
tangent space. -/
theorem norm_efficientScore_sq_add_norm_starProjection_sq (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    ‖efficientScore P N ℓ‖ ^ 2 + ‖(tangentSpace P N).toSubmodule.starProjection ℓ‖ ^ 2 =
      ‖ℓ‖ ^ 2 := by
  rw [efficientScore_eq_starProjection_orthogonal, add_comm]
  exact (Submodule.norm_sq_eq_add_norm_sq_starProjection ℓ (tangentSpace P N).toSubmodule).symm

/-! ### Information matrices -/

/-- The information matrix `Iᵢⱼ = ⟪ℓᵢ, ℓⱼ⟫` of an indexed family of scores in `Lp ℝ 2 P`. -/
def informationMatrix {ι : Type*} (ℓ : ι → Lp ℝ 2 P) : Matrix ι ι ℝ :=
  Matrix.gram ℝ ℓ

/-- Definitional restatement of `informationMatrix P ℓ` as `Matrix.gram ℝ ℓ`. -/
theorem informationMatrix_eq_gram {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    informationMatrix P ℓ = Matrix.gram ℝ ℓ :=
  (rfl)

/-- The efficient information matrix of an indexed family of scores relative to a set `N` of
nuisance scores: the Gram matrix of `efficientScore P N (ℓ i)`. -/
def efficientInformationMatrix {ι : Type*} (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    Matrix ι ι ℝ :=
  Matrix.gram ℝ fun i ↦ efficientScore P N (ℓ i)

/-- Definitional restatement of `efficientInformationMatrix P N ℓ` as the Gram matrix of the
efficient scores. -/
theorem efficientInformationMatrix_eq_gram {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = Matrix.gram ℝ fun i ↦ efficientScore P N (ℓ i) :=
  (rfl)

/-- The `(i, j)` entry of the information matrix is `⟪ℓ i, ℓ j⟫`. -/
@[simp]
theorem informationMatrix_apply {ι : Type*} (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    informationMatrix P ℓ i j = inner ℝ (ℓ i) (ℓ j) :=
  (rfl)

/-- The `(i, j)` entry of the efficient information matrix is
`⟪efficientScore P N (ℓ i), efficientScore P N (ℓ j)⟫`. -/
@[simp]
theorem efficientInformationMatrix_apply {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    efficientInformationMatrix P N ℓ i j =
      inner ℝ (efficientScore P N (ℓ i)) (efficientScore P N (ℓ j)) :=
  (rfl)

/-- With no nuisance scores, the efficient information matrix is the information matrix. -/
@[simp]
theorem efficientInformationMatrix_empty {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P ∅ ℓ = informationMatrix P ℓ := by
  simp [efficientInformationMatrix, informationMatrix]

/-- The information matrix is positive semidefinite. -/
theorem posSemidef_informationMatrix {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ).PosSemidef :=
  Matrix.posSemidef_gram ℝ ℓ

/-- The information matrix is positive definite if and only if the scores are linearly independent
in `Lp ℝ 2 P`. -/
theorem posDef_informationMatrix_iff {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ).PosDef ↔ LinearIndependent ℝ ℓ :=
  Matrix.posDef_gram_iff_linearIndependent

/-- The efficient information matrix is positive semidefinite. -/
theorem posSemidef_efficientInformationMatrix {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : (efficientInformationMatrix P N ℓ).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

/-- The efficient information matrix is positive definite if and only if the efficient scores are
linearly independent in `Lp ℝ 2 P`. -/
theorem posDef_efficientInformationMatrix_iff {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    (efficientInformationMatrix P N ℓ).PosDef ↔
      LinearIndependent ℝ fun i ↦ efficientScore P N (ℓ i) :=
  Matrix.posDef_gram_iff_linearIndependent

/-- For nested nuisance sets `N ⊆ N'`, the drop in efficient information
`efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ` is the Gram matrix of the
projection increments `Π_{N'} ℓᵢ - Π_N ℓᵢ`. -/
theorem efficientInformationMatrix_sub_eq_gram_of_subset {ι : Type*} {N N' : Set (Lp ℝ 2 P)}
    (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ =
      Matrix.gram ℝ fun i ↦
        (tangentSpace P N').toSubmodule.starProjection (ℓ i) -
          (tangentSpace P N).toSubmodule.starProjection (ℓ i) := by
  set K := (tangentSpace P N).toSubmodule
  set K' := (tangentSpace P N').toSubmodule
  have hK : K ≤ K' := tangentSpace_mono P h
  ext i j
  simp only [Matrix.sub_apply, efficientInformationMatrix_apply, Matrix.gram_apply]
  -- Split `efficientScore P N (ℓ k) = efficientScore P N' (ℓ k) + (Π_{N'} ℓ - Π_N ℓ)`, where the
  -- two summands lie in `K'ᗮ` and `K'`.
  have hsplit (k : ι) :
      efficientScore P N (ℓ k) =
        efficientScore P N' (ℓ k) + (K'.starProjection (ℓ k) - K.starProjection (ℓ k)) := by
    simp only [efficientScore, K, K']
    abel
  have hd_mem (k : ι) : K'.starProjection (ℓ k) - K.starProjection (ℓ k) ∈ K' :=
    K'.sub_mem (K'.starProjection_apply_mem _) (hK (K.starProjection_apply_mem _))
  have he_orth (k : ι) : efficientScore P N' (ℓ k) ∈ K'ᗮ :=
    efficientScore_mem_orthogonal P N' (ℓ k)
  have hcross₁ :
      inner ℝ (efficientScore P N' (ℓ i)) (K'.starProjection (ℓ j) - K.starProjection (ℓ j)) = 0 :=
    Submodule.inner_left_of_mem_orthogonal (hd_mem j) (he_orth i)
  have hcross₂ :
      inner ℝ (K'.starProjection (ℓ i) - K.starProjection (ℓ i)) (efficientScore P N' (ℓ j)) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (hd_mem i) (he_orth j)
  rw [hsplit i, hsplit j, inner_add_left, inner_add_right, inner_add_right, hcross₁, hcross₂]
  ring

/-- Enlarging the nuisance set can only decrease the efficient information matrix in the Loewner
order. -/
theorem posSemidef_efficientInformationMatrix_sub_of_subset {ι : Type*} {N N' : Set (Lp ℝ 2 P)}
    (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    (efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ).PosSemidef := by
  rw [efficientInformationMatrix_sub_eq_gram_of_subset P h]
  exact Matrix.posSemidef_gram ℝ _

/-- For `N ⊆ N'`, enlarging the nuisance set leaves the efficient information matrix unchanged if
and only if every score has the same projection onto both nuisance tangent spaces. -/
theorem efficientInformationMatrix_eq_of_subset_iff {ι : Type*} {N N' : Set (Lp ℝ 2 P)}
    (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N' ℓ = efficientInformationMatrix P N ℓ ↔
      ∀ i, (tangentSpace P N').toSubmodule.starProjection (ℓ i) =
        (tangentSpace P N).toSubmodule.starProjection (ℓ i) := by
  refine ⟨fun hEq i ↦ ?_, fun hproj ↦ ?_⟩
  · have h0 : (efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ) i i = 0 := by
      rw [hEq, sub_self]
      rfl
    rw [efficientInformationMatrix_sub_eq_gram_of_subset P h, Matrix.gram_apply,
      inner_self_eq_zero, sub_eq_zero] at h0
    exact h0
  · ext i j
    simp [efficientScore, hproj i, hproj j]

/-- The information loss `informationMatrix P ℓ - efficientInformationMatrix P N ℓ` due to the
nuisance set `N` is the Gram matrix of the projections of the scores onto `tangentSpace P N`. -/
theorem informationMatrix_sub_efficientInformationMatrix_eq_gram {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    informationMatrix P ℓ - efficientInformationMatrix P N ℓ =
      Matrix.gram ℝ fun i ↦ (tangentSpace P N).toSubmodule.starProjection (ℓ i) := by
  simpa using efficientInformationMatrix_sub_eq_gram_of_subset P (Set.empty_subset N) ℓ

/-- Information loss: `informationMatrix P ℓ - efficientInformationMatrix P N ℓ` is positive
semidefinite. -/
theorem posSemidef_informationMatrix_sub_efficient {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ - efficientInformationMatrix P N ℓ).PosSemidef := by
  rw [informationMatrix_sub_efficientInformationMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℝ _

/-- Adaptation criterion: the efficient information matrix equals the full information matrix if and
only if every score is orthogonal to every nuisance score in `N`. -/
theorem efficientInformationMatrix_eq_informationMatrix_iff {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = informationMatrix P ℓ ↔
      ∀ i, ∀ g ∈ N, inner ℝ g (ℓ i) = 0 := by
  rw [← efficientInformationMatrix_empty P ℓ,
    efficientInformationMatrix_eq_of_subset_iff P (Set.empty_subset N) ℓ]
  simp only [tangentSpace_empty, ClosedSubmodule.toSubmodule_bot, Submodule.starProjection_bot,
    zero_apply, Submodule.starProjection_apply_eq_zero_iff,
    mem_orthogonal_tangentSpace_iff]

end TauCeti
