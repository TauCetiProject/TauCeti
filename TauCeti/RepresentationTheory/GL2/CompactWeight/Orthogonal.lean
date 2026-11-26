/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
public import TauCeti.RepresentationTheory.GKModule.Basic
public import TauCeti.RepresentationTheory.GL2.CompactWeight.Module

/-!
# The action of `O(2)` on the module of compact weights

The orthogonal group `O(2)` acts on `𝔤𝔩₂(ℂ)` by conjugation, `Ad g M = g M g⁻¹ = g M gᵀ`. A
rotation `g = !![a, -b; b, a]` has phase `z(g) = a - i b`, of absolute value one, and every
reflection is a rotation followed by `A = diag(1, -1)`. This file makes
`TauCeti.CompactWeightModule k μ` a `(𝔤𝔩₂(ℂ), O(2))`-module: a rotation acts on the weight vector
`v_ℓ` by `z(g) ^ ℓ` and a reflection `g` by `v_ℓ ↦ z(g) ^ (-ℓ) v_{-ℓ}`, that is
`g • v_ℓ = z(g) ^ (ε ℓ) v_{ε ℓ}` with `ε = det g = ±1`. For the rotation `r_θ = exp(θJ)`,
`z(r_θ) = e^{iθ}`, so `r_θ` acts on `v_ℓ` by `e^{iℓθ}`, matching the derivative
`TauCeti.lie_gl2RotationGenerator_weightVector`; `A` acts by `TauCeti.reflection`. The action is
covariant: conjugation by a rotation multiplies the `X_c`- and `Y_c`-coordinates of a matrix by
`z(g) ^ 2` and `z(g) ^ (-2)`, and conjugation by `A` exchanges them
(`TauCeti.reflection_lie`).

The Lie submodules `TauCeti.CompactWeightModule.weightLieSubmodule k μ S` with `-S = S` are
`O(2)`-stable, so they are `(𝔤𝔩₂(ℂ), O(2))`-modules; this applies to the discrete series
`D_k(μ)`, whose weights `|ℓ| ≥ k`, `ℓ ≡ k mod 2` form a symmetric set.

## Main definitions

* `TauCeti.orthogonalPhase g`: the phase `z(g) = g₀₀ - i g₁₀` of `g ∈ O(2)`.
* `TauCeti.orthogonalSign g`: `det g = ±1`, as an integer.
* `TauCeti.orthogonalAd`: the conjugation action of `O(2)` on `𝔤𝔩₂(ℂ)`.
* `TauCeti.CompactWeightModule.orthogonalRep k μ`: the action of `O(2)` on the compact weights.
* `TauCeti.CompactWeightModule.gkModule k μ`: the `(𝔤𝔩₂(ℂ), O(2))`-module of all compact weights.
* `TauCeti.CompactWeightModule.weightGKSubmodule k μ S`: the `(𝔤𝔩₂(ℂ), O(2))`-submodule of the
  vectors supported on a symmetric set `S`.

## Main results

* `TauCeti.orthogonalPhase_mul`: `z(gh) = z(g) z(h) ^ (det g)`.
* `TauCeti.CompactWeightModule.orthogonalRep_weightVector`: `g • v_ℓ = z(g) ^ (ε ℓ) v_{ε ℓ}`.
* `TauCeti.CompactWeightModule.orthogonalRep_lie`: covariance,
  `g • ⁅M, v⁆ = ⁅g M g⁻¹, g • v⁆`.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
* W. Casselman, *Representations of SL₂(ℝ)*, lecture notes, §§2, 5–6, pp. 9–11, 17–20.
-/

public section

noncomputable section

open Complex Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-! ### Elements of `O(2)` -/

/-- The complex matrix of an element of `O(2)`. -/
def orthogonalComplexMatrix (g : orthogonalGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ofRealHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) ℝ)

/-- The entries of the complex matrix of `g ∈ O(2)`. -/
@[simp]
theorem orthogonalComplexMatrix_apply (g : orthogonalGroup (Fin 2) ℝ) (i j : Fin 2) :
    orthogonalComplexMatrix g i j = ((g : Matrix (Fin 2) (Fin 2) ℝ) i j : ℂ) :=
  (rfl)

/-- The complex matrix of a product is the product of the complex matrices. -/
theorem orthogonalComplexMatrix_mul (g h : orthogonalGroup (Fin 2) ℝ) :
    orthogonalComplexMatrix (g * h) = orthogonalComplexMatrix g * orthogonalComplexMatrix h := by
  simp only [orthogonalComplexMatrix, Submonoid.coe_mul, map_mul]

/-- The complex matrix of the identity is the identity. -/
@[simp]
theorem orthogonalComplexMatrix_one : orthogonalComplexMatrix 1 = 1 := by
  simp only [orthogonalComplexMatrix, OneMemClass.coe_one, map_one]

/-- The transpose of the complex matrix of `g ∈ O(2)` is its inverse. -/
theorem transpose_orthogonalComplexMatrix_mul (g : orthogonalGroup (Fin 2) ℝ) :
    (orthogonalComplexMatrix g)ᵀ * orthogonalComplexMatrix g = 1 := by
  have h := (mem_orthogonalGroup_iff' (Fin 2) ℝ).1 g.property
  have ht : (orthogonalComplexMatrix g)ᵀ =
      ofRealHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by
    rw [orthogonalComplexMatrix, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, transpose_map]
  rw [ht, orthogonalComplexMatrix, ← map_mul, h, map_one]

/-- The orthogonality relations of the entries of `g ∈ O(2)`: the first column is a unit vector
orthogonal to the second. -/
private theorem orthogonalGroup_relations (g : orthogonalGroup (Fin 2) ℝ) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 +
        (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0 := by
  have h := (mem_orthogonalGroup_iff' (Fin 2) ℝ).1 g.property
  have h₀₀ := congrFun₂ h 0 0
  have h₀₁ := congrFun₂ h 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, transpose_apply, one_apply_eq,
    one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h₀₀ h₀₁
  exact ⟨by linear_combination h₀₀, h₀₁⟩

/-- The first column of `g ∈ O(2)` is a unit vector. -/
theorem orthogonalGroup_sq_add_sq (g : orthogonalGroup (Fin 2) ℝ) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 = 1 :=
  (orthogonalGroup_relations g).1

/-- A rotation `g ∈ O(2)`, `det g = 1`, is `!![a, -b; b, a]`. -/
theorem orthogonalGroup_eq_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
  obtain ⟨h₀, h₁⟩ := orthogonalGroup_relations g
  rw [det_fin_two] at hg
  set a := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set c := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set d := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  exact ⟨by linear_combination b * h₁ + a * hg - d * h₀,
    by linear_combination a * h₁ - b * hg - c * h₀⟩

/-- A reflection `g ∈ O(2)`, `det g = -1`, is `!![a, b; b, -a]`. -/
theorem orthogonalGroup_eq_of_det_eq_neg_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = -(g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
  obtain ⟨h₀, h₁⟩ := orthogonalGroup_relations g
  rw [det_fin_two] at hg
  set a := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set c := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set d := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  exact ⟨by linear_combination b * h₁ + a * hg - d * h₀,
    by linear_combination a * h₁ - b * hg - c * h₀⟩

/-- The **phase** `z(g) = g₀₀ - i g₁₀` of `g ∈ O(2)`: a rotation `!![a, -b; b, a]` has phase
`a - i b`, so the rotation `r_θ = exp(θJ)` has phase `e^{iθ}`; a reflection `r_θ A` has the phase
of `r_θ`. -/
def orthogonalPhase (g : orthogonalGroup (Fin 2) ℝ) : ℂ :=
  ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) - I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ)

/-- The phase in matrix entries. -/
theorem orthogonalPhase_def (g : orthogonalGroup (Fin 2) ℝ) :
    orthogonalPhase g =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) - I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) :=
  (rfl)

/-- The inverse of the phase is `g₀₀ + i g₁₀`. -/
theorem orthogonalPhase_mul_conj (g : orthogonalGroup (Fin 2) ℝ) :
    orthogonalPhase g *
      (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ)) =
      1 := by
  have h := congrArg (fun x : ℝ ↦ (x : ℂ)) (orthogonalGroup_sq_add_sq g)
  push_cast at h
  rw [orthogonalPhase_def]
  linear_combination h - ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) ^ 2 * I_sq

/-- The phase is nonzero. -/
theorem orthogonalPhase_ne_zero (g : orthogonalGroup (Fin 2) ℝ) : orthogonalPhase g ≠ 0 :=
  left_ne_zero_of_mul_eq_one (orthogonalPhase_mul_conj g)

/-- The inverse of the phase is `g₀₀ + i g₁₀`. -/
theorem inv_orthogonalPhase (g : orthogonalGroup (Fin 2) ℝ) :
    (orthogonalPhase g)⁻¹ =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) :=
  inv_eq_of_mul_eq_one_right (orthogonalPhase_mul_conj g)

/-- The **sign** `det g = ±1` of `g ∈ O(2)`, as an integer: `1` for a rotation, `-1` for a
reflection. -/
def orthogonalSign (g : orthogonalGroup (Fin 2) ℝ) : ℤ :=
  if (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 then 1 else -1

/-- The sign of a rotation is `1`. -/
theorem orthogonalSign_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) : orthogonalSign g = 1 := by
  simp [orthogonalSign, hg]

/-- The sign of a reflection is `-1`. -/
theorem orthogonalSign_of_det_eq_neg_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1) : orthogonalSign g = -1 := by
  simp [orthogonalSign, hg]
  norm_num

/-- The sign is the determinant. -/
theorem orthogonalSign_eq_det (g : orthogonalGroup (Fin 2) ℝ) :
    (orthogonalSign g : ℝ) = (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup g.property with hg | hg
  · rw [orthogonalSign_of_det_eq_one hg, hg, Int.cast_one]
  · rw [orthogonalSign_of_det_eq_neg_one hg, hg, Int.cast_neg, Int.cast_one]

/-- The sign squares to `1`. -/
theorem orthogonalSign_mul_self (g : orthogonalGroup (Fin 2) ℝ) :
    orthogonalSign g * orthogonalSign g = 1 := by
  unfold orthogonalSign
  split_ifs <;> norm_num

/-- The sign is multiplicative. -/
theorem orthogonalSign_mul (g h : orthogonalGroup (Fin 2) ℝ) :
    orthogonalSign (g * h) = orthogonalSign g * orthogonalSign h := by
  have : ((orthogonalSign (g * h) : ℤ) : ℝ) = ((orthogonalSign g * orthogonalSign h : ℤ) : ℝ) := by
    rw [Int.cast_mul, orthogonalSign_eq_det, orthogonalSign_eq_det, orthogonalSign_eq_det,
      Submonoid.coe_mul, det_mul]
  exact_mod_cast this

/-- The sign of the identity is `1`. -/
@[simp]
theorem orthogonalSign_one : orthogonalSign 1 = 1 :=
  orthogonalSign_of_det_eq_one (by simp)

/-- **The phase of a product**: `z(gh) = z(g) z(h) ^ (det g)`. Composing with a reflection
conjugates the phase of the second factor. -/
theorem orthogonalPhase_mul (g h : orthogonalGroup (Fin 2) ℝ) :
    orthogonalPhase (g * h) = orthogonalPhase g * orthogonalPhase h ^ orthogonalSign g := by
  have hgh : ∀ i, ((g * h : orthogonalGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i 0 =
      (g : Matrix (Fin 2) (Fin 2) ℝ) i 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) ℝ) i 1 * (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := fun i ↦ by
    simp [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup g.property with hg | hg
  · obtain ⟨h₁, h₂⟩ := orthogonalGroup_eq_of_det_eq_one hg
    rw [orthogonalSign_of_det_eq_one hg, zpow_one, orthogonalPhase_def, orthogonalPhase_def,
      orthogonalPhase_def, hgh, hgh, h₁, h₂]
    push_cast
    linear_combination -((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 :
      ℂ) * I_sq
  · obtain ⟨h₁, h₂⟩ := orthogonalGroup_eq_of_det_eq_neg_one hg
    rw [orthogonalSign_of_det_eq_neg_one hg, _root_.zpow_neg_one, inv_orthogonalPhase,
      orthogonalPhase_def, orthogonalPhase_def, hgh, hgh, h₁, h₂]
    push_cast
    linear_combination ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 :
      ℂ) * I_sq

/-! ### The conjugation action of `O(2)` on `𝔤𝔩₂(ℂ)` -/

/-- The conjugation action `Ad g M = g M g⁻¹ = g M gᵀ` of `O(2)` on `𝔤𝔩₂(ℂ)`. -/
def orthogonalAd : Representation ℂ (orthogonalGroup (Fin 2) ℝ) (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun g := LinearMap.mulLeft ℂ (orthogonalComplexMatrix g) ∘ₗ
    LinearMap.mulRight ℂ (orthogonalComplexMatrix g)ᵀ
  map_one' := by ext; simp
  map_mul' g h := by
    ext M
    simp [orthogonalComplexMatrix_mul, transpose_mul, Matrix.mul_assoc]

/-- `Ad g M = g M gᵀ`. -/
theorem orthogonalAd_apply (g : orthogonalGroup (Fin 2) ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    orthogonalAd g M = orthogonalComplexMatrix g * M * (orthogonalComplexMatrix g)ᵀ := by
  simp [orthogonalAd, Matrix.mul_assoc]

/-- `O(2)` acts on `𝔤𝔩₂(ℂ)` by Lie algebra automorphisms. -/
instance instIsLieActionOrthogonalAd : orthogonalAd.IsLieAction where
  map_lie g M N := by
    simp only [orthogonalAd_apply, Ring.lie_def]
    have h := transpose_orthogonalComplexMatrix_mul g
    simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
    rw [← Matrix.mul_assoc (orthogonalComplexMatrix g)ᵀ, h, Matrix.one_mul,
      ← Matrix.mul_assoc (orthogonalComplexMatrix g)ᵀ, h, Matrix.one_mul]

/-- `Ad g M` for a rotation `g = !![a, -b; b, a]`. -/
private theorem orthogonalAd_eq_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    orthogonalAd g M =
      !![((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ), -((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ);
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)] * M *
        !![((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ);
          -((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)] := by
  obtain ⟨h₁, h₂⟩ := orthogonalGroup_eq_of_det_eq_one hg
  rw [orthogonalAd_apply]
  congr 2 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [h₁, h₂]

/-- `Ad g M` for a reflection `g = !![a, b; b, -a]`. -/
private theorem orthogonalAd_eq_of_det_eq_neg_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    orthogonalAd g M =
      !![((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ);
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ), -((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)] * M *
        !![((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ);
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ), -((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)] := by
  obtain ⟨h₁, h₂⟩ := orthogonalGroup_eq_of_det_eq_neg_one hg
  rw [orthogonalAd_apply]
  congr 2 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [h₁, h₂]

/-- The first column of `g ∈ O(2)` is a unit vector, in `ℂ`. -/
private theorem orthogonalGroup_sq_add_sq_complex (g : orthogonalGroup (Fin 2) ℝ) :
    ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) ^ 2 =
      1 := by
  exact_mod_cast orthogonalGroup_sq_add_sq g

/-- Conjugation by a rotation fixes the `H_c`-coordinate. -/
theorem compactCoordH_orthogonalAd_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordH (orthogonalAd g M) = compactCoordH M := by
  have h₀ := orthogonalGroup_sq_add_sq_complex g
  have := I_sq
  rw [orthogonalAd_eq_of_det_eq_one hg, Matrix.eta_fin_two M]
  simp only [Matrix.mul_fin_two, compactCoordH_apply, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  grind

/-- Conjugation by a rotation multiplies the `X_c`-coordinate by `z(g) ^ 2`. -/
theorem compactCoordX_orthogonalAd_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordX (orthogonalAd g M) = orthogonalPhase g ^ 2 * compactCoordX M := by
  have := I_sq
  rw [orthogonalAd_eq_of_det_eq_one hg, Matrix.eta_fin_two M, orthogonalPhase_def]
  simp only [Matrix.mul_fin_two, compactCoordX_apply, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  grind

/-- Conjugation by a rotation multiplies the `Y_c`-coordinate by `z(g) ^ (-2)`. -/
theorem compactCoordY_orthogonalAd_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordY (orthogonalAd g M) = (orthogonalPhase g)⁻¹ ^ 2 * compactCoordY M := by
  have := I_sq
  rw [orthogonalAd_eq_of_det_eq_one hg, Matrix.eta_fin_two M, inv_orthogonalPhase]
  simp only [Matrix.mul_fin_two, compactCoordY_apply, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  grind

/-- Conjugation by a rotation fixes the coordinate along the identity. -/
theorem compactCoordOne_orthogonalAd_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordOne (orthogonalAd g M) = compactCoordOne M := by
  have h₀ := orthogonalGroup_sq_add_sq_complex g
  rw [orthogonalAd_eq_of_det_eq_one hg, Matrix.eta_fin_two M]
  simp only [Matrix.mul_fin_two, compactCoordOne_apply, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  grind

/-- Conjugation by a reflection negates the `H_c`-coordinate. -/
theorem compactCoordH_orthogonalAd_of_det_eq_neg_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordH (orthogonalAd g M) = -compactCoordH M := by
  have h₀ := orthogonalGroup_sq_add_sq_complex g
  have := I_sq
  rw [orthogonalAd_eq_of_det_eq_neg_one hg, Matrix.eta_fin_two M]
  simp only [Matrix.mul_fin_two, compactCoordH_apply, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  grind

/-- Conjugation by a reflection moves the `Y_c`-coordinate to `X_c`, times `z(g) ^ 2`. -/
theorem compactCoordX_orthogonalAd_of_det_eq_neg_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordX (orthogonalAd g M) = orthogonalPhase g ^ 2 * compactCoordY M := by
  have := I_sq
  rw [orthogonalAd_eq_of_det_eq_neg_one hg, Matrix.eta_fin_two M, orthogonalPhase_def]
  simp only [Matrix.mul_fin_two, compactCoordX_apply, compactCoordY_apply, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  grind

/-- Conjugation by a reflection moves the `X_c`-coordinate to `Y_c`, times `z(g) ^ (-2)`. -/
theorem compactCoordY_orthogonalAd_of_det_eq_neg_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordY (orthogonalAd g M) = (orthogonalPhase g)⁻¹ ^ 2 * compactCoordX M := by
  have := I_sq
  rw [orthogonalAd_eq_of_det_eq_neg_one hg, Matrix.eta_fin_two M, inv_orthogonalPhase]
  simp only [Matrix.mul_fin_two, compactCoordX_apply, compactCoordY_apply, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  grind

/-- Conjugation by a reflection fixes the coordinate along the identity. -/
theorem compactCoordOne_orthogonalAd_of_det_eq_neg_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordOne (orthogonalAd g M) = compactCoordOne M := by
  have h₀ := orthogonalGroup_sq_add_sq_complex g
  rw [orthogonalAd_eq_of_det_eq_neg_one hg, Matrix.eta_fin_two M]
  simp only [Matrix.mul_fin_two, compactCoordOne_apply, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  grind

/-! ### The action of `O(2)` on the compact weights -/

namespace CompactWeightModule

variable {k μ : ℂ}

/-- A linear map built on the weight basis sends `v_ℓ` to the prescribed vector. -/
private theorem constr_weightVector (f : ℤ → CompactWeightModule k μ) (ℓ : ℤ) :
    (weightBasis k μ).constr ℂ f (weightVector k μ ℓ) = f ℓ := by
  rw [← weightBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

variable (k μ) in
/-- **The action of `O(2)` on the compact weights**: `g ∈ O(2)` sends `v_ℓ` to
`z(g) ^ (ε ℓ) v_{ε ℓ}`, where `z(g)` is the phase and `ε = det g = ±1`. A rotation `r_θ` acts on
`v_ℓ` by `e^{iℓθ}`, and `A = diag(1, -1)` acts by the reflection `v_ℓ ↦ v_{-ℓ}`. -/
def orthogonalRep : Representation ℂ (orthogonalGroup (Fin 2) ℝ) (CompactWeightModule k μ) where
  toFun g := (weightBasis k μ).constr ℂ fun ℓ ↦
    (orthogonalPhase g ^ (orthogonalSign g * ℓ)) • weightVector k μ (orthogonalSign g * ℓ)
  map_one' := (weightBasis k μ).ext fun ℓ ↦ by
    simp [constr_weightVector, orthogonalPhase_def]
  map_mul' g h := (weightBasis k μ).ext fun ℓ ↦ by
    simp only [weightBasis_apply, Module.End.mul_eq_comp, LinearMap.comp_apply,
      constr_weightVector, map_smul, smul_smul, orthogonalSign_mul, orthogonalPhase_mul]
    rw [mul_zpow, ← _root_.zpow_mul, mul_assoc (orthogonalSign g) (orthogonalSign h) ℓ, mul_comm]
    congr 2
    rw [← mul_assoc (orthogonalSign g) (orthogonalSign g), orthogonalSign_mul_self, one_mul]

/-- `g ∈ O(2)` sends `v_ℓ` to `z(g) ^ (ε ℓ) v_{ε ℓ}`, `ε = det g`. -/
@[simp]
theorem orthogonalRep_weightVector (g : orthogonalGroup (Fin 2) ℝ) (ℓ : ℤ) :
    orthogonalRep k μ g (weightVector k μ ℓ) =
      (orthogonalPhase g ^ (orthogonalSign g * ℓ)) • weightVector k μ (orthogonalSign g * ℓ) :=
  constr_weightVector _ ℓ

/-- `ε ℓ` is `ℓ` or `-ℓ`. -/
private theorem orthogonalSign_mul_eq (g : orthogonalGroup (Fin 2) ℝ) (ℓ : ℤ) :
    orthogonalSign g * ℓ = ℓ ∨ orthogonalSign g * ℓ = -ℓ := by
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup g.property with hg | hg
  · simp [orthogonalSign_of_det_eq_one hg]
  · simp [orthogonalSign_of_det_eq_neg_one hg]

/-- **Covariance of the action of `O(2)`**: `g • ⁅M, v⁆ = ⁅g M g⁻¹, g • v⁆`. -/
theorem orthogonalRep_lie (g : orthogonalGroup (Fin 2) ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (v : CompactWeightModule k μ) :
    orthogonalRep k μ g ⁅M, v⁆ = ⁅orthogonalAd g M, orthogonalRep k μ g v⁆ := by
  have hz := orthogonalPhase_ne_zero g
  have h : orthogonalRep k μ g ∘ₗ LieModule.toEnd ℂ _ _ M =
      LieModule.toEnd ℂ _ _ (orthogonalAd g M) ∘ₗ orthogonalRep k μ g := by
    refine (weightBasis k μ).ext fun ℓ ↦ ?_
    simp only [weightBasis_apply, LinearMap.coe_comp, Function.comp_apply,
      LieModule.toEnd_apply_apply, lie_weightVector, map_add, map_smul,
      orthogonalRep_weightVector, smul_add, smul_smul]
    rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup g.property with hg | hg
    · simp only [orthogonalSign_of_det_eq_one hg, one_mul,
        compactCoordH_orthogonalAd_of_det_eq_one hg, compactCoordX_orthogonalAd_of_det_eq_one hg,
        compactCoordY_orthogonalAd_of_det_eq_one hg,
        compactCoordOne_orthogonalAd_of_det_eq_one hg]
      rw [zpow_add₀ hz, zpow_sub₀ hz, zpow_two, div_eq_mul_inv]
      module
    · simp only [orthogonalSign_of_det_eq_neg_one hg, neg_one_mul,
        compactCoordH_orthogonalAd_of_det_eq_neg_one hg,
        compactCoordX_orthogonalAd_of_det_eq_neg_one hg,
        compactCoordY_orthogonalAd_of_det_eq_neg_one hg,
        compactCoordOne_orthogonalAd_of_det_eq_neg_one hg]
      rw [show -(ℓ + 2) = -ℓ - 2 by ring, show -(ℓ - 2) = -ℓ + 2 by ring, zpow_sub₀ hz,
        zpow_add₀ hz, zpow_two, div_eq_mul_inv]
      push_cast
      module
  simpa using congr($h v)

variable (k μ) in
/-- **The `(𝔤𝔩₂(ℂ), O(2))`-module of all compact weights**: `TauCeti.CompactWeightModule k μ` with
the action `TauCeti.CompactWeightModule.orthogonalRep k μ` of `O(2)`, covariant for the
conjugation action `TauCeti.orthogonalAd`. Every vector is `O(2)`-finite: the orbit of `v_ℓ` lies
in the span of `v_ℓ` and `v_{-ℓ}`. -/
def gkModule : GKModule orthogonalAd (CompactWeightModule k μ) where
  ρ := orthogonalRep k μ
  map_lie := orthogonalRep_lie
  isGFinite v := by
    have hfin : ∀ ℓ, (orthogonalRep k μ).IsGFinite (weightVector k μ ℓ) := fun ℓ ↦ by
      have := FiniteDimensional.span_of_finite ℂ
        (Set.toFinite {weightVector k μ ℓ, weightVector k μ (-ℓ)})
      refine Representation.IsGFinite.of_forall_apply_mem
        (W := Submodule.span ℂ {weightVector k μ ℓ, weightVector k μ (-ℓ)}) fun g ↦ ?_
      rw [orthogonalRep_weightVector]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rcases orthogonalSign_mul_eq g ℓ with h | h <;> simp [h]
    have htop : ⊤ ≤ (orthogonalRep k μ).gFiniteSubmodule := by
      rw [← (weightBasis k μ).span_eq, Submodule.span_le]
      rintro _ ⟨ℓ, rfl⟩
      exact (Representation.mem_gFiniteSubmodule _).2 (by simpa using hfin ℓ)
    exact (Representation.mem_gFiniteSubmodule _).1 (htop Submodule.mem_top)

/-- The action of `O(2)` in `TauCeti.CompactWeightModule.gkModule`. -/
@[simp]
theorem gkModule_ρ : (gkModule k μ).ρ = orthogonalRep k μ :=
  (rfl)

/-- `O(2)` preserves the vectors supported on a symmetric set of weights `S`, `-S = S`. -/
theorem equivFinsupp_orthogonalRep_mem_supported {S : Set ℤ} (hS : ∀ ℓ, -ℓ ∈ S ↔ ℓ ∈ S)
    (g : orthogonalGroup (Fin 2) ℝ) {v : CompactWeightModule k μ}
    (hv : equivFinsupp k μ v ∈ Finsupp.supported ℂ ℂ S) :
    equivFinsupp k μ (orthogonalRep k μ g v) ∈ Finsupp.supported ℂ ℂ S := by
  have hc : ∀ ℓ ∈ S, orthogonalSign g * ℓ ∉ S → orthogonalPhase g ^ (orthogonalSign g * ℓ) = 0 :=
    fun ℓ hℓ hℓ' ↦ by
      rcases orthogonalSign_mul_eq g ℓ with h | h <;> rw [h] at hℓ'
      · exact absurd hℓ hℓ'
      · exact absurd ((hS ℓ).2 hℓ) hℓ'
  have key := Finsupp.map_mem_supported_of_map_single_eq_smul_single ℂ
    ((equivFinsupp k μ).toLinearMap ∘ₗ orthogonalRep k μ g ∘ₗ (equivFinsupp k μ).symm.toLinearMap)
    (fun ℓ ↦ orthogonalPhase g ^ (orthogonalSign g * ℓ)) (fun ℓ ↦ orthogonalSign g * ℓ)
    (fun ℓ ↦ by
      rw [← equivFinsupp_weightVector (k := k) (μ := μ),
        ← equivFinsupp_weightVector (k := k) (μ := μ)]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply, orthogonalRep_weightVector, map_smul]) hc hv
  simpa using key

variable (k μ) in
/-- The `(𝔤𝔩₂(ℂ), O(2))`-submodule of the vectors supported on a set of weights `S` with
`-S = S` that `X_c` and `Y_c` leave only with coefficient zero: the Lie submodule
`TauCeti.CompactWeightModule.weightLieSubmodule k μ S` is `O(2)`-stable. -/
def weightGKSubmodule (S : Set ℤ) (hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0)
    (hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0) (hS : ∀ ℓ, -ℓ ∈ S ↔ ℓ ∈ S) :
    GKSubmodule (gkModule k μ) where
  toLieSubmodule := weightLieSubmodule k μ S hX hY
  apply_mem g _ hv := mem_weightLieSubmodule.2
    (equivFinsupp_orthogonalRep_mem_supported hS g (mem_weightLieSubmodule.1 hv))

/-- The underlying Lie submodule of `TauCeti.CompactWeightModule.weightGKSubmodule`. -/
@[simp]
theorem toLieSubmodule_weightGKSubmodule (S : Set ℤ) (hX : ∀ ℓ ∈ S, ℓ + 2 ∉ S → k + ℓ = 0)
    (hY : ∀ ℓ ∈ S, ℓ - 2 ∉ S → k - ℓ = 0) (hS : ∀ ℓ, -ℓ ∈ S ↔ ℓ ∈ S) :
    (weightGKSubmodule k μ S hX hY hS).toLieSubmodule = weightLieSubmodule k μ S hX hY :=
  (rfl)

end CompactWeightModule

end TauCeti
