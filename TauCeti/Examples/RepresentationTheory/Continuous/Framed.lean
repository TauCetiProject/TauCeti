/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Framed

/-!
# Examples: framed continuous representations

* In rank zero there is exactly one framed representation, and its carrier is zero.
* In rank one a framed representation is a character: `ofFramed ρ ≅ ofCharacter χ` for
  `χ = det ∘ ρ`.
* Changing coefficients along the identity changes nothing.
* `(1 a; 0 1)` and `(1 ℓa; 0 1)` with `a ≠ 0` are conjugate under `GL₂(ℚ_ℓ)` but not under
  `GL₂(ℤ_ℓ)`, so by `TauCeti.ContinuousRep.nonempty_iso_ofFramed_iff` isomorphism of framed
  representations over `ℤ_ℓ` is finer than conjugacy over the fraction field. The representations
  of `ℤ` they generate are compared in `TauCeti.ContinuousRep.ReductionCheck.isEmpty_iso_unipotent`.
-/

open TauCeti ContinuousRep

variable {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A]

-- In rank zero there is exactly one framed representation.
example : Unique (Γ →ₜ* GL (Fin 0) A) where
  default := 1
  uniq _ := ContinuousMonoidHom.ext fun _ => Units.ext (Subsingleton.elim _ _)

-- The framed representation of rank zero lives on the zero module.
example : Subsingleton (Fin 0 → A) :=
  inferInstance

-- In rank one a framed representation is the character line of its determinant.
example (ρ : Γ →ₜ* GL (Fin 1) A) (χ : Γ →ₜ* Aˣ)
    (hχ : ∀ g, (χ g : A) = Matrix.det (ρ g : Matrix (Fin 1) (Fin 1) A)) :
    Nonempty (Iso (ofFramed ρ) (ofCharacter χ)) :=
  ⟨Iso.ofEquiv (.mk (LinearEquiv.funUnique (Fin 1) A A) fun g => LinearMap.ext fun v => by
    simp [hχ, Matrix.mulVec, dotProduct, Matrix.det_unique])⟩

-- Coefficient change along the identity changes nothing.
example (ρ : Γ →ₜ* GL (Fin 2) A) : framedMap (RingHom.id A) continuous_id ρ = ρ :=
  framedMap_id ρ

-- `(1 a; 0 1)` and `(1 ℓa; 0 1)` with `a ≠ 0` are not conjugate under `GL₂(ℤ_ℓ)`: a conjugating
-- matrix `P` would be upper triangular with `P₀₀ = ℓ P₁₁`, so `det P = ℓ P₁₁²` is not a unit.
example (ℓ : ℕ) [Fact ℓ.Prime] {a : ℤ_[ℓ]} (ha : a ≠ 0) :
    ¬ ∃ P : GL (Fin 2) ℤ_[ℓ], (P : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) * !![1, a; 0, 1] =
      !![1, (ℓ : ℤ_[ℓ]) * a; 0, 1] * P := by
  rintro ⟨P, hP⟩
  have hℓ : (ℓ : ℤ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have hdet : IsUnit (P : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).det :=
    (Matrix.GeneralLinearGroup.det P).isUnit
  rw [(P : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).eta_fin_two, Matrix.mul_fin_two,
    Matrix.mul_fin_two] at hP
  have h00 := congrFun (congrFun hP 0) 0
  have h01 := congrFun (congrFun hP 0) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01
  have h10 : (P : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) 1 0 = 0 := by
    have : (ℓ : ℤ_[ℓ]) * a * (P : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) 1 0 = 0 := by
      linear_combination -h00
    simpa [hℓ, ha] using this
  have h11 : (P : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) 0 0 =
      ℓ * (P : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) 1 1 := by
    refine mul_right_cancel₀ ha ?_
    linear_combination h01
  rw [Matrix.det_fin_two, h10, h11, mul_zero, sub_zero, mul_assoc] at hdet
  exact PadicInt.p_nonunit (isUnit_of_mul_isUnit_left hdet)

-- Over `ℚ_ℓ` the two matrices are conjugate, by `diag(ℓ, 1)`.
example (ℓ : ℕ) [Fact ℓ.Prime] (a : ℚ_[ℓ]) :
    ∃ P : GL (Fin 2) ℚ_[ℓ], (P : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) * !![1, a; 0, 1] =
      !![1, (ℓ : ℚ_[ℓ]) * a; 0, 1] * P := by
  have hℓ : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ℓ : ℚ_[ℓ]), 0; 0, 1]
    (by simpa [Matrix.det_fin_two] using hℓ), ?_⟩
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
