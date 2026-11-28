/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.MvPolynomial.Basic

/-!
# Products of column determinants under a change of directions

A filled column of height `h` determines a square determinant in variables indexed by
place, row, height and direction. The product over the columns is homogeneous of degree
equal to the number of boxes. Under a linear change of directions, each column contributes the
determinant of its direction change and each box contributes its row scale. The resulting
polynomial identity allows these factors to be extracted from a jet without dividing by them.

The direction change is the one in `New.jet_columnDetProd_subst` of lsernau/grh-lean,
`grh/src/New/Derivatives/Divisibility/Count.lean` at revision `72fead1`. Here the polynomial
identity is stated separately from the jet pairing, over any commutative coefficient algebra.
-/

public section

open Matrix MvPolynomial

namespace TauCeti.ThetaLift

variable {ι Φ ρ : Type*} [Fintype ι] {N : ℕ}

/-- The product of the column determinants of a filling. The columns are indexed by `ι`,
with height `h i`, place `place i`, and row `row i b` in box `b`. Variables are shared by
boxes with the same place, row, height and direction index. -/
noncomputable def columnDetProd (R : Type*) [CommRing R] (h : ι → Fin N) (place : ι → Φ)
    (row : (i : ι) → Fin (h i) → ρ) : MvPolynomial (Φ × ρ × (Σ t : Fin N, Fin t)) R :=
  ∏ i, (Matrix.of fun b k : Fin (h i) ↦ X (place i, row i b, ⟨h i, k⟩)).det

/-- The column determinant product expressed in the entries of the formal direction matrices. -/
theorem columnDetProd_def (R : Type*) [CommRing R] (h : ι → Fin N) (place : ι → Φ)
    (row : (i : ι) → Fin (h i) → ρ) :
    columnDetProd R h place row =
      ∏ i, (Matrix.of fun b k : Fin (h i) ↦ X (place i, row i b, ⟨h i, k⟩)).det := (rfl)

/-- Changing the coefficient ring leaves the formal column determinant product unchanged. -/
@[simp] theorem map_columnDetProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (h : ι → Fin N) (place : ι → Φ) (row : (i : ι) → Fin (h i) → ρ) :
    (columnDetProd R h place row).map f = columnDetProd S h place row := by
  rw [columnDetProd_def, columnDetProd_def, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [RingHom.map_det]
  congr 1
  ext b k
  simp [RingHom.mapMatrix_apply]

/-- Evaluating a column determinant product substitutes the assigned value in each entry. -/
@[simp] theorem aeval_columnDetProd {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (h : ι → Fin N) (place : ι → Φ) (row : (i : ι) → Fin (h i) → ρ)
    (f : Φ × ρ × (Σ t : Fin N, Fin t) → A) :
    aeval f (columnDetProd R h place row) =
      ∏ i, (Matrix.of fun b k : Fin (h i) ↦ f (place i, row i b, ⟨h i, k⟩)).det := by
  rw [columnDetProd_def, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [AlgHom.map_det]
  congr 1
  ext b k
  simp [AlgHom.mapMatrix_apply]

/-- The column determinant product is homogeneous of degree the total number of boxes. -/
theorem isHomogeneous_columnDetProd (R : Type*) [CommRing R] (h : ι → Fin N) (place : ι → Φ)
    (row : (i : ι) → Fin (h i) → ρ) :
    (columnDetProd R h place row).IsHomogeneous (∑ i, (h i : ℕ)) := by
  rw [columnDetProd_def]
  apply IsHomogeneous.prod
  intro i _
  let f : Fin (h i) × Fin (h i) → Φ × ρ × (Σ t : Fin N, Fin t) :=
    fun (b, k) ↦ (place i, row i b, ⟨h i, k⟩)
  have he : rename f (mvPolynomialX (Fin (h i)) (Fin (h i)) R).det =
      (Matrix.of fun b k : Fin (h i) ↦ (X (place i, row i b, ⟨h i, k⟩) :
        MvPolynomial (Φ × ρ × (Σ t : Fin N, Fin t)) R)).det := by
    rw [AlgHom.map_det]
    congr 1
    ext b k
    simp [f, AlgHom.mapMatrix_apply, mvPolynomialX_apply]
  rw [← he]
  simpa only [Fintype.card_fin] using
    (isHomogeneous_det_mvPolynomialX (n := Fin (h i)) (R := R)).rename_isHomogeneous (f := f)

/-- Evaluate each direction variable at a scaled row of `Z` paired with a changed direction.
The direction changes are the matrices `G`, acting on the directions (columns) of `Y` by
right multiplication by `Gᵀ`. The determinant of `G` occurs once per column of the filling,
and its row scale `c` occurs once per box. No determinant or row scale needs to be invertible. -/
theorem aeval_columnDetProd_direction {R A α : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype α] (h : ι → Fin N) (place : ι → Φ) (row : (i : ι) → Fin (h i) → ρ)
    (Z : Φ → Matrix ρ α A) (Y : Φ → (t : Fin N) → Matrix α (Fin t) A)
    (G : Φ → (t : Fin N) → Matrix (Fin t) (Fin t) A) (c : Φ → Fin N → ρ → A) :
    aeval (fun (x : Φ × ρ × (Σ t : Fin N, Fin t)) ↦
      c x.1 x.2.2.1 x.2.1 * (Z x.1 * Y x.1 x.2.2.1 * (G x.1 x.2.2.1)ᵀ) x.2.1 x.2.2.2)
      (columnDetProd R h place row) =
      (∏ i, (G (place i) (h i)).det * ∏ b, c (place i) (h i) (row i b)) *
        ∏ i, (((Z (place i)).submatrix (row i) id) * Y (place i) (h i)).det := by
  rw [aeval_columnDetProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  -- Restrict the rows of the full matrix product before taking its determinant.
  let M := (Z (place i) * Y (place i) (h i) * (G (place i) (h i))ᵀ).submatrix (row i) id
  have hm : M = (Z (place i)).submatrix (row i) id * Y (place i) (h i) * (G (place i) (h i))ᵀ := by
    simp only [M, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_id_id]
  dsimp only [Prod.fst, Prod.snd, Sigma.fst, Sigma.snd]
  calc
    _ = (∏ b, c (place i) (h i) (row i b)) * M.det :=
      Matrix.det_mul_column (fun b ↦ c (place i) (h i) (row i b)) M
    _ = _ := by rw [hm, det_mul, det_transpose]; ac_rfl

end TauCeti.ThetaLift
