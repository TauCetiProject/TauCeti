/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Twisted.Basic

/-!
# The determinant product of a system of linear forms

For a system of square coefficient matrices `L v` indexed by the places of a number field,
`TauCeti.deltaL L` is the product of the degree-normalized absolute values of their determinants.
This is the normalization factor in the product bounds for successive minima of twisted heights.
It is distinct from the height of the tuple of all minors of the forms.

For independent local systems taking finitely many values, the product has finite multiplicative
support and is positive. A common invertible change of variables leaves it unchanged by the
product formula. Permuting the forms, even separately at each place, also leaves it unchanged.
Coordinate forms have determinant product one, including in dimension zero.

The finite-modification formula distinguishes local and global changes: replacing coordinate
forms at just one place contributes the absolute value of that determinant at that place,
whereas the same invertible matrix used at every place has determinant product one.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §2.2, (2.11), and Lemma 7.3.
-/

public noncomputable section

open Function Matrix TauCeti.GlobalNumberFields

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product `Δ_L = ∏ᶠ v, |det (L v)|_v`, using degree-normalized absolute values.
For independent systems with finite range this is a genuine finite product. On arbitrary data
it uses the `finprod` convention, giving one when the multiplicative support is infinite. -/
def deltaL (L : Place K → Matrix ι ι K) : ℝ :=
  ∏ᶠ v, normAbs v (L v).det

variable {L : Place K → Matrix ι ι K}

theorem deltaL_def (L : Place K → Matrix ι ι K) :
    deltaL L = ∏ᶠ v, normAbs v (L v).det := (rfl)

/-- The determinant factors have finite multiplicative support when the local systems are
independent and only finitely many distinct systems occur. -/
theorem hasFiniteMulSupport_normAbs_det (hL : ∀ v, IsUnit (L v))
    (hLfin : (Set.range L).Finite) :
    HasFiniteMulSupport fun v ↦ normAbs v (L v).det := by
  have h (A : Matrix ι ι K) (hA : A ∈ Set.range L) :
      HasFiniteMulSupport fun v : Place K ↦ normAbs v A.det := by
    obtain ⟨v, rfl⟩ := hA
    exact hasFiniteMulSupport_normAbs ((L v).isUnit_iff_isUnit_det.mp (hL v)).ne_zero
  refine (hLfin.biUnion h).subset fun v hv ↦ ?_
  exact Set.mem_biUnion (Set.mem_range_self v) hv

/-- The determinant product is nonnegative, even without finite-support assumptions. -/
theorem deltaL_nonneg (L : Place K → Matrix ι ι K) : 0 ≤ deltaL L :=
  finprod_nonneg fun v ↦ normAbs_nonneg v _

/-- Locally independent forms have positive determinant product. Finiteness of the range is
not needed for this statement about the total `finprod` definition. -/
theorem deltaL_pos (hL : ∀ v, IsUnit (L v)) : 0 < deltaL L := by
  rw [deltaL_def]
  by_cases hfin : HasFiniteMulSupport fun v ↦ normAbs v (L v).det
  · rw [finprod_eq_prod _ hfin]
    exact Finset.prod_pos fun v _ ↦
      normAbs_pos v ((L v).isUnit_iff_isUnit_det.mp (hL v)).ne_zero
  · rw [finprod_of_not_hasFiniteMulSupport hfin]
    exact one_pos

/-- A single invertible system used at every place has determinant product one. -/
@[simp]
theorem deltaL_const (A : Matrix ι ι K) (hA : IsUnit A) :
    deltaL (fun _ : Place K ↦ A) = 1 :=
  finprod_normAbs_eq_one (A.isUnit_iff_isUnit_det.mp hA).ne_zero

/-- A common invertible change of variables leaves the determinant product unchanged.
There are no independence or finite-range assumptions on `L`. -/
@[simp]
theorem deltaL_mul (L : Place K → Matrix ι ι K) {A : Matrix ι ι K} (hA : IsUnit A) :
    deltaL (fun v ↦ L v * A) = deltaL L := by
  simp only [deltaL_def, det_mul, map_mul]
  simpa only [mul_comm] using
    finprod_mul_eq_right_of_finprod_eq_one
      (g := fun v ↦ normAbs v (L v).det)
      (hasFiniteMulSupport_normAbs (A.isUnit_iff_isUnit_det.mp hA).ne_zero)
      (finprod_normAbs_eq_one (A.isUnit_iff_isUnit_det.mp hA).ne_zero)

/-- A common invertible linear combination of the forms leaves their determinant product
unchanged. -/
@[simp]
theorem deltaL_mul_left (L : Place K → Matrix ι ι K) {A : Matrix ι ι K} (hA : IsUnit A) :
    deltaL (fun v ↦ A * L v) = deltaL L := by
  simp only [deltaL_def, det_mul, map_mul]
  exact finprod_mul_eq_right_of_finprod_eq_one
    (hasFiniteMulSupport_normAbs (A.isUnit_iff_isUnit_det.mp hA).ne_zero)
    (finprod_normAbs_eq_one (A.isUnit_iff_isUnit_det.mp hA).ne_zero)

/-- Permuting the local forms independently at every place preserves the determinant product. -/
@[simp]
theorem deltaL_permute (L : Place K → Matrix ι ι K) (σ : Place K → Equiv.Perm ι) :
    deltaL (fun v ↦ (L v).submatrix (σ v) id) = deltaL L := by
  apply finprod_congr
  intro v
  rw [det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (σ v)) with h | h <;> simp [h]

/-- Relabeling the coordinate type and the forms by the same equivalence preserves the
normalization, with no ordering choice on the finite coordinate types. -/
@[simp]
theorem deltaL_submatrix_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Place K → Matrix ι ι K) (e : κ ≃ ι) :
    deltaL (fun v ↦ (L v).submatrix e e) = deltaL L := by
  simp [deltaL_def]

open Classical in
/-- Replacing coordinate forms on a finite set of places contributes exactly the product of
those local determinants. Singular replacement matrices are allowed. -/
theorem deltaL_piecewise_one (s : Finset (Place K)) (A : Place K → Matrix ι ι K) :
    deltaL (s.piecewise A (fun _ ↦ 1)) =
      ∏ v ∈ s, normAbs v (A v).det := by
  classical
  rw [deltaL_def]
  calc
    _ = ∏ v ∈ s, normAbs v
        (s.piecewise A (fun _ ↦ 1) v).det := by
      apply finprod_eq_prod_of_mulSupport_subset
      intro v hv
      by_contra hvs
      apply hv
      dsimp only
      rw [Finset.piecewise_eq_of_notMem _ _ _ hvs, det_one, map_one]
    _ = _ := Finset.prod_congr rfl fun v hv ↦ by rw [Finset.piecewise_eq_of_mem _ _ _ hv]

open Classical in
/-- Changing coordinate forms at one place gives a single local determinant factor, not the
global product formula. -/
@[simp]
theorem deltaL_update_one (v : Place K) (A : Matrix ι ι K) :
    deltaL (Function.update (fun _ ↦ 1) v A) = normAbs v A.det := by
  classical
  simpa only [Finset.piecewise_singleton, Finset.prod_singleton] using
    deltaL_piecewise_one {v} (fun _ ↦ A)

end TauCeti
