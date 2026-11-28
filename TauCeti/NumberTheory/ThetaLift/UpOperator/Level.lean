/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.UpOperator.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel.MarkedColumn

/-!
# Level invariance of the theta-lift operator `Up`

In the basis of the modified lattice, the source level at the level prime fixes the marked
column on reduction. Moving the inverse diagonal factor of `Up` past a level element switches
the column congruence to a row congruence. This permutes the summands of `Up` without changing
their weights. The local statement is the invariance used in `New.Data.upOperator_mem_sourceForm`
in `New/UpperBound/Divisibility/SetupAtLevel.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open Matrix Matrix.GeneralLinearGroup Finset

namespace TauCeti.ThetaLift

variable {k A F R ι V : Type*} [CommRing k] [CommRing A] [CommRing F] [Algebra A F]
  [CommRing R] [Fintype R] [DecidableEq R] [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module k V]

/-- The residue sum in `Up` is fixed by the integral elements whose marked row reduces to the
standard row, when the input is fixed by those whose marked column reduces to the standard
column. Only the column condition on the chosen representatives is needed. -/
theorem sum_upOperator_fixed_of_row_eq (π : Representation k (GL ι F) V)
    (red : A →+* R) (l : ι) (g : (ι → R) → GL ι A) (ψ : R → k) (φ : V)
    (hg : ∀ y, IsUnit (y l) → (map red (g y) : Matrix ι ι R).col l = y)
    (hφ : ∀ a : GL ι A, (map red a : Matrix ι ι R).col l = Pi.single l 1 →
      π (map (algebraMap A F) a) φ = φ)
    {b : GL ι A} (hb : (map red b : Matrix ι ι R).row l = Pi.single l 1) :
    π (map (algebraMap A F) b) (∑ y ∈ univ.filter (fun y : ι → R ↦ IsUnit (y l)),
        ψ (y l) • π (map (algebraMap A F) (g y)) φ) =
      ∑ y ∈ univ.filter (fun y : ι → R ↦ IsUnit (y l)),
        ψ (y l) • π (map (algebraMap A F) (g y)) φ := by
  let B := map red b
  let f := fun y : ι → R ↦ (B : Matrix ι ι R) *ᵥ y
  let finv := fun y : ι → R ↦ (B⁻¹ : GL ι R).val *ᵥ y
  have hcoord (y : ι → R) : f y l = y l := calc
    f y l = B.val.row l ⬝ᵥ y := rfl
    _ = y l := by rw [hb, single_one_dotProduct]
  have hleft (y : ι → R) : finv (f y) = y := by simp [f, finv, mulVec_mulVec]
  have hright (y : ι → R) : f (finv y) = y := by simp [f, finv, mulVec_mulVec]
  have hcoord' (y : ι → R) : finv y l = y l := by rw [← hcoord (finv y), hright]
  simp only [map_sum, map_smul]
  refine Finset.sum_nbij' f finv (fun y hy ↦ ?_) (fun y hy ↦ ?_)
    (fun y _ ↦ hleft y) (fun y _ ↦ hright y) fun y hy ↦ ?_
  · simpa only [mem_filter_univ, hcoord] using hy
  · simpa only [mem_filter_univ, hcoord'] using hy
  have hy' : IsUnit (y l) := (mem_filter.mp hy).2
  have hfy : IsUnit (f y l) := (hcoord y).symm ▸ hy'
  let c := (g (f y))⁻¹ * (b * g y)
  have hc : (map red c : Matrix ι ι R).col l = Pi.single l 1 := by
    apply (mulVec_injective_of_isUnit (map red (g (f y))).isUnit)
    rw [mulVec_single_one, ← col_mul_eq_mulVec_col, ← GeneralLinearGroup.coe_mul, ← map_mul,
      hg (f y) hfy]
    simp only [c, mul_inv_cancel_left, map_mul, GeneralLinearGroup.coe_mul,
      col_mul_eq_mulVec_col, hg y hy', f, B]
  have hterm : π (map (algebraMap A F) (g (f y))) φ =
      π (map (algebraMap A F) b) (π (map (algebraMap A F) (g y)) φ) := calc
    _ = π (map (algebraMap A F) (g (f y))) (π (map (algebraMap A F) c) φ) := by rw [hφ _ hc]
    _ = _ := by simp only [← mul_apply_eq_comp, ← map_mul, c, mul_inv_cancel_left]
  rw [hcoord, hterm]

/-- The local `Up` operator at a principal congruence ideal preserves the fixed vectors of the
level fixing the marked column. The diagonal step scales that coordinate by `τ⁻¹`. This works
also for products of local integer rings, with no freeness condition on the representation. -/
theorem upOperator_fixed_of_col_eq (π : Representation k (GL ι F) V)
    (red : A →+* R) (l : ι) (g : (ι → R) → GL ι A) (ψ : R → k) (φ : V)
    (hg : ∀ y, IsUnit (y l) → (map red (g y) : Matrix ι ι R).col l = y)
    (hφ : ∀ a : GL ι A, (map red a : Matrix ι ι R).col l = Pi.single l 1 →
      π (map (algebraMap A F) a) φ = φ)
    {τ : A} (u : Fˣ) (hu : algebraMap A F τ = u)
    (hτ : IsRegular τ) (hker : ∀ x, red x = 0 ↔ τ ∣ x)
    {a : GL ι A} (ha : (map red a : Matrix ι ι R).col l = Pi.single l 1) :
    let D := (diagGL (fun i ↦ if i = l then u else 1) : GL ι F)⁻¹
    π (map (algebraMap A F) a) (upOperator π D l g ψ φ) = upOperator π D l g ψ φ := by
  obtain ⟨b, hb, hab⟩ := a.exists_map_eq_diagGL_mul_mul_inv_of_col_eq red l u hu hτ hker ha
  let U : GL ι F := diagGL (fun i ↦ if i = l then u else 1)
  have hcomm : map (algebraMap A F) a * U⁻¹ = U⁻¹ * map (algebraMap A F) b := by
    calc
      _ = U⁻¹ * (U * map (algebraMap A F) a * U⁻¹) := by simp [mul_assoc]
      _ = _ := congrArg (U⁻¹ * ·) hab.symm
  dsimp only
  rw [upOperator_apply, ← mul_apply_eq_comp, ← map_mul, hcomm, map_mul, mul_apply_eq_comp,
    sum_upOperator_fixed_of_row_eq π red l g ψ φ hg hφ hb]

end TauCeti.ThetaLift
