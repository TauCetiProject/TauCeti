/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AffineGrassmannian.Lattice.Cartan
public import TauCeti.RingTheory.PowerSeries.Jet
public import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
import TauCeti.Algebra.Algebra.IsUnit
import Mathlib.Algebra.Group.Action.End

/-!
# Finite-jet actions on bounded lattices

The integral general linear group preserves every interval between two constant diagonal
lattices. A matrix congruent to the identity modulo `ξ ^ m` acts trivially on the interval
`ξ ^ b Bⁿ ⊆ L ⊆ ξ ^ a Bⁿ` when `b ≤ a + m`. Indeed its displacement sends `L` into
`ξ ^ (a + m) Bⁿ`, and the same applies to its inverse.

For power series this gives an action of `GLₙ(R[X]/(X ^ m))` on the interval, compatible with
the arc-group action, for every commutative ring `R` and positive `m ≥ b - a`.
Laurent series use Mathlib's localization algebra structure over power series.

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1 and §2.1.
-/

public section

open Matrix
open scoped Polynomial PowerSeries LaurentSeries

namespace TauCeti.ProjectiveLattice

section General

variable {B K : Type*} [CommRing B] [CommRing K] [Algebra B K] [FaithfulSMul B K]
  {n : Type*} [Fintype n] [DecidableEq n] {ξ : B}

/-- The integral general linear group acts on the interval between constant diagonal lattices.
The endpoints need not be distinct, and an empty interval is allowed. -/
noncomputable def diagonalIntervalAction (hξ : IsUnit (algebraMap B K ξ)) (a b : ℤ) :
    GL n B →* Equiv.Perm
      (Set.Icc (diagonal (fun _ : n ↦ b) hξ) (diagonal (fun _ : n ↦ a) hξ)) where
  toFun g :=
    { toFun L := ⟨GeneralLinearGroup.map (algebraMap B K) g • L.val,
        (diagonal_const_le_map_smul_iff g b hξ L.val).2 L.property.1,
        (map_smul_le_diagonal_const_iff g a hξ L.val).2 L.property.2⟩
      invFun L := ⟨GeneralLinearGroup.map (algebraMap B K) g⁻¹ • L.val,
        (diagonal_const_le_map_smul_iff g⁻¹ b hξ L.val).2 L.property.1,
        (map_smul_le_diagonal_const_iff g⁻¹ a hξ L.val).2 L.property.2⟩
      left_inv L := Subtype.ext (by simp)
      right_inv L := Subtype.ext (by simp) }
  map_one' := by ext L : 2; simp
  map_mul' g h := by ext L : 2; simp [mul_smul]

/-- The action on the interval is the usual matrix action on its underlying lattice. -/
@[simp]
theorem coe_diagonalIntervalAction (hξ : IsUnit (algebraMap B K ξ)) (a b : ℤ)
    (g : GL n B) (L : Set.Icc (diagonal (fun _ : n ↦ b) hξ)
      (diagonal (fun _ : n ↦ a) hξ)) :
    (diagonalIntervalAction hξ a b g L).val =
      GeneralLinearGroup.map (algebraMap B K) g • L.val := (rfl)

/-- A matrix divisible entrywise by `ξ ^ m` raises the constant diagonal bound by `m`. -/
theorem mulVec_mem_diagonal_const_add (hξ : IsUnit (algebraMap B K ξ)) (a : ℤ) (m : ℕ)
    {A : Matrix n n B} (hA : ∀ i j, ξ ^ m ∣ A i j) {v : n → K}
    (hv : v ∈ diagonal (fun _ : n ↦ a) hξ) :
    A.map (algebraMap B K) *ᵥ v ∈ diagonal (fun _ : n ↦ a + m) hξ := by
  choose C hC using hA
  choose w hw using mem_diagonal.mp hv
  refine mem_diagonal.mpr fun i ↦ ⟨∑ j, C i j * w j, ?_⟩
  have hp := hξ.val_unit_zpow_eq_mul_algebraMap_pow_of_le
    (m := a) (n := a + m) (by omega)
  simp only [add_sub_cancel_left, Int.toNat_natCast] at hp
  simp only [mulVec, dotProduct, Matrix.map_apply, hC, hw, map_mul, map_sum, Finset.mul_sum, hp]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- A matrix congruent to the identity modulo `ξ ^ m` displaces vectors of `ξ ^ a Bⁿ` into
`ξ ^ (a + m) Bⁿ`. Invertibility is not required for this estimate. -/
theorem mulVec_sub_mem_diagonal_const_add (hξ : IsUnit (algebraMap B K ξ)) (a : ℤ) (m : ℕ)
    {A : Matrix n n B} (hA : ∀ i j, ξ ^ m ∣ (A - 1) i j)
    {v : n → K} (hv : v ∈ diagonal (fun _ : n ↦ a) hξ) :
    A.map (algebraMap B K) *ᵥ v - v ∈
      diagonal (fun _ : n ↦ a + m) hξ := by
  have h := mulVec_mem_diagonal_const_add hξ a m hA hv
  simpa [Matrix.map_sub, Matrix.map_one, sub_mulVec] using h

/-- A congruence element fixes a lattice between constant diagonal bounds when its level is
at least the width of the interval. -/
theorem map_smul_eq_of_congruent (hξ : IsUnit (algebraMap B K ξ)) {a b : ℤ} {m : ℕ}
    (hm : b ≤ a + m) {g : GL n B}
    (hg : ∀ i j, ξ ^ m ∣ ((g : Matrix n n B) - 1) i j)
    {L : ProjectiveLattice B K (n → K)}
    (hL : L ∈ Set.Icc (diagonal (fun _ : n ↦ b) hξ) (diagonal (fun _ : n ↦ a) hξ)) :
    GeneralLinearGroup.map (algebraMap B K) g • L = L := by
  have lower : diagonal (fun _ : n ↦ a + m) hξ ≤ diagonal (fun _ : n ↦ b) hξ := by
    intro v hv
    choose w hw using mem_diagonal.mp hv
    exact mem_diagonal.mpr fun i ↦ ⟨ξ ^ (a + m - b).toNat * w i, by
      rw [hw, hξ.val_unit_zpow_eq_mul_algebraMap_pow_of_le hm, map_mul, mul_assoc]⟩
  have preserves (u : GL n B) (hu : ∀ i j, ξ ^ m ∣ ((u : Matrix n n B) - 1) i j)
      {v : n → K} (hv : v ∈ L) : (u : Matrix n n B).map (algebraMap B K) *ᵥ v ∈ L := by
    have hd := hL.1 (lower (mulVec_sub_mem_diagonal_const_add hξ a m hu (hL.2 hv)))
    simpa using add_mem hd hv
  have hgi : ∀ i j, ξ ^ m ∣ ((g⁻¹ : GL n B) - 1 : Matrix n n B) i j := by
    have heq : (g⁻¹ : GL n B).val - 1 = -((g⁻¹ : GL n B).val * (g.val - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    intro i j
    rw [heq, Matrix.neg_apply, dvd_neg, Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_right (hg k j) _
  apply le_antisymm
  · intro v hv
    have hi : (g⁻¹ : GL n B).val.map (algebraMap B K) *ᵥ v ∈ L := by
      rwa [mem_GL_smul, ← map_inv, GeneralLinearGroup.val_map_apply] at hv
    simpa [mulVec_mulVec, ← Matrix.map_mul] using preserves g hg hi
  · intro v hv
    rw [mem_GL_smul, ← map_inv, GeneralLinearGroup.val_map_apply]
    exact preserves g⁻¹ hgi hv

end General

section PowerSeries

variable (R n : Type*) [CommRing R] [Fintype n] [DecidableEq n]

local instance : FaithfulSMul R⟦X⟧ R⸨X⸩ :=
  (faithfulSMul_iff_algebraMap_injective R⟦X⟧ R⸨X⸩).2 HahnSeries.ofPowerSeries_injective

/-- The lattices between `X ^ b R⟦X⟧ⁿ` and `X ^ a R⟦X⟧ⁿ`, with the localization algebra
structure on Laurent series. The bounds may coincide, and the coefficient ring may be nonreduced. -/
noncomputable abbrev powerSeriesInterval (a b : ℤ) :=
  Set.Icc (diagonal (fun _ : n ↦ b)
    (IsLocalization.Away.algebraMap_isUnit (S := R⸨X⸩) (PowerSeries.X : R⟦X⟧)))
    (diagonal (fun _ : n ↦ a)
      (IsLocalization.Away.algebraMap_isUnit (S := R⸨X⸩) (PowerSeries.X : R⟦X⟧)))

variable {R n}

/-- The reduction kernel at level `m` fixes every lattice in an interval of width at most `m`.
No positivity hypothesis is needed for this kernel assertion. -/
theorem map_smul_eq_of_jet_eq_one {a b : ℤ} {m : ℕ} (hm : b ≤ a + m)
    {g : GL n R⟦X⟧} (hg : GeneralLinearGroup.map
      (↑(PowerSeries.jet R m) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ m : R[X])) g = 1)
    (L : powerSeriesInterval R n a b) :
    GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val = L.val := by
  apply map_smul_eq_of_congruent _ hm ?_ L.property
  intro i j
  apply PowerSeries.jet_eq_zero_iff.mp
  have he := congrArg (fun u : GL n (AdjoinRoot (Polynomial.X ^ m : R[X])) ↦
    u.val i j) hg
  simpa [map_sub, Matrix.sub_apply, GeneralLinearGroup.val_map_apply, Matrix.one_apply] using
    sub_eq_zero.mpr he

variable (R n)

/-- The action of the finite jet group on an interval of lattices whose width is at most `m`.
It is uniquely determined by compatibility with the arc-group action. -/
noncomputable def jetAction (a b : ℤ) (m : ℕ) [NeZero m] (hm : b ≤ a + m) :
    GL n (AdjoinRoot (Polynomial.X ^ m : R[X])) →*
      Equiv.Perm (powerSeriesInterval R n a b) :=
  (GeneralLinearGroup.map (↑(PowerSeries.jet R m))).liftOfSurjective
    (GeneralLinearGroup.map_surjective _ PowerSeries.jet_surjective)
    ⟨diagonalIntervalAction (IsLocalization.Away.algebraMap_isUnit
        (PowerSeries.X : R⟦X⟧)) a b, fun g hg ↦ by
      apply MonoidHom.mem_ker.mpr
      ext L : 2
      exact map_smul_eq_of_jet_eq_one hm hg L⟩

/-- The finite-jet action as a `MulAction`, for use as a local instance after choosing the
jet level and its width bound. -/
noncomputable abbrev jetMulAction (a b : ℤ) (m : ℕ) [NeZero m] (hm : b ≤ a + m) :
    MulAction (GL n (AdjoinRoot (Polynomial.X ^ m : R[X]))) (powerSeriesInterval R n a b) :=
  MulAction.compHom _ (jetAction R n a b m hm)

variable {R n}

/-- Reducing an arc to its jet and applying the jet action gives the original lattice action. -/
@[simp]
theorem coe_jetAction_map {a b : ℤ} {m : ℕ} [NeZero m] (hm : b ≤ a + m)
    (g : GL n R⟦X⟧) (L : powerSeriesInterval R n a b) :
    (jetAction R n a b m hm (GeneralLinearGroup.map (↑(PowerSeries.jet R m)) g) L).val =
      GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val := by
  dsimp only [jetAction, MonoidHom.liftOfSurjective]
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  exact coe_diagonalIntervalAction _ a b g L

/-- The jet action is the unique action homomorphism extending the arc action on the interval. -/
theorem jetAction_unique {a b : ℤ} {m : ℕ} [NeZero m] (hm : b ≤ a + m)
    (ρ : GL n (AdjoinRoot (Polynomial.X ^ m : R[X])) →*
      Equiv.Perm (powerSeriesInterval R n a b))
    (hρ : ∀ (g : GL n R⟦X⟧) (L : powerSeriesInterval R n a b),
      (ρ (GeneralLinearGroup.map (↑(PowerSeries.jet R m)) g) L).val =
        GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val) :
    ρ = jetAction R n a b m hm := by
  ext q L : 3
  obtain ⟨g, rfl⟩ := GeneralLinearGroup.map_surjective
    (↑(PowerSeries.jet R m) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ m : R[X]))
    PowerSeries.jet_surjective q
  exact (hρ g L).trans (coe_jetAction_map hm g L).symm

/-- On a singleton interval every jet acts trivially. -/
@[simp]
theorem jetAction_self (a : ℤ) (m : ℕ) [NeZero m]
    (q : GL n (AdjoinRoot (Polynomial.X ^ m : R[X])))
    (L : powerSeriesInterval R n a a) :
    jetAction R n a a m (by omega) q L = L := by
  apply Subtype.ext
  exact (Set.subsingleton_Icc_of_ge le_rfl)
    (jetAction R n a a m (by omega) q L).property L.property

/-- On any lattice interval of width at most one, an arc acts in the same way as its constant
matrix. In particular this identifies the first-jet action on `XL₀ ⊆ L ⊆ L₀`. -/
theorem map_smul_eq_constantCoeff {a b : ℤ} (hab : b ≤ a + 1)
    (L : powerSeriesInterval R n a b) (g : GL n R⟦X⟧) :
    GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val =
      GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩)
        (GeneralLinearGroup.map (PowerSeries.C : R →+* R⟦X⟧)
          (GeneralLinearGroup.map (PowerSeries.constantCoeff : R⟦X⟧ →+* R) g)) • L.val := by
  have hj : GeneralLinearGroup.map
      (↑(PowerSeries.jet R 1) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ 1 : R[X])) g =
      GeneralLinearGroup.map
        (↑(PowerSeries.jet R 1) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ 1 : R[X]))
        (GeneralLinearGroup.map (PowerSeries.C : R →+* R⟦X⟧)
          (GeneralLinearGroup.map (PowerSeries.constantCoeff : R⟦X⟧ →+* R) g)) := by
    ext i j
    apply PowerSeries.jet_eq_jet_iff.mpr
    intro d hd
    obtain rfl : d = 0 := by omega
    simp [PowerSeries.coeff_zero_eq_constantCoeff]
  rw [← coe_jetAction_map (m := 1) hab g L, ← coe_jetAction_map (m := 1) hab _ L, hj]

end PowerSeries

end TauCeti.ProjectiveLattice
