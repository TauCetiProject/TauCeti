/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import TauCeti.NumberTheory.Padics.Measure.Clopen.Topology
public import TauCeti.NumberTheory.Padics.Measure.FiniteProjection
public import TauCeti.NumberTheory.Padics.Measure.Multiples

/-!
# Restricting p-adic measures to residue classes

The residue classes modulo `p ^ n` give a finite clopen partition of `ℤ_p`. Weighting by their
indicators defines orthogonal projectors on measures on the ambient space, whose sum is the
identity. Passing to a finer modulus decomposes each projector into the projectors above it.

These restrictions agree with restriction to the clopen subtype followed by inclusion. Their
masses are the finite coordinates of a measure, and their Amice coefficients are the corresponding
restricted Mahler moments. Depth zero is allowed and gives the identity, including at `p = 2`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.3–5,
  Remark 3.31 and equation (3-5).
-/

public noncomputable section

open ContinuousMap TopologicalSpace

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

section TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local instance instContinuousMulResidue : ContinuousMul C(ℤ_[p], R) :=
  ContinuousMap.instContinuousMulOfLocallyCompactSpace

/-- Restriction to a residue class, extended by zero on the ambient `ℤ_p` measure carrier. -/
def restrictResidue (n : ℕ) (a : ZMod (p ^ n)) : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R) :=
  weight (fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a)

/-- A residue restriction integrates after multiplication by its fibre indicator. -/
@[simp]
theorem restrictResidue_apply (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R))
    (f : C(ℤ_[p], R)) :
    restrictResidue n a μ f =
      μ (fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a * f) := by
  rw [restrictResidue, weight_apply]

/-- Restriction keeps exactly the atoms in the specified residue class. -/
@[simp]
theorem restrictResidue_dirac (n : ℕ) (a : ZMod (p ^ n)) (x : ℤ_[p]) :
    restrictResidue n a (dirac R x) =
      if PadicInt.toZModPow n x = a then dirac R x else 0 := by
  classical
  rw [restrictResidue, weight_dirac, fiberIndicator_apply, coe_mk]
  split_ifs
  · exact one_smul R (dirac R x)
  · exact zero_smul R (dirac R x)

/-- Residue restrictions at a fixed depth are orthogonal idempotents. -/
theorem restrictResidue_comp (n : ℕ) (a b : ZMod (p ^ n)) (μ : D(ℤ_[p], R)) :
    restrictResidue n a (restrictResidue n b μ) =
      if a = b then restrictResidue n a μ else 0 := by
  classical
  have hmul :
      fiberIndicator (R := R) ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a *
        fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ b =
      if a = b then
        fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a else 0 := by
    ext x
    split_ifs with hab
    · subst b
      simp only [ContinuousMap.mul_apply, fiberIndicator_apply, coe_mk]
      split_ifs <;> simp_all
    · simp only [ContinuousMap.zero_apply, ContinuousMap.mul_apply, fiberIndicator_apply,
        coe_mk]
      split_ifs <;> simp_all
  rw [restrictResidue, restrictResidue, ← weight_mul, hmul]
  split_ifs with h
  · rfl
  · exact weight_zero μ

/-- Restricting twice to the same residue class is the same as restricting once. -/
@[simp]
theorem restrictResidue_idem (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R)) :
    restrictResidue n a (restrictResidue n a μ) = restrictResidue n a μ := by
  simp [restrictResidue_comp]

/-- A measure is the sum of its restrictions to all residue classes at any fixed depth. -/
@[simp]
theorem sum_restrictResidue (n : ℕ) (μ : D(ℤ_[p], R)) :
    ∑ a : ZMod (p ^ n), restrictResidue n a μ = μ := by
  classical
  apply toCLMEquiv.injective
  ext f
  have hfun :
      ∑ a : ZMod (p ^ n),
        fiberIndicator (R := R) ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a * f =
      f := by
    ext x
    simp [fiberIndicator_apply]
  simpa only [map_sum, _root_.sum_apply, coe_toCLMEquiv, restrictResidue_apply] using
    congrArg μ hfun

/-- Modulo `p ^ 0 = 1` there is only one residue class, so restriction is the identity. -/
@[simp]
theorem restrictResidue_zero_depth (a : ZMod (p ^ 0)) (μ : D(ℤ_[p], R)) :
    restrictResidue 0 a μ = μ := by
  classical
  have : Subsingleton (ZMod (p ^ 0)) := by simp only [pow_zero]; infer_instance
  have hfun :
      fiberIndicator (R := R) ⟨PadicInt.toZModPow 0, PadicInt.continuous_toZModPow 0⟩ a = 1 := by
    ext x
    rw [fiberIndicator_apply, coe_mk]
    exact ite_eq_left (Subsingleton.elim _ _)
  rw [restrictResidue, hfun, weight_one]

/-- A coarse residue restriction is the sum of the finer restrictions lying above it. -/
theorem restrictResidue_refinement {m n : ℕ} (hmn : m ≤ n) (a : ZMod (p ^ m))
    (μ : D(ℤ_[p], R)) :
    restrictResidue m a μ =
      ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ n) ↦
        ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)) b = a), restrictResidue n b μ := by
  classical
  apply toCLMEquiv.injective
  ext f
  have hfun :
      fiberIndicator (R := R) ⟨PadicInt.toZModPow m, PadicInt.continuous_toZModPow m⟩ a * f =
      ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ n) ↦
        ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)) b = a),
        fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ b * f := by
    ext x
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, fiberIndicator_apply,
      coe_mk, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [ZMod.castHom_apply, PadicInt.cast_toZModPow m n hmn x]
  simpa only [map_sum, _root_.sum_apply, coe_toCLMEquiv, restrictResidue_apply] using
    congrArg μ hfun

/-- Translation carries restriction to a residue class to restriction to the translated class. -/
theorem restrictResidue_map_addRight (n : ℕ) (a : ZMod (p ^ n)) (b : ℤ_[p])
    (μ : D(ℤ_[p], R)) :
    restrictResidue n (a + PadicInt.toZModPow n b) (map (ContinuousMap.addRight b) μ) =
      map (ContinuousMap.addRight b) (restrictResidue n a μ) := by
  classical
  have htest :
      (fiberIndicator (R := R) ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩
        (a + PadicInt.toZModPow n b)).comp (ContinuousMap.addRight b) =
      fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a := by
    ext x
    simp [fiberIndicator_apply, coe_mk]
  rw [restrictResidue, ← map_weight, htest, restrictResidue]

/-- The mass in a residue class is the corresponding finite coefficient of the measure. -/
theorem restrictResidue_mass (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R)) :
    restrictResidue n a μ 1 =
      finiteProjection ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ μ a := by
  simp

/-- The Amice coefficients after restriction are the restricted Mahler moments. -/
theorem coeff_amiceTransform_restrictResidue [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R]
    (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R)) (k : ℕ) :
    (restrictResidue n a μ).amiceTransform.coeff k =
      μ (fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a *
        ((mahler k : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R)))) := by
  rw [coeff_amiceTransform, restrictResidue_apply]

end TopologicalRing

section NormedRing

variable {R : Type*} [NormedCommRing R]

/-- Ambient residue restriction agrees with intrinsic clopen restriction followed by inclusion. -/
theorem restrictResidue_eq_map_restrictClopen (n : ℕ) (a : ZMod (p ^ n))
    (μ : D(ℤ_[p], R)) :
    restrictResidue n a μ =
      map (subtypeVal (PadicInt.residueClopen n a : Set ℤ_[p]))
        (restrictClopen (PadicInt.residueClopen n a) μ) := by
  ext f
  rw [restrictResidue_apply, map_subtype_restrictClopen_apply]
  congr 2
  ext x
  rw [fiberIndicator_apply, coe_mk]
  by_cases hx : x ∈ PadicInt.residueClopen n a
  · simp only [PadicInt.mem_residueClopen] at hx
    simp [hx, LocallyConstant.charFn, PadicInt.mem_residueClopen]
  · simp only [PadicInt.mem_residueClopen] at hx
    simp [hx, LocallyConstant.charFn, PadicInt.mem_residueClopen]

/-- Residue restriction is continuous for the weak topology, without selecting a topology instance
on measures globally. -/
theorem continuous_restrictResidue_weak (n : ℕ) (a : ZMod (p ^ n)) :
    @Continuous _ _ (WeakTopology (X := ℤ_[p]) (R := R) (E := R))
      (WeakTopology (X := ℤ_[p]) (R := R) (E := R)) (restrictResidue n a) := by
  let : TopologicalSpace D(ℤ_[p], R) := WeakTopology
  let : TopologicalSpace D(PadicInt.residueClopen n a, R) := WeakTopology
  have h :=
    (subtypeVal (PadicInt.residueClopen n a : Set ℤ_[p])).continuous_abstractMeasure_map_weak
      (R := R) (E := R)
  exact (h.comp (Clopens.continuous_restrictClopen_weak (PadicInt.residueClopen n a))).congr
    fun μ ↦ (restrictResidue_eq_map_restrictClopen n a μ).symm

/-- The zero residue class modulo `p` recovers restriction to the multiples of `p`. -/
theorem restrictResidue_one_zero (μ : D(ℤ_[p], R)) :
    restrictResidue 1 0 μ = restrictMultiples μ := by
  ext f
  rw [restrictResidue_apply, restrictMultiples_apply]
  congr 2
  ext x
  by_cases hx : (p : ℤ_[p]) ∣ x
  · simp [fiberIndicator_apply, PadicInt.toZModPow_eq_zero_iff_dvd, hx]
  · simp [fiberIndicator_apply, PadicInt.toZModPow_eq_zero_iff_dvd, hx]

end NormedRing

-- These tests distinguish a residue class from its larger unit-support locus.
example (μ : D(ℤ_[2], ℤ)) : restrictResidue 0 0 μ = μ := by simp

example : restrictResidue 2 (1 : ZMod (2 ^ 2)) (dirac ℤ (5 : ℤ_[2])) =
    dirac ℤ (5 : ℤ_[2]) := by
  have h : PadicInt.toZModPow 2 (5 : ℤ_[2]) = (1 : ZMod (2 ^ 2)) := by
    rw [map_ofNat]
    decide
  rw [restrictResidue_dirac, ite_eq_left h]

example : restrictResidue 2 (1 : ZMod (2 ^ 2)) (dirac ℤ (3 : ℤ_[2])) = 0 := by
  have h : PadicInt.toZModPow 2 (3 : ℤ_[2]) ≠ (1 : ZMod (2 ^ 2)) := by
    rw [map_ofNat]
    decide
  rw [restrictResidue_dirac, ite_eq_right h]

end AbstractMeasure
