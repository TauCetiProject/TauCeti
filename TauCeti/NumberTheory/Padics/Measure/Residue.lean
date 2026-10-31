/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.FiniteProjection
public import TauCeti.NumberTheory.Padics.Measure.Multiples
public import TauCeti.NumberTheory.Padics.Measure.Clopen.Basic
public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform

/-!
# Restriction of p-adic measures to residue classes

The fibres of reduction modulo `p ^ n` partition `ℤ_p` into clopen residue classes.
Weighting by their characteristic functions gives mutually orthogonal linear projectors
on abstract measures. Their sum is the identity, and a projector at a coarse level is the
sum of the projectors over its finer residue classes. Their masses recover the finite
coordinates of the measure.

Restriction is compatible with translation, intrinsic clopen restriction, and the weak
measure topology. The Amice coefficients of a restricted measure are the integrals of the
Mahler tests multiplied by the residue-class indicator. Depth zero and the prime two are
included throughout; no norm or topology instance is installed on measures.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
§3.5.3, Remark 3.31 and equation (3-5), and §3.5.4–5.
-/

public noncomputable section

open ContinuousMap TopologicalSpace

variable {p : ℕ} [Fact p.Prime]

namespace TauCeti

/-- The clopen residue class `a` modulo `p ^ n` in the p-adic integers. -/
def padicResidueClopen (n : ℕ) (a : ZMod (p ^ n)) : Clopens ℤ_[p] :=
  ⟨{x | PadicInt.toZModPow n x = a},
    (isClopen_discrete {a}).preimage (PadicInt.continuous_toZModPow n)⟩

@[simp]
theorem mem_padicResidueClopen (n : ℕ) (a : ZMod (p ^ n)) (x : ℤ_[p]) :
    x ∈ padicResidueClopen n a ↔ PadicInt.toZModPow n x = a := Iff.rfl

/-- The residue class of `y` is the coset of `p ^ n ℤ_p` represented by `y`. -/
theorem mem_padicResidueClopen_iff_dvd_sub (n : ℕ) (x y : ℤ_[p]) :
    x ∈ padicResidueClopen n (PadicInt.toZModPow n y) ↔ (p : ℤ_[p]) ^ n ∣ x - y := by
  rw [mem_padicResidueClopen, PadicInt.toZModPow_eq_iff_dvd_sub, dvd_sub_comm]

end TauCeti

namespace AbstractMeasure

section TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Restriction to the residue class `a` modulo `p ^ n`, extended by zero on `ℤ_p`. -/
def restrictResidue (n : ℕ) (a : ZMod (p ^ n)) : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R) :=
  weight (fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a)

/-- Residue restriction is weighting by the indicator of the reduction fibre. -/
theorem restrictResidue_eq_weight (n : ℕ) (a : ZMod (p ^ n)) :
    restrictResidue (R := R) n a =
      weight (fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a) := (rfl)

@[simp]
theorem restrictResidue_apply (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R))
    (f : C(ℤ_[p], R)) :
    restrictResidue n a μ f =
      μ (fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a * f) := by
  rw [restrictResidue_eq_weight, weight_apply]

/-- A residue projector keeps exactly the atoms whose reductions equal its residue. -/
@[simp]
theorem restrictResidue_dirac (n : ℕ) (a : ZMod (p ^ n)) (x : ℤ_[p]) :
    restrictResidue n a (dirac R x) =
      if PadicInt.toZModPow n x = a then dirac R x else 0 := by
  classical
  by_cases hx : PadicInt.toZModPow n x = a
  · simp only [ite_eq_left hx]
    ext f
    simp [fiberIndicator_apply, hx]
  · simp only [ite_eq_right hx]
    apply toCLMEquiv.injective
    rw [map_zero]
    ext f
    simp [fiberIndicator_apply, hx]

/-- At a fixed depth, the residue projectors are orthogonal. -/
theorem restrictResidue_comp (n : ℕ) (a b : ZMod (p ^ n)) (μ : D(ℤ_[p], R)) :
    restrictResidue n a (restrictResidue n b μ) =
      if a = b then restrictResidue n a μ else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    ext f
    simp only [ite_true, restrictResidue_apply]
    apply congrArg μ
    ext x
    by_cases hx : PadicInt.toZModPow n x = a <;> simp [fiberIndicator_apply, hx]
  · simp only [ite_eq_right hab]
    ext f
    have hzero : fiberIndicator (R := R)
        ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ b *
        (fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a * f) = 0 := by
      ext x
      by_cases hx : PadicInt.toZModPow n x = a <;> simp [fiberIndicator_apply, hx, hab]
    rw [← coe_toCLMEquiv (0 : D(ℤ_[p], R)), map_zero]
    simp [hzero]

/-- Restriction to a residue class is idempotent. -/
@[simp]
theorem restrictResidue_idem (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R)) :
    restrictResidue n a (restrictResidue n a μ) = restrictResidue n a μ := by
  simp [restrictResidue_comp]

/-- Summing the restrictions over all residues recovers the measure. -/
-- Apply the partition identity before simplifying numerical powers in the residue type.
@[simp↓]
theorem sum_restrictResidue (n : ℕ) (μ : D(ℤ_[p], R)) :
    ∑ a : ZMod (p ^ n), restrictResidue n a μ = μ := by
  classical
  ext f
  have hsum : (∑ a : ZMod (p ^ n),
      fiberIndicator (R := R)
        ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a * f) = f := by
    ext x
    simp [fiberIndicator_apply]
  rw [← coe_toCLMEquiv, map_sum, _root_.sum_apply]
  simpa only [coe_toCLMEquiv, restrictResidue_apply, ← map_sum] using congrArg μ hsum

/-- At depth zero there is only one residue class, so restriction is the identity. -/
@[simp]
theorem restrictResidue_zero_depth (a : ZMod (p ^ 0)) (μ : D(ℤ_[p], R)) :
    restrictResidue 0 a μ = μ := by
  let : Subsingleton (ZMod (p ^ 0)) := by simpa using (inferInstance : Subsingleton (ZMod 1))
  have h : fiberIndicator (R := R)
      ⟨PadicInt.toZModPow 0, PadicInt.continuous_toZModPow 0⟩ a = 1 := by
    ext x
    rw [fiberIndicator_apply]
    exact ite_eq_left (Subsingleton.elim _ _)
  rw [restrictResidue_eq_weight, h, weight_one]

/-- A coarse restriction is the sum of the restrictions over the finer residues above it. -/
theorem restrictResidue_refinement {m n : ℕ} (h : m ≤ n) (a : ZMod (p ^ m))
    (μ : D(ℤ_[p], R)) :
    restrictResidue m a μ = ∑ b : ZMod (p ^ n),
      if ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) b = a then restrictResidue n b μ else 0 := by
  classical
  have hsum : fiberIndicator (R := R)
      ⟨PadicInt.toZModPow m, PadicInt.continuous_toZModPow m⟩ a =
      ∑ b : ZMod (p ^ n), if ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) b = a then
        fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ b else 0 := by
    ext x
    rw [fiberIndicator_apply, ContinuousMap.sum_apply]
    calc
      _ = ∑ b : ZMod (p ^ n), if PadicInt.toZModPow n x = b then
          (if ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) b = a then (1 : R) else 0)
          else 0 := by
        simp [PadicInt.cast_toZModPow m n h]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : (ZMod.cast b : ZMod (p ^ m)) = a <;>
          simp [hb, fiberIndicator_apply]
  ext f
  rw [← coe_toCLMEquiv (∑ b : ZMod (p ^ n), _), map_sum, _root_.sum_apply,
    restrictResidue_apply, hsum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

/-- The mass of a residue restriction is the corresponding finite coordinate. -/
theorem restrictResidue_mass (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R)) :
    restrictResidue n a μ 1 =
      finiteProjection ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ μ a := by
  simp

/-- Translation carries restriction at `a` to restriction at the translated residue. -/
theorem restrictResidue_map_add (n : ℕ) (a : ZMod (p ^ n)) (c : ℤ_[p]) (μ : D(ℤ_[p], R)) :
    restrictResidue n (a + PadicInt.toZModPow n c)
        (map (⟨fun x ↦ x + c, continuous_id.add continuous_const⟩ : C(ℤ_[p], ℤ_[p])) μ) =
      map (⟨fun x ↦ x + c, continuous_id.add continuous_const⟩ : C(ℤ_[p], ℤ_[p]))
        (restrictResidue n a μ) := by
  ext f
  simp only [restrictResidue_apply, map_apply]
  congr 1
  ext x
  simp [fiberIndicator_apply]

end TopologicalRing

section Normed

variable {R : Type*} [NormedCommRing R]

/-- Ambient residue restriction agrees with restriction to the clopen subtype and inclusion. -/
theorem restrictResidue_eq_map_restrictClopen (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R)) :
    restrictResidue n a μ =
      map (subtypeVal (TauCeti.padicResidueClopen n a : Set ℤ_[p]))
        (restrictClopen (TauCeti.padicResidueClopen n a) μ) := by
  ext f
  rw [restrictResidue_apply, map_subtype_restrictClopen_apply]
  congr 1
  ext x
  classical
  simp only [ContinuousMap.mul_apply, LocallyConstant.toContinuousMap,
    ContinuousMap.coe_mk, LocallyConstant.coe_charFn]
  by_cases hx : x ∈ TauCeti.padicResidueClopen n a
  · rw [Set.indicator_of_mem hx]
    simp [fiberIndicator_apply, (TauCeti.mem_padicResidueClopen n a x).mp hx]
  · rw [Set.indicator_of_notMem hx]
    simp [fiberIndicator_apply, (TauCeti.mem_padicResidueClopen n a x).not.mp hx]

/-- Residue restriction is continuous for the weak topology of test evaluations. -/
theorem continuous_restrictResidue_weak (n : ℕ) (a : ZMod (p ^ n)) :
    @Continuous _ _ (WeakTopology (X := ℤ_[p]) (R := R) (E := R))
      (WeakTopology (X := ℤ_[p]) (R := R) (E := R)) (restrictResidue (R := R) n a) := by
  let : TopologicalSpace D(ℤ_[p], R) := WeakTopology
  have heval : Continuous (fun μ : D(ℤ_[p], R) ↦ fun f : C(ℤ_[p], R) ↦ μ f) :=
    continuous_induced_dom
  exact continuous_induced_rng.mpr <| continuous_pi fun f ↦
    ((continuous_apply (_ * f)).comp heval).congr fun μ ↦
      (restrictResidue_apply n a μ f).symm

/-- Restriction to zero modulo `p` is the projector onto multiples of `p`. -/
@[simp]
theorem restrictResidue_one_zero (μ : D(ℤ_[p], R)) :
    restrictResidue 1 0 μ = restrictMultiples μ := by
  ext f
  rw [restrictResidue_apply, restrictMultiples_apply]
  congr 1
  ext x
  classical
  by_cases hx : (p : ℤ_[p]) ∣ x
  · simp [fiberIndicator_apply, PadicInt.toZModPow_eq_zero_iff_dvd, hx]
  · simp [fiberIndicator_apply, PadicInt.toZModPow_eq_zero_iff_dvd, hx]

end Normed

section Amice

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R]

/-- Amice coefficients after residue restriction are the restricted Mahler integrals. -/
theorem coeff_amiceTransform_restrictResidue (n : ℕ) (a : ZMod (p ^ n)) (μ : D(ℤ_[p], R))
    (k : ℕ) :
    PowerSeries.coeff k (restrictResidue n a μ).amiceTransform =
      μ (fiberIndicator ⟨PadicInt.toZModPow n, PadicInt.continuous_toZModPow n⟩ a *
        ((mahler k : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R)))) := by
  rw [coeff_amiceTransform, restrictResidue_apply]

end Amice

/-! Depth zero and two distinct odd residue classes modulo four. -/

example (μ : D(ℤ_[2], ℤ)) : restrictResidue 0 0 μ = μ := by simp

example : restrictResidue 2 (1 : ZMod (2 ^ 2)) (dirac ℤ (5 : ℤ_[2])) = dirac ℤ 5 := by
  have h : PadicInt.toZModPow (p := 2) 2 (5 : ℤ_[2]) = 1 := by
    rw [map_ofNat]
    decide
  rw [restrictResidue_dirac, ite_eq_left h]

example : restrictResidue 2 (1 : ZMod (2 ^ 2)) (dirac ℤ (3 : ℤ_[2])) = 0 := by
  have h : PadicInt.toZModPow (p := 2) 2 (3 : ℤ_[2]) ≠ 1 := by
    rw [map_ofNat]
    decide
  rw [restrictResidue_dirac, ite_eq_right h]

end AbstractMeasure
