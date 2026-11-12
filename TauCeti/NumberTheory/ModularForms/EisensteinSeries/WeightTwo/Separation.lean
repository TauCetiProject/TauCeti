/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Weighted
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem

/-!
# Separation by Weierstrass division values

The single-residue weight-two Eisenstein series at a nonzero vector `a mod N` is
`N⁻² ℘((a₀ τ + a₁) / N; ℤ τ + ℤ)`. At every `τ` these values distinguish the nonzero vectors
exactly up to sign. Consequently a matrix preserving all the division values is `I` or `-I`.
This includes level two, where the two matrices coincide.

These are the separation statements for constructing modular function field generators from
the division values: multiplying them by a common nonzero modular factor of weight minus two
preserves the separation and gives weight-zero functions. The assertions here concern the
weight-two division values themselves.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1 (the Fricke functions).
-/

public noncomputable section

open Complex Matrix UpperHalfPlane PeriodPair

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- **Separation of nonzero division vectors.** At any point of the upper half-plane, two
single-residue weight-two series have the same value exactly when their residues agree up to
sign. The nonzero conditions exclude the lattice points, where `℘` has a junk value. -/
theorem weightedG2_single_apply_eq_iff {a b : Fin 2 → ZMod N} (ha : a ≠ 0) (hb : b ≠ 0)
    (z : ℍ) :
    weightedG2 (Pi.single a (1 : ℂ)) z = weightedG2 (Pi.single b (1 : ℂ)) z ↔
      a = b ∨ a = -b := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hnot (c : Fin 2 → ZMod N) (hc : c ≠ 0) :
      ((c 0).val * (z : ℂ) + (c 1).val) / N ∉ z.periodPair.lattice := by
    intro h
    have he := intCast_comp_eq_zero_of_div_mem_lattice_periodPair
      (b := fun i ↦ ((c i).val : ℤ)) h
    apply hc
    ext i
    simpa using congrFun he i
  constructor
  · intro h
    rw [weightedG2_single_apply, weightedG2_single_apply,
      mul_right_inj' (inv_ne_zero (pow_ne_zero 2 hN)),
      z.periodPair.weierstrassP_eq_weierstrassP_iff (hnot a ha) (hnot b hb)] at h
    rcases h with h | h
    · have hdiv : (((((a 0).val : ℤ) - (b 0).val : ℤ) : ℂ) * z +
          (((a 1).val : ℤ) - (b 1).val : ℤ)) / N ∈ z.periodPair.lattice := by
        convert h using 1
        push_cast
        ring
      have he := intCast_comp_eq_zero_of_div_mem_lattice_periodPair
        (b := fun i ↦ ((a i).val : ℤ) - (b i).val) hdiv
      left
      ext i
      have hi : a i - b i = 0 := by simpa using congrFun he i
      exact sub_eq_zero.mp hi
    · have hdiv : (((((a 0).val : ℤ) + (b 0).val : ℤ) : ℂ) * z +
          (((a 1).val : ℤ) + (b 1).val : ℤ)) / N ∈ z.periodPair.lattice := by
        convert h using 1
        push_cast
        ring
      have he := intCast_comp_eq_zero_of_div_mem_lattice_periodPair
        (b := fun i ↦ ((a i).val : ℤ) + (b i).val) hdiv
      right
      ext i
      have hi : a i + b i = 0 := by simpa using congrFun he i
      exact eq_neg_of_add_eq_zero_left hi
  · rintro (rfl | rfl)
    · rfl
    · simp

end TauCeti.EisensteinSeries

namespace Matrix.GeneralLinearGroup

open TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- **The common stabilizer of the division values is `±I`.** An invertible matrix acting on
residue row vectors preserves every nonzero division value if and only if it is the identity or
its negative. This holds at each fixed `z`, and for every positive level, including levels one
and two. -/
theorem forall_weightedG2_single_vecMul_apply_eq_iff (g : GL (Fin 2) (ZMod N)) (z : ℍ) :
    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      weightedG2 (Pi.single (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N))) (1 : ℂ)) z =
        weightedG2 (Pi.single a (1 : ℂ)) z) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    have hsign (a : Fin 2 → ZMod N) :
        a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N)) = a ∨
          a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N)) = -a := by
      by_cases ha : a = 0
      · simp [ha]
      have hga : a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N)) ≠ 0 := by
        intro he
        apply ha
        apply Matrix.vecMul_injective_of_isUnit g.isUnit
        simpa using he
      exact (weightedG2_single_apply_eq_iff hga ha z).mp (h a ha)
    -- The two basis vectors determine the rows. Their sum forces the same sign on both.
    have h₀ := hsign ![1, 0]
    have h₁ := hsign ![0, 1]
    have h₂ := hsign ![1, 1]
    clear h hsign
    simp only [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.neg_apply, one_mul, zero_mul, add_zero, zero_add, neg_zero] at h₀ h₁ h₂
    rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    all_goals
      first
      | solve
        | left
          apply Units.ext
          ext i j
          fin_cases i <;> fin_cases j <;> simp only [Units.val_one, Matrix.one_apply] <;> grind
      | right
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply] <;> grind
  · rintro (rfl | rfl) a _
    · simp
    · simp [Matrix.vecMul_neg]

/-- At level two the common stabilizer of the division values is the identity, since `-I = I`.
-/
theorem forall_weightedG2_single_vecMul_apply_eq_iff_level_two
    (g : GL (Fin 2) (ZMod 2)) (z : ℍ) :
    (∀ a : Fin 2 → ZMod 2, a ≠ 0 →
      weightedG2 (Pi.single (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod 2))) (1 : ℂ)) z =
        weightedG2 (Pi.single a (1 : ℂ)) z) ↔ g = 1 := by
  rw [forall_weightedG2_single_vecMul_apply_eq_iff]
  have h : (-1 : GL (Fin 2) (ZMod 2)) = 1 := by
    ext i j
    simp [ZMod.neg_eq_self_mod_two]
  rw [h, or_self]

end Matrix.GeneralLinearGroup
