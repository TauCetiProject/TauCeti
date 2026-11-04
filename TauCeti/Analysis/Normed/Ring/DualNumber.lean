/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# The dual numbers with the maximum norm

The ring of dual numbers `K[ε]`, `ε ^ 2 = 0`, with the maximum norm `‖a + b ε‖ = max ‖a‖ ‖b‖`
of its two coefficients (`TauCeti.MaxDualNumber`). Mathlib's `DualNumber K` carries the `ℓ¹`
norm `‖a‖ + ‖b‖` instead, which is not ultrametric, so the maximum norm lives on a type synonym.
Over a complete ultrametric normed ring `K` with `‖1‖ = 1` it is a complete ultrametric normed
ring with `‖1‖ = 1` and `‖ε‖ = 1`, and its norm is not multiplicative since `ε * ε = 0`.

It is a basic example of a nonreduced ultrametric Banach ring, built on Mathlib's `DualNumber K`
(`TrivSqZeroExt K K`) through the ring identification `TauCeti.MaxDualNumber.ofDualNumber`.
-/

public section

namespace TauCeti

/-- The dual numbers `K[ε]` with the maximum norm `‖a + b ε‖ = max ‖a‖ ‖b‖` of the two
coefficients, in place of the `ℓ¹` norm Mathlib puts on `DualNumber K`. -/
@[expose] def MaxDualNumber (K : Type*) : Type _ := DualNumber K

namespace MaxDualNumber

variable {K : Type*} [NormedCommRing K] [IsUltrametricDist K]

/-- The maximum norm of the coefficients of dual numbers is submultiplicative, because the norm of
`K` is ultrametric: `‖a * d + b * c‖ ≤ max ‖a * d‖ ‖b * c‖`. -/
private theorem max_norm_mul_le (a b : DualNumber K) :
    max ‖(a * b).fst‖ ‖(a * b).snd‖ ≤ max ‖a.fst‖ ‖a.snd‖ * max ‖b.fst‖ ‖b.snd‖ := by
  rw [TrivSqZeroExt.fst_mul, DualNumber.snd_mul,
    mul_max_of_nonneg _ _ ((norm_nonneg _).trans (le_max_left _ _)),
    max_mul_of_nonneg _ _ (norm_nonneg _), max_mul_of_nonneg _ _ (norm_nonneg _)]
  exact max_le (le_max_of_le_left (le_max_of_le_left (norm_mul_le _ _)))
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (le_max_of_le_right (le_max_of_le_left (norm_mul_le _ _)))
      (le_max_of_le_left (le_max_of_le_right (norm_mul_le _ _)))))

/-- The ring structure of the dual numbers with the maximum norm of the coefficient pair, which
is the norm of `K × K`. -/
noncomputable instance : NormedCommRing (MaxDualNumber K) where
  __ : NormedAddCommGroup (K × K) := inferInstance
  __ : CommRing (DualNumber K) := inferInstance
  -- The norm of `x` is by definition the maximum norm of its coefficients.
  norm_mul_le a b := by exact max_norm_mul_le a b

/-- The identification of `MaxDualNumber K` with Mathlib's dual numbers, as rings. -/
def ofDualNumber : DualNumber K ≃+* MaxDualNumber K := RingEquiv.refl _

/-- The norm of a dual number is the maximum of the norms of its two coefficients. -/
@[simp]
theorem norm_ofDualNumber (x : DualNumber K) :
    ‖ofDualNumber x‖ = max ‖x.fst‖ ‖x.snd‖ := (rfl)

/-- The square-zero generator `ε` of `MaxDualNumber K`. -/
def eps : MaxDualNumber K := ofDualNumber DualNumber.eps

/-- The generator `ε` squares to zero, so `MaxDualNumber K` has nilpotents. -/
@[simp]
theorem eps_mul_eps : (eps * eps : MaxDualNumber K) = 0 := by
  rw [eps, ← map_mul, DualNumber.eps_mul_eps, map_zero]

instance : IsUltrametricDist (MaxDualNumber K) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ ?_
  obtain ⟨a, rfl⟩ := ofDualNumber.surjective x
  obtain ⟨b, rfl⟩ := ofDualNumber.surjective y
  rw [← map_add, norm_ofDualNumber, norm_ofDualNumber, norm_ofDualNumber, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.snd_add, max_max_max_comm]
  exact max_le_max (IsUltrametricDist.norm_add_le_max _ _) (IsUltrametricDist.norm_add_le_max _ _)

instance [CompleteSpace K] : CompleteSpace (MaxDualNumber K) :=
  inferInstanceAs (CompleteSpace (K × K))

variable [NormOneClass K]

instance : NormOneClass (MaxDualNumber K) :=
  ⟨by rw [← map_one ofDualNumber, norm_ofDualNumber]; simp⟩

/-- The generator `ε` has norm one, the norm of its only nonzero coefficient. -/
@[simp]
theorem norm_eps : ‖(eps : MaxDualNumber K)‖ = 1 := by
  rw [eps, norm_ofDualNumber, DualNumber.fst_eps, DualNumber.snd_eps]
  simp

/-- The maximum norm on the dual numbers is not multiplicative: `‖ε * ε‖ = 0` while `‖ε‖ = 1`. -/
theorem not_normMulClass : ¬NormMulClass (MaxDualNumber K) := fun _ ↦ by
  simpa using norm_mul (eps : MaxDualNumber K) eps

end MaxDualNumber

end TauCeti
