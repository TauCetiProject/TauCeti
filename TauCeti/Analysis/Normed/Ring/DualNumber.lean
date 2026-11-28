/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Group.Constructions
public import TauCeti.Topology.MetricSpace.Ultra.Prod

import TauCeti.Algebra.TrivSqZeroExt.Basic

/-!
# The dual numbers with the maximum norm

The ring of dual numbers `K[ε]`, `ε ^ 2 = 0`, with the maximum norm `‖a + b ε‖ = max ‖a‖ ‖b‖`
of its two coefficients (`TauCeti.MaxDualNumber`). Mathlib's `DualNumber K` carries the `ℓ¹`
norm `‖a‖ + ‖b‖` instead, which is not ultrametric, so the maximum norm lives on a type synonym.
Over a complete ultrametric normed ring `K` with `‖1‖ = 1` it is a complete ultrametric normed
ring with `‖1‖ = 1` and `‖ε‖ = 1`, and its norm is not multiplicative since `ε * ε = 0`.

It is a basic example of a nonreduced ultrametric Banach ring, built on Mathlib's `DualNumber K`
(`TrivSqZeroExt K K`) through the ring identification `TauCeti.MaxDualNumber.ofDualNumber`, with
canonical bounded inclusion `TauCeti.MaxDualNumber.inlHom` and projection
`TauCeti.MaxDualNumber.fstHom` modulo nilpotents.
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

instance : IsUltrametricDist (MaxDualNumber K) :=
  inferInstanceAs (IsUltrametricDist (K × K))

instance [CompleteSpace K] : CompleteSpace (MaxDualNumber K) :=
  inferInstanceAs (CompleteSpace (K × K))

/-- The canonical ring inclusion `K →+* MaxDualNumber K`. -/
noncomputable def inlHom (K : Type*) [NormedCommRing K] [IsUltrametricDist K] :
    K →+* MaxDualNumber K :=
  ofDualNumber.toRingHom.comp (TrivSqZeroExt.inlHom K K)

/-- The canonical ring projection `MaxDualNumber K →+* K`. -/
noncomputable def fstHom (K : Type*) [NormedCommRing K] [IsUltrametricDist K] :
    MaxDualNumber K →+* K :=
  (TrivSqZeroExt.fstHom ℕ K K).toRingHom.comp ofDualNumber.symm.toRingHom

/-- Applying `MaxDualNumber.inlHom` embeds an element as the constant part in `MaxDualNumber K`. -/
@[simp]
theorem inlHom_apply (x : K) : inlHom K x = ofDualNumber (TrivSqZeroExt.inl x) := by
  simp only [inlHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    TrivSqZeroExt.inlHom_apply]

/-- Applying `MaxDualNumber.fstHom` extracts the constant coefficient of a dual number. -/
@[simp]
theorem fstHom_apply (y : MaxDualNumber K) : fstHom K y = (ofDualNumber.symm y).fst := by
  simp only [fstHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, TrivSqZeroExt.fstHom_apply]

/-- The canonical inclusion `MaxDualNumber.inlHom K` is bounded with constant `1` for the
maximum norm. -/
theorem isBounded_inlHom (K : Type*) [NormedCommRing K] [IsUltrametricDist K] :
    (inlHom K).IsBounded :=
  ⟨1, zero_lt_one, fun x ↦ by simp⟩

/-- The canonical projection `MaxDualNumber.fstHom K` is bounded with constant `1` for the
maximum norm. -/
theorem isBounded_fstHom (K : Type*) [NormedCommRing K] [IsUltrametricDist K] :
    (fstHom K).IsBounded :=
  ⟨1, zero_lt_one, fun y ↦ by
    obtain ⟨z, rfl⟩ := ofDualNumber.surjective y
    rw [fstHom_apply, RingEquiv.symm_apply_apply, norm_ofDualNumber, one_mul]
    exact le_max_left _ _⟩

/-- Projecting after `MaxDualNumber.inlHom` recovers the original element. -/
theorem fstHom_inlHom (x : K) : fstHom K (inlHom K x) = x := by
  rw [fstHom_apply, inlHom_apply, RingEquiv.symm_apply_apply, TrivSqZeroExt.fst_inl]

/-- Every element of `MaxDualNumber K` differs from `inlHom K (fstHom K y)` by a nilpotent
element. -/
theorem isNilpotent_sub_inlHom_fstHom (y : MaxDualNumber K) :
    IsNilpotent (y - inlHom K (fstHom K y)) := by
  rw [fstHom_apply, inlHom_apply]
  obtain ⟨n, hn⟩ := TrivSqZeroExt.isNilpotent_sub_inl_fst (ofDualNumber.symm y)
  refine ⟨n, ?_⟩
  simpa only [map_sub, map_pow, RingEquiv.apply_symm_apply, map_zero] using
    congrArg ofDualNumber hn

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
