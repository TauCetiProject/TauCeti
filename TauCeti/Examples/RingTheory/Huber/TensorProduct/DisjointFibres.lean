/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
public import TauCeti.RingTheory.Huber.TensorProduct.Pushout
public import TauCeti.RingTheory.Huber.Padic.Field
public import TauCeti.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod

/-!
# Checks: disjoint fibres and zero factors of completed tensor products

The generic fibre `ℤ_[p] → ℚ_[p]` and the special fibre `ℤ_[p] → 𝔽_p` of `ℤ_[p]` are both adic,
the latter with the discrete topology on `𝔽_p = ZMod p`. Their completed tensor product over
`(ℤ_[p], ℤ_[p])`, of `(ℚ_[p], ℤ_[p])` with `(𝔽_p, 𝔽_p)`, is the zero pair: `p` is a unit on the
left and zero on the right, so already `ℚ_[p] ⊗_{ℤ_[p]} 𝔽_p = 0`. This zero pair is the completed
pushout of the two fibres, and its adic spectrum is empty: the generic and special fibres of
`Spa ℤ_[p]` have empty fibre product (*disjoint_fibres_zero_ring*).

More generally a zero factor makes the completed tensor product zero and its adic spectrum empty,
so there is no compatible pair of points to lift (*completedTensor_point_zero_factor*).
-/

public section

open TensorProduct TauCeti.Huber TauCeti.ValuationSpectrum

namespace TauCeti.Huber.DisjointFibresChecks

section ZeroFactor

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- *completedTensor_point_zero_factor*: a zero right factor has empty adic spectrum, and so has
the completed tensor product. -/
example [Subsingleton C] (S : Pair B) (T : Pair C) :
    spa T.plus = ∅ ∧ spa (S.completedTensor A T).plus = ∅ := by
  have : Subsingleton (CompletedTensor A B C) := (CompletedTensor.inr A B C).codomain_trivial
  exact ⟨(spa_eq_empty_iff_one_mem_closure_zero _ T.isRingOfIntegralElements).mpr
      (subset_closure (Subsingleton.elim _ _)),
    (spa_eq_empty_iff_subsingleton _ (S.completedTensor A T).isRingOfIntegralElements).mpr
      inferInstance⟩

/-- *completedTensor_point_zero_factor*, left factor: a zero left factor has empty adic spectrum,
and so has the completed tensor product. -/
example [Subsingleton B] (S : Pair B) (T : Pair C) :
    spa S.plus = ∅ ∧ spa (S.completedTensor A T).plus = ∅ := by
  have : Subsingleton (CompletedTensor A B C) := (CompletedTensor.inl A B C).codomain_trivial
  exact ⟨(spa_eq_empty_iff_one_mem_closure_zero _ S.isRingOfIntegralElements).mpr
      (subset_closure (Subsingleton.elim _ _)),
    (spa_eq_empty_iff_subsingleton _ (S.completedTensor A T).isRingOfIntegralElements).mpr
      inferInstance⟩

end ZeroFactor

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- `𝔽_p` as a `ℤ_[p]`-algebra through the reduction `ℤ_[p] → 𝔽_p`. -/
private noncomputable abbrev algebraZMod : Algebra ℤ_[p] (ZMod p) := PadicInt.toZMod.toAlgebra

attribute [local instance] algebraZMod

/-- The reduction `ℤ_[p] → 𝔽_p` is adic: every ideal of the discrete ring `𝔽_p` is open. -/
private local instance isAdicHom_algebraMap_zmod : IsAdicHom (algebraMap ℤ_[p] (ZMod p)) :=
  IsAdicHom.of_continuous_isOpen_map PadicInt.continuous_toZMod fun _ _ ↦ isOpen_discrete _

/-- The algebraic tensor product of the generic and special fibres is zero: `p` is a unit in
`ℚ_[p]` and zero in `𝔽_p`. -/
private theorem subsingleton_tensor : Subsingleton (ℚ_[p] ⊗[ℤ_[p]] ZMod p) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpZ : (p : ℤ_[p]) • (1 : ZMod p) = 0 := by
    rw [Algebra.smul_def, mul_one, map_natCast, ZMod.natCast_self]
  have hpQ : (p : ℤ_[p]) • ((p : ℚ_[p])⁻¹) = 1 := by
    rw [Algebra.smul_def, map_natCast, mul_inv_cancel₀ hp]
  refine subsingleton_of_zero_eq_one ?_
  rw [Algebra.TensorProduct.one_def, ← hpQ, TensorProduct.smul_tmul, hpZ,
    TensorProduct.tmul_zero]

/-- The zero completed tensor product of the two fibres. -/
private theorem subsingleton_completedTensor :
    Subsingleton (CompletedTensor ℤ_[p] ℚ_[p] (ZMod p)) :=
  have := subsingleton_tensor p
  (CompletedTensor.toCompletion ℤ_[p] ℚ_[p] (ZMod p)).codomain_trivial

/-- The generic fibre `(ℤ_[p], ℤ_[p]) → (ℚ_[p], ℤ_[p])`. -/
noncomputable def generic : Pair.Hom (Pair.powerBounded ℤ_[p]) (Pair.powerBounded ℚ_[p]) where
  toRingHom := algebraMap ℤ_[p] ℚ_[p]
  continuous_toRingHom := continuous_subtypeVal
  map_mem_plus a _ := by
    rw [Pair.powerBounded_plus]
    exact mem_powerBoundedSubring.mpr (IsPowerBounded.of_norm_le_one a.property)

/-- The special fibre `(ℤ_[p], ℤ_[p]) → (𝔽_p, 𝔽_p)`. -/
private noncomputable def special :
    Pair.Hom (Pair.powerBounded ℤ_[p]) (Pair.discrete (ZMod p)) where
  toRingHom := algebraMap ℤ_[p] (ZMod p)
  continuous_toRingHom := PadicInt.continuous_toZMod
  map_mem_plus _ _ := by simp

/-- *disjoint_fibres_zero_ring*: the completed tensor product over `(ℤ_[p], ℤ_[p])` of the
generic fibre `(ℚ_[p], ℤ_[p])` and the special fibre `(𝔽_p, 𝔽_p)` is their
completed pushout, its ring is zero, and its adic spectrum is empty. -/
example :
    IsCompletedPushout (generic p) (special p)
        (Pair.completedTensor.inl ℤ_[p] (Pair.powerBounded ℚ_[p]) (Pair.discrete (ZMod p)))
        (Pair.completedTensor.inr ℤ_[p] (Pair.powerBounded ℚ_[p]) (Pair.discrete (ZMod p))) ∧
      Subsingleton (CompletedTensor ℤ_[p] ℚ_[p] (ZMod p)) ∧
      spa ((Pair.powerBounded ℚ_[p]).completedTensor ℤ_[p] (Pair.discrete (ZMod p))).plus = ∅ := by
  have := subsingleton_completedTensor p
  exact ⟨Pair.completedTensor.isCompletedPushout _ _ rfl rfl, this,
    (spa_eq_empty_iff_subsingleton _ (Pair.isRingOfIntegralElements _)).mpr this⟩

/-- Neither fibre is zero: `ℚ_[p]` and `𝔽_p` are fields. -/
example : Nontrivial ℚ_[p] ∧ Nontrivial (ZMod p) := ⟨inferInstance, inferInstance⟩

end Padic

end TauCeti.Huber.DisjointFibresChecks
