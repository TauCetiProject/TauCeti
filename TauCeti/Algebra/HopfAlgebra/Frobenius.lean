/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Existence

/-!
# Frobenius functionals from invariant integrals

A nonzero right invariant functional on a finite-dimensional Hopf algebra is a
Frobenius functional. Here right invariance means `(φ ⊗ id) Δ(x) = φ(x) 1`,
so this is the right-cointegral convention. Left invariant functionals give
Frobenius functionals as well.

A Frobenius functional on a finite-dimensional bialgebra pairs nontrivially with
both integral spaces: each has a unique element on which the functional is one.
For a right invariant functional, strong invariance gives a reconstruction formula
from the coproduct of its normalized left integral. In particular the antipode is
bijective. These statements assume a nonzero invariant functional.

Over a field, the existence of a nonzero right cointegral, proved in
`TauCeti.Algebra.HopfAlgebra.Cointegral.Existence`, removes this hypothesis: a
finite-dimensional Hopf algebra is a Frobenius algebra, its antipode is bijective, and its
spaces of left and right integrals and of left and right cointegrals are lines.

## Main declarations

* `TauCeti.HopfAlgebra.exists_isFrobeniusFunctional`: a finite-dimensional Hopf algebra over a
  field is Frobenius.
* `TauCeti.HopfAlgebra.antipode_bijective_of_finiteDimensional`: bijectivity of the antipode.
* `TauCeti.finrank_leftIntegral`, `TauCeti.finrank_rightIntegral`,
  `TauCeti.finrank_leftCointegrals`, `TauCeti.finrank_rightCointegrals`: the integral and
  cointegral spaces are one-dimensional.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Chapter 2.
* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for
  Hopf algebras*, Amer. J. Math. 91 (1969), 75–94.

The nondegeneracy input is the algebraic faithfulness theorem in
`TauCeti.Algebra.HopfAlgebra.Integral`.
-/

public section

open Coalgebra HopfAlgebra TauCeti
open scoped Coalgebra

namespace LinearMap

variable {k H : Type*} [Field k] [Ring H]

section Bialgebra

variable [Bialgebra k H] [FiniteDimensional k H] {φ : H →ₗ[k] k}

/-- The left integral pairing to one against a Frobenius functional exists uniquely.
No normalization of its counit is required. -/
theorem IsFrobeniusFunctional.existsUnique_leftIntegral_apply_eq_one
    (hφ : φ.IsFrobeniusFunctional) :
    ∃! t : leftIntegral k H, φ t = 1 := by
  obtain ⟨t, ht⟩ := hφ.isPerfPair.bijective_right.surjective (counit (R := k))
  have ht' (x : H) : φ (x * t) = counit (R := k) x :=
    DFunLike.congr_fun ht x
  have hmem : t ∈ leftIntegral k H := by
    rw [mem_leftIntegral_iff]
    intro x
    apply hφ.eq_of_forall_apply_mul_eq
    intro y
    simp [← mul_assoc, ht', mul_comm]
  have hone : φ t = 1 := by simpa using ht' 1
  refine ⟨⟨t, hmem⟩, hone, ?_⟩
  intro u hu
  apply Subtype.ext
  apply hφ.eq_of_forall_apply_mul_eq
  intro x
  simp [(mem_leftIntegral_iff.mp u.property) x, hu, ht']

/-- The right integral pairing to one against a Frobenius functional exists uniquely. -/
theorem IsFrobeniusFunctional.existsUnique_rightIntegral_apply_eq_one
    (hφ : φ.IsFrobeniusFunctional) :
    ∃! t : rightIntegral k H, φ t = 1 := by
  obtain ⟨t, ht⟩ := hφ.toDualEquiv.surjective (counit (R := k))
  have ht' (x : H) : φ (t * x) = counit (R := k) x := by
    simpa using DFunLike.congr_fun ht x
  have hmem : t ∈ rightIntegral k H := by
    rw [mem_rightIntegral_iff]
    intro x
    apply sub_eq_zero.mp
    apply hφ.eq_zero_of_forall_left
    intro y
    simp [sub_mul, mul_assoc, ht']
  have hone : φ t = 1 := by simpa using ht' 1
  refine ⟨⟨t, hmem⟩, hone, ?_⟩
  intro u hu
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hφ.eq_zero_of_forall_left
  intro x
  simp [sub_mul, (mem_rightIntegral_iff.mp u.property) x, hu, ht']

/-- A Frobenius functional identifies the left integral space with a line. -/
theorem IsFrobeniusFunctional.finrank_leftIntegral
    (hφ : φ.IsFrobeniusFunctional) : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨t, ht, _⟩ := hφ.existsUnique_leftIntegral_apply_eq_one
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  apply (finrank_eq_one_iff_of_ne_zero' t ht0).mpr
  intro u
  refine ⟨φ u, ?_⟩
  apply Subtype.ext
  apply hφ.eq_of_forall_apply_mul_eq
  intro x
  simp [(mem_leftIntegral_iff.mp t.property) x,
    (mem_leftIntegral_iff.mp u.property) x, ht, mul_comm]

/-- A Frobenius functional identifies the right integral space with a line. -/
theorem IsFrobeniusFunctional.finrank_rightIntegral
    (hφ : φ.IsFrobeniusFunctional) : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨t, ht, _⟩ := hφ.existsUnique_rightIntegral_apply_eq_one
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  apply (finrank_eq_one_iff_of_ne_zero' t ht0).mpr
  intro u
  refine ⟨φ u, ?_⟩
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hφ.eq_zero_of_forall_left
  intro x
  simp [sub_mul, (mem_rightIntegral_iff.mp t.property) x,
    (mem_rightIntegral_iff.mp u.property) x, ht, mul_comm]

end Bialgebra

section Hopf

variable [HopfAlgebra k H] {φ : H →ₗ[k] k}

/-- A nonzero right invariant functional on a finite-dimensional Hopf algebra
is a Frobenius functional. -/
theorem IsRightInvariantIntegral.isFrobeniusFunctional [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  .of_left fun _ hx => hφ.eq_zero_of_forall_mul_eq_zero h0 hx

/-- A nonzero left invariant functional on a finite-dimensional Hopf algebra
is a Frobenius functional. -/
theorem IsLeftInvariantIntegral.isFrobeniusFunctional [FiniteDimensional k H]
    (hφ : φ.IsLeftInvariantIntegral) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  .of_right fun _ hx => hφ.eq_zero_of_forall_mul_eq_zero h0 hx

/-- A nonzero right invariant functional makes the antipode surjective in finite
dimension, via the normalized left integral's reconstruction formula. -/
theorem IsRightInvariantIntegral.antipode_surjective [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) :
    Function.Surjective (antipode k : H → H) := by
  classical
  obtain ⟨t, ht, _⟩ :=
    (hφ.isFrobeniusFunctional h0).existsUnique_leftIntegral_apply_eq_one
  let r := ℛ k (t : H)
  intro x
  refine ⟨∑ i ∈ r.index, φ (x * r.left i) • r.right i, ?_⟩
  simpa only [map_sum, map_smul] using
    hφ.sum_apply_mul_smul_antipode t.property ht r x

/-- The antipode is bijective whenever a finite-dimensional Hopf algebra admits
a nonzero right invariant functional. -/
theorem IsRightInvariantIntegral.antipode_bijective [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) :
    Function.Bijective (antipode k : H → H) :=
  ⟨LinearMap.injective_iff_surjective.mpr (hφ.antipode_surjective h0),
    hφ.antipode_surjective h0⟩

end Hopf

end LinearMap

namespace TauCeti

section Field

variable {k H : Type*} [Field k] [Ring H] [_root_.HopfAlgebra k H] [FiniteDimensional k H]

variable (k H) in
/-- **Larson–Sweedler theorem**: a finite-dimensional Hopf algebra over a field is a Frobenius
algebra. A nonzero right cointegral is a Frobenius functional. -/
theorem HopfAlgebra.exists_isFrobeniusFunctional :
    ∃ φ : H →ₗ[k] k, φ.IsFrobeniusFunctional := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact ⟨φ, (LinearMap.isRightInvariantIntegral_iff.mpr
    ((isRightCointegral_def φ).mp hφ)).isFrobeniusFunctional h0⟩

variable (k H) in
/-- The antipode of a finite-dimensional Hopf algebra over a field is bijective. -/
theorem HopfAlgebra.antipode_bijective_of_finiteDimensional :
    Function.Bijective (antipode k : H → H) := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact (LinearMap.isRightInvariantIntegral_iff.mpr
    ((isRightCointegral_def φ).mp hφ)).antipode_bijective h0

variable (k H) in
/-- The left integrals of a finite-dimensional Hopf algebra over a field form a line. -/
theorem finrank_leftIntegral : Module.finrank k (leftIntegral k H) = 1 :=
  (HopfAlgebra.exists_isFrobeniusFunctional k H).choose_spec.finrank_leftIntegral

variable (k H) in
/-- The right integrals of a finite-dimensional Hopf algebra over a field form a line. -/
theorem finrank_rightIntegral : Module.finrank k (rightIntegral k H) = 1 :=
  (HopfAlgebra.exists_isFrobeniusFunctional k H).choose_spec.finrank_rightIntegral

variable (k H) in
/-- The right cointegrals of a finite-dimensional Hopf algebra over a field form a line. -/
theorem finrank_rightCointegrals : Module.finrank k (rightCointegrals k H) = 1 := by
  let e := (WithConv.linearEquiv k (Module.Dual k H)).symm
  have hmap : (rightCointegrals k H).map e.toLinearMap =
      rightIntegral k (ConvolutionDual k H) := by
    ext ψ
    rw [Submodule.mem_map_equiv, ← WithConv.toConv_ofConv ψ, toConv_mem_rightIntegral_iff]
    simp [e, mem_rightCointegrals]
  rw [← LinearEquiv.finrank_map_eq e, hmap, finrank_rightIntegral]

variable (k H) in
/-- The left cointegrals of a finite-dimensional Hopf algebra over a field form a line. -/
theorem finrank_leftCointegrals : Module.finrank k (leftCointegrals k H) = 1 := by
  let e := (WithConv.linearEquiv k (Module.Dual k H)).symm
  have hmap : (leftCointegrals k H).map e.toLinearMap =
      leftIntegral k (ConvolutionDual k H) := by
    ext ψ
    rw [Submodule.mem_map_equiv, ← WithConv.toConv_ofConv ψ, toConv_mem_leftIntegral_iff]
    simp [e, mem_leftCointegrals]
  rw [← LinearEquiv.finrank_map_eq e, hmap, finrank_leftIntegral]

end Field

end TauCeti
