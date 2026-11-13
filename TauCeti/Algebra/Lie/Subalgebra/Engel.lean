/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.EngelSubalgebra
public import Mathlib.LinearAlgebra.Semisimple
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import TauCeti.Algebra.Lie.OfAssociative
import TauCeti.LinearAlgebra.End.CommutingCubic

/-!
# Nilpotent subalgebras and Engel subalgebras

A nilpotent Lie subalgebra lies in the Engel subalgebra of each of its elements. This is the
converse of Mathlib's `LieSubalgebra.isNilpotent_of_forall_le_engel`, and it holds over any
commutative ring.

The Engel subalgebra of `x` is the generalized eigenspace of `ad x` at `0`. When `ad x` is
semisimple this generalized eigenspace is the eigenspace, so the Engel subalgebra of `x` is the
centralizer of `x`.

For commuting elements `x`, `y` of a Lie subalgebra of an associative algebra with `x * x = 1` and
`y * y = -1`, the operators `ad x` and `ad y` satisfy the cubics `(ad x)³ = 4 ad x` and
`(ad y)³ = -4 ad y` (`LieSubalgebra.ad_pow_three_eq_smul_ad`). These force every element of the
Engel subalgebra of `x + y` to commute with `x` and with `y`
(`Module.End.apply_eq_zero_and_apply_eq_zero_of_pow_add_apply_eq_zero`).

## Main results

* `LieSubalgebra.le_engel_of_isNilpotent`: a nilpotent subalgebra lies in the Engel subalgebra of
  each of its elements.
* `LieSubalgebra.mem_engel_iff_lie_eq_zero`: if `ad x` is semisimple, then `y` lies in the Engel
  subalgebra of `x` exactly when `⁅x, y⁆ = 0`.
* `LieSubalgebra.lie_eq_zero_and_lie_eq_zero_of_mem_engel_add`: for commuting `x`, `y` with
  `x * x = 1` and `y * y = -1`, every element of the Engel subalgebra of `x + y` commutes with `x`
  and `y`.
-/

public section

namespace LieSubalgebra

open LieAlgebra LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A nilpotent subalgebra lies in the Engel subalgebra of each of its elements. -/
theorem le_engel_of_isNilpotent (U : LieSubalgebra R L) [LieRing.IsNilpotent U] (h : U) :
    U ≤ engel R (h : L) := by
  intro y hy
  have hy₀ : y ∈ rootSpace U (0 : U → R) := toLieSubmodule_le_rootSpace_zero R L U hy
  have := genWeightSpace_le_genWeightSpaceOf L h (0 : U → R) hy₀
  rw [LieModule.mem_genWeightSpaceOf] at this
  simpa only [mem_engel_iff, zero_smul, sub_zero, LieAlgebra.ad, LieSubalgebra.toEnd_eq,
    Pi.zero_apply] using this

/-- If the adjoint action of `x` is semisimple, then the Engel subalgebra of `x` is the centralizer
of `x`: `y` lies in it exactly when `⁅x, y⁆ = 0`. -/
theorem mem_engel_iff_lie_eq_zero {x y : L} (hx : (ad R L x).IsFinitelySemisimple) :
    y ∈ engel R x ↔ ⁅x, y⁆ = 0 := by
  have h := hx.maxGenEigenspace_eq_eigenspace 0
  refine ⟨fun hy ↦ ?_, fun hy ↦ (mem_engel_iff R x y).2 ⟨1, by simpa using hy⟩⟩
  obtain ⟨n, hn⟩ := (mem_engel_iff R x y).1 hy
  have hmem : y ∈ (ad R L x).maxGenEigenspace 0 :=
    (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨n, by simpa using hn⟩
  rw [h, Module.End.mem_eigenspace_iff, zero_smul] at hmem
  simpa using hmem

end LieSubalgebra

namespace LieSubalgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [Field R] [NeZero (2 : R)] [Ring A] [Algebra R A]

/-- **The Engel subalgebra of `x + y` for commuting square roots of `1` and `-1`.** Let `x`, `y` be
commuting elements of a Lie subalgebra `K` of an associative algebra with `x * x = 1` and
`y * y = -1`. Then every element of `K` killed by a power of `ad (x + y)` commutes with `x` and
with `y`. -/
theorem lie_eq_zero_and_lie_eq_zero_of_mem_engel_add {K : LieSubalgebra R A} {x y z : K}
    (hx : (x : A) * x = 1) (hy : (y : A) * y = -1) (hxy : ⁅x, y⁆ = 0)
    (hz : z ∈ LieSubalgebra.engel R (x + y)) :
    ⁅x, z⁆ = 0 ∧ ⁅y, z⁆ = 0 := by
  have hN := ad_pow_three_eq_smul_ad (u := x) (c := (1 : R)) (by rw [hx, one_smul])
  have hP := ad_pow_three_eq_smul_ad (u := y) (c := (-1 : R)) (by rw [hy, neg_smul, one_smul])
  rw [mul_one] at hN
  rw [mul_neg_one, neg_smul] at hP
  have hNP : Commute (LieAlgebra.ad R K x) (LieAlgebra.ad R K y) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, hxy, map_zero]
  obtain ⟨n, hn⟩ := (mem_engel_iff R (x + y) z).1 hz
  rw [map_add] at hn
  simpa only [LieAlgebra.ad_apply] using
    Module.End.apply_eq_zero_and_apply_eq_zero_of_pow_add_apply_eq_zero hN hP hNP n hn

end LieSubalgebra
