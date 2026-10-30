/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Basic

/-!
# Fundamental weights

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `b` be a base of the root
system `LieAlgebra.IsKilling.rootSystem H`. The simple coroots `αᵢ^∨` form a basis of `H`
(`RootPairing.Base.toCoweightBasis`), and the **fundamental weights** `ϖᵢ` are the dual basis of
`Module.Dual K H`: `ϖᵢ (αⱼ^∨) = δᵢⱼ`.

The fundamental weights are the dominant integral weights generating all the others: a linear form
is dominant integral exactly when it is a natural combination of them, the coefficient of `ϖᵢ`
being its value on `αᵢ^∨`. The irreducible modules `L(ϖᵢ)` are the fundamental representations.

## Main definitions

* `TauCeti.fundamentalWeightBasis b`: the basis of `Module.Dual K H` dual to the simple coroots.

## Main results

* `TauCeti.fundamentalWeightBasis_apply_coroot_self` and
  `TauCeti.fundamentalWeightBasis_apply_coroot_of_ne`: `ϖᵢ (αⱼ^∨) = δᵢⱼ`.
* `TauCeti.fundamentalWeightBasis_repr`: the coordinates of a linear form in the fundamental
  weights are its values on the simple coroots.
* `TauCeti.isDominantIntegral_fundamentalWeightBasis`: each fundamental weight is dominant
  integral.
* `TauCeti.isDominantIntegral_iff_exists_eq_sum_fundamentalWeightBasis`: the dominant integral
  weights are the natural combinations of the fundamental weights.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.1.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (IsKilling.rootSystem H).Base)

/-- The **fundamental weights** of the base `b`, as the basis of `Module.Dual K H` dual to the basis
of simple coroots: `ϖᵢ (αⱼ^∨) = δᵢⱼ`. -/
noncomputable def fundamentalWeightBasis : Basis b.support K (Dual K H) :=
  open scoped Classical in b.toCoweightBasis.dualBasis

/-- **The defining property of the fundamental weights**, diagonal part: `ϖᵢ (αᵢ^∨) = 1`. -/
@[simp]
theorem fundamentalWeightBasis_apply_coroot_self (i : b.support) :
    fundamentalWeightBasis b i (IsKilling.coroot (i : Weight K H L)) = 1 := by
  classical
  rw [← IsKilling.rootSystem_coroot_apply]
  simp only [fundamentalWeightBasis, Basis.dualBasis_apply,
    RootPairing.Base.toCoweightBasis_repr_coroot, Finsupp.single_eq_same]

/-- **The defining property of the fundamental weights**, off-diagonal part: `ϖᵢ (αⱼ^∨) = 0` for
`j ≠ i`. -/
theorem fundamentalWeightBasis_apply_coroot_of_ne {i j : b.support} (hij : j ≠ i) :
    fundamentalWeightBasis b i (IsKilling.coroot (j : Weight K H L)) = 0 := by
  classical
  rw [← IsKilling.rootSystem_coroot_apply]
  simp only [fundamentalWeightBasis, Basis.dualBasis_apply,
    RootPairing.Base.toCoweightBasis_repr_coroot, Finsupp.single_eq_of_ne' hij]

/-- The coordinate of a linear form `lam` along the fundamental weight `ϖᵢ` is its value
`lam (αᵢ^∨)` on the corresponding simple coroot. -/
@[simp]
theorem fundamentalWeightBasis_repr (lam : Dual K H) (i : b.support) :
    (fundamentalWeightBasis b).repr lam i = lam (IsKilling.coroot (i : Weight K H L)) := by
  classical
  simp only [fundamentalWeightBasis, Basis.dualBasis_repr, RootPairing.Base.toCoweightBasis_apply,
    IsKilling.rootSystem_coroot_apply]

/-- A linear form on `H` is the combination of the fundamental weights with coefficients its values
on the simple coroots. -/
theorem sum_apply_coroot_smul_fundamentalWeightBasis (lam : Dual K H) :
    ∑ i : b.support, lam (IsKilling.coroot (i : Weight K H L)) • fundamentalWeightBasis b i =
      lam := by
  simpa only [fundamentalWeightBasis_repr] using (fundamentalWeightBasis b).sum_repr lam

variable {b}

/-- **The dominant integral weights are the natural combinations of the fundamental weights.** -/
theorem isDominantIntegral_iff_exists_eq_sum_fundamentalWeightBasis {lam : Dual K H} :
    IsDominantIntegral b lam ↔
      ∃ n : b.support → ℕ, lam = ∑ i, (n i : K) • fundamentalWeightBasis b i := by
  simp only [isDominantIntegral_iff, IsKilling.rootSystem_coroot_apply]
  constructor
  · intro hlam
    choose n hn using fun i : b.support => hlam i i.property
    refine ⟨n, ?_⟩
    conv_lhs => rw [← sum_apply_coroot_smul_fundamentalWeightBasis b lam]
    simp only [hn]
  · rintro ⟨n, rfl⟩ i hi
    refine ⟨n ⟨i, hi⟩, ?_⟩
    rw [LinearMap.sum_apply, Finset.sum_eq_single_of_mem ⟨i, hi⟩ (Finset.mem_univ _)
      fun j _ hj => ?_]
    · rw [LinearMap.smul_apply, fundamentalWeightBasis_apply_coroot_self, smul_eq_mul, mul_one]
    · rw [LinearMap.smul_apply, fundamentalWeightBasis_apply_coroot_of_ne b (Ne.symm hj),
        smul_zero]

/-- **Each fundamental weight is dominant integral.** -/
theorem isDominantIntegral_fundamentalWeightBasis (i : b.support) :
    IsDominantIntegral b (fundamentalWeightBasis b i) := by
  simp only [isDominantIntegral_iff, IsKilling.rootSystem_coroot_apply]
  intro j hj
  by_cases hji : (⟨j, hj⟩ : b.support) = i
  · exact ⟨1, by rw [← hji, fundamentalWeightBasis_apply_coroot_self, Nat.cast_one]⟩
  · exact ⟨0, by
      rw [fundamentalWeightBasis_apply_coroot_of_ne b hji, Nat.cast_zero]⟩

end TauCeti
