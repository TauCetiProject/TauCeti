/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isomorphism.Basic

/-!
# Integer pairings under Cartan-matching root bijections

A bijection between simple-root supports preserving the Cartan matrix determines the root-index
bijection `RootPairing.Base.indexEquivOfCartanMatrixEq`. This file proves that it preserves every
integer root-coroot pairing. The coefficient rings may be different characteristic-zero domains,
and neither the roots nor the coroots need span their ambient modules. This allows comparison of
a component of a reductive root datum with a semisimple model without discarding the central
lattice directions.

The comparison uses the simple-root coordinates of `RootPairing.Base.rootCoefficients` and the
column reflections of `Matrix.columnReflection`. Pairings with simple coroots read the corresponding
Cartan columns; reflection induction then determines all pairings.

## Main results

* `RootPairing.Base.indexEquivOfCartanMatrixEq_reflectionPerm`: compatibility with simple
  reflections.
* `RootPairing.Base.indexEquivOfCartanMatrixEq_reflectionPerm_self`: compatibility with opposition.
* `RootPairing.Base.pairingIn_indexEquivOfCartanMatrixEq`: preservation of all integer pairings.

## References

Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI, §1: bases and the
Cartan-matrix isomorphism theorem.
-/

public section

namespace RootPairing.Base

variable {ι R M N ι₂ R₂ M₂ N₂ : Type*}
  [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [CommRing R₂] [IsDomain R₂] [CharZero R₂]
  [AddCommGroup M₂] [Module R₂ M₂] [AddCommGroup N₂] [Module R₂ N₂]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  {P₂ : RootPairing ι₂ R₂ M₂ N₂} [Finite ι₂] [P₂.IsCrystallographic] [P₂.IsReduced]
  (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
  (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j)

/-- The Cartan-matching root bijection intertwines the reflections at corresponding simple
roots. -/
@[simp]
theorem indexEquivOfCartanMatrixEq_reflectionPerm (i : b.support) (j : ι) :
    b.indexEquivOfCartanMatrixEq b₂ e he (P.reflectionPerm i j) =
      P₂.reflectionPerm (e i) (b.indexEquivOfCartanMatrixEq b₂ e he j) := by
  classical
  apply b₂.rootCoefficients_injective
  rw [rootCoefficients_indexEquivOfCartanMatrixEq,
    ← b₂.coefficientReflection_rootCoefficients (e i),
    rootCoefficients_indexEquivOfCartanMatrixEq, ← b.coefficientReflection_rootCoefficients i]
  have h := b.cartanMatrix.columnReflection_comp_equiv b.cartanMatrix_apply_same
    b₂.cartanMatrix_apply_same e.symm
    (fun u v ↦ by simpa using he (e.symm u) (e.symm v)) (e i) (b.rootCoefficients j)
  simpa only [Equiv.symm_apply_apply] using h.symm

/-- The Cartan-matching root bijection sends the negative of a root to the negative of its
image, using the ring-independent reflection-permutation description of opposition. -/
@[simp]
theorem indexEquivOfCartanMatrixEq_reflectionPerm_self (i : ι) :
    b.indexEquivOfCartanMatrixEq b₂ e he (P.reflectionPerm i i) =
      P₂.reflectionPerm (b.indexEquivOfCartanMatrixEq b₂ e he i)
        (b.indexEquivOfCartanMatrixEq b₂ e he i) := by
  apply b₂.rootCoefficients_injective
  simp only [rootCoefficients_indexEquivOfCartanMatrixEq, rootCoefficients_reflectionPerm_self]
  rfl

/-- The Cartan-matching root bijection preserves pairings with simple coroots. -/
private lemma pairingIn_indexEquivOfCartanMatrixEq_support (i : ι) (j : b.support) :
    P₂.pairingIn ℤ (b.indexEquivOfCartanMatrixEq b₂ e he i)
        (b.indexEquivOfCartanMatrixEq b₂ e he j) = P.pairingIn ℤ i j := by
  rw [indexEquivOfCartanMatrixEq_apply_support, b₂.pairingIn_eq_sum_rootCoefficients,
    b.pairingIn_eq_sum_rootCoefficients, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [rootCoefficients_indexEquivOfCartanMatrixEq]
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, ← cartanMatrixIn_def] using
    congrArg (b.rootCoefficients i k * ·) (he k j)

/-- A Cartan-matrix-preserving bijection between simple-root supports preserves every integer
root-coroot pairing under its induced root-index equivalence. The rings are independent and the
root and coroot spans may be proper submodules. -/
@[simp]
theorem pairingIn_indexEquivOfCartanMatrixEq (i j : ι) :
    P₂.pairingIn ℤ (b.indexEquivOfCartanMatrixEq b₂ e he i)
        (b.indexEquivOfCartanMatrixEq b₂ e he j) = P.pairingIn ℤ i j := by
  -- Quantifying over the root index lets a reflection move from the coroot to the root.
  refine b.induction_reflect j (p := fun j ↦ ∀ i,
    P₂.pairingIn ℤ (b.indexEquivOfCartanMatrixEq b₂ e he i)
      (b.indexEquivOfCartanMatrixEq b₂ e he j) = P.pairingIn ℤ i j) ?_ ?_ ?_ i
  · intro j hj i
    simp only [indexEquivOfCartanMatrixEq_reflectionPerm_self,
      RootPairing.pairingIn_reflectionPerm_self_right, hj]
  · intro j hj i
    exact pairingIn_indexEquivOfCartanMatrixEq_support b b₂ e he i ⟨j, hj⟩
  · intro j k hj hk i
    rw [indexEquivOfCartanMatrixEq_reflectionPerm b b₂ e he ⟨k, hk⟩,
      RootPairing.pairingIn_reflectionPerm,
      ← indexEquivOfCartanMatrixEq_reflectionPerm b b₂ e he ⟨k, hk⟩, hj,
      RootPairing.pairingIn_reflectionPerm]

end RootPairing.Base
