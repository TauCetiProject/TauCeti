/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# The integral weights of the roots relative to a base

Let `b` be a base of a finite crystallographic root system `P`. A root `αⱼ` determines the integral
family `k ↦ ⟨αⱼ, αₖ∨⟩` indexed by the simple roots, its weight. The weight of a simple root `αᵢ` is
the `i`-th row of the Cartan matrix, and the simple reflection `sᵢ` acts on weights by
`χ ↦ χ - χ i • b.cartanMatrix.row i`. Since every root is obtained from a simple root by simple
reflections, a property of integral weights can be propagated from the rows of the Cartan matrix to
the weights of all roots. This is how the weight spaces of a Lie algebra presented by Serre's
relations are compared at all the roots, starting from the simple ones.

## Main results

* `RootPairing.pairingIn_reflectionPerm_left_eq_sub`: the action of a reflection on the pairings of
  a root.
* `RootPairing.Base.linearIndependent_cartanMatrix_row`: the rows of the Cartan matrix are linearly
  independent over `ℤ`.
* `RootPairing.Base.induction_pairingIn_reflection`: the induction principle on weights.

## References

* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972], §10.3
-/

public section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- A reflection acts on the pairings of a root by
`⟨sᵢ αⱼ, αₖ∨⟩ = ⟨αⱼ, αₖ∨⟩ - ⟨αⱼ, αᵢ∨⟩ * ⟨αᵢ, αₖ∨⟩`. -/
theorem RootPairing.pairingIn_reflectionPerm_left_eq_sub (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι) :
    P.pairingIn S (P.reflectionPerm i j) k =
      P.pairingIn S j k - P.pairingIn S j i * P.pairingIn S i k := by
  apply FaithfulSMul.algebraMap_injective S R
  simp only [algebraMap_pairingIn, map_sub, map_mul]
  rw [← P.root_coroot_eq_pairing (P.reflectionPerm i j) k, P.root_reflectionPerm,
    P.reflection_apply_root]
  simp

namespace RootPairing.Base

variable [P.IsCrystallographic] [CharZero R] [Finite ι] [IsDomain R]

/-- The rows of the Cartan matrix of a base of a finite crystallographic root system are linearly
independent over `ℤ`. -/
theorem linearIndependent_cartanMatrix_row [P.IsRootSystem] (b : P.Base) :
    LinearIndependent ℤ b.cartanMatrix.row := by
  classical
  refine b.cartanMatrix.linearIndependent_rows_of_det_ne_zero ?_
  rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

/-- **Induction on the weights of the roots.** For a base of a finite reduced crystallographic root
pairing, a property of integral weights that holds at the rows of the Cartan matrix (the weights of
the simple roots) and is stable under the simple reflections holds at the weight of every root. -/
theorem induction_pairingIn_reflection [P.IsReduced] (b : P.Base) {Q : (b.support → ℤ) → Prop}
    (hsimple : ∀ i : b.support, Q (b.cartanMatrix.row i))
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (j : ι) : Q fun k : b.support ↦ P.pairingIn ℤ j k := by
  let w (j : ι) : b.support → ℤ := fun k ↦ P.pairingIn ℤ j k
  have hrow (i : b.support) : w i = b.cartanMatrix.row i := by
    funext k
    simp [w, cartanMatrixIn_def]
  have hreflect (i : b.support) (j : ι) :
      w (P.reflectionPerm i j) = w j - w j i • b.cartanMatrix.row i := by
    funext k
    rw [Pi.sub_apply, Pi.smul_apply, ← hrow, smul_eq_mul]
    exact P.pairingIn_reflectionPerm_left_eq_sub ℤ i j k
  have hneg (i : ι) : w (P.reflectionPerm i i) = -w i := by
    funext k
    simp [w]
  -- Negation is not a simple reflection in general, so both signs have to be carried along.
  suffices h : Q (w j) ∧ Q (-w j) from h.1
  refine b.induction_reflect j (p := fun j ↦ Q (w j) ∧ Q (-w j)) ?_ ?_ ?_
  · rintro i ⟨h₁, h₂⟩
    rw [hneg, neg_neg]
    exact ⟨h₂, h₁⟩
  · intro i hi
    have hsi := hrow ⟨i, hi⟩
    refine ⟨hsi ▸ hsimple _, ?_⟩
    rw [← hneg, hreflect ⟨i, hi⟩ i, hsi]
    exact hrefl _ _ (hsimple _)
  · rintro i l ⟨h₁, h₂⟩ hl
    rw [hreflect ⟨l, hl⟩ i]
    refine ⟨hrefl _ _ h₁, ?_⟩
    have hsub : -(w i - w i ⟨l, hl⟩ • b.cartanMatrix.row ⟨l, hl⟩) =
        -w i - (-w i) ⟨l, hl⟩ • b.cartanMatrix.row ⟨l, hl⟩ := by
      funext k
      simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact hsub ▸ hrefl _ _ h₂

end RootPairing.Base
