/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Prime-power decomposition and reduction of `SL(n, ℤ/Nℤ)`

This file develops the prime-power decomposition
`SL(n, ℤ/Nℤ) ≃* ∀ p : N.primeFactors, SL(n, ℤ/p^{v_p(N)}ℤ)` for `N ≠ 0` and surjectivity of
the reduction map `SL₂(ℤ/Nℤ) →* SL₂(ℤ/Mℤ)` whenever `M ∣ N` (exact cardinalities live in
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Card`).

The `p`-group/solvability structure of congruence kernels is in
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.CongruenceKernel`, signed-quotient orders
are in `TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.SignedQuotient`, and prime-field
`PSL₂(𝔽_p)` orders are in `TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.ZMod`.

## References

* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton University
  Press, 1971, §1.6.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, §1.2 and Exercise 1.2.3.
-/

public section

open Matrix

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-! ### Prime-power decomposition and reduction modulo divisors -/

/-- For `N ≠ 0`, `SL(n, ℤ/Nℤ)` decomposes as the product of `SL(n, ℤ/p^{v_p(N)}ℤ)` over the prime
factors of `N`. -/
noncomputable def zmodEquivPi (n : Type*) [Fintype n] [DecidableEq n] {N : ℕ} (hN : N ≠ 0) :
    SpecialLinearGroup n (ZMod N) ≃*
      ∀ p : N.primeFactors, SpecialLinearGroup n (ZMod (p ^ N.factorization p)) :=
  (mapEquiv n (ZMod.equivPi N hN)).trans
    (piEquiv n fun p : N.primeFactors ↦ ZMod (p ^ N.factorization p))

/-- The `p`-th component of `zmodEquivPi n hN A` is reduction modulo `p ^ N.factorization p`. -/
@[simp]
theorem zmodEquivPi_apply {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ} (hN : N ≠ 0)
    (A : SpecialLinearGroup n (ZMod N)) (p : N.primeFactors) :
    zmodEquivPi n hN A p =
      map (ZMod.castHom (Nat.ordProj_dvd N p) (ZMod (p ^ N.factorization p))) A := by
  ext i j
  exact congrArg (· (A i j)) <| Subsingleton.elim
    ((Pi.evalRingHom (fun q : N.primeFactors ↦ ZMod (q ^ N.factorization q)) p).comp
      (ZMod.equivPi N hN).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd N p) (ZMod (p ^ N.factorization p)))

/-- **Strong approximation between finite levels**: whenever `M ∣ N`, the natural reduction
`SL₂(ℤ/Nℤ) →* SL₂(ℤ/Mℤ)` is surjective. -/
theorem map_zmod_castHom_surjective {M N : ℕ} (h : M ∣ N) :
    Function.Surjective
      (map (ZMod.castHom h (ZMod M)) : SL(2, ZMod N) →* SL(2, ZMod M)) := fun A ↦ by
  obtain ⟨γ, rfl⟩ := map_intCast_zmod_surjective (d := M) A
  refine ⟨map (Int.castRingHom (ZMod N)) γ, ?_⟩
  rw [← MonoidHom.comp_apply, map_comp_map,
    RingHom.ext_int ((ZMod.castHom h (ZMod M)).comp (Int.castRingHom (ZMod N)))
      (Int.castRingHom (ZMod M))]

end Matrix.SpecialLinearGroup
