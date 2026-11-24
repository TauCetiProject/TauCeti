/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Conjugate
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The Euler class of the conjugate bundle

Let `E → B` be a complex vector bundle of complex rank `r + 1`. A fibrewise conjugate-linear
isomorphism, continuous on total spaces, multiplies the Euler class `e(E_ℝ)` by `(-1) ^ (r + 1)`
(`TauCeti.complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise`).

For the conjugate bundle `TauCeti.ConjugateBundle E` the identity of total spaces is such an
isomorphism, so `e(conj E) = (-1) ^ (r + 1) e(E)` (`TauCeti.complexEulerClass_conjugateBundle`),
and `e(conj L) = -e(L)` for a line bundle
(`TauCeti.complexEulerClass_conjugateBundle_eq_neg_of_finrank_eq_one`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14, Lemma 14.9 (the conjugate bundle).
-/

public section

noncomputable section

open Bundle Module

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {r : ℕ}

/-! ### The conjugate bundle -/

section Conjugate

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]

/-- **The Euler class of the conjugate bundle.** For a complex vector bundle `E` of complex rank
`r + 1`, `e(conj E) = (-1) ^ (r + 1) e(E)`. -/
@[simp]
theorem complexEulerClass_conjugateBundle (hF : finrank ℂ (Conjugate F) = r + 1) :
    complexEulerClass (Conjugate F) (ConjugateBundle E) hF =
      (-1 : ℤ) ^ (r + 1) • complexEulerClass F E (Conjugate.finrank_complex.symm.trans hF) :=
  complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise _ hF
    (φ := fun b ↦ (Conjugate.toConjL : E b ≃L⋆[ℂ] Conjugate (E b)).symm)
    ((ConjugateBundle.toConjHomeomorph F E).symm.continuous.congr fun v ↦ by
      rw [ConjugateBundle.toConjHomeomorph_symm_apply, Conjugate.coe_toConjL_symm])

/-- **The Euler class of the conjugate of a complex line bundle is the negative**:
`e(conj L) = -e(L)`. -/
theorem complexEulerClass_conjugateBundle_eq_neg_of_finrank_eq_one
    (hF : finrank ℂ (Conjugate F) = 0 + 1) :
    complexEulerClass (Conjugate F) (ConjugateBundle E) hF =
      -complexEulerClass F E (Conjugate.finrank_complex.symm.trans hF) := by
  rw [complexEulerClass_conjugateBundle hF, pow_one, neg_one_zsmul]

end Conjugate

end TauCeti
