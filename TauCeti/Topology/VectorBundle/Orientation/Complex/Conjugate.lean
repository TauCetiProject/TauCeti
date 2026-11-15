/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.FiniteDimensional
public import TauCeti.Topology.VectorBundle.Complexification
public import TauCeti.Topology.VectorBundle.Conjugate
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian

/-!
# The Euler class of the conjugate, the dual and the complexification

Let `E → B` be a complex vector bundle of complex rank `r + 1`. A fibrewise conjugate-linear
isomorphism, continuous on total spaces, multiplies the Euler class `e(E_ℝ)` by `(-1) ^ (r + 1)`
(`TauCeti.complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise`). This file applies that law
to three bundles built from `E`, each with an explicit conjugate-linear identification.

* The conjugate bundle `TauCeti.ConjugateBundle E`, through the identity of total spaces:
  `e(conj E) = (-1) ^ (r + 1) e(E)` (`TauCeti.complexEulerClass_conjugateBundle`); for a trivial
  bundle both sides vanish (`TauCeti.complexEulerClass_conjugateBundle_trivial`).
* The dual bundle `fun b ↦ StrongDual ℂ (E b)`, when the fibres carry a Hermitian inner product
  whose norm is continuous on the total space (`TauCeti.ContinuousFiberNorm`): the fibrewise Riesz
  map `v ↦ ⟪v, ·⟫` (`InnerProductSpace.toDual`) is conjugate linear, so
  `e(E*) = (-1) ^ (r + 1) e(E)` (`TauCeti.complexEulerClass_dual_of_hermitian`). For a line bundle
  this is `e(L*) = -e(L)` (`TauCeti.complexEulerClass_dual_eq_neg_of_finrank_eq_one`).
* The complexification `fun b ↦ ℂ ⊗[ℝ] E b` of a real vector bundle `E` of real rank `r + 1`, whose
  fibrewise conjugation `z ⊗ v ↦ conj z ⊗ v` is conjugate linear:
  `e(E_ℂ) = (-1) ^ (r + 1) e(E_ℂ)`
  (`TauCeti.complexEulerClass_complexification_eq_neg_one_pow_smul`), so for odd real rank the
  Euler class of the complexification is `2`-torsion
  (`TauCeti.two_smul_complexEulerClass_complexification_eq_zero`).

The Hermitian metric in the dual statement is a hypothesis: it supplies the conjugate-linear
isomorphism `E ≅ E*`, and no metric is chosen.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14, Lemma 14.9 (the conjugate bundle and the dual of a Hermitian bundle) and
  §15 (complexification and the `2`-torsion of the odd Chern classes of `E ⊗ ℂ`).
-/

public section

noncomputable section

open Bundle FiberBundle Module Set
open scoped InnerProductSpace TensorProduct

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
theorem complexEulerClass_conjugateBundle (hF : finrank ℂ F = r + 1) :
    complexEulerClass (Conjugate F) (ConjugateBundle E) (Conjugate.finrank_complex.trans hF) =
      (-1 : ℤ) ^ (r + 1) • complexEulerClass F E hF :=
  complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise hF _
    (φ := fun b ↦ (Conjugate.toConjL : E b ≃L⋆[ℂ] Conjugate (E b)).symm)
    ((ConjugateBundle.toConjHomeomorph F E).symm.continuous.congr fun v ↦ by
      rw [ConjugateBundle.toConjHomeomorph_symm_apply, Conjugate.coe_toConjL_symm])

/-- **The Euler class of the conjugate of a complex line bundle is the negative**:
`e(conj L) = -e(L)`. -/
theorem complexEulerClass_conjugateBundle_eq_neg_of_finrank_eq_one (hF : finrank ℂ F = 0 + 1) :
    complexEulerClass (Conjugate F) (ConjugateBundle E) (Conjugate.finrank_complex.trans hF) =
      -complexEulerClass F E hF := by
  rw [complexEulerClass_conjugateBundle hF, pow_one, neg_one_zsmul]

end Conjugate

/-! ### The dual of a Hermitian bundle -/

section Dual

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℂ (E b)] [FiberBundle F E] [VectorBundle ℂ F E]

variable [ContinuousFiberNorm F E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [∀ b, NormedSpace ℝ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]

/-- **The Euler class of the dual of a Hermitian bundle.** For a complex vector bundle `E` of
complex rank `r + 1` whose fibres carry a Hermitian inner product with continuous norm, the dual
bundle `E*` has `e(E*) = (-1) ^ (r + 1) e(E)`. -/
theorem complexEulerClass_dual_of_hermitian (hF : finrank ℂ F = r + 1) :
    complexEulerClass (StrongDual ℂ F) (fun b ↦ StrongDual ℂ (E b))
        (finrank_strongDual.trans hF) =
      (-1 : ℤ) ^ (r + 1) • complexEulerClass F E hF := by
  have h := complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise
    (finrank_strongDual.trans hF) hF (φ := bundleToDual F E ℂ) (continuous_bundleToDual ℂ)
  rw [h, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- **The Euler class of the dual of a Hermitian line bundle is the negative**:
`e(L*) = -e(L)`. -/
theorem complexEulerClass_dual_eq_neg_of_finrank_eq_one (hF : finrank ℂ F = 0 + 1) :
    complexEulerClass (StrongDual ℂ F) (fun b ↦ StrongDual ℂ (E b))
        (finrank_strongDual.trans hF) =
      -complexEulerClass F E hF := by
  rw [complexEulerClass_dual_of_hermitian hF, pow_one, neg_one_zsmul]

end Dual

/-! ### The complexification of a real bundle -/

section Complexification

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ b, TopologicalSpace (ℂ ⊗[ℝ] E b)]
  [∀ b, IsComplexificationTopology (E b)]

variable [FiniteDimensional ℝ F]

/-- **The Euler class of a complexification is fixed up to sign by conjugation.** For a real vector
bundle `E` of real rank `r + 1`, the complexification `E_ℂ` satisfies
`e(E_ℂ) = (-1) ^ (r + 1) e(E_ℂ)`. -/
theorem complexEulerClass_complexification_eq_neg_one_pow_smul (hF : finrank ℝ F = r + 1) :
    complexEulerClass (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b)
        (Complexification.finrank_complex.trans hF) =
      (-1 : ℤ) ^ (r + 1) •
        complexEulerClass (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b)
          (Complexification.finrank_complex.trans hF) := by
  -- Each fibre is linearly homeomorphic to `F`, so negation on it is continuous.
  have (b : B) : ContinuousNeg (E b) :=
    let e := VectorBundle.continuousLinearEquivAt ℝ F E b
    e.toHomeomorph.isInducing.continuousNeg (map_neg e)
  exact complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise _ _
    (φ := fun b ↦ tmulConjCLE (E b)) ((tmulConjHomeomorph F E).continuous.congr fun v ↦ by
      rw [tmulConjHomeomorph_apply, coe_tmulConjCLE])

/-- **The Euler class of the complexification of a real bundle of odd rank is `2`-torsion**: for
`r + 1` odd, `2 e(E_ℂ) = 0`. -/
theorem two_smul_complexEulerClass_complexification_eq_zero (hF : finrank ℝ F = r + 1)
    (hr : Odd (r + 1)) :
    (2 : ℤ) • complexEulerClass (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b)
        (Complexification.finrank_complex.trans hF) = 0 := by
  have h := complexEulerClass_complexification_eq_neg_one_pow_smul (E := E) hF
  rw [hr.neg_one_pow, neg_one_zsmul, eq_neg_iff_add_eq_zero] at h
  rw [two_zsmul, h]

end Complexification

/-! ### Trivial bundles -/

section Trivial

variable (B) {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]

/-- The conjugate of a trivial complex vector bundle has zero Euler class, as the trivial bundle
does. -/
@[simp]
theorem complexEulerClass_conjugateBundle_trivial (hF : finrank ℂ F = r + 1) :
    complexEulerClass (Conjugate F) (ConjugateBundle (Bundle.Trivial B F))
      (Conjugate.finrank_complex.trans hF) = 0 := by
  rw [complexEulerClass_conjugateBundle hF, complexEulerClass_trivial]
  exact zsmul_zero _

end Trivial

end TauCeti
