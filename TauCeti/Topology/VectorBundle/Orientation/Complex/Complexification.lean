/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complexification
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The Euler class of the complexification of a real bundle

Let `E → B` be a complex vector bundle of complex rank `r + 1`. A fibrewise conjugate-linear
isomorphism, continuous on total spaces, multiplies the Euler class `e(E_ℝ)` by `(-1) ^ (r + 1)`
(`TauCeti.complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise`).

For the complexification `fun b ↦ ℂ ⊗[ℝ] E b` of a real vector bundle `E` of real rank `r + 1`,
the fibrewise conjugation `z ⊗ v ↦ conj z ⊗ v` is such an isomorphism of the bundle with itself.
So `e(E_ℂ) = (-1) ^ (r + 1) e(E_ℂ)`
(`TauCeti.complexEulerClass_complexification_eq_neg_one_pow_smul`), and for odd real rank the Euler
class of the complexification is `2`-torsion
(`TauCeti.two_smul_complexEulerClass_complexification_eq_zero`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §15 (complexification and the `2`-torsion of the odd Chern classes of
  `E ⊗ ℂ`).
-/

public section

noncomputable section

open Bundle Module
open scoped TensorProduct

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {r : ℕ}

/-! ### The complexification of a real bundle -/

section Complexification

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ b, TopologicalSpace (ℂ ⊗[ℝ] E b)]
  [∀ b, IsComplexificationTopology (E b)]

variable [FiniteDimensional ℝ F]

/-- **The Euler class of a complexification is fixed up to sign by conjugation.** For a real vector
bundle `E` of real rank `r + 1`, so that the complexification `E_ℂ` has complex rank `r + 1`
(`TauCeti.Complexification.finrank_complex`), `e(E_ℂ) = (-1) ^ (r + 1) e(E_ℂ)`. -/
theorem complexEulerClass_complexification_eq_neg_one_pow_smul
    (hF : finrank ℂ (Complexification F) = r + 1) :
    complexEulerClass (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b) hF =
      (-1 : ℤ) ^ (r + 1) • complexEulerClass (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b) hF := by
  -- Each fibre is linearly homeomorphic to `F`, so negation on it is continuous.
  have (b : B) : ContinuousNeg (E b) :=
    let e := VectorBundle.continuousLinearEquivAt ℝ F E b
    e.toHomeomorph.isInducing.continuousNeg (map_neg e)
  exact complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise _ _
    (φ := fun b ↦ tmulConjCLE (E b)) ((tmulConjHomeomorph F E).continuous.congr fun v ↦ by
      rw [tmulConjHomeomorph_apply, coe_tmulConjCLE])

/-- **The Euler class of the complexification of a real bundle of odd rank is `2`-torsion**: for
`r + 1` odd, `2 e(E_ℂ) = 0`. -/
theorem two_smul_complexEulerClass_complexification_eq_zero
    (hF : finrank ℂ (Complexification F) = r + 1) (hr : Odd (r + 1)) :
    (2 : ℤ) • complexEulerClass (Complexification F) (fun b ↦ ℂ ⊗[ℝ] E b) hF = 0 := by
  have h := complexEulerClass_complexification_eq_neg_one_pow_smul (E := E) hF
  rw [hr.neg_one_pow, neg_one_zsmul, eq_neg_iff_add_eq_zero] at h
  rw [two_zsmul, h]

end Complexification

end TauCeti
