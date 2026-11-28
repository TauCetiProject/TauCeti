/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Forms
import TauCeti.RingTheory.MvPolynomial.Ideal.Weighted

/-!
# Multiplicity of deep forms at orbit points

Deep forms have no low-depth terms after any twisted substitution. On a slice through a point
whose inverse translate has zero deep coordinates, this forces the specialized form to vanish
to at least the depth of the form, even when the shallow coordinates lie in a larger field.

The application to multiplicities at the unipotent orbit is from
`New.FrobeniusCycle.exists_le_weight_of_mem_deepForms` in
`New/UpperBound/ElementaryDivisors/Depth.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/UpperBound/ElementaryDivisors/Depth.lean
-/

public section

open MvPolynomial Matrix

namespace TauCeti.FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N k n : ℕ}
  {T : FrobeniusCycle W R N} {r d : ℕ} {F : Exponent N k n → R}

/-- After any translate of a deep form, substituting elements of `I` for the deep variables
sends the form into `I ^ d`. The shallow variables can be evaluated at arbitrary elements. -/
theorem aeval_twistedAction_mem_pow_of_mem_deepForms {A : Type*} [CommSemiring A] [Algebra R A]
    {I : Ideal A} {x : Fin k × ZMod N → A} (hF : F ∈ T.deepForms k n r d)
    (g : GL (Fin k) W) (hx : ∀ i, T.IsDeep r i → x i ∈ I) :
    aeval x (T.twistedAction g (formToMvPolynomial F)) ∈ I ^ d := by
  let w (i : Fin k × ZMod N) : ℕ := if T.IsDeep r i then 1 else 0
  have hw (i) : x i ∈ I ^ w i := by
    by_cases hi : T.IsDeep r i
    · simpa only [w, ite_eq_left hi, pow_one] using hx i hi
    · simp only [w, ite_eq_right hi, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  rw [T.twistedAction_formToMvPolynomial]
  refine aeval_mem_pow_of_le_weight hw fun β hβ ↦ ?_
  have hc := mem_support_iff.mp hβ
  by_cases hdeg : ∀ s, ∑ b, β (b, s) = n
  · have hweight : Finsupp.weight w β = T.depth r β := by
      rw [T.depth_apply, Finsupp.weight_apply]
      refine Finsupp.sum_congr fun i _ ↦ ?_
      by_cases hi : T.IsDeep r i
      · simp only [w, ite_eq_left hi, nsmul_one, Nat.cast_id]
      · simp only [w, ite_eq_right hi, nsmul_zero]
    rw [hweight]
    exact le_of_not_gt fun h ↦ hc <| (coeff_formToMvPolynomial _ ⟨β, hdeg⟩).trans
      (T.mem_deepForms_iff.mp hF g ⟨β, hdeg⟩ h)
  · exact (hc (coeff_formToMvPolynomial_eq_zero _ hdeg)).elim

/-- A polynomial substitution `x` specializes a deep form to a polynomial vanishing to order at
least `d` at `z`, provided the point it parametrizes at `z` is the `g`-translate of a point `u`
with zero deep coordinates. For a slice, `x` keeps the deep indeterminates and freezes the
shallow coordinates; the hypothesis is an equality of evaluations at the respective points. -/
theorem aeval_formToMvPolynomial_mem_pow_vanishingIdeal_of_mem_deepForms {A τ : Type*}
    [Field A] [Algebra R A] (hF : F ∈ T.deepForms k n r d)
    {x : Fin k × ZMod N → MvPolynomial τ A} {z : τ → A} (g : GL (Fin k) W)
    {u : Fin k × ZMod N → A} (hu : ∀ i, T.IsDeep r i → u i = 0)
    (hz : ((aeval z).restrictScalars R).comp (aeval x) = (aeval u).comp (T.twistedAction g)) :
    aeval x (formToMvPolynomial F) ∈ vanishingIdeal A {z} ^ d := by
  have hinv (p : MvPolynomial (Fin k × ZMod N) R) :
      T.twistedAction g (T.twistedAction g⁻¹ p) = p := by
    rw [← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]
  let y (i : Fin k × ZMod N) := aeval x (T.twistedAction g⁻¹ (X i))
  have hy : (aeval y : _ →ₐ[R] _) = (aeval x).comp (T.twistedAction g⁻¹) :=
    MvPolynomial.algHom_ext fun i ↦ by simp [y]
  have hI (i) (hi : T.IsDeep r i) : y i ∈ vanishingIdeal A {z} := by
    rw [mem_vanishingIdeal_singleton_iff]
    have he := DFunLike.congr_fun hz (T.twistedAction g⁻¹ (X i))
    simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hinv, aeval_X, hu i hi, y] using he
  have h := aeval_twistedAction_mem_pow_of_mem_deepForms hF g (x := y) hI
  rw [hy, AlgHom.comp_apply] at h
  simpa only [← AlgHom.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgHom.one_apply] using h

end TauCeti.FrobeniusCycle
