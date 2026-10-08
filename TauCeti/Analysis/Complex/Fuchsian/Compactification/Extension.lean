/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Meromorphic

/-!
# Extension of invariant meromorphic functions to the compactified quotient

A meromorphic function on the upper half-plane may have interior poles. If it is invariant
under a discrete Fuchsian group, holomorphic at sufficiently large heights in a normalized
coordinate for each cusp, and satisfies an exponential growth bound there, it descends to a
meromorphic function on the compactified quotient.

The construction reuses `Subgroup.existsUnique_meromorphicAt_quotientMk` on the ordinary orbit
quotient and the explicit compactified carrier. It assigns zero at the adjoined cusps: meromorphy
and order depend only on the punctured germ, so
these point values do not affect either conclusion. The order bounds use the width of the
chosen normalized cusp datum; growth at rate `2πk / w` gives order at least `-k`.

## Main declarations

* `TauCeti.Fuchsian.meromorphicAt_of_forall_isBigO`: meromorphy of a function on the compactified
  quotient from its meromorphic pullback and cusp growth.
* `TauCeti.Fuchsian.exists_meromorphicAt_comp_ofQuotient`: descent and extension of an invariant
  meromorphic function with controlled growth at every cusp.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.4–2.5.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.

The analytic cusp criterion reuses Mathlib's periodic cusp function and removable singularity
results, through `TauCeti.Subgroup.CuspDatum.meromorphicAt_cuspExtension_zero`.
-/

public noncomputable section

open Asymptotics Filter MulAction UpperHalfPlane
open _root_.Subgroup.CompactifiedQuotient
open scoped Manifold MatrixGroups

namespace TauCeti.Fuchsian

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]
  {F : Γ.CompactifiedQuotient → ℂ} {f : ℍ → ℂ}

/-- A function on the compactified quotient is meromorphic everywhere if its pullback is
meromorphic on the upper half-plane and is holomorphic sufficiently high with controlled
exponential growth at each cusp. Interior poles of the pullback are permitted. -/
theorem meromorphicAt_of_forall_isBigO
    (hF : ∀ z, F (ofQuotient (Quotient.mk _ z)) = f z)
    (hmero : ∀ z, RiemannSurface.MeromorphicAt f z)
    (hgrowth : ∀ C : Γ.CuspOrbit, ∃ (D : Γ.CuspDatum) (k : ℤ), D.cuspOrbit = C ∧
      (∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z)) ∧
      (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
        fun z ↦ Real.exp (2 * Real.pi * k * z.im / D.width))
    (x : Γ.CompactifiedQuotient) : RiemannSurface.MeromorphicAt F x := by
  cases x with
  | ofQuotient p =>
      induction p using Quotient.inductionOn with
      | h z =>
          have hpull : F ∘ ofQuotient ∘ Quotient.mk _ = f := funext hF
          rw [meromorphicAt_ofQuotient_mk_iff, hpull]
          exact hmero z
  | ofCusp C =>
      obtain ⟨D, k, rfl, hhol, hbound⟩ := hgrowth C
      exact meromorphicAt_ofCusp_of_isBigO hF D k hhol hbound

/-- An invariant meromorphic function on the upper half-plane extends to a meromorphic function
on the compactified quotient when it is holomorphic at sufficiently large normalized heights
and has at most exponential growth at every cusp. The extension pulls back along the ordinary
orbit projection to the original function.

For any such cusp datum and integer growth rate, the extension has order at least the negative
of that integer, by `Subgroup.CompactifiedQuotient.neg_le_meromorphicOrderAt_ofCusp`. Its interior
orders satisfy the elliptic ramification formula
`Subgroup.CompactifiedQuotient.meromorphicOrderAt_comp_ofQuotient_mk`. -/
theorem exists_meromorphicAt_comp_ofQuotient (hinv : ∀ (g : Γ) (z : ℍ), f (g • z) = f z)
    (hmero : ∀ z, RiemannSurface.MeromorphicAt f z)
    (hgrowth : ∀ C : Γ.CuspOrbit, ∃ (D : Γ.CuspDatum) (k : ℤ), D.cuspOrbit = C ∧
      (∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z)) ∧
      (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
        fun z ↦ Real.exp (2 * Real.pi * k * z.im / D.width)) :
    ∃ F : Γ.CompactifiedQuotient → ℂ,
      (∀ x, RiemannSurface.MeromorphicAt F x) ∧ F ∘ ofQuotient ∘ Quotient.mk _ = f := by
  obtain ⟨descended, ⟨_, hpull⟩, _⟩ := Γ.existsUnique_meromorphicAt_quotientMk f hinv hmero
  let F : Γ.CompactifiedQuotient → ℂ := fun x ↦ Sum.elim descended 0 (equivSum Γ x)
  have hF : ∀ z, F (ofQuotient (Quotient.mk _ z)) = f z := fun z ↦ by
    simpa only [F, equivSum_ofQuotient, Sum.elim_inl, Function.comp_apply] using congrFun hpull z
  exact ⟨F, meromorphicAt_of_forall_isBigO hF hmero hgrowth, funext hF⟩

end TauCeti.Fuchsian
