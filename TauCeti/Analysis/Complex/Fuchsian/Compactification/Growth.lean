/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Extension
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Asymptotics

/-!
# A growth characterization of meromorphic extension to a Fuchsian compactification

An invariant meromorphic function on the upper half-plane extends to the compactified quotient
exactly when it is holomorphic sufficiently high and has at most exponential growth at each
cusp. The bound uses the width of any chosen normalized datum for that cusp;
no finiteness of the cusp set or cofiniteness of the group is required.

This characterizes existence of an extension rather than uniqueness of its point values:
meromorphic functions here may be assigned arbitrary values at their poles. The original
function is recovered pointwise on the upper half-plane.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.4–2.5.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.

The proof combines the meromorphic descent in `Compactification.Extension`, the q-chart
comparison in `Compactification.Meromorphic`, and the exact cusp criterion in `Cusp.Asymptotics`.
-/

public noncomputable section

open Asymptotics Filter MulAction UpperHalfPlane
open _root_.Subgroup.CompactifiedQuotient
open scoped Manifold MatrixGroups

namespace TauCeti.Fuchsian

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ] {f : ℍ → ℂ}

/-- An invariant meromorphic function extends meromorphically to the compactified quotient
exactly when it is holomorphic sufficiently high and satisfies an exponential growth bound at
each cusp. The criterion holds for every choice of normalized cusp data, with each bound
expressed using that datum's width. Interior poles are allowed. -/
theorem exists_meromorphicAt_comp_ofQuotient_iff
    (hinv : ∀ (g : Γ) (z : ℍ), f (g • z) = f z)
    (hmero : ∀ z, RiemannSurface.MeromorphicAt f z)
    (D : Γ.CuspOrbit → Γ.CuspDatum) (hD : ∀ C, (D C).cuspOrbit = C) :
    (∃ F : Γ.CompactifiedQuotient → ℂ,
      (∀ x, RiemannSurface.MeromorphicAt F x) ∧ F ∘ ofQuotient ∘ Quotient.mk _ = f) ↔
      ∀ C, (∀ᶠ z in atImInfty,
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f ((D C).scaling⁻¹ • z)) ∧
          ∃ k : ℤ, (fun z : ℍ ↦ f ((D C).scaling⁻¹ • z)) =O[atImInfty]
            fun z ↦ Real.exp (2 * Real.pi * k * z.im / (D C).width) := by
  constructor
  · rintro ⟨F, hF, hpull⟩ C
    apply (Subgroup.CuspDatum.meromorphicAt_cuspExtension_zero_iff
      (D C) f (fun g ↦ hinv g.1)).1
    exact (meromorphicAt_ofCusp_iff (D C) (congrFun hpull)).1 (hF _)
  · intro hgrowth
    apply exists_meromorphicAt_comp_ofQuotient hinv hmero
    intro C
    obtain ⟨hhol, k, hk⟩ := hgrowth C
    exact ⟨D C, k, hD C, hhol, hk⟩

end TauCeti.Fuchsian
