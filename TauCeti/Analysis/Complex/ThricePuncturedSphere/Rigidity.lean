/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.Conformal.PuncturedPlane

/-!
# Puncture-preserving holomorphic self-maps of the thrice-punctured sphere

The pair-of-pants domain of Floer theory is the thrice-punctured sphere `S = ℂ ∖ {0, 1}`, the
Riemann sphere with the three ordered punctures `0`, `1` and `∞`. Unlike the cylinder `ℝ × S¹`,
whose translations in `s` act on the moduli spaces of Floer cylinders, it carries no continuous
family of conformal symmetries preserving its ordered punctures: the only such symmetry is the
identity. This is why moduli spaces of pairs of pants with ordered ends are not divided by a
reparametrization group, in contrast to the translation quotient of moduli spaces of Floer
cylinders.

This file proves the rigidity in a strong form. Let `f` be holomorphic and injective on `S` and
fix the two finite punctures in the sense that `f w → 0` as `w → 0` and `f w → 1` as `w → 1`.
Then `f` is the identity of `S` (`TauCeti.ThricePuncturedSphere.eqOn_id_of_injOn`). Nothing is
assumed at `∞`, `f` is not assumed to map `S` into itself, and it need not be surjective. Such an
`f` is a punctured embedding of the plane punctured at `0` and `1` into itself, so it is the
identity (`TauCeti.IsPuncturedEmbedding.eqOn_id`): it is affine, and the only affine map fixing `0`
and `1` is the identity.

## Main results

* `TauCeti.ThricePuncturedSphere.eqOn_id_of_injOn`: an injective holomorphic self-map of `S`
  fixing the punctures `0` and `1` is the identity.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Appendix D, on
  stable curves and the automorphisms of the sphere with three marked points.
-/

public section

open Filter Set Topology Function

namespace TauCeti.ThricePuncturedSphere

/-- **The thrice-punctured sphere has no nontrivial puncture-preserving automorphisms.** A map
`f` that is holomorphic and injective on `ℂ ∖ {0, 1}` and tends to `0` at `0` and to `1` at `1`
is the identity on `ℂ ∖ {0, 1}`. -/
theorem eqOn_id_of_injOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {w | w ≠ 0 ∧ w ≠ 1})
    (hinj : InjOn f {w | w ≠ 0 ∧ w ≠ 1}) (h₀ : Tendsto f (𝓝[≠] 0) (𝓝 0))
    (h₁ : Tendsto f (𝓝[≠] 1) (𝓝 1)) : EqOn f id {w | w ≠ 0 ∧ w ≠ 1} := by
  -- The two finite punctures, labelled `0` and `1`.
  set c : Fin 2 → ℂ := ![0, 1]
  have hS : (range c)ᶜ = {w | w ≠ 0 ∧ w ≠ 1} := by
    ext w
    simp [c, and_comm]
  have hemb : IsPuncturedEmbedding c c f :=
    { differentiableOn := hS ▸ hf
      injOn := hS ▸ hinj
      tendsto := fun i => by fin_cases i <;> simpa [c] }
  -- A punctured embedding fixing the two distinct punctures `0` and `1` is the identity.
  simpa only [hS] using hemb.eqOn_id (i := 0) (j := 1) (by simp [c])

end TauCeti.ThricePuncturedSphere
