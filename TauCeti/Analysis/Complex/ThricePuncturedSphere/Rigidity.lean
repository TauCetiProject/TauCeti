/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.Conformal.EntireInjection

/-!
# Puncture-preserving holomorphic self-maps of the thrice-punctured sphere

The pair-of-pants domain of Floer theory is the thrice-punctured sphere `S = ℂ ∖ {0, 1}`, the
Riemann sphere with the three ordered punctures `0`, `1` and `∞`. Unlike the cylinder `ℝ × S¹`,
whose translations in `s` act on the moduli spaces of Floer cylinders, it carries no continuous
family of conformal symmetries preserving its ordered punctures: the only such symmetry is the
identity. This is why moduli spaces of pairs of pants with ordered ends are not divided by a
reparametrization group, in contrast to the translation quotient of moduli spaces of Floer
cylinders.

This file proves the rigidity in a strong form. Let `f` be holomorphic and injective on `S`, map
`S` into itself, and fix the two finite punctures in the sense that `f w → 0` as `w → 0` and
`f w → 1` as `w → 1`. Then `f` is the identity of `S`
(`TauCeti.ThricePuncturedSphere.eqOn_id_of_injOn`). Nothing is assumed at `∞`, and `f` need not be
surjective. Filling in `f 0 = 0` and `f 1 = 1` removes the two singularities and gives an
injective entire function, which is affine (`Differentiable.exists_eq_mul_add_of_injective`), and
the only affine map fixing `0` and `1` is the identity.

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
`f` that is holomorphic and injective on `ℂ ∖ {0, 1}`, maps it into itself, and tends to `0`
at `0` and to `1` at `1`, is the identity on `ℂ ∖ {0, 1}`. -/
theorem eqOn_id_of_injOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {w | w ≠ 0 ∧ w ≠ 1})
    (hmaps : MapsTo f {w | w ≠ 0 ∧ w ≠ 1} {w | w ≠ 0 ∧ w ≠ 1})
    (hinj : InjOn f {w | w ≠ 0 ∧ w ≠ 1}) (h₀ : Tendsto f (𝓝[≠] 0) (𝓝 0))
    (h₁ : Tendsto f (𝓝[≠] 1) (𝓝 1)) : EqOn f id {w | w ≠ 0 ∧ w ≠ 1} := by
  set S : Set ℂ := {w | w ≠ 0 ∧ w ≠ 1}
  have hSo : IsOpen S := isOpen_ne.inter isOpen_ne
  -- Fill in the two finite punctures.
  set g : ℂ → ℂ := update (update f 0 0) 1 1 with hg
  have hgS : ∀ w ∈ S, g w = f w := fun w hw => by
    rw [hg, update_of_ne hw.2, update_of_ne hw.1]
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = 1 := by simp [g]
  have hgc : ∀ w ∉ S, g w = w := fun w hw => by
    obtain rfl | rfl : w = 0 ∨ w = 1 := by
      by_contra h
      exact hw (not_or.1 h)
    exacts [hg0, hg1]
  -- Near each finite puncture, the other points lie in `S`.
  have hpunct : ∀ c : ℂ, c ∉ S → ∀ᶠ w in 𝓝[≠] c, w ∈ S := fun c hc => by
    obtain rfl | rfl : c = 0 ∨ c = 1 := by
      by_contra h
      exact hc (not_or.1 h)
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ne.mem_nhds zero_ne_one)]
        with w hw hw1
      exact ⟨hw, hw1⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero)]
        with w hw hw0
      exact ⟨hw0, hw⟩
  have hdS : ∀ w ∈ S, DifferentiableAt ℂ g w := fun w hw =>
    (hf.differentiableAt (hSo.mem_nhds hw)).congr_of_eventuallyEq
      (eventually_of_mem (hSo.mem_nhds hw) hgS)
  -- The singularities at the punctures are removable, so `g` is entire.
  have hd : Differentiable ℂ g := fun c => by
    by_cases hc : c ∈ S
    · exact hdS c hc
    refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ((hpunct c hc).mono hdS) ?_).differentiableAt
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hgc c hc]
    obtain rfl | rfl : c = 0 ∨ c = 1 := by
      by_contra h
      exact hc (not_or.1 h)
    exacts [h₀.congr' ((hpunct 0 hc).mono fun w hw => (hgS w hw).symm),
      h₁.congr' ((hpunct 1 hc).mono fun w hw => (hgS w hw).symm)]
  -- `g` maps `S` into `S` and fixes the punctures, so it is injective.
  have hgmem : ∀ w, g w ∈ S ↔ w ∈ S := fun w => by
    by_cases hw : w ∈ S
    · exact iff_of_true (hgS w hw ▸ hmaps hw) hw
    · rw [hgc w hw]
  have hginj : Injective g := fun x y hxy => by
    by_cases hx : x ∈ S
    · have hy : y ∈ S := (hgmem y).1 (hxy ▸ (hgmem x).2 hx)
      exact hinj hx hy (by rwa [← hgS x hx, ← hgS y hy])
    · have hy : y ∉ S := fun hy => hx ((hgmem x).1 (hxy ▸ (hgmem y).2 hy))
      rwa [hgc x hx, hgc y hy] at hxy
  -- An injective entire function fixing `0` and `1` is the identity.
  obtain ⟨a, b, -, hab⟩ := hd.exists_eq_mul_add_of_injective hginj
  have hb : b = 0 := by simpa [hg0] using (hab 0).symm
  have ha : a = 1 := by simpa [hg1, hb] using (hab 1).symm
  intro w hw
  rw [← hgS w hw, hab, ha, hb, one_mul, add_zero, id]

end TauCeti.ThricePuncturedSphere
