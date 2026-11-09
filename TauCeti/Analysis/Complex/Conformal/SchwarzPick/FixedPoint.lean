/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Defs
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Rigidity
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Parametrization

/-!
# Fixed points of holomorphic self-maps of the unit disc

A holomorphic self-map of the open unit disc that fixes **two** distinct points of the disc is
the identity on the disc (`TauCeti.eqOn_id_of_isFixedPt_of_isFixedPt`).  More precisely, a
holomorphic self-map of the disc differs from the identity on the disc exactly when its
fixed-point set in the disc is a subsingleton
(`TauCeti.subsingleton_inter_fixedPoints_iff_not_eqOn_id`), which gives the
dichotomy that a holomorphic self-map of the disc is either the identity or fixes at most one
point of the disc (`TauCeti.eqOn_id_or_subsingleton_inter_fixedPoints`).

This generalises `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt`, which says the same for a
member of `Aut(𝔻)`, from automorphisms to arbitrary holomorphic self-maps.

## The argument

Two fixed points make the Schwarz--Pick contraction estimate an equality at that pair of points
for a trivial reason: both sides are the same pseudo-hyperbolic expression.  The classification
form of Schwarz--Pick rigidity,
`exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq`,
therefore turns `f` into a standard disc automorphism `ζ ↦ u * (ζ - b) / (1 - conj b * ζ)`.
Its two fixed points force it to be the identity of `Aut(𝔻)` by the automorphism statement.

## References

* [Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505), the preceding
  human-curated Riemann-mapping development and its local analytic prerequisites.
* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.2.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VI §2.
-/

public section

namespace TauCeti

open Metric Set

variable {f : ℂ → ℂ} {z w : ℂ}

/-- **A holomorphic self-map of the disc with two distinct fixed points is the identity.**

If `f` is differentiable on the open unit ball `ball (0 : ℂ) 1`, maps that ball into itself and
fixes two distinct points `z ≠ w` of it, then `f` agrees with the identity on the whole ball.
This is `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt` with its hypothesis weakened from
membership in `Aut(𝔻)` to an arbitrary holomorphic self-map. -/
theorem eqOn_id_of_isFixedPt_of_isFixedPt (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (hz : z ∈ ball (0 : ℂ) 1)
    (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w) (hfz : Function.IsFixedPt f z)
    (hfw : Function.IsFixedPt f w) : EqOn f id (ball (0 : ℂ) 1) := by
  obtain ⟨u, b, hb⟩ :=
    exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq
      hf hmaps hz hw hne (by rw [hfz.eq, hfw.eq])
  -- A fixed point of `f` in the disc is a fixed point of the automorphism.
  have hfix {p : ℂ} (hp : ‖p‖ < 1) (hfp : Function.IsFixedPt f p) :
      Function.IsFixedPt (unitDiscStandardAutomorphismEquiv u b) (.mk p hp) :=
    Complex.UnitDisc.coe_injective <| by rw [← hb, Complex.UnitDisc.coe_mk, hfp.eq]
  have hz1 := mem_ball_zero_iff.mp hz
  have hw1 := mem_ball_zero_iff.mp hw
  have hone := eq_one_of_mem_unitDiscAut_of_isFixedPt
    (unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u b)
    (by rwa [Ne, Complex.UnitDisc.mk_inj]) (hfix hz1 hfz) (hfix hw1 hfw)
  intro ζ hζ
  simpa [hone] using hb (.mk ζ (mem_ball_zero_iff.mp hζ))

/-- **A holomorphic self-map of the disc is not the identity iff it has at most one fixed point
in the disc.**

The hypotheses constrain `f` only on `ball (0 : ℂ) 1`, so only the fixed points lying in that
ball are controlled: fixed points of `f` outside the disc are arbitrary. -/
theorem subsingleton_inter_fixedPoints_iff_not_eqOn_id
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    (ball (0 : ℂ) 1 ∩ Function.fixedPoints f).Subsingleton ↔ ¬ EqOn f id (ball (0 : ℂ) 1) := by
  refine ⟨fun hs hid => ?_, fun hid p ⟨hp, hfp⟩ q ⟨hq, hfq⟩ => ?_⟩
  · have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    have h2 : (2⁻¹ : ℂ) ∈ ball (0 : ℂ) 1 := by norm_num [mem_ball_zero_iff]
    exact absurd (hs ⟨h0, hid h0⟩ ⟨h2, hid h2⟩) (by norm_num)
  · by_contra hne
    exact hid (eqOn_id_of_isFixedPt_of_isFixedPt hf hmaps hp hq hne hfp hfq)

/-- **The fixed-point dichotomy for a holomorphic self-map of the disc.** Either the map is the
identity, or it fixes at most one point of the disc. -/
theorem eqOn_id_or_subsingleton_inter_fixedPoints (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    EqOn f id (ball (0 : ℂ) 1) ∨ (ball (0 : ℂ) 1 ∩ Function.fixedPoints f).Subsingleton :=
  or_iff_not_imp_left.2 (subsingleton_inter_fixedPoints_iff_not_eqOn_id hf hmaps).2

end TauCeti
