/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Automorphy
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Automorphy

/-!
# Automorphy transitions on cusp–elliptic overlaps

The transition functions between a cusp chart and a local linearizing chart are inverse
on their overlap, so they vanish nowhere. Compatibility of each frame with the weight-`k`
action suffices; precise invariance is one way to obtain this compatibility.

The main results are:

* [`automorphyDescent_automorphyExtension_mul_linearizingCoordinate_automorphyDescent_eq_one`](https://taucetiproject.org/docs/TauCeti/Analysis/Complex/Fuchsian/Automorphy/Overlap.html#TauCeti.Subgroup.CuspDatum.automorphyDescent_automorphyExtension_mul_linearizingCoordinate_automorphyDescent_eq_one):
  the two transition functions multiply to one.
* [`automorphyDescent_automorphyExtension_linearizingCoordinate_automorphyFrame_ne_zero`](https://taucetiproject.org/docs/TauCeti/Analysis/Complex/Fuchsian/Automorphy/Overlap.html#TauCeti.Subgroup.CuspDatum.automorphyDescent_automorphyExtension_linearizingCoordinate_automorphyFrame_ne_zero):
  the transition from the elliptic chart to the cusp chart is nonzero.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§3.5–3.6.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §2.4.
-/

public section

noncomputable section

open Filter Function Matrix.ProjectiveSpecialLinearGroup Metric MulAction Set UpperHalfPlane
open scoped ComplexConjugate ContDiff Manifold MatrixGroups ModularForm Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)} {D : Γ.CuspDatum}
variable {s : SL(2, ℝ)} {k : ℤ} {r : ℕ} {A : ℝ}

/-! ### Transition functions between the charts at a cusp and at an elliptic point -/

variable {Γ' : _root_.Subgroup SL(2, ℝ)}
variable {z' : ℍ} {ε' : ℝ} [Finite (stabilizer Γ z')]

/-- **The transition functions between the chart at a cusp and an elliptic chart are inverse to
each other.** Let `Γ'` contain lifts of `Γ`, let every lift in `Γ'` of the generator of `D`
satisfy the sign condition with `r < 2`, and let the cusp frame be compatible on the horodisc of
height `A`. Let `ψ'` be a local linearizing coordinate at `z'` with compatible frame and exponent
`r' < m'` satisfying the frame condition. If `τ` is a point of the horodisc and `σ = h • τ`, for
`h ∈ Γ'`, is a point of the disc about `z'`, then the transition function from the chart of `ψ'`
to that at the cusp, at the cusp coordinate of `τ`, times the transition function from the chart
at the cusp to that of `ψ'`, at the quotient coordinate of `σ`, is `1`; so both transition
functions are units on the whole overlap of the two charts. If the horodisc is precisely
invariant, its points have trivial stabilizer in `Γ`, so the overlap contains no elliptic point. -/
theorem automorphyDescent_automorphyExtension_mul_linearizingCoordinate_automorphyDescent_eq_one
    (hs : (s : PSL(2, ℝ)) = D.scaling) (ψ' : Γ.LinearizingCoordinate z' ε')
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', (g : PSL(2, ℝ)) = D.generator → ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hr : r < 2)
    (hF : ∀ g ∈ Γ', ∀ σ ∈ horodisc D A, g • σ ∈ horodisc D A →
      automorphyFrame D s k r (g • σ) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * automorphyFrame D s k r σ) {r' : ℕ}
    (hk' : ∀ g ∈ Γ', g • z' = z' →
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z' ^ (2 * r' + k) = 1)
    (hr' : r' < Nat.card (stabilizer Γ z'))
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ ball z' ε', g • σ ∈ ball z' ε' →
      (((g • σ : ℍ) : ℂ) - conj (z' : ℂ)) ^ (-k) *
        ψ'.toEquiv (UpperHalfPlane.discCoordinate z' (g • σ)) ^ r' =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k *
        (((σ : ℂ) - conj (z' : ℂ)) ^ (-k) *
          ψ'.toEquiv (UpperHalfPlane.discCoordinate z' σ) ^ r'))
    {τ : ℍ} (hτ : τ ∈ horodisc D A) {σ : Γ.stabilizerBall z' ε'} {h : SL(2, ℝ)} (hh : h ∈ Γ')
    (hσ : (σ : ℍ) = h • τ) :
    automorphyDescent D s k r (Γ'.automorphyExtension (ball z' ε') k fun σ ↦
          ((σ : ℂ) - conj (z' : ℂ)) ^ (-k) * ψ'.toEquiv (UpperHalfPlane.discCoordinate z' σ) ^ r')
        (coordinate D τ) *
      ψ'.automorphyDescent k r' (Γ'.automorphyExtension (horodisc D A) k
          (automorphyFrame D s k r)) (ψ'.quotientCoordinate σ) = 1 := by
  -- a lift `g ∈ Γ'` of the generator of `D`
  obtain ⟨g, hgΓ, hg⟩ := _root_.Subgroup.mem_map.mp (hΓ D.generator.2 :
    (D.generator : PSL(2, ℝ)) ∈ Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))))
  have hσb : (σ : ℍ) ∈ ball z' ε' :=
    mem_ball.mpr ((_root_.Subgroup.mem_stabilizerBall Γ z' ε').1 σ.2)
  -- the coefficient in the chart of `ψ'` of the extension of the frame at the cusp
  have hσA : h⁻¹ • (σ : ℍ) ∈ horodisc D A := by rwa [hσ, inv_smul_smul]
  have hc := ψ'.automorphyFrame_mul_automorphyDescent_automorphyExtension hΓ hk'
    (isOpen_horodisc D A) hF (mdifferentiable_automorphyFrame D s k r).mdifferentiableOn hr'
    (Γ'.inv_mem hh) hσA
  rw [← _root_.Subgroup.automorphyExtension_eq hF (Γ'.inv_mem hh) hσA] at hc
  rw [_root_.Subgroup.LinearizingCoordinate.automorphyFrame_eq_toEquiv_discCoordinate, hσ] at hc
  have h₁ := automorphyDescent_eq_automorphyDescent_automorphyExtension_mul hs hg (hk g hgΓ hg) hgΓ
    (F' := fun σ ↦
      ((σ : ℂ) - conj (z' : ℂ)) ^ (-k) * ψ'.toEquiv (UpperHalfPlane.discCoordinate z' σ) ^ r')
    hF' hr
    (fun _ hg σ ↦ _root_.Subgroup.automorphyExtension_smul hF hg σ) hh (hσ ▸ hσb) hc
  rw [← h₁]
  -- the transition function from the chart at the cusp to itself is `1`
  refine mul_left_cancel₀ (automorphyFrame_ne_zero D s k r τ) ?_
  simpa only [map_one, denom_one, one_zpow, one_mul, one_smul, mul_one] using
    automorphyFrame_mul_automorphyDescent_automorphyExtension hs hg (hk g hgΓ hg) hgΓ hF hr
      Γ'.one_mem (by simpa using hτ)

/-- **The transition function from an elliptic chart to the chart at a cusp vanishes nowhere
on their overlap.** The frames are compatible on the horodisc and the elliptic disc, and
their exponents satisfy the frame conditions. -/
theorem automorphyDescent_automorphyExtension_linearizingCoordinate_automorphyFrame_ne_zero
    (hs : (s : PSL(2, ℝ)) = D.scaling) (ψ' : Γ.LinearizingCoordinate z' ε')
    (hΓ : Γ ≤ Γ'.map (QuotientGroup.mk' (_root_.Subgroup.center SL(2, ℝ))))
    (hk : ∀ g ∈ Γ', (g : PSL(2, ℝ)) = D.generator → ((s * g * s⁻¹) 1 1 : ℝ) ^ k = (-1) ^ r)
    (hr : r < 2)
    (hF : ∀ g ∈ Γ', ∀ σ ∈ horodisc D A, g • σ ∈ horodisc D A →
      automorphyFrame D s k r (g • σ) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k * automorphyFrame D s k r σ) {r' : ℕ}
    (hk' : ∀ g ∈ Γ', g • z' = z' →
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) z' ^ (2 * r' + k) = 1)
    (hr' : r' < Nat.card (stabilizer Γ z'))
    (hF' : ∀ g ∈ Γ', ∀ σ ∈ ball z' ε', g • σ ∈ ball z' ε' →
      (((g • σ : ℍ) : ℂ) - conj (z' : ℂ)) ^ (-k) *
        ψ'.toEquiv (UpperHalfPlane.discCoordinate z' (g • σ)) ^ r' =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ k *
        (((σ : ℂ) - conj (z' : ℂ)) ^ (-k) *
          ψ'.toEquiv (UpperHalfPlane.discCoordinate z' σ) ^ r'))
    {τ : ℍ} (hτ : τ ∈ horodisc D A) {h : SL(2, ℝ)} (hh : h ∈ Γ')
    (hτ' : h • τ ∈ ball z' ε') :
    automorphyDescent D s k r (Γ'.automorphyExtension (ball z' ε') k fun σ ↦
          ((σ : ℂ) - conj (z' : ℂ)) ^ (-k) * ψ'.toEquiv (UpperHalfPlane.discCoordinate z' σ) ^ r')
        (coordinate D τ) ≠ 0 :=
  left_ne_zero_of_mul_eq_one
    (automorphyDescent_automorphyExtension_mul_linearizingCoordinate_automorphyDescent_eq_one hs ψ'
      hΓ hk hr hF hk' hr' hF' hτ
      (σ := ⟨h • τ, (_root_.Subgroup.mem_stabilizerBall Γ z' ε').2 (mem_ball.mp hτ')⟩) hh rfl)

end TauCeti.Subgroup.CuspDatum
