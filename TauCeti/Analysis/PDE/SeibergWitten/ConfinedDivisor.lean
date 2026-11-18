/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import TauCeti.Analysis.PDE.Vortex.Deformation
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Wirtinger.WholeSpace
import TauCeti.Analysis.PDE.Vortex.Existence
import TauCeti.Analysis.PDE.Vortex.Zeros

/-!
# Confined zero divisors of flat limiting sections and their comparison vortices

Rescaling a large-parameter Seiberg–Witten solution on a symplectic four-manifold near its zero
set gives, in the limit, fields on `ℂ_base × ℂ_normal` whose spinor lies on the canonical line,
`χ = α u₀`, with a connection `a` on the trivial line. The flat limiting equations then say that
`∂bar_a α = 0` and that the curvature of `a` has no `(0,2)` part
(`TauCeti.SeibergWitten.add_hodgeStar_eq_sub_quadraticTwoForm_iff`,
`TauCeti.SeibergWitten.sum_covariantDeriv_smul_ι_apply_eq_zero_iff`). In complex coordinates
`z = (z_j)` on `ι → ℂ`, the `(0,1)` part of `a` is a `bar∂`-closed form `∑ j, b_j d(conj z_j)` and
the first equation reads `∂α/∂(conj z_j) + b_j α = 0`. Taubes's analysis also confines the zeros
of the limit in the normal direction: `α z ≠ 0` when the normal coordinate `z_i` satisfies
`‖z_i‖ ≥ K`.

This file proves that such a section is, up to a smooth nowhere vanishing factor, the section of
a plane vortex pulled back along the normal coordinate
(`TauCeti.SeibergWitten.exists_eq_mul_sectionValue`). Precisely, there are a multiset `s` of
points of norm less than `K` and a smooth framed vortex `x` of degree `|s|` on `ℂ`, with zero
divisor `s`, such that

`α z = h z * α_x (z_i)`

for a smooth nowhere vanishing function `h`. The argument has three steps.

* In a holomorphic gauge `α` is an entire function times `exp (-g)`, and the confined zero divisor
  of an entire function on `(ι → ℂ) × ℂ` is the product of the base with a fixed divisor of the
  normal line. Hence `α = u ∏_{a ∈ s} (z_i - a)` with `u` smooth and nowhere zero
  (`TauCeti.exists_contDiff_ne_zero_eq_mul_prod_sub`).
* Taubes's existence theorem gives a smooth framed vortex `x` whose section vanishes exactly at
  the points of `s`, to the order of their multiplicities
  (`TauCeti.Vortex.exists_contDiff_equation_eq_zero_isZeroMultiplicity`).
* Its section has the same zero multiplicities as the polynomial `∏_{a ∈ s} (w - a)`, the section
  of the field reconstructed from that polynomial with zero amplitude, so the two differ by a
  smooth nowhere vanishing factor `W` (`TauCeti.Vortex.exists_contDiff_sectionValue_eq_mul`).
  Then `h z = u z / W (z_i)`.

The factor `h` is the quotient whose log-modulus `log |h|²` is Taubes's log-modulus ratio of the
limit against the vortex. If it is bounded, and both sections satisfy the transverse vacuum
condition, the comparison theorem
`TauCeti.SeibergWitten.norm_eq_one_and_eq_sub_phaseForm_of_tendsto` makes the limit the gauge
transform of the pulled-back vortex by `h`. This file does not prove that `log |h|²` is bounded,
does not translate the frame form of the flat limiting equations into the coordinates used here,
and does not derive the hypotheses from rescaled solutions.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 4.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

open Complex Filter Topology
open scoped ContDiff

namespace TauCeti.SeibergWitten

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A confined flat limiting section is a unit times a pulled-back vortex section.** Let
`b = ∑ j, b_j d(conj z_j)` be a smooth `bar∂`-closed `(0,1)`-form on `ι → ℂ` and `α` a
real-differentiable section with `bar∂ α + b α = 0` and `α z ≠ 0` whenever `K ≤ ‖z i‖`. Then there
are a multiset `s` of points of norm less than `K` and a smooth plane vortex `x` with the degree
`|s|` end framing whose section has zero divisor `s`, such that `α z = h z * α_x (z i)` for a
smooth nowhere vanishing function `h`. -/
theorem exists_eq_mul_sectionValue (i : ι) {b : ι → (ι → ℂ) → ℂ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (hclosed : ∀ z j k,
      conjWirtingerDeriv (b k) z (Pi.single j 1) = conjWirtingerDeriv (b j) z (Pi.single k 1))
    {α : (ι → ℂ) → ℂ} (hα : Differentiable ℝ α)
    (hαb : ∀ z j, conjWirtingerDeriv α z (Pi.single j 1) + b j z * α z = 0)
    {K : ℝ} (hK : ∀ z, K ≤ ‖z i‖ → α z ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧
      ∃ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x ∧ (∀ w, Vortex.equation x w = 0) ∧
        Tendsto (fun w ↦ Vortex.sectionValue x w * ((w / (‖w‖ : ℂ)) ^ Multiset.card s)⁻¹)
          (cocompact ℂ) (𝓝 1) ∧
        IsZeroMultiplicity (Vortex.sectionValue x) (fun w ↦ s.count w) ∧
        ∃ h : (ι → ℂ) → ℂ, ContDiff ℝ ∞ h ∧ (∀ z, h z ≠ 0) ∧
          ∀ z, α z = h z * Vortex.sectionValue x (z i) := by
  obtain ⟨s, hsK, u, hu, hu0, hαu⟩ :=
    exists_contDiff_ne_zero_eq_mul_prod_sub i hb hclosed hα hαb hK
  obtain ⟨x, hx, hxeq, hxframe, hxmult⟩ :=
    Vortex.exists_contDiff_equation_eq_zero_isZeroMultiplicity (⟨s, rfl⟩ : Sym ℂ (Multiset.card s))
  -- The field reconstructed from the polynomial `P w = ∏_{a ∈ s} (w - a)` with zero amplitude has
  -- section `P` and the same zero multiplicities as `x`.
  set P : ℂ → ℂ := fun w ↦ (s.map fun a ↦ w - a).prod with hP
  have hPpoly : P = fun w ↦ ((s.map fun a ↦ Polynomial.X - Polynomial.C a).prod).eval w := by
    funext w
    simp [hP, Polynomial.eval_multiset_prod]
  have hPd : Differentiable ℂ P := by
    rw [hPpoly]
    exact Polynomial.differentiable _
  set y := Vortex.amplitudeField 0 P with hy
  have hyc : ContDiff ℝ ∞ y :=
    Vortex.contDiff_amplitudeField (n := ⊤) contDiff_const
      (by rw [hPpoly]; exact (Polynomial.differentiable _).contDiff.restrict_scalars ℝ)
  have hyP (w : ℂ) : Vortex.sectionValue y w = P w := by
    simp [hy, Vortex.sectionValue_amplitudeField]
  have hcomp {z : ℂ → EuclideanSpace ℝ (Fin 4)} (hz : ContDiff ℝ ∞ z) (k : Fin 4) :
      ContDiff ℝ ∞ fun w ↦ z w k :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hz
  obtain ⟨W, hW, hW0, hxW⟩ := Vortex.exists_contDiff_sectionValue_eq_mul (k := ⊤) le_top
    (hcomp hx 0) (hcomp hx 1) ((hcomp hx 2).differentiable (by simp))
    ((hcomp hx 3).differentiable (by simp)) (fun w ↦ by simp [hxeq w])
    (hcomp hyc 0) (hcomp hyc 1) ((hcomp hyc 2).differentiable (by simp))
    ((hcomp hyc 3).differentiable (by simp))
    (fun w ↦ Vortex.equation_amplitudeField_apply_one_eq_zero_and_apply_two_eq_zero
      (differentiableAt_const _) (hPd w))
    (isZeroMultiplicity_iff.1 hxmult)
    (isZeroMultiplicity_iff.1 (Vortex.isZeroMultiplicity_sectionValue_amplitudeField_prod_sub
      continuous_const s))
  refine ⟨s, hsK, x, hx, hxeq, hxframe, hxmult, fun z ↦ u z / W (z i), ?_,
    fun z ↦ div_ne_zero (hu0 z) (hW0 _), fun z ↦ ?_⟩
  · have hpr : ContDiff ℝ ∞ fun z : ι → ℂ ↦ z i := by fun_prop
    have hWi : ContDiff ℝ ∞ fun z : ι → ℂ ↦ (W (z i))⁻¹ := (hW.comp hpr).inv fun z ↦ hW0 _
    simpa only [div_eq_mul_inv] using hu.mul hWi
  · rw [hαu z, hxW, hyP, div_mul_eq_mul_div, eq_div_iff (hW0 _)]
    ring

end TauCeti.SeibergWitten
