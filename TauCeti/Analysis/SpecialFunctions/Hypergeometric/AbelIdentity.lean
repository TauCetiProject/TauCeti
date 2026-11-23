/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.ODE.Complex.ScalarLinear
import TauCeti.Analysis.ODE.Wronskian

/-!
# Abel's identity for the hypergeometric equation

For solutions `f`, `g` of the hypergeometric equation (DLMF 15.10.1)

`z (1 − z) w′′ + (c − (a + b + 1) z) w′ − a b w = 0`

the Wronskian `𝒲{f, g} = f g′ − f′ g` satisfies Abel's identity
`𝒲′ = −((c − (a + b + 1) z)/(z (1 − z))) 𝒲` at every point other than `0` and `1` where `f`,
`g` and their derivatives are differentiable. Consequently, on a connected open subset of
`slitPlane ∩ {1 − z ∈ slitPlane}` the Wronskian is a constant multiple of
`z^{−c} (1 − z)^{c−a−b−1}`, and on any connected open set two solutions whose Wronskian is
nonzero at one point span all solutions.

The statements are about arbitrary solutions, so they do not need a definition of the Gauss
function. The Wronskian is written out as `f z * deriv g z - deriv f z * g z`.

Abel's identity is the case of `HasDerivAt.wronskian_of_secondOrderLinearEquation` for the
normalized equation `w′′ + p w′ + q w = 0`. The other two results compare solutions of the
first-order equation `y′ = −p y` by `IsOpen.exists_eq_const_mul_of_hasDerivAt_mul`: the Wronskian
with the power product `z^{−c} (1 − z)^{c−a−b−1}`, and two Wronskians with each other.

## Main results

* `TauCeti.hasDerivAt_wronskian_of_hypergeometricEquation`: Abel's identity.
* `IsOpen.exists_wronskian_eq_mul_cpow_mul_one_sub_cpow_of_hypergeometricEquation`: the
  Wronskian is a constant multiple of `z^{−c} (1 − z)^{c−a−b−1}` on a connected open set in the
  cut plane.
* `IsOpen.exists_eq_mul_add_mul_of_hypergeometricEquation`: the span criterion.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §15.10, <https://dlmf.nist.gov/15.10>.
-/

public section

open Complex Filter Set
open scoped Topology

namespace TauCeti

variable {a b c : ℂ} {U : Set ℂ}

/-- **Abel's identity** for the hypergeometric equation (DLMF 15.10.1): if `f`, `g`, `f′` and `g′`
are differentiable at a point `z ≠ 0, 1` where `f` and `g` solve 15.10.1, then the Wronskian
`𝒲{f, g} = f g′ − f′ g` has derivative `−((c − (a + b + 1) z)/(z (1 − z))) 𝒲{f, g}` at `z`. -/
theorem hasDerivAt_wronskian_of_hypergeometricEquation {f g : ℂ → ℂ} {z : ℂ} (hz₀ : z ≠ 0)
    (hz₁ : z ≠ 1) (hf : DifferentiableAt ℂ f z) (hdf : DifferentiableAt ℂ (deriv f) z)
    (hg : DifferentiableAt ℂ g z) (hdg : DifferentiableAt ℂ (deriv g) z)
    (hf' : z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z - a * b * f z = 0)
    (hg' : z * (1 - z) * deriv (deriv g) z + (c - (a + b + 1) * z) * deriv g z - a * b * g z = 0) :
    HasDerivAt (fun ζ => f ζ * deriv g ζ - deriv f ζ * g ζ)
      (-((c - (a + b + 1) * z) / (z * (1 - z))) * (f z * deriv g z - deriv f z * g z)) z := by
  have : z * (1 - z) ≠ 0 := mul_ne_zero hz₀ (sub_ne_zero.mpr hz₁.symm)
  -- Divided by `z (1 − z)`, 15.10.1 is `w′′ + p w′ + q w = 0`.
  refine hf.hasDerivAt.wronskian_of_secondOrderLinearEquation (q := -(a * b) / (z * (1 - z)))
    hdf.hasDerivAt hg.hasDerivAt hdg.hasDerivAt ?_ ?_
  · field_simp
    linear_combination hf'
  · field_simp
    linear_combination hg'

/-- Abel's identity at a point `z ≠ 0, 1` of an open set on which `f` and `g` are holomorphic. -/
private theorem hasDerivAt_wronskian_of_hypergeometricEquation_of_mem {f g : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {z : ℂ}
    (hz : z ∈ U) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1)
    (hf' : z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z - a * b * f z = 0)
    (hg' : z * (1 - z) * deriv (deriv g) z + (c - (a + b + 1) * z) * deriv g z - a * b * g z = 0) :
    HasDerivAt (fun ζ => f ζ * deriv g ζ - deriv f ζ * g ζ)
      (-((c - (a + b + 1) * z) / (z * (1 - z))) * (f z * deriv g z - deriv f z * g z)) z :=
  hasDerivAt_wronskian_of_hypergeometricEquation hz₀ hz₁ (hf.differentiableAt (hU.mem_nhds hz))
    ((hf.deriv hU).differentiableAt (hU.mem_nhds hz)) (hg.differentiableAt (hU.mem_nhds hz))
    ((hg.deriv hU).differentiableAt (hU.mem_nhds hz)) hf' hg'

/-- The power product `z^{−c} (1 − z)^{c−a−b−1}` satisfies `y′ = −p y` with the coefficient
`p = (c − (a + b + 1) z)/(z (1 − z))` of 15.10.1, where `z` and `1 − z` lie in the slit plane. -/
private theorem hasDerivAt_cpow_mul_one_sub_cpow {z : ℂ} (hz : z ∈ slitPlane)
    (hz' : 1 - z ∈ slitPlane) :
    HasDerivAt (fun ζ => ζ ^ (-c) * (1 - ζ) ^ (c - a - b - 1))
      (-((c - (a + b + 1) * z) / (z * (1 - z))) * (z ^ (-c) * (1 - z) ^ (c - a - b - 1))) z := by
  have hz₀ : z ≠ 0 := slitPlane_ne_zero hz
  have hz₁ : 1 - z ≠ 0 := slitPlane_ne_zero hz'
  have hp := (hasDerivAt_id z).cpow_const (c := -c) hz
  have hr := ((hasDerivAt_id z).const_sub 1).cpow_const (c := c - a - b - 1) hz'
  refine (hp.mul hr).congr_deriv ?_
  simp only [id]
  rw [cpow_sub (-c) 1 hz₀, cpow_sub (c - a - b - 1) 1 hz₁, cpow_one, cpow_one]
  field_simp
  ring

/-- **The Wronskian in the cut plane** (DLMF 15.10.1, Abel's identity integrated): if `f` and `g`
solve 15.10.1 on a connected open set `U ⊆ slitPlane ∩ {1 − z ∈ slitPlane}`, then
`𝒲{f, g} = C z^{−c} (1 − z)^{c−a−b−1}` on `U` for a constant `C`. -/
theorem _root_.IsOpen.exists_wronskian_eq_mul_cpow_mul_one_sub_cpow_of_hypergeometricEquation
    {f g : ℂ → ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUs : ∀ z ∈ U, z ∈ slitPlane ∧ 1 - z ∈ slitPlane)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hf' : ∀ z ∈ U, z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z -
      a * b * f z = 0)
    (hg' : ∀ z ∈ U, z * (1 - z) * deriv (deriv g) z + (c - (a + b + 1) * z) * deriv g z -
      a * b * g z = 0) :
    ∃ C : ℂ, ∀ z ∈ U, f z * deriv g z - deriv f z * g z =
      C * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, fun z hz => hz.elim⟩
  have hne (z : ℂ) (hz : z ∈ U) : z ≠ 0 ∧ z ≠ 1 :=
    ⟨slitPlane_ne_zero (hUs z hz).1, fun h => slitPlane_ne_zero (hUs z hz).2 (by rw [h, sub_self])⟩
  -- The power product is nonzero at `z₀`, and both sides satisfy `y′ = −p y` on `U`.
  obtain ⟨C, hC⟩ := hU.exists_eq_const_mul_of_hasDerivAt_mul hUc dense_univ
    (p := fun z => -((c - (a + b + 1) * z) / (z * (1 - z))))
    (((hf.mul (hg.deriv hU)).sub ((hf.deriv hU).mul hg)))
    (v := fun z => z ^ (-c) * (1 - z) ^ (c - a - b - 1))
    (fun z hz => ((hasDerivAt_cpow_mul_one_sub_cpow (a := a) (b := b) (c := c) (hUs z hz).1
      (hUs z hz).2).differentiableAt.differentiableWithinAt)) hz₀
    (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (hUs z₀ hz₀).1)))
      (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (hUs z₀ hz₀).2))))
    (fun z hz => hasDerivAt_wronskian_of_hypergeometricEquation_of_mem hU hf hg hz.1
      (hne z hz.1).1 (hne z hz.1).2 (hf' z hz.1) (hg' z hz.1))
    (fun z hz => hasDerivAt_cpow_mul_one_sub_cpow (hUs z hz.1).1 (hUs z hz.1).2)
  exact ⟨C, fun z hz => (hC z hz).trans (mul_assoc _ _ _).symm⟩

/-- **The span criterion** for the hypergeometric equation: if `f₁` and `f₂` solve 15.10.1 on a
connected open set `U`, and `𝒲{f₁, f₂}` is nonzero at a point `z₀ ∈ U`, then every solution `w` on
`U` is `A f₁ + B f₂` with constants `A`, `B`. The set `U` may contain the singular points `0`
and `1`. -/
theorem _root_.IsOpen.exists_eq_mul_add_mul_of_hypergeometricEquation {f₁ f₂ w : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf₁ : DifferentiableOn ℂ f₁ U) (hf₂ : DifferentiableOn ℂ f₂ U)
    (hw : DifferentiableOn ℂ w U)
    (hf₁' : ∀ z ∈ U, z * (1 - z) * deriv (deriv f₁) z + (c - (a + b + 1) * z) * deriv f₁ z -
      a * b * f₁ z = 0)
    (hf₂' : ∀ z ∈ U, z * (1 - z) * deriv (deriv f₂) z + (c - (a + b + 1) * z) * deriv f₂ z -
      a * b * f₂ z = 0)
    (hw' : ∀ z ∈ U, z * (1 - z) * deriv (deriv w) z + (c - (a + b + 1) * z) * deriv w z -
      a * b * w z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hW : f₁ z₀ * deriv f₂ z₀ - deriv f₁ z₀ * f₂ z₀ ≠ 0) :
    ∃ A B : ℂ, ∀ z ∈ U, w z = A * f₁ z + B * f₂ z := by
  -- On the dense subset `U ∩ {0, 1}ᶜ` every Wronskian of two solutions satisfies Abel's
  -- identity, so it is a constant multiple of `𝒲{f₁, f₂}`, which is nonzero at `z₀`.
  have hS : Dense ({0}ᶜ ∩ {1}ᶜ : Set ℂ) := by
    simpa only [Set.sdiff_eq] using (dense_compl_singleton (0 : ℂ)).sdiff_singleton 1
  have hW₁₂ := (hf₁.mul (hf₂.deriv hU)).sub ((hf₁.deriv hU).mul hf₂)
  have hratio {g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
      (hg₁' : ∀ z ∈ U, z * (1 - z) * deriv (deriv g₁) z + (c - (a + b + 1) * z) * deriv g₁ z -
        a * b * g₁ z = 0)
      (hg₂' : ∀ z ∈ U, z * (1 - z) * deriv (deriv g₂) z + (c - (a + b + 1) * z) * deriv g₂ z -
        a * b * g₂ z = 0) :
      ∃ K : ℂ, ∀ z ∈ U, g₁ z * deriv g₂ z - deriv g₁ z * g₂ z =
        K * (f₁ z * deriv f₂ z - deriv f₁ z * f₂ z) :=
    hU.exists_eq_const_mul_of_hasDerivAt_mul hUc hS
      ((hg₁.mul (hg₂.deriv hU)).sub ((hg₁.deriv hU).mul hg₂)) hW₁₂ hz₀ hW
      (fun z hz => hasDerivAt_wronskian_of_hypergeometricEquation_of_mem hU hg₁ hg₂ hz.1
        (mem_compl_singleton_iff.1 hz.2.1) (mem_compl_singleton_iff.1 hz.2.2) (hg₁' z hz.1)
        (hg₂' z hz.1))
      (fun z hz => hasDerivAt_wronskian_of_hypergeometricEquation_of_mem hU hf₁ hf₂ hz.1
        (mem_compl_singleton_iff.1 hz.2.1) (mem_compl_singleton_iff.1 hz.2.2) (hf₁' z hz.1)
        (hf₂' z hz.1))
  obtain ⟨A, hA⟩ := hratio hw hf₂ hw' hf₂'
  obtain ⟨B, hB⟩ := hratio hf₁ hw hf₁' hw'
  -- `𝒲{f₁, f₂} w = 𝒲{f₁, f₂} (A f₁ + B f₂)` on `U`, so `w = A f₁ + B f₂` near `z₀`, where
  -- `𝒲{f₁, f₂}` has no zero; the identity theorem extends this to `U`.
  refine ⟨A, B, fun z hz => (hw.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (((hf₁.const_mul A).add (hf₂.const_mul B)).analyticOnNhd hU) hUc hz₀ ?_ hz⟩
  filter_upwards [((hW₁₂.differentiableAt (hU.mem_nhds hz₀)).continuousAt).eventually_ne hW,
    hU.mem_nhds hz₀] with z hWz hz
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply] at hWz ⊢
  apply mul_right_cancel₀ hWz
  linear_combination f₁ z * hA z hz + f₂ z * hB z hz

end TauCeti
