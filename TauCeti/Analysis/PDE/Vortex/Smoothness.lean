/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Semilinear

/-!
# Smoothness of continuous weak solutions of Taubes's reduced vortex equation

For coefficient functions `h` and `k`, the Euler–Lagrange equation of Taubes's functional
`TauCeti.Vortex.taubesFunctional` is the reduced vortex equation

`Δw = h (exp (2w) - 1) / 8 + k`.

For the background coefficients `TauCeti.Vortex.backgroundWeight` and
`TauCeti.Vortex.backgroundSource` of a polynomial `P`, a `C²` solution `w` makes the field
reconstructed from the amplitude `-log (1 + |P|²) / 2 + w` and the section `P` a solution of the
plane vortex equation
(`TauCeti.Vortex.laplacian_eq_iff_equation_amplitudeField_backgroundAmplitude_add_eq_zero`).
Taubes's existence proof minimizes the functional over `H¹`, so it produces a weak solution, and
must then show that the weak solution is smooth. This file proves the second half of that
regularity step on an open subset `Ω` of the plane: a weak solution `u ∈ H¹(Ω)` that agrees almost
everywhere on `Ω` with a function `w` continuous on `Ω` has `w` smooth on `Ω`
(`TauCeti.Vortex.contDiffOn_of_energyFormH1_eq_neg`). The weak form is

`∫_Ω ⟨∇u, ∇v⟩ = -∫_Ω (h (exp (2w) - 1) / 8 + k) v` for every `v ∈ H¹₀(Ω)`.

Continuity of weak solutions is the first half of the regularity step; it comes from Trudinger's
inequality, which controls `exp (2w)` for `w ∈ H¹`. Here the equation is the case `a = 1`,
`A = -h / 8`, `Φ(t) = exp (2t)`, `C = h / 8 - k` of the semilinear bootstrap
`TauCeti.PDE.UniformlyEllipticOn.contDiffOn_of_energyFormH1_eq`. The plane is
`EuclideanSpace ℝ (Fin 2)`, the space on which `TauCeti.W1p` carries the interior regularity
theory; neither the decay of `w` at infinity nor the weak equation of a minimizer is treated.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III, §4.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

open MeasureTheory TopologicalSpace
open scoped ContDiff

namespace TauCeti

namespace Vortex

/-- **Continuous weak solutions of Taubes's reduced vortex equation are smooth.** Let `h` and `k` be
smooth on an open subset `Ω` of the plane. If `u ∈ H¹(Ω)` agrees almost everywhere on `Ω` with a
function `w` continuous on `Ω`, and weakly solves `Δw = h (exp (2w) - 1) / 8 + k`, in the sense that
`∫_Ω ⟨∇u, ∇v⟩ = -∫_Ω (h (exp (2w) - 1) / 8 + k) v` for every `v ∈ H¹₀(Ω)`, then `w` is smooth on
`Ω`. -/
theorem contDiffOn_of_energyFormH1_eq_neg {Omega : Opens (EuclideanSpace ℝ (Fin 2))}
    {h k : EuclideanSpace ℝ (Fin 2) → ℝ} (hh : ContDiffOn ℝ ∞ h Omega)
    (hk : ContDiffOn ℝ ∞ k Omega) {u : W1p volume Omega 2} {w : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hw : ContinuousOn w Omega)
    (huw : (W1p.value u : EuclideanSpace ℝ (Fin 2) → ℝ) =ᵐ[volume.restrict (Omega : Set _)] w)
    (hu : ∀ v : W1p0 volume Omega 2, PDE.energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
      -∫ x in Omega, (h x * (Real.exp (2 * w x) - 1) / 8 + k x) *
        W1p.value (v : W1p volume Omega 2) x) :
    ContDiffOn ℝ ∞ w Omega := by
  refine (PDE.uniformlyEllipticOn_const_one_one _).contDiffOn_of_energyFormH1_eq (by simp)
    (fun _ _ => contDiffOn_const) (hh.neg.div_const 8) ((hh.div_const 8).sub hk)
    (Φ := fun t => Real.exp (2 * t)) (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
    hw huw fun v => ?_
  rw [hu v, ← integral_neg]
  congr 1
  ext x
  ring

end Vortex

end TauCeti
