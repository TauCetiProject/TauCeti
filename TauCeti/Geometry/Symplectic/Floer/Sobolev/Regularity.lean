/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.CauchyRiemann
public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation

/-!
# Floer cylinders in `W^{1,p}` are smooth

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J_z` a family of almost complex
structures on `V` and `K = Ks ds + Kt dt` a Hamiltonian perturbation, all of period one in `t`.
The Floer equation on the cylinder `ℝ × S¹` is

`∂s u - X_Ks(u) + J(z, u) (∂t u - X_Kt(u)) = 0`,

the zero set of `TauCeti.SymplecticForm.floerOperator`. In the transversality and gluing arguments
of Floer theory its solutions are sought near a reference map `w` of the cylinder, as `u = w + ξ`
with an increment `x = (ξ, ξ_s, ξ_t)` in the Sobolev space `W^{1,p}(ℝ × S¹, V)`, `p > 2`
(`TauCeti.CylinderSobolev.W1p`), whose value has the continuous representative
`TauCeti.CylinderSobolev.continuousValue p x`. Such a `u` solves the Floer equation when

`∂s w + ξ_s - X_Ks(u) + J(z, u) (∂t w + ξ_t - X_Kt(u)) = 0`

almost everywhere on the strip `ℝ × [0, 1]`. This file shows that `u` is then as regular as the
data: if `w`, `J` are of class `C^ℓ` and `Ks`, `Kt` of class `C^(ℓ+1)`, `ℓ ≥ 1`, then `u` is of
class `C^ℓ` (`TauCeti.SymplecticForm.contDiff_add_continuousValue_of_ae_floer`), in particular
smooth for smooth data. The Floer equation is the quasilinear equation
`∂s u + A(z, u) ∂t u + G(z, u) = 0` with `A = J` and `G = -X_Ks - J X_Kt`, so this is
`TauCeti.CylinderSobolev.contDiff_add_continuousValue_of_ae_eq_zero`.

## References

* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292, on the `W^{1,p}` setting of the Floer equation.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.4,
  on elliptic bootstrapping.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Floer cylinders in `W^{1,p}` are regular.** Let `2 < p < ∞` and `1 ≤ ℓ ≤ ∞`, let `w` and the
family of complex structures `J` be of class `C^ℓ` and the Hamiltonians `Ks`, `Kt` of class
`C^(ℓ+1)`, jointly in all variables, all of period one in `t`. If `x = (ξ, ξ_s, ξ_t) ∈ W^{1,p}` and
`u = w + ξ`, with `ξ` its continuous representative, satisfies `J(z, u z)² = -1` and the Floer
equation `∂s w + ξ_s - X_Ks(u) + J(z, u) (∂t w + ξ_t - X_Kt(u)) = 0` almost everywhere on the
strip, then `u` is of class `C^ℓ` on the plane. -/
theorem contDiff_add_continuousValue_of_ae_floer (ω : SymplecticForm V) (hp : 2 < p)
    (hpt : p ≠ ∞) {ℓ : ℕ∞} (hℓ : 1 ≤ ℓ) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    (hJ : ContDiff ℝ ℓ fun y : (ℝ × ℝ) × V ↦ J y.1 y.2)
    (hKs : ContDiff ℝ (ℓ + 1) (Function.uncurry Ks))
    (hKt : ContDiff ℝ (ℓ + 1) (Function.uncurry Kt))
    (hJper : ∀ s t, J (s, t + 1) = J (s, t)) (hKsper : ∀ s t, Ks (s, t + 1) = Ks (s, t))
    (hKtper : ∀ s t, Kt (s, t + 1) = Kt (s, t)) {w : ℝ × ℝ → V} (hw : ContDiff ℝ ℓ w)
    (hwper : ∀ s t, w (s, t + 1) = w (s, t)) (x : CylinderSobolev.W1p V p)
    (hJ2 : ∀ᵐ z ∂stripMeasure,
      J z (w z + continuousValue p x z) * J z (w z + continuousValue p x z) = -1)
    (h : ∀ᵐ z ∂stripMeasure,
      fderiv ℝ w z (1, 0) + ((x : Lp (V × V × V) p stripMeasure) z).2.1 -
          ω.hamiltonianVectorField (Ks z) (w z + continuousValue p x z) +
        J z (w z + continuousValue p x z)
          (fderiv ℝ w z (0, 1) + ((x : Lp (V × V × V) p stripMeasure) z).2.2 -
            ω.hamiltonianVectorField (Kt z) (w z + continuousValue p x z)) = 0) :
    ContDiff ℝ ℓ fun z ↦ w z + continuousValue p x z := by
  have hXs := ω.contDiff_hamiltonianVectorField_uncurry (n := ℓ) hKs
  have hXt := ω.contDiff_hamiltonianVectorField_uncurry (n := ℓ) hKt
  refine contDiff_add_continuousValue_of_ae_eq_zero hp hpt hℓ hw hwper hJ
    (G := fun z v ↦ -ω.hamiltonianVectorField (Ks z) v - J z v (ω.hamiltonianVectorField (Kt z) v))
    (hXs.neg.sub (hJ.clm_apply hXt)) hJper (fun s t ↦ by simp [hKsper, hKtper, hJper]) x hJ2 ?_
  filter_upwards [h] with z hz
  rw [← hz, map_sub]
  abel

end TauCeti.SymplecticForm
