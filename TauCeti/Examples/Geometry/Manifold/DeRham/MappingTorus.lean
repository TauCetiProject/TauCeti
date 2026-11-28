/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MappingTorus

/-!
# Examples: the period of a closed orbit and the sign of its exponent

Let `φ` be a diffeomorphism of a manifold `M` and `Y_φ` its mapping torus, with time form `dt`.
The series of the mapping-torus application are indexed by `H₁(Y_φ; ℤ)` and specialized in one
variable through the time period `N(h) = ∫_h dt` (`TauCeti.SmoothMappingTorus.timePeriodHom`).
The suspension flow is the negative gradient flow of the closed one-form `α = -dt`, whose period
homomorphism is `P_α = -N` (`TauCeti.SmoothMappingTorus.homologyPeriodHom_neg_timeForm`). This
file checks the signs on a closed orbit.

The class `[γ]` of the closed orbit through a point of period `d` has `N [γ] = d`
(`TauCeti.SmoothMappingTorus.timePeriodHom_closedOrbitHomologyClass`) and
`P_α [γ] = -d` (`homologyPeriodHom_neg_timeForm_closedOrbitHomologyClass`). For `d > 0` the time
period is positive (`TauCeti.SmoothMappingTorus.timePeriodHom_closedOrbitHomologyClass_pos`)
while `P_α [γ]` is negative (`homologyPeriodHom_neg_timeForm_closedOrbitHomologyClass_neg`):
the orbit series, whose support is finite below in the exponent `N`, must invert the exponents of
`P_α`; read with `P_α` as the exponent, every closed orbit would sit at negative period.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and
  Seiberg–Witten invariants of 3-manifolds*, Topology 38 (1999), 861–888.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.Examples.MappingTorus

open SmoothMappingTorus

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M} {d : ℕ} {x : M}

/-- **The period of a closed orbit for `α = -dt`.** The class `[γ]` of the closed orbit through a
point of period `d` has `P_α [γ] = ∫_γ (-dt) = -d`. -/
theorem homologyPeriodHom_neg_timeForm_closedOrbitHomologyClass (hx : IsPeriodicPt φ d x) :
    homologyPeriodHom (-(timeForm φ).val) (closedOrbitHomologyClass hx) = -d := by
  rw [homologyPeriodHom_neg_timeForm, AddMonoidHom.neg_apply,
    timePeriodHom_closedOrbitHomologyClass]

/-- **A closed orbit has negative period for `α = -dt`.** For a point of period `d > 0`, the class
`[γ]` of its closed orbit has `P_α [γ] = -d < 0`, although its time period `N [γ] = d` is positive
(`TauCeti.SmoothMappingTorus.timePeriodHom_closedOrbitHomologyClass_pos`). -/
theorem homologyPeriodHom_neg_timeForm_closedOrbitHomologyClass_neg (hx : IsPeriodicPt φ d x)
    (hd : 0 < d) : homologyPeriodHom (-(timeForm φ).val) (closedOrbitHomologyClass hx) < 0 := by
  rw [homologyPeriodHom_neg_timeForm_closedOrbitHomologyClass, neg_lt_zero]
  exact_mod_cast hd

end TauCeti.Examples.MappingTorus
