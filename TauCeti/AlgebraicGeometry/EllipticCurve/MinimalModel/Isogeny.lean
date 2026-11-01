/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
-- Proof-only: a change of variables is an isogeny.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange

/-!
# Isogenies between minimal equations

Let `R` be a discrete valuation ring with fraction field `K`. The chosen minimal equation
`W.minimal R` of a Weierstrass curve `W` over `K` is obtained from `W` by a change of variables
(`WeierstrassCurve.exists_smul_eq_minimal`), and a change of variables is an isogeny. Composing an
isogeny `W₁ → W₂` with the changes of variables to and from the minimal equations gives an isogeny
between the minimal equations. So statements about isogenous minimal equations, such as their
having good reduction together, apply to arbitrary isogenous Weierstrass curves.

## Main results

* `TauCeti.Isogeny.nonempty_isogeny_minimal`: isogenous curves have isogenous chosen minimal
  equations.
-/

public section

open WeierstrassCurve

namespace TauCeti.Isogeny

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {W₁ W₂ : WeierstrassCurve K}

/-- **Isogenous curves have isogenous minimal equations**: if there is an isogeny `W₁ → W₂` of
Weierstrass curves over the fraction field of a discrete valuation ring `R`, there is one between
the chosen minimal equations `W₁.minimal R` and `W₂.minimal R`, composing with the changes of
variables to and from them. -/
theorem nonempty_isogeny_minimal (φ : Isogeny W₁.toAffine W₂.toAffine) :
    Nonempty (Isogeny (W₁.minimal R).toAffine (W₂.minimal R).toAffine) := by
  obtain ⟨C₁, hC₁⟩ := W₁.exists_smul_eq_minimal R
  obtain ⟨C₂, hC₂⟩ := W₂.exists_smul_eq_minimal R
  refine ⟨(variableChangeIsogeny C₂ hC₂).comp <| φ.comp (variableChangeIsogeny C₁⁻¹ ?_)⟩
  rw [← hC₁, inv_smul_smul]

end TauCeti.Isogeny

end
