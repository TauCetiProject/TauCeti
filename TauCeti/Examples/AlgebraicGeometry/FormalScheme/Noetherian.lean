/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Noetherian
public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Checks for locally noetherian formal schemes

`Spf ℤ_[p]` is a noetherian formal scheme, and so are its completed localisations. Locally
noetherian ordinary schemes are locally noetherian formal schemes, and the affine formal opens of
a locally noetherian formal scheme have noetherian rings of sections, whatever chart exhibits
them. A non-noetherian adic ring, such as a discrete ring of polynomials in infinitely many
variables, has a formal spectrum that is not locally noetherian.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry TauCeti TauCeti.FormalScheme

noncomputable section

namespace TauCeti.Examples.FormalScheme.Noetherian

variable (p : ℕ) [Fact p.Prime]

-- The formal spectrum of the `p`-adic integers is a noetherian formal scheme.
example : (ofSpf ℤ_[p]).IsNoetherian := inferInstance

-- Its basic open subsets are noetherian formal schemes too.
example (f : ℤ_[p]) : (ofSpf (AdicRing.CompletedAway ℤ_[p] f)).IsNoetherian := inferInstance

-- Stalks of `Spf ℤ_[p]` are noetherian.
example (x : ofSpf ℤ_[p]) : IsNoetherianRing ((ofSpf ℤ_[p]).presheaf.stalk x) := inferInstance

-- Every affine formal open of a locally noetherian formal scheme has a noetherian ring of
-- sections, including those not given by the defining charts.
example (X : FormalScheme) [X.IsLocallyNoetherian] (U : Opens X) (hU : X.IsAffineOpen U) :
    IsNoetherianRing (X.presheaf.obj (Opposite.op U)) :=
  hU.isNoetherianRing

-- Open formal subschemes of `Spf ℤ_[p]` are locally noetherian.
example (U : Opens (ofSpf ℤ_[p])) : ((ofSpf ℤ_[p]).restrict U).IsLocallyNoetherian :=
  inferInstance

-- A noetherian scheme, such as `Spec ℤ`, gives a noetherian formal scheme.
example : (Spec (CommRingCat.of ℤ)).toFormalScheme.IsNoetherian := inferInstance

section NonNoetherian

/-- The discrete topology on a polynomial ring in countably many variables. -/
local instance mvPolynomialTopology : TopologicalSpace (MvPolynomial ℕ ℚ) := ⊥

/-- Discreteness of the topology on the polynomial ring. -/
local instance mvPolynomialDiscreteTopology : DiscreteTopology (MvPolynomial ℕ ℚ) := ⟨rfl⟩

-- A discrete ring that is not noetherian has a formal spectrum that is not locally noetherian.
example : ¬ (ofSpf (MvPolynomial ℕ ℚ)).IsLocallyNoetherian := by
  rw [isLocallyNoetherian_ofSpf_iff]
  exact MvPolynomial.not_isNoetherianRing ℕ ℚ

end NonNoetherian

end TauCeti.Examples.FormalScheme.Noetherian
