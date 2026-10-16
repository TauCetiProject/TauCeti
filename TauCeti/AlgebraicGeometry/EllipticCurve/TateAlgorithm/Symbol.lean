/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation

/-!
# Reduction symbols from Tate's algorithm

`ReductionSymbol` records the possible outputs of Tate's algorithm on a minimal Weierstrass
equation. The multiplicative branch is classified by the valuation of the minimal discriminant:
it has symbol `Iₙ`, where `n` is positive. This type is the codomain for classifiers that state the
output of an individual branch of the algorithm.

The symbols and the multiplicative branch follow Tate's algorithm (J. Tate, *Algorithm for
determining the type of a singular fibre in an elliptic pencil*, LNM 476, 1975).
-/

public section

/-- The possible reduction symbols in Tate's algorithm for an elliptic curve over a discrete
valuation ring. `I 0` and `IStar 0` are the symbols `I₀` and `I₀*`; positive indices give `Iₙ` and
`Iₙ*`, respectively. -/
inductive TauCeti.ReductionSymbol where
  /-- Symbol `Iₙ`; `n = 0` means good reduction. -/
  | I (n : ℕ)
  /-- Additive reduction, with symbol `II`. -/
  | II
  /-- Additive reduction, with symbol `III`. -/
  | III
  /-- Additive reduction, with symbol `IV`. -/
  | IV
  /-- Symbol `Iₙ*`; `n = 0` gives `I₀*`. -/
  | IStar (n : ℕ)
  /-- Additive reduction, with symbol `IV*`. -/
  | IVStar
  /-- Additive reduction, with symbol `III*`. -/
  | IIIStar
  /-- Additive reduction, with symbol `II*`. -/
  | IIStar
  deriving DecidableEq, Repr

namespace WeierstrassCurve

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The output of Tate's good-reduction branch** is `I₀`. -/
def goodReductionSymbol (_W : WeierstrassCurve K)
    [_hgood : WeierstrassCurve.HasGoodReduction R _W] :
    TauCeti.ReductionSymbol :=
  TauCeti.ReductionSymbol.I 0

/-- The simplification rule evaluating the good-reduction symbol to `I₀`. -/
@[simp]
theorem goodReductionSymbol_eq (W : WeierstrassCurve K)
    [WeierstrassCurve.HasGoodReduction R W] :
    W.goodReductionSymbol (R := R) = TauCeti.ReductionSymbol.I 0 := (rfl)

/-- **The output of Tate's multiplicative branch**: a curve with multiplicative reduction has
symbol `Iₙ`, where `n = v(Δ_min)`. The local minimal-discriminant valuation makes the symbol
independent of the chosen integral equation. -/
noncomputable def multiplicativeReductionSymbol (W : WeierstrassCurve K) [W.IsElliptic]
    [_hmult : WeierstrassCurve.HasMultiplicativeReduction R W] : TauCeti.ReductionSymbol :=
  TauCeti.ReductionSymbol.I (W.localMinimalDiscriminantValuation R)

/-- The simplification rule identifying the multiplicative-reduction symbol with `Iₙ`, where
`n = v(Δ_min)`. -/
@[simp]
theorem multiplicativeReductionSymbol_eq (W : WeierstrassCurve K) [W.IsElliptic]
    [WeierstrassCurve.HasMultiplicativeReduction R W] :
    W.multiplicativeReductionSymbol (R := R) =
      TauCeti.ReductionSymbol.I (W.localMinimalDiscriminantValuation R) := (rfl)

end WeierstrassCurve

end
