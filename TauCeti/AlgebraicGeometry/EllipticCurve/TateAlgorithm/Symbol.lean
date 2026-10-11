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
it has symbol `Iₙ`, where `n` is positive. This is the first branch-level interface for the
algorithm; the additive branches and their component data are developed separately.

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
def goodReductionSymbol (_W : WeierstrassCurve K) : TauCeti.ReductionSymbol :=
  TauCeti.ReductionSymbol.I 0

omit [Field K] in
/-- The good-reduction branch returns the symbol `I₀`. -/
theorem goodReductionSymbol_eq_I0 (W : WeierstrassCurve K) :
    W.goodReductionSymbol = TauCeti.ReductionSymbol.I 0 := (rfl)
attribute [simp] goodReductionSymbol_eq_I0

private theorem not_hasGoodReduction_minimal_of_hasMultiplicativeReduction
    (W : WeierstrassCurve K) [W.HasMultiplicativeReduction R] :
    ¬ (W.minimal R).HasGoodReduction R := by
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  have hval := W.valuation_Δ_eq_of_isMinimal_smul R C hC
  intro hgood
  exact (inferInstance : W.HasMultiplicativeReduction R).badReduction.ne
    (hval.symm.trans hgood.goodReduction)

/-- **The output of Tate's multiplicative branch**: a curve with multiplicative reduction has
symbol `Iₙ`, where `n = v(Δ_min)`. The local minimal-discriminant valuation makes the symbol
independent of the chosen integral equation. -/
noncomputable def multiplicativeReductionSymbol (W : WeierstrassCurve K) [W.IsElliptic] :
    TauCeti.ReductionSymbol :=
  TauCeti.ReductionSymbol.I (W.localMinimalDiscriminantValuation R)

/-- The index in the multiplicative reduction symbol is the minimal discriminant valuation. -/
@[simp]
theorem multiplicativeReductionSymbol_eq_I (W : WeierstrassCurve K) [W.IsElliptic] :
    W.multiplicativeReductionSymbol (R := R) =
      TauCeti.ReductionSymbol.I (W.localMinimalDiscriminantValuation R) := (rfl)

/-- In the multiplicative branch, the index `n` in `Iₙ` is positive. -/
theorem multiplicativeReductionSymbol_index_pos (W : WeierstrassCurve K) [W.IsElliptic]
    [W.HasMultiplicativeReduction R] :
    0 < W.localMinimalDiscriminantValuation R :=
  (W.localMinimalDiscriminantValuation_pos_iff R).2
    (not_hasGoodReduction_minimal_of_hasMultiplicativeReduction W)

end WeierstrassCurve

end
