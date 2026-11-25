/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic

/-!
# Multiplying classical symbols by smooth functions of the position

The product `ψ(x) a(x, ξ)` of a classical symbol `a` of order `m` with a smooth scalar function `ψ`
of the position is a classical symbol of order `m` (`TauCeti.ClassicalSymbol.smulLeft`), the
symbol of `ψ Op(a)`, for instance the left factor of a compression `φ Op(a) ψ` by cutoffs. Its full
symbol is `TauCeti.Symbol.smulLeft` (`TauCeti.ClassicalSymbol.toSymbol_smulLeft`), whose
coefficient and quantization are `TauCeti.Symbol.coefficient_smulLeft` and
`TauCeti.Symbol.quantizeSchwartzValue_smulLeft`, its homogeneous terms are `ψ(x) aⱼ(x, ξ)`
(`TauCeti.ClassicalSymbol.coefficient_term_smulLeft`), and its principal symbol is
`ψ(x) σ(a)(x, ξ)` (`TauCeti.ClassicalSymbol.coefficient_principal_smulLeft`).
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti.ClassicalSymbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The product `ψ(x) a(x, ξ)` of a classical symbol `a` with a smooth scalar function `ψ` of the
position, a classical symbol of the same order as `a`: the composition with the classical symbol of
multiplication by `ψ`. -/
def smulLeft {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ) (a : ClassicalSymbol n V W m) :
    ClassicalSymbol n V W m :=
  inclusion 0 (by simp)
    ((ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ W) (hψ.smul contDiff_const)).comp a)

variable {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ) (a : ClassicalSymbol n V W m)

@[simp]
theorem toSymbol_smulLeft : (smulLeft hψ a).toSymbol = Symbol.smulLeft hψ a.toSymbol := by
  ext1
  funext p
  simp [smulLeft, Symbol.coefficient_inclusion, ContinuousLinearMap.smul_comp]

/-- The homogeneous terms of `ψ(x) a(x, ξ)` are `ψ(x) aⱼ(x, ξ)`. -/
@[simp]
theorem coefficient_term_smulLeft (j : ℕ) (x ξ : CoordinateSpace n) :
    ((smulLeft hψ a).term j).coefficient (x, ξ) = ψ x • (a.term j).coefficient (x, ξ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [HomogeneousSymbol.zero_covector]
  have hψξ := coefficient_principal_ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ W)
    (hψ.smul contDiff_const) (x := x) hξ
  rw [coefficient_principal] at hψξ
  ext v
  simp [smulLeft, coefficient_compTerms, Finset.sum_range_succ', hψξ]

/-- The principal symbol of `ψ(x) a(x, ξ)` is `ψ(x) σ(a)(x, ξ)`. -/
theorem coefficient_principal_smulLeft (x ξ : CoordinateSpace n) :
    (smulLeft hψ a).principal.coefficient (x, ξ) = ψ x • a.principal.coefficient (x, ξ) := by
  simp

end TauCeti.ClassicalSymbol
