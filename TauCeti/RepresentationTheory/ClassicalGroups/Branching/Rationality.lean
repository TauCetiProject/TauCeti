/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.BlockSucc
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality

/-!
# Rational representations under the block inclusion

The block inclusion `TauCeti.glBlockSucc : GL (Fin n) ℂ →* GL (Fin (n + 1)) ℂ` replaces a
matrix `g` by `diag(g, 1)`.  Polynomial and rational functions pull back along it
(`TauCeti.Matrix.GeneralLinearGroup.comp_glBlockSucc_mem_polynomialFunctions` and
`TauCeti.Matrix.GeneralLinearGroup.comp_glBlockSucc_mem_rationalFunctions`), so polynomial and
rational representations remain so after restriction.

Applying this to the rational Weyl representations gives the coordinate-regularity statement needed
by the `GL (n + 1) ↓ GL n` branching problem.  This file does not construct the multiplicity-free
decomposition of that restriction; the decomposition additionally needs the highest-weight
classification and complete reducibility.

## Main results

* `TauCeti.IsPolynomialRep.comp_glBlockSucc` and `TauCeti.IsRationalRep.comp_glBlockSucc`:
  polynomiality and rationality are preserved by restriction.
* `TauCeti.isRationalRep_rationalWeylRep_comp_glBlockSucc`: the restricted rational Weyl
  representation is rational.
-/

public section

universe v

namespace TauCeti

/-! ## Restriction of representations -/

section Representations

open _root_.TauCeti.Matrix.GeneralLinearGroup

variable {n : ℕ} {W : Type v} [AddCommMonoid W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin (n + 1)) ℂ) W}

/-- **A polynomial representation remains polynomial after restriction along the block
inclusion.** -/
theorem IsPolynomialRep.comp_glBlockSucc (h : IsPolynomialRep ρ) :
    IsPolynomialRep (ρ.comp (glBlockSucc ℂ n)) := by
  obtain ⟨b, -⟩ := (isPolynomialRep_iff ρ).mp h
  exact (isPolynomialRep_iff_forall_mem_polynomialFunctions b).mpr fun i j =>
    comp_glBlockSucc_mem_polynomialFunctions
      ((isPolynomialRep_iff_forall_mem_polynomialFunctions b).mp h i j)

/-- **A rational representation remains rational after restriction along the block inclusion.** -/
theorem IsRationalRep.comp_glBlockSucc (h : IsRationalRep ρ) :
    IsRationalRep (ρ.comp (glBlockSucc ℂ n)) := by
  obtain ⟨b, -⟩ := (isRationalRep_iff ρ).mp h
  exact (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j =>
    comp_glBlockSucc_mem_rationalFunctions
      ((isRationalRep_iff_forall_mem_rationalFunctions b).mp h i j)

end Representations

/-! ## Restricted rational Weyl representations -/

/-- **The restriction of a rational Weyl representation from `GL (n + 1)` to `GL n` is
rational.**  This is the rationality input for its multiplicity-free branching decomposition. -/
@[simp]
theorem isRationalRep_rationalWeylRep_comp_glBlockSucc (n : ℕ)
    (l : DominantWeight (n + 1)) :
    IsRationalRep ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)) :=
  (isRationalRep_rationalWeylRep (n + 1) l).comp_glBlockSucc

end TauCeti
