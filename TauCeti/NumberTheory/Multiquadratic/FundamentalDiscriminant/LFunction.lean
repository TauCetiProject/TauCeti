/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
public import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel

/-!
# Positive continued L-values and Siegel's bound for fundamental discriminants

For a fundamental discriminant `D ≠ 1`, the complex realization of its primitive quadratic
character has positive real continued L-values on the real interval `[1, ∞)`. The endpoint
uses the continued `DirichletCharacter.LFunction`, not the Dirichlet series, whose convergence
at `1` is not assumed.

Siegel's lower bound `c * |D| ^ (-ε) ≤ Re L(1, χ_D)` holds uniformly for all fundamental
discriminants `D ≠ 1`, stated as
`TauCeti.Multiquadratic.exists_pos_forall_rpow_le_fundamentalDiscriminantCharCast_LFunction_one_re`.

## Main results

* `fundamentalDiscriminantCharCast_LFunction_pos`: `0 < L(s, χ_D)` for `s ≥ 1` and `D ≠ 1`,
  providing the nonvanishing input for the class-number formula.
* `exists_pos_forall_rpow_le_fundamentalDiscriminantCharCast_LFunction_one_re`: Siegel's lower
  bound `c * |D| ^ (-ε) ≤ Re L(1, χ_D)` for all fundamental discriminants `D ≠ 1`.

## References

* C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935), 83–86.
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
-/

public section

namespace TauCeti.Multiquadratic

open scoped ComplexOrder

/-- The continued L-function of the fundamental-discriminant character is positive real on
`[1, ∞)`, for every fundamental discriminant other than `1`. -/
theorem fundamentalDiscriminantCharCast_LFunction_pos {D : ℤ} [NeZero D.natAbs]
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) {s : ℝ} (hs : 1 ≤ s) :
    0 < (fundamentalDiscriminantCharCast ℂ D hD).LFunction s := by
  exact DirichletCharacter.LFunction_pos_of_one_le
    (fundamentalDiscriminantCharCast_isQuadratic hD)
    (fun h ↦ hD1 ((fundamentalDiscriminantCharCast_eq_one_iff hD).mp h)) hs

/-- **Siegel's theorem for fundamental-discriminant characters.** For every `ε > 0` there exists
`c > 0` such that for every fundamental discriminant `D ≠ 1`, the associated complex quadratic
Dirichlet character `χ_D` of conductor `|D|` satisfies `c * |D| ^ (-ε) ≤ Re L(1, χ_D)`. -/
theorem exists_pos_forall_rpow_le_fundamentalDiscriminantCharCast_LFunction_one_re {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (D : ℤ) [NeZero D.natAbs] (hD : Int.IsFundamentalDiscr D), D ≠ 1 →
      c * |(D : ℝ)| ^ (-ε) ≤
        ((fundamentalDiscriminantCharCast ℂ D hD).LFunction 1).re := by
  obtain ⟨c, hc, hS⟩ := TauCeti.DirichletCharacter.exists_pos_forall_rpow_le_LFunction_one_re hε
  refine ⟨c, hc, fun D _ hD hD1 ↦ ?_⟩
  have h := hS D.natAbs (fundamentalDiscriminantCharCast ℂ D hD)
    (fundamentalDiscriminantCharCast_isQuadratic hD)
    (mt (fundamentalDiscriminantCharCast_eq_one_iff hD).mp hD1)
  rwa [Nat.cast_natAbs, Int.cast_abs] at h

end TauCeti.Multiquadratic
