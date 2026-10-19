/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Isogeny

/-!
# Every isogeny is a Frobenius power followed by a Vélu quotient

Vélu's formulas construct, for a finite subgroup `Φ` of `W(F)`, the quotient isogeny
`veluIsogeny W Φ : W → W / Φ` (`Isogeny/Velu/Isogeny.lean`). This file shows that, up to a change
of variables on the target, these quotients together with the relative Frobenius powers reach
every isogeny between elliptic curves over a separably closed field.

* An isogeny `ψ : W → W'` whose kernel has `deg ψ` points is the Vélu isogeny by its kernel
  followed by a change of variables `W / ker ψ ≅ W'`, and that change of variables is unique.
  Over a separably closed field this applies to every separable isogeny (Silverman III.4.10(c),
  III.4.12).
* Over a separably closed field of exponential characteristic `p`, every isogeny `ψ : W → W'`
  factors as `ψ = λ ∘ (W⁽ᵖʳ⁾ → W⁽ᵖʳ⁾ / Φ) ∘ F^r`, with `F^r : W → W⁽ᵖʳ⁾` the `r`-fold relative
  Frobenius, `p ^ r` the inseparable degree of `ψ`, `Φ` a finite subgroup of `W⁽ᵖʳ⁾` with as many
  points as the separable degree of `ψ`, and `λ` the isogeny of a change of variables
  (Silverman II.2.12 and III.4.12).

Vélu's construction sees only a finite set of points, so the inseparable part of an isogeny is
invisible to it and is supplied by the relative Frobenius instead. Over a field that is not
separably closed the kernel of a separable isogeny, which consists of rational points, can be too
small, and the first statement carries the count `#ker ψ = deg ψ` as a hypothesis.

## Main results

* `WeierstrassCurve.Affine.existsUnique_variableChangeIsogeny_comp_veluIsogeny_eq`: an isogeny
  whose kernel has as many points as its degree is the Vélu isogeny by its kernel followed by a
  unique change of variables.
* `WeierstrassCurve.Affine.existsUnique_variableChangeIsogeny_comp_veluIsogeny_eq_of_isSeparable`:
  over a separably closed field this holds for every separable isogeny.
* `exists_variableChangeIsogeny_comp_veluIsogeny_comp_iterateRelativeFrobeniusIsogeny_eq`, in
  the same namespace: over a separably closed field every isogeny is a relative Frobenius power,
  followed by a Vélu isogeny, followed by a change of variables.

## References

* J. Vélu, *Isogénies entre courbes elliptiques*, C. R. Acad. Sci. Paris Sér. A 273 (1971),
  238–241.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12, III.4.10 and
  III.4.12.
-/

public section

open TauCeti

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W W' : Affine F} [W.IsElliptic] [W'.IsElliptic]

/-- **An isogeny whose kernel counts its degree is a Vélu quotient** (Silverman III.4.12): if
`ψ : W → W'` has `#ker ψ = deg ψ`, then `ψ` is the Vélu isogeny `W → W / ker ψ` followed by the
isogeny of a change of variables `C` with `C • (W / ker ψ) = W'`, and `C` is unique. -/
theorem existsUnique_variableChangeIsogeny_comp_veluIsogeny_eq (ψ : Isogeny W W')
    (hψ : Nat.card ψ.ker = ψ.degree) :
    ∃! C : VariableChange F, ∃ h : C • (veluCurve W ψ.ker).toAffine = W',
      (Isogeny.variableChangeIsogeny C h).comp (veluIsogeny W ψ.ker) = ψ :=
  Isogeny.existsUnique_variableChangeIsogeny_comp_eq_of_ker_eq (by simp) hψ
    (ker_veluIsogeny W ψ.ker)

/-- **A separable isogeny over a separably closed field is a Vélu quotient** (Silverman III.4.12):
it is the Vélu isogeny by its kernel followed by the isogeny of a unique change of variables. -/
theorem existsUnique_variableChangeIsogeny_comp_veluIsogeny_eq_of_isSeparable [IsSepClosed F]
    (ψ : Isogeny W W') [Algebra.IsSeparable ψ.fieldPullback.fieldRange W.FunctionField] :
    ∃! C : VariableChange F, ∃ h : C • (veluCurve W ψ.ker).toAffine = W',
      (Isogeny.variableChangeIsogeny C h).comp (veluIsogeny W ψ.ker) = ψ :=
  existsUnique_variableChangeIsogeny_comp_veluIsogeny_eq ψ ψ.card_ker_eq_degree

/-- **Every isogeny is a Frobenius power followed by a Vélu quotient** (Silverman II.2.12 and
III.4.12). Over a separably closed field of exponential characteristic `p`, an isogeny
`ψ : W → W'` factors as the `r`-fold relative Frobenius `W → W⁽ᵖʳ⁾`, followed by the Vélu isogeny
`W⁽ᵖʳ⁾ → W⁽ᵖʳ⁾ / Φ` by a finite subgroup `Φ`, followed by the isogeny of a change of variables
`C` with `C • (W⁽ᵖʳ⁾ / Φ) = W'`. Here `p ^ r` is the inseparable degree of `ψ` and `Φ` has as
many points as the separable degree of `ψ`. -/
theorem exists_variableChangeIsogeny_comp_veluIsogeny_comp_iterateRelativeFrobeniusIsogeny_eq
    [IsSepClosed F] (p : ℕ) [ExpChar F p] (ψ : Isogeny W W') :
    ∃ (r : ℕ) (Φ : AddSubgroup ((W.map (iterateFrobenius F p r))⁄F).toAffine.Point)
      (_ : Finite Φ) (C : VariableChange F)
      (h : C • (veluCurve (W.map (iterateFrobenius F p r)) Φ).toAffine = W'),
      ψ.inseparableDegree = p ^ r ∧ Nat.card Φ = ψ.separableDegree ∧
        (Isogeny.variableChangeIsogeny C h).comp
          ((veluIsogeny (W.map (iterateFrobenius F p r)) Φ).comp
            (Isogeny.iterateRelativeFrobeniusIsogeny p W r)) = ψ := by
  obtain ⟨r, χ, _, hχ⟩ := Isogeny.exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p ψ
  obtain ⟨C, ⟨h, hC⟩, -⟩ := existsUnique_variableChangeIsogeny_comp_veluIsogeny_eq_of_isSeparable χ
  refine ⟨r, χ.ker, inferInstance, C, h,
    Isogeny.inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ,
    χ.card_ker_eq_degree.trans
      (Isogeny.degree_eq_separableDegree_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ), ?_⟩
  rw [← Isogeny.comp_assoc, hC, hχ]

end WeierstrassCurve.Affine

end
