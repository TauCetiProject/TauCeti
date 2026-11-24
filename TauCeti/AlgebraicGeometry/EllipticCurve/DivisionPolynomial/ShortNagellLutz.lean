/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Chris Birkbeck, David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Discriminant
-- Proof-only, and not reachable transitively: `Torsion/Discriminant.lean` imports this
-- module non-publicly, so `evalEval_ψ₂_of_isCharNeTwoNF` is not re-exported through it.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
-- Proof-only: `sq_dvd_cubic_discr`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.CubicDiscriminant
public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.AlgebraicGeometry.EllipticCurve.ShortWeierstrass

/-!
# The Nagell–Lutz theorem for a short Weierstrass model

For `A B : ℤ`, a nonzero rational point of finite order on `y² = x³ + Ax + B` has **integral**
coordinates, and its `y`-coordinate satisfies `y = 0` or `y² ∣ 4A³ + 27B²`. That is the classical
statement, and unlike the long-model theorem it has no order-two exception.

The exception disappears for a computable reason rather than by assumption. On a short model
`a₁ = a₃ = 0`, so `ψ₂ = 2y`; a point of order two makes `ψ₂` vanish, hence `y = 0`, and then the
curve equation exhibits `x` as a rational root of the **monic** `X³ + AX + B`, so `x` is an
integer too. The long model's honest bound `4x, 8y ∈ ℤ` therefore sharpens to full integrality
exactly here.

**Two forms of the divisibility.** For a model `y² = x³ + a₂x² + a₄x + a₆`, Mathlib's `Δ` is `16`
times the discriminant of the cubic `x³ + a₂x² + a₄x + a₆`, and the discriminant half below gives
`y²` dividing that discriminant. On the short model the cubic's discriminant is `-(4A³ + 27B²)`:
`lutz_nagell_sharp` states the classical `y² ∣ 4A³ + 27B²`, and `lutz_nagell` states `y² ∣ Δ`,
which is weaker by the factor `16`. At `A = 0`, `B = 1`, for instance, the first allows only
`y = ±1, ±3`, the second also `y = ±2, ±4, ±6, ±12`.

**No `Δ ≠ 0` hypothesis.** The source carries one on all three of its headline theorems and uses
it in none of them; what the argument needs is that the *point* is nonsingular, not that the curve
is elliptic. See the Provenance note.

## Main results

* `WeierstrassCurve.lutz_nagell_sharp`: the theorem at the explicit short model
  `y² = x³ + Ax + B` — integral coordinates together with `y₀ = 0 ∨ y₀² ∣ 4A³ + 27B²`.
* `WeierstrassCurve.lutz_nagell`: the same with the weaker `y₀ = 0 ∨ y₀² ∣ Δ`.
* `WeierstrassCurve.isInteger_of_torsion`: the integrality half, with no order-two exception, for
  any integral model in characteristic-≠-2 normal form.
* `WeierstrassCurve.y_eq_zero_or_sq_dvd_cubic_discr_of_torsion`: the discriminant half, likewise,
  with `y₀²` dividing the discriminant of the cubic `x³ + a₂x² + a₄x + a₆`.

The two halves are stated at `[W.IsCharNeTwoNF]`, i.e. `a₁ = a₃ = 0`, not at `shortCurve`: no
step uses `a₂ = 0`, and the cubic `X³ + a₂X² + a₄X + a₆` is monic either way. `lutz_nagell_sharp`
is their specialisation, and costs nothing to obtain — Mathlib's `isCharNeTwoNF_of_isShortNF`
supplies the instance.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.7.

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), from three files whose authorship differs and
is credited separately.

**`LutzNagellTheorem/Main.lean` — `Authors: Chris Birkbeck`.** Its three headline theorems are
`lutz_nagell_integrality` (`:40`), `lutz_nagell_discriminant` (`:53`) and `lutz_nagell` (`:71`).
The first and last are `isInteger_of_torsion` and `lutz_nagell` here; the second concludes
`y² ∣ Δ`, which the discriminant half below sharpens. That file carries its own author header, so
it is credited to Chris Birkbeck rather than to the project's usual pair, and the header of this
file names them accordingly.

**`LutzNagellTheorem/GeneralMain.lean` — no author header.** Its
`lutz_nagell_integrality_short` (`:155`) is where the order-two collapse is carried out; with no
header to go on it is credited to the project, as the sibling ports in this chain are.

**`LutzNagellTheorem/PIDMain.lean` — Chris Birkbeck and David Kurniadi Angdinata.** The file
carries no author header; these are its authors, and the header of this file names them. Its
`lutz_nagell_cubicDisc_discriminant` (`:438`) is the
discriminant half `y_eq_zero_or_sq_dvd_cubic_discr_of_torsion`, stated there over the fraction
field of a principal ideal domain, under a squarefreeness hypothesis on the order and with the
curve equation over the ring as a hypothesis, and with the cubic's discriminant written out in
`a₂, a₄, a₆`. Here the base is `ℤ`, where the squarefreeness holds outright, the equation follows
from the point's, and the discriminant is Mathlib's `Cubic.discr`. The source's proof runs through
`kappa_sq_dvd_four_Psi3_of_torsion` and two inline identities, which here are
`sq_evalEval_ψ₂_dvd_four_mul_eval_Ψ₃` and `sq_dvd_cubic_discr`. The specialisation to `a₂ = 0`
that its docstring states is `lutz_nagell_sharp`.

**The `Δ ≠ 0` hypothesis is dropped.** All three source theorems take
`hΔ : (shortCurveZ A B).Δ ≠ 0`; none uses it. It occurs in the three signatures and twice in the
bodies, both times in `lutz_nagell` forwarding it to the two theorems whose proofs never mention
it — a pass-through of a hypothesis nothing consumes, which this repository's `unusedArguments`
linter would reject in any case.

One further adaptation: `ψ₂ = 2y` is stated over an arbitrary commutative ring, since the point
lives over `ℚ` while the conclusion is over `ℤ` and both need it. The monic-root step follows the
source and goes through `isInteger_of_is_root_of_monic` — Mathlib's, which is what the source's
own lemma of that name restates.
-/

public section

open Polynomial

namespace WeierstrassCurve

open WeierstrassCurve

variable {W : WeierstrassCurve ℤ} [W.IsCharNeTwoNF]

/-- **Nagell–Lutz, discriminant half.** For a torsion point with integral coordinates on an
integral model `y² = x³ + a₂x² + a₄x + a₆`, either `y₀ = 0` or `y₀²` divides the discriminant of
the cubic `x³ + a₂x² + a₄x + a₆`.

Mathlib's `Δ` of such a model is `16` times that discriminant, so this implies `y₀² ∣ Δ` and is
sharper by the factor `16`. -/
theorem y_eq_zero_or_sq_dvd_cubic_discr_of_torsion {x y : ℚ}
    (hns : (W.baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    {x₀ y₀ : ℤ} (hx : algebraMap ℤ ℚ x₀ = x) (hy : algebraMap ℤ ℚ y₀ = y) :
    y₀ = 0 ∨ y₀ ^ 2 ∣ (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr := by
  refine or_iff_not_imp_left.mpr fun hy₀ ↦ ?_
  have hEq : W.toAffine.Equation x₀ y₀ :=
    (W.toAffine.map_equation (IsFractionRing.injective ℤ ℚ) x₀ y₀).mp (hx ▸ hy ▸ hns.left)
  -- `ψ₂` commutes with base change, and on this model it is `2y₀`, which is nonzero.
  have hκ : (W.baseChange ℚ).ψ₂.evalEval x y ≠ 0 := by
    rw [← hx, ← hy, WeierstrassCurve.baseChange, map_ψ₂, map_mapRingHom_evalEval,
      evalEval_ψ₂_of_isCharNeTwoNF]
    exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ ℚ)).mpr (mul_ne_zero two_ne_zero hy₀)
  have hΨ₃ := sq_evalEval_ψ₂_dvd_four_mul_eval_Ψ₃_rat hns htor hx hEq hκ
  -- `ψ₂ = 2y₀`, so the torsion input `(2y₀)² ∣ 4·Ψ₃(x₀)` is `y₀² ∣ Ψ₃(x₀)` once the `4` cancels.
  rw [evalEval_ψ₂_of_isCharNeTwoNF, mul_pow, show (2 : ℤ) ^ 2 = 4 by norm_num] at hΨ₃
  refine sq_dvd_cubic_discr W (a₁_of_isCharNeTwoNF W) (a₃_of_isCharNeTwoNF W) ?_
    ((mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp hΨ₃)
  rw [Affine.equation_iff] at hEq
  simpa [a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF] using hEq

/-- **Nagell–Lutz, integrality half.** On an integral model in characteristic-≠-2 normal form a
nonzero torsion point has integral coordinates — with *no* order-two exception.

The long-model theorem leaves order two aside with only `4x, 8y ∈ ℤ`. Here that case collapses:
`ψ₂ = 2y`, so order two forces `y = 0`, and the curve equation then exhibits `x` as a rational root
of the monic `X³ + a₂X² + a₄X + a₆`. The `a₂` term costs nothing — the cubic is monic either
way. -/
theorem isInteger_of_torsion {x y : ℚ}
    (hns : (W.baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns)) :
    IsLocalization.IsInteger ℤ x ∧ IsLocalization.IsInteger ℤ y := by
  rcases isInteger_or_order_two_of_torsion_rat hns htor with h | ⟨h2, -, -⟩
  · exact h
  · have hy : y = 0 := y_eq_zero_of_order_two two_ne_zero hns (h2 ▸ addOrderOf_nsmul_eq_zero _)
    refine ⟨?_, hy ▸ ⟨0, by simp⟩⟩
    have hmonic : (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : ℤ[X]).Monic := by
      simpa [add_assoc] using monic_X_pow_add (n := 3) (by compute_degree!)
    have heq := hns.left
    rw [Affine.equation_iff] at heq
    simp only [a₃_of_isCharNeTwoNF, WeierstrassCurve.baseChange, map_a₂, map_a₄, map_a₆,
      eq_intCast, zero_mul] at heq
    rw [hy] at heq
    refine isInteger_of_is_root_of_monic hmonic ?_
    -- `aeval_C` must fire before the casts are normalised: `eq_intCast` would otherwise rewrite
    -- `C W.a₂` to an `ℤ[X]` cast, which `aeval_C` no longer matches.
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    simp only [eq_intCast]
    linarith

variable (A B : ℤ)

/-- **The Nagell–Lutz theorem.** Let `A B : ℤ` and let `(x, y)` be a nonzero rational point of
finite order on `y² = x³ + Ax + B`. Then `x` and `y` are integers, and either `y = 0` or
`y² ∣ 4A³ + 27B²`.

This is the classical statement. It is the specialisation of the two theorems above at a short
model, where the cubic `x³ + Ax + B` has discriminant `-(4A³ + 27B²)`; Mathlib's
`isCharNeTwoNF_of_isShortNF` supplies the instance. No hypothesis `4A³ + 27B² ≠ 0` is needed — see
the module docstring. -/
theorem lutz_nagell_sharp {x y : ℚ}
    (hns : ((shortCurve A B).baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns)) :
    ∃ x₀ y₀ : ℤ, (x₀ : ℚ) = x ∧ (y₀ : ℚ) = y ∧
      (y₀ = 0 ∨ y₀ ^ 2 ∣ 4 * A ^ 3 + 27 * B ^ 2) := by
  obtain ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩ := isInteger_of_torsion hns htor
  refine ⟨x₀, y₀, by simpa using hx₀, by simpa using hy₀, ?_⟩
  have hdiscr : (Cubic.mk 1 0 A B).discr = -(4 * A ^ 3 + 27 * B ^ 2) := by
    simp only [Cubic.discr]
    ring
  have h := y_eq_zero_or_sq_dvd_cubic_discr_of_torsion hns htor hx₀ hy₀
  rwa [shortCurve_a₂, shortCurve_a₄, shortCurve_a₆, hdiscr, dvd_neg] at h

/-- **The Nagell–Lutz theorem, discriminant form.** Let `A B : ℤ` and let `(x, y)` be a nonzero
rational point of finite order on `y² = x³ + Ax + B`. Then `x` and `y` are integers, and either
`y = 0` or `y² ∣ Δ`.

Mathlib's `Δ` of this curve is `-16(4A³ + 27B²)`, so the divisibility is weaker than the classical
`y² ∣ 4A³ + 27B²` of `lutz_nagell_sharp` by the factor `16`, from which it follows. -/
theorem lutz_nagell {x y : ℚ}
    (hns : ((shortCurve A B).baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns)) :
    ∃ x₀ y₀ : ℤ, (x₀ : ℚ) = x ∧ (y₀ : ℚ) = y ∧
      (y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurve A B).Δ) := by
  obtain ⟨x₀, y₀, hx₀, hy₀, h⟩ := lutz_nagell_sharp A B hns htor
  refine ⟨x₀, y₀, hx₀, hy₀, h.imp_right fun h ↦ ?_⟩
  rw [Δ_of_isShortNF, shortCurve_a₄, shortCurve_a₆]
  exact h.mul_left _

end WeierstrassCurve
