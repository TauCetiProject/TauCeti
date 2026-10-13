/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.DoubleRoot
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Symbol
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.TripleRoot
import TauCeti.Algebra.Polynomial.Cubic.RepeatedRoot
import TauCeti.Algebra.Polynomial.Cubic.TripleRoot
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Discriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.LateDiscriminant

/-!
# Tate's algorithm: the stopping conditions, and termination

Tate's algorithm reads the reduction symbol of a minimal Weierstrass equation over a discrete
valuation ring `R` with uniformiser `ϖ` and perfect residue field `k`. It alternates changes of
variables over `R` with divisibility tests, and stops as soon as one test succeeds. This file
records the test at which the algorithm stops as a predicate on an integral equation,
`WeierstrassCurve.IsTateTerminal W ϖ s`, and proves that the algorithm terminates: every minimal
equation is carried by a change of variables over `R` to an equation on which one of the stopping
tests succeeds.

The stopping conditions are stated on the coefficients of `W` without dividing by `ϖ`. With the
residue cubic `P(T) = T³ + (a₂/ϖ) T² + (a₄/ϖ²) T + a₆/ϖ³` of the Step 6 normal form, they are:

* `I₀`: `ϖ ∤ Δ` (Step 1);
* `Iₙ` for `n ≥ 1`: the reduction is singular at the origin (`ϖ ∣ a₃, a₄, a₆`), `ϖ ∤ b₂`, and
  `v(Δ) = n` (Step 2);
* `II`, `III`, `IV`: the reduction is singular at the origin, `ϖ ∣ b₂`, and respectively
  `ϖ² ∤ a₆`; `ϖ² ∣ a₆` and `ϖ³ ∤ b₈`; `ϖ² ∣ a₆`, `ϖ³ ∣ b₈` and `ϖ³ ∤ b₆` (Steps 3 to 5);
* `I₀*`: the Step 6 normal form `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄`, `ϖ³ ∣ a₆`, and `P` has nonzero
  discriminant, that is `ϖ⁷ ∤ disc(T³ + a₂ T² + a₄ T + a₆)`
  (`WeierstrassCurve.pow_seven_dvd_discr_iff`);
* `Iₙ*` for `n ≥ 1`: the stopping stage `n` of the subprocedure of Step 7
  (`WeierstrassCurve.IsTateOddStage`, `WeierstrassCurve.IsTateEvenStage`);
* `IV*`, `III*`, `II*`: the normal forms and tests of Steps 8, 9 and 10.

The equation must be minimal for the algorithm to stop: on a non-minimal equation the triple-root
branch may reach Step 11, which rescales the equation and starts again. Minimality is used only
there.

The algorithmic Ogg exponent `v(Δ) − m + 1` of a symbol with `m` components
(`TauCeti.ReductionSymbol.algorithmicOggExponent`) is `0` at `I₀` and `1` at `Iₙ`, since there
`v(Δ) = n`; at every additive symbol the stopping conditions force `v(Δ) > m`, so the exponent is
at least `2`.

## Main definitions

* `WeierstrassCurve.IsTateTerminal`: Tate's algorithm, run on `W`, stops with output `s` without a
  further change of variables.

## Main results

* `WeierstrassCurve.exists_isTateTerminal`: **Tate's algorithm terminates.** Over a discrete
  valuation ring with perfect residue field, a minimal equation with nonzero discriminant is carried
  by a change of variables over `R` to an equation on which the algorithm stops.
* `WeierstrassCurve.isTateTerminal_map_iff`: the stopping conditions transfer along a ring map
  that reflects divisibility by powers of the uniformiser.
* `WeierstrassCurve.IsTateTerminal.addVal_Δ_eq`: at a symbol `Iₙ`, the discriminant has valuation
  `n`.
* `WeierstrassCurve.IsTateTerminal.pow_componentCount_add_one_dvd_Δ`: at an additive symbol with
  `m` components, `ϖ^(m+1) ∣ Δ`.
* `WeierstrassCurve.IsTateTerminal.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆` and
  `WeierstrassCurve.IsTateTerminal.dvd_c₄`: at an additive symbol, `ϖ` divides `b₂`, `a₃`, `a₄`,
  `a₆` and hence `c₄`.
* `WeierstrassCurve.IsTateTerminal.dvd_Δ_iff`: the algorithm stops at a symbol other than `I₀`
  exactly when `ϖ ∣ Δ`.
* `WeierstrassCurve.IsTateTerminal.two_le_algorithmicOggExponent`: at an additive symbol, the
  algorithmic Ogg exponent is at least `2`.

The output of the algorithm is not shown here to be independent of the choices made along the way.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing IsDiscreteValuationRing TauCeti

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ϖ : R)

/-- **The stopping conditions of Tate's algorithm.** `W.IsTateTerminal ϖ s` says that Tate's
algorithm, run on the integral equation `W` with uniformiser `ϖ`, stops with output `s` without a
further change of variables. The conditions are those listed in the module docstring; for `Iₙ*`
the stage `n = 2k + 1` or `n = 2k + 2` is the normal form `IsTateOddStage ϖ k` or
`IsTateEvenStage ϖ k` of the subprocedure of Step 7. -/
def IsTateTerminal : ReductionSymbol → Prop
  | .I 0 => ¬ ϖ ∣ W.Δ
  | .I (n + 1) => ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ∣ W.a₆ ∧ ¬ ϖ ∣ W.b₂ ∧ ϖ ^ (n + 1) ∣ W.Δ ∧
      ¬ ϖ ^ (n + 2) ∣ W.Δ
  | .II => ϖ ∣ W.b₂ ∧ ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ∣ W.a₆ ∧ ¬ ϖ ^ 2 ∣ W.a₆
  | .III => ϖ ∣ W.b₂ ∧ ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ^ 2 ∣ W.a₆ ∧ ¬ ϖ ^ 3 ∣ W.b₈
  | .IV => ϖ ∣ W.b₂ ∧ ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ^ 2 ∣ W.a₆ ∧ ϖ ^ 3 ∣ W.b₈ ∧ ¬ ϖ ^ 3 ∣ W.b₆
  | .IStar 0 => ϖ ∣ W.a₁ ∧ ϖ ∣ W.a₂ ∧ ϖ ^ 2 ∣ W.a₃ ∧ ϖ ^ 2 ∣ W.a₄ ∧ ϖ ^ 3 ∣ W.a₆ ∧
      ¬ ϖ ^ 7 ∣ (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr
  | .IStar (n + 1) =>
      (∃ k, n = 2 * k ∧ IsTateOddStage ϖ k W ∧ ¬ ϖ ^ (2 * k + 5) ∣ W.b₆) ∨
        ∃ k, n = 2 * k + 1 ∧ IsTateEvenStage ϖ k W ∧ ¬ ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆
  | .IVStar => ϖ ∣ W.a₁ ∧ ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ 2 ∣ W.a₃ ∧ ϖ ^ 3 ∣ W.a₄ ∧ ϖ ^ 4 ∣ W.a₆ ∧
      ¬ ϖ ^ 5 ∣ W.b₆
  | .IIIStar => ϖ ∣ W.a₁ ∧ ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ 3 ∣ W.a₃ ∧ ϖ ^ 3 ∣ W.a₄ ∧ ϖ ^ 5 ∣ W.a₆ ∧
      ¬ ϖ ^ 4 ∣ W.a₄
  | .IIStar => ϖ ∣ W.a₁ ∧ ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ 3 ∣ W.a₃ ∧ ϖ ^ 4 ∣ W.a₄ ∧ ϖ ^ 5 ∣ W.a₆ ∧
      ¬ ϖ ^ 6 ∣ W.a₆

variable {W ϖ}

@[simp]
theorem isTateTerminal_I_zero : W.IsTateTerminal ϖ (.I 0) ↔ ¬ ϖ ∣ W.Δ :=
  Iff.rfl

@[simp]
theorem isTateTerminal_I_add_one {n : ℕ} : W.IsTateTerminal ϖ (.I (n + 1)) ↔
    ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ∣ W.a₆ ∧ ¬ ϖ ∣ W.b₂ ∧ ϖ ^ (n + 1) ∣ W.Δ ∧ ¬ ϖ ^ (n + 2) ∣ W.Δ :=
  Iff.rfl

@[simp]
theorem isTateTerminal_II : W.IsTateTerminal ϖ .II ↔
    ϖ ∣ W.b₂ ∧ ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ∣ W.a₆ ∧ ¬ ϖ ^ 2 ∣ W.a₆ :=
  Iff.rfl

@[simp]
theorem isTateTerminal_III : W.IsTateTerminal ϖ .III ↔
    ϖ ∣ W.b₂ ∧ ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ^ 2 ∣ W.a₆ ∧ ¬ ϖ ^ 3 ∣ W.b₈ :=
  Iff.rfl

@[simp]
theorem isTateTerminal_IV : W.IsTateTerminal ϖ .IV ↔
    ϖ ∣ W.b₂ ∧ ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ^ 2 ∣ W.a₆ ∧ ϖ ^ 3 ∣ W.b₈ ∧ ¬ ϖ ^ 3 ∣ W.b₆ :=
  Iff.rfl

@[simp]
theorem isTateTerminal_IStar_zero : W.IsTateTerminal ϖ (.IStar 0) ↔
    ϖ ∣ W.a₁ ∧ ϖ ∣ W.a₂ ∧ ϖ ^ 2 ∣ W.a₃ ∧ ϖ ^ 2 ∣ W.a₄ ∧ ϖ ^ 3 ∣ W.a₆ ∧
      ¬ ϖ ^ 7 ∣ (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr :=
  Iff.rfl

@[simp]
theorem isTateTerminal_IStar_add_one {n : ℕ} : W.IsTateTerminal ϖ (.IStar (n + 1)) ↔
    (∃ k, n = 2 * k ∧ IsTateOddStage ϖ k W ∧ ¬ ϖ ^ (2 * k + 5) ∣ W.b₆) ∨
      ∃ k, n = 2 * k + 1 ∧ IsTateEvenStage ϖ k W ∧ ¬ ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆ :=
  Iff.rfl

@[simp]
theorem isTateTerminal_IVStar : W.IsTateTerminal ϖ .IVStar ↔
    ϖ ∣ W.a₁ ∧ ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ 2 ∣ W.a₃ ∧ ϖ ^ 3 ∣ W.a₄ ∧ ϖ ^ 4 ∣ W.a₆ ∧ ¬ ϖ ^ 5 ∣ W.b₆ :=
  Iff.rfl

@[simp]
theorem isTateTerminal_IIIStar : W.IsTateTerminal ϖ .IIIStar ↔
    ϖ ∣ W.a₁ ∧ ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ 3 ∣ W.a₃ ∧ ϖ ^ 3 ∣ W.a₄ ∧ ϖ ^ 5 ∣ W.a₆ ∧ ¬ ϖ ^ 4 ∣ W.a₄ :=
  Iff.rfl

@[simp]
theorem isTateTerminal_IIStar : W.IsTateTerminal ϖ .IIStar ↔
    ϖ ∣ W.a₁ ∧ ϖ ^ 2 ∣ W.a₂ ∧ ϖ ^ 3 ∣ W.a₃ ∧ ϖ ^ 4 ∣ W.a₄ ∧ ϖ ^ 5 ∣ W.a₆ ∧ ¬ ϖ ^ 6 ∣ W.a₆ :=
  Iff.rfl

/-- **The stopping conditions are read along a ring map that reflects divisibility by powers of
the uniformiser.** If `f ϖ ^ n ∣ f x ↔ ϖ ^ n ∣ x` for all `n` and `x`, then Tate's algorithm stops
on `W.map f` with uniformiser `f ϖ` exactly where it stops on `W` with uniformiser `ϖ`. For
instance the cast from `ℤ` to a discrete valuation ring with uniformiser a prime `p` reflects
divisibility by powers of `p` (`Nat.Prime.pow_dvd_intCast_iff`), so the symbol of an integral
equation over `ℤ` can be computed over `ℤ`. -/
theorem isTateTerminal_map_iff {S : Type*} [CommRing S] (f : R →+* S)
    (hf : ∀ (n : ℕ) (x : R), f ϖ ^ n ∣ f x ↔ ϖ ^ n ∣ x) {s : ReductionSymbol} :
    (W.map f).IsTateTerminal (f ϖ) s ↔ W.IsTateTerminal ϖ s := by
  have hf₁ (x : R) : f ϖ ∣ f x ↔ ϖ ∣ x := by simpa using hf 1 x
  have hd : (Cubic.mk 1 (f W.a₂) (f W.a₄) (f W.a₆)).discr =
      f (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr := by
    simp [Cubic.discr, map_ofNat]
  have hq : discrim (f W.a₂) (f W.a₄) (f W.a₆) = f (discrim W.a₂ W.a₄ W.a₆) := by
    simp [discrim, map_ofNat]
  rcases s with (_ | n) | _ | _ | _ | (_ | n) | _ | _ | _ <;>
    simp [IsTateTerminal, hd, hq, hf, hf₁]

/-- At a stopping symbol other than `Iₙ` with `m` components, `ϖ^(m+1)` divides the
discriminant. This is the bound that makes the algorithmic Ogg exponent at least `2` there. -/
theorem IsTateTerminal.pow_componentCount_add_one_dvd_Δ [IsDomain R] (hϖ : Prime ϖ)
    {s : ReductionSymbol} (h : W.IsTateTerminal ϖ s) (hs : ∀ n, s ≠ .I n) :
    ϖ ^ (s.componentCount + 1) ∣ W.Δ := by
  match s, h with
  | .I n, _ => exact absurd rfl (hs n)
  | .II, ⟨hb₂, h₃, h₄, h₆, _⟩ =>
    simpa using W.sq_dvd_Δ_of_dvd_b₂_of_dvd_a₃_of_dvd_a₄_of_dvd_a₆ ϖ hb₂ h₃ h₄ h₆
  | .III, ⟨hb₂, h₃, h₄, h₆, _⟩ =>
    simpa using W.pow_three_dvd_Δ_of_dvd_b₂_of_dvd_a₃_of_dvd_a₄_of_sq_dvd_a₆ ϖ hb₂ h₃ h₄ h₆
  | .IV, ⟨hb₂, ⟨A₃, h₃⟩, _, ⟨A₆, h₆⟩, hb₈, _⟩ =>
    have hb₆ : ϖ ^ 2 ∣ W.b₆ := ⟨A₃ ^ 2 + 4 * A₆, by rw [b₆, h₃, h₆]; ring⟩
    simpa using W.pow_four_dvd_Δ_of_dvd_b₂_of_sq_dvd_b₆_of_pow_three_dvd_b₈ ϖ hϖ hb₂ hb₆ hb₈
  | .IStar 0, ⟨h₁, h₂, h₃, h₄, h₆, _⟩ => simpa using W.pow_six_dvd_Δ_of_pow_dvd ϖ h₁ h₂ h₃ h₄ h₆
  | .IStar (n + 1), .inl ⟨k, hk, hW, _⟩ =>
    subst hk
    simpa only [ReductionSymbol.componentCount_IStar, show 2 * k + 1 + 5 + 1 = 2 * k + 7 by ring]
      using hW.pow_dvd_Δ
  | .IStar (n + 1), .inr ⟨k, hk, hW, _⟩ =>
    subst hk
    simpa only [ReductionSymbol.componentCount_IStar,
      show 2 * k + 1 + 1 + 5 + 1 = 2 * k + 8 by ring] using hW.pow_dvd_Δ
  | .IVStar, ⟨h₁, h₂, h₃, h₄, h₆, _⟩ => simpa using W.pow_eight_dvd_Δ_of_stepEight ϖ h₁ h₂ h₃ h₄ h₆
  | .IIIStar, ⟨h₁, h₂, h₃, h₄, h₆, _⟩ => simpa using W.pow_nine_dvd_Δ_of_stepNine ϖ h₁ h₂ h₃ h₄ h₆
  | .IIStar, ⟨h₁, h₂, h₃, h₄, h₆, _⟩ => simpa using W.pow_ten_dvd_Δ_of_stepTen ϖ h₁ h₂ h₃ h₄ h₆

/-- At a stopping symbol other than `Iₙ`, the equation is in the additive normal form of Step 2 of
Tate's algorithm: `ϖ` divides `b₂`, `a₃`, `a₄` and `a₆`. -/
theorem IsTateTerminal.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆ {s : ReductionSymbol}
    (h : W.IsTateTerminal ϖ s) (hs : ∀ n, s ≠ .I n) :
    ϖ ∣ W.b₂ ∧ ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ∣ W.a₆ := by
  have hb₂ (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ∣ W.a₂) : ϖ ∣ W.b₂ := by
    rw [b₂]
    exact dvd_add (dvd_pow h₁ two_ne_zero) (dvd_mul_of_dvd_right h₂ 4)
  have hp {k : ℕ} {x : R} (hk : k ≠ 0) (hx : ϖ ^ k ∣ x) : ϖ ∣ x := (dvd_pow_self ϖ hk).trans hx
  match s, h with
  | .I n, _ => exact absurd rfl (hs n)
  | .II, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, -⟩ := isTateTerminal_II.1 h
    exact ⟨hb₂, h₃, h₄, h₆⟩
  | .III, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, -⟩ := isTateTerminal_III.1 h
    exact ⟨hb₂, h₃, h₄, hp (by omega) h₆⟩
  | .IV, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IV.1 h
    exact ⟨hb₂, h₃, h₄, hp (by omega) h₆⟩
  | .IStar 0, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IStar_zero.1 h
    exact ⟨hb₂ h₁ h₂, hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
  | .IStar (_ + 1), h =>
    rcases isTateTerminal_IStar_add_one.1 h with ⟨_, -, hW, -⟩ | ⟨_, -, hW, -⟩
    · obtain ⟨h₁, h₂, -, h₃, h₄, h₆⟩ := isTateOddStage_iff.1 hW
      exact ⟨hb₂ h₁ h₂, hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
    · obtain ⟨h₁, h₂, -, h₃, h₄, h₆⟩ := isTateEvenStage_iff.1 hW
      exact ⟨hb₂ h₁ h₂, hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
  | .IVStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IVStar.1 h
    exact ⟨hb₂ h₁ (hp (by omega) h₂), hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
  | .IIIStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IIIStar.1 h
    exact ⟨hb₂ h₁ (hp (by omega) h₂), hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
  | .IIStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IIStar.1 h
    exact ⟨hb₂ h₁ (hp (by omega) h₂), hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩

/-- **At a stopping symbol other than `Iₙ`, `ϖ` divides `c₄`.** In the additive normal form `ϖ`
divides `b₂` and `b₄`, and `c₄ = b₂² − 24 b₄`. -/
theorem IsTateTerminal.dvd_c₄ {s : ReductionSymbol} (h : W.IsTateTerminal ϖ s)
    (hs : ∀ n, s ≠ .I n) : ϖ ∣ W.c₄ := by
  obtain ⟨hb₂, h₃, h₄, h₆⟩ := h.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆ hs
  have hb₄ := (W.dvd_b₄_and_dvd_b₆_and_sq_dvd_b₈_of_dvd_b₂_of_dvd_a₃_of_dvd_a₄_of_dvd_a₆
    ϖ hb₂ h₃ h₄ h₆).1
  rw [c₄]
  exact dvd_sub (dvd_pow hb₂ two_ne_zero) (dvd_mul_of_dvd_right hb₄ _)

/-- **Tate's algorithm stops at a symbol other than `I₀` exactly when `ϖ` divides the
discriminant.** -/
theorem IsTateTerminal.dvd_Δ_iff [IsDomain R] (hϖ : Prime ϖ) {s : ReductionSymbol}
    (h : W.IsTateTerminal ϖ s) : ϖ ∣ W.Δ ↔ s ≠ .I 0 := by
  refine ⟨fun hΔ hs ↦ (isTateTerminal_I_zero.1 (hs ▸ h)) hΔ, fun hs ↦ ?_⟩
  by_cases hI : ∃ n, s = .I n
  · obtain ⟨n, rfl⟩ := hI
    cases n with
    | zero => exact absurd rfl hs
    | succ n => exact (dvd_pow_self ϖ n.succ_ne_zero).trans (isTateTerminal_I_add_one.1 h).2.2.2.2.1
  · simp only [not_exists] at hI
    exact (dvd_pow_self ϖ (Nat.succ_ne_zero _)).trans (h.pow_componentCount_add_one_dvd_Δ hϖ hI)

end CommRing

section DiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  {W : WeierstrassCurve R}

/-- The `I₀*` test is the residue-cubic test. If `a₂ = ϖ A₂`, `a₄ = ϖ² A₄` and `a₆ = ϖ³ A₆`, then
`ϖ⁷` divides the discriminant of `T³ + a₂ T² + a₄ T + a₆` exactly when the residue cubic
`T³ + A₂ T² + A₄ T + A₆` over the residue field has zero discriminant. -/
theorem pow_seven_dvd_discr_iff (hϖ : Irreducible ϖ) {A₂ A₄ A₆ : R} (hA₂ : W.a₂ = ϖ * A₂)
    (hA₄ : W.a₄ = ϖ ^ 2 * A₄) (hA₆ : W.a₆ = ϖ ^ 3 * A₆) :
    ϖ ^ 7 ∣ (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr ↔
      (Cubic.mk 1 (residue R A₂) (residue R A₄) (residue R A₆)).discr = 0 := by
  -- The discriminant is homogeneous of weight `6` in `(a₂, a₄, a₆)`.
  have h : (Cubic.mk 1 (ϖ * A₂) (ϖ ^ 2 * A₄) (ϖ ^ 3 * A₆)).discr =
      ϖ ^ 6 * (Cubic.mk 1 A₂ A₄ A₆).discr := by
    simp only [Cubic.discr]
    ring
  rw [hA₂, hA₄, hA₆, h, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero 6 hϖ.ne_zero), ← Ideal.mem_span_singleton,
    ← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
  simp [Cubic.discr, map_ofNat]

/-- At the symbol `Iₙ`, the discriminant has valuation `n`. -/
theorem IsTateTerminal.addVal_Δ_eq (hϖ : Irreducible ϖ) {n : ℕ} (h : W.IsTateTerminal ϖ (.I n)) :
    addVal R W.Δ = n := by
  have key : ϖ ^ n ∣ W.Δ ∧ ¬ ϖ ^ (n + 1) ∣ W.Δ := by
    cases n with
    | zero => simpa using h
    | succ n => exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  rw [← addVal_le_iff_dvd, ← addVal_le_iff_dvd, hϖ.addVal_pow, hϖ.addVal_pow, not_le] at key
  push_cast at key
  exact le_antisymm ((ENat.lt_add_one_iff (ENat.natCast_ne_top n)).1 key.2) key.1

/-- **The algorithmic Ogg exponent at an additive symbol is at least `2`.** If Tate's algorithm
stops on `W` with a symbol other than `Iₙ`, and `n` is the valuation of the discriminant, then
`n − m + 1 ≥ 2`, where `m` is the component count of the symbol. -/
theorem IsTateTerminal.two_le_algorithmicOggExponent (hϖ : Irreducible ϖ) {s : ReductionSymbol}
    (h : W.IsTateTerminal ϖ s) (hs : ∀ n, s ≠ .I n) {n : ℕ} (hn : addVal R W.Δ = n) :
    2 ≤ s.algorithmicOggExponent n := by
  have key := addVal_le_iff_dvd.2 (h.pow_componentCount_add_one_dvd_Δ hϖ.prime hs)
  rw [hϖ.addVal_pow, hn] at key
  have : s.componentCount + 1 ≤ n := by exact_mod_cast key
  rw [ReductionSymbol.algorithmicOggExponent_eq]
  omega

/-! ### Termination -/

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable [PerfectField (ResidueField R)]

/-- The double-root branch (Step 7): if the residue cubic of the Step 6 normal form is
`(T - ρ)² (T - σ)` with `ρ ≠ σ`, the algorithm stops at a symbol `Iₙ*`. -/
private theorem exists_isTateTerminal_of_double_root (hϖ : Irreducible ϖ)
    (W : WeierstrassCurve R) (hΔ : W.Δ ≠ 0) (h₁ : ϖ ∣ W.a₁) (h₃ : ϖ ^ 2 ∣ W.a₃) {A₂ A₄ A₆ : R}
    (hA₂ : W.a₂ = ϖ * A₂) (hA₄ : W.a₄ = ϖ ^ 2 * A₄) (hA₆ : W.a₆ = ϖ ^ 3 * A₆)
    {ρ σ : ResidueField R} (hρσ : ρ ≠ σ) (hb : residue R A₂ = -(ρ + ρ + σ))
    (hc : residue R A₄ = ρ * ρ + ρ * σ + ρ * σ) (hd : residue R A₆ = -(ρ * ρ * σ)) :
    ∃ (C : VariableChange R) (s : ReductionSymbol), (C • W).IsTateTerminal ϖ s := by
  obtain ⟨r, g₁, g₂, g₂', g₃, g₄, g₆⟩ :=
    W.exists_variableChange_not_sq_dvd_a₂_and_pow_dvd_a₄_a₆ hϖ h₁ h₃ hA₂ hA₄ hA₆ ρ
      (by rw [hb, hc, hd]; ring) (by rw [hb, hc]; ring)
      (by rw [hb]; exact fun h ↦ hρσ (by linear_combination h))
  obtain ⟨r', t', k, f₁, f₂, f₂', hodd | heven⟩ :=
    exists_variableChange_not_pow_dvd_b₆_or_discrim hϖ _ (by simpa [variableChange_Δ] using hΔ)
      g₁ g₂ g₂' g₃ g₄ g₆
  · refine ⟨VariableChange.mk 1 r' 0 t' * VariableChange.mk 1 r 0 0, .IStar (2 * k + 1), ?_⟩
    rw [mul_smul, isTateTerminal_IStar_add_one]
    exact .inl ⟨k, rfl,
      isTateOddStage_iff.2 ⟨f₁, f₂, f₂', hodd.1, hodd.2.1, hodd.2.2.1⟩, hodd.2.2.2.1⟩
  · refine ⟨VariableChange.mk 1 r' 0 t' * VariableChange.mk 1 r 0 0, .IStar (2 * k + 2), ?_⟩
    rw [mul_smul, isTateTerminal_IStar_add_one]
    exact .inr ⟨k, rfl,
      isTateEvenStage_iff.2 ⟨f₁, f₂, f₂', heven.1, heven.2.1, heven.2.2.1⟩, heven.2.2.2.1⟩

/-- The triple-root branch (Steps 8 to 10): if the residue cubic of the Step 6 normal form is a
cube, the algorithm stops at `IV*`, `III*` or `II*`. Minimality rules out Step 11. -/
private theorem exists_isTateTerminal_of_triple_root (hϖ : Irreducible ϖ)
    (W : WeierstrassCurve R) (hΔ : W.Δ ≠ 0) [IsMinimal R (W.baseChange K)] (h₁ : ϖ ∣ W.a₁)
    (h₃ : ϖ ^ 2 ∣ W.a₃) {A₂ A₄ A₆ : R} (hA₂ : W.a₂ = ϖ * A₂) (hA₄ : W.a₄ = ϖ ^ 2 * A₄)
    (hA₆ : W.a₆ = ϖ ^ 3 * A₆) (hb : residue R A₂ ^ 2 = 3 * residue R A₄)
    (hc : residue R A₄ ^ 2 = 3 * residue R A₂ * residue R A₆)
    (hd : residue R A₂ * residue R A₄ = 9 * residue R A₆) :
    ∃ (C : VariableChange R) (s : ReductionSymbol), (C • W).IsTateTerminal ϖ s := by
  have key (x : R) : residue R x = 0 ↔ ϖ ∣ x := by
    rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  obtain ⟨x, hx⟩ := (key (A₂ ^ 2 - 3 * A₄)).1 (by simp [hb, map_ofNat])
  obtain ⟨y, hy⟩ := (key (A₄ ^ 2 - 3 * A₂ * A₆)).1 (by simp [hc, map_ofNat])
  obtain ⟨z, hz⟩ := (key (A₂ * A₄ - 9 * A₆)).1 (by simp [hd, map_ofNat])
  obtain ⟨r, t, g₁, g₂, g₃, g₄, g₆, hstop⟩ :=
    W.exists_variableChange_not_pow_dvd_b₆_or_a₄_or_a₆ (K := K) hϖ hΔ h₁ h₃ ⟨A₄, hA₄⟩ ⟨A₆, hA₆⟩
      ⟨x, by rw [hA₂, hA₄]; linear_combination ϖ ^ 2 * hx⟩
      ⟨y, by rw [hA₂, hA₄, hA₆]; linear_combination ϖ ^ 4 * hy⟩
      ⟨z, by rw [hA₂, hA₄, hA₆]; linear_combination ϖ ^ 3 * hz⟩
  rcases hstop with hb₆ | ⟨k₃, k₆, hstop⟩
  · exact ⟨_, .IVStar, g₁, g₂, g₃, g₄, g₆, hb₆⟩
  by_cases k₄ : ϖ ^ 4 ∣ (VariableChange.mk 1 r 0 t • W).a₄
  · exact ⟨_, .IIStar, g₁, g₂, k₃, k₄, k₆, hstop.resolve_left (not_not_intro k₄)⟩
  · exact ⟨_, .IIIStar, g₁, g₂, k₃, g₄, k₆, k₄⟩

/-- From the Step 6 normal form `ϖ ∣ a₁, a₂`, `ϖ² ∣ a₃, a₄`, `ϖ³ ∣ a₆`, the algorithm stops at
`I₀*` when the residue cubic has nonzero discriminant, and otherwise in the double- or triple-root
branch. -/
private theorem exists_isTateTerminal_of_stepSix (hϖ : Irreducible ϖ) (W : WeierstrassCurve R)
    (hΔ : W.Δ ≠ 0) [IsMinimal R (W.baseChange K)] (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ∣ W.a₂)
    (h₃ : ϖ ^ 2 ∣ W.a₃) (h₄ : ϖ ^ 2 ∣ W.a₄) (h₆ : ϖ ^ 3 ∣ W.a₆) :
    ∃ (C : VariableChange R) (s : ReductionSymbol), (C • W).IsTateTerminal ϖ s := by
  obtain ⟨A₂, hA₂⟩ := h₂
  obtain ⟨A₄, hA₄⟩ := h₄
  obtain ⟨A₆, hA₆⟩ := h₆
  rcases TauCeti.Polynomial.cubic_root_trichotomy (b := residue R A₂) (c := residue R A₄)
    (d := residue R A₆) with hD | ⟨ρ, σ, hρσ, hP⟩ | hP
  · refine ⟨1, .IStar 0, ?_⟩
    rw [one_smul]
    exact ⟨h₁, ⟨A₂, hA₂⟩, h₃, ⟨A₄, hA₄⟩, ⟨A₆, hA₆⟩,
      (pow_seven_dvd_discr_iff hϖ hA₂ hA₄ hA₆).not.2 hD⟩
  · obtain ⟨hb, hc, hd⟩ := TauCeti.Polynomial.cubic_eq_X_sub_C_sq_mul_X_sub_C_iff.1 hP
    exact exists_isTateTerminal_of_double_root hϖ W hΔ h₁ h₃ hA₂ hA₄ hA₆ hρσ hb hc hd
  · obtain ⟨hb, hc, hd⟩ := TauCeti.Polynomial.exists_cubic_eq_X_sub_C_pow_three_iff.1 hP
    exact exists_isTateTerminal_of_triple_root (K := K) hϖ W hΔ h₁ h₃ hA₂ hA₄ hA₆ hb hc hd

/-- From the additive Step 2 normal form `ϖ ∣ b₂` and `ϖ ∣ a₃, a₄, a₆`, the algorithm stops at
`II`, `III` or `IV` (Steps 3 to 5), or reaches the Step 6 normal form. -/
private theorem exists_isTateTerminal_of_dvd_b₂ (hϖ : Irreducible ϖ) (W : WeierstrassCurve R)
    (hΔ : W.Δ ≠ 0) [IsMinimal R (W.baseChange K)] (hb₂ : ϖ ∣ W.b₂) (h₃ : ϖ ∣ W.a₃)
    (h₄ : ϖ ∣ W.a₄) (h₆ : ϖ ∣ W.a₆) :
    ∃ (C : VariableChange R) (s : ReductionSymbol), (C • W).IsTateTerminal ϖ s := by
  by_cases h₆' : ϖ ^ 2 ∣ W.a₆
  swap
  · exact ⟨1, .II, by rw [one_smul]; exact ⟨hb₂, h₃, h₄, h₆, h₆'⟩⟩
  by_cases hb₈ : ϖ ^ 3 ∣ W.b₈
  swap
  · exact ⟨1, .III, by rw [one_smul]; exact ⟨hb₂, h₃, h₄, h₆', hb₈⟩⟩
  by_cases hb₆ : ϖ ^ 3 ∣ W.b₆
  swap
  · exact ⟨1, .IV, by rw [one_smul]; exact ⟨hb₂, h₃, h₄, h₆', hb₈, hb₆⟩⟩
  obtain ⟨s', t', g₁, g₂, g₃, g₄, g₆⟩ :=
    W.exists_variableChange_dvd_a₁_a₂_a₃_a₄_a₆ hϖ hb₂ h₆' hb₆ hb₈
  have : IsMinimal R ((VariableChange.mk 1 0 s' t' • W).baseChange K) := by
    rw [baseChange, ← map_variableChange]
    exact isMinimal_baseChange_smul R (W.baseChange K) _
  obtain ⟨C, s, h⟩ := exists_isTateTerminal_of_stepSix (K := K) hϖ _
    (by simpa [variableChange_Δ] using hΔ) g₁ g₂ g₃ g₄ g₆
  exact ⟨C * VariableChange.mk 1 0 s' t', s, by rwa [mul_smul]⟩

/-- **Tate's algorithm terminates.** Over a discrete valuation ring with uniformiser `ϖ` and
perfect residue field, a Weierstrass equation over `R` with nonzero discriminant that is minimal
over the fraction field `K` is carried by a change of variables over `R` to an equation on which
one of the stopping tests of Tate's algorithm succeeds. -/
theorem exists_isTateTerminal (hϖ : Irreducible ϖ) (W : WeierstrassCurve R) (hΔ : W.Δ ≠ 0)
    [IsMinimal R (W.baseChange K)] :
    ∃ (C : VariableChange R) (s : ReductionSymbol), (C • W).IsTateTerminal ϖ s := by
  have key (x : R) : x ∈ IsLocalRing.maximalIdeal R ↔ ϖ ∣ x := by
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  -- Step 1: good reduction.
  by_cases h₀ : ϖ ∣ W.Δ
  swap
  · exact ⟨1, .I 0, by rwa [one_smul, isTateTerminal_I_zero]⟩
  -- Step 2: move the singular point of the reduction to the origin.
  obtain ⟨r, t, hrt⟩ := W.exists_map_residue_variableChange_isSingular_zero ((key _).2 h₀)
  set V := VariableChange.mk 1 r 0 t • W with hV
  obtain ⟨h₆, h₄, h₃⟩ := map_residue_isSingular_zero_iff V |>.1 hrt
  rw [key] at h₃ h₄ h₆
  have hVΔ : V.Δ = W.Δ := by simp [hV, variableChange_Δ]
  by_cases hb₂ : ϖ ∣ V.b₂
  · -- Additive reduction: Steps 3 to 10.
    have : IsMinimal R (V.baseChange K) := by
      rw [hV, baseChange, ← map_variableChange]
      exact isMinimal_baseChange_smul R (W.baseChange K) _
    obtain ⟨C, s, h⟩ := exists_isTateTerminal_of_dvd_b₂ (K := K) hϖ V (hVΔ ▸ hΔ) hb₂ h₃ h₄ h₆
    exact ⟨C * VariableChange.mk 1 r 0 t, s, by rwa [mul_smul]⟩
  · -- Multiplicative reduction: the symbol is `Iₙ` with `n = v(Δ) ≥ 1`.
    obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hΔ hϖ
    cases n with
    | zero =>
      rw [pow_zero, mul_one] at hu
      exact absurd (isUnit_of_dvd_unit (hu ▸ h₀) u.isUnit) hϖ.not_isUnit
    | succ n =>
      refine ⟨VariableChange.mk 1 r 0 t, .I (n + 1), ?_⟩
      rw [isTateTerminal_I_add_one, hVΔ, hu]
      refine ⟨h₃, h₄, h₆, hb₂, Dvd.intro_left _ rfl, fun h ↦ hϖ.not_isUnit ?_⟩
      rw [pow_succ, mul_comm, mul_dvd_mul_iff_right (pow_ne_zero _ hϖ.ne_zero)] at h
      exact isUnit_of_dvd_unit h u.isUnit

end DiscreteValuationRing

end WeierstrassCurve

end
