/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.PrimeKernel
-- Proof-only: `#ker [n] = n ²`, which the dimension is read off from.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# The `ℓ`-torsion is a two-dimensional `ZMod ℓ`-vector space

For a prime `ℓ` invertible in the base field, `ker [ℓ]` is free of rank two over `ZMod ℓ` as soon
as the geometric `ℓ`-torsion is rational. Every point of the kernel is killed by `ℓ`, which makes
it a `ZMod ℓ`-module, and `ZMod ℓ` is a field, so the kernel is a vector space whose cardinality
`ℓ ²` reads off its dimension.

Beyond `ℓ` being invertible, rationality is the only thing the base field is asked for, so the
statements take the two together, and a closure assumption enters only where the rationality is
discharged.

Rank two is what lets an endomorphism act on the torsion as a `2 × 2` matrix over `ZMod ℓ`, which
is the form the degree and the trace are read off in.

## Main results

* `TauCeti.Isogeny.finrank_ker_mulByPrimeIsogeny_of_torsion_rational`: it has dimension two.
* `TauCeti.Isogeny.nonempty_linearEquiv_ker_mulByPrimeIsogeny_of_torsion_rational`: hence
  `E[ℓ] ≅ (ZMod ℓ) ²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
  {l : ℕ} [hl : Fact l.Prime]

/-- The dimension read off a kernel of `ℓ ²` points: `ZMod ℓ` is a field of `ℓ` elements, so a
vector space over it with `ℓ ²` points has dimension two. -/
private theorem finrank_ker_of_card_eq
    (hcard : Nat.card (mulByPrimeIsogeny W l).ker = l ^ 2) :
    Module.finrank (ZMod l) (mulByPrimeIsogeny W l).ker = 2 := by
  have : Module.Finite (ZMod l) (mulByPrimeIsogeny W l).ker := Module.Finite.of_finite
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod l) (V := (mulByPrimeIsogeny W l).ker)
  rw [hcard, Nat.card_zmod] at hpow
  exact (Nat.pow_right_injective hl.out.two_le hpow).symm

/-- A two-dimensional `ZMod ℓ`-space is `(ZMod ℓ) ²`. -/
private theorem nonempty_linearEquiv_of_finrank_eq
    (h : Module.finrank (ZMod l) (mulByPrimeIsogeny W l).ker = 2) :
    Nonempty ((mulByPrimeIsogeny W l).ker ≃ₗ[ZMod l] (Fin 2 → ZMod l)) := by
  have : Module.Finite (ZMod l) (mulByPrimeIsogeny W l).ker := Module.Finite.of_finite
  exact FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simpa using h)

open scoped Classical in
/-- **`E[ℓ]` is two-dimensional over `ZMod ℓ`** for `ℓ` invertible in the base field whenever the
geometric `ℓ`-torsion is rational. -/
theorem finrank_ker_mulByPrimeIsogeny_of_torsion_rational
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point,
      (l : ℤ) • P = 0 →
        P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hchar : (l : F) ≠ 0) :
    Module.finrank (ZMod l) (mulByPrimeIsogeny W l).ker = 2 :=
  finrank_ker_of_card_eq W (card_ker_mulByPrimeIsogeny_of_torsion_rational W hrat hchar)

open scoped Classical in
/-- **`E[ℓ] ≅ (ZMod ℓ)²`** for `ℓ` invertible in the base field whenever the geometric `ℓ`-torsion
is rational: the `ℓ`-torsion is free of rank two. -/
theorem nonempty_linearEquiv_ker_mulByPrimeIsogeny_of_torsion_rational
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point,
      (l : ℤ) • P = 0 →
        P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hchar : (l : F) ≠ 0) :
    Nonempty ((mulByPrimeIsogeny W l).ker ≃ₗ[ZMod l] (Fin 2 → ZMod l)) :=
  nonempty_linearEquiv_of_finrank_eq W
    (finrank_ker_mulByPrimeIsogeny_of_torsion_rational W hrat hchar)

end TauCeti.Isogeny

end
