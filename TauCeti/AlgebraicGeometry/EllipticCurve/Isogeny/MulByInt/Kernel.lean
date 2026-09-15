/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity

/-!
# The kernel of multiplication by `n` is the `n`-torsion

An isogeny in this development has no point map, so its kernel is the subgroup of points whose
translation fixes the pulled-back field (`Isogeny.ker`). For `[n]` that subgroup is the one the
classical statement names: the `n`-torsion of `W` over the base field.

`[n]` is an isogeny only where the division polynomial does not vanish, so the statement carries
`psiFunctionField W n ≠ 0` — the same hypothesis `mulByIntIsogeny` is built from, and not a
restriction beyond it. On an elliptic curve it holds for every `n ≠ 0`, by
`psiFunctionField_ne_zero_of_Δ_ne_zero`.

The bridge is the tautological point. A coordinate pullback is determined by it, that of `[n]` is
`n` times the generic point, and translating by `P` moves the generic point to `g + P`. So the
translation fixes `[n]` exactly when `n • (g + P) = n • g`, which is `n • P = 0`.

Only the base field's points appear, as everywhere in `Isogeny.ker`: this is the rational
`n`-torsion, not the geometric one, and the two differ unless the base field carries the whole
kernel.

## Main results

* `TauCeti.Isogeny.mem_ker_mulByIntIsogeny_iff`: `P ∈ ker [n] ↔ n • P = 0`, for an `n` whose
  division polynomial does not vanish, and
  `TauCeti.Isogeny.mem_ker_mulByIntIsogenyOfNeZero_iff`, the same at the `n ≠ 0` the elliptic case
  discharges it from.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.6.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **A point is in the kernel of `[n]` exactly when it is `n`-torsion**, for an `n` whose
division polynomial does not vanish — the hypothesis `mulByIntIsogeny` itself carries. -/
-- Not `@[simp]`: `Isogeny.mem_ker_iff` is, and rewrites this left-hand side first, so the
-- annotation is a simp-normal-form violation.
theorem mem_ker_mulByIntIsogeny_iff {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    {P : (W⁄F).toAffine.Point} :
    P ∈ (mulByIntIsogeny W hn).ker ↔ n • P = 0 := by
  rw [mem_ker_iff_map_tautologicalPoint_eq, mulByIntIsogeny_pullback,
    tautologicalPoint_mulByIntPullback,
    map_zsmul, map_translation_genericPoint, translatedGenericPoint_def]
  -- The scalar action here arrives through `map_zsmul` as `SubNegMonoid.toZSMul`, so the rule is
  -- `zsmul_add`; `smul_add` is stated for the `Module ℤ` action and its pattern does not match.
  have hsmul : n • (W.genericPoint + Point.baseChange (W' := W) F W.FunctionField P) =
      n • W.genericPoint + n • Point.baseChange (W' := W) F W.FunctionField P :=
    zsmul_add _ _ _
  have hzero : n • Point.baseChange (W' := W) F W.FunctionField P =
      Point.baseChange (W' := W) F W.FunctionField (n • P) := (map_zsmul _ _ _).symm
  rw [hsmul, hzero]
  constructor
  · intro h
    refine Point.map_injective (W' := W) (f := Algebra.ofId F W.FunctionField) ?_
    rw [map_zero]
    exact add_left_cancel (h.trans (add_zero _).symm)
  · intro h
    rw [h, map_zero, add_zero]

/-- **A point is in the kernel of `[n]` exactly when it is `n`-torsion**, with the non-vanishing
hypothesis discharged from `n ≠ 0` as in `mulByIntIsogenyOfNeZero`. -/
theorem mem_ker_mulByIntIsogenyOfNeZero_iff {n : ℤ} (hn : n ≠ 0)
    {P : (W⁄F).toAffine.Point} :
    P ∈ (mulByIntIsogenyOfNeZero W hn).ker ↔ n • P = 0 := by
  simpa only [mulByIntIsogenyOfNeZero] using mem_ker_mulByIntIsogeny_iff W _

end TauCeti.Isogeny

end
