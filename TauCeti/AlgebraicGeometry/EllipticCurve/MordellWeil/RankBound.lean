/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SemilocalComparison

/-!
# Finiteness of the 2-Selmer group over a number field, and the rank bound

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a number field `F`, with square classes `W.M` in its étale algebra `F[X] ⧸ (f)`. The
explicit `2`-Selmer group `W.selmerGroup₂ (𝓞 F) Loc` is cut out of `W.M` by the norm condition and
by the local `2`-descent conditions at every finite place of `F` and at each member of an
auxiliary family `Loc` of `F`-fields (classically, the completions at the infinite places).

This file proves that this group is **finite**, for every auxiliary family `Loc`, and turns that
into the **effective Mordell–Weil rank bound**
`2 ^ rank W(F) * #W(F)[2] ≤ #Sel₂(W/F)`.

The finiteness argument is short. At every finite place `v`, the local descent image over the
completion `F_v` is unramified away from the bad primes of the base-changed curve over
`𝒪_v` (`range_μ_le_selmerGroupA`, applied over `F_v`), so a Selmer class localizes to an
unramified class at every good place. By the semilocal comparison
(`mem_selmerGroupA_of_forall_localRes`) it is then `S`-unramified globally, `S` the bad primes
of `W` over `𝓞 F`. So the `2`-Selmer group lies in `A(S, 2)`, and `A(S, 2)` is finite by the
class number theorem and Dirichlet's unit theorem for the field factors of the étale algebra
(`finite_selmerGroupA`).

## Main results

* `WeierstrassCurve.Affine.selmerGroup₂_le_selmerGroupA`: over a number field, every
  `2`-Selmer class is unramified outside the bad primes, `Sel₂(W/F) ≤ A(S, 2)`.
* `WeierstrassCurve.Affine.finite_selmerGroup₂`: the `2`-Selmer group of an elliptic curve
  over a number field is finite.
* `WeierstrassCurve.Affine.pow_rank_le_card_selmerGroup₂`: the rank bound
  `2 ^ rank W(F) * #W(F)[2] ≤ #Sel₂(W/F)`.

## Provenance

The statement `finite_selmerGroup₂` follows Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, commit `66889eada51a`),
`EllipticCurves/SelmerGroup.lean`, there stated for the family of completions at the infinite
places. The source deduces it from its reduction of the `2`-Selmer group to the bad places,
whose proof needs a count of the local descent image at every good place; here only the
inclusion `Sel₂(W/F) ≤ A(S, 2)` is needed, and it follows directly from the semilocal comparison
(adapted from the same source) together with Step 6 of weak Mordell–Weil applied over each
completion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

open IsDedekindDomain Module NumberField

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [NumberField F] (W : Affine F) [W.IsElliptic] [W.IsCharNeTwoNF]
  {ι : Type*} (Loc : ι → Type*) [(i : ι) → Field (Loc i)] [(i : ι) → Algebra F (Loc i)]

open scoped Classical in
/-- **The 2-Selmer group is unramified outside the bad primes**: over a number field `F`, every
class in the `2`-Selmer group lies in `A(S, 2)`, for `S` the bad primes of `W` over `𝓞 F`. Only
the local conditions at the finite places are used, so this holds for every auxiliary family
`Loc`. -/
theorem selmerGroup₂_le_selmerGroupA : W.selmerGroup₂ (𝓞 F) Loc ≤ W.selmerGroupA (𝓞 F) :=
  fun _ hm ↦ W.mem_selmerGroupA_of_forall_localRes fun v _ ↦
    (W⁄(v.adicCompletion F)).toAffine.range_μ_le_selmerGroupA (v.adicCompletionIntegers F) <|
      (W.mem_localCondition_iff _).mp (((W.mem_selmerGroup₂_iff (𝓞 F) Loc).mp hm).2.1 v)

open scoped Classical in
/-- **The 2-Selmer group of an elliptic curve over a number field is finite**, for every
auxiliary family `Loc` of local conditions beyond the finite places. -/
theorem finite_selmerGroup₂ : Finite (W.selmerGroup₂ (𝓞 F) Loc) :=
  have := W.finite_selmerGroupA (𝓞 F)
  Finite.of_injective _ (Subgroup.inclusion_injective (W.selmerGroup₂_le_selmerGroupA Loc))

open scoped Classical in
/-- **The Mordell–Weil rank bound from the 2-Selmer group**: for an elliptic curve over a number
field `F`, `2 ^ rank W(F) * #W(F)[2] ≤ #Sel₂(W/F)`. The rank is that of the finitely generated
group `W(F)` (`fg_point_of_numberField`), and the right-hand side is finite by
`finite_selmerGroup₂`. -/
theorem pow_rank_le_card_selmerGroup₂ :
    2 ^ finrank ℤ W.Point * Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker ≤
      Nat.card (W.selmerGroup₂ (𝓞 F) Loc) :=
  have := fg_point_of_numberField (W := W)
  have := W.finite_selmerGroup₂ Loc
  W.pow_rank_le_card_of_range_μ_le (W.range_μ_le_selmerGroup₂ (𝓞 F) Loc)

end WeierstrassCurve.Affine

end
