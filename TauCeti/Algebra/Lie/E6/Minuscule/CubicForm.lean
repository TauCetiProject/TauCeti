/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight

/-!
# The invariant cubic form on the type-E6 minuscule module

The `27`-dimensional minuscule module `V(ϖ₁)` of type `E₆` carries an invariant cubic form,
classically the cubic norm of the exceptional Jordan algebra. This file records an integral
normalization of its symmetric trilinear coefficients `cubicForm a b c` in the minuscule weight
basis indexed by `TauCeti.DynkinType.e6MinusculeWeight`, on which the raising and lowering matrices
`TauCeti.E6Minuscule.raisingMatrix` and `TauCeti.E6Minuscule.loweringMatrix` act by moving a basis
vector along a simple reflection `TauCeti.DynkinType.e6MinusculeReflection`.

A coefficient is nonzero exactly when the three weights sum to zero. There are `45` such unordered
triples of basis indices, the triads of the `27` weights, and every nonzero coefficient is `1` or
`-1`. Each index lies in five triads, and two distinct indices lie in at most one, so the
coefficients are stored as a signed lookup table: the entry at `(a, b)` is `±(c + 1)` for the
third index `c` of the triad through `a` and `b`, and `0` when there is none. The signs are chosen
so that every positive and negative Chevalley generator acts as a derivation of the form; this
invariance is checked on the integral coefficients by kernel computation.

The form is the input for an `E₆`-invariant product on the doubled module `V(ϖ₁) ⊕ V(ϖ₆)`,
which pins the diagonal points of the doubled carrier to its weight torus.

## Main declarations

* `TauCeti.E6Minuscule.cubicForm`: the symmetric trilinear coefficients of the invariant cubic
  form.
* `TauCeti.E6Minuscule.cubicForm_swap_left` and `TauCeti.E6Minuscule.cubicForm_swap_right`: the
  coefficients are symmetric.
* `TauCeti.E6Minuscule.cubicForm_ne_zero_iff`: a coefficient is nonzero exactly when the three
  weights sum to zero.
* `TauCeti.E6Minuscule.cubicForm_eq_neg_one_or_eq_zero_or_eq_one`: every coefficient is `-1`, `0`
  or `1`.
* `TauCeti.E6Minuscule.cubicForm_raising_invariant` and
  `TauCeti.E6Minuscule.cubicForm_lowering_invariant`: every positive and negative Chevalley
  generator is a derivation of the form.

## References

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Chapters 5 and 7.
* M. Aschbacher, *The 27-dimensional module for E6. I*, Invent. Math. **89** (1987), 159--195.
* The signed lookup table follows `TauCeti.D4Tripled.trialityCoefficient`.
-/

public section

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType

/-- **The symmetric trilinear coefficients of the invariant cubic form on `V(ϖ₁)`**, in the
minuscule weight basis. The entry of the signed lookup table at `(a, b)` is `±(c + 1)` for the
unique index `c` whose weight is minus the sum of the weights of `a` and `b`, when such a triad
exists, and `0` otherwise; its sign is the coefficient. -/
@[expose] def cubicForm (a b c : Fin 27) : ℤ :=
  -- The table is a list of lists rather than a `![...]` vector because the kernel certificates
  -- below look up list entries faster.
  let table : List (List ℤ) := [
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0,
        0, -26, 0, 25, 0, -24, 0, 23, 22, -20, 18, -16, 13],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -27, 0, 0, 26,
        0, 0, -25, 0, 24, 0, -23, 0, -21, 19, -17, 14, -11],
      [0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, -26, 0, 0,
        25, 0, 0, 0, -22, 21, 20, -19, 0, 0, 15, -12, 9],
      [0, 0, 0, 0, 0, 0, -27, 0, 0, 26, 0, 0, 0, 0,
        -24, 0, 22, -21, 0, 0, -18, 17, 0, -15, 0, 10, -7],
      [0, 0, 0, 0, 0, 27, 0, -26, 0, 0, 0, 0, 0, 0,
        23, 0, -20, 19, 18, -17, 0, 0, 15, 0, 0, -8, 6],
      [0, 0, 0, 0, 27, 0, 0, 0, 0, -25, 0, 24, 0, -22,
        0, 21, 0, 0, 0, 0, 16, -14, 0, 12, -10, 0, 5],
      [0, 0, 0, -27, 0, 0, 0, 25, 0, 0, 0, -23, 0, 20,
        0, -19, 0, 0, -16, 14, 0, 0, -12, 0, 8, 0, -4],
      [0, 0, 0, 0, -26, 0, 25, 0, -24, 0, 22, 0, -21, 0,
        0, 0, 0, 0, 0, 0, -13, 11, 0, -9, 7, -5, 0],
      [0, 0, 27, 0, 0, 0, 0, -24, 0, 23, 0, 0, 0, -18,
        0, 17, 16, -14, 0, 0, 0, 0, 10, -8, 0, 0, 3],
      [0, 0, 0, 26, 0, -25, 0, 0, 23, 0, -20, 0, 19, 0,
        0, 0, 0, 0, 13, -11, 0, 0, 9, 0, -6, 4, 0],
      [0, -27, 0, 0, 0, 0, 0, 22, 0, -20, 0, 18, 0, 0,
        -16, -15, 0, 12, 0, -10, 0, 8, 0, 0, 0, 0, -2],
      [0, 0, -26, 0, 0, 24, -23, 0, 0, 0, 18, 0, -17, 0,
        0, 0, -13, 11, 0, 0, 0, 0, -7, 6, 0, -3, 0],
      [27, 0, 0, 0, 0, 0, 0, -21, 0, 19, 0, -17, 0, 15,
        14, 0, -12, 0, 10, 0, -8, 0, 0, 0, 0, 0, 1],
      [0, 26, 0, 0, 0, -22, 20, 0, -18, 0, 0, 0, 15, 0,
        13, 0, 0, -9, 0, 7, 0, -6, 0, 0, 0, 2, 0],
      [0, 0, 25, -24, 23, 0, 0, 0, 0, 0, -16, 0, 14, 13,
        0, -11, 0, 0, 0, 0, 0, 0, 5, -4, 3, 0, 0],
      [-26, 0, 0, 0, 0, 21, -19, 0, 17, 0, -15, 0, 0, 0,
        -11, 0, 9, 0, -7, 0, 6, 0, 0, 0, 0, -1, 0],
      [0, -25, 0, 22, -20, 0, 0, 0, 16, 0, 0, -13, -12, 0,
        0, 9, 0, 0, 0, -5, 0, 4, 0, 0, -2, 0, 0],
      [25, 0, 0, -21, 19, 0, 0, 0, -14, 0, 12, 11, 0, -9,
        0, 0, 0, 0, 5, 0, -4, 0, 0, 0, 1, 0, 0],
      [0, 24, -22, 0, 18, 0, -16, 0, 0, 13, 0, 0, 10, 0,
        0, -7, 0, 5, 0, 0, 0, -3, 0, 2, 0, 0, 0],
      [-24, 0, 21, 0, -17, 0, 14, 0, 0, -11, -10, 0, 0, 7,
        0, 0, -5, 0, 0, 0, 3, 0, 0, -1, 0, 0, 0],
      [0, -23, 20, -18, 0, 16, 0, -13, 0, 0, 0, 0, -8, 0,
        0, 6, 0, -4, 0, 3, 0, 0, -2, 0, 0, 0, 0],
      [23, 0, -19, 17, 0, -14, 0, 11, 0, 0, 8, 0, 0, -6,
        0, 0, 4, 0, -3, 0, 0, 0, 1, 0, 0, 0, 0],
      [22, -21, 0, 0, 15, 0, -12, 0, 10, 9, 0, -7, 0, 0,
        5, 0, 0, 0, 0, 0, -2, 1, 0, 0, 0, 0, 0],
      [-20, 19, 0, -15, 0, 12, 0, -9, -8, 0, 0, 6, 0, 0,
        -4, 0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0],
      [18, -17, 15, 0, 0, -10, 8, 7, 0, -6, 0, 0, 0, 0,
        3, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [-16, 14, -12, 10, -8, 0, 0, -5, 0, 4, 0, -3, 0, 2,
        0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [13, -11, 9, -7, 6, 5, -4, 0, 3, 0, -2, 0, 1, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  let q := (table.getD a []).getD b 0
  if q.natAbs = c.val + 1 then q.sign else 0

/-!
## Kernel certificates

The identities below are checked by `decide +kernel`. Each certificate is split so that one
kernel check enumerates at most `27 ^ 3` cases: the symmetry and support certificates fix the first
index, and the derivation certificates fix the node and the sign of the root move, with one
declaration per node to stay within the default heartbeat budget. A single check over all cases
keeps the intermediate terms of the whole enumeration in the kernel's caches at once, which nearly
tripled the peak memory of building this file.
-/

/-- The cubic form coefficients are symmetric in their first two arguments. -/
theorem cubicForm_swap_left (a b c : Fin 27) : cubicForm a b c = cubicForm b a c := by
  revert b c
  fin_cases a <;> decide +kernel

/-- The cubic form coefficients are symmetric in their last two arguments. -/
theorem cubicForm_swap_right (a b c : Fin 27) : cubicForm a b c = cubicForm a c b := by
  revert b c
  fin_cases a <;> decide +kernel

/-- **A cubic form coefficient is nonzero exactly when the three minuscule weights sum to zero.**
-/
theorem cubicForm_ne_zero_iff (a b c : Fin 27) :
    cubicForm a b c ≠ 0 ↔
      e6MinusculeWeight a + e6MinusculeWeight b + e6MinusculeWeight c = 0 := by
  revert b c
  fin_cases a <;> decide +kernel

/-- Every cubic form coefficient is `-1`, `0` or `1`. -/
theorem cubicForm_eq_neg_one_or_eq_zero_or_eq_one (a b c : Fin 27) :
    cubicForm a b c = -1 ∨ cubicForm a b c = 0 ∨ cubicForm a b c = 1 := by
  revert b c
  fin_cases a <;> decide +kernel

/-- The move of the minuscule weight basis along the `i`-th simple root, raising when `ε = -1` and
lowering when `ε = 1`, is a derivation of the cubic form. -/
private def IsDerivationAt (i : Fin 6) (ε : ℤ) : Prop :=
  ∀ a b c : Fin 27,
    ((if e6MinusculeWeight a i = ε then cubicForm (e6MinusculeReflection i a) b c else 0) +
      (if e6MinusculeWeight b i = ε then cubicForm a (e6MinusculeReflection i b) c else 0) +
        if e6MinusculeWeight c i = ε then cubicForm a b (e6MinusculeReflection i c) else 0) =
      0

private instance (i : Fin 6) (ε : ℤ) : Decidable (IsDerivationAt i ε) := by
  unfold IsDerivationAt
  infer_instance

private theorem isDerivationAt_zero {ε : ℤ} (hε : ε = -1 ∨ ε = 1) :
    IsDerivationAt 0 ε := by
  rcases hε with rfl | rfl <;> decide +kernel

private theorem isDerivationAt_one {ε : ℤ} (hε : ε = -1 ∨ ε = 1) :
    IsDerivationAt 1 ε := by
  rcases hε with rfl | rfl <;> decide +kernel

private theorem isDerivationAt_two {ε : ℤ} (hε : ε = -1 ∨ ε = 1) :
    IsDerivationAt 2 ε := by
  rcases hε with rfl | rfl <;> decide +kernel

private theorem isDerivationAt_three {ε : ℤ} (hε : ε = -1 ∨ ε = 1) :
    IsDerivationAt 3 ε := by
  rcases hε with rfl | rfl <;> decide +kernel

private theorem isDerivationAt_four {ε : ℤ} (hε : ε = -1 ∨ ε = 1) :
    IsDerivationAt 4 ε := by
  rcases hε with rfl | rfl <;> decide +kernel

private theorem isDerivationAt_five {ε : ℤ} (hε : ε = -1 ∨ ε = 1) :
    IsDerivationAt 5 ε := by
  rcases hε with rfl | rfl <;> decide +kernel

/-- Every simple root move of either sign is a derivation of the cubic form. -/
private theorem isDerivationAt (i : Fin 6) {ε : ℤ} (hε : ε = -1 ∨ ε = 1) :
    IsDerivationAt i ε := by
  fin_cases i
  exacts [isDerivationAt_zero hε, isDerivationAt_one hε, isDerivationAt_two hε,
    isDerivationAt_three hε, isDerivationAt_four hε, isDerivationAt_five hε]

/-- **Every positive Chevalley generator is a derivation of the cubic form**:
`c(X a, b, c) + c(a, X b, c) + c(a, b, X c) = 0` for the `i`-th raising matrix `X`, which sends the
basis vector at `a` to the one at `e6MinusculeReflection i a` when the weight of `a` pairs to `-1`
with the `i`-th simple coroot, and to zero otherwise. -/
theorem cubicForm_raising_invariant : ∀ (i : Fin 6) (a b c : Fin 27),
    ((if e6MinusculeWeight a i = -1 then cubicForm (e6MinusculeReflection i a) b c else 0) +
      (if e6MinusculeWeight b i = -1 then cubicForm a (e6MinusculeReflection i b) c else 0) +
        if e6MinusculeWeight c i = -1 then cubicForm a b (e6MinusculeReflection i c) else 0) =
      0 :=
  fun i => isDerivationAt i (.inl rfl)

/-- **Every negative Chevalley generator is a derivation of the cubic form**:
`c(Y a, b, c) + c(a, Y b, c) + c(a, b, Y c) = 0` for the `i`-th lowering matrix `Y`, which sends the
basis vector at `a` to the one at `e6MinusculeReflection i a` when the weight of `a` pairs to `1`
with the `i`-th simple coroot, and to zero otherwise. -/
theorem cubicForm_lowering_invariant : ∀ (i : Fin 6) (a b c : Fin 27),
    ((if e6MinusculeWeight a i = 1 then cubicForm (e6MinusculeReflection i a) b c else 0) +
      (if e6MinusculeWeight b i = 1 then cubicForm a (e6MinusculeReflection i b) c else 0) +
        if e6MinusculeWeight c i = 1 then cubicForm a b (e6MinusculeReflection i c) else 0) =
      0 :=
  fun i => isDerivationAt i (.inr rfl)

end TauCeti.E6Minuscule
