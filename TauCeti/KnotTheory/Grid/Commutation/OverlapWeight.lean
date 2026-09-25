/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Pentagon
public import TauCeti.KnotTheory.Grid.Commutation.Move

/-!
# Pentagon weight correction for the overlap recut

Analysis of the relationship between `pentagonWeight` and the underlying rectangle's
`OMonomial`, and the correction needed for recut weight preservation.

## The mathematical situation

For a pentagon `P : GridPentagonBetween C.column C.turnRow x y`:

- `pentagonWeight R C P = ∏ c ∈ pentagonOColumns C P, X (swap a b c)`
  where `pentagonOColumns C P = OColumnsOfSquares P.coveredSquares` (pentagon shape).

- `OMonomial R P.toGridRectangle = ∏ c ∈ OColumns P.toGridRectangle, X c`
  where `OColumns r = OColumnsOfSquares r.coveredSquares` (underlying rectangle).

- `rename (swap a b) (OMonomial R P.toGridRectangle)`
  `= ∏ p ∈ P.toGridRectangle.coveredSquares, if p ∈ OSet then X (swap a b p.1) else 1`
  by `OMonomial_eq_prod_coveredSquares` and `map_prod`.

- `pentagonWeight R C P`
  `= ∏ p ∈ P.coveredSquares, if p ∈ OSet then X (swap a b p.1) else 1`
  by `pentagonWeight_eq_prod_coveredSquares`.

The two products differ only in their index sets:
- `P.toGridRectangle.coveredSquares = cIco P.left P.right ×ˢ cIco P.bottom P.top`
  with `P.right = finRotate n a`.
- `P.coveredSquares`
  `= ((cIco P.left (finRotate n a)).erase a ×ˢ cIco P.bottom P.top) ∪`
  `(({a} ×ˢ cIoo s P.top) ∪ ({finRotate n a} ×ˢ cIco P.bottom s))`
  with `s = C.turnRow`.

## The correction factor

Write `a = C.column`, `b = finRotate n a`, `s = C.turnRow`.

Rectangle squares: all `(c, r)` with `c ∈ cIco P.left b`, `r ∈ cIco P.bottom P.top`.
Pentagon squares:
  (i)   `(c, r)` with `c ∈ (cIco P.left b).erase a`, `r ∈ cIco P.bottom P.top`;
  (ii)  `(a, r)` with `r ∈ cIoo s P.top`;
  (iii) `(b, r)` with `r ∈ cIco P.bottom s`.

Compared to the rectangle:
- **Removed**: `(a, r)` for `r ∈ cIco P.bottom P.top ∖ cIoo s P.top = cIco P.bottom s`
  (using `s ∈ cIco P.bottom P.top`, which holds for the turn row).
- **Added**: `(b, r)` for `r ∈ cIco P.bottom s`.

Since `swap a b` exchanges `a` and `b`:
- `X (swap a b b) = X a`
- `X (swap a b a) = X b`

Therefore, with `O(c) = (c, G.O c)`:
```
pentagonWeight R C P
  = rename (swap a b) (OMonomial R P.toGridRectangle)
    * (∏ r ∈ cIco P.bottom s, if O(b) = (b, r) then X a else 1)
    / (∏ r ∈ cIco P.bottom s, if O(a) = (a, r) then X b else 1)
```
i.e. the correction is the ratio of the "added strip" contribution to the "removed strip"
contribution. Each product has at most one nontrivial factor (the `O`-marking of the
respective column, if it lies in the strip).

## The added strip is empty for counted pentagons

Claim: for `P ∈ G.pentagons C x y`, the added strip contains no `O`-marking, so its
contribution is `1`.

Proof sketch: The added strip is `{b} ×ˢ cIco P.bottom s`. The only `O`-marking with
first coordinate `b` is `O(b) = (b, G.O b)`. By `C.O_next_above`:
```
G.O b ∈ insert C.oppositeTurnRow (cIco s C.oppositeTurnRow)
```
- If `G.O b ∈ cIco s C.oppositeTurnRow`: this interval is disjoint from
  `cIco P.bottom s` (they meet only at `s`, excluded from the left interval's right end
  and the right interval's left end... more precisely `Disjoint (cIco P.bottom s)
  (cIco s C.oppositeTurnRow)` by `disjoint_cIco_swap`-type lemmas, provided the cyclic
  order is right). Hence `G.O b ∉ cIco P.bottom s`.
- If `G.O b = C.oppositeTurnRow`: need `C.oppositeTurnRow ∉ cIco P.bottom s`.
  This is a geometric fact about the pentagon's row span relative to the opposite turn.
  For a counted pentagon, `P.bottom` and `P.top` are determined by the states `x, y`;
  the opposite turn row is the "other" intersection of the two vertical curves, which
  lies outside the pentagon's row span in the relevant configurations. This needs a
  dedicated lemma.

## The removed strip

The removed strip is `{a} ×ˢ cIco P.bottom s` with contribution `X b` if
`G.O a ∈ cIco P.bottom s`, else `1`.

By `C.O_column_below`: `G.O a ∈ insert s (cIco C.oppositeTurnRow s)`.
- If `G.O a = s`: then `G.O a ∉ cIco P.bottom s` (right endpoint excluded). Contribution `1`.
- If `G.O a ∈ cIco C.oppositeTurnRow s`: need to compare with `cIco P.bottom s`.
  This depends on where `P.bottom` sits relative to `C.oppositeTurnRow`.

## Cancellation across the recut

For the weight identity
`rectanglePentagonWeight D = pentagonRectangleWeight (recutLeftEqLeft D)`,
using the correction form and `OMonomial_mul_OMonomial_recutLeftEqLeft`, the remaining
obligation is:
```
correction(D.pentagon) = correction(E.pentagon)
```
where `E = D.recutLeftEqLeft ...`.

The new pentagon `E.pentagon` is `GridPentagonBetween.ofRightEq E.first ...`, so
`E.pentagon.toGridRectangle = E.first` (the first recut rectangle). Its `bottom`/`top`
are those of `E.first`, which differ from `D.pentagon`'s in general.

**However**: if both corrections are `1` (both strips empty of `O`-markings for both
the old and new pentagons), the identity holds trivially. The analysis above suggests:

1. The added strip is empty for the old pentagon (needs the opposite-turn-row lemma).
2. The added strip is empty for the new pentagon (same argument, applied to `E.pentagon`;
   needs `E.pentagon` to satisfy the same geometric hypotheses — i.e., the turn-row
   transport that is currently taken as hypothesis `hturn` in `OverlapRight.lean`).
3. The removed strip contribution: if `G.O a = s` (the common case for the distinguished
   turn), both corrections are `1` regardless of `P.bottom`.

**The cleanest path**: prove that for counted pentagons in this commutation setup,
`G.O C.column = C.turnRow` (or at least `G.O a ∉ cIco P.bottom s` for both pentagons).
Combined with the added-strip emptiness, both corrections are `1` and the weight
identity follows from `OMonomial_mul_OMonomial_recutLeftEqLeft` plus the
covered-columns transfer (item 1b).

## What remains to be formalized

1. **Added-strip emptiness** (`O(b)` not in `{b} ×ˢ cIco P.bottom s`):
   - The `cIco s C.oppositeTurnRow` case: pure cyclic-interval disjointness.
   - The `= C.oppositeTurnRow` case: needs `C.oppositeTurnRow ∉ cIco P.bottom s`,
     a geometric lemma about the pentagon's row span.
2. **Removed-strip analysis** (`O(a)` vs `cIco P.bottom s`): needs either
   `G.O a = s` or a comparison of `P.bottom` with `C.oppositeTurnRow`.
3. **New pentagon inherits the hypotheses**: the turn-row transport for `E.pentagon`
   (currently `hturn` in `OverlapRight.lean`) must be proved to apply the strip
   lemmas to the new pentagon.
4. **Assemble**: combine correction-`1` for both pentagons with
   `OMonomial_mul_OMonomial_recutLeftEqLeft` and the item-1b covered-columns transfer
   to get `rectanglePentagonWeight D = pentagonRectangleWeight E`.

## Formalized below

The added-strip disjointness for the `cIco`-case, which is pure interval combinatorics.
-/

namespace TauCeti
namespace GridDiagram

variable {n : ℕ} {G : GridDiagram n}

public section

/-- The added strip of a pentagon (column `b`, rows below the turn) is disjoint from the
bigon above the turn. Hence an `O`-marking in `cIco s t` cannot lie in the strip rows. -/
theorem addedStrip_disjoint_bigonAbove {s t pb : Fin n}
    (h : Disjoint (Grid.cIco pb s) (Grid.cIco s t)) {r : Fin n}
    (hr : r ∈ Grid.cIco s t) : r ∉ Grid.cIco pb s :=
  fun hmem => Finset.disjoint_left.mp h hmem hr

end

end GridDiagram
end TauCeti
