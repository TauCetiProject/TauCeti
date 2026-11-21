/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Semicontinuity.Defs
import TauCeti.Topology.Semicontinuity.Basic

/-!
# Semicontinuity of locally finite functions in the lexicographic order

Coordinatewise continuity or upper semicontinuity of `f : α → ∀ i, β i` does not in general imply
upper semicontinuity of `fun x ↦ toLex (f x) : α → Lex (∀ i, β i)`: for example, `t ↦ (|t|, 0)`
on `ℝ` is coordinatewise continuous at `0`, satisfies `toLex (0, 0) < toLex (0, 1)` at `t = 0`,
yet satisfies `toLex (0, 1) < toLex (|t|, 0)` for every `t ≠ 0`.

When `f` locally takes finitely many values, however, the general product-order results in
`TauCeti.Topology.Semicontinuity.Basic` (`TauCeti.eventually_le_of_upperSemicontinuousWithinAt` and
`Monotone.upperSemicontinuousWithinAt_comp_of_finite`, together with their `At`, `On`, global, and
lower semicontinuous variants) show that post-composing with any monotone map into a preorder
preserves semicontinuity. Specializing along `toLex : (∀ i, β i) → Lex (∀ i, β i)` when `ι` is
well-ordered (`Pi.toLex_monotone`) lifts coordinatewise upper and lower semicontinuity to
`Lex (∀ i, β i)`.

This mechanism underlies Zariski upper semicontinuity of lexicographically ordered invariants (such
as Hilbert–Samuel functions on closed points) once pointwise upper semicontinuity and local
finiteness of attained values are established.

## Main results

* `TauCeti.upperSemicontinuousWithinAt_toLex`, `TauCeti.upperSemicontinuousAt_toLex`,
  `TauCeti.upperSemicontinuousOn_toLex`, `TauCeti.upperSemicontinuous_toLex`: coordinatewise upper
  semicontinuity lifts to `Lex (∀ i, β i)` whenever `f` locally takes finitely many values.
* `TauCeti.lowerSemicontinuousWithinAt_toLex`, `TauCeti.lowerSemicontinuousAt_toLex`,
  `TauCeti.lowerSemicontinuousOn_toLex`, `TauCeti.lowerSemicontinuous_toLex`: the dual lower
  semicontinuity statements.

## References

* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *$\mathbb{Q}$-universal
  desingularization*, Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

open scoped Topology

namespace TauCeti

section PiLex

variable {α ι : Type*} {β : ι → Type*} [TopologicalSpace α]
  [LinearOrder ι] [WellFoundedLT ι] [∀ i, LinearOrder (β i)]

/-- If each coordinate of `f` is upper semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `fun x' ↦ toLex (f x')` is upper semicontinuous
within `s` at `x`. -/
theorem upperSemicontinuousWithinAt_toLex {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, UpperSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x :=
  Pi.toLex_monotone.upperSemicontinuousWithinAt_comp_of_finite hf hfin

/-- If each coordinate of `f` is upper semicontinuous at `x` and `f` takes finitely many values on
a neighbourhood of `x`, then `fun x' ↦ toLex (f x')` is upper semicontinuous at `x`. -/
theorem upperSemicontinuousAt_toLex {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, UpperSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuousAt (fun x' ↦ toLex (f x')) x :=
  Pi.toLex_monotone.upperSemicontinuousAt_comp_of_finite hf hfin

/-- If each coordinate of `f` is upper semicontinuous on `s` and `f` locally takes finitely many
values within `s`, then `fun x' ↦ toLex (f x')` is upper semicontinuous on `s`. -/
theorem upperSemicontinuousOn_toLex {f : α → ∀ i, β i} {s : Set α}
    (hf : ∀ i, UpperSemicontinuousOn (f · i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    UpperSemicontinuousOn (fun x' ↦ toLex (f x')) s :=
  Pi.toLex_monotone.upperSemicontinuousOn_comp_of_finite hf hfin

/-- If each coordinate of `f` is upper semicontinuous and `f` locally takes finitely many values,
then `fun x' ↦ toLex (f x')` is upper semicontinuous. -/
theorem upperSemicontinuous_toLex {f : α → ∀ i, β i}
    (hf : ∀ i, UpperSemicontinuous (f · i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    UpperSemicontinuous (fun x' ↦ toLex (f x')) :=
  Pi.toLex_monotone.upperSemicontinuous_comp_of_finite hf hfin

/-- If each coordinate of `f` is lower semicontinuous within `s` at `x` and `f` takes finitely many
values on a neighbourhood of `x` within `s`, then `fun x' ↦ toLex (f x')` is lower semicontinuous
within `s` at `x`. -/
theorem lowerSemicontinuousWithinAt_toLex {f : α → ∀ i, β i} {s : Set α} {x : α}
    (hf : ∀ i, LowerSemicontinuousWithinAt (f · i) s x)
    (hfin : ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousWithinAt (fun x' ↦ toLex (f x')) s x :=
  Pi.toLex_monotone.lowerSemicontinuousWithinAt_comp_of_finite hf hfin

/-- If each coordinate of `f` is lower semicontinuous at `x` and `f` takes finitely many values on
a neighbourhood of `x`, then `fun x' ↦ toLex (f x')` is lower semicontinuous at `x`. -/
theorem lowerSemicontinuousAt_toLex {f : α → ∀ i, β i} {x : α}
    (hf : ∀ i, LowerSemicontinuousAt (f · i) x)
    (hfin : ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    LowerSemicontinuousAt (fun x' ↦ toLex (f x')) x :=
  Pi.toLex_monotone.lowerSemicontinuousAt_comp_of_finite hf hfin

/-- If each coordinate of `f` is lower semicontinuous on `s` and `f` locally takes finitely many
values within `s`, then `fun x' ↦ toLex (f x')` is lower semicontinuous on `s`. -/
theorem lowerSemicontinuousOn_toLex {f : α → ∀ i, β i} {s : Set α}
    (hf : ∀ i, LowerSemicontinuousOn (f · i) s)
    (hfin : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, (f '' u).Finite) :
    LowerSemicontinuousOn (fun x' ↦ toLex (f x')) s :=
  Pi.toLex_monotone.lowerSemicontinuousOn_comp_of_finite hf hfin

/-- If each coordinate of `f` is lower semicontinuous and `f` locally takes finitely many values,
then `fun x' ↦ toLex (f x')` is lower semicontinuous. -/
theorem lowerSemicontinuous_toLex {f : α → ∀ i, β i}
    (hf : ∀ i, LowerSemicontinuous (f · i))
    (hfin : ∀ x, ∃ u ∈ 𝓝 x, (f '' u).Finite) :
    LowerSemicontinuous (fun x' ↦ toLex (f x')) :=
  Pi.toLex_monotone.lowerSemicontinuous_comp_of_finite hf hfin

end PiLex

end TauCeti
