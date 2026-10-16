/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# The p-adic numbers are a Tate ring

`ℚ_[p]` is a Tate ring, with `(ℤ_[p], (p))` as a pair of definition and `p` as a
pseudouniformiser. Together with `TauCeti.Huber.PadicInt.not_isTateRing` this is the example
separating the two notions: the same ideal of definition makes `ℤ_[p]` Huber but not Tate, and
`ℚ_[p]` Tate, the difference being that `p` becomes a unit in `ℚ_[p]`.

The instance itself is not stated here: `ℚ_[p]` is a nontrivially normed field with an ultrametric
norm, so it is a Tate ring by `TauCeti.Huber.IsTateRing.of_nontriviallyNormedField`. This file
records the explicit pair of definition and pseudouniformiser.

No `Ideal.comap` is needed here. Mathlib's `ℤ_[p]` is the subtype `{x : ℚ_[p] // ‖x‖ ≤ 1}` and
`PadicInt.subring p` is a separate declaration cutting out the same set, so `ℤ_[p]` and
`↥(PadicInt.subring p)` are definitionally equal. That is why `idealOfDefinition :=
maximalIdeal ℤ_[p]` typechecks against the expected `Ideal ↥(PadicInt.subring p)` below.

## Main definitions

* `TauCeti.Huber.Padic.pairOfDefinition`: the pair of definition `(ℤ_[p], (p))` of `ℚ_[p]`.

## Main results

* `TauCeti.Huber.Padic.pairOfDefinition_ringOfDefinition` and
  `TauCeti.Huber.Padic.mem_pairOfDefinition_idealOfDefinition`: the two projections of the pair.
  The ring of definition is pinned down by an equation, the ideal of definition by the
  membership form `‖x‖ < 1` — see the note on that lemma for why.
* `TauCeti.Huber.Padic.isPseudoUniformizer_p`: `p` is a pseudouniformiser of `ℚ_[p]`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §6, where Huber and Tate rings are introduced
  (Proposition and Definition 6.1) and `ℚ_[p]` is the standard example of a Tate ring.
-/

public section

open Topology IsLocalRing

namespace TauCeti.Huber

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- The unit ball `ℤ_[p]` is open in `ℚ_[p]`. This is Mathlib's
`PadicInt.isOpenEmbedding_coe` read through `Subtype.range_coe`. -/
private theorem isOpen_padicIntSubring :
    IsOpen ((_root_.PadicInt.subring p : Subring ℚ_[p]) : Set ℚ_[p]) := by
  have h := (_root_.PadicInt.isOpenEmbedding_coe (p := p)).isOpen_range
  rwa [Subtype.range_coe_subtype] at h

/-- `p` is a pseudouniformiser of `ℚ_[p]`: it is a unit, and its powers have norm `p⁻ⁿ → 0`. -/
theorem isPseudoUniformizer_p : IsPseudoUniformizer (p : ℚ_[p]) :=
  isPseudoUniformizer_iff_norm_lt_one.mpr
    ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero, _root_.Padic.norm_p_lt_one⟩

/-- The pair of definition `(ℤ_[p], (p))` exhibiting `ℚ_[p]` as a Huber ring. -/
noncomputable def pairOfDefinition : PairOfDefinition ℚ_[p] where
  ringOfDefinition := _root_.PadicInt.subring p
  isOpen_ringOfDefinition := isOpen_padicIntSubring
  idealOfDefinition := maximalIdeal ℤ_[p]
  fg_idealOfDefinition := by
    rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _
  isAdic_idealOfDefinition := PadicInt.isAdic_maximalIdeal

/-- The ring of definition of `pairOfDefinition` is `ℤ_[p]`.

The companion projection, the ideal of definition, is characterised by
`TauCeti.Huber.Padic.mem_pairOfDefinition_idealOfDefinition` in membership form rather than by an
equation; that lemma's docstring gives the reason. -/
@[simp]
theorem pairOfDefinition_ringOfDefinition :
    (pairOfDefinition (p := p)).ringOfDefinition = _root_.PadicInt.subring p := (rfl)

/-- **The ideal of definition of `pairOfDefinition` is `(p)`**, in membership form: an element
belongs exactly when its norm is less than one.

The membership form is used because the equation
`pairOfDefinition.idealOfDefinition = maximalIdeal ℤ_[p]` does not elaborate. The two sides *are*
definitionally equal — marking `pairOfDefinition` `@[expose]` makes that very statement typecheck
and closes it by `rfl` — but at the transparency the elaborator uses it will not unfold a
definition whose body is unexposed, so checking `Ideal ℤ_[p]` against
`Ideal ↥pairOfDefinition.ringOfDefinition` fails with the note that `pairOfDefinition` "was not
unfolded because their definition is not exposed". This is a limit on elaboration, not a
statement that the projection cannot reduce. Exposing the body is not worth it here, since it
would force the proof-only `isOpen_padicIntSubring` public too; membership sidesteps the issue
entirely, as `x` already inhabits the dependent type. -/
@[simp]
theorem mem_pairOfDefinition_idealOfDefinition
    {x : (pairOfDefinition (p := p)).ringOfDefinition} :
    x ∈ (pairOfDefinition (p := p)).idealOfDefinition ↔ ‖(x : ℚ_[p])‖ < 1 := by
  simp only [pairOfDefinition]
  exact _root_.PadicInt.mem_nonunits

end Padic

end TauCeti.Huber
