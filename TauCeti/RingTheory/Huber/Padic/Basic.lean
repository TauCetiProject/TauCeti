/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Ring.Compact
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.AdicRing.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# The p-adic integers are an adic ring, a Huber ring, and not a Tate ring

`ℤ_[p]` with its norm topology is an adic ring of finite ideal type and hence a Huber ring, with
`(ℤ_[p], (p))` as a pair of definition, and it is not a Tate ring. After the discrete case it is
the simplest example, and it separates `TauCeti.Huber.IsHuberRing` from
`TauCeti.Huber.IsTateRing`: the topology is adic for the proper ideal `(p)`, so no unit is
topologically nilpotent.

## Main results

* `TauCeti.Huber.PadicInt.instIsLinearTopology`: from `PadicInt.isAdic_maximalIdeal` (in
  `TauCeti.NumberTheory.Padics.PadicIntegers`), `ℤ_[p]` is linearly topologized, and
  `TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd`: its topologically nilpotent
  elements are the multiples of `p`.
* `TauCeti.Huber.PadicInt.isAdicRing`, `TauCeti.Huber.PadicInt.isHuberRing`, and
  `TauCeti.Huber.PadicInt.not_isTateRing`: `ℤ_[p]` is an adic ring of finite ideal type (hence a
  Huber ring) and not a Tate ring.

## Implementation notes

The pair of definition `(ℤ_[p], (p))` is the general adic pair
`TauCeti.Huber.PairOfDefinition.adic` of `TauCeti/RingTheory/Huber/Adic.lean`, applied to the
maximal ideal.

## Scope

Only `ℤ_[p]` is treated here. That `ℚ_[p]` is a Tate ring is in
`TauCeti.RingTheory.Huber.Padic.Field`, and that the Tate algebra `ℚ_p⟨T₁,…,Tₙ⟩` is a complete
strongly noetherian Tate ring is in `TauCeti.RingTheory.Huber.Padic.TateAlgebra`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §6, where Huber and Tate rings are introduced
  (Proposition and Definition 6.1) and `ℤ_[p]` is the standard example of a Huber ring that
  is not Tate.
-/

public section

open Topology IsLocalRing

namespace TauCeti.Huber

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The norm topology of `ℤ_[p]` is linear: the ideals `(p ^ n)` are a neighbourhood basis of
zero. -/
instance instIsLinearTopology : IsLinearTopology ℤ_[p] ℤ_[p] :=
  _root_.PadicInt.isAdic_maximalIdeal.isLinearTopology

/-- A `p`-adic integer is topologically nilpotent exactly when it is divisible by `p`. -/
theorem isTopologicallyNilpotent_iff_dvd {c : ℤ_[p]} :
    IsTopologicallyNilpotent c ↔ (p : ℤ_[p]) ∣ c := by
  rw [_root_.PadicInt.isAdic_maximalIdeal.isTopologicallyNilpotent_iff_mem_radical,
    (maximalIdeal.isMaximal ℤ_[p]).isPrime.radical, _root_.PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/-- **`ℤ_[p]` is an adic ring of finite ideal type**, with `(p)` as a finitely generated ideal of
definition. -/
instance isAdicRing : IsAdicRing ℤ_[p] :=
  ⟨maximalIdeal ℤ_[p], IsNoetherian.noetherian _, _root_.PadicInt.isAdic_maximalIdeal,
    inferInstance⟩

/-- **`ℤ_[p]` is a Huber ring**, with `(ℤ_[p], (p))` as a pair of definition: the norm topology
is the adic topology of the principal ideal `(p)`. -/
instance isHuberRing : IsHuberRing ℤ_[p] := inferInstance

/-- **`ℤ_[p]` is not a Tate ring**: it admits no pseudouniformiser. Together with
`TauCeti.Huber.PadicInt.isHuberRing` this separates `IsHuberRing` from `IsTateRing`. -/
theorem not_isTateRing : ¬ IsTateRing ℤ_[p] := fun _ ↦
  (maximalIdeal.isMaximal ℤ_[p]).ne_top
    (IsTateRing.eq_top_of_isAdic _root_.PadicInt.isAdic_maximalIdeal)

end PadicInt

end TauCeti.Huber
