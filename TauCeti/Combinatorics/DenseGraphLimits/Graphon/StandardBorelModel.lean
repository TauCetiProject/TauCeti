/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Pullback
import TauCeti.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Every graphon is pulled back from a standard Borel carrier

A graphon is jointly measurable, so it depends on only countably many measurable sets of each
argument: it factors as `W x y = V (q x) (q y)` through a measurable `q : Ω → ℕ → Bool` into the
Cantor space, and the factor `V` is again symmetric and `[0, 1]`-valued
(`TauCeti.DenseGraphLimits.Graphon.exists_comap_natBool`). Since `q` is measure preserving
onto the pushforward `μ.map q`, this presents an arbitrary graphon as a pullback
`W = V.comap q` of a graphon on a **standard Borel** probability carrier.

This is the carrier-free half of Janson's Lemma 7.3, and it is what removes the standard Borel
hypothesis from the arguments that need one: the measure-theoretic input has no hypothesis on `Ω`
at all, because the factorization happens before any measure is involved.

Symmetry and the range constraint are *retained*, not re-imposed: the factor produced by the
measurable factorization need be neither, so it is averaged with its transpose and truncated to
`[0, 1]`. Both operations are invisible on the image of `q`, where the values are already
symmetric and in `[0, 1]`.

## Main results

* `TauCeti.DenseGraphLimits.Graphon.exists_comap_natBool` — every graphon is the pullback,
  along a measurable map to the Cantor space, of a graphon on the pushforward measure.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 7.3.
-/

public section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Every graphon is a pullback from a standard Borel carrier** (Janson, Lemma 7.3). There is a
measurable `q : Ω → ℕ → Bool` and a graphon `V` on the Cantor space, carrying the pushforward
measure `μ.map q`, with `W = V.comap q`; no hypothesis on `Ω` is needed.

The map `q` is measure preserving from `μ` onto `μ.map q` by construction, so `W` and `V` have the
same observables; this is the reduction that lets a statement proved over standard Borel carriers
be transported to an arbitrary probability carrier. -/
theorem Graphon.exists_comap_natBool (W : Graphon Ω μ) :
    ∃ (q : Ω → ℕ → Bool) (hq : Measurable q) (V : Graphon (ℕ → Bool) (μ.map q)),
      V.comap q hq μ = W := by
  obtain ⟨q, g, hq, hg, hW⟩ :=
    W.measurable.exists_eq_measurable_comp_prodMap_self
  have hgq : ∀ x y : Ω, g (q x, q y) = W x y := fun x y => (congrFun hW (x, y)).symm
  let V : Graphon (ℕ → Bool) (μ.map q) := Graphon.clampSymm (μ.map q) (fun a b => g (a, b)) hg
  have hVq : ∀ x y, V (q x) (q y) = W x y := by
    intro x y
    change Graphon.clampSymm (μ.map q) (fun a b => g (a, b)) hg (q x) (q y) = W x y
    calc
      _ = g (q x, q y) := Graphon.clampSymm_apply_of_mem (μ.map q)
        (fun a b => g (a, b)) hg (x := q x) (y := q y)
        (by rw [hgq, hgq, W.symm]) (by rw [hgq]; exact W.mem_Icc x y)
      _ = W x y := hgq x y
  exact ⟨q, hq, V, Graphon.ext fun x y => by simp only [Graphon.comap_apply]; exact hVq x y⟩

end DenseGraphLimits

end TauCeti
