/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Pullback

/-!
# Graphons given by a matrix on a countable carrier

On a countable discrete probability carrier there is nothing to a graphon beyond a symmetric
`[0, 1]`-valued matrix: measurability is automatic.  `Graphon.ofMatrix` packages such a matrix as a
graphon, with the vertex weights carried by the measure and the edge weights by the matrix.  When
the carrier is finite this is a **weighted graph** in the terminology of the graph-limit
literature, but nothing here needs finiteness.

The point of the construction is that these carriers are the *values* a graphon takes once it has
been coarsened: a graphon whose value at `(x, y)` depends on `x` and `y` only through a measurable
map `g : Ω → κ` into such a carrier is exactly the pullback of a matrix along `g`, which is
`exists_ofMatrix_eq_comap_of_factorsThrough`.  Step graphons are the case where `g` is the
part-index map of a measurable finite partition, so a step graphon is the pullback of its block
matrix and the cut distance to it is a cut distance to a finite object.

## Main definitions

* `TauCeti.DenseGraphLimits.Graphon.ofMatrix` -- the graphon of a symmetric `[0, 1]`-valued matrix
  on a countable discrete probability carrier.

## Main results

* `TauCeti.DenseGraphLimits.exists_ofMatrix_eq_comap_of_factorsThrough` -- a graphon whose value
  depends only on the image of its two arguments under a measurable map into a countable discrete
  space is the pullback of a matrix along that map.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 2 -- weighted graphs as "the
  technically convenient dense subset", and the step graphons the density and total-boundedness
  statements are about.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.1 and
  §9.2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

section OfMatrix

variable {κ : Type*} [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]
  (ν : Measure κ) [IsProbabilityMeasure ν]

/-- The graphon of a symmetric `[0, 1]`-valued matrix `b` on a countable discrete probability
carrier `(κ, ν)`, with `ν` carrying the vertex weights and `b` the edge weights.  For a finite
carrier this is the graphon of a weighted graph.

Nothing has to be checked beyond symmetry and the range constraint: every function out of a
countable discrete space is measurable. -/
def Graphon.ofMatrix (b : κ → κ → Set.Icc (0 : ℝ) 1) (hb : ∀ i j, b i j = b j i) :
    Graphon κ ν where
  toFun i j := b i j
  symm' i j := congrArg Subtype.val (hb i j)
  meas' := measurable_of_countable _
  bdd' := ⟨1, fun i j => by
    rw [abs_of_nonneg (b i j).property.1]
    exact (b i j).property.2⟩
  mem01' i j := (b i j).property

@[simp]
theorem Graphon.ofMatrix_apply (b : κ → κ → Set.Icc (0 : ℝ) 1) (hb : ∀ i j, b i j = b j i)
    (i j : κ) : Graphon.ofMatrix ν b hb i j = (b i j : ℝ) := (rfl)

end OfMatrix

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {κ : Type*} [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]
  {ν : Measure κ} [IsProbabilityMeasure ν]

/-- A graphon whose value at `(x, y)` depends on `x` and `y` only through a measurable map `g` into
a countable discrete carrier is the pullback along `g` of a matrix on that carrier.  The vertex
weights `ν` are arbitrary: only the underlying function is being rebuilt.

The matrix is existentially quantified because it is only determined on the range of `g`: outside
the range any symmetric completion does, and the one produced here reads the value at an arbitrary
`g`-preimage. -/
theorem exists_ofMatrix_eq_comap_of_factorsThrough (W : Graphon Ω μ) {g : Ω → κ}
    (hg : Measurable g)
    (hfac : ∀ x y x' y', g x = g x' → g y = g y' → W x y = W x' y') :
    ∃ (b : κ → κ → Set.Icc (0 : ℝ) 1) (hb : ∀ i j, b i j = b j i),
      W = (Graphon.ofMatrix ν b hb).comap g hg μ := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  refine ⟨fun i j => ⟨W (Function.invFun g i) (Function.invFun g j), W.mem_Icc _ _⟩,
    fun i j => Subtype.ext (W.symm _ _), ?_⟩
  ext x y
  rw [Graphon.comap_apply, Graphon.ofMatrix_apply]
  exact hfac x y _ _ (Function.invFun_eq ⟨x, rfl⟩).symm (Function.invFun_eq ⟨y, rfl⟩).symm

end DenseGraphLimits

end TauCeti
