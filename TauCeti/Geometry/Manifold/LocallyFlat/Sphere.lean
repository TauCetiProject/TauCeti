/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Brown's bicollaring theorem for locally flat spheres

A locally flat codimension-one sphere in a sphere has a global bicollar.  This is the global
collaring theorem that turns the local product charts in `TauCeti.IsLocallyFlat` into one product
neighbourhood of the entire embedded sphere.  It is the structural input to the annulus theorem:
the two sides of the bicollar distinguish the regions adjacent to a locally flat sphere, a
conclusion which fails for wild embeddings such as the Alexander horned sphere.

This file records Brown's theorem as the dimension-indexed proposition
`TauCeti.BrownBicollaring`.  The theorem is stated rather than proved.

The indexing uses an `n`-sphere in `EuclideanSpace ℝ (Fin (n + 1))` embedded in the
`(n + 1)`-sphere in `EuclideanSpace ℝ (Fin (n + 2))`.  Local flatness is read in the split
ambient model `EuclideanSpace ℝ (Fin n) × ℝ`: the first factor is the model of the source
sphere, and the second is its one-dimensional normal direction.  No orientation or choice of
side is included in the statement.

## Main definitions

* `TauCeti.BrownBicollaring`: every locally flat embedding `Sⁿ → Sⁿ⁺¹` is globally
  bicollared.

## Main results

* `TauCeti.brownBicollaring_iff`: the defining characterization of Brown's theorem.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* R. J. Daverman and G. A. Venema, *Embeddings in Manifolds*, Graduate Studies in Mathematics
  106, American Mathematical Society (2009), Chapter 2.
-/

public section

noncomputable section

namespace TauCeti

open Metric
open Topology
open scoped EuclideanSpace

/-- **Brown's bicollaring theorem in dimension `n`:** every locally flat embedding of the
standard `n`-sphere in the standard `(n + 1)`-sphere admits a global bicollar.

The local-flatness model is `EuclideanSpace ℝ (Fin n) × ℝ`: its zero slice has dimension
`n`, and its complementary factor has dimension one.  Thus the hypothesis says precisely that
the embedding is locally a codimension-one coordinate slice.  The conclusion is the existence of
an open embedding `Sⁿ × ℝ → Sⁿ⁺¹` whose zero slice is the original embedding. -/
def BrownBicollaring (n : ℕ) : Prop :=
  ∀ f :
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
    IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f → IsBicollared f

/-- The defining characterization of Brown's bicollaring theorem. -/
theorem brownBicollaring_iff {n : ℕ} :
    BrownBicollaring n ↔
      ∀ f :
          sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
            sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
        IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f → IsBicollared f :=
  by rfl

end TauCeti
