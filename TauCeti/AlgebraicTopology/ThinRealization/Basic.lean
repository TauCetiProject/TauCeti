/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.AlgebraicTopology.SimplexCategory.Basic
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Topology.Compactness.Lindelof

/-!
# Thin geometric realization of simplicial spaces

Let `X : SimplicialObject TopCat.{u}` be a simplicial topological space. Its *thin geometric
realization* `TauCeti.thinRealization X` is the functor tensor product
`TauCeti.functorTensor SimplexCategory.toTop X`: the quotient of `Σ n : SimplexCategory, Xₙ × Δⁿ`
by the identifications `(X(f) x, t) ∼ (x, f_* t)` along **all** morphisms `f : m ⟶ n` of
`SimplexCategory`—both face and degeneracy operators—equipped with the quotient topology.

Unlike the fat realization `TauCeti.fatRealization` (which quotients only by injective operators of
`SemiSimplexCategory`), the thin realization collapses degenerate simplices along codegeneracies.
Forgetting degeneracies therefore induces a canonical surjective quotient map
`TauCeti.thinRealization.fatToThin` from the fat realization to the thin realization via
`TauCeti.functorTensor.reindex`.

Characteristic maps, universal property, functoriality, augmentations, homotopies, and open/closed
restrictions for saturated simplicial subspaces are inherited directly from `TauCeti.functorTensor`.
This file adds the simplicial specializations `TauCeti.thinRealization.instLindelofSpace`,
`TauCeti.thinRealization.instUCompactlyGeneratedSpace`, and `TauCeti.thinRealization.fatToThin`.

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. (2) **65**
  (1957), 357–362.
* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
-/

public noncomputable section

open CategoryTheory Opposite Topology
open scoped Simplicial

universe v u

namespace TauCeti

open SimplexCategory (toTop)

/-- The thin geometric realization `|X|` of a simplicial space `X`: the functor tensor product of
`SimplexCategory.toTop` and `X`. -/
abbrev thinRealization (X : SimplicialObject TopCat.{u}) : TopCat.{u} :=
  functorTensor SimplexCategory.toTop X

/-- The thin geometric realization as a functor from simplicial spaces to spaces. -/
abbrev thinRealizationFunctor : SimplicialObject TopCat.{u} ⥤ TopCat.{u} :=
  functorTensorFunctor SimplexCategory.toTop

namespace thinRealization

variable (X : SimplicialObject TopCat.{u})

/-- If every level of `X` is Lindelöf, then its thin realization is Lindelöf: each `Xₙ × Δⁿ` is
a product of a Lindelöf space with a compact simplex, and `SimplexCategory` is countable. -/
instance instLindelofSpace [hX : ∀ n : ℕ, LindelofSpace (X _⦋n⦌)] :
    LindelofSpace (thinRealization X) := by
  have (n : SimplexCategory) : LindelofSpace (X.obj (op n) × toTop.{u}.obj n) := by
    have : LindelofSpace (X.obj (op ⦋n.len⦌)) := hX n.len
    infer_instance
  infer_instance

/-- If each cell space `Xₙ × Δⁿ` is compactly generated (for instance when each `Xₙ` is first
countable, or Hausdorff and weakly locally compact), then `thinRealization X` is compactly
generated. -/
instance instUCompactlyGeneratedSpace
    [hX : ∀ n : ℕ, UCompactlyGeneratedSpace.{v} (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{v} (thinRealization X) := by
  have (n : SimplexCategory) : UCompactlyGeneratedSpace.{v} (X.obj (op n) × toTop.{u}.obj n) :=
    hX n.len
  infer_instance

/-- The canonical comparison map from the fat realization of the underlying semi-simplicial space
to the thin realization, collapsing codegeneracy identifications. -/
def fatToThin :
    fatRealization (SemiSimplexCategory.toSimplexCategory.op ⋙ X) ⟶ thinRealization X :=
  functorTensor.reindex SemiSimplexCategory.toSimplexCategory SimplexCategory.toTop X

/-- `fatToThin` sends each fat characteristic simplex to the corresponding thin characteristic
simplex. -/
-- Simplify before the functor-object types in the characteristic map are normalized.
@[simp↓]
theorem fatToThin_ι (n : SemiSimplexCategory)
    (x : (SemiSimplexCategory.toSimplexCategory.op ⋙ X).obj (op n))
    (t : SemiSimplexCategory.toTop.{u}.obj n) :
    fatToThin X
        (functorTensor.ι SemiSimplexCategory.toTop
          (SemiSimplexCategory.toSimplexCategory.op ⋙ X) n (x, t)) =
      functorTensor.ι SimplexCategory.toTop X
        (SemiSimplexCategory.toSimplexCategory.obj n) (x, t) :=
  functorTensor.reindex_ι SemiSimplexCategory.toSimplexCategory SimplexCategory.toTop X n x t

/-- The comparison map from the fat realization to the thin realization is a quotient map. -/
theorem isQuotientMap_fatToThin : IsQuotientMap (fatToThin X) :=
  functorTensor.isQuotientMap_reindex SemiSimplexCategory.toSimplexCategory SimplexCategory.toTop X
    fun n ↦ ⟨SemiSimplexCategory.mk n.len, rfl⟩

/-- The comparison map from the fat realization to the thin realization is surjective. -/
theorem fatToThin_surjective : Function.Surjective (fatToThin X) :=
  (isQuotientMap_fatToThin X).surjective

/-- `fatToThin` is natural in the simplicial space. -/
@[reassoc (attr := simp)]
theorem fatToThin_naturality {X Y : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) :
    functorTensor.map SemiSimplexCategory.toTop (Functor.whiskerLeft _ φ) ≫ fatToThin Y =
      fatToThin X ≫ functorTensor.map SimplexCategory.toTop φ :=
  functorTensor.map_comp_reindex SemiSimplexCategory.toSimplexCategory SimplexCategory.toTop φ

/-- Pulling a thin augmentation back along `fatToThin` recovers the fat augmentation of the
underlying semi-simplicial space. -/
@[reassoc (attr := simp)]
theorem fatToThin_comp_augment {X : SimplicialObject TopCat.{u}} {Z : TopCat.{u}}
    (ε : X ⟶ (Functor.const _).obj Z) :
    fatToThin X ≫ functorTensor.augment SimplexCategory.toTop ε =
      functorTensor.augment SemiSimplexCategory.toTop
        (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op ε) :=
  functorTensor.reindex_comp_augment SemiSimplexCategory.toSimplexCategory SimplexCategory.toTop ε

end thinRealization

end TauCeti
