/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Local dimension of schemes locally of finite type over a field

Let `X` be a scheme locally of finite type over a field `k`, and let `x ∈ X`. The residue field
`κ(x)` is a `k`-algebra through the structure morphism (`Scheme.residueFieldBaseAlgebra`). This
file computes the dimension of the closure of `x` and the local Krull dimension `dim_x X` of `X`
at `x` (`TauCeti.topologicalKrullDimAt`):

* `dim {x}⁻ = trdeg_k κ(x)`;
* `dim_x X = dim O_{X,x} + trdeg_k κ(x) = dim O_{X,x} + dim {x}⁻`;
* `dim_x X` is the supremum of `dim Z` over the irreducible components `Z` of `X` through `x`,
  that is, of `trdeg_k κ(ξ)` over their generic points `ξ`.

The first two statements are local on `X`. On an affine chart `Spec A ⟶ X` through `x`, with `A` a
finitely generated `k`-algebra and `x` corresponding to a prime `p`, they are the affine statements
`dim (A ⧸ p) = trdeg_k κ(p)` (`Ideal.ringKrullDim_quotient_eq_toNat_trdeg_residueField`) and
`dim_p Spec A = ht p + dim (A ⧸ p)`
(`TauCeti.topologicalKrullDimAt_eq_height_add_ringKrullDim_quotient`). The chart is an open
embedding, so it preserves local dimension; it identifies the stalk `O_{X,x}` with `A_p`, whose
dimension is `ht p`; and it identifies `κ(x)` with `κ(p)` as `k`-algebras. The closure of `x`
meets the chart in a nonempty open part of an irreducible closed set, which has the dimension of
the whole closure (`TauCeti.AlgebraicGeometry.topologicalKrullDim_inter_eq_of_locallyOfFiniteType`).
For the same reason every open neighbourhood of `x` has dimension at least that of each
component through `x`; conversely, in an affine chart a small neighbourhood of `x` is covered by
the components through `x` (`PrimeSpectrum.topologicalKrullDimAt_le_iSup_ringKrullDim_quotient`).

## Main results

All in the namespace `TauCeti.AlgebraicGeometry`:

* `topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField`: `dim {x}⁻ = trdeg_k κ(x)`.
* `topologicalKrullDimAt_eq_ringKrullDim_stalk_add_toNat_trdeg_residueField`:
  `dim_x X = dim O_{X,x} + trdeg_k κ(x)`.
* `topologicalKrullDimAt_eq_ringKrullDim_stalk_add_topologicalKrullDim_closure`:
  `dim_x X = dim O_{X,x} + dim {x}⁻`.
* `topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents`: `dim_x X` is the
  supremum of the dimensions of the irreducible components through `x`.
* `topologicalKrullDimAt_eq_iSup_toNat_trdeg_residueField`: `dim_x X` is the supremum of
  `trdeg_k κ(ξ)` over the generic points `ξ` of the irreducible components through `x`.

## References

* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0),
  [Tag 06RP](https://stacks.math.columbia.edu/tag/06RP) and
  [Tag 00P1](https://stacks.math.columbia.edu/tag/00P1) (dimension of finite type algebras over a
  field)
-/
public section

open CategoryTheory AlgebraicGeometry Topology

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **Dimension of a point closure.** On a scheme `X` locally of finite type over a field `k`, the
closure of a point `x` has dimension the transcendence degree of the residue field `κ(x)`
over `k`. -/
theorem topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) = (Algebra.trdeg k (X.residueField x)).toNat := by
  obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := (X ↘ Spec (.of k)).exists_isOpenImmersion_finiteType x
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k R := hR
  have := y.isPrime
  -- The closure of `g y` meets the chart in the closure `V(y)` of `y`, a nonempty open part of an
  -- irreducible closed set; so it has the dimension `dim (R ⧸ y) = trdeg_k κ(y)` of `V(y)`.
  have hpre : g ⁻¹' closure {g y} = closure {y} := by
    rw [g.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage g.continuous,
      ← Set.image_singleton, g.isOpenEmbedding.injective.preimage_image]
  calc topologicalKrullDim (closure ({g y} : Set X))
      = topologicalKrullDim ↥(closure {g y} ∩ Set.range g) :=
        (topologicalKrullDim_inter_eq_of_locallyOfFiniteType (X ↘ Spec (.of k))
          isIrreducible_singleton.closure isClosed_closure g.isOpenEmbedding.isOpen_range
          ⟨g y, subset_closure rfl, y, rfl⟩).symm
    _ = topologicalKrullDim (closure ({y} : Set (Spec R))) := by
        rw [← g.isOpenEmbedding.isEmbedding.topologicalKrullDim_preimage, hpre]
    -- The underlying space of `Spec R` is `PrimeSpectrum R` by definition.
    _ = ringKrullDim (R ⧸ y.asIdeal) :=
        (congrArg (fun s : Set (PrimeSpectrum R) ↦ topologicalKrullDim s)
          (PrimeSpectrum.closure_singleton y)).trans (Ideal.topologicalKrullDim_zeroLocus _)
    _ = _ := by
        rw [Ideal.ringKrullDim_quotient_eq_toNat_trdeg_residueField k,
          (g.residueFieldAlgEquivOfIsOpenImmersion φ hφ y).trdeg_eq]

/-- **Local dimension via the stalk.** On a scheme `X` locally of finite type over a field `k`, the
local Krull dimension at a point `x` is the dimension of the local ring `O_{X,x}` plus the
transcendence degree of the residue field `κ(x)` over `k`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_stalk_add_toNat_trdeg_residueField (x : X) :
    topologicalKrullDimAt X x =
      ringKrullDim (X.presheaf.stalk x) + (Algebra.trdeg k (X.residueField x)).toNat := by
  obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := (X ↘ Spec (.of k)).exists_isOpenImmersion_finiteType x
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k R := hR
  -- The chart preserves local dimension, identifies `O_{X,g y}` with `R_y` (of dimension
  -- `ht y`) and `κ(g y)` with `κ(y)`; then apply the affine formula `ht y + dim (R ⧸ y)`.
  rw [← g.isOpenEmbedding.topologicalKrullDimAt_eq, ringKrullDim_stalk_eq_coheight,
    coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight,
    (g.residueFieldAlgEquivOfIsOpenImmersion φ hφ y).trdeg_eq]
  rw [← Ideal.ringKrullDim_quotient_eq_toNat_trdeg_residueField k]
  exact topologicalKrullDimAt_eq_height_add_ringKrullDim_quotient k y

include k in
/-- **Local dimension via the stalk and the point closure.** On a scheme `X` locally of finite
type over a field, the local Krull dimension at a point `x` is the dimension of the local ring
`O_{X,x}` plus the dimension of the closure of `x`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_stalk_add_topologicalKrullDim_closure (x : X) :
    topologicalKrullDimAt X x =
      ringKrullDim (X.presheaf.stalk x) + topologicalKrullDim (closure ({x} : Set X)) := by
  rw [topologicalKrullDimAt_eq_ringKrullDim_stalk_add_toNat_trdeg_residueField k,
    topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField k]

include k in
/-- **Local dimension via irreducible components.** On a scheme `X` locally of finite type over a
field, the local Krull dimension at a point `x` is the supremum of the dimensions of the
irreducible components of `X` through `x`. -/
theorem topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents (x : X) :
    topologicalKrullDimAt X x =
      ⨆ (Z ∈ irreducibleComponents X) (_ : x ∈ Z), topologicalKrullDim Z := by
  refine le_antisymm ?_ (iSup₂_le fun Z hZ ↦ iSup_le fun hxZ ↦
    (topologicalKrullDimAt_eq_iInf x).ge.trans' (le_iInf fun U ↦ ?_))
  · -- In an affine chart `Spec R` through `x`, the local dimension is bounded by the dimensions
    -- of the components `V(q)` of `Spec R` through `x`, and each lies in a component of `X`.
    obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := (X ↘ Spec (.of k)).exists_isOpenImmersion_finiteType x
    let := φ.hom.toAlgebra
    have : Algebra.FiniteType k R := hR
    have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    rw [← g.isOpenEmbedding.topologicalKrullDimAt_eq]
    refine (PrimeSpectrum.topologicalKrullDimAt_le_iSup_ringKrullDim_quotient y).trans
      (iSup₂_le fun q hq ↦ iSup_le fun hqy ↦ ?_)
    have := hq.1.1
    let V : Set (Spec R) := PrimeSpectrum.zeroLocus (q : Set R)
    have hV : IsIrreducible V := (PrimeSpectrum.isIrreducible_zeroLocus_iff q).2 (by
      rwa [this.radical])
    obtain ⟨Z, hZ, hVZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (hV.image g g.continuous.continuousOn)
    refine le_iSup₂_of_le Z hZ (le_iSup_of_le (hVZ ⟨y, (PrimeSpectrum.mem_zeroLocus _ _).2 hqy,
      rfl⟩) ?_)
    rw [← Ideal.topologicalKrullDim_zeroLocus]
    exact ((g.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict Z
      fun v ↦ hVZ ⟨v.1, v.2, rfl⟩).isInducing.topologicalKrullDim_le
  · -- A component `Z` through `x` meets every open neighbourhood `U` of `x` in a nonempty open
    -- part of `Z`, which has the dimension of `Z`.
    rw [← topologicalKrullDim_inter_eq_of_locallyOfFiniteType (X ↘ Spec (.of k)) hZ.1
      (isClosed_of_mem_irreducibleComponents Z hZ) U.2.1 ⟨x, hxZ, U.2.2⟩]
    exact (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le

/-- **Local dimension via generic points.** On a scheme `X` locally of finite type over a field
`k`, the local Krull dimension at a point `x` is the supremum of the transcendence degrees over `k`
of the residue fields at the generic points `ξ` of the irreducible components of `X` through `x`.
-/
theorem topologicalKrullDimAt_eq_iSup_toNat_trdeg_residueField (x : X) :
    topologicalKrullDimAt X x = ⨆ (ξ : X) (_ : closure {ξ} ∈ irreducibleComponents X)
      (_ : ξ ⤳ x), ((Algebra.trdeg k (X.residueField ξ)).toNat : WithBot ℕ∞) := by
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents k]
  refine le_antisymm (iSup₂_le fun Z hZ ↦ iSup_le fun hxZ ↦ ?_)
    (iSup₂_le fun ξ hξ ↦ iSup_le fun hξx ↦ ?_)
  · -- Every component `Z` is the closure of its generic point.
    have hξ : closure {hZ.1.genericPoint} = Z :=
      hZ.1.isGenericPoint_genericPoint_closure.trans
        (isClosed_of_mem_irreducibleComponents Z hZ).closure_eq
    refine le_iSup₂_of_le hZ.1.genericPoint (by rwa [hξ])
      (le_iSup_of_le (specializes_iff_mem_closure.2 (by rwa [hξ])) ?_)
    rw [← topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField k, hξ]
  · rw [← topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField k]
    exact le_iSup₂_of_le _ hξ (le_iSup_of_le (specializes_iff_mem_closure.1 hξx) le_rfl)

end AlgebraicGeometry

end TauCeti
