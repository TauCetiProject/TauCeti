/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.ResidueDegree
import Mathlib.FieldTheory.FinTrdeg
import TauCeti.Topology.NoetherianSpace.ClosedPoints

/-!
# Local dimension of schemes locally of finite type over a field

Let `X` be a scheme locally of finite type over a field `k`, and let `x ∈ X`. The residue field
`κ(x)` is a `k`-algebra through the structure morphism (`Scheme.residueFieldBaseAlgebra`). This
file computes the dimension of the closure of `x` and the local Krull dimension `dim_x X` of `X`
at `x` (`TauCeti.topologicalKrullDimAt`):

* `dim {x}⁻ = trdeg_k κ(x)`;
* `dim_x X = dim O_{X,x} + trdeg_k κ(x) = dim O_{X,x} + dim {x}⁻`;
* `dim_x X` is the supremum of `dim Z` over the irreducible components `Z` of `X` through `x`,
  that is, of `trdeg_k κ(ξ)` over their generic points `ξ`;
* for `X` irreducible, `dim O_{X,x} + dim {x}⁻ = dim X`: the codimension of `x` and the dimension
  of its closure add up to the dimension of `X`.

The first two statements are local on `X`. On an affine chart `Spec A ⟶ X` through `x`, with `A` a
finitely generated `k`-algebra and `x` corresponding to a prime `p`, they are the affine statements
`dim (A ⧸ p) = trdeg_k κ(p)` (`Ideal.ringKrullDim_quotient_eq_toNat_trdeg_residueField`) and
`dim_p Spec A = ht p + dim (A ⧸ p)`
(`PrimeSpectrum.topologicalKrullDimAt_eq_height_add_ringKrullDim_quotient`). The chart is an open
embedding, so it preserves local dimension; it identifies the stalk `O_{X,x}` with `A_p`, whose
dimension is `ht p`; and it identifies `κ(x)` with `κ(p)` as `k`-algebras. The closure of `x`
meets the chart in a nonempty open part of an irreducible closed set, which has the dimension of
the whole closure (`TauCeti.AlgebraicGeometry.topologicalKrullDim_inter_eq_of_locallyOfFiniteType`).
For the same reason every open neighbourhood of `x` has dimension at least that of each
component through `x`; conversely, in an affine chart a small neighbourhood of `x` is covered by
the components through `x` (`PrimeSpectrum.topologicalKrullDimAt_le_iSup_ringKrullDim_quotient`).

## Main results

All in the namespace `TauCeti.AlgebraicGeometry`, except the last, which is in
`AlgebraicGeometry.Scheme.Hom`:

* `topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField`: `dim {x}⁻ = trdeg_k κ(x)`.
* `topologicalKrullDimAt_eq_ringKrullDim_stalk_add_toNat_trdeg_residueField`:
  `dim_x X = dim O_{X,x} + trdeg_k κ(x)`.
* `topologicalKrullDimAt_eq_ringKrullDim_stalk_add_topologicalKrullDim_closure`:
  `dim_x X = dim O_{X,x} + dim {x}⁻`.
* `topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents`: `dim_x X` is the
  supremum of the dimensions of the irreducible components through `x`.
* `topologicalKrullDimAt_eq_of_isPureDimensional`: if `X` is pure of dimension `d`, then
  `dim_x X = d` at every point.
* `topologicalKrullDimAt_eq_iSup_toNat_trdeg_residueField`: `dim_x X` is the supremum of
  `trdeg_k κ(ξ)` over the generic points `ξ` of the irreducible components through `x`.
* `coheight_add_height_eq_topologicalKrullDim`: for `X` irreducible, `codim x + dim {x}⁻ = dim X`.
* `height_eq_toNat_trdeg_residueField`: the height of `x` is `trdeg_k κ(x)`.
* `height_apply_eq_height_of_residueDegree_ne_zero`: a morphism over `k` preserves the height of
  a point with finite residue field extension.
* `height_apply_of_isOpenImmersion`: an open immersion into `X` preserves the height of points.
* `trdeg_residueField_lt_aleph0`: every residue field `κ(x)` has finite transcendence degree
  over `k`.
* `trdeg_residueField_eq_add_of_over`: for a scheme `F` over a field `K` whose structure
  morphism to `Spec k` factors through `Spec K ⟶ Spec k`,
  `trdeg_k κ(z) = trdeg_k K + trdeg_K κ(z)`.
* `AlgebraicGeometry.Scheme.Hom.trdeg_residueField_eq_of_isIso_residueFieldMap`: over any
  commutative ring `k`, a morphism over `Spec k` inducing an isomorphism `κ(f x) ≅ κ(x)` preserves
  the transcendence degree over `k` of the residue field.
* `finite_preimage_singleton_of_height_eq`: a fibre whose points all have the height of their
  image is finite.
* `exists_isFinite_morphismRestrict_of_height_add_one`: a proper dominant morphism from an
  irreducible scheme to a scheme of the same finite dimension is finite over a neighbourhood of
  every point of codimension one.

## References

* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0),
  [Tag 06RP](https://stacks.math.columbia.edu/tag/06RP) and
  [Tag 00P1](https://stacks.math.columbia.edu/tag/00P1) (dimension of finite type algebras over a
  field)
* [Stacks Project, Tag 02UP](https://stacks.math.columbia.edu/tag/02UP) (a proper morphism with
  a finite fibre is finite over a neighbourhood of its image)
* W. Fulton, *Intersection Theory*, 2nd ed., Section 1.4 (the pushforward of a principal divisor
  along a proper generically finite morphism is computed near points of codimension one)
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
  exact y.topologicalKrullDimAt_eq_height_add_ringKrullDim_quotient k

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
    obtain ⟨R, g, _, y, φ, _, rfl, hR⟩ := (X ↘ Spec (.of k)).exists_isOpenImmersion_finiteType x
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
      fun v ↦ hVZ ⟨v.val, v.property, rfl⟩).isInducing.topologicalKrullDim_le
  · -- A component `Z` through `x` meets every open neighbourhood `U` of `x` in a nonempty open
    -- part of `Z`, which has the dimension of `Z`.
    rw [← topologicalKrullDim_inter_eq_of_locallyOfFiniteType (X ↘ Spec (.of k)) hZ.1
      (isClosed_of_mem_irreducibleComponents Z hZ) U.property.1 ⟨x, hxZ, U.property.2⟩]
    exact (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le

include k in
/-- **Dimension formula.** On an irreducible scheme `X` locally of finite type over a field, the
codimension and the dimension of the closure of any point add up to the dimension of `X`:
`coheight x + height x = dim X`, where `height x = dim {x}⁻` for the specialization order. -/
theorem coheight_add_height_eq_topologicalKrullDim [IrreducibleSpace X] (x : X) :
    (Order.coheight x : WithBot ℕ∞) + Order.height x = topologicalKrullDim X := by
  -- `X` is its only irreducible component, so the local dimension at `x` is the dimension of `X`.
  have hx := topologicalKrullDimAt_eq_ringKrullDim_stalk_add_topologicalKrullDim_closure k x
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents k,
    irreducibleComponents_eq_singleton, iSup_singleton, iSup_pos (Set.mem_univ x),
    (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, ringKrullDim_stalk_eq_coheight,
    ← height_eq_topologicalKrullDim_closure_singleton] at hx
  exact hx.symm

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

/-- **Height of a point.** On a scheme `X` locally of finite type over a field `k`, the height of a
point `x` for the specialization order, that is the dimension of its closure, is the transcendence
degree of the residue field `κ(x)` over `k`. -/
theorem height_eq_toNat_trdeg_residueField (x : X) :
    Order.height x = (Algebra.trdeg k (X.residueField x)).toNat := by
  have h := (height_eq_topologicalKrullDim_closure_singleton x).trans
    (topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField k x)
  exact_mod_cast h

/-- **Points with finite residue extension have the same dimension.** Let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over a field `k`, and let `x ∈ X` be a point whose
residue field `κ(x)` is finite over `κ(f x)`, that is, `f.residueDegree x ≠ 0`. Then the closures
of `x` and of `f x` have the same dimension: both are the transcendence degree of `κ(x)` over `k`.
-/
theorem height_apply_eq_height_of_residueDegree_ne_zero {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] {x : X}
    (hx : f.residueDegree x ≠ 0) : Order.height (f x) = Order.height x := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k (Y.residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (f.residueFieldMap_algebraMap k x c).symm
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    (f.residueDegree_ne_zero_iff x).mp hx
  -- `κ(x)` is algebraic over `κ(f x)`, so both residue fields have the same transcendence degree
  -- over `k`.
  rw [height_eq_toNat_trdeg_residueField k, height_eq_toNat_trdeg_residueField k,
    ← trdeg_add_eq k (Y.residueField (f x)) (A := X.residueField x),
    trdeg_eq_zero (R := Y.residueField (f x)), add_zero]

include k in
/-- On a scheme locally of finite type over a field and pure of dimension `d`, the local
dimension at every point is `d`. -/
theorem topologicalKrullDimAt_eq_of_isPureDimensional {d : ℕ} (h : IsPureDimensional d X)
    (x : X) :
    topologicalKrullDimAt X x = d := by
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents k]
  refine le_antisymm (iSup₂_le fun Z hZ ↦ iSup_le fun _ ↦ (isPureDimensional_iff.mp h Z hZ).le) ?_
  exact le_iSup₂_of_le (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
    (le_iSup_of_le mem_irreducibleComponent (isPureDimensional_iff.mp h _
      (irreducibleComponent_mem_irreducibleComponents x)).ge)

include k in
/-- Over a field, an open immersion preserves the dimension of points: its residue degrees are
one, so a point and its image have residue fields of the same transcendence degree over `k`. No
structure over `k` is needed on the source, which is given the one induced from the target. -/
theorem height_apply_of_isOpenImmersion {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (u : U) : Order.height (j u) = Order.height u := by
  let : U.Over (Spec (.of k)) := ⟨j ≫ X ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ X ↘ Spec (.of k)))
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  exact height_apply_eq_height_of_residueDegree_ne_zero k j
    (by rw [Scheme.Hom.residueDegree_eq_one_of_surjectiveOnStalks]; exact one_ne_zero)

/-- **Fibres of equal height are finite.** Let `f : X ⟶ Y` be a quasi-compact morphism of schemes
over a field `k`, with `X` locally of finite type over `k`, and let `y ∈ Y` be such that every
point of the fibre over `y` has the height of `y`. Then the fibre is finite. -/
theorem finite_preimage_singleton_of_height_eq {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f] (y : Y)
    (h : ∀ x, f x = y → Order.height x = Order.height y) :
    (f ⁻¹' {y}).Finite := by
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of k)) := by
      rw [CategoryTheory.comp_over]; infer_instance
    exact locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  have : T1Space (f ⁻¹' {y}) := by
    refine t1Space_iff_specializes_imp_eq.2 fun a b hab ↦ Subtype.ext ?_
    have hab : (a : X) ⤳ b := Topology.IsInducing.subtypeVal.specializes_iff.2 hab
    by_contra hne
    -- `b` is a proper specialization of `a`, so its height is strictly smaller.
    have hlt : (b : X) < a := ⟨hab, fun hba ↦ hne (hab.antisymm hba).eq⟩
    have hb : Order.height (b : X) = Order.height y := h b b.property
    have ha : Order.height (a : X) = Order.height y := h a a.property
    have hfin : Order.height (b : X) < ⊤ := by
      rw [height_eq_toNat_trdeg_residueField k]
      exact ENat.natCast_lt_top _
    exact (Order.height_strictMono hlt hfin).ne (hb.trans ha.symm)
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
  have : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  have : IsNoetherian (f.fiber y) := {}
  have : T1Space (f.fiber y) := (f.fiberHomeo y).isEmbedding.t1Space
  have : Finite (f.fiber y) := TopologicalSpace.NoetherianSpace.finite_of_t1Space
  exact f.range_fiberι y ▸ Set.finite_range _

/-- **Proper generically finite morphisms are finite in codimension one.** Let `f : X ⟶ Y` be a
proper dominant morphism of schemes over a field `k`, with `X` irreducible and locally of
finite type over `k` (so `Y` is irreducible too), both of dimension `n + 1`, and let `y ∈ Y` be
a point of codimension one, that is, of height `n`. Then `f` is finite over an open neighbourhood
of `y` (Stacks, Tag 02UP, since the fibre over `y` is finite). -/
theorem exists_isFinite_morphismRestrict_of_height_add_one {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [IrreducibleSpace X] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsProper f] [IsDominant f] {n : ℕ}
    (hX : topologicalKrullDim X = n + 1) (hY : topologicalKrullDim Y = n + 1) {y : Y}
    (hy : Order.height y = n) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := by
  have : IrreducibleSpace Y := f.irreducibleSpace_of_isDominant
  have hgen : ∀ (Z : Scheme.{u}) [IrreducibleSpace Z], topologicalKrullDim Z = n + 1 →
      Order.height (genericPoint Z) = n + 1 := fun Z _ hZ ↦ by
    rw [← (genericPoint_spec Z).height_eq_topologicalKrullDim] at hZ
    exact_mod_cast hZ
  -- Every point `x` over `y` has height `n`: at least `n` since the closed map `f` does not
  -- increase heights, and less than `n + 1` since `x` is not the generic point of `X`, which maps
  -- to that of `Y`.
  refine exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y
    (finite_preimage_singleton_of_height_eq k f y fun x hx ↦ ?_)
  subst hx
  refine le_antisymm ?_ (f.isClosedMap.specializingMap.height_apply_le_height x)
  have hne : x ≠ genericPoint X := by
    rintro rfl
    have h := hgen Y hY
    rw [← f.genericPoint_eq_of_isDominant, hy] at h
    exact absurd h (by norm_cast; omega)
  have hspec := (genericPoint_spec X).specializes (Set.mem_univ x)
  have hlt : x < genericPoint X := ⟨hspec, fun h ↦ hne (h.antisymm hspec).eq⟩
  have := Order.height_strictMono hlt (by
    rw [height_eq_toNat_trdeg_residueField k]; exact ENat.natCast_lt_top _)
  rw [hgen X hX] at this
  rw [hy]
  exact Order.le_of_lt_add_one this

end AlgebraicGeometry

end TauCeti

namespace TauCeti.AlgebraicGeometry

open CategoryTheory

universe u

section ResidueFieldTrdeg

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- On a scheme locally of finite type over a field `k`, every residue field has finite
transcendence degree over `k`. -/
theorem trdeg_residueField_lt_aleph0 [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X) :
    Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 := by
  obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := (X ↘ Spec (.of k)).exists_isOpenImmersion_finiteType x
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k R := hR
  have := y.isPrime
  rw [(g.residueFieldAlgEquivOfIsOpenImmersion φ hφ y).trdeg_eq]
  have : Algebra.EssFiniteType k y.asIdeal.ResidueField := .comp k R _
  exact trdeg_lt_aleph0 k _

end ResidueFieldTrdeg

/-- **Additivity of transcendence degrees of residue fields.** Let `F` be a scheme over fields
`k` and `K`, with `K` a `k`-algebra, such that the structure morphism `F ⟶ Spec k` is the one to
`Spec K` followed by `Spec K ⟶ Spec k`. Then for every point `z` of `F`,
`trdeg_k κ(z) = trdeg_k K + trdeg_K κ(z)`. -/
theorem trdeg_residueField_eq_add_of_over (k K : Type u) [Field k] [Field K] [Algebra k K]
    {F : Scheme.{u}} [F.Over (Spec (.of k))] [F.Over (Spec (.of K))]
    (h : F ↘ Spec (.of K) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) = F ↘ Spec (.of k))
    (z : F) :
    Algebra.trdeg k (F.residueField z) =
      Algebra.trdeg k K + Algebra.trdeg K (F.residueField z) := by
  have : IsScalarTower k K (F.residueField z) := by
    refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
    simp only [Scheme.algebraMap_residueField_eq_residue_comp_baseRingToStalk, RingHom.comp_apply,
      Scheme.baseRingToStalk_apply, Scheme.Modules.baseRingToGlobalSections_apply, ← h,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    -- Both sides pull back `c` to global sections of `Spec K`, through `Spec k` or directly.
    exact congr(F.residue z (F.presheaf.germ ⊤ z trivial ((F ↘ Spec (.of K)).appTop
      ($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K))) c)))).symm
  exact (trdeg_add_eq k K).symm

/-- A morphism over `Spec k` inducing an isomorphism of residue fields at `x` preserves the
transcendence degree of the residue field over `k`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.trdeg_residueField_eq_of_isIso_residueFieldMap
    {k : Type u} [CommRing k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (x : X) [IsIso (f.residueFieldMap x)] :
    Algebra.trdeg k (X.residueField x) = Algebra.trdeg k (Y.residueField (f x)) := by
  let e : Y.residueField (f x) ≃+* X.residueField x :=
    (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv
  exact (AlgEquiv.ofRingEquiv (f := e) fun c ↦ f.residueFieldMap_algebraMap k x c).trdeg_eq.symm

end TauCeti.AlgebraicGeometry
