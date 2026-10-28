/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
public import TauCeti.RingTheory.KrullDimension.FiniteType

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

/-- An open immersion `g : Spec A ⟶ X` over `Spec k` identifies the residue field of `X` at `g y`
with the residue field of the prime `y` of `A`, as `k`-algebras; so the two have the same
transcendence degree over `k`. -/
private lemma trdeg_residueField_eq_of_isOpenImmersion {R : CommRingCat.{u}} (g : Spec R ⟶ X)
    [IsOpenImmersion g] (φ : CommRingCat.of k ⟶ R) (hφ : Spec.map φ = g ≫ X ↘ Spec (.of k))
    (y : Spec R) :
    letI := φ.hom.toAlgebra
    haveI := y.isPrime
    Algebra.trdeg k (X.residueField (g y)) = Algebra.trdeg k y.asIdeal.ResidueField := by
  let := φ.hom.toAlgebra
  have := y.isPrime
  let e : X.residueField (g y) ≅ .of y.asIdeal.ResidueField :=
    asIso (g.residueFieldMap y) ≪≫ Scheme.Spec.residueFieldIso R y
  -- On `k`, the composite `k → Γ(X) → κ(g y) → κ(y)` is `k → Γ(Spec R) → κ(y)` by naturality of
  -- evaluation at a point, and the latter is the algebra map `k → R → κ(y)`. The two steps are
  -- glued by `congrArg` rather than `rw`: goals mentioning `y.asIdeal` for `y : Spec R` are not
  -- type-correct at the transparency `rw` uses for its motive.
  have h₁ : (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫ X.Γevaluation (g y) ≫
      g.residueFieldMap y = φ ≫ (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation y := by
    rw [Scheme.Γevaluation_naturality, ← Scheme.Hom.comp_appTop_assoc, ← hφ,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  have h₂ : ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation y) ≫
      (Scheme.Spec.residueFieldIso R y).hom =
        CommRingCat.ofHom (algebraMap R y.asIdeal.ResidueField) :=
    ((Iso.comp_inv_eq _).mp (Scheme.Spec.algebraMap_residueFieldIso_inv R y)).symm
  have he : ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫ X.Γevaluation (g y) ≫
      g.residueFieldMap y) ≫ (Scheme.Spec.residueFieldIso R y).hom =
        φ ≫ CommRingCat.ofHom (algebraMap R y.asIdeal.ResidueField) :=
    (congrArg (· ≫ (Scheme.Spec.residueFieldIso R y).hom) h₁).trans
      ((Category.assoc _ _ _).trans (congrArg (φ ≫ ·) h₂))
  refine (AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun c ↦ ?_).trdeg_eq
  have hc : algebraMap k (X.residueField (g y)) c =
      X.Γevaluation (g y) ((X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)) := by
    rw [Scheme.algebraMap_residueField_eq_residue_comp_baseRingToStalk, RingHom.comp_apply,
      Scheme.residue_baseRingToStalk, Scheme.Modules.baseRingToGlobalSections_apply]
  refine (congrArg e.commRingCatIsoToRingEquiv hc).trans ?_
  refine congr($he c).trans ?_
  exact (IsScalarTower.algebraMap_apply k R y.asIdeal.ResidueField c).symm

variable [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- Every point of a scheme locally of finite type over `k` lies in the image of an affine open
immersion `Spec A ⟶ X` with `A` a finitely generated `k`-algebra, the structure of `k`-algebra
being the one induced by the structure morphism. -/
private lemma exists_isOpenImmersion_finiteType (x : X) :
    ∃ (R : CommRingCat.{u}) (g : Spec R ⟶ X) (_ : IsOpenImmersion g) (y : Spec R)
      (φ : CommRingCat.of k ⟶ R) (_ : Spec.map φ = g ≫ X ↘ Spec (.of k)),
      g y = x ∧ letI := φ.hom.toAlgebra; Algebra.FiniteType k R := by
  obtain ⟨R, g, _, ⟨y, rfl⟩, -⟩ :=
    X.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) (by simp)
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = g ≫ X ↘ Spec (.of k) := ⟨_, Spec.map_preimage _⟩
  let := φ.hom.toAlgebra
  exact ⟨R, g, inferInstance, y, φ, hφ, rfl,
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)⟩

/-- **Dimension of a point closure.** On a scheme `X` locally of finite type over a field `k`, the
closure of a point `x` has dimension the transcendence degree of the residue field `κ(x)`
over `k`. -/
theorem topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) = (Algebra.trdeg k (X.residueField x)).toNat := by
  obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := exists_isOpenImmersion_finiteType k x
  let := φ.hom.toAlgebra
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
          trdeg_residueField_eq_of_isOpenImmersion k g φ hφ y]

/-- **Local dimension via the stalk.** On a scheme `X` locally of finite type over a field `k`, the
local Krull dimension at a point `x` is the dimension of the local ring `O_{X,x}` plus the
transcendence degree of the residue field `κ(x)` over `k`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_stalk_add_toNat_trdeg_residueField (x : X) :
    topologicalKrullDimAt X x =
      ringKrullDim (X.presheaf.stalk x) + (Algebra.trdeg k (X.residueField x)).toNat := by
  obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := exists_isOpenImmersion_finiteType k x
  let := φ.hom.toAlgebra
  -- The chart preserves local dimension, identifies `O_{X,g y}` with `R_y` (of dimension
  -- `ht y`) and `κ(g y)` with `κ(y)`; then apply the affine formula `ht y + dim (R ⧸ y)`.
  rw [← g.isOpenEmbedding.topologicalKrullDimAt_eq, ringKrullDim_stalk_eq_coheight,
    coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight,
    trdeg_residueField_eq_of_isOpenImmersion k g φ hφ y]
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
    obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := exists_isOpenImmersion_finiteType k x
    let := φ.hom.toAlgebra
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
