/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.FundamentalGroup
public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.AlgebraicGeometry.Scheme.SpecAlgHom
public import TauCeti.FieldTheory.Galois.Restriction

/-!
# The image of the fundamental group of a field extension

Let `K → L → Ω` be fields with `Ω` separably closed and Galois over `K` (hence over `L`). The
homomorphism of étale fundamental groups `π₁(Spec L, x) → π₁(Spec K, x)` induced by
`Spec L ⟶ Spec K` is restriction of scalars `Gal(Ω/L) → Gal(Ω/K)`
(`TauCeti.FiniteEtaleScheme.mapAutFiber_toAutContinuousMulEquiv`). So it is injective
(`TauCeti.FiniteEtaleScheme.mapAutFiber_spec_injective`), its image consists of the loops given by
the automorphisms of `Ω` over `K` that fix `L`
(`TauCeti.FiniteEtaleScheme.mem_range_mapAutFiber_spec_iff`), that is, it is the image of the
subgroup `TauCeti.embeddingSubgroup K L Ω` fixing `L`
(`TauCeti.FiniteEtaleScheme.range_mapAutFiber_spec`), and by the Galois correspondence
(`TauCeti.index_embeddingSubgroup`) this image has index `[L : K]`
(`TauCeti.FiniteEtaleScheme.index_range_mapAutFiber_spec`). In particular the map is surjective
exactly when `[L : K] = 1`
(`TauCeti.FiniteEtaleScheme.mapAutFiber_spec_surjective_iff_finrank_eq_one`).

## Main results

* `TauCeti.FiniteEtaleScheme.mapAutFiber_spec_injective`: the map is injective.
* `TauCeti.FiniteEtaleScheme.mem_range_mapAutFiber_spec_iff`: membership in its image.
* `TauCeti.FiniteEtaleScheme.range_mapAutFiber_spec`: its image is the fixing subgroup of `L`.
* `TauCeti.FiniteEtaleScheme.index_range_mapAutFiber_spec`: the image has index `[L : K]`.
* `TauCeti.FiniteEtaleScheme.mapAutFiber_spec_surjective_iff_finrank_eq_one`: the map is
  surjective exactly when `[L : K] = 1`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, Proposition 8.1.
-/

public section

open CategoryTheory AlgebraicGeometry PreGaloisCategory

universe u

namespace TauCeti.FiniteEtaleScheme

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  (L : Type u) [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsSepClosed Ω] [IsGalois K Ω]

/-- **The map of fundamental groups of a field extension is injective**, since restriction of
scalars `Gal(Ω/L) → Gal(Ω/K)` is. -/
theorem mapAutFiber_spec_injective :
    Function.Injective (mapAutFiber (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.algebraMap_comp_algebraMap K L Ω)) := by
  have := IsGalois.tower_top_of_isGalois K L Ω
  intro a b hab
  obtain ⟨σ, rfl⟩ := (toAutContinuousMulEquiv _ Gal(Ω/L)).surjective a
  obtain ⟨τ, rfl⟩ := (toAutContinuousMulEquiv _ Gal(Ω/L)).surjective b
  rw [mapAutFiber_toAutContinuousMulEquiv, mapAutFiber_toAutContinuousMulEquiv] at hab
  rw [AlgEquiv.restrictScalars_injective K ((toAutContinuousMulEquiv _ Gal(Ω/K)).injective hab)]

/-- **The image of the map of fundamental groups of a field extension is the fixing subgroup of
`L`**: it is the image in `π₁(Spec K, x)` of `TauCeti.embeddingSubgroup K L Ω`, the subgroup of
`Gal(Ω/K)` fixing `L`, since the map is restriction of scalars `Gal(Ω/L) → Gal(Ω/K)`. -/
theorem range_mapAutFiber_spec :
    (mapAutFiber (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.algebraMap_comp_algebraMap K L Ω)).toMonoidHom.range =
      (embeddingSubgroup K L Ω).map
        (toAutContinuousMulEquiv _ Gal(Ω/K)).toMulEquiv.toMonoidHom := by
  have := IsGalois.tower_top_of_isGalois K L Ω
  rw [← range_restrictScalarsHom_eq_embeddingSubgroup K L Ω, ← MonoidHom.range_comp]
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨τ, rfl⟩ := (toAutContinuousMulEquiv _ Gal(Ω/L)).surjective a
    exact ⟨τ, (mapAutFiber_toAutContinuousMulEquiv K Ω L
      (Spec.algebraMap_comp_algebraMap K L Ω) τ).symm⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨toAutContinuousMulEquiv _ Gal(Ω/L) τ, mapAutFiber_toAutContinuousMulEquiv K Ω L
      (Spec.algebraMap_comp_algebraMap K L Ω) τ⟩

/-- **The image of the map of fundamental groups of a field extension**: a loop of `π₁(Spec K, x)`
lies in the image of `π₁(Spec L, x)` exactly when the automorphism of `Ω` over `K` it comes from
fixes `L`. -/
theorem mem_range_mapAutFiber_spec_iff
    (g : Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))) :
    g ∈ (mapAutFiber (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (Spec.algebraMap_comp_algebraMap K L Ω)).toMonoidHom.range ↔ ∀ l : L,
      (toAutContinuousMulEquiv _ Gal(Ω/K)).symm g (algebraMap L Ω l) = algebraMap L Ω l := by
  rw [range_mapAutFiber_spec, Subgroup.mem_map_equiv, mem_embeddingSubgroup_iff]
  -- `ContinuousMulEquiv.symm` is built from `MulEquiv.symm`, so the two inverses agree.
  rfl

/-- **The image of the map of fundamental groups of a field extension has index `[L : K]`**, by
the Galois correspondence for `Ω/K` (infinite `L/K` gives `0` on both sides). -/
theorem index_range_mapAutFiber_spec :
    (mapAutFiber (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.algebraMap_comp_algebraMap K L Ω)).toMonoidHom.range.index =
        Module.finrank K L := by
  rw [range_mapAutFiber_spec,
    Subgroup.index_map_of_bijective (toAutContinuousMulEquiv _ Gal(Ω/K)).toMulEquiv.bijective,
    index_embeddingSubgroup]

/-- **The map of fundamental groups of a field extension is surjective exactly when the extension
is trivial**, `[L : K] = 1` (an infinite extension has `Module.finrank K L = 0`). -/
theorem mapAutFiber_spec_surjective_iff_finrank_eq_one :
    Function.Surjective (mapAutFiber (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.algebraMap_comp_algebraMap K L Ω)) ↔ Module.finrank K L = 1 := by
  rw [← index_range_mapAutFiber_spec K Ω L, Subgroup.index_eq_one, MonoidHom.range_eq_top,
    ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass]

end TauCeti.FiniteEtaleScheme
