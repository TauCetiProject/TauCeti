/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# The Brauer correspondent of a block idempotent

For a subgroup `D` of `G` and `e ∈ R[G]`, the **Brauer correspondent** `brauerCorrespondent D e` is
the Brauer projection `Br_D(e) ∈ R[C_G(D)]`, read in `R[N_G(D)]` through the inclusion
`C_G(D) ≤ N_G(D)` (`TauCeti.brauerCorrespondent`). Its coefficient at `n ∈ N_G(D)` is the
coefficient of `e` at `n` when `n` centralizes `D`, and `0` otherwise; it vanishes exactly when
`Br_D(e)` does.

For a central idempotent `e` of `R[G]`, `G` finite, a `p`-subgroup `D` and `R` of
characteristic `p`, `brauerCorrespondent D e` is a central idempotent of `R[N_G(D)]`: it is
central because the coefficients of `e` are constant on `N_G(D)`-conjugacy classes and `C_G(D)` is
normal in `N_G(D)`, and idempotent because the Brauer projection is multiplicative on `R[G]^D`
(`TauCeti.brauerProjection_mul`). When `D` is a defect group of a block idempotent `e_B` it is
nonzero. That it is then a block idempotent of `R[N_G(D)]` with defect group `D`, the idempotent
of the Brauer correspondent of `B`, is Brauer's first main theorem, not proved here.

## Main definitions

* `TauCeti.brauerCorrespondent D`: the `R`-linear map `R[G] → R[N_G(D)]`, `e ↦ Br_D(e)`.

## Main results

* `TauCeti.coeff_brauerCorrespondent_of_mem`, `TauCeti.coeff_brauerCorrespondent_of_notMem`: its
  coefficients; `TauCeti.brauerCorrespondent_one`, `TauCeti.brauerCorrespondent_single_coe`,
  `TauCeti.brauerCorrespondent_single_of_mem`, `TauCeti.brauerCorrespondent_single_of_notMem`: its
  values at `1` and at basis elements.
* `TauCeti.brauerCorrespondent_eq_zero_iff`: it vanishes exactly when `Br_D(e)` does.
* `TauCeti.brauerCorrespondent_mul`: it is multiplicative on `R[G]^D` for a `p`-subgroup `D` in
  characteristic `p`.
* `TauCeti.brauerCorrespondent_mem_center`: it maps `R[G]^{N_G(D)}`, so in particular `Z(R[G])`,
  into `Z(R[N_G(D)])`.
* `TauCeti.isIdempotentElem_brauerCorrespondent`: it maps idempotents of `R[G]^D` to idempotents,
  for a `p`-subgroup `D` of a finite group in characteristic `p`;
  `TauCeti.IsBlockIdempotent.isIdempotentElem_brauerCorrespondent` states this for a block
  idempotent.
* `TauCeti.IsDefectGroup.brauerCorrespondent_ne_zero`: it is nonzero at a defect group.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.5, p. 243.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G : Type*} [CommSemiring R] [Group G]

/-- The **Brauer correspondent** of `e ∈ R[G]` at a subgroup `D`: the Brauer projection
`Br_D(e) ∈ R[C_G(D)]`, read in `R[N_G(D)]` through the inclusion `C_G(D) ≤ N_G(D)`. When `R` is a
field of characteristic `p`, `G` is finite and `D` is a defect group of a block idempotent `e_B`,
Brauer's first main theorem (not proved here) identifies it with the block idempotent of the
Brauer correspondent of the block. -/
noncomputable def brauerCorrespondent (D : Subgroup G) :
    MonoidAlgebra R G →ₗ[R] MonoidAlgebra R (Subgroup.normalizer (D : Set G)) :=
  (mapDomainAlgHom R R
      (Subgroup.inclusion (Subgroup.centralizer_le_normalizer (D : Set G)))).toLinearMap ∘ₗ
    brauerProjection D

/-- The Brauer correspondent is the image of the Brauer projection under the inclusion
`C_G(D) → N_G(D)`. -/
theorem brauerCorrespondent_apply (D : Subgroup G) (x : MonoidAlgebra R G) :
    brauerCorrespondent D x =
      mapDomainRingHom R (Subgroup.inclusion (Subgroup.centralizer_le_normalizer (D : Set G)))
        (brauerProjection D x) := by
  rw [brauerCorrespondent, LinearMap.comp_apply, AlgHom.toLinearMap_apply, mapDomainAlgHom_apply,
    mapDomainRingHom_apply]

/-- The coefficient of the Brauer correspondent at an element of `N_G(D)` centralizing `D` is the
coefficient of `x` there. -/
@[simp]
theorem coeff_brauerCorrespondent_of_mem {D : Subgroup G} (x : MonoidAlgebra R G)
    (n : Subgroup.normalizer (D : Set G)) (hn : (n : G) ∈ Subgroup.centralizer (D : Set G)) :
    (brauerCorrespondent D x).coeff n = x.coeff n := by
  have hincl : Subgroup.inclusion (Subgroup.centralizer_le_normalizer (D : Set G)) ⟨n, hn⟩ = n :=
    Subtype.ext (Subgroup.coe_inclusion _ _)
  rw [brauerCorrespondent_apply, mapDomainRingHom_apply, coeff_mapDomain, ← hincl,
    Finsupp.mapDomain_apply_of_injective (Subgroup.inclusion_injective _), coeff_brauerProjection,
    Subgroup.coe_inclusion]

/-- The coefficient of the Brauer correspondent at an element of `N_G(D)` not centralizing `D` is
`0`. -/
@[simp]
theorem coeff_brauerCorrespondent_of_notMem {D : Subgroup G} (x : MonoidAlgebra R G)
    (n : Subgroup.normalizer (D : Set G)) (hn : (n : G) ∉ Subgroup.centralizer (D : Set G)) :
    (brauerCorrespondent D x).coeff n = 0 := by
  rw [brauerCorrespondent_apply, mapDomainRingHom_apply, coeff_mapDomain]
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨c, rfl⟩
  exact hn c.property

/-- The Brauer correspondent of `1` is `1`, since `1 ∈ C_G(D)`. -/
@[simp]
theorem brauerCorrespondent_one (D : Subgroup G) :
    brauerCorrespondent D (1 : MonoidAlgebra R G) = 1 := by
  rw [brauerCorrespondent_apply, brauerProjection_one, map_one]

/-- The Brauer correspondent keeps a basis element `single c r` with `c ∈ C_G(D)`. -/
@[simp]
theorem brauerCorrespondent_single_coe (D : Subgroup G) (c : Subgroup.centralizer (D : Set G))
    (r : R) :
    brauerCorrespondent D (single (c : G) r) =
      single (Subgroup.inclusion (Subgroup.centralizer_le_normalizer (D : Set G)) c) r := by
  rw [brauerCorrespondent_apply, brauerProjection_single_coe, mapDomainRingHom_apply,
    mapDomain_single]

/-- The Brauer correspondent keeps a basis element `single g r` with `g ∈ C_G(D)`. -/
theorem brauerCorrespondent_single_of_mem (D : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.centralizer (D : Set G)) (r : R) :
    brauerCorrespondent D (single g r) =
      single ⟨g, Subgroup.centralizer_le_normalizer (D : Set G) hg⟩ r :=
  (brauerCorrespondent_single_coe D ⟨g, hg⟩ r).trans
    (congrArg (single · r) (Subtype.ext (Subgroup.coe_inclusion _ _)))

/-- The Brauer correspondent discards a basis element `single g r` with `g ∉ C_G(D)`. -/
theorem brauerCorrespondent_single_of_notMem (D : Subgroup G) {g : G}
    (hg : g ∉ Subgroup.centralizer (D : Set G)) (r : R) :
    brauerCorrespondent D (single g r) = 0 := by
  rw [brauerCorrespondent_apply, brauerProjection_single_of_notMem D hg, map_zero]

/-- The Brauer correspondent of `x` vanishes exactly when `Br_D(x)` does. -/
theorem brauerCorrespondent_eq_zero_iff {D : Subgroup G} {x : MonoidAlgebra R G} :
    brauerCorrespondent D x = 0 ↔ brauerProjection D x = 0 := by
  rw [brauerCorrespondent_apply, ← map_zero (mapDomainRingHom R
    (Subgroup.inclusion (Subgroup.centralizer_le_normalizer (D : Set G))))]
  exact (mapDomain_injective (Subgroup.inclusion_injective _)).eq_iff

/-- **The Brauer correspondent of an `N_G(D)`-invariant element is central.** For `z ∈ R[G]`
commuting with `N_G(D)`, for instance `z ∈ Z(R[G])` (`TauCeti.center_le_conjInvariants`),
`brauerCorrespondent D z` is central in `R[N_G(D)]`: its coefficients are constant on
`N_G(D)`-conjugacy classes, since those of `z` are and `C_G(D)` is normal in `N_G(D)`. -/
theorem brauerCorrespondent_mem_center (D : Subgroup G) {z : MonoidAlgebra R G}
    (hz : z ∈ conjInvariants R (Subgroup.normalizer (D : Set G))) :
    brauerCorrespondent D z ∈ Subalgebra.center R (MonoidAlgebra R (Subgroup.normalizer
      (D : Set G))) := by
  rw [← conjInvariants_top, mem_conjInvariants_iff_coeff]
  rw [mem_conjInvariants_iff_coeff] at hz
  intro h _ n
  have hnormal := (Subgroup.normal_subgroupOf_iff
    (Subgroup.centralizer_le_normalizer (D : Set G))).1 inferInstance
  by_cases hn : (n : G) ∈ Subgroup.centralizer (D : Set G)
  · rw [coeff_brauerCorrespondent_of_mem _ _ hn,
      coeff_brauerCorrespondent_of_mem _ _ (hnormal _ _ hn h.property)]
    exact hz h h.property n
  · have hn' : ((h * n * h⁻¹ : Subgroup.normalizer (D : Set G)) : G) ∉
        Subgroup.centralizer (D : Set G) := fun hc => hn <| by
      simpa [mul_assoc] using hnormal _ _ hc h⁻¹.property
    rw [coeff_brauerCorrespondent_of_notMem _ _ hn, coeff_brauerCorrespondent_of_notMem _ _ hn']

/-- **The Brauer correspondent is multiplicative on `R[G]^D`.** For a `p`-subgroup `D` of a
finite group `G` and `R` of characteristic `p`, `brauerCorrespondent D (x y)` is the product of
the Brauer correspondents of `x, y ∈ R[G]^D` (`TauCeti.brauerProjection_mul`). -/
theorem brauerCorrespondent_mul [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p] {D : Subgroup G}
    (hD : IsPGroup p D) {x y : MonoidAlgebra R G} (hx : x ∈ conjInvariants R D)
    (hy : y ∈ conjInvariants R D) :
    brauerCorrespondent D (x * y) = brauerCorrespondent D x * brauerCorrespondent D y := by
  simp only [brauerCorrespondent_apply, brauerProjection_mul hD hx hy, map_mul]

/-- For a `p`-subgroup `D` of a finite group `G` and `R` of characteristic `p`, the Brauer
correspondent of an idempotent of `R[G]^D` is an idempotent of `R[N_G(D)]`. -/
theorem isIdempotentElem_brauerCorrespondent [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p]
    {D : Subgroup G} (hD : IsPGroup p D) {x : MonoidAlgebra R G} (hx : x ∈ conjInvariants R D)
    (he : IsIdempotentElem x) : IsIdempotentElem (brauerCorrespondent D x) := by
  rw [IsIdempotentElem, ← brauerCorrespondent_mul hD hx hx, he.eq]

/-- **The Brauer correspondent of a block.** For a block idempotent `e_B` of `R[G]`, `R` of
characteristic `p`, and a `p`-subgroup `D` of the finite group `G`, for instance a defect group of
`e_B`, `brauerCorrespondent D e_B` is an idempotent of `R[N_G(D)]`. It is also central
(`TauCeti.brauerCorrespondent_mem_center`). -/
theorem IsBlockIdempotent.isIdempotentElem_brauerCorrespondent [Finite G] {p : ℕ} [Fact p.Prime]
    [CharP R p] {D : Subgroup G} {b : Subalgebra.center R (MonoidAlgebra R G)}
    (hb : IsBlockIdempotent b) (hD : IsPGroup p D) :
    IsIdempotentElem (brauerCorrespondent D (b : MonoidAlgebra R G)) :=
  TauCeti.isIdempotentElem_brauerCorrespondent hD (center_le_conjInvariants D b.property)
    hb.isIdempotentElem_val

/-- The Brauer correspondent of `e` at a defect group of `e` is nonzero. -/
theorem IsDefectGroup.brauerCorrespondent_ne_zero {p : ℕ} {e : MonoidAlgebra R G}
    {D : Subgroup G} (hD : IsDefectGroup R p e D) : brauerCorrespondent D e ≠ 0 :=
  brauerCorrespondent_eq_zero_iff.not.2 hD.brauerProjection_ne_zero

end TauCeti
