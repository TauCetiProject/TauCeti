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

For a subgroup `D` of `G` and a subgroup `H` with `C_G(D) ≤ H`, the **Brauer correspondent**
`brauerCorrespondent hCH e` of `e ∈ R[G]` is the Brauer projection `Br_D(e) ∈ R[C_G(D)]`, read in
`R[H]` through the inclusion `C_G(D) ≤ H` (`TauCeti.brauerCorrespondent`). The main case is
`H = N_G(D)`, through `Subgroup.centralizer_le_normalizer`. Its coefficient at `h ∈ H` is the
coefficient of `e` at `h` when `h` centralizes `D`, and `0` otherwise; it vanishes exactly when
`Br_D(e)` does.

For a central idempotent `e` of `R[G]`, `G` finite, a `p`-subgroup `D`, `R` of characteristic `p`
and `C_G(D) ≤ H ≤ N_G(D)`, `brauerCorrespondent hCH e` is a central idempotent of `R[H]`: it is
central because the coefficients of `e` are constant on `H`-conjugacy classes and `C_G(D)` is
normalized by `H`, and idempotent because the Brauer projection is multiplicative on `R[G]^D`
(`TauCeti.brauerProjection_mul`). On centres this is `TauCeti.centerBrauerCorrespondent`. When `D`
is a defect group of a block idempotent `e_B` it is nonzero. That at `H = N_G(D)` it is then a block
idempotent of `R[N_G(D)]` with defect group `D`, the idempotent of the Brauer correspondent of
`B`, is Brauer's first main theorem, not proved here.

## Main definitions

* `TauCeti.brauerCorrespondent hCH`: for `C_G(D) ≤ H`, the `R`-linear map `R[G] → R[H]`,
  `e ↦ Br_D(e)`.
* `TauCeti.centerBrauerCorrespondent hCH hHN`: for `C_G(D) ≤ H ≤ N_G(D)`, its restriction
  `Z(R[G]) →ₗ[R] Z(R[H])` to centres.

## Main results

* `TauCeti.coeff_brauerCorrespondent_of_mem`, `TauCeti.coeff_brauerCorrespondent_of_notMem`: its
  coefficients; `TauCeti.brauerCorrespondent_one`, `TauCeti.brauerCorrespondent_single_coe`,
  `TauCeti.brauerCorrespondent_single_of_mem`, `TauCeti.brauerCorrespondent_single_of_notMem`: its
  values at `1` and at basis elements.
* `TauCeti.brauerCorrespondent_eq_zero_iff`: it vanishes exactly when `Br_D(e)` does.
* `TauCeti.brauerCorrespondent_mul`: it is multiplicative on `R[G]^D` for a `p`-subgroup `D` in
  characteristic `p`.
* `TauCeti.brauerCorrespondent_mem_center`: for `H ≤ N_G(D)` it maps `R[G]^H`, so in particular
  `Z(R[G])`, into `Z(R[H])`.
* `TauCeti.isIdempotentElem_brauerCorrespondent`: it maps idempotents of `R[G]^D` to idempotents,
  for a `p`-subgroup `D` of a finite group in characteristic `p`;
  `TauCeti.IsBlockIdempotent.isIdempotentElem_brauerCorrespondent` states this for a block
  idempotent, and `TauCeti.isIdempotentElem_centerBrauerCorrespondent` on centres.
* `TauCeti.centerBrauerCorrespondent_one`, `TauCeti.centerBrauerCorrespondent_mul`: on centres it is
  unital, and multiplicative for a `p`-subgroup `D` in characteristic `p`.
* `TauCeti.IsDefectGroup.brauerCorrespondent_ne_zero`: it is nonzero at a defect group.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.5, p. 243.
* A. Martínez, *Modular representation theory of finite groups*, Theorem 4.5, p. 26.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G : Type*} [CommSemiring R] [Group G] {D H : Subgroup G}

/-- The **Brauer correspondent** of `e ∈ R[G]` at a subgroup `D`, for a subgroup `H` with
`C_G(D) ≤ H`: the Brauer projection `Br_D(e) ∈ R[C_G(D)]`, read in `R[H]` through the inclusion
`C_G(D) ≤ H`. The main case is `H = N_G(D)`. When `R` is a field of characteristic `p`, `G` is
finite and `D` is a defect group of a block idempotent `e_B`, Brauer's first main theorem (not
proved here) identifies it at `H = N_G(D)` with the block idempotent of the Brauer correspondent
of the block. -/
noncomputable def brauerCorrespondent (hCH : Subgroup.centralizer (D : Set G) ≤ H) :
    MonoidAlgebra R G →ₗ[R] MonoidAlgebra R H :=
  (mapDomainAlgHom R R (Subgroup.inclusion hCH)).toLinearMap ∘ₗ brauerProjection D

/-- The Brauer correspondent is the image of the Brauer projection under the inclusion
`C_G(D) → H`. -/
theorem brauerCorrespondent_apply (hCH : Subgroup.centralizer (D : Set G) ≤ H)
    (x : MonoidAlgebra R G) :
    brauerCorrespondent hCH x =
      mapDomainRingHom R (Subgroup.inclusion hCH) (brauerProjection D x) := by
  rw [brauerCorrespondent, LinearMap.comp_apply, AlgHom.toLinearMap_apply, mapDomainAlgHom_apply,
    mapDomainRingHom_apply]

/-- The coefficient of the Brauer correspondent at an element of `H` centralizing `D` is the
coefficient of `x` there. -/
@[simp]
theorem coeff_brauerCorrespondent_of_mem {hCH : Subgroup.centralizer (D : Set G) ≤ H}
    (x : MonoidAlgebra R G) (h : H) (hh : (h : G) ∈ Subgroup.centralizer (D : Set G)) :
    (brauerCorrespondent hCH x).coeff h = x.coeff h := by
  have hincl : Subgroup.inclusion hCH ⟨h, hh⟩ = h := Subtype.ext (Subgroup.coe_inclusion _ _)
  rw [brauerCorrespondent_apply, mapDomainRingHom_apply, coeff_mapDomain, ← hincl,
    Finsupp.mapDomain_apply_of_injective (Subgroup.inclusion_injective _), coeff_brauerProjection,
    Subgroup.coe_inclusion]

/-- The coefficient of the Brauer correspondent at an element of `H` not centralizing `D` is
`0`. -/
@[simp]
theorem coeff_brauerCorrespondent_of_notMem {hCH : Subgroup.centralizer (D : Set G) ≤ H}
    (x : MonoidAlgebra R G) (h : H) (hh : (h : G) ∉ Subgroup.centralizer (D : Set G)) :
    (brauerCorrespondent hCH x).coeff h = 0 := by
  rw [brauerCorrespondent_apply, mapDomainRingHom_apply, coeff_mapDomain]
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨c, rfl⟩
  exact hh c.property

/-- The Brauer correspondent of `1` is `1`, since `1 ∈ C_G(D)`. -/
@[simp]
theorem brauerCorrespondent_one (hCH : Subgroup.centralizer (D : Set G) ≤ H) :
    brauerCorrespondent hCH (1 : MonoidAlgebra R G) = 1 := by
  rw [brauerCorrespondent_apply, brauerProjection_one, map_one]

/-- The Brauer correspondent keeps a basis element `single c r` with `c ∈ C_G(D)`. -/
@[simp]
theorem brauerCorrespondent_single_coe (hCH : Subgroup.centralizer (D : Set G) ≤ H)
    (c : Subgroup.centralizer (D : Set G)) (r : R) :
    brauerCorrespondent hCH (single (c : G) r) = single (Subgroup.inclusion hCH c) r := by
  rw [brauerCorrespondent_apply, brauerProjection_single_coe, mapDomainRingHom_apply,
    mapDomain_single]

/-- The Brauer correspondent keeps a basis element `single g r` with `g ∈ C_G(D)`. -/
theorem brauerCorrespondent_single_of_mem (hCH : Subgroup.centralizer (D : Set G) ≤ H) {g : G}
    (hg : g ∈ Subgroup.centralizer (D : Set G)) (r : R) :
    brauerCorrespondent hCH (single g r) = single ⟨g, hCH hg⟩ r :=
  (brauerCorrespondent_single_coe hCH ⟨g, hg⟩ r).trans
    (congrArg (single · r) (Subtype.ext (Subgroup.coe_inclusion _ _)))

/-- The Brauer correspondent discards a basis element `single g r` with `g ∉ C_G(D)`. -/
theorem brauerCorrespondent_single_of_notMem (hCH : Subgroup.centralizer (D : Set G) ≤ H) {g : G}
    (hg : g ∉ Subgroup.centralizer (D : Set G)) (r : R) :
    brauerCorrespondent hCH (single g r) = 0 := by
  rw [brauerCorrespondent_apply, brauerProjection_single_of_notMem D hg, map_zero]

/-- The Brauer correspondent of `x` vanishes exactly when `Br_D(x)` does. -/
theorem brauerCorrespondent_eq_zero_iff {hCH : Subgroup.centralizer (D : Set G) ≤ H}
    {x : MonoidAlgebra R G} : brauerCorrespondent hCH x = 0 ↔ brauerProjection D x = 0 := by
  rw [brauerCorrespondent_apply, ← map_zero (mapDomainRingHom R (Subgroup.inclusion hCH))]
  exact (mapDomain_injective (Subgroup.inclusion_injective _)).eq_iff

/-- **The Brauer correspondent of an `H`-invariant element is central.** For
`C_G(D) ≤ H ≤ N_G(D)` and `z ∈ R[G]` commuting with `H`, for instance `z ∈ Z(R[G])`
(`TauCeti.center_le_conjInvariants`), `brauerCorrespondent hCH z` is central in `R[H]`: its
coefficients are constant on `H`-conjugacy classes, since those of `z` are and `C_G(D)` is
normalized by `H`. -/
theorem brauerCorrespondent_mem_center (hCH : Subgroup.centralizer (D : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (D : Set G)) {z : MonoidAlgebra R G}
    (hz : z ∈ conjInvariants R H) :
    brauerCorrespondent hCH z ∈ Subalgebra.center R (MonoidAlgebra R H) := by
  rw [← conjInvariants_top, mem_conjInvariants_iff_coeff]
  rw [mem_conjInvariants_iff_coeff] at hz
  intro h _ n
  have hnormal := (Subgroup.normal_subgroupOf_iff
    (Subgroup.centralizer_le_normalizer (D : Set G))).1 inferInstance
  by_cases hn : (n : G) ∈ Subgroup.centralizer (D : Set G)
  · rw [coeff_brauerCorrespondent_of_mem _ _ hn,
      coeff_brauerCorrespondent_of_mem _ _ (hnormal _ _ hn (hHN h.property))]
    exact hz h h.property n
  · have hn' : ((h * n * h⁻¹ : H) : G) ∉ Subgroup.centralizer (D : Set G) := fun hc => hn <| by
      simpa [mul_assoc] using hnormal _ _ hc (hHN h⁻¹.property)
    rw [coeff_brauerCorrespondent_of_notMem _ _ hn, coeff_brauerCorrespondent_of_notMem _ _ hn']

/-- **The Brauer correspondent is multiplicative on `R[G]^D`.** For a `p`-subgroup `D` of a
finite group `G` and `R` of characteristic `p`, `brauerCorrespondent hCH (x y)` is the product of
the Brauer correspondents of `x, y ∈ R[G]^D` (`TauCeti.brauerProjection_mul`). -/
theorem brauerCorrespondent_mul [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p]
    (hCH : Subgroup.centralizer (D : Set G) ≤ H) (hD : IsPGroup p D) {x y : MonoidAlgebra R G}
    (hx : x ∈ conjInvariants R D) (hy : y ∈ conjInvariants R D) :
    brauerCorrespondent hCH (x * y) = brauerCorrespondent hCH x * brauerCorrespondent hCH y := by
  simp only [brauerCorrespondent_apply, brauerProjection_mul hD hx hy, map_mul]

/-- For a `p`-subgroup `D` of a finite group `G` and `R` of characteristic `p`, the Brauer
correspondent of an idempotent of `R[G]^D` is an idempotent of `R[H]`. -/
theorem isIdempotentElem_brauerCorrespondent [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p]
    (hCH : Subgroup.centralizer (D : Set G) ≤ H) (hD : IsPGroup p D) {x : MonoidAlgebra R G}
    (hx : x ∈ conjInvariants R D) (he : IsIdempotentElem x) :
    IsIdempotentElem (brauerCorrespondent hCH x) := by
  rw [IsIdempotentElem, ← brauerCorrespondent_mul hCH hD hx hx, he.eq]

/-- **The Brauer correspondent of a block.** For a block idempotent `e_B` of `R[G]`, `R` of
characteristic `p`, and a `p`-subgroup `D` of the finite group `G`, for instance a defect group of
`e_B`, `brauerCorrespondent hCH e_B` is an idempotent of `R[H]`. It is also central for
`H ≤ N_G(D)` (`TauCeti.brauerCorrespondent_mem_center`). -/
theorem IsBlockIdempotent.isIdempotentElem_brauerCorrespondent [Finite G] {p : ℕ} [Fact p.Prime]
    [CharP R p] (hCH : Subgroup.centralizer (D : Set G) ≤ H)
    {b : Subalgebra.center R (MonoidAlgebra R G)} (hb : IsBlockIdempotent b) (hD : IsPGroup p D) :
    IsIdempotentElem (brauerCorrespondent hCH (b : MonoidAlgebra R G)) :=
  TauCeti.isIdempotentElem_brauerCorrespondent hCH hD (center_le_conjInvariants D b.property)
    hb.isIdempotentElem_val

/-- The Brauer correspondent of `e` at a defect group of `e` is nonzero. -/
theorem IsDefectGroup.brauerCorrespondent_ne_zero {p : ℕ} {e : MonoidAlgebra R G}
    (hCH : Subgroup.centralizer (D : Set G) ≤ H) (hD : IsDefectGroup R p e D) :
    brauerCorrespondent hCH e ≠ 0 :=
  brauerCorrespondent_eq_zero_iff.not.2 hD.brauerProjection_ne_zero

/-- The **Brauer correspondent on centres** (Martínez, Theorem 4.5, p. 26): for
`C_G(D) ≤ H ≤ N_G(D)`, the `R`-linear map `Z(R[G]) → Z(R[H])`, `z ↦ Br_D(z)`, with the
coefficients of `z` on `C_G(D)` and `0` elsewhere (`TauCeti.brauerCorrespondent_mem_center`). -/
noncomputable def centerBrauerCorrespondent (hCH : Subgroup.centralizer (D : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (D : Set G)) :
    Subalgebra.center R (MonoidAlgebra R G) →ₗ[R] Subalgebra.center R (MonoidAlgebra R H) where
  toFun z := ⟨brauerCorrespondent hCH (z : MonoidAlgebra R G),
    brauerCorrespondent_mem_center hCH hHN (center_le_conjInvariants H z.property)⟩
  map_add' z w := Subtype.ext (map_add (brauerCorrespondent hCH) (z : MonoidAlgebra R G) w)
  map_smul' c z := Subtype.ext (map_smul (brauerCorrespondent hCH) c (z : MonoidAlgebra R G))

/-- `centerBrauerCorrespondent hCH hHN z` is the Brauer correspondent of `z`. -/
@[simp]
theorem coe_centerBrauerCorrespondent (hCH : Subgroup.centralizer (D : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (D : Set G)) (z : Subalgebra.center R (MonoidAlgebra R G)) :
    (centerBrauerCorrespondent hCH hHN z : MonoidAlgebra R H) =
      brauerCorrespondent hCH (z : MonoidAlgebra R G) :=
  (rfl)

/-- The Brauer correspondent on centres sends `1` to `1`. -/
@[simp]
theorem centerBrauerCorrespondent_one (hCH : Subgroup.centralizer (D : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (D : Set G)) :
    centerBrauerCorrespondent hCH hHN (1 : Subalgebra.center R (MonoidAlgebra R G)) = 1 :=
  Subtype.ext (brauerCorrespondent_one hCH)

/-- For a `p`-subgroup `D` of a finite group `G` and `R` of characteristic `p`, the Brauer
correspondent on centres is multiplicative (`TauCeti.brauerCorrespondent_mul`). -/
theorem centerBrauerCorrespondent_mul [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p]
    (hCH : Subgroup.centralizer (D : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (D : Set G))
    (hD : IsPGroup p D) (z w : Subalgebra.center R (MonoidAlgebra R G)) :
    centerBrauerCorrespondent hCH hHN (z * w) =
      centerBrauerCorrespondent hCH hHN z * centerBrauerCorrespondent hCH hHN w :=
  Subtype.ext (brauerCorrespondent_mul hCH hD (center_le_conjInvariants D z.property)
    (center_le_conjInvariants D w.property))

/-- For a `p`-subgroup `D` of a finite group `G` and `R` of characteristic `p`, the Brauer
correspondent on centres maps idempotents to idempotents. -/
theorem isIdempotentElem_centerBrauerCorrespondent [Finite G] {p : ℕ} [Fact p.Prime] [CharP R p]
    (hCH : Subgroup.centralizer (D : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (D : Set G))
    (hD : IsPGroup p D) {e : Subalgebra.center R (MonoidAlgebra R G)} (he : IsIdempotentElem e) :
    IsIdempotentElem (centerBrauerCorrespondent hCH hHN e) := by
  rw [IsIdempotentElem, ← centerBrauerCorrespondent_mul hCH hHN hD, he.eq]

end TauCeti
