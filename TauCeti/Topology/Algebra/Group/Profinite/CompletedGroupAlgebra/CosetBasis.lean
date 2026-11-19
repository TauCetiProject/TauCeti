/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Map
import TauCeti.GroupTheory.Index.Map

/-!
# Completed group algebras are free over open subgroups

Let `H` be an open subgroup of finite index of a topological group `Γ`, for instance an open
subgroup of a profinite group. The inclusion `H → Γ` induces the algebra map
`ι : R[[H]] → R[[Γ]]`, through which `R[[Γ]]` is a left `R[[H]]`-module. This file proves that it
is free on any set of representatives of the right cosets `H g`. Such a set is written
`(s q)⁻¹`, for a representative `s q` of each left coset `q ∈ Γ ⧸ H`, and every `x ∈ R[[Γ]]` is
uniquely a sum

```text
x = ∑ q, ι (a q) * (s q)⁻¹,      a q ∈ R[[H]],
```

so the rank is the index `[Γ : H] = Nat.card (Γ ⧸ H)`. For the profinite group `Γ = ℤ_p` and
`H = pℤ_p` one may take the basis `1, γ, …, γ ^ (p - 1)` for a topological generator `γ`.

The coordinates are read off by the restriction `restrict R hH : R[[Γ]] → R[[H]]` to the subgroup
`H`. Viewing `R[[Γ]]` as measures on `Γ`, it restricts a measure to the clopen subset `H`; at the
level of an open normal subgroup `U ≤ H` of `Γ` it keeps the coefficients of `R[Γ ⧸ U]` on the
subgroup `H ⧸ U` (`proj_restrict`). It is left `R[[H]]`-linear (`restrict_map_mul`), a retraction
of `ι` (`restrict_map`), and sends a group element to itself or to zero according as it lies in
`H` or not (`restrict_of_of_mem`, `restrict_of_of_notMem`). The coordinate of `x` at the coset `q`
is `restrict R hH (x * s q)` (`basisCosets_repr_apply`).

The open normal subgroups of `H` do not come from `Γ`, so the levels of `R[[H]]` and of `R[[Γ]]`
are compared through the normal core in `Γ` of an open normal subgroup of `H`. Since `H` has
finite index this core is open (`Subgroup.isOpen_normalCore_of_finiteIndex_normalizer`), so the
open normal subgroups of `Γ` contained in `H` are cofinal among those of `H`; no compactness is
used. Freeness then makes finite generation of a module over `R[[Γ]]` equivalent to its finite
generation over `R[[H]]` (`module_finite_iff_of_isOpen`).

The coefficient ring `R` is any commutative ring, so this covers the Iwasawa algebras `ℤ_p[[Γ]]`
and `𝒪[[Γ]]` and the residual algebras `𝔽_p[[Γ]]` and `k[[Γ]]` alike.

The formal model for the inclusion-induced scalar action and inverse-representative convention
is the discrete coset basis `TauCeti.MonoidAlgebra.basisCosets` in
`TauCeti/Algebra/MonoidAlgebra/CosetBasis.lean`.

## Main definitions

* `TauCeti.completedGroupAlgebra.restrict R hH`: the restriction `R[[Γ]] →ₗ[R] R[[H]]` to an open
  subgroup `H` of finite index.
* `TauCeti.completedGroupAlgebra.basisCosets R hH s hs`: the basis of `R[[Γ]]` over `R[[H]]` given
  by the inverses `(s q)⁻¹` of representatives `s q` of the left cosets `q ∈ Γ ⧸ H`.

## Main results

* `TauCeti.completedGroupAlgebra.proj_restrict`: the levelwise description of `restrict`.
* `TauCeti.completedGroupAlgebra.restrict_map_mul`, `TauCeti.completedGroupAlgebra.restrict_map`:
  `restrict` is left `R[[H]]`-linear and a retraction of the inclusion.
* `TauCeti.completedGroupAlgebra.restrict_of_of_mem`,
  `TauCeti.completedGroupAlgebra.restrict_of_of_notMem`: `restrict` on group elements.
* `TauCeti.completedGroupAlgebra.basisCosets_apply`,
  `TauCeti.completedGroupAlgebra.basisCosets_repr_apply`: the basis vectors and the coordinates.
* `TauCeti.completedGroupAlgebra.module_finite_iff_of_isOpen`: a module over `R[[Γ]]` is finitely
  generated over `R[[H]]` if and only if it is finitely generated over `R[[Γ]]`.

## References

* M. Lazard, *Groupes analytiques `p`-adiques*, Publ. Math. IHÉS 26 (1965), Chap. II, (2.2.7).
* J. Coates, T. Fukaya, K. Kato, R. Sujatha and O. Venjakob, *The `GL₂` main conjecture for
  elliptic curves without complex multiplication*, Publ. Math. IHÉS 101 (2005), §2.
-/

public section

namespace TauCeti

universe u v

variable (R : Type u) [CommRing R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]

namespace completedGroupAlgebra

section Levels

variable {H : Subgroup Γ}

/-- The map `H ⧸ (U ⊓ H) → Γ ⧸ U` induced by the inclusion of `H`, at an open normal subgroup `U`
of `Γ`. -/
private noncomputable def levelMap (U : OpenNormalSubgroup Γ) :
    H ⧸ (U.comap H.subtype continuous_subtype_val).toSubgroup →* Γ ⧸ U.toSubgroup :=
  QuotientGroup.map _ _ H.subtype (U.toSubgroup_comap _ _).le

private theorem levelMap_mk (U : OpenNormalSubgroup Γ) (h : H) :
    levelMap U (h : H ⧸ (U.comap H.subtype continuous_subtype_val).toSubgroup) =
      ((h : Γ) : Γ ⧸ U.toSubgroup) := by
  rw [levelMap, QuotientGroup.map_mk, Subgroup.coe_subtype]

private theorem levelMap_injective (U : OpenNormalSubgroup Γ) :
    Function.Injective (levelMap (H := H) U) :=
  (QuotientGroup.map_injective_iff _ U.toSubgroup H.subtype _).mpr (U.toSubgroup_comap _ _).ge

/-- When `U ≤ H`, the class of `γ` modulo `U` comes from `H` exactly when `γ ∈ H`. -/
private theorem mk_mem_range_levelMap_iff {U : OpenNormalSubgroup Γ} (hU : U.toSubgroup ≤ H)
    (γ : Γ) : (γ : Γ ⧸ U.toSubgroup) ∈ Set.range (levelMap (H := H) U) ↔ γ ∈ H := by
  refine ⟨fun ⟨q, hq⟩ ↦ ?_, fun hγ ↦ ⟨((⟨γ, hγ⟩ : H) : H ⧸ _), levelMap_mk U _⟩⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  rw [levelMap_mk, QuotientGroup.eq] at hq
  simpa using H.mul_mem h.2 (hU hq)

/-- The restriction `R[Γ ⧸ U] → R[H ⧸ (U ⊓ H)]` of coefficients to the classes of elements
of `H`. -/
private noncomputable def levelRes (U : OpenNormalSubgroup Γ) :
    MonoidAlgebra R (Γ ⧸ U.toSubgroup) →+
      MonoidAlgebra R (H ⧸ (U.comap H.subtype continuous_subtype_val).toSubgroup) :=
  MonoidAlgebra.comapDomainAddMonoidHom (levelMap U) (levelMap_injective U)

private theorem levelRes_apply (U : OpenNormalSubgroup Γ) (z : MonoidAlgebra R (Γ ⧸ U.toSubgroup)) :
    levelRes R (H := H) U z = MonoidAlgebra.comapDomain (levelMap U) (levelMap_injective U) z :=
  (rfl)

private theorem levelRes_smul (U : OpenNormalSubgroup Γ) (r : R)
    (z : MonoidAlgebra R (Γ ⧸ U.toSubgroup)) :
    levelRes R (H := H) U (r • z) = r • levelRes R U z := by
  rw [levelRes_apply, levelRes_apply]
  ext : 1
  rw [MonoidAlgebra.coeff_comapDomain, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_smul,
    MonoidAlgebra.coeff_comapDomain, Finsupp.comapDomain_smul_of_injective (levelMap_injective U)]

/-- The level `U` of the image of `a ∈ R[[H]]` in `R[[Γ]]` is the level `U ⊓ H` of `a` pushed
along `levelMap U`. -/
private theorem proj_map_subtype (U : OpenNormalSubgroup Γ) (a : completedGroupAlgebra R H) :
    proj R Γ U (map R H.subtype continuous_subtype_val a) =
      MonoidAlgebra.mapDomain (levelMap U)
        (proj R H (U.comap H.subtype continuous_subtype_val) a) :=
  proj_map R _ _ U a

/-- For `U ≤ H`, restricting a monomial to `H` keeps it if its group element lies in `H` and
kills it otherwise. -/
private theorem levelRes_single_of_mem (U : OpenNormalSubgroup Γ) {γ : Γ} (hγ : γ ∈ H) (r : R) :
    levelRes R (H := H) U (MonoidAlgebra.single (γ : Γ ⧸ U.toSubgroup) r) =
      MonoidAlgebra.single (((⟨γ, hγ⟩ : H)) : H ⧸ _) r := by
  rw [levelRes_apply, ← levelMap_mk U ⟨γ, hγ⟩, MonoidAlgebra.comapDomain_single_map]

private theorem levelRes_single_of_notMem {U : OpenNormalSubgroup Γ} (hU : U.toSubgroup ≤ H)
    {γ : Γ} (hγ : γ ∉ H) (r : R) :
    levelRes R (H := H) U (MonoidAlgebra.single (γ : Γ ⧸ U.toSubgroup) r) = 0 := by
  rw [levelRes_apply,
    MonoidAlgebra.comapDomain_single_of_notMem_range (mt (mk_mem_range_levelMap_iff hU γ).mp hγ)]

/-- Restricting to `H` commutes with passing from the level `U` to a larger level `U' ≤ H`. -/
private theorem mapDomain_mapOfLE_levelRes {U U' : OpenNormalSubgroup Γ} (hUU' : U ≤ U')
    (hU' : U'.toSubgroup ≤ H) (z : MonoidAlgebra R (Γ ⧸ U.toSubgroup)) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE
        (OpenNormalSubgroup.comap_mono H.subtype continuous_subtype_val hUU'))
        (levelRes R U z) =
      levelRes R U' (MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUU') z) := by
  have hU : U.toSubgroup ≤ H := (OpenNormalSubgroup.toSubgroup_le.mpr hUU').trans hU'
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, MonoidAlgebra.mapDomain_add, hx, hy, MonoidAlgebra.mapDomain_add, map_add]
  | single q r =>
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidAlgebra.mapDomain_single, QuotientGroup.mapOfLE_mk]
    by_cases hγ : γ ∈ H
    · rw [levelRes_single_of_mem R U hγ, levelRes_single_of_mem R U' hγ,
        MonoidAlgebra.mapDomain_single, QuotientGroup.mapOfLE_mk]
    · rw [levelRes_single_of_notMem R hU hγ, levelRes_single_of_notMem R hU' hγ,
        MonoidAlgebra.mapDomain_zero]

/-- The restriction to `H` read at a level `U ≤ H` and pushed to a level `V` of `H`, agrees with
the same construction at any smaller level `U₀ ≤ U`. -/
private theorem mapDomain_levelRes_eq_of_le {U₀ U : OpenNormalSubgroup Γ} (hU₀U : U₀ ≤ U)
    (hU : U.toSubgroup ≤ H) (V : OpenNormalSubgroup H)
    (hV : (U.comap H.subtype continuous_subtype_val) ≤ V) (x : completedGroupAlgebra R Γ) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hV) (levelRes R U (proj R Γ U x)) =
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE
        ((OpenNormalSubgroup.comap_mono H.subtype continuous_subtype_val hU₀U).trans hV))
        (levelRes R U₀ (proj R Γ U₀ x)) := by
  rw [← mapDomain_mapOfLE_proj hU₀U, ← mapDomain_mapOfLE_levelRes R hU₀U hU,
    MonoidAlgebra.mapDomain_mapDomain, ← MonoidHom.coe_comp, QuotientGroup.mapOfLE_comp]

end Levels

section Restrict

variable [SeparatelyContinuousMul Γ] {H : Subgroup Γ} (hH : IsOpen (H : Set Γ)) [H.FiniteIndex]

/-- The normal core in `Γ` of an open normal subgroup `V` of `H`: an open normal subgroup of `Γ`
contained in `V`. -/
private noncomputable def core (V : OpenNormalSubgroup H) : OpenNormalSubgroup Γ where
  toSubgroup := (V.toSubgroup.map H.subtype).normalCore
  isOpen' :=
    have := H.finiteIndex_normalizer_map_subtype V.toSubgroup
    Subgroup.isOpen_normalCore_of_finiteIndex_normalizer <| by
      rw [Subgroup.coe_map, Subgroup.coe_subtype]
      exact hH.isOpenMap_subtype_val _ V.isOpen
  isNormal' := Subgroup.normalCore_normal _

private theorem core_le (V : OpenNormalSubgroup H) : (core hH V).toSubgroup ≤ H :=
  (Subgroup.normalCore_le _).trans (Subgroup.map_subtype_le _)

private theorem comap_core_le (V : OpenNormalSubgroup H) :
    (core hH V).comap H.subtype continuous_subtype_val ≤ V := fun _ hh ↦
  (Subgroup.mem_map_iff_mem H.subtype_injective).mp
    (Subgroup.normalCore_le _ (OpenNormalSubgroup.mem_comap.mp hh))

/-- The level `V` of the restriction of `x` to `H`, read at the level `core V` of `R[[Γ]]`. -/
private noncomputable def restrictLevel (x : completedGroupAlgebra R Γ) (V : OpenNormalSubgroup H) :
    MonoidAlgebra R (H ⧸ V.toSubgroup) :=
  MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE (comap_core_le hH V))
    (levelRes R (core hH V) (proj R Γ (core hH V) x))

/-- The level `V` of the restriction may be read at any level `U ≤ H` of `R[[Γ]]` whose
intersection with `H` lies in `V`. -/
private theorem restrictLevel_eq (x : completedGroupAlgebra R Γ) (U : OpenNormalSubgroup Γ)
    (hU : U.toSubgroup ≤ H) (V : OpenNormalSubgroup H)
    (hUV : U.comap H.subtype continuous_subtype_val ≤ V) :
    restrictLevel R hH x V =
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (levelRes R U (proj R Γ U x)) := by
  rw [restrictLevel, mapDomain_levelRes_eq_of_le R (inf_le_right : U ⊓ core hH V ≤ _)
    (core_le hH V), mapDomain_levelRes_eq_of_le R (inf_le_left : U ⊓ core hH V ≤ _) hU]

/-- The **restriction** `R[[Γ]] → R[[H]]` to an open subgroup `H` of finite index. Viewing elements
of `R[[Γ]]` as measures on `Γ`, it restricts a measure to the clopen subset `H`. At the level of an
open normal subgroup `U ≤ H` of `Γ` it keeps the coefficients of `R[Γ ⧸ U]` on `H ⧸ U`
(`proj_restrict`). It is left `R[[H]]`-linear (`restrict_map_mul`), and the coordinates of `x`
in the coset basis `basisCosets R hH s hs` are `restrict R hH (x * of R Γ (s q))`, where `s q`
is the chosen representative of `q`. -/
noncomputable def restrict : completedGroupAlgebra R Γ →ₗ[R] completedGroupAlgebra R H where
  toFun x := mk R H (restrictLevel R hH x) fun V W hVW ↦ by
    rw [restrictLevel_eq R hH x (core hH V) (core_le hH V) W
        ((comap_core_le hH V).trans hVW), restrictLevel, MonoidAlgebra.mapDomain_mapDomain,
      ← MonoidHom.coe_comp, QuotientGroup.mapOfLE_comp]
  map_add' x y := ext fun V ↦ by
    simp only [proj_mk, restrictLevel, map_add, MonoidAlgebra.mapDomain_add]
  map_smul' r x := ext fun V ↦ by
    simp only [proj_mk, restrictLevel, map_smul, RingHom.id_apply, levelRes_smul,
      MonoidAlgebra.mapDomain_smul]

private theorem proj_comap_restrict (U : OpenNormalSubgroup Γ) (hU : U.toSubgroup ≤ H)
    (x : completedGroupAlgebra R Γ) :
    proj R H (U.comap H.subtype continuous_subtype_val) (restrict R hH x) =
      levelRes R U (proj R Γ U x) := by
  rw [restrict, LinearMap.coe_mk, AddHom.coe_mk, proj_mk, restrictLevel_eq R hH x U hU _ le_rfl,
    QuotientGroup.mapOfLE_refl, MonoidHom.coe_id, MonoidAlgebra.mapDomain_id]

/-- At the level `U ⊓ H` of `R[[H]]`, for an open normal subgroup `U ≤ H` of `Γ`, the restriction
of `x` keeps the coefficients of the level `U` of `x` on the classes of elements of `H`. -/
theorem proj_restrict (U : OpenNormalSubgroup Γ) (hU : U.toSubgroup ≤ H)
    (x : completedGroupAlgebra R Γ) :
    proj R H (U.comap H.subtype continuous_subtype_val) (restrict R hH x) =
      MonoidAlgebra.comapDomain
        (QuotientGroup.map _ _ H.subtype (U.toSubgroup_comap H.subtype continuous_subtype_val).le)
        ((QuotientGroup.map_injective_iff _ U.toSubgroup H.subtype _).mpr
          (U.toSubgroup_comap _ _).ge)
        (proj R Γ U x) := by
  rw [proj_comap_restrict R hH U hU, levelRes_apply]
  -- `levelMap U` is by definition the map on quotients induced by `H.subtype`
  rfl

/-- The restriction to `H` is left linear over `R[[H]]`, acting on `R[[Γ]]` through the
inclusion. -/
theorem restrict_map_mul (a : completedGroupAlgebra R H) (x : completedGroupAlgebra R Γ) :
    restrict R hH (map R H.subtype continuous_subtype_val a * x) = a * restrict R hH x := by
  refine ext fun V ↦ ?_
  simp only [restrict, LinearMap.coe_mk, AddHom.coe_mk, proj_mk, restrictLevel, map_mul]
  rw [proj_map_subtype, levelRes_apply, levelRes_apply, MonoidAlgebra.comapDomain_mapDomain_mul,
    MonoidAlgebra.mapDomain_mul,
    mapDomain_mapOfLE_proj]

/-- A group element of `H` restricts to itself. -/
@[simp]
theorem restrict_of_of_mem {γ : Γ} (hγ : γ ∈ H) :
    restrict R hH (of R Γ γ) = of R H ⟨γ, hγ⟩ := by
  refine ext fun V ↦ ?_
  simp only [restrict, LinearMap.coe_mk, AddHom.coe_mk, proj_mk, restrictLevel, proj_of]
  rw [levelRes_single_of_mem R _ hγ, MonoidAlgebra.mapDomain_single, QuotientGroup.mapOfLE_mk]

/-- A group element outside `H` restricts to zero. -/
@[simp]
theorem restrict_of_of_notMem {γ : Γ} (hγ : γ ∉ H) : restrict R hH (of R Γ γ) = 0 := by
  refine ext fun V ↦ ?_
  simp only [restrict, LinearMap.coe_mk, AddHom.coe_mk, proj_mk, restrictLevel, proj_of, map_zero]
  rw [levelRes_single_of_notMem R (core_le hH V) hγ, MonoidAlgebra.mapDomain_zero]

/-- The restriction to `H` is a retraction of the inclusion `R[[H]] → R[[Γ]]`. -/
@[simp]
theorem restrict_map (a : completedGroupAlgebra R H) :
    restrict R hH (map R H.subtype continuous_subtype_val a) = a := by
  have h1 : restrict R hH 1 = 1 := by
    rw [← map_one (of R Γ), restrict_of_of_mem R hH H.one_mem]
    exact map_one (of R H)
  simpa [h1] using restrict_map_mul R hH a 1

include hH in
/-- Two elements of `R[[Γ]]` agreeing at every level contained in `H` are equal: these levels are
cofinal, since `H` contains an open normal subgroup of `Γ`. -/
private theorem ext_of_le_subgroup {x y : completedGroupAlgebra R Γ}
    (h : ∀ U : OpenNormalSubgroup Γ, U.toSubgroup ≤ H → proj R Γ U x = proj R Γ U y) : x = y := by
  have : (⟨H, hH⟩ : OpenSubgroup Γ).toSubgroup.FiniteIndex := ‹H.FiniteIndex›
  obtain ⟨N, hN, -⟩ := OpenSubgroup.exists_openNormalSubgroup_le (⟨H, hH⟩ : OpenSubgroup Γ)
  refine ext fun W ↦ ?_
  have hWN : (W ⊓ N).toSubgroup ≤ H := by
    rw [OpenNormalSubgroup.toSubgroup_inf]
    exact inf_le_right.trans hN
  rw [← mapDomain_mapOfLE_proj (inf_le_left : W ⊓ N ≤ W) x,
    ← mapDomain_mapOfLE_proj (inf_le_left : W ⊓ N ≤ W) y, h _ hWN]

omit [SeparatelyContinuousMul Γ] [H.FiniteIndex] in
/-- At a level `U ≤ H`, an element of `R[Γ ⧸ U]` is the sum over the cosets `q ∈ Γ ⧸ H` of its
coefficients on `H ⧸ U` after translation by a representative `s q` of `q`, translated back by
`(s q)⁻¹`. -/
private theorem sum_mapDomain_levelRes_mul_single [Fintype (Γ ⧸ H)] (s : Γ ⧸ H → Γ)
    (hs : ∀ q, (s q : Γ ⧸ H) = q) {U : OpenNormalSubgroup Γ} (hU : U.toSubgroup ≤ H)
    (z : MonoidAlgebra R (Γ ⧸ U.toSubgroup)) :
    ∑ q : Γ ⧸ H, MonoidAlgebra.mapDomain (levelMap (H := H) U)
        (levelRes R U (z * MonoidAlgebra.single ((s q : Γ) : Γ ⧸ U.toSubgroup) 1)) *
          MonoidAlgebra.single (((s q)⁻¹ : Γ) : Γ ⧸ U.toSubgroup) 1 = z := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [add_mul, map_add, MonoidAlgebra.mapDomain_add, Finset.sum_add_distrib, hx, hy]
  | single g r =>
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
    -- only the coset `q` of `γ⁻¹` contributes, and it contributes the monomial itself
    have hmem (q : Γ ⧸ H) : γ * s q ∈ H ↔ q = (γ⁻¹ : Γ) := by
      conv_rhs => rw [← hs q]
      rw [eq_comm, QuotientGroup.eq, inv_inv]
    have hterm (q : Γ ⧸ H) :
        MonoidAlgebra.mapDomain (levelMap (H := H) U) (levelRes R U
          (MonoidAlgebra.single (γ : Γ ⧸ U.toSubgroup) r *
            MonoidAlgebra.single ((s q : Γ) : Γ ⧸ U.toSubgroup) 1)) *
          MonoidAlgebra.single (((s q)⁻¹ : Γ) : Γ ⧸ U.toSubgroup) 1 =
        if q = (γ⁻¹ : Γ) then MonoidAlgebra.single (γ : Γ ⧸ U.toSubgroup) r else 0 := by
      rw [MonoidAlgebra.single_mul_single, mul_one, ← QuotientGroup.mk_mul]
      split_ifs with hq
      · rw [levelRes_single_of_mem R U ((hmem q).mpr hq), MonoidAlgebra.mapDomain_single,
          levelMap_mk, MonoidAlgebra.single_mul_single, mul_one, ← QuotientGroup.mk_mul,
          mul_inv_cancel_right]
      · rw [levelRes_single_of_notMem R hU (mt (hmem q).mp hq), MonoidAlgebra.mapDomain_zero,
          zero_mul]
    rw [Finset.sum_congr rfl fun q _ ↦ hterm q]
    simp

/-- Every element of `R[[Γ]]` is the sum over the cosets `q ∈ Γ ⧸ H` of the restrictions to `H` of
its translates `x * s q` by representatives `s q` of `q`, translated back by `(s q)⁻¹`. -/
private theorem sum_map_restrict_mul_of [Fintype (Γ ⧸ H)] (s : Γ ⧸ H → Γ)
    (hs : ∀ q, (s q : Γ ⧸ H) = q) (x : completedGroupAlgebra R Γ) :
    ∑ q : Γ ⧸ H, map R H.subtype continuous_subtype_val (restrict R hH (x * of R Γ (s q))) *
      of R Γ (s q)⁻¹ = x :=
  ext_of_le_subgroup R hH fun U hU ↦ by
    simp only [map_sum, map_mul, proj_map_subtype, proj_comap_restrict R hH U hU, proj_of]
    exact sum_mapDomain_levelRes_mul_single R s hs hU _

/-- For representatives `s q` of the cosets `q ∈ Γ ⧸ H`, the restriction to `H` of
`(∑ q', ι (c q') * (s q')⁻¹) * s q` is the coefficient `c q`. -/
private theorem restrict_sum_mul_of (s : Γ ⧸ H → Γ) (hs : ∀ q, (s q : Γ ⧸ H) = q)
    (c : Γ ⧸ H →₀ completedGroupAlgebra R H) (q : Γ ⧸ H) :
    restrict R hH ((c.sum fun q' a ↦ map R H.subtype continuous_subtype_val a *
      of R Γ (s q')⁻¹) * of R Γ (s q)) = c q := by
  classical
  simp_rw [Finsupp.sum_mul, map_finsuppSum, mul_assoc, ← map_mul (of R Γ), restrict_map_mul]
  rw [Finsupp.sum, Finset.sum_eq_single q]
  · rw [inv_mul_cancel, map_one, ← map_one (of R Γ), restrict_of_of_mem R hH H.one_mem,
      ← OneMemClass.one_def, map_one, mul_one]
  · intro q' _ hq'
    rw [restrict_of_of_notMem R hH, mul_zero]
    rwa [← QuotientGroup.eq, hs, hs]
  · intro hq
    rw [Finsupp.notMem_support_iff.mp hq, zero_mul]

end Restrict

section Basis

variable [SeparatelyContinuousMul Γ] {H : Subgroup Γ} (hH : IsOpen (H : Set Γ)) [H.FiniteIndex]

/-- The **coset basis** of the completed group algebra `R[[Γ]]` over `R[[H]]`, for an open subgroup
`H` of finite index acting on `R[[Γ]]` by left multiplication through the inclusion. Given a
representative `s q` of each left coset `q ∈ Γ ⧸ H`, the basis vector at `q` is the group element
`(s q)⁻¹`; these elements represent the right cosets of `H`, and every set of representatives of
the right cosets arises in this way. The coordinate at `q` of `x` is the restriction to `H` of
`x * s q` (`basisCosets_repr_apply`). In particular `R[[Γ]]` is free over `R[[H]]` of rank the index
`[Γ : H]`. -/
noncomputable def basisCosets (s : Γ ⧸ H → Γ) (hs : ∀ q, (s q : Γ ⧸ H) = q) :
    letI := (map R H.subtype continuous_subtype_val).toRingHom.toModule
    Module.Basis (Γ ⧸ H) (completedGroupAlgebra R H) (completedGroupAlgebra R Γ) :=
  letI := (map R H.subtype continuous_subtype_val).toRingHom.toModule
  have hsum (c : Γ ⧸ H →₀ completedGroupAlgebra R H) :
      Finsupp.linearCombination (completedGroupAlgebra R H) (fun q : Γ ⧸ H ↦ of R Γ (s q)⁻¹) c =
        c.sum fun q a ↦ map R H.subtype continuous_subtype_val a * of R Γ (s q)⁻¹ :=
    Finsupp.linearCombination_apply _ _
  .mk (v := fun q : Γ ⧸ H ↦ of R Γ (s q)⁻¹)
    (linearIndependent_iff.mpr fun c hc ↦ Finsupp.ext fun q ↦ by
      rw [Finsupp.coe_zero, Pi.zero_apply, ← restrict_sum_mul_of R hH s hs c q, ← hsum, hc,
        zero_mul, map_zero])
    fun x _ ↦ by
      let := Fintype.ofFinite (Γ ⧸ H)
      rw [← sum_map_restrict_mul_of R hH s hs x]
      exact Submodule.sum_mem _ fun q _ ↦
        Submodule.smul_mem _ (restrict R hH (x * of R Γ (s q))) (Submodule.subset_span ⟨q, rfl⟩)

/-- The basis vector of `basisCosets` at the coset `q` is the group element `(s q)⁻¹`. -/
@[simp]
theorem basisCosets_apply (s : Γ ⧸ H → Γ) (hs : ∀ q, (s q : Γ ⧸ H) = q) (q : Γ ⧸ H) :
    basisCosets R hH s hs q = of R Γ (s q)⁻¹ := by
  let := (map R H.subtype continuous_subtype_val).toRingHom.toModule
  unfold basisCosets
  exact Module.Basis.mk_apply _ _ q

/-- The coordinate at the coset `q` of `x` in `basisCosets` is the restriction to `H` of the
translate `x * s q`. -/
@[simp]
theorem basisCosets_repr_apply (s : Γ ⧸ H → Γ) (hs : ∀ q, (s q : Γ ⧸ H) = q)
    (x : completedGroupAlgebra R Γ) (q : Γ ⧸ H) :
    letI := (map R H.subtype continuous_subtype_val).toRingHom.toModule
    (basisCosets R hH s hs).repr x q = restrict R hH (x * of R Γ (s q)) := by
  let := (map R H.subtype continuous_subtype_val).toRingHom.toModule
  conv_rhs => rw [← (basisCosets R hH s hs).linearCombination_repr x]
  rw [Finsupp.linearCombination_apply]
  simp only [basisCosets_apply, RingHom.toModule_smul, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom]
  exact (restrict_sum_mul_of R hH s hs _ q).symm

include hH in
/-- **Finite generation over an open subgroup.** A module `M` over `R[[Γ]]`, viewed as a module over
`R[[H]]` through the inclusion, is finitely generated over `R[[H]]` if and only if it is finitely
generated over `R[[Γ]]`, since `R[[Γ]]` is finite free over `R[[H]]`. -/
theorem module_finite_iff_of_isOpen (M : Type*) [AddCommMonoid M]
    [Module (completedGroupAlgebra R Γ) M] [Module (completedGroupAlgebra R H) M]
    (hM : ∀ (a : completedGroupAlgebra R H) (m : M),
      a • m = map R H.subtype continuous_subtype_val a • m) :
    Module.Finite (completedGroupAlgebra R H) M ↔ Module.Finite (completedGroupAlgebra R Γ) M := by
  let := (map R H.subtype continuous_subtype_val).toRingHom.toModule
  have : IsScalarTower (completedGroupAlgebra R H) (completedGroupAlgebra R Γ) M :=
    ⟨fun a x m ↦ by
      rw [hM, RingHom.toModule_smul, mul_smul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]⟩
  have : Module.Finite (completedGroupAlgebra R H) (completedGroupAlgebra R Γ) :=
    .of_basis (basisCosets R hH Quotient.out QuotientGroup.out_eq')
  exact ⟨fun _ ↦ .of_restrictScalars_finite (completedGroupAlgebra R H) _ M,
    fun _ ↦ .trans (completedGroupAlgebra R Γ) M⟩

end Basis

end completedGroupAlgebra

end TauCeti
