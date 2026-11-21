/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
public import TauCeti.Topology.Algebra.Group.Subgroup
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Map
import TauCeti.Algebra.MonoidAlgebra.ComapDomain

/-!
# Restriction of the completed group algebra to an open subgroup

Let `H` be an open subgroup of finite index of a topological group `Γ`. The inclusion of `H`
induces an `R`-algebra homomorphism `map R H.subtype _ : R[[H]] → R[[Γ]]`. This file constructs a
retraction of it in the opposite direction, the `R`-linear map
`completedGroupAlgebra.restrict R hH : R[[Γ]] → R[[H]]`. Thinking of `R[[Γ]]` as `R`-valued
measures on `Γ`, it restricts a measure to the clopen subset `H`. On a group element `γ` it gives
`γ` itself if `γ ∈ H` and `0` otherwise, and it is linear for the two-sided action of `R[[H]]` on
`R[[Γ]]`.

At a level `V ≤ H` of `R[[Γ]]` the restriction keeps the coefficients of an element of
`R[Γ ⧸ V]` at the classes of the elements of `H` (`coeff_proj_restrict`). These levels are
cofinal: because `H` is open of finite index, every open normal subgroup of `H` contains an open
normal subgroup of `Γ` (`OpenNormalSubgroup.exists_le_map_subtype`); this is where both
hypotheses on `H` are used. For a compact `Γ`, for instance a profinite group, every open
subgroup has finite index.

Multiplying by the representatives of the cosets of `H` decomposes every element of `R[[Γ]]`
along those cosets: for a right transversal `T` of `H`,
`x = ∑ t ∈ T, map (restrict (x * t⁻¹)) * t`, and symmetrically for a left transversal. These
decompositions are what make `R[[Γ]]` a free `R[[H]]`-module on the coset representatives, with
`restrict` computing the coordinates.

## Main definitions

* `TauCeti.completedGroupAlgebra.restrict R hH`: the restriction `R[[Γ]] →ₗ[R] R[[H]]` to an
  open subgroup `H` of finite index.

## Main results

* `TauCeti.completedGroupAlgebra.coeff_proj_restrict`: the restriction keeps the coefficients at
  the classes of the elements of `H`, at every level `V ≤ H` of `R[[Γ]]`.
* `TauCeti.completedGroupAlgebra.restrict_map`: the restriction is a retraction of the map induced
  by the inclusion.
* `TauCeti.completedGroupAlgebra.restrict_of_mem`,
  `TauCeti.completedGroupAlgebra.restrict_of_notMem`: the restriction of a group element.
* `TauCeti.completedGroupAlgebra.restrict_map_mul`,
  `TauCeti.completedGroupAlgebra.restrict_mul_map`: the restriction is linear for the left and
  right actions of `R[[H]]`.
* `TauCeti.completedGroupAlgebra.sum_map_restrict_mul_of`,
  `TauCeti.completedGroupAlgebra.sum_of_mul_map_restrict`: the decompositions of an element of
  `R[[Γ]]` along a right, respectively left, transversal of `H`.

## References

* M. Lazard, *Groupes analytiques p-adiques*, Publ. Math. IHÉS 26 (1965), Chapitre II, (2.2.7).
* J. Coates, T. Fukaya, K. Kato, R. Sujatha, O. Venjakob, *The GL₂ main conjecture for elliptic
  curves without complex multiplication*, Publ. Math. IHÉS 101 (2005), §2.
-/

public section

namespace TauCeti.completedGroupAlgebra

open _root_.MonoidAlgebra

universe u v

variable (R : Type u) [CommRing R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ)

/-! ### The levels below `H` -/

/-- The map `H ⧸ (V ∩ H) → Γ ⧸ V` induced by the inclusion of `H`, for an open normal subgroup `V`
of `Γ`. It is the map through which `map R H.subtype _` acts at the level `V` (`proj_map`). -/
private noncomputable def levelMap (V : OpenNormalSubgroup Γ) :
    H ⧸ (V.comap H.subtype H.continuous_subtype).toSubgroup →* Γ ⧸ V.toSubgroup :=
  QuotientGroup.map _ _ H.subtype (V.toSubgroup_comap H.subtype H.continuous_subtype).le

private theorem levelMap_mk (V : OpenNormalSubgroup Γ) (k : H) :
    levelMap H V (k : H ⧸ (V.comap H.subtype H.continuous_subtype).toSubgroup) =
      ((k : Γ) : Γ ⧸ V.toSubgroup) :=
  (rfl)

private theorem levelMap_injective (V : OpenNormalSubgroup Γ) :
    Function.Injective (levelMap H V) :=
  (QuotientGroup.map_injective_iff _ V.toSubgroup H.subtype _).mpr
    (V.toSubgroup_comap H.subtype H.continuous_subtype).ge

/-- For a level `V ≤ H`, the class of `g` modulo `V` comes from `H` exactly when `g ∈ H`. -/
private theorem mk_mem_range_levelMap {V : OpenNormalSubgroup Γ} (hV : V.toSubgroup ≤ H)
    (g : Γ) : ((g : Γ ⧸ V.toSubgroup) ∈ Set.range (levelMap H V)) ↔ g ∈ H := by
  refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun hg ↦ ⟨((⟨g, hg⟩ : H) : H ⧸ _), levelMap_mk H V ⟨g, hg⟩⟩⟩
  induction k using QuotientGroup.induction_on with
  | H k =>
    rw [levelMap_mk, QuotientGroup.eq] at hk
    exact (H.mul_mem_cancel_left (H.inv_mem k.property)).mp (hV hk)

/-- Restricting to `H` commutes with passing from a level `V₁ ≤ H` to a coarser level `V₂ ≤ H`. -/
private theorem mapDomain_comapDomain_levelMap {V₁ V₂ : OpenNormalSubgroup Γ} (h₁₂ : V₁ ≤ V₂)
    (hV₂ : V₂.toSubgroup ≤ H) (y : MonoidAlgebra R (Γ ⧸ V₁.toSubgroup)) :
    mapDomain
        (QuotientGroup.mapOfLE (OpenNormalSubgroup.comap_mono H.subtype H.continuous_subtype h₁₂))
        (comapDomain (levelMap H V₁) (levelMap_injective H V₁) y) =
      comapDomain (levelMap H V₂) (levelMap_injective H V₂)
        (mapDomain (QuotientGroup.mapOfLE h₁₂) y) := by
  refine mapDomain_comapDomain_eq_comapDomain_mapDomain _ _ (fun m ↦ ?_) (fun n hn ↦ ?_) y
  · induction m using QuotientGroup.induction_on with
    | H k => rw [levelMap_mk, QuotientGroup.mapOfLE_mk, QuotientGroup.mapOfLE_mk, levelMap_mk]
  · induction n using QuotientGroup.induction_on with
    | H g =>
      rw [QuotientGroup.mapOfLE_mk, mk_mem_range_levelMap H hV₂] at hn
      exact (mk_mem_range_levelMap H (le_trans h₁₂ hV₂) g).mpr hn

/-- The map induced by the inclusion of `H`, at a level `V` of `R[[Γ]]`. -/
private theorem proj_map_subtype (V : OpenNormalSubgroup Γ) (a : completedGroupAlgebra R H) :
    proj R Γ V (map R H.subtype H.continuous_subtype a) =
      mapDomain (levelMap H V) (proj R H (V.comap H.subtype H.continuous_subtype) a) :=
  proj_map R H.subtype H.continuous_subtype V a

/-- The restriction to `H` read at the level `W` of `R[[H]]` from a level `V ≤ H` of `R[[Γ]]`
with `V ∩ H ≤ W`. -/
private noncomputable def restrictAt (V : OpenNormalSubgroup Γ) (W : OpenNormalSubgroup H)
    (h : V.comap H.subtype H.continuous_subtype ≤ W) (x : completedGroupAlgebra R Γ) :
    MonoidAlgebra R (H ⧸ W.toSubgroup) :=
  mapDomain (QuotientGroup.mapOfLE h)
    (comapDomain (levelMap H V) (levelMap_injective H V) (proj R Γ V x))

/-- `restrictAt` does not depend on the level `V ≤ H`, first for comparable levels. -/
private theorem restrictAt_eq_of_le {V₁ V₂ : OpenNormalSubgroup Γ} (h₁₂ : V₁ ≤ V₂)
    (hV₂ : V₂.toSubgroup ≤ H) {W : OpenNormalSubgroup H}
    (h₁ : V₁.comap H.subtype H.continuous_subtype ≤ W)
    (h₂ : V₂.comap H.subtype H.continuous_subtype ≤ W) (x : completedGroupAlgebra R Γ) :
    restrictAt R H V₁ W h₁ x = restrictAt R H V₂ W h₂ x := by
  rw [restrictAt, restrictAt, ← mapDomain_mapOfLE_proj h₁₂ x,
    ← mapDomain_comapDomain_levelMap R H h₁₂ hV₂, mapDomain_mapDomain, ← MonoidHom.coe_comp,
    QuotientGroup.mapOfLE_comp]

/-- `restrictAt` does not depend on the level `V ≤ H`. -/
private theorem restrictAt_eq {V₁ V₂ : OpenNormalSubgroup Γ} (hV₁ : V₁.toSubgroup ≤ H)
    (hV₂ : V₂.toSubgroup ≤ H) {W : OpenNormalSubgroup H}
    (h₁ : V₁.comap H.subtype H.continuous_subtype ≤ W)
    (h₂ : V₂.comap H.subtype H.continuous_subtype ≤ W) (x : completedGroupAlgebra R Γ) :
    restrictAt R H V₁ W h₁ x = restrictAt R H V₂ W h₂ x :=
  have h := (OpenNormalSubgroup.comap_mono H.subtype H.continuous_subtype inf_le_left).trans h₁
  (restrictAt_eq_of_le R H inf_le_left hV₁ h h₁ x).symm.trans
    (restrictAt_eq_of_le R H inf_le_right hV₂ h h₂ x)

variable [SeparatelyContinuousMul Γ] {H} (hH : IsOpen (H : Set Γ)) [H.FiniteIndex]

include hH in
/-- Every level of `R[[H]]` lies above the intersection with `H` of a level `V ≤ H` of
`R[[Γ]]`. -/
private theorem exists_level (W : OpenNormalSubgroup H) :
    ∃ V : OpenNormalSubgroup Γ,
      V.toSubgroup ≤ H ∧ V.comap H.subtype H.continuous_subtype ≤ W := by
  obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_map_subtype hH W
  exact ⟨V, hV.trans (Subgroup.map_subtype_le _), fun k hk ↦
    (Subgroup.mem_map_iff_mem H.subtype_injective).mp (hV hk)⟩

include hH in
/-- Elements of `R[[H]]` agreeing at the intersections with `H` of the levels `V ≤ H` of `R[[Γ]]`
are equal. -/
private theorem ext_comap {a b : completedGroupAlgebra R H}
    (h : ∀ V : OpenNormalSubgroup Γ, V.toSubgroup ≤ H →
      proj R H (V.comap H.subtype H.continuous_subtype) a =
        proj R H (V.comap H.subtype H.continuous_subtype) b) : a = b :=
  ext fun W ↦ by
    obtain ⟨V, hV, hVW⟩ := exists_level hH W
    rw [← mapDomain_mapOfLE_proj hVW a, ← mapDomain_mapOfLE_proj hVW b, h V hV]

include hH in
/-- Elements of `R[[Γ]]` agreeing at the levels `V ≤ H` are equal. -/
private theorem ext_le {x y : completedGroupAlgebra R Γ}
    (h : ∀ V : OpenNormalSubgroup Γ, V.toSubgroup ≤ H → proj R Γ V x = proj R Γ V y) : x = y :=
  ext fun U ↦ by
    obtain ⟨V, hV, -⟩ := exists_level hH ⊤
    rw [← mapDomain_mapOfLE_proj (inf_le_left : U ⊓ V ≤ U) x,
      ← mapDomain_mapOfLE_proj (inf_le_left : U ⊓ V ≤ U) y, h _ (inf_le_right.trans hV)]

/-! ### The restriction map -/

/-- The **restriction to an open subgroup** `H` of finite index, `R[[Γ]] →ₗ[R] R[[H]]`: at every
level `V ≤ H` of `R[[Γ]]` it keeps the coefficients of an element of `R[Γ ⧸ V]` at the classes of
the elements of `H` (`coeff_proj_restrict`). It is a retraction of the map induced by the
inclusion (`restrict_map`), sends a group element of `H` to itself and any other group element to
`0` (`restrict_of_mem`, `restrict_of_notMem`), and is linear for the left and right actions of
`R[[H]]` (`restrict_map_mul`, `restrict_mul_map`). -/
noncomputable def restrict : completedGroupAlgebra R Γ →ₗ[R] completedGroupAlgebra R H where
  toFun x := mk R H
    (fun W ↦ restrictAt R H (exists_level hH W).choose W (exists_level hH W).choose_spec.2 x)
    fun W₁ W₂ h ↦ by
      rw [restrictAt, mapDomain_mapDomain, ← MonoidHom.coe_comp, QuotientGroup.mapOfLE_comp]
      exact restrictAt_eq R H (exists_level hH W₁).choose_spec.1
        (exists_level hH W₂).choose_spec.1 _ _ x
  map_add' x y := ext fun W ↦ by
    simp only [proj_mk, restrictAt, map_add, comapDomain_add, mapDomain_add]
  map_smul' r x := ext fun W ↦ by
    simp only [proj_mk, restrictAt, map_smul, comapDomain_smul, mapDomain_smul, RingHom.id_apply]

/-- The restriction at the intersection with `H` of a level `V ≤ H` of `R[[Γ]]`, as the pullback
of coefficients along the inclusion `H ⧸ (V ∩ H) → Γ ⧸ V`. -/
private theorem proj_comap_restrict {V : OpenNormalSubgroup Γ} (hV : V.toSubgroup ≤ H)
    (x : completedGroupAlgebra R Γ) :
    proj R H (V.comap H.subtype H.continuous_subtype) (restrict R hH x) =
      comapDomain (levelMap H V) (levelMap_injective H V) (proj R Γ V x) := by
  rw [restrict, LinearMap.coe_mk, AddHom.coe_mk, proj_mk,
    restrictAt_eq R H (exists_level hH _).choose_spec.1 hV _ le_rfl, restrictAt,
    QuotientGroup.mapOfLE_refl, MonoidHom.coe_id, mapDomain_id]

/-- **The coefficients of the restriction.** At every level `V ≤ H` of `R[[Γ]]`, the coefficient
of the restriction of `x` at the class of `k ∈ H` modulo `V ∩ H` is the coefficient of `x` at the
class of `k` modulo `V`. -/
theorem coeff_proj_restrict {V : OpenNormalSubgroup Γ} (hV : V.toSubgroup ≤ H)
    (x : completedGroupAlgebra R Γ) (k : H) :
    (proj R H (V.comap H.subtype H.continuous_subtype) (restrict R hH x)).coeff
        (k : H ⧸ (V.comap H.subtype H.continuous_subtype).toSubgroup) =
      (proj R Γ V x).coeff (k : Γ ⧸ V.toSubgroup) := by
  rw [proj_comap_restrict R hH hV, coeff_comapDomain, Finsupp.comapDomain_apply, levelMap_mk]

/-- **The restriction is a retraction** of the map `R[[H]] → R[[Γ]]` induced by the inclusion. -/
@[simp]
theorem restrict_map (a : completedGroupAlgebra R H) :
    restrict R hH (map R H.subtype H.continuous_subtype a) = a :=
  ext_comap R hH fun V hV ↦ by
    rw [proj_comap_restrict R hH hV, proj_map_subtype, comapDomain_mapDomain]

/-- The restriction of `1` is `1`. -/
@[simp]
theorem restrict_one : restrict R hH (1 : completedGroupAlgebra R Γ) = 1 := by
  rw [← map_one (map R H.subtype H.continuous_subtype), restrict_map]

/-- The restriction of a group element of `H` is that group element. -/
@[simp]
theorem restrict_of_mem {γ : Γ} (hγ : γ ∈ H) : restrict R hH (of R Γ γ) = of R H ⟨γ, hγ⟩ := by
  rw [← restrict_map R hH (of R H ⟨γ, hγ⟩), map_of, Subgroup.coe_subtype]

/-- The restriction of a group element outside `H` vanishes. -/
@[simp]
theorem restrict_of_notMem {γ : Γ} (hγ : γ ∉ H) : restrict R hH (of R Γ γ) = 0 :=
  ext_comap R hH fun V hV ↦ by
    rw [proj_comap_restrict R hH hV, proj_of, map_zero,
      comapDomain_single_of_notMem_range (mt (mk_mem_range_levelMap H hV γ).mp hγ)]

/-- **The restriction is left `R[[H]]`-linear**: restricting `a * x`, for `a` in the image of
`R[[H]]`, is multiplying the restriction of `x` on the left by `a`. -/
@[simp]
theorem restrict_map_mul (a : completedGroupAlgebra R H) (x : completedGroupAlgebra R Γ) :
    restrict R hH (map R H.subtype H.continuous_subtype a * x) = a * restrict R hH x :=
  ext_comap R hH fun V hV ↦ by
    rw [proj_comap_restrict R hH hV, map_mul, map_mul, proj_map_subtype,
      comapDomain_mapDomain_mul, proj_comap_restrict R hH hV]

/-- **The restriction is right `R[[H]]`-linear**: restricting `x * a`, for `a` in the image of
`R[[H]]`, is multiplying the restriction of `x` on the right by `a`. -/
@[simp]
theorem restrict_mul_map (x : completedGroupAlgebra R Γ) (a : completedGroupAlgebra R H) :
    restrict R hH (x * map R H.subtype H.continuous_subtype a) = restrict R hH x * a :=
  ext_comap R hH fun V hV ↦ by
    rw [proj_comap_restrict R hH hV, map_mul, map_mul, proj_map_subtype,
      comapDomain_mul_mapDomain, proj_comap_restrict R hH hV]

/-- For `s t` in a right transversal of `H`, the restriction of the group element `s * t⁻¹` is `1`
if `s = t` and `0` otherwise. -/
theorem restrict_of_mul_inv_of_isComplement {T : Set Γ} (hT : Subgroup.IsComplement (H : Set Γ) T)
    [DecidableEq T] (s t : T) :
    restrict R hH (of R Γ (s : Γ) * of R Γ (t : Γ)⁻¹) = if s = t then 1 else 0 := by
  split_ifs with hst
  · rw [hst, ← map_mul, mul_inv_cancel, map_one, restrict_one]
  · rw [← map_mul]
    refine restrict_of_notMem R hH fun h ↦ hst ?_
    obtain ⟨u, -, hu⟩ := Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hT s
    exact (hu s (by simp)).trans (hu t h).symm

/-- For `s t` in a left transversal of `H`, the restriction of the group element `s⁻¹ * t` is `1`
if `s = t` and `0` otherwise. -/
theorem restrict_of_inv_mul_of_isComplement {S : Set Γ} (hS : Subgroup.IsComplement S (H : Set Γ))
    [DecidableEq S] (s t : S) :
    restrict R hH (of R Γ (s : Γ)⁻¹ * of R Γ (t : Γ)) = if s = t then 1 else 0 := by
  split_ifs with hst
  · rw [hst, ← map_mul, inv_mul_cancel, map_one, restrict_one]
  · rw [← map_mul]
    refine restrict_of_notMem R hH fun h ↦ hst ?_
    obtain ⟨u, -, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp hS t
    exact (hu s h).trans (hu t (by simp)).symm

/-! ### Decomposition along the cosets of `H` -/

/-- **Decomposition along a right transversal.** If `T` is a right transversal of `H`, every
element `x` of `R[[Γ]]` is the sum over `t ∈ T` of the restriction of `x * t⁻¹`, mapped back to
`R[[Γ]]` and multiplied on the right by `t`. -/
theorem sum_map_restrict_mul_of {T : Set Γ} (hT : Subgroup.IsComplement (H : Set Γ) T)
    [Fintype T] (x : completedGroupAlgebra R Γ) :
    ∑ t : T, map R H.subtype H.continuous_subtype
        (restrict R hH (x * of R Γ (t : Γ)⁻¹)) * of R Γ (t : Γ) = x :=
  ext_le R hH fun V hV ↦ by
    simp only [map_sum, map_mul, proj_map_subtype, proj_comap_restrict R hH hV, proj_of,
      QuotientGroup.mk_inv]
    refine sum_mapDomain_comapDomain_mul_single _ _ (fun t : T ↦ ((t : Γ) : Γ ⧸ V.toSubgroup))
      (fun q ↦ ?_) _
    induction q using QuotientGroup.induction_on with
    | H g =>
      simpa only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_mem_range_levelMap H hV,
        SetLike.mem_coe] using
        Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hT g

/-- **Decomposition along a left transversal.** If `S` is a left transversal of `H`, every
element `x` of `R[[Γ]]` is the sum over `s ∈ S` of `s` multiplied on the right by the restriction
of `s⁻¹ * x`, mapped back to `R[[Γ]]`. -/
theorem sum_of_mul_map_restrict {S : Set Γ} (hS : Subgroup.IsComplement S (H : Set Γ))
    [Fintype S] (x : completedGroupAlgebra R Γ) :
    ∑ s : S, of R Γ (s : Γ) *
        map R H.subtype H.continuous_subtype (restrict R hH (of R Γ (s : Γ)⁻¹ * x)) = x :=
  ext_le R hH fun V hV ↦ by
    simp only [map_sum, map_mul, proj_map_subtype, proj_comap_restrict R hH hV, proj_of,
      QuotientGroup.mk_inv]
    refine sum_single_mul_mapDomain_comapDomain _ _ (fun s : S ↦ ((s : Γ) : Γ ⧸ V.toSubgroup))
      (fun q ↦ ?_) _
    induction q using QuotientGroup.induction_on with
    | H g =>
      simpa only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_mem_range_levelMap H hV,
        SetLike.mem_coe] using
        Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp hS g

end TauCeti.completedGroupAlgebra
