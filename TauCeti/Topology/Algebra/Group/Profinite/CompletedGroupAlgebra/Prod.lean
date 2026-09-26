/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Map

/-!
# The completed group algebra of a product with a finite group

For a finite discrete group `C` and a topological group `Γ`, the completed group algebra of the
product `C × Γ` is the group algebra of `C` over the completed group algebra of `Γ`:

```text
R[[C × Γ]] ≅ R[[Γ]][C].
```

The map `R[[Γ]][C] → R[[C × Γ]]` sends the monomial `x · c` to `x · (c, 1)`, where `x ∈ R[[Γ]]`
is pushed into `R[[C × Γ]]` along the inclusion `γ ↦ (1, γ)` of the second factor and `(c, 1)` is
a group element (`TauCeti.completedGroupAlgebra.monoidAlgebraProdHom`, which is an `R`-algebra
homomorphism because these two kinds of elements commute). At the level `{1} × U` of `R[[C × Γ]]`,
for an open normal subgroup `U` of `Γ`, it reads the coefficient at the class of `(c, γ)` off the
coefficient at the class of `γ` of the level `U` of the coefficient at `c`
(`coeff_proj_monoidAlgebraProdHom`); this makes it injective for every discrete `C` and every
`Γ`. When `C` is finite it is also surjective, for every coefficient ring and every `Γ`: the levels
`{1} × U` are cofinal among the open normal subgroups of `C × Γ`
(`ext_of_proj_openNormalSubgroupBot_prod`), and reading the coefficients of an element of
`R[[C × Γ]]` at these levels along the classes of the `(c, γ)` for fixed `c` gives, for each
`c`, a compatible family of elements of the levels of `R[[Γ]]`, that is, an element of `R[[Γ]]`.
The resulting isomorphism is `TauCeti.completedGroupAlgebra.monoidAlgebraProdEquiv`.

For `R = ℤ_p` and `Γ ≅ ℤ_p` this identifies `ℤ_p[[C × ℤ_p]]` with `ℤ_p[[ℤ_p]][C]`, and through the
power-series coordinate of the Iwasawa algebra with `ℤ_p⟦X⟧[C]`; it is the first step in writing
the completed group algebra of the orientation image `{±1} × (1 + 2^f ℤ₂)` of a dyadic Demushkin
group as a power-series ring over the group ring `ℤ₂[C₂]`, the coefficient ring of Labute's
treatment of the even-rank case with `q = 2`.

## Main definitions

* `TauCeti.completedGroupAlgebra.monoidAlgebraProdHom R C Γ`: the `R`-algebra homomorphism
  `R[[Γ]][C] →ₐ[R] R[[C × Γ]]`.
* `TauCeti.completedGroupAlgebra.monoidAlgebraProdEquiv R C Γ`: the isomorphism
  `R[[Γ]][C] ≃ₐ[R] R[[C × Γ]]` for finite `C`.
* `TauCeti.botProdMk U c`: the map `Γ ⧸ U → (C × Γ) ⧸ ({1} × U)` sending the class of `γ` to the
  class of `(c, γ)`, through which the levels `{1} × U` are read.

## Main results

* `TauCeti.completedGroupAlgebra.monoidAlgebraProdHom_single_of`: the monomial `γ · c` goes to the
  group element `(c, γ)`.
* `TauCeti.completedGroupAlgebra.coeff_proj_monoidAlgebraProdHom`: the levelwise description at
  the level `{1} × U`.
* `TauCeti.completedGroupAlgebra.monoidAlgebraProdHom_injective`,
  `TauCeti.completedGroupAlgebra.monoidAlgebraProdHom_surjective`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 4.
-/

public section

namespace TauCeti

open Topology

universe u v w

variable (R : Type u) [CommRing R] (C : Type v) [Group C] [TopologicalSpace C]
  (Γ : Type w) [Group Γ] [TopologicalSpace Γ]

section BotProd

variable {R C Γ} [DiscreteTopology C]

/-- Membership in the level `{1} × U` of `C × Γ`, for `C` discrete and `U` an open normal subgroup
of `Γ`. -/
theorem mem_openNormalSubgroupBot_prod (U : OpenNormalSubgroup Γ) (x : C × Γ) :
    x ∈ ((openNormalSubgroupBot C).prod U).toSubgroup ↔ x.1 = 1 ∧ x.2 ∈ U.toSubgroup := by
  rw [OpenNormalSubgroup.toSubgroup_prod, Subgroup.mem_prod, openNormalSubgroupBot_toSubgroup,
    Subgroup.mem_bot]

/-- Two classes modulo the level `{1} × U` of `C × Γ` agree iff their `C`-coordinates agree and
their `Γ`-coordinates agree modulo `U`. -/
theorem mk_eq_mk_iff_openNormalSubgroupBot_prod (U : OpenNormalSubgroup Γ) {c c' : C}
    {γ γ' : Γ} :
    ((c, γ) : (C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup) = (c', γ') ↔
      c = c' ∧ (γ : Γ ⧸ U.toSubgroup) = γ' := by
  simp only [QuotientGroup.eq, mem_openNormalSubgroupBot_prod, Prod.inv_mk, Prod.mk_mul_mk,
    inv_mul_eq_one]

/-- The levels `{1} × U` grow with `U`. -/
theorem openNormalSubgroupBot_prod_mono {U V : OpenNormalSubgroup Γ} (hUV : U ≤ V) :
    (openNormalSubgroupBot C).prod U ≤ (openNormalSubgroupBot C).prod V := by
  rw [← OpenNormalSubgroup.toSubgroup_le, OpenNormalSubgroup.toSubgroup_prod,
    OpenNormalSubgroup.toSubgroup_prod]
  exact Subgroup.prod_mono le_rfl (OpenNormalSubgroup.toSubgroup_le.mpr hUV)

/-- The map `Γ ⧸ U → (C × Γ) ⧸ ({1} × U)` sending the class of `γ` to the class of `(c, γ)`, for
a group `C` with the discrete topology and an open normal subgroup `U` of `Γ`. It is injective
(`botProdMk_injective`), its range is the set of classes with `C`-coordinate `c`
(`mem_range_botProdMk_iff`), and the classes of these maps for the various `c` exhaust the
quotient; they are how the level `{1} × U` of `R[[C × Γ]]` is read off the level `U` of
`R[[Γ]]`. -/
def botProdMk (U : OpenNormalSubgroup Γ) (c : C) :
    Γ ⧸ U.toSubgroup → (C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup :=
  Quotient.map' (fun γ ↦ (c, γ)) fun _ _ h ↦
    Quotient.exact ((mk_eq_mk_iff_openNormalSubgroupBot_prod U).mpr ⟨rfl, Quotient.sound h⟩)

/-- `botProdMk U c` sends the class of `γ` to the class of `(c, γ)`. -/
@[simp]
theorem botProdMk_mk (U : OpenNormalSubgroup Γ) (c : C) (γ : Γ) :
    botProdMk U c (γ : Γ ⧸ U.toSubgroup) =
      ((c, γ) : (C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup) :=
  (rfl)

/-- `botProdMk U c` is injective. -/
theorem botProdMk_injective (U : OpenNormalSubgroup Γ) (c : C) :
    Function.Injective (botProdMk U c) := by
  intro q q' h
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨γ', rfl⟩ := QuotientGroup.mk_surjective q'
  rw [botProdMk_mk, botProdMk_mk, mk_eq_mk_iff_openNormalSubgroupBot_prod] at h
  exact h.2

/-- The class of `(c', γ)` is in the range of `botProdMk U c` iff `c' = c`. -/
theorem mem_range_botProdMk_iff (U : OpenNormalSubgroup Γ) {c c' : C} (γ : Γ) :
    ((c', γ) : (C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup) ∈
      Set.range (botProdMk U c) ↔ c' = c := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [botProdMk_mk, mk_eq_mk_iff_openNormalSubgroupBot_prod] at hq
    exact hq.1.symm
  · rintro rfl
    exact ⟨γ, botProdMk_mk U c' γ⟩

/-- Reading the coefficients of an element of `R[(C × Γ) ⧸ ({1} × U)]` along the classes of the
`(c, γ)` is compatible with passing to a larger level `V ≥ U`. -/
theorem mapDomain_mapOfLE_comapDomain_botProdMk {U V : OpenNormalSubgroup Γ} (hUV : U ≤ V) (c : C)
    (z : MonoidAlgebra R ((C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup)) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV)
        (MonoidAlgebra.comapDomain (botProdMk U c) (botProdMk_injective U c) z) =
      MonoidAlgebra.comapDomain (botProdMk V c) (botProdMk_injective V c)
        (MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE (openNormalSubgroupBot_prod_mono hUV))
          z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [MonoidAlgebra.comapDomain_add, MonoidAlgebra.mapDomain_add, hx, hy,
      MonoidAlgebra.mapDomain_add, MonoidAlgebra.comapDomain_add]
  | single q r =>
    obtain ⟨⟨c', γ⟩, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidAlgebra.mapDomain_single, QuotientGroup.mapOfLE_mk]
    by_cases hc : c' = c
    · subst hc
      rw [← botProdMk_mk U c' γ, MonoidAlgebra.comapDomain_single_map,
        MonoidAlgebra.mapDomain_single, QuotientGroup.mapOfLE_mk, ← botProdMk_mk V c' γ,
        MonoidAlgebra.comapDomain_single_map]
    · rw [MonoidAlgebra.comapDomain_single_of_not_mem_range
          (mt (mem_range_botProdMk_iff U γ).mp hc),
        MonoidAlgebra.mapDomain_zero,
        MonoidAlgebra.comapDomain_single_of_not_mem_range
          (mt (mem_range_botProdMk_iff V γ).mp hc)]

end BotProd

namespace completedGroupAlgebra

/-- The inclusion of the second factor `γ ↦ (1, γ)` is continuous. -/
theorem continuous_inr : Continuous (MonoidHom.inr C Γ) :=
  continuous_const.prodMk continuous_id

variable {C Γ}

/-- Every open normal subgroup `W` of `C × Γ`, for `C` discrete, contains the level `{1} × U` for
`U` the preimage of `W` under `γ ↦ (1, γ)`: the levels `{1} × U` are cofinal. -/
theorem openNormalSubgroupBot_prod_comap_inr_le [DiscreteTopology C]
    (W : OpenNormalSubgroup (C × Γ)) :
    (openNormalSubgroupBot C).prod (W.comap (MonoidHom.inr C Γ) (continuous_inr C Γ)) ≤ W := by
  rw [← OpenNormalSubgroup.toSubgroup_le]
  intro x hx
  obtain ⟨hc, hγ⟩ := (mem_openNormalSubgroupBot_prod _ x).mp hx
  rw [OpenNormalSubgroup.toSubgroup_comap, Subgroup.mem_comap, MonoidHom.inr_apply, ← hc] at hγ
  exact hγ

variable {R} in
/-- Two elements of `R[[C × Γ]]`, for `C` discrete, agreeing at every level `{1} × U` are equal:
these levels are cofinal. -/
theorem ext_of_proj_openNormalSubgroupBot_prod [DiscreteTopology C]
    {x y : completedGroupAlgebra R (C × Γ)}
    (h : ∀ U : OpenNormalSubgroup Γ, proj R (C × Γ) ((openNormalSubgroupBot C).prod U) x =
      proj R (C × Γ) ((openNormalSubgroupBot C).prod U) y) : x = y :=
  ext fun W ↦ by
    rw [← mapDomain_mapOfLE_proj (openNormalSubgroupBot_prod_comap_inr_le W) x, h,
      mapDomain_mapOfLE_proj]

/-- The elements of `R[[C × Γ]]` coming from `R[[Γ]]` along `γ ↦ (1, γ)` commute with the group
elements `(c, 1)` of the first factor. -/
theorem commute_map_inr_of_inl (x : completedGroupAlgebra R Γ) (c : C) :
    Commute (map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x)
      (of R (C × Γ) (MonoidHom.inl C Γ c)) := by
  refine ext fun W ↦ ?_
  rw [map_mul, map_mul, proj_map, proj_of]
  refine MonoidAlgebra.mapDomain_commute_single (fun q ↦ ?_) (fun s ↦ Commute.all _ _) _
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  rw [QuotientGroup.map_mk, MonoidHom.inr_apply, MonoidHom.inl_apply]
  exact Commute.map (by simp [Commute, SemiconjBy] : Commute ((1 : C), γ) (c, (1 : Γ)))
    (QuotientGroup.mk' _)

variable (C Γ)

/-- The `R`-algebra homomorphism `R[[Γ]][C] →ₐ[R] R[[C × Γ]]` sending the monomial `x · c` to the
product of the image of `x` along `γ ↦ (1, γ)` with the group element `(c, 1)`. It sends `γ · c`
to the group element `(c, γ)` (`monoidAlgebraProdHom_single_of`), is injective
(`monoidAlgebraProdHom_injective`), and is an isomorphism for finite `C`
(`monoidAlgebraProdEquiv`). -/
noncomputable def monoidAlgebraProdHom :
    MonoidAlgebra (completedGroupAlgebra R Γ) C →ₐ[R] completedGroupAlgebra R (C × Γ) :=
  MonoidAlgebra.liftNCAlgHom (map R (MonoidHom.inr C Γ) (continuous_inr C Γ))
    ((of R (C × Γ)).comp (MonoidHom.inl C Γ)) (commute_map_inr_of_inl R)

/-- On the monomial `x · c`, the map `R[[Γ]][C] → R[[C × Γ]]` is the image of `x` along
`γ ↦ (1, γ)` times the group element `(c, 1)`. -/
theorem monoidAlgebraProdHom_single (c : C) (x : completedGroupAlgebra R Γ) :
    monoidAlgebraProdHom R C Γ (MonoidAlgebra.single c x) =
      map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x * of R (C × Γ) (c, 1) := by
  simp only [monoidAlgebraProdHom, MonoidAlgebra.coe_liftNCAlgHom, MonoidAlgebra.liftNC_single,
    MonoidHom.comp_apply, MonoidHom.inl_apply, AddMonoidHom.coe_coe]

/-- The monomial `γ · c` goes to the group element `(c, γ)`. -/
@[simp]
theorem monoidAlgebraProdHom_single_of (c : C) (γ : Γ) :
    monoidAlgebraProdHom R C Γ (MonoidAlgebra.single c (of R Γ γ)) = of R (C × Γ) (c, γ) := by
  rw [monoidAlgebraProdHom_single, map_of, MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, one_mul,
    mul_one]

/-- The monomial `x · 1` goes to the image of `x` along `γ ↦ (1, γ)`. -/
@[simp]
theorem monoidAlgebraProdHom_single_one (x : completedGroupAlgebra R Γ) :
    monoidAlgebraProdHom R C Γ (MonoidAlgebra.single 1 x) =
      map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x := by
  rw [monoidAlgebraProdHom_single, ← Prod.one_eq_mk, map_one, mul_one]

variable {C Γ} [DiscreteTopology C]

/-- The level `U` of `R[[Γ]]` maps into the level `{1} × U` of `R[[C × Γ]]` along `γ ↦ (1, γ)`. -/
theorem le_comap_inr_openNormalSubgroupBot_prod (U : OpenNormalSubgroup Γ) :
    U.toSubgroup ≤ ((openNormalSubgroupBot C).prod U).toSubgroup.comap (MonoidHom.inr C Γ) :=
  fun _ hγ ↦ (mem_openNormalSubgroupBot_prod U _).mpr ⟨rfl, hγ⟩

/-- At the level `{1} × U`, the image of `x ∈ R[[Γ]]` along `γ ↦ (1, γ)` is the level `U` of `x`
pushed along `botProdMk U 1`, the class of `γ` going to the class of `(1, γ)`. -/
theorem proj_map_inr (U : OpenNormalSubgroup Γ) (x : completedGroupAlgebra R Γ) :
    proj R (C × Γ) ((openNormalSubgroupBot C).prod U)
        (map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x) =
      MonoidAlgebra.mapDomain (botProdMk U 1) (proj R Γ U x) := by
  have h : ⇑(QuotientGroup.map U.toSubgroup ((openNormalSubgroupBot C).prod U).toSubgroup
      (MonoidHom.inr C Γ) (le_comap_inr_openNormalSubgroupBot_prod U)) = botProdMk U 1 :=
    funext fun q ↦ by
      obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
      rw [QuotientGroup.map_mk, MonoidHom.inr_apply, botProdMk_mk]
  rw [proj_map_of_le R _ _ U _ (le_comap_inr_openNormalSubgroupBot_prod U), h]

/-- At the level `{1} × U`, the image of `x ∈ R[[Γ]]` along `γ ↦ (1, γ)` has, at the class of
`(1, γ)`, the coefficient of the level `U` of `x` at the class of `γ`. -/
theorem coeff_proj_map_inr_one (U : OpenNormalSubgroup Γ) (x : completedGroupAlgebra R Γ)
    (γ : Γ) :
    (proj R (C × Γ) ((openNormalSubgroupBot C).prod U)
        (map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x)).coeff
        (((1 : C), γ) : (C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup) =
      (proj R Γ U x).coeff (γ : Γ ⧸ U.toSubgroup) := by
  rw [proj_map_inr, MonoidAlgebra.coeff_mapDomain, ← botProdMk_mk U 1 γ,
    Finsupp.mapDomain_apply_of_injective (botProdMk_injective U 1)]

/-- At the level `{1} × U`, the image of `x ∈ R[[Γ]]` along `γ ↦ (1, γ)` has coefficient `0` at
the class of `(c, γ)` for `c ≠ 1`. -/
theorem coeff_proj_map_inr_of_ne_one (U : OpenNormalSubgroup Γ) (x : completedGroupAlgebra R Γ)
    {c : C} (hc : c ≠ 1) (γ : Γ) :
    (proj R (C × Γ) ((openNormalSubgroupBot C).prod U)
        (map R (MonoidHom.inr C Γ) (continuous_inr C Γ) x)).coeff
        ((c, γ) : (C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup) = 0 := by
  rw [proj_map_inr, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_of_notMem_range _ _ (mt (mem_range_botProdMk_iff U γ).mp hc)

/-- The level `{1} × U` of `R[[C × Γ]]` reads the level `U` of the coefficients: the coefficient at
the class of `(c, γ)` of the image of `f` is the coefficient at the class of `γ` of the level `U`
of the coefficient of `f` at `c`. -/
theorem coeff_proj_monoidAlgebraProdHom (f : MonoidAlgebra (completedGroupAlgebra R Γ) C)
    (U : OpenNormalSubgroup Γ) (c : C) (γ : Γ) :
    (proj R (C × Γ) ((openNormalSubgroupBot C).prod U) (monoidAlgebraProdHom R C Γ f)).coeff
        ((c, γ) : (C × Γ) ⧸ ((openNormalSubgroupBot C).prod U).toSubgroup) =
      (proj R Γ U (f.coeff c)).coeff (γ : Γ ⧸ U.toSubgroup) := by
  classical
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
  | single c' x =>
    rw [monoidAlgebraProdHom_single, map_mul, proj_of, MonoidAlgebra.coeff_mul_single_apply,
      mul_one, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, Prod.inv_mk, Prod.mk_mul_mk, inv_one,
      mul_one, MonoidAlgebra.coeff_single]
    by_cases hc : c' = c
    · subst hc
      rw [Finsupp.single_eq_same, mul_inv_cancel, coeff_proj_map_inr_one]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hc), map_zero, MonoidAlgebra.coeff_zero,
        Finsupp.zero_apply,
        coeff_proj_map_inr_of_ne_one _ _ _ (mul_inv_eq_one.not.mpr (Ne.symm hc))]

/-- The map `R[[Γ]][C] → R[[C × Γ]]` is injective, for every group `C` with the discrete topology
and every topological group `Γ`. -/
theorem monoidAlgebraProdHom_injective : Function.Injective (monoidAlgebraProdHom R C Γ) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ MonoidAlgebra.coeff_injective
    (Finsupp.ext fun c ↦ ext fun U ↦ MonoidAlgebra.coeff_injective (Finsupp.ext fun q ↦ ?_))
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← coeff_proj_monoidAlgebraProdHom, hf]
  simp

section Surjective

variable [Finite C]

/-- The map `R[[Γ]][C] → R[[C × Γ]]` is surjective when `C` is finite, for every coefficient ring
and every `Γ`: the coefficient at `c` of a preimage of `y` is the element of `R[[Γ]]` whose level
`U` reads the coefficients of `y` at the level `{1} × U` along the classes of the `(c, γ)`. -/
theorem monoidAlgebraProdHom_surjective : Function.Surjective (monoidAlgebraProdHom R C Γ) := by
  intro y
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun c ↦ mk R Γ
    (fun U ↦ MonoidAlgebra.comapDomain (botProdMk U c) (botProdMk_injective U c)
      (proj R (C × Γ) ((openNormalSubgroupBot C).prod U) y)) fun U V hUV ↦ ?_),
    ext_of_proj_openNormalSubgroupBot_prod fun U ↦ MonoidAlgebra.coeff_injective
      (Finsupp.ext fun q ↦ ?_)⟩
  · rw [mapDomain_mapOfLE_comapDomain_botProdMk, mapDomain_mapOfLE_proj]
  · obtain ⟨⟨c, γ⟩, rfl⟩ := QuotientGroup.mk_surjective q
    rw [coeff_proj_monoidAlgebraProdHom, MonoidAlgebra.coeff_ofCoeff,
      Finsupp.coe_equivFunOnFinite_symm, proj_mk, MonoidAlgebra.coeff_comapDomain,
      Finsupp.comapDomain_apply, botProdMk_mk]

variable (C Γ)

/-- **The completed group algebra of a product with a finite group.** For a finite discrete group
`C` and a topological group `Γ`, the group algebra of `C` over `R[[Γ]]` is the completed group
algebra of `C × Γ`: the monomial `γ · c` corresponds to the group element `(c, γ)`. -/
noncomputable def monoidAlgebraProdEquiv :
    MonoidAlgebra (completedGroupAlgebra R Γ) C ≃ₐ[R] completedGroupAlgebra R (C × Γ) :=
  AlgEquiv.ofBijective (monoidAlgebraProdHom R C Γ)
    ⟨monoidAlgebraProdHom_injective R, monoidAlgebraProdHom_surjective R⟩

@[simp]
theorem coe_monoidAlgebraProdEquiv :
    ⇑(monoidAlgebraProdEquiv R C Γ) = monoidAlgebraProdHom R C Γ :=
  (rfl)

/-- The inverse of `monoidAlgebraProdEquiv` sends the group element `(c, γ)` to the monomial
`γ · c`. -/
@[simp]
theorem monoidAlgebraProdEquiv_symm_of (c : C) (γ : Γ) :
    (monoidAlgebraProdEquiv R C Γ).symm (of R (C × Γ) (c, γ)) =
      MonoidAlgebra.single c (of R Γ γ) :=
  (monoidAlgebraProdEquiv R C Γ).symm_apply_eq.mpr (monoidAlgebraProdHom_single_of R C Γ c γ).symm

end Surjective

end completedGroupAlgebra

end TauCeti
