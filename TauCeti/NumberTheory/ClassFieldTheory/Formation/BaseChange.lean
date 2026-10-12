/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.GroundNorm

/-!
# Base change of a finite normal layer, and its norm quotient

Let `V ◁ U` be a finite normal layer of a formation, the layer `K/F` in field notation, and let
`U' ≤ U` be an open subgroup, cutting out a finite extension `F'` of `F`. The **base change** of
the layer to `U'` is the layer `V ⊓ U' ◁ U'` (`NormalLayer.baseChange`), the layer `KF'/F'`. Its
Galois group maps injectively to that of the original layer (`NormalLayer.baseChangeGalHom`, the
restriction `Gal(KF'/F') → Gal(K/F)`), so its degree divides the degree of the layer
(`NormalLayer.degree_baseChange_dvd`). When the two degrees agree, the case `K ∩ F' = F` in field
notation, this map is an isomorphism (`NormalLayer.baseChangeGalHom_bijective`).

On norm quotients there are two maps:

* the **restriction** `A^U / N_{U/V}(A^V) → A^{U'} / N_{U'/(V ⊓ U')}(A^{V ⊓ U'})`
  (`NormalLayer.normQuotientRes`), induced by the inclusion `A^U ⊆ A^{U'}`, defined when the two
  degrees agree, because then the norm of the layer is the norm of its base change;
* the **corestriction** in the other direction (`NormalLayer.normQuotientCor`), induced by the
  norm `N_{U/U'} : A^{U'} → A^U`, defined for every `U' ≤ U` by transitivity of norms.

Their composite is multiplication by the index `[U : U']`
(`NormalLayer.normQuotientCor_normQuotientRes`). The norm quotient of a layer is killed by its
degree (`NormalLayer.degree_nsmul_eq_zero`), so when `[U : U']` is prime to the degree `[U : V]`
the restriction is injective (`NormalLayer.normQuotientRes_injective`) and the order of the norm
quotient of the layer divides that of its base change
(`NormalLayer.natCard_normQuotient_dvd_natCard_normQuotient_baseChange`). In that case the degrees
agree automatically (`NormalLayer.degree_baseChange_of_coprime`).

This is the reduction used in the proof of the second fundamental inequality for a cyclic
extension `K/F` of prime degree `p`: adjoining the `p`-th roots of unity gives an extension `F'/F`
of degree dividing `p - 1`, and the bound `[C_F : N_{K/F} C_K] ∣ p` for `K/F` follows from the
same bound for `KF'/F'` (`NormalLayer.natCard_normQuotient_dvd_degree_of_baseChange`), where the
ground field contains the `p`-th roots of unity and Kummer theory applies.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.baseChange`: the layer `V ⊓ U' ◁ U'`.
* `TauCeti.ClassFieldTheory.NormalLayer.baseChangeGalHom`: the injective homomorphism from its
  Galois group to that of the layer.
* `TauCeti.ClassFieldTheory.NormalLayer.normQuotientRes`,
  `TauCeti.ClassFieldTheory.NormalLayer.normQuotientCor`: restriction and corestriction between
  the norm quotients.

## Main statements

* `TauCeti.ClassFieldTheory.NormalLayer.degree_baseChange_dvd`: the degree of the base change
  divides the degree of the layer.
* `TauCeti.ClassFieldTheory.NormalLayer.degree_baseChange_of_coprime`: the degrees agree when
  `[U : U']` is prime to `[U : V]`.
* `TauCeti.ClassFieldTheory.NormalLayer.normQuotientCor_normQuotientRes`: corestriction after
  restriction is multiplication by `[U : U']`.
* `TauCeti.ClassFieldTheory.NormalLayer.normQuotientRes_injective`: restriction is injective when
  `[U : U']` is prime to `[U : V]`.
* `TauCeti.ClassFieldTheory.NormalLayer.natCard_normQuotient_dvd_degree_of_baseChange`: the
  divisibility `#(A^U / N(A^V)) ∣ [U : V]` descends from the base change along a subgroup of
  index prime to the degree.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §4 (the reduction to a ground field
  containing the `p`-th roots of unity in the proof of the second inequality).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §§5–6.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

variable (L : NormalLayer G) {U' : OpenSubgroup G} (hU' : U' ≤ L.ground)

/-! ### The base-changed layer -/

/-- The **base change** of a layer `V ◁ U` to an open subgroup `U' ≤ U`: the layer `V ⊓ U' ◁ U'`.
In field notation, for a finite extension `F'/F` inside the formation, it is the layer `KF'/F'`
of the layer `K/F`. -/
def baseChange : NormalLayer G where
  ground := U'
  top := L.top ⊓ U'
  top_le_ground := inf_le_right
  normal := ⟨fun v hv u ↦ by
    rw [Subgroup.mem_subgroupOf, OpenSubgroup.toSubgroup_inf, Subgroup.mem_inf] at hv ⊢
    exact ⟨L.conj_mem_top (hU' u.2) hv.1, U'.mul_mem (U'.mul_mem u.2 hv.2) (U'.inv_mem u.2)⟩⟩

/-- The ground subgroup of the base change to `U'` is `U'`. -/
@[simp]
theorem baseChange_ground : (L.baseChange hU').ground = U' :=
  (rfl)

/-- The top subgroup of the base change to `U'` is `V ⊓ U'`. -/
@[simp]
theorem baseChange_top : (L.baseChange hU').top = L.top ⊓ U' :=
  (rfl)

/-- The ground subgroup `U'` of the base change lies in the ground subgroup `U` of the layer. -/
theorem baseChange_ground_le : (L.baseChange hU').ground ≤ L.ground :=
  hU'

/-- The top subgroup `V ⊓ U'` of the base change lies in the top subgroup `V` of the layer. -/
theorem baseChange_top_le : (L.baseChange hU').top ≤ L.top :=
  inf_le_left

/-- The homomorphism `U' ⧸ (V ⊓ U') → U ⧸ V` from the Galois group of the base change to that of
the layer, induced by the inclusion `U' ≤ U`: in field notation, the restriction
`Gal(KF'/F') → Gal(K/F)`. -/
def baseChangeGalHom : (L.baseChange hU').Gal →* L.Gal :=
  @QuotientGroup.quotientMapSubgroupOfOfLe G _ (L.baseChange hU').top.toSubgroup
    (L.baseChange hU').ground.toSubgroup L.top.toSubgroup L.ground.toSubgroup
    (L.baseChange hU').normal L.normal (OpenSubgroup.toSubgroup_le.2 (L.baseChange_top_le hU'))
    (OpenSubgroup.toSubgroup_le.2 (L.baseChange_ground_le hU'))

/-- The homomorphism of Galois groups is induced by the inclusion `U' ≤ U`. -/
@[simp]
theorem baseChangeGalHom_mk (u : (L.baseChange hU').ground) :
    L.baseChangeGalHom hU' (QuotientGroup.mk u) =
      QuotientGroup.mk
        (Subgroup.inclusion (OpenSubgroup.toSubgroup_le.2 (L.baseChange_ground_le hU')) u) :=
  @QuotientGroup.quotientMapSubgroupOfOfLe_mk G _ (L.baseChange hU').top.toSubgroup
    (L.baseChange hU').ground.toSubgroup L.top.toSubgroup L.ground.toSubgroup
    (L.baseChange hU').normal L.normal (OpenSubgroup.toSubgroup_le.2 (L.baseChange_top_le hU'))
    (OpenSubgroup.toSubgroup_le.2 (L.baseChange_ground_le hU')) u

/-- The Galois group of the base change embeds in the Galois group of the layer: an element of
`U'` that lies in `V` lies in `V ⊓ U'`. -/
theorem baseChangeGalHom_injective : Function.Injective (L.baseChangeGalHom hU') := by
  refine (injective_iff_map_eq_one _).2 fun γ hγ ↦ ?_
  induction γ using QuotientGroup.induction_on with
  | H u =>
    rw [baseChangeGalHom_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hγ
    have hu : (u : G) ∈ U' := u.2
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, OpenSubgroup.mem_toSubgroup,
      baseChange_top, OpenSubgroup.mem_inf]
    exact ⟨hγ, hu⟩

/-- **The degree of the base change divides the degree of the layer.** -/
theorem degree_baseChange_dvd : (L.baseChange hU').degree ∣ L.degree := by
  rw [degree_eq_natCard_gal, degree_eq_natCard_gal]
  exact Subgroup.card_dvd_of_injective _ (L.baseChangeGalHom_injective hU')

/-- When the base change has the same degree as the layer, the homomorphism of Galois groups is
an isomorphism. -/
theorem baseChangeGalHom_bijective (hdeg : (L.baseChange hU').degree = L.degree) :
    Function.Bijective (L.baseChangeGalHom hU') :=
  (L.baseChangeGalHom_injective hU').bijective_of_nat_card_le
    (by rw [← degree_eq_natCard_gal, ← degree_eq_natCard_gal, hdeg])

/-- **The degree of a base change along a subgroup of index prime to the degree is unchanged.**
If `[U : U']` is prime to `[U : V]`, then `[U' : V ⊓ U'] = [U : V]`. -/
theorem degree_baseChange_of_coprime
    (hcop : (U'.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree) :
    (L.baseChange hU').degree = L.degree := by
  refine Nat.dvd_antisymm (L.degree_baseChange_dvd hU') (hcop.symm.dvd_of_dvd_mul_right ?_)
  -- Both `[U' : V ⊓ U'] * [U : U']` and `[U : V] * [V : V ⊓ U']` are the index of `V ⊓ U'` in `U`.
  refine ⟨(L.baseChange hU').top.toSubgroup.relIndex L.top.toSubgroup, ?_⟩
  rw [degree_eq_relIndex, degree_eq_relIndex, show U'.toSubgroup.relIndex L.ground.toSubgroup =
      (L.baseChange hU').ground.toSubgroup.relIndex L.ground.toSubgroup from rfl,
    Subgroup.relIndex_mul_relIndex _ _ _
      (OpenSubgroup.toSubgroup_le.2 (L.baseChange hU').top_le_ground)
      (OpenSubgroup.toSubgroup_le.2 (L.baseChange_ground_le hU')),
    mul_comm, Subgroup.relIndex_mul_relIndex _ _ _
      (OpenSubgroup.toSubgroup_le.2 (L.baseChange_top_le hU'))
      (OpenSubgroup.toSubgroup_le.2 L.top_le_ground)]

/-! ### Restriction and corestriction of norm quotients -/

variable (F : Formation G)

/-- When the base change has the same degree as the layer, the norm of an element of `A^V` along
the base change is its norm along the layer: the cosets of `V ⊓ U'` in `U'` are those of `V` in
`U`. -/
theorem coe_norm_baseChange (hdeg : (L.baseChange hU').degree = L.degree)
    (a : F.level L.top) :
    (dsimp% only ((L.baseChange hU').norm F
        (Submodule.inclusion (F.level_antitone (L.baseChange_top_le hU')) a) : F.toRep.V)) =
      L.norm F a := by
  rw [norm_apply_coe, norm_apply_coe]
  refine Fintype.sum_bijective _ (L.baseChangeGalHom_bijective hU' hdeg) _ _ fun γ ↦ ?_
  induction γ using QuotientGroup.induction_on with
  | H u =>
    rw [baseChangeGalHom_mk, rep_ρ_mk_apply_coe, rep_ρ_mk_apply_coe]
    rfl

/-- The **restriction** `A^U / N_{U/V}(A^V) → A^{U'} / N_{U'/(V ⊓ U')}(A^{V ⊓ U'})` of norm
quotients to the base change, induced by the inclusion `A^U ⊆ A^{U'}`. It is defined when the base
change has the same degree as the layer, which makes every norm of the layer a norm of its base
change. -/
def normQuotientRes (hdeg : (L.baseChange hU').degree = L.degree) :
    L.NormQuotient F →ₗ[ℤ] (L.baseChange hU').NormQuotient F :=
  Submodule.mapQ _ _ (Submodule.inclusion (F.level_antitone (L.baseChange_ground_le hU')))
    fun y hy ↦ by
      obtain ⟨a, rfl⟩ := (L.mem_normSubgroup F).1 hy
      refine Submodule.mem_comap.2 ((mem_normSubgroup _ F).2
        ⟨Submodule.inclusion (F.level_antitone (L.baseChange_top_le hU')) a, Subtype.ext ?_⟩)
      rw [L.coe_norm_baseChange hU' F hdeg, Submodule.coe_inclusion]

-- `dsimp% only` on the left-hand sides of this and `normQuotientCor_mk`, as explained in the
-- implementation notes of `Formation/Basic.lean`.
/-- Restriction sends the class of `x ∈ A^U` to the class of `x` in `A^{U'}`. -/
@[simp]
theorem normQuotientRes_mk (hdeg : (L.baseChange hU').degree = L.degree)
    (x : F.level L.ground) :
    (dsimp% only (L.normQuotientRes hU' F hdeg (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk
        (Submodule.inclusion (F.level_antitone (L.baseChange_ground_le hU')) x) :=
  (rfl)

/-- The **corestriction** `A^{U'} / N_{U'/(V ⊓ U')}(A^{V ⊓ U'}) → A^U / N_{U/V}(A^V)` of norm
quotients from the base change, induced by the norm `N_{U/U'} : A^{U'} → A^U`, which carries norms
of the base change to norms of the layer by transitivity of norms. -/
def normQuotientCor : (L.baseChange hU').NormQuotient F →ₗ[ℤ] L.NormQuotient F :=
  Submodule.mapQ _ _ (F.levelNorm (L.baseChange_ground_le hU')).toIntLinearMap fun y hy ↦ by
    obtain ⟨b, rfl⟩ := ((L.baseChange hU').mem_normSubgroup F).1 hy
    refine Submodule.mem_comap.2 ((L.mem_normSubgroup F).2
      ⟨F.levelNorm (L.baseChange_top_le hU') b, ?_⟩)
    -- `N_{U/U'} ∘ N_{U'/(V ⊓ U')} = N_{U/(V ⊓ U')} = N_{U/V} ∘ N_{V/(V ⊓ U')}`.
    have hn (L₀ : NormalLayer G) (x : F.level L₀.top) :
        L₀.norm F x = F.levelNorm L₀.top_le_ground x :=
      DFunLike.congr_fun (L₀.toAddMonoidHom_norm F) x
    rw [hn, hn, AddMonoidHom.coe_toIntLinearMap,
      ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, ← Formation.levelNorm_trans,
      ← Formation.levelNorm_trans]

/-- Corestriction sends the class of `y ∈ A^{U'}` to the class of its norm `N_{U/U'} y`. -/
@[simp]
theorem normQuotientCor_mk (y : F.level (L.baseChange hU').ground) :
    (dsimp% only (L.normQuotientCor hU' F (Submodule.Quotient.mk y))) =
      Submodule.Quotient.mk (F.levelNorm (L.baseChange_ground_le hU') y) :=
  (rfl)

/-- **Corestriction after restriction is multiplication by the index** `[U : U']`. -/
@[simp]
theorem normQuotientCor_normQuotientRes (hdeg : (L.baseChange hU').degree = L.degree)
    (x : L.NormQuotient F) :
    L.normQuotientCor hU' F (L.normQuotientRes hU' F hdeg x) =
      U'.toSubgroup.relIndex L.ground.toSubgroup • x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [normQuotientRes_mk, normQuotientCor_mk, Formation.levelNorm_inclusion,
      Submodule.Quotient.mk_smul, baseChange_ground]

/-- **Restriction to a base change of index prime to the degree is injective.** If `[U : U']` is
prime to `[U : V]`, then `A^U / N_{U/V}(A^V) → A^{U'} / N_{U'/(V ⊓ U')}(A^{V ⊓ U'})` is
injective: its kernel is killed by both `[U : U']` and `[U : V]`. -/
theorem normQuotientRes_injective
    (hcop : (U'.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree) :
    Function.Injective (L.normQuotientRes hU' F (L.degree_baseChange_of_coprime hU' hcop)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have h₁ : U'.toSubgroup.relIndex L.ground.toSubgroup • x = 0 := by
    rw [← L.normQuotientCor_normQuotientRes hU' F (L.degree_baseChange_of_coprime hU' hcop), hx,
      map_zero]
  rw [← AddMonoid.addOrderOf_eq_one_iff, ← Nat.dvd_one, ← hcop.gcd_eq_one]
  exact Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h₁)
    (addOrderOf_dvd_of_nsmul_eq_zero (L.degree_nsmul_eq_zero F x))

/-- **The norm quotient of a layer is no larger than that of a base change of index prime to the
degree.** If `[U : U']` is prime to `[U : V]`, then the order of `A^U / N_{U/V}(A^V)` divides the
order of `A^{U'} / N_{U'/(V ⊓ U')}(A^{V ⊓ U'})`. -/
theorem natCard_normQuotient_dvd_natCard_normQuotient_baseChange
    (hcop : (U'.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree) :
    Nat.card (L.NormQuotient F) ∣ Nat.card ((L.baseChange hU').NormQuotient F) :=
  AddSubgroup.card_dvd_of_injective (L.normQuotientRes hU' F
    (L.degree_baseChange_of_coprime hU' hcop)).toAddMonoidHom
    (L.normQuotientRes_injective hU' F hcop)

/-- **The bound on the norm index descends from a base change of index prime to the degree.** If
`[U : U']` is prime to `[U : V]` and the order of the norm quotient of the base change divides its
degree, then the order of the norm quotient `A^U / N_{U/V}(A^V)` divides `[U : V]`. -/
theorem natCard_normQuotient_dvd_degree_of_baseChange
    (hcop : (U'.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree)
    (h : Nat.card ((L.baseChange hU').NormQuotient F) ∣ (L.baseChange hU').degree) :
    Nat.card (L.NormQuotient F) ∣ L.degree :=
  (L.natCard_normQuotient_dvd_natCard_normQuotient_baseChange hU' F hcop).trans
    (L.degree_baseChange_of_coprime hU' hcop ▸ h)

end NormalLayer

end TauCeti.ClassFieldTheory
