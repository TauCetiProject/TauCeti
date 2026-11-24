/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Transfer
public import TauCeti.GroupTheory.Index.Basic
import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.GroupTheory.Transfer.Basic

/-!
# The group-theoretic transfer on abelianizations

Let `H` be a finite-index subgroup of a group `G`. Mathlib's group-theoretic transfer
`MonoidHom.transfer` sends `of : H →* Group.Abelianization H` to a homomorphism
`G →* Group.Abelianization H`, which factors through the universal property of
`Group.Abelianization G` to give the **transfer (Verlagerung)**

```text
Group.Abelianization.transfer H : Group.Abelianization G →* Group.Abelianization H.
```

More generally, an injective homomorphism `f : H →* G` whose range has finite index in `G`
induces `Group.Abelianization.transferOfInjective hf : Group.Abelianization G →*
Group.Abelianization H` by transporting along the equivalence `H ≃* f.range`. For a restriction of
open normal layers of a profinite group, `(transferOfInjective T.galHom_injective).toAdditive` is
`TauCeti.ClassFieldTheory.LayerRestriction.transferHom`.

## Main definitions

* `Group.Abelianization.transfer H`: the transfer `Gᵃᵇ →* Hᵃᵇ` for a finite-index subgroup `H ≤ G`.
* `Group.Abelianization.transferOfInjective hf`: the transfer `Gᵃᵇ →* Hᵃᵇ` along an injective
  homomorphism `f : H →* G` with finite-index range.

## Main results

* `Group.Abelianization.lift_transfer_of` and `Group.Abelianization.lift_transfer`: simp normal
  form and universal-property factorization of `MonoidHom.transfer` through `transfer H`.
* `Group.Abelianization.transfer_of` and `Group.Abelianization.transferOfInjective_of`: evaluation
  on the abelianization class of a group element.
* `Group.Abelianization.transfer_eq_prod_quotient_orbitRel_zpowers_quot` and
  `Group.Abelianization.transferOfInjective_eq_prod_quotient_orbitRel_zpowers_quot`: orbit-product
  formulas over the `⟨g⟩`-orbits on `G ⧸ H` and `G ⧸ f.range`.
* `Group.Abelianization.transfer_trans` and `Group.Abelianization.transferOfInjective_comp`:
  contravariant transitivity of the transfer in towers.
* `Group.Abelianization.map_subtype_transfer` and `Group.Abelianization.map_transferOfInjective`:
  transfer followed by the map induced by inclusion raises every class in `Gᵃᵇ` to the
  `[G : H]`-th power.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
* J.-P. Serre, *Local Fields*, Chapter VII, §8.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII and Chapter XIV, §5.
-/

public noncomputable section

namespace Group.Abelianization

open MulAction Subgroup

variable {G : Type*} [Group G]

/-! ### Transfer to a finite-index subgroup -/

/-- The **group-theoretic transfer (Verlagerung)** `Gᵃᵇ →* Hᵃᵇ` to a finite-index subgroup `H ≤ G`:
Mathlib's `MonoidHom.transfer` applied to `of : H →* Hᵃᵇ`, descended through `of : G →* Gᵃᵇ`. -/
def transfer (H : Subgroup G) [H.FiniteIndex] :
    Group.Abelianization G →* Group.Abelianization H :=
  lift (MonoidHom.transfer (of : H →* Group.Abelianization H))

/-- Use `Group.Abelianization.transfer` as the preferred `simp` normal form for `lift` of
`MonoidHom.transfer of`. -/
@[simp]
theorem lift_transfer_of (H : Subgroup G) [H.FiniteIndex] :
    lift (MonoidHom.transfer (of : H →* Group.Abelianization H)) = transfer H :=
  (rfl)

/-- On the class of `g ∈ G`, `transfer H` is Mathlib's `MonoidHom.transfer` of `of : H →* Hᵃᵇ`. -/
theorem transfer_of (H : Subgroup G) [H.FiniteIndex] (g : G) :
    transfer H (of g) = MonoidHom.transfer (of : H →* Group.Abelianization H) g :=
  (rfl)

open scoped IsMulCommutative in
/-- Universal-property factorization of `MonoidHom.transfer` through
`Group.Abelianization.transfer`: for any commutative group `A` and homomorphism `ϕ : H →* A`, the
transfer of `ϕ` descended to `Gᵃᵇ` factors as `transfer H` followed by `lift ϕ`. -/
theorem lift_transfer {A : Type*} [Group A] [IsMulCommutative A] (H : Subgroup G) [H.FiniteIndex]
    (ϕ : H →* A) :
    lift (MonoidHom.transfer ϕ) = (lift ϕ).comp (transfer H) := by
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  rw [MonoidHom.comp_apply, lift_apply_of, MonoidHom.comp_apply, MonoidHom.comp_apply, transfer_of,
    ← MonoidHom.comp_apply (lift ϕ), ← MonoidHom.transfer_comp, ← lift_symm_apply,
    lift.symm_apply_apply]

/-- **Orbit-product formula for the abelianized transfer.** On the class of `g ∈ G`, `transfer H`
is the product over the `⟨g⟩`-orbits `q` in `G ⧸ H` of the classes of
`g_q⁻¹ * g ^ m_q * g_q ∈ H`, where `g_q H = q.out` and `m_q` is the minimal period of `g` on
`q.out`. -/
theorem transfer_eq_prod_quotient_orbitRel_zpowers_quot (H : Subgroup G) [H.FiniteIndex] (g : G)
    [Fintype (Quotient (orbitRel (zpowers g) (G ⧸ H)))] :
    transfer H (of g) =
      ∏ q : Quotient (orbitRel (zpowers g) (G ⧸ H)),
        of ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H g q.out⟩ := by
  rw [transfer_of, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]

/-- Transfer to the improper subgroup `⊤ ≤ G` is the inverse of the isomorphism `(⊤ : Subgroup G)ᵃᵇ
≃* Gᵃᵇ`. -/
@[simp]
theorem transfer_top :
    transfer (⊤ : Subgroup G) =
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.abelianizationCongr.toMonoidHom := by
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  have hbij : Function.Bijective fun _ : Unit ↦ ((1 : G) : G ⧸ (⊤ : Subgroup G)) :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun q ↦ ⟨(), Subsingleton.elim _ _⟩⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, transfer_of,
    Group.abelianizationCongr_of,
    MonoidHom.transfer_eq_prod_of_bijective _ (fun _ : Unit ↦ (1 : G)) hbij g id
      (fun _ ↦ Subsingleton.elim _ _)]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, inv_one, one_mul, mul_one,
    Finset.prod_singleton]
  exact congrArg of ((Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm_apply_eq.mpr (by simp)).symm

/-- **Transitivity of the abelianized transfer.** For `K ≤ H ≤ G` with `K` of finite index in `G`,
transferring from `G` to `H` and then from `H` to `K.subgroupOf H` agrees, after `K.subgroupOf H ≃*
K`, with transferring directly from `G` to `K`. -/
theorem transfer_trans {K H : Subgroup G} (hKH : K ≤ H) [K.FiniteIndex] :
    haveI := Subgroup.finiteIndex_of_le hKH
    (map (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom).comp
        ((transfer (K.subgroupOf H)).comp (transfer H)) =
      transfer K := by
  have := Subgroup.finiteIndex_of_le hKH
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  simp only [MonoidHom.comp_apply, transfer_of]
  have hmap :
      (map (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom).comp
          (lift (MonoidHom.transfer (of : K.subgroupOf H →* _))) =
        lift (MonoidHom.transfer
          ((of : K →* Group.Abelianization K).comp
            (Subgroup.subgroupOfEquivOfLe hKH : K.subgroupOf H →* K))) := by
    refine hom_ext _ _ (MonoidHom.ext fun h ↦ ?_)
    simp only [MonoidHom.comp_apply, lift_apply_of]
    have hof :
        (map (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom).comp
            (of : K.subgroupOf H →* Group.Abelianization (K.subgroupOf H)) =
          (of : K →* Group.Abelianization K).comp
            (Subgroup.subgroupOfEquivOfLe hKH : K.subgroupOf H →* K) := by
      ext
      simp
    rw [← MonoidHom.comp_apply (map _), ← MonoidHom.transfer_comp, hof]
  rw [transfer, ← MonoidHom.comp_apply (map _), hmap, ← MonoidHom.comp_apply (lift _),
    ← MonoidHom.transfer_comp, ← lift_symm_apply, lift.symm_apply_apply,
    MonoidHom.transfer_transfer]

open scoped IsMulCommutative in
/-- In a commutative group `G`, `transfer H` sends `of g` to `of ⟨g ^ [G : H], _⟩`. -/
theorem transfer_of_eq_of_pow [IsMulCommutative G] (H : Subgroup G) [H.FiniteIndex] (g : G) :
    haveI : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k :=
      fun k g₀ _ ↦ by rw [inv_mul_cancel_comm]
    transfer H (of g) =
      of ⟨g ^ H.index, MonoidHom.transfer_eq_pow_aux g this⟩ := by
  rw [transfer_of]
  exact MonoidHom.transfer_eq_pow (of : H →* Group.Abelianization H) g
    fun k g₀ _ ↦ by rw [inv_mul_cancel_comm]

/-- For any finite-index subgroup `H ≤ G`, `transfer H` followed by `map H.subtype` raises every
element of `Gᵃᵇ` to the `[G : H]`-th power. -/
@[simp]
theorem map_subtype_transfer (H : Subgroup G) [H.FiniteIndex] (x : Group.Abelianization G) :
    map H.subtype (transfer H x) = x ^ H.index := by
  classical
  obtain ⟨g, rfl⟩ : ∃ g, of g = x := QuotientGroup.mk_surjective x
  let := H.fintypeQuotientOfFiniteIndex
  rw [transfer_eq_prod_quotient_orbitRel_zpowers_quot, map_prod]
  simp only [map_of, Subgroup.coe_subtype, of_inv_mul_mul, map_pow, Finset.prod_pow_eq_pow_sum,
    ← Subgroup.index_eq_sum_minimalPeriod H g]

/-! ### Transfer along an injective homomorphism -/

section Injective

variable {H : Type*} [Group H] {f : H →* G}

/-- The **group-theoretic transfer** `Gᵃᵇ →* Hᵃᵇ` along an injective homomorphism `f : H →* G`
whose range has finite index in `G`: Mathlib's `MonoidHom.transfer` of `f.range ≃* H →* Hᵃᵇ`,
descended through `of : G →* Gᵃᵇ`. -/
def transferOfInjective (hf : Function.Injective f) [f.range.FiniteIndex] :
    Group.Abelianization G →* Group.Abelianization H :=
  lift (MonoidHom.transfer (of.comp (MonoidHom.ofInjective hf).symm.toMonoidHom))

/-- On the class of `g ∈ G`, `transferOfInjective hf` is `MonoidHom.transfer` of the inverse
equivalence `f.range ≃* H` composed with `of : H →* Hᵃᵇ`. -/
theorem transferOfInjective_of (hf : Function.Injective f) [f.range.FiniteIndex] (g : G) :
    transferOfInjective hf (of g) =
      MonoidHom.transfer (of.comp (MonoidHom.ofInjective hf).symm.toMonoidHom) g :=
  (rfl)

/-- `transferOfInjective` depends only on the homomorphism `f`, not on its presentation or proof of
injectivity. -/
theorem transferOfInjective_congr {f' : H →* G} (h : f = f') (hf : Function.Injective f)
    (hf' : Function.Injective f') [f.range.FiniteIndex] [f'.range.FiniteIndex] :
    transferOfInjective hf = transferOfInjective hf' := by
  subst h
  rfl

/-- `transferOfInjective hf` factors as `transfer f.range` followed by the equivalence
`f.rangeᵃᵇ ≃* Hᵃᵇ` inverse to `f`. -/
theorem transferOfInjective_eq_comp_transfer (hf : Function.Injective f) [f.range.FiniteIndex] :
    transferOfInjective hf =
      (MonoidHom.ofInjective hf).symm.abelianizationCongr.toMonoidHom.comp (transfer f.range) := by
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  have hmap :
      of.comp (MonoidHom.ofInjective hf).symm.toMonoidHom =
        (MonoidHom.ofInjective hf).symm.abelianizationCongr.toMonoidHom.comp
          (of : f.range →* Group.Abelianization f.range) := by
    ext
    simp
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, transferOfInjective_of,
    transfer_of, hmap, MonoidHom.transfer_comp, MonoidHom.comp_apply]

/-- Orbit-product formula for `transferOfInjective hf` on the class of `g ∈ G`. -/
theorem transferOfInjective_eq_prod_quotient_orbitRel_zpowers_quot
    (hf : Function.Injective f) [f.range.FiniteIndex] (g : G)
    [Fintype (Quotient (orbitRel (zpowers g) (G ⧸ f.range)))] :
    transferOfInjective hf (of g) =
      ∏ q : Quotient (orbitRel (zpowers g) (G ⧸ f.range)),
        of ((MonoidHom.ofInjective hf).symm
          ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem f.range g q.out⟩) := by
  simp only [transferOfInjective_of, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- For the inclusion of a finite-index subgroup `S ≤ G`, `transferOfInjective` is `transfer S`. -/
@[simp]
theorem transferOfInjective_subtype (S : Subgroup G) [S.FiniteIndex] :
    haveI : S.subtype.range.FiniteIndex := (Subgroup.range_subtype S).symm ▸ inferInstance
    transferOfInjective S.subtype_injective = transfer S := by
  have : S.subtype.range.FiniteIndex := (Subgroup.range_subtype S).symm ▸ inferInstance
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, transferOfInjective_of, transfer_of]
  let e : G ≃* G := MulEquiv.refl G
  have he : S.map (e : G →* G) = S.subtype.range := by simp [e]
  exact MonoidHom.transfer_apply_of_mulEquiv (of : S →* Group.Abelianization S) e he _
    (fun s ↦ by
      rw [MonoidHom.comp_apply]
      refine congrArg of (S.subtype_injective ?_)
      simp [e]) g

/-- Transfer along a bijective homomorphism `f : H →* G` is the abelianization equivalence induced
by the inverse of `f`. -/
theorem transferOfInjective_of_surjective (hf : Function.Injective f)
    (hsurj : Function.Surjective f) :
    haveI : f.range.FiniteIndex :=
      (MonoidHom.range_eq_top.mpr hsurj).symm ▸ inferInstance
    transferOfInjective hf =
      (MulEquiv.ofBijective f ⟨hf, hsurj⟩).symm.abelianizationCongr.toMonoidHom := by
  have : f.range.FiniteIndex :=
    (MonoidHom.range_eq_top.mpr hsurj).symm ▸ inferInstance
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  let e : G ≃* G := MulEquiv.refl G
  let e_bij : H ≃* G := MulEquiv.ofBijective f ⟨hf, hsurj⟩
  have he : (⊤ : Subgroup G).map (e : G →* G) = f.range := by
    simp [e, MonoidHom.range_eq_top.mpr hsurj]
  have hpoint :
      MonoidHom.transfer (of.comp (MonoidHom.ofInjective hf).symm.toMonoidHom) (e g) =
        MonoidHom.transfer
          ((e_bij.symm.abelianizationCongr.toMonoidHom.comp
              (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).abelianizationCongr.toMonoidHom).comp
            (of : (⊤ : Subgroup G) →* Group.Abelianization (⊤ : Subgroup G))) g :=
    MonoidHom.transfer_apply_of_mulEquiv _ e he _ (fun s ↦ by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Group.abelianizationCongr_of,
        Subgroup.topEquiv_apply]
      refine congrArg of (hf ?_)
      have hs : f (e_bij.symm (s : G)) = (s : G) := e_bij.apply_symm_apply (s : G)
      simp [e, hs]) g
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Group.abelianizationCongr_of, transferOfInjective_of]
  simpa only [e, e_bij, MulEquiv.refl_apply, MonoidHom.transfer_comp, ← transfer_of, transfer_top,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Group.abelianizationCongr_of,
    MulEquiv.apply_symm_apply] using hpoint

/-- Transfer along the identity homomorphism is the identity on `Gᵃᵇ`. -/
@[simp]
theorem transferOfInjective_id :
    haveI : (MonoidHom.id G).range.FiniteIndex :=
      (MonoidHom.range_eq_top (f := MonoidHom.id G) |>.mpr Function.surjective_id).symm ▸
        inferInstance
    transferOfInjective (f := MonoidHom.id G) Function.injective_id = MonoidHom.id _ := by
  rw [transferOfInjective_of_surjective Function.injective_id Function.surjective_id]
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Group.abelianizationCongr_of,
    MonoidHom.id_apply]
  let e_id : G ≃* G :=
    MulEquiv.ofBijective (MonoidHom.id G) ⟨Function.injective_id, Function.surjective_id⟩
  have hid : MonoidHom.id G (e_id.symm g) = g := e_id.apply_symm_apply g
  rw [MonoidHom.id_apply] at hid
  exact congrArg of hid

/-- **Contravariant functoriality of `transferOfInjective` in towers.** For injective homomorphisms
`f₁ : K →* H` and `f₂ : H →* G` whose composite has finite-index range in `G`, transferring along
`f₂.comp f₁` is transferring along `f₂` and then along `f₁`. -/
theorem transferOfInjective_comp {K : Type*} [Group K] {f₁ : K →* H} {f₂ : H →* G}
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂)
    [(f₂.comp f₁).range.FiniteIndex] :
    haveI : f₂.range.FiniteIndex :=
      Subgroup.finiteIndex_of_le (MonoidHom.range_comp f₂ f₁ ▸ Subgroup.map_le_range f₂ f₁.range)
    haveI : f₁.range.FiniteIndex := f₁.finiteIndex_range_of_injective_comp f₂ hf₂
    transferOfInjective (f := f₂.comp f₁) (hf₂.comp hf₁) =
      (transferOfInjective (f := f₁) hf₁).comp (transferOfInjective (f := f₂) hf₂) := by
  have hle : (f₂.comp f₁).range ≤ f₂.range :=
    MonoidHom.range_comp f₂ f₁ ▸ Subgroup.map_le_range f₂ f₁.range
  have : f₂.range.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have : f₁.range.FiniteIndex := f₁.finiteIndex_range_of_injective_comp f₂ hf₂
  -- Factor each `transferOfInjective` through `transfer` and apply `transfer_trans` to
  -- `(f₂.comp f₁).range ≤ f₂.range ≤ G`.
  rw [transferOfInjective_eq_comp_transfer (f := f₂.comp f₁) (hf₂.comp hf₁), ← transfer_trans hle,
    transferOfInjective_eq_comp_transfer (f := f₂) hf₂]
  simp only [← MonoidHom.comp_assoc]
  refine congrArg (MonoidHom.comp · (transfer f₂.range)) ?_
  apply hom_ext
  ext z
  -- Transport `transfer f₁.range` along the subgroup equivalence `MonoidHom.ofInjective hf₂`.
  obtain ⟨m, rfl⟩ := (MonoidHom.ofInjective hf₂).surjective z
  have hmap : f₁.range.map ((MonoidHom.ofInjective hf₂ : H ≃* f₂.range) : H →* f₂.range) =
      (f₂.comp f₁).range.subgroupOf f₂.range := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, MonoidHom.mem_range, Subgroup.mem_subgroupOf,
      MonoidHom.comp_apply]
    exact ⟨fun ⟨_, ⟨k, rfl⟩, hxy⟩ ↦ ⟨k, congrArg Subtype.val hxy⟩,
      fun ⟨k, hk⟩ ↦ ⟨f₁ k, ⟨k, rfl⟩, Subtype.ext hk⟩⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Group.abelianizationCongr_of,
    MulEquiv.symm_apply_apply, transferOfInjective_of, transfer_of]
  rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.comp_apply _ (map _),
    ← MonoidHom.comp_apply _ (MonoidHom.transfer _), ← MonoidHom.transfer_comp]
  refine MonoidHom.transfer_apply_of_mulEquiv
    (of.comp (MonoidHom.ofInjective hf₁).symm.toMonoidHom)
    (MonoidHom.ofInjective hf₂) hmap _ (fun k ↦ ?_) m
  simp only [MonoidHom.comp_apply, map_of, MulEquiv.coe_toMonoidHom, Group.abelianizationCongr_of]
  refine congrArg of (hf₁ (hf₂ ?_))
  simp [← MonoidHom.comp_apply f₂ f₁, MonoidHom.ofInjective_apply]

/-- For any injective homomorphism `f : H →* G` with finite-index range, `transferOfInjective hf`
followed by `map f` raises every element of `Gᵃᵇ` to the `[G : f(H)]`-th power. -/
@[simp]
theorem map_transferOfInjective (hf : Function.Injective f) [f.range.FiniteIndex]
    (x : Group.Abelianization G) :
    map f (transferOfInjective hf x) = x ^ f.range.index := by
  have hf_sub : map f ((MonoidHom.ofInjective hf).symm.abelianizationCongr (transfer f.range x)) =
      map f.range.subtype (transfer f.range x) := by
    obtain ⟨y, hy⟩ : ∃ y, of y = transfer f.range x := QuotientGroup.mk_surjective _
    rw [← hy]
    simp
  rw [transferOfInjective_eq_comp_transfer, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    hf_sub, map_subtype_transfer]

end Injective

end Group.Abelianization
