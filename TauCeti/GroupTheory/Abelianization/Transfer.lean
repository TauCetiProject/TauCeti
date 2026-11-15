/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Transfer
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

* `Group.Abelianization.transfer_of` and `Group.Abelianization.transferOfInjective_of`: evaluation
  on the abelianization class of a group element.
* `Group.Abelianization.transfer_eq_prod_quotient_orbitRel_zpowers_quot` and
  `Group.Abelianization.transferOfInjective_eq_prod_quotient_orbitRel_zpowers_quot`: orbit-product
  formulas over the `⟨g⟩`-orbits on `G ⧸ H` and `G ⧸ f.range`.
* `Group.Abelianization.transfer_trans` and `Group.Abelianization.transferOfInjective_comp`:
  contravariant transitivity of the transfer in towers.
* `Group.Abelianization.map_subtype_transfer_of_comm` and
  `Group.Abelianization.map_transferOfInjective_of_comm`: when `G` is commutative, transfer
  followed by the map induced by inclusion raises every class to the `[G : H]`-th power.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
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

/-- On the class of `g ∈ G`, `transfer H` is Mathlib's `MonoidHom.transfer` of `of : H →* Hᵃᵇ`. -/
@[simp]
theorem transfer_of (H : Subgroup G) [H.FiniteIndex] (g : G) :
    transfer H (of g) = MonoidHom.transfer (of : H →* Group.Abelianization H) g :=
  (rfl)

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
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
    ⟨fun a b ↦ Quotient.inductionOn₂' a b fun _ _ ↦ QuotientGroup.eq.mpr (Subgroup.mem_top _)⟩
  have hbij : Function.Bijective fun _ : Unit ↦ ((1 : G) : G ⧸ (⊤ : Subgroup G)) :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun q ↦ ⟨(), Subsingleton.elim _ _⟩⟩
  rw [MonoidHom.comp_apply, transfer_of,
    MonoidHom.transfer_eq_prod_of_bijective _ (fun _ : Unit ↦ (1 : G)) hbij g id
      (fun _ ↦ Subsingleton.elim _ _)]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, inv_one, one_mul, mul_one,
    Finset.prod_singleton]
  rfl

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

open scoped IsMulCommutative in
/-- In a commutative group `G`, `transfer H` followed by `map H.subtype` raises every element of
`Gᵃᵇ` to the `[G : H]`-th power. -/
@[simp]
theorem map_subtype_transfer_of_comm [IsMulCommutative G] (H : Subgroup G) [H.FiniteIndex]
    (x : Group.Abelianization G) :
    map H.subtype (transfer H x) = x ^ H.index := by
  obtain ⟨g, rfl⟩ : ∃ g, of g = x := QuotientGroup.mk_surjective x
  rw [transfer_of_eq_of_pow, map_of, Subgroup.coe_subtype, ← map_pow]

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
@[simp]
theorem transferOfInjective_of (hf : Function.Injective f) [f.range.FiniteIndex] (g : G) :
    transferOfInjective hf (of g) =
      MonoidHom.transfer (of.comp (MonoidHom.ofInjective hf).symm.toMonoidHom) g :=
  (rfl)

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
  rw [transferOfInjective_of, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  rfl

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

/-- Transfer along the identity homomorphism is the identity on `Gᵃᵇ`. -/
@[simp]
theorem transferOfInjective_id :
    haveI : (MonoidHom.id G).range.FiniteIndex :=
      (MonoidHom.range_eq_top (f := MonoidHom.id G) |>.mpr Function.surjective_id).symm ▸
        inferInstance
    transferOfInjective (f := MonoidHom.id G) Function.injective_id = MonoidHom.id _ := by
  have : (MonoidHom.id G).range.FiniteIndex :=
    (MonoidHom.range_eq_top (f := MonoidHom.id G) |>.mpr Function.surjective_id).symm ▸
      inferInstance
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  have : Subsingleton (G ⧸ (MonoidHom.id G).range) :=
    ⟨fun a b ↦ Quotient.inductionOn₂' a b fun x y ↦ QuotientGroup.eq.mpr ⟨x⁻¹ * y, rfl⟩⟩
  have hbij : Function.Bijective fun _ : Unit ↦ ((1 : G) : G ⧸ (MonoidHom.id G).range) :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun q ↦ ⟨(), Subsingleton.elim _ _⟩⟩
  rw [MonoidHom.comp_apply, transferOfInjective_of,
    MonoidHom.transfer_eq_prod_of_bijective _ (fun _ : Unit ↦ (1 : G)) hbij g id
      (fun _ ↦ Subsingleton.elim _ _)]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, inv_one, one_mul, mul_one,
    Finset.prod_singleton, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
  congr 1
  exact (MonoidHom.ofInjective Function.injective_id).symm_apply_eq.mpr (Subtype.ext rfl)

/-- If `(f.comp f₁).range` has finite index and `f` is injective, then `f₁.range` has finite
index, being the preimage of `(f.comp f₁).range` under `f`. -/
theorem _root_.MonoidHom.finiteIndex_range_of_comp_injective {K : Type*} [Group K] (f₁ : K →* H)
    (hf₂ : Function.Injective f) [(f.comp f₁).range.FiniteIndex] : f₁.range.FiniteIndex := by
  simpa only [MonoidHom.range_comp, Subgroup.comap_map_eq_self_of_injective hf₂] using
    (inferInstance : ((f.comp f₁).range.comap f).FiniteIndex)

/-- **Contravariant functoriality of `transferOfInjective` in towers.** For injective homomorphisms
`f₁ : K →* H` and `f₂ : H →* G` whose composite has finite-index range in `G`, transferring along
`f₂.comp f₁` is transferring along `f₂` and then along `f₁`. -/
theorem transferOfInjective_comp {K : Type*} [Group K] {f₁ : K →* H}
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f)
    [(f.comp f₁).range.FiniteIndex] :
    haveI : f.range.FiniteIndex :=
      Subgroup.finiteIndex_of_le (MonoidHom.range_comp f f₁ ▸ Subgroup.map_le_range f f₁.range)
    haveI : f₁.range.FiniteIndex := f.finiteIndex_range_of_comp_injective f₁ hf₂
    transferOfInjective (f := f.comp f₁) (hf₂.comp hf₁) =
      (transferOfInjective (f := f₁) hf₁).comp (transferOfInjective (f := f) hf₂) := by
  have hle : (f.comp f₁).range ≤ f.range :=
    MonoidHom.range_comp f f₁ ▸ Subgroup.map_le_range f f₁.range
  have : f.range.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have : f₁.range.FiniteIndex := f.finiteIndex_range_of_comp_injective f₁ hf₂
  have hmap : f₁.range.map ((MonoidHom.ofInjective hf₂ : H ≃* f.range) : H →* f.range) =
      (f.comp f₁).range.subgroupOf f.range := by
    ext ⟨y, hy⟩
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, hxy⟩
      exact ⟨k, congrArg Subtype.val hxy⟩
    · rintro ⟨k, hk⟩
      exact ⟨f₁ k, ⟨k, rfl⟩, Subtype.ext hk⟩
  have htransport :
      (MonoidHom.transfer (of.comp (MonoidHom.ofInjective hf₁).symm.toMonoidHom)).comp
          (MonoidHom.ofInjective hf₂).symm.toMonoidHom =
        MonoidHom.transfer
          ((of.comp (MonoidHom.ofInjective (f := f.comp f₁) (hf₂.comp hf₁)).symm.toMonoidHom).comp
            (Subgroup.subgroupOfEquivOfLe hle : (f.comp f₁).range.subgroupOf f.range →* _)) := by
    ext z
    obtain ⟨m, rfl⟩ := (MonoidHom.ofInjective hf₂).surjective z
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    refine (MonoidHom.transfer_apply_of_mulEquiv _ (MonoidHom.ofInjective hf₂) hmap _
      (fun k ↦ ?_) m).symm
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    refine congrArg of (hf₁ (hf₂ ?_))
    have hk1 : f.comp f₁ ((MonoidHom.ofInjective (f := f.comp f₁) (hf₂.comp hf₁)).symm
        ((Subgroup.subgroupOfEquivOfLe hle :
          (f.comp f₁).range.subgroupOf f.range →* _)
          ⟨MonoidHom.ofInjective hf₂ k, hmap ▸ Subgroup.mem_map_of_mem _ k.2⟩)) =
        f k :=
      congrArg Subtype.val
        ((MonoidHom.ofInjective (f := f.comp f₁) (hf₂.comp hf₁)).apply_symm_apply _)
    have hk2 : f₁ ((MonoidHom.ofInjective hf₁).symm k) = (k : H) :=
      congrArg Subtype.val ((MonoidHom.ofInjective hf₁).apply_symm_apply k)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hk2] using hk1
  refine hom_ext _ _ (MonoidHom.ext fun g ↦ ?_)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    transferOfInjective_of, transferOfInjective_of,
    ← MonoidHom.comp_apply (transferOfInjective hf₁), ← MonoidHom.transfer_comp]
  have hcomp :
      (transferOfInjective (f := f₁) hf₁).comp
          (of.comp (MonoidHom.ofInjective hf₂).symm.toMonoidHom) =
        (MonoidHom.transfer (of.comp (MonoidHom.ofInjective hf₁).symm.toMonoidHom)).comp
          (MonoidHom.ofInjective hf₂).symm.toMonoidHom := by
    ext z
    exact transferOfInjective_of hf₁ _
  rw [hcomp, htransport, MonoidHom.transfer_transfer]

open scoped IsMulCommutative in
/-- In a commutative group `G`, `transferOfInjective hf` followed by `map f` raises every element
of `Gᵃᵇ` to the `[G : f(H)]`-th power. -/
@[simp]
theorem map_transferOfInjective_of_comm [IsMulCommutative G] (hf : Function.Injective f)
    [f.range.FiniteIndex] (x : Group.Abelianization G) :
    map f (transferOfInjective hf x) = x ^ f.range.index := by
  have hf_sub : map f ((MonoidHom.ofInjective hf).symm.abelianizationCongr (transfer f.range x)) =
      map f.range.subtype (transfer f.range x) := by
    obtain ⟨y, hy⟩ : ∃ y, of y = transfer f.range x := QuotientGroup.mk_surjective _
    rw [← hy]
    simp
  rw [transferOfInjective_eq_comp_transfer, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    hf_sub, map_subtype_transfer_of_comm]

end Injective

end Group.Abelianization
