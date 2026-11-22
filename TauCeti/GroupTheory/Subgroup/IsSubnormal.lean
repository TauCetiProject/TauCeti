/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Solvable
import TauCeti.GroupTheory.QuotientGroup.Subquotient

/-!
# Subnormal sections and simple composition factors of groups

A *subnormal section* of a group `G` is a quotient `H ⧸ K.subgroupOf H` with `H` subnormal in `G`
and `K ≤ H` normal in `H`. When this quotient is a simple group, it is a composition factor of any
subnormal series passing through `K` and `H`. For finite or infinite groups alike, simple subnormal
sections satisfy the Schreier–Jordan–Hölder dichotomy across any normal subgroup `N ⊴ G`: every
simple subnormal section of `G` is isomorphic either to a simple subnormal section of `N` or to a
simple subnormal section of `G ⧸ N`.

This file develops the predicate `TauCeti.HasSubnormalSection` and the subnormal-section
isomorphisms needed to classify simple subnormal sections of quotients, extensions, and finite
direct products without assuming the ambient group has finite composition length.

## Main definitions

* `Subgroup.IsSubnormal.quotientMulEquivOfIsSimpleGroup`: in a simple group `G`, any nontrivial
  subnormal section `H ⧸ K.subgroupOf H` (`K ≤ H`) is canonically isomorphic to `G`.
* `TauCeti.HasSubnormalSection`: `S` is isomorphic to `H ⧸ K.subgroupOf H` for some
  subnormal subgroup `H` of `G` and `K ≤ H` normal in `H`.

## Main results

* `TauCeti.HasSubnormalSection.or_of_normal`: across `N ⊴ G`, any simple subnormal
  section of `G` occurs as a subnormal section of `N` or of `G ⧸ N`.
* `TauCeti.HasSubnormalSection.or_of_prod` and
  `TauCeti.HasSubnormalSection.exists_of_pi`: any simple subnormal section of a binary or
  finite direct product occurs in one of the factors.

## References

* J. J. Rotman, *An Introduction to the Theory of Groups*, 4th ed., Graduate Texts in Mathematics
  148, Springer, 1995, §5.1 (subnormal series and the Zassenhaus/Jordan–Hölder butterfly).
-/

public section

open QuotientGroup

namespace Subgroup

/-! ### Nontrivial subnormal sections of simple groups -/

namespace IsSubnormal

variable {G : Type*} [Group G] {H K : Subgroup G}

/-- In a simple group `G`, any subnormal subgroup `H` that admits a nontrivial quotient
`H ⧸ K.subgroupOf H` is `⊤`. -/
@[to_additive]
theorem eq_top_of_nontrivial_quotient [IsSimpleGroup G] (hH : H.IsSubnormal) (K : Subgroup G)
    [(K.subgroupOf H).Normal] [Nontrivial (H ⧸ K.subgroupOf H)] : H = ⊤ := by
  rcases hH.eq_bot_or_top_of_isSimpleGroup ‹_› with rfl | htop
  · exact absurd (QuotientGroup.mk'_surjective _).subsingleton
      (not_subsingleton ((⊥ : Subgroup G) ⧸ K.subgroupOf ⊥))
  · exact htop

/-- In a simple group `G`, if `H` is subnormal, `K ≤ H` is normal in `H`, and `H ⧸ K.subgroupOf H`
is nontrivial, then `K = ⊥`. -/
@[to_additive]
theorem eq_bot_of_nontrivial_quotient [IsSimpleGroup G] (hH : H.IsSubnormal) (hKH : K ≤ H)
    [hKN : (K.subgroupOf H).Normal] [Nontrivial (H ⧸ K.subgroupOf H)] : K = ⊥ := by
  rcases (IsSubnormal.trans hKH hKN.isSubnormal hH).eq_bot_or_top_of_isSimpleGroup ‹_› with h | rfl
  · exact h
  · obtain rfl := hH.eq_top_of_nontrivial_quotient ⊤
    have : Subsingleton ((⊤ : Subgroup G) ⧸ (⊤ : Subgroup G).subgroupOf ⊤) := by
      rw [Subgroup.top_subgroupOf]
      exact QuotientGroup.subsingleton_quotient_top
    exact absurd this (not_subsingleton _)

/-- **A nontrivial subnormal section of a simple group is the group itself.** -/
@[to_additive /-- **A nontrivial subnormal section of a simple additive group is the group
itself.** -/]
noncomputable def quotientMulEquivOfIsSimpleGroup [IsSimpleGroup G] (hH : H.IsSubnormal)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal] [Nontrivial (H ⧸ K.subgroupOf H)] :
    (H ⧸ K.subgroupOf H) ≃* G :=
  subquotientEquivOfEqTopOfEqBot (hH.eq_top_of_nontrivial_quotient K)
    (hH.eq_bot_of_nontrivial_quotient hKH)

/-- Evaluation of `Subgroup.IsSubnormal.quotientMulEquivOfIsSimpleGroup` on coset
representatives. -/
@[to_additive (attr := simp) /-- Evaluation of
`AddSubgroup.IsSubnormal.quotientAddEquivOfIsSimpleAddGroup` on coset representatives. -/]
theorem quotientMulEquivOfIsSimpleGroup_mk [IsSimpleGroup G] (hH : H.IsSubnormal)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal] [Nontrivial (H ⧸ K.subgroupOf H)] (x : H) :
    hH.quotientMulEquivOfIsSimpleGroup hKH (QuotientGroup.mk x) = (x : G) :=
  subquotientEquivOfEqTopOfEqBot_mk _ _ x

end IsSubnormal

end Subgroup

/-! ### The subnormal-section predicate and Schreier–Jordan–Hölder splitting -/

namespace TauCeti

open Subgroup

/-- `TauCeti.HasSubnormalSection G S` means that `S` is multiplicatively isomorphic to a section
`H ⧸ K.subgroupOf H` of `G` with `H` subnormal in `G` and `K ≤ H` normal in `H`. When `S` is
simple, these sections are the composition factors appearing in subnormal chains of `G`. -/
def HasSubnormalSection (G : Type*) (S : Type*) [Group G] [Group S] : Prop :=
  ∃ H K : Subgroup G, H.IsSubnormal ∧ K ≤ H ∧
    ∃ (_ : (K.subgroupOf H).Normal), Nonempty ((H ⧸ K.subgroupOf H) ≃* S)

/-- Unfolding characterization of `TauCeti.HasSubnormalSection`. -/
theorem hasSubnormalSection_def (G : Type*) (S : Type*) [Group G] [Group S] :
    HasSubnormalSection G S ↔
      ∃ H K : Subgroup G, H.IsSubnormal ∧ K ≤ H ∧
        ∃ (_ : (K.subgroupOf H).Normal), Nonempty ((H ⧸ K.subgroupOf H) ≃* S) :=
  Iff.rfl

namespace HasSubnormalSection

variable {G G₁ G₂ Q S S' : Type*} [Group G] [Group G₁] [Group G₂] [Group Q] [Group S] [Group S']

/-- Any subnormal subgroup `H` and normal subgroup `K ≤ H` exhibit `H ⧸ K.subgroupOf H` as a
subnormal section of `G`. -/
theorem mk_quotient {H K : Subgroup G} (hH : H.IsSubnormal) (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] : HasSubnormalSection G (H ⧸ K.subgroupOf H) :=
  ⟨H, K, hH, hKH, inferInstance, ⟨MulEquiv.refl _⟩⟩

/-- Every group is a subnormal section of itself via `⊤ ⧸ ⊥`. -/
@[simp]
theorem refl (G : Type*) [Group G] : HasSubnormalSection G G :=
  ⟨⊤, ⊥, IsSubnormal.top, bot_le, inferInstance, ⟨subquotientEquivOfEqTopOfEqBot rfl rfl⟩⟩

/-- Transport a subnormal section along an isomorphism on the right. -/
theorem congr_right (h : HasSubnormalSection G S) (e : S ≃* S') : HasSubnormalSection G S' :=
  let ⟨H, K, hH, hKH, hKN, ⟨e₀⟩⟩ := h
  ⟨H, K, hH, hKH, hKN, ⟨e₀.trans e⟩⟩

/-- Pull back a subnormal section along a surjective group homomorphism. -/
theorem of_surjective {f : G →* Q} (hf : Function.Surjective f) (h : HasSubnormalSection Q S) :
    HasSubnormalSection G S :=
  let ⟨H, K, hH, hKH, _, ⟨e₀⟩⟩ := h
  ⟨H.comap f, K.comap f, hH.comap f, comap_mono hKH, normal_comap_subgroupOf f K H,
    ⟨(f.comapSubquotientEquivOfSurjective hf K H).trans e₀⟩⟩

/-- Transport a subnormal section along an isomorphism of ambient groups. -/
theorem congr_left (e : G ≃* Q) (h : HasSubnormalSection G S) : HasSubnormalSection Q S :=
  h.of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- Transitivity: a subnormal section of a subnormal subgroup `M` of `G` is a subnormal section of
`G`. -/
theorem of_isSubnormal {M : Subgroup G} (hM : M.IsSubnormal) (h : HasSubnormalSection M S) :
    HasSubnormalSection G S :=
  let ⟨H, K, hH, hKH, _, ⟨e₀⟩⟩ := h
  ⟨H.map M.subtype, K.map M.subtype, hH.trans' hM, map_mono hKH,
    normal_map_subtype_subgroupOf K H, ⟨(mapSubtypeSubquotientEquiv K H).symm.trans e₀⟩⟩

/-- Every simple subnormal section of a solvable group is commutative. -/
theorem isMulCommutative_of_isSolvable [Group.IsSolvable G] [IsSimpleGroup S]
    (h : HasSubnormalSection G S) : IsMulCommutative S := by
  rcases h with ⟨H, K, _, _, _, ⟨e⟩⟩
  have : Group.IsSolvable S := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr this)

/-- Every nontrivial subnormal section of a simple group is isomorphic to that group. -/
theorem nonempty_mulEquiv_of_isSimpleGroup [IsSimpleGroup G] [Nontrivial S]
    (h : HasSubnormalSection G S) : Nonempty (S ≃* G) := by
  rcases h with ⟨H, K, hH, hKH, _, ⟨e⟩⟩
  have := e.symm.injective.nontrivial
  exact ⟨e.symm.trans (hH.quotientMulEquivOfIsSimpleGroup hKH)⟩

/-- When `N ⊴ G` meets `H` inside `K`, the subnormal section `H ⧸ K.subgroupOf H` descends
unaltered to `(H.map (mk' N)) ⧸ (K.map (mk' N)).subgroupOf (H.map (mk' N))` in `G ⧸ N`. -/
private theorem of_normal_map_eq_bot {H K N : Subgroup G} [N.Normal] (hH : H.IsSubnormal)
    (hKH : K ≤ H) [hKN : (K.subgroupOf H).Normal] (e : (H ⧸ K.subgroupOf H) ≃* S)
    (hbot : (N.subgroupOf H).map (QuotientGroup.mk' (K.subgroupOf H)) = ⊥) :
    HasSubnormalSection (G ⧸ N) S := by
  let πN := QuotientGroup.mk' N
  let ψ : H →* H.map πN := πN.subgroupMap H
  have hψ_surj : Function.Surjective ψ := πN.subgroupMap_surjective H
  have hker_le : ψ.ker ≤ K.subgroupOf H := by
    rw [H.ker_subgroupMap πN, QuotientGroup.ker_mk']
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  have hmap : (K.subgroupOf H).map ψ = (K.map πN).subgroupOf (H.map πN) := by
    have hmem : K.map πN = ((K.subgroupOf H).map ψ).map (H.map πN).subtype := by
      conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [hmem, Subgroup.subgroupOf]
    exact (Subgroup.comap_map_eq_self_of_injective (H.map πN).subtype_injective _).symm
  have hK'N : ((K.map πN).subgroupOf (H.map πN)).Normal := hmap ▸ hKN.map ψ hψ_surj
  let eψ := QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj
  have heψ_map : ((K.subgroupOf H).map (QuotientGroup.mk' ψ.ker)).map eψ.toMonoidHom =
      (K.map πN).subgroupOf (H.map πN) := by
    rw [Subgroup.map_map]
    exact hmap
  exact ⟨H.map πN, K.map πN, hH.quotient, map_mono hKH, hK'N,
    ⟨(QuotientGroup.congr _ _ eψ heψ_map).symm.trans
      ((QuotientGroup.quotientQuotientEquivQuotient ψ.ker (K.subgroupOf H) hker_le).trans e)⟩⟩

/-- When `(N ∩ H)` surjects onto `H ⧸ K.subgroupOf H`, the section is realized inside `N` via
`H.subgroupOf N` and `K.subgroupOf N`. -/
private theorem of_normal_map_eq_top {H K N : Subgroup G} (hH : H.IsSubnormal)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal] (e : (H ⧸ K.subgroupOf H) ≃* S)
    (htop : (N.subgroupOf H).map (QuotientGroup.mk' (K.subgroupOf H)) = ⊤) :
    HasSubnormalSection N S := by
  let α : H.subgroupOf N →* H := ⟨⟨fun x ↦ ⟨x.val.val, x.property⟩, rfl⟩, fun _ _ ↦ rfl⟩
  let ω := (QuotientGroup.mk' (K.subgroupOf H)).comp α
  have hω_surj : Function.Surjective ω := fun q ↦ by
    rcases mem_map.mp (htop.symm ▸ mem_top q) with ⟨y, hyN, rfl⟩
    exact ⟨⟨⟨y.val, hyN⟩, y.property⟩, rfl⟩
  have hker : ω.ker = (K.subgroupOf N).subgroupOf (H.subgroupOf N) := by
    ext x; exact QuotientGroup.eq_one_iff _
  have hKNN : ((K.subgroupOf N).subgroupOf (H.subgroupOf N)).Normal := hker ▸ ω.normal_ker
  exact ⟨H.subgroupOf N, K.subgroupOf N, hH.subgroupOf, subgroupOf_mono N hKH, hKNN,
    ⟨(QuotientGroup.liftEquiv _ (φ := ω) hω_surj hker.symm).trans e⟩⟩

/-- **Schreier–Jordan–Hölder dichotomy across a normal subgroup.** Let `N` be a normal subgroup of
`G` and `S` a simple group. Every subnormal section of `G` isomorphic to `S` arises either as a
subnormal section of `N` or as a subnormal section of `G ⧸ N`. -/
theorem or_of_normal [IsSimpleGroup S] (h : HasSubnormalSection G S) (N : Subgroup G)
    [N.Normal] : HasSubnormalSection N S ∨ HasSubnormalSection (G ⧸ N) S := by
  rcases h with ⟨H, K, hH, hKH, _, ⟨e⟩⟩
  have := e.isSimpleGroup
  have hMN := (normal_subgroupOf (H := H) (N := N)).map (QuotientGroup.mk' (K.subgroupOf H))
    (QuotientGroup.mk'_surjective _)
  rcases hMN.eq_bot_or_eq_top with hbot | htop
  · exact Or.inr (of_normal_map_eq_bot hH hKH e hbot)
  · exact Or.inl (of_normal_map_eq_top hH hKH e htop)

/-- Every simple subnormal section of `G₁ × G₂` occurs as a subnormal section of `G₁` or of
`G₂`. -/
theorem or_of_prod [IsSimpleGroup S] (h : HasSubnormalSection (G₁ × G₂) S) :
    HasSubnormalSection G₁ S ∨ HasSubnormalSection G₂ S := by
  let N := (MonoidHom.snd G₁ G₂).ker
  rcases h.or_of_normal N with h₁ | h₂
  · exact Or.inl <| h₁.congr_left <|
      (MulEquiv.subgroupCongr MonoidHom.ker_snd).trans
        (((Subgroup.prodEquiv ..).trans .prodUnique).trans Subgroup.topEquiv)
  · exact Or.inr <| h₂.congr_left <|
      QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.snd G₁ G₂) Prod.snd_surjective

/-- Every simple subnormal section of a finite direct product `∀ i, G i` occurs in at least one
factor `G i`. -/
theorem exists_of_pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)] [IsSimpleGroup S]
    (h : HasSubnormalSection (∀ i, G i) S) : ∃ i : ι, HasSubnormalSection (G i) S := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨a, ha⟩ := ih
      (h.congr_left { (Equiv.piCongrLeft G e).symm with map_mul' := fun _ _ ↦ rfl })
    exact ⟨e a, ha⟩
  | h_empty =>
    rcases h with ⟨_, _, _, _, _, ⟨eS⟩⟩
    exact absurd (eS.surjective.comp (QuotientGroup.mk'_surjective _)).subsingleton
      (not_subsingleton S)
  | h_option ih =>
    rcases (h.congr_left { Equiv.piOptionEquivProd with map_mul' := fun _ _ ↦ rfl }).or_of_prod with
      hnone | hsome
    · exact ⟨none, hnone⟩
    · obtain ⟨a, ha⟩ := ih hsome; exact ⟨some a, ha⟩

end HasSubnormalSection

end TauCeti
