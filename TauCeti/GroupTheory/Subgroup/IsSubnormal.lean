/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Solvable

/-!
# Subnormal sections and simple composition factors of groups

A *subnormal section* of a group `G` is a quotient `H ⧸ K.subgroupOf H` with `H` subnormal in `G`
and `K ≤ H` normal in `H`. When this quotient is a simple group, it is a composition factor of any
subnormal series passing through `K` and `H`. For finite or infinite groups alike, simple subnormal
sections satisfy the Schreier–Jordan–Hölder dichotomy across any normal subgroup `N ⊴ G`: every
simple subnormal section of `G` is isomorphic either to a simple subnormal section of `N` or to a
simple subnormal section of `G ⧸ N`.

This file develops the subquotient isomorphisms and the predicate
`TauCeti.HasSubnormalSection` needed to classify simple subnormal sections of quotients,
extensions, and finite direct products without assuming the ambient group has finite composition
length.

## Main definitions

* `MonoidHom.comapSubquotientEquivOfSurjective`: a surjective homomorphism `f : G →* Q` identifies
  `(H.comap f) ⧸ (K.comap f).subgroupOf (H.comap f)` with `H ⧸ K.subgroupOf H`.
* `Subgroup.mapSubtypeSubquotientEquiv`: for subgroups `K, H ≤ M`, mapping through `M.subtype`
  identifies `(H.map M.subtype) ⧸ (K.map M.subtype).subgroupOf (H.map M.subtype)` with
  `H ⧸ K.subgroupOf H`.
* `Subgroup.IsSubnormal.quotientMulEquivOfIsSimpleGroup`: in a simple group `G`, any nontrivial
  subnormal section `H ⧸ K.subgroupOf H` (`K ≤ H`) is canonically isomorphic to `G`.
* `TauCeti.HasSubnormalSection`: `S` is isomorphic to `H ⧸ K.subgroupOf H` for some
  subnormal subgroup `H` of `G` and `K ≤ H` normal in `H`.

## Main results

* `IsSimpleGroup.isMulCommutative_of_isSolvable`: a simple solvable group is commutative
  (`IsMulCommutative` form of `IsSimpleGroup.comm_iff_isSolvable`).
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

/-! ### Simple solvable groups -/

/-- A simple group that is also solvable is commutative: `IsMulCommutative` form of
`IsSimpleGroup.comm_iff_isSolvable`. -/
@[to_additive /-- A simple additive group that is also solvable is commutative. -/]
theorem IsSimpleGroup.isMulCommutative_of_isSolvable (G : Type*) [Group G]
    [IsSimpleGroup G] [Group.IsSolvable G] : IsMulCommutative G :=
  IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr ‹_›)

namespace Subgroup

/-- Every simple section `H ⧸ K.subgroupOf H` of a solvable group is commutative. -/
theorem isMulCommutative_quotient_of_isSolvable {G : Type*} [Group G] [Group.IsSolvable G]
    (H K : Subgroup G) [(K.subgroupOf H).Normal] [IsSimpleGroup (H ⧸ K.subgroupOf H)] :
    IsMulCommutative (H ⧸ K.subgroupOf H) :=
  IsSimpleGroup.isMulCommutative_of_isSolvable (H ⧸ K.subgroupOf H)

/-! ### Subquotients along homomorphisms and inclusions -/

section Subquotients

variable {G Q : Type*} [Group G] [Group Q]

/-- Pulling back two subgroups along `f : G →* Q` and restricting one to the other agrees with
pulling back `K.subgroupOf H` along `f.subgroupComap H`. -/
@[to_additive /-- Pulling back two additive subgroups along `f : G →+ Q` and restricting one to
the other agrees with pulling back `K.addSubgroupOf H` along `f.addSubgroupComap H`. -/]
theorem comap_subgroupOf (f : G →* Q) (K H : Subgroup Q) :
    (K.comap f).subgroupOf (H.comap f) = (K.subgroupOf H).comap (f.subgroupComap H) :=
  rfl

/-- Normality of `K.subgroupOf H` pulls back along any group homomorphism `f : G →* Q`. -/
@[to_additive /-- Normality of `K.addSubgroupOf H` pulls back along any additive group
homomorphism `f : G →+ Q`. -/]
instance normal_comap_subgroupOf (f : G →* Q) (K H : Subgroup Q)
    [hN : (K.subgroupOf H).Normal] :
    ((K.comap f).subgroupOf (H.comap f)).Normal := by
  rw [comap_subgroupOf]; exact hN.comap _

/-- The kernel of `x ↦ f x mod (K.subgroupOf H)` on `H.comap f` is
`(K.comap f).subgroupOf (H.comap f)`. -/
@[to_additive]
theorem _root_.MonoidHom.ker_mk'_comp_subgroupComap (f : G →* Q) (K H : Subgroup Q)
    [(K.subgroupOf H).Normal] :
    ((QuotientGroup.mk' (K.subgroupOf H)).comp (f.subgroupComap H)).ker =
      (K.comap f).subgroupOf (H.comap f) := by
  ext x; exact QuotientGroup.eq_one_iff _

/-- **A surjective group homomorphism identifies subquotients.** Given `f : G →* Q` surjective and
subgroups `K, H` of `Q` with `K.subgroupOf H` normal, the subquotient of their preimages is
canonically isomorphic to `H ⧸ K.subgroupOf H`. -/
@[to_additive /-- **A surjective additive group homomorphism identifies subquotients.** -/]
noncomputable def _root_.MonoidHom.comapSubquotientEquivOfSurjective (f : G →* Q)
    (hf : Function.Surjective f) (K H : Subgroup Q) [(K.subgroupOf H).Normal] :
    ((H.comap f) ⧸ (K.comap f).subgroupOf (H.comap f)) ≃* (H ⧸ K.subgroupOf H) :=
  (QuotientGroup.quotientMulEquivOfEq (f.ker_mk'_comp_subgroupComap K H).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp (f.subgroupComap_surjective H hf)))

@[to_additive (attr := simp)]
theorem _root_.MonoidHom.comapSubquotientEquivOfSurjective_mk (f : G →* Q)
    (hf : Function.Surjective f) (K H : Subgroup Q) [(K.subgroupOf H).Normal]
    (x : H.comap f) :
    f.comapSubquotientEquivOfSurjective hf K H (QuotientGroup.mk x) =
      QuotientGroup.mk (f.subgroupComap H x) := by
  rw [MonoidHom.comapSubquotientEquivOfSurjective]; rfl

/-- Mapping two subgroups of `M ≤ G` into `G` via `M.subtype` preserves normality of their
relative subgroup. -/
@[to_additive]
instance normal_map_subtype_subgroupOf {M : Subgroup G} (K H : Subgroup M)
    [hN : (K.subgroupOf H).Normal] :
    ((K.map M.subtype).subgroupOf (H.map M.subtype)).Normal := by
  let e := H.equivMapOfInjective M.subtype M.subtype_injective
  have heq : (K.map M.subtype).subgroupOf (H.map M.subtype) =
      (K.subgroupOf H).map e.toMonoidHom := by
    ext ⟨_, ⟨x, hxH, rfl⟩⟩
    exact ⟨fun ⟨y, hyK, hyx⟩ ↦ ⟨⟨y, M.subtype_injective hyx ▸ hxH⟩, hyK, Subtype.ext hyx⟩,
      fun ⟨⟨y, _⟩, hyK, hyx⟩ ↦ ⟨y, hyK, congrArg (Subtype.val : H.map M.subtype → G) hyx⟩⟩
  exact heq ▸ hN.map e.toMonoidHom e.surjective

/-- Mapping subgroups `K, H ≤ M` to `G` along `M.subtype` identifies their subquotient in `G` with
`H ⧸ K.subgroupOf H`. -/
@[to_additive /-- Mapping additive subgroups `K, H ≤ M` to `G` along `M.subtype` identifies their
subquotient in `G` with `H ⧸ K.addSubgroupOf H`. -/]
noncomputable def mapSubtypeSubquotientEquiv {M : Subgroup G} (K H : Subgroup M)
    [(K.subgroupOf H).Normal] :
    (H ⧸ K.subgroupOf H) ≃*
      ((H.map M.subtype) ⧸ (K.map M.subtype).subgroupOf (H.map M.subtype)) :=
  let e := H.equivMapOfInjective M.subtype M.subtype_injective
  let φ := (QuotientGroup.mk' ((K.map M.subtype).subgroupOf (H.map M.subtype))).comp e.toMonoidHom
  have hker : φ.ker = K.subgroupOf H := by
    ext x
    simp only [φ, e, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, mem_map]
    exact ⟨fun ⟨y, hyK, hyx⟩ ↦ M.subtype_injective hyx ▸ hyK, fun hxK ↦ ⟨x.1, hxK, rfl⟩⟩
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ
      ((QuotientGroup.mk'_surjective _).comp e.surjective))

@[to_additive (attr := simp)]
theorem mapSubtypeSubquotientEquiv_mk {M : Subgroup G} (K H : Subgroup M)
    [(K.subgroupOf H).Normal] (x : H) :
    mapSubtypeSubquotientEquiv K H (QuotientGroup.mk x) =
      QuotientGroup.mk (H.equivMapOfInjective M.subtype M.subtype_injective x) := by
  rw [mapSubtypeSubquotientEquiv]; rfl

/-- For `H = ⊤` and `K = ⊥`, the subquotient `H ⧸ K.subgroupOf H` is canonically isomorphic to
`G`. -/
@[to_additive /-- For `H = ⊤` and `K = ⊥`, the additive subquotient `H ⧸ K.addSubgroupOf H` is
canonically isomorphic to `G`. -/]
noncomputable def subquotientEquivOfEqTopOfEqBot {H K : Subgroup G} [(K.subgroupOf H).Normal]
    (hH : H = ⊤) (hK : K = ⊥) : (H ⧸ K.subgroupOf H) ≃* G :=
  have hker : H.subtype.ker = K.subgroupOf H := by ext x; simp [hK]
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective H.subtype fun g ↦ ⟨⟨g, hH.symm ▸ mem_top g⟩, rfl⟩)

@[to_additive (attr := simp)]
theorem subquotientEquivOfEqTopOfEqBot_mk {H K : Subgroup G} [(K.subgroupOf H).Normal]
    (hH : H = ⊤) (hK : K = ⊥) (x : H) :
    subquotientEquivOfEqTopOfEqBot hH hK (QuotientGroup.mk x) = (x : G) := by
  rw [subquotientEquivOfEqTopOfEqBot]; rfl

end Subquotients

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
    have : Subsingleton ((⊤ : Subgroup G) ⧸ (⊤ : Subgroup G).subgroupOf ⊤) :=
      ⟨fun x y ↦ QuotientGroup.induction_on x fun _ ↦
        QuotientGroup.induction_on y fun _ ↦ QuotientGroup.eq.mpr trivial⟩
    exact absurd this (not_subsingleton _)

/-- **A nontrivial subnormal section of a simple group is the group itself.** -/
@[to_additive /-- **A nontrivial subnormal section of a simple additive group is the group
itself.** -/]
noncomputable def quotientMulEquivOfIsSimpleGroup [IsSimpleGroup G] (hH : H.IsSubnormal)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal] [Nontrivial (H ⧸ K.subgroupOf H)] :
    (H ⧸ K.subgroupOf H) ≃* G :=
  subquotientEquivOfEqTopOfEqBot (hH.eq_top_of_nontrivial_quotient K)
    (hH.eq_bot_of_nontrivial_quotient hKH)

@[to_additive (attr := simp)]
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
  have := e.isSimpleGroup
  have := isMulCommutative_quotient_of_isSolvable H K
  exact e.surjective.isMulCommutative

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
  have hcomap : ((K.map πN).subgroupOf (H.map πN)).comap ψ = K.subgroupOf H := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hxK ↦ mem_map.mpr ⟨x.1, hxK, rfl⟩⟩
    rcases mem_map.mp hx with ⟨k, hkK, hkx⟩
    have hmem : (⟨k⁻¹ * x.1, mul_mem (inv_mem (hKH hkK)) x.2⟩ : H) ∈ N.subgroupOf H :=
      mem_subgroupOf.mpr (QuotientGroup.eq.mp hkx)
    have hm := mem_map_of_mem (QuotientGroup.mk' (K.subgroupOf H)) hmem
    rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
    exact mem_subgroupOf.mpr (by simpa using mul_mem hkK hm)
  have hK'N : ((K.map πN).subgroupOf (H.map πN)).Normal := by
    have hmap : (K.subgroupOf H).map ψ = (K.map πN).subgroupOf (H.map πN) :=
      hcomap ▸ map_comap_eq_self_of_surjective hψ_surj _
    exact hmap ▸ hKN.map ψ hψ_surj
  let φ := (QuotientGroup.mk' ((K.map πN).subgroupOf (H.map πN))).comp ψ
  have hφ_ker : φ.ker = K.subgroupOf H := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact ⟨H.map πN, K.map πN, hH.quotient, map_mono hKH, hK'N,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective φ ((QuotientGroup.mk'_surjective _).comp
      hψ_surj)).symm.trans <| (QuotientGroup.quotientMulEquivOfEq hφ_ker).trans e⟩⟩

/-- When `(N ∩ H)` surjects onto `H ⧸ K.subgroupOf H`, the section is realized inside `N` via
`H.subgroupOf N` and `K.subgroupOf N`. -/
private theorem of_normal_map_eq_top {H K N : Subgroup G} (hH : H.IsSubnormal)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal] (e : (H ⧸ K.subgroupOf H) ≃* S)
    (htop : (N.subgroupOf H).map (QuotientGroup.mk' (K.subgroupOf H)) = ⊤) :
    HasSubnormalSection N S := by
  let α : H.subgroupOf N →* H := ⟨⟨fun x ↦ ⟨x.1.1, x.2⟩, rfl⟩, fun _ _ ↦ rfl⟩
  let ω := (QuotientGroup.mk' (K.subgroupOf H)).comp α
  have hω_surj : Function.Surjective ω := fun q ↦ by
    rcases mem_map.mp (htop.symm ▸ mem_top q) with ⟨y, hyN, rfl⟩
    exact ⟨⟨⟨y.1, hyN⟩, y.2⟩, rfl⟩
  have hker : ω.ker = (K.subgroupOf N).subgroupOf (H.subgroupOf N) := by
    ext x; exact QuotientGroup.eq_one_iff _
  have hKNN : ((K.subgroupOf N).subgroupOf (H.subgroupOf N)).Normal := hker ▸ ω.normal_ker
  exact ⟨H.subgroupOf N, K.subgroupOf N, hH.subgroupOf, subgroupOf_mono N hKH, hKNN,
    ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans <|
      (QuotientGroup.quotientKerEquivOfSurjective ω hω_surj).trans e⟩⟩

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
      MonoidHom.toMulEquiv ((MonoidHom.fst G₁ G₂).comp N.subtype)
        ((MonoidHom.inl G₁ G₂).codRestrict N fun _ ↦ rfl)
        (by
          ext ⟨⟨_, _⟩, hb⟩
          · rfl
          · exact hb.symm) (by ext; rfl)
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
