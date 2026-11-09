/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.QuotientGroup.Basic
import TauCeti.GroupTheory.Commutator
import TauCeti.GroupTheory.FreeGroup.Basis

/-!
# Universal central extensions of perfect groups

A **central extension** of a group `G` is a surjective homomorphism `p : E →* G` whose kernel
lies in the centre of `E`. It is **universal** when it maps uniquely, over `G`, to every central
extension of `G`. This file proves that a group has a universal central extension exactly when
it is perfect, by constructing one explicitly from a presentation.

Let `π : F →* G` be a surjective homomorphism with kernel `R`. Its **central cover** is the
quotient `U = [F, F] / [F, R]` of the commutator subgroup of `F` by the normal subgroup generated
by the commutators of elements of `F` with elements of `R`, together with the map `U →* G`
induced by `π`. For every `π`:

* the image of `U` in `G` is the commutator subgroup of `G`, so `U →* G` is onto exactly when
  `G` is perfect;
* its kernel is the image of `R ∩ [F, F]`, and it is isomorphic to `(R ∩ [F, F]) / [F, R]`
  (Hopf's formula for the kernel), and it is central;
* when `G` is perfect, `U` is perfect too, although `[F, F]` need not be: the commutator of two
  elements of `F` has a class in `U` that only depends on their images in `G`.

When `F` is a free group, a central extension `E →* G` receives a homomorphism from `U` over
`G`, obtained by lifting the free generators of `F` to `E`. Two such homomorphisms differ by a
homomorphism from `U` into the centre of `E`, which is trivial because `U` is perfect, so the
central cover of a free presentation of a perfect group is a universal central extension. In
particular the covers of two free presentations of the same perfect group are isomorphic over
`G`. Conversely, the total group of a universal central extension is perfect, since otherwise
its two maps to the product of `G` with the abelianization of the total group would differ, and
so is its image `G`.

This is a theorem about abstract groups: it involves no topology and no identification with the
universal covering group of a Lie group.

## Main definitions

* `MonoidHom.IsCentralExtension`: `p : E →* G` is surjective with central kernel.
* `MonoidHom.IsUniversalCentralExtension`: `p` is a central extension which maps uniquely over
  `G` to every central extension of `G` whose total group lies in a given universe.
* `MonoidHom.CentralCover`: the group `[F, F] / [F, R]` of a homomorphism `π : F →* G` with
  kernel `R`, with its quotient map `MonoidHom.CentralCover.mk` and its projection
  `MonoidHom.CentralCover.projection` to `G`.
* `MonoidHom.CentralCover.desc`: a homomorphism from `[F, F]` killing `[F, R]` descends to the
  central cover.
* `MonoidHom.CentralCover.quotientEquivKerProjection`: Hopf's formula
  `(R ∩ [F, F]) / [F, R] ≃* ker (U →* G)`.
* `MonoidHom.CentralCover.lift`: for a free presentation, the homomorphism from the central cover
  to a central extension over `G`.
* `MonoidHom.CentralCover.congr`: the central covers of two free presentations of a perfect group
  are isomorphic over the group.

## Main results

* `MonoidHom.CentralCover.range_projection_of_surjective`,
  `MonoidHom.CentralCover.ker_projection` and `MonoidHom.CentralCover.ker_projection_le_center`:
  the image, the kernel and the centrality of the kernel of the projection.
* `MonoidHom.CentralCover.isPerfect`: the central cover of a perfect group is perfect.
* `MonoidHom.CentralCover.isUniversalCentralExtension_projection`: the central cover of a free
  presentation of a perfect group is a universal central extension.
* `MonoidHom.IsUniversalCentralExtension.isPerfect`: the total group of a universal central
  extension is perfect.
* `Group.isPerfect_iff_exists_isUniversalCentralExtension`: a group is perfect exactly when it
  has a universal central extension.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72, Princeton
  University Press (1971), §5.
* M. Kervaire, *Multiplicateurs de Schur et K-théorie*, in *Essays on Topology and Related
  Topics* (Mémoires dédiés à Georges de Rham), Springer (1970), 212–225.
-/

public section

open Subgroup
open scoped commutatorElement

universe w u v

namespace MonoidHom

variable {E : Type*} [Group E] {F : Type*} [Group F] {G : Type*} [Group G]

/-- `p : E →* G` is a **central extension** of `G`: it is surjective and its kernel is central.
-/
structure IsCentralExtension (p : E →* G) : Prop where
  /-- A central extension is surjective. -/
  surjective : Function.Surjective p
  /-- The kernel of a central extension is central. -/
  ker_le_center : p.ker ≤ center E

/-- `p : E →* G` is a **universal central extension** of `G`, with respect to the central
extensions whose total group lies in the universe `w`: it is a central extension, and every
such central extension `q` of `G` receives a unique homomorphism from `E` over `G`. -/
structure IsUniversalCentralExtension (p : E →* G) : Prop where
  /-- A universal central extension is a central extension. -/
  isCentralExtension : p.IsCentralExtension
  /-- A universal central extension maps uniquely over `G` to every central extension. -/
  existsUnique_comp_eq : ∀ ⦃E' : Type w⦄ [Group E'] ⦃q : E' →* G⦄, q.IsCentralExtension →
    ∃! f : E →* E', q.comp f = p

/-- **The total group of a universal central extension is perfect.** Otherwise its two maps to
the product of `G` with its abelianization, through the trivial and through the canonical map to
the abelianization, are distinct homomorphisms over `G`. -/
theorem IsUniversalCentralExtension.isPerfect {E : Type u} [Group E] {G : Type v} [Group G]
    {p : E →* G} (hp : p.IsUniversalCentralExtension.{max v u}) : Group.IsPerfect E := by
  have hq : (fst G (Abelianization E)).IsCentralExtension := by
    refine ⟨Prod.fst_surjective, fun x hx ↦ mem_center_iff.mpr fun y ↦ ?_⟩
    rw [mem_ker, coe_fst] at hx
    ext
    · simp [hx]
    · exact mul_comm _ _
  obtain ⟨f, -, hf⟩ := hp.existsUnique_comp_eq hq
  have h₁ := hf (p.prod 1) (by ext; simp)
  have h₂ := hf (p.prod Abelianization.of) (by ext; simp)
  have hof : (Abelianization.of : E →* Abelianization E) = 1 := by
    have := congrArg ((snd G (Abelianization E)).comp ·) (h₂.trans h₁.symm)
    simpa only [snd_comp_prod] using this
  rw [Group.isPerfect_def, ← Abelianization.ker_of, hof]
  exact ker_one

/-- The group `[F, F] / [F, R]` of a homomorphism `π : F →* G` with kernel `R`: the commutator
subgroup of `F` modulo the normal subgroup generated by the commutators of elements of `F` with
elements of `R`. When `π` is surjective it maps onto the commutator subgroup of `G` with central
kernel, so it is a central extension of `G` when `G` is perfect, and a universal one when, in
addition, `F` is free (`MonoidHom.CentralCover.isUniversalCentralExtension_projection`). -/
def CentralCover (π : F →* G) : Type _ :=
  commutator F ⧸ (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (commutator F)
deriving Group

namespace CentralCover

variable (π : F →* G)

/-- The quotient map from the commutator subgroup `[F, F]` onto the central cover
`[F, F] / [F, R]`. -/
def mk : commutator F →* π.CentralCover :=
  QuotientGroup.mk' ((⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (commutator F))

theorem mk_surjective : Function.Surjective (mk π) :=
  QuotientGroup.mk'_surjective _

@[simp]
theorem ker_mk : (mk π).ker = (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (commutator F) :=
  QuotientGroup.ker_mk' _

@[simp]
theorem mk_eq_one_iff {x : commutator F} :
    mk π x = 1 ↔ (x : F) ∈ ⁅(⊤ : Subgroup F), π.ker⁆ := by
  rw [← mem_ker, ker_mk, mem_subgroupOf]

theorem mk_eq_mk_iff {x y : commutator F} :
    mk π x = mk π y ↔ (x : F)⁻¹ * y ∈ ⁅(⊤ : Subgroup F), π.ker⁆ := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, mk_eq_one_iff, coe_mul, coe_inv]

variable {π} in
/-- **Universal property of the central cover**: a homomorphism from `[F, F]` killing `[F, R]`
descends to the central cover `[F, F] / [F, R]`. -/
def desc {H : Type*} [Group H] (f : commutator F →* H)
    (hf : (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (commutator F) ≤ f.ker) : π.CentralCover →* H :=
  QuotientGroup.lift _ f hf

@[simp]
theorem desc_mk {H : Type*} [Group H] (f : commutator F →* H)
    (hf : (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (commutator F) ≤ f.ker) (x : commutator F) :
    desc f hf (mk π x) = f x :=
  (rfl)

@[simp]
theorem desc_comp_mk {H : Type*} [Group H] (f : commutator F →* H)
    (hf : (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (commutator F) ≤ f.ker) :
    (desc f hf).comp (mk π) = f :=
  (rfl)

/-- The kernel of the descended homomorphism is the image of the kernel of `f`. -/
theorem ker_desc {H : Type*} [Group H] (f : commutator F →* H)
    (hf : (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (commutator F) ≤ f.ker) :
    (desc f hf).ker = f.ker.map (mk π) :=
  QuotientGroup.ker_lift _ _ _

/-- Two homomorphisms out of the central cover agreeing on the classes of elements of `[F, F]`
are equal. -/
@[ext]
theorem hom_ext {H : Type*} [Group H] {f g : π.CentralCover →* H}
    (h : f.comp (mk π) = g.comp (mk π)) : f = g :=
  QuotientGroup.monoidHom_ext _ h

/-- The projection `[F, F] / [F, R] →* G` induced by `π`. -/
def projection : π.CentralCover →* G :=
  desc (π.domRestrict (commutator F)) <| by
    rw [ker_domRestrict]
    exact subgroupOf_mono _ (commutator_le_right _ _)

@[simp]
theorem projection_mk (x : commutator F) : projection π (mk π x) = π x :=
  (rfl)

/-- The image of the central cover is the image of the commutator subgroup of `F`. -/
theorem range_projection : (projection π).range = (commutator F).map π := by
  have h : (projection π).comp (mk π) = π.domRestrict (commutator F) := desc_comp_mk π _ _
  rw [← domRestrict_range, ← h, range_comp, range_eq_top_of_surjective _ (mk_surjective π),
    Subgroup.map_top]

/-- For a surjective `π`, the image of the central cover is the commutator subgroup of `G`. -/
theorem range_projection_of_surjective (hπ : Function.Surjective π) :
    (projection π).range = commutator G := by
  rw [range_projection, map_commutator_of_surjective hπ]

/-- For a surjective `π` onto a perfect group, the projection of the central cover is onto. -/
theorem projection_surjective (hπ : Function.Surjective π) [Group.IsPerfect G] :
    Function.Surjective (projection π) := by
  rw [← range_eq_top, range_projection_of_surjective π hπ, Group.IsPerfect.commutator_eq_top]

/-- The kernel of the projection is the image of `R ∩ [F, F]`. -/
theorem ker_projection :
    (projection π).ker = (π.ker.subgroupOf (commutator F)).map (mk π) :=
  (ker_desc π _ _).trans (congrArg (map (mk π)) (ker_domRestrict _ _))

/-- **The kernel of the projection is central.** The commutator of an element of `R` with any
element of `F` lies in `[F, R]`. -/
theorem ker_projection_le_center : (projection π).ker ≤ center π.CentralCover := by
  rw [ker_projection]
  rintro _ ⟨x, hx, rfl⟩
  refine mem_center_iff.mpr fun u ↦ ?_
  obtain ⟨y, rfl⟩ := mk_surjective π u
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, mk_eq_one_iff]
  exact commutator_mem_commutator (mem_top _) (mem_subgroupOf.mp hx)

/-- For a surjective `π` onto a perfect group, the projection of the central cover is a central
extension. -/
theorem isCentralExtension_projection (hπ : Function.Surjective π) [Group.IsPerfect G] :
    (projection π).IsCentralExtension :=
  ⟨projection_surjective π hπ, ker_projection_le_center π⟩

/-- The map from `R ∩ [F, F]` onto the kernel of the projection, whose kernel is the
intersection with `[F, R]`. -/
private def toKerProjection : ↥(π.ker ⊓ commutator F) →* (projection π).ker :=
  ((mk π).comp (inclusion inf_le_right)).codRestrict _ fun x ↦ by
    rw [ker_projection]
    exact ⟨inclusion inf_le_right x, mem_subgroupOf.mpr (mem_inf.mp x.2).1, rfl⟩

private theorem toKerProjection_surjective : Function.Surjective (toKerProjection π) := by
  rintro ⟨_, hy⟩
  rw [ker_projection] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, mem_inf.mpr ⟨mem_subgroupOf.mp hx, x.2⟩⟩, rfl⟩

private theorem ker_toKerProjection :
    (toKerProjection π).ker = (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (π.ker ⊓ commutator F) := by
  ext x
  rw [mem_ker, mem_subgroupOf]
  exact Subtype.ext_iff.trans (mk_eq_one_iff π)

/-- **Hopf's formula for the kernel of the central cover**: the kernel of the projection
`[F, F] / [F, R] →* G` is `(R ∩ [F, F]) / [F, R]`. When `F` is free and `π` is onto, this is
the Schur multiplier of `G`. -/
noncomputable def quotientEquivKerProjection :
    ↥(π.ker ⊓ commutator F) ⧸ (⁅(⊤ : Subgroup F), π.ker⁆).subgroupOf (π.ker ⊓ commutator F) ≃*
      (projection π).ker :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toKerProjection π).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toKerProjection_surjective π))

@[simp]
theorem coe_quotientEquivKerProjection_mk (x : ↥(π.ker ⊓ commutator F)) :
    (quotientEquivKerProjection π x : π.CentralCover) = mk π (inclusion inf_le_right x) :=
  (rfl)

/-- The class in the central cover of the commutator of two elements of `F` only depends on
their images in `G`, because the elements of `R` are central in `F / [F, R]`: it is the
commutator of the classes of any two elements of `[F, F]` with the same images. -/
theorem mk_commutatorElement_eq {a b : F} {a' b' : commutator F} (ha : π a' = π a)
    (hb : π b' = π b) :
    mk π ⟨⁅a, b⁆, commutator_mem_commutator (mem_top a) (mem_top b)⟩ = ⁅mk π a', mk π b'⁆ := by
  -- Work in `F / [F, R]`, where the image of `R` is central.
  let q := QuotientGroup.mk' (⁅(⊤ : Subgroup F), π.ker⁆)
  have hcen {r : F} (hr : r ∈ π.ker) : q r ∈ center (F ⧸ ⁅(⊤ : Subgroup F), π.ker⁆) := by
    refine mem_center_iff.mpr fun g ↦ ?_
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective _ g
    exact QuotientGroup.commute_mk_iff.mpr (commutator_mem_commutator (mem_top f) hr)
  have hr (c c' : F) (hc : π c' = π c) : c⁻¹ * c' ∈ π.ker := by
    rw [mem_ker, map_mul, map_inv, hc, inv_mul_cancel]
  have hq : q ⁅a, b⁆ = q ⁅(a' : F), (b' : F)⁆ := by
    rw [map_commutatorElement, map_commutatorElement, ← mul_inv_cancel_left a a',
      ← mul_inv_cancel_left b b', map_mul q a, map_mul q b,
      TauCeti.commutatorElement_mul_mul_of_mem_center (hcen (hr a a' ha)) (hcen (hr b b' hb))]
  rw [← map_commutatorElement, mk_eq_mk_iff]
  exact QuotientGroup.eq.mp hq

/-- **The central cover of a perfect group is perfect.** Since `G` is perfect, every element of
`F` has the same image in `G` as an element of `[F, F]`, so by
`MonoidHom.CentralCover.mk_commutatorElement_eq` the class of a commutator of two elements of `F`
is the commutator of two elements of the central cover. The commutator subgroup `[F, F]` itself
need not be perfect. -/
theorem isPerfect (hπ : Function.Surjective π) [Group.IsPerfect G] :
    Group.IsPerfect π.CentralCover := by
  have hlift (a : F) : ∃ a' ∈ commutator F, π a' = π a := by
    have : π a ∈ (commutator F).map π := by
      rw [← range_projection, range_projection_of_surjective π hπ]
      exact Group.IsPerfect.mem_commutator
    simpa only [mem_map] using this
  have key : ∀ (x : F) (hx : x ∈ commutator F), mk π ⟨x, hx⟩ ∈ commutator π.CentralCover := by
    intro x hx
    have hx' := hx
    rw [commutator_eq_closure] at hx'
    induction hx' using closure_induction with
    | mem x hx' =>
      obtain ⟨a, b, rfl⟩ := hx'
      obtain ⟨a', ha', ha⟩ := hlift a
      obtain ⟨b', hb', hb⟩ := hlift b
      rw [mk_commutatorElement_eq π (a' := ⟨a', ha'⟩) (b' := ⟨b', hb'⟩) ha hb]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    | one => exact (map_one (mk π)).symm ▸ one_mem _
    | mul x y hx' hy' ihx ihy =>
      rw [← commutator_eq_closure] at hx' hy'
      have : mk π ⟨x * y, hx⟩ = mk π ⟨x, hx'⟩ * mk π ⟨y, hy'⟩ :=
        map_mul (mk π) ⟨x, hx'⟩ ⟨y, hy'⟩
      exact this ▸ mul_mem (ihx hx') (ihy hy')
    | inv x hx' ihx =>
      rw [← commutator_eq_closure] at hx'
      have : mk π ⟨x⁻¹, hx⟩ = (mk π ⟨x, hx'⟩)⁻¹ := map_inv (mk π) ⟨x, hx'⟩
      exact this ▸ inv_mem (ihx hx')
  rw [Group.isPerfect_def, eq_top_iff]
  intro u _
  obtain ⟨⟨x, hx⟩, rfl⟩ := mk_surjective π u
  exact key x hx

section Free

variable {X : Type*} (π : FreeGroup X →* G) {p : E →* G}

/-- For a free presentation `π : FreeGroup X →* G`, the homomorphism from the central cover to a
central extension `p : E →* G`, obtained by lifting `π` through `p` on the free generators
(`FreeGroupBasis.exists_comp_eq_of_surjective`) and restricting to the commutator subgroup, which
kills `[F, R]` since the lifts of relations are central. For a perfect `G` it is the unique
homomorphism over `G` (`MonoidHom.CentralCover.isUniversalCentralExtension_projection`). -/
noncomputable def lift (hp : p.IsCentralExtension) : π.CentralCover →* E :=
  have hψ := (FreeGroupBasis.ofFreeGroup X).exists_comp_eq_of_surjective hp.surjective π
  desc (hψ.choose.domRestrict (commutator _)) <| by
    have h := commutator_top_ker_comp_le_ker hp.ker_le_center hψ.choose
    rw [hψ.choose_spec] at h
    rw [ker_domRestrict]
    exact subgroupOf_mono _ h

@[simp]
theorem comp_lift (hp : p.IsCentralExtension) : p.comp (lift π hp) = projection π := by
  refine MonoidHom.ext fun u ↦ ?_
  obtain ⟨x, rfl⟩ := mk_surjective π u
  exact DFunLike.congr_fun
    ((FreeGroupBasis.ofFreeGroup X).exists_comp_eq_of_surjective hp.surjective π).choose_spec x.1

/-- **The central cover of a free presentation of a perfect group is a universal central
extension**, for central extensions with total group in any universe. -/
theorem isUniversalCentralExtension_projection (hπ : Function.Surjective π) [Group.IsPerfect G] :
    (projection π).IsUniversalCentralExtension.{w} := by
  have := isPerfect π hπ
  refine ⟨isCentralExtension_projection π hπ, fun E' _ q hq ↦ ⟨lift π hq, comp_lift π hq, ?_⟩⟩
  intro f hf
  exact eq_of_comp_eq_of_ker_le_center hq.ker_le_center (hf.trans (comp_lift π hq).symm)

/-- The central covers of two free presentations of a perfect group are isomorphic over the group.
-/
noncomputable def congr {Y : Type*} (π' : FreeGroup Y →* G) (hπ : Function.Surjective π)
    (hπ' : Function.Surjective π') [Group.IsPerfect G] : π.CentralCover ≃* π'.CentralCover :=
  have := isPerfect π hπ
  have := isPerfect π' hπ'
  (lift π (isCentralExtension_projection π' hπ')).toMulEquiv
    (lift π' (isCentralExtension_projection π hπ))
    (eq_of_comp_eq_of_ker_le_center (ker_projection_le_center π) <| by
      rw [← comp_assoc, comp_lift, comp_lift, comp_id])
    (eq_of_comp_eq_of_ker_le_center (ker_projection_le_center π') <| by
      rw [← comp_assoc, comp_lift, comp_lift, comp_id])

@[simp]
theorem projection_congr {Y : Type*} (π' : FreeGroup Y →* G) (hπ : Function.Surjective π)
    (hπ' : Function.Surjective π') [Group.IsPerfect G] (u : π.CentralCover) :
    projection π' (congr π π' hπ hπ' u) = projection π u :=
  DFunLike.congr_fun (comp_lift π (isCentralExtension_projection π' hπ')) u

end Free

end CentralCover

end MonoidHom

namespace Group

/-- **A group is perfect exactly when it has a universal central extension.** The central cover
`[F, F] / [F, R]` of the canonical free presentation `FreeGroup.prod : FreeGroup G →* G` is one
when `G` is perfect, and the total group of a universal central extension is perfect and maps onto
`G`. -/
theorem isPerfect_iff_exists_isUniversalCentralExtension {G : Type u} [Group G] :
    IsPerfect G ↔
      ∃ (E : Type u) (_ : Group E) (p : E →* G), p.IsUniversalCentralExtension.{u} := by
  constructor
  · intro _
    exact ⟨_, _, _, MonoidHom.CentralCover.isUniversalCentralExtension_projection
      FreeGroup.prod FreeGroup.prod_surjective⟩
  · rintro ⟨E, _, p, hp⟩
    have := hp.isPerfect
    exact IsPerfect.ofSurjective hp.isCentralExtension.surjective

end Group
