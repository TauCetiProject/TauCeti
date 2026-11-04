/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Subgroup.Saturated
public import TauCeti.Algebra.Group.Submonoid.GroupCompletion

/-!
# Saturation of a submonoid by positive powers

Given a submonoid `s` of a commutative monoid `M`, its *saturation* is the submonoid of all
elements whose positive power lies in `s`, that is `{x : M | ∃ n, 0 < n ∧ x ^ n ∈ s}`. This is the
least `PowSaturated` submonoid containing `s` (a submonoid `t` is `PowSaturated` when `x ^ n ∈ t`
forces `n = 0` or `x ∈ t`). Applying saturation to an already `PowSaturated` submonoid is a no-op,
and saturation commutes with pullbacks along monoid homomorphisms and with binary intersections.

For a submonoid `s` of a commutative group `G`, saturating `s` inside the subgroup it generates
yields `s.powSaturation ⊓ (Subgroup.closure (s : Set G)).toSubmonoid`, which generates the same
subgroup as `s`, is canonically isomorphic to
`(s.comap (Subgroup.closure s).subtype).powSaturation`, and characterizes when the pullback of `s`
to its generated subgroup is saturated.

General declarations are stated multiplicatively and translated with `@[to_additive]` to their
additive counterparts (e.g. `Submonoid.powSaturation` becomes `AddSubmonoid.nsmulSaturation` and
`Submonoid.mem_powSaturation` becomes `AddSubmonoid.mem_nsmulSaturation`); the homomorphism
`AddSubmonoid.nsmulSaturationToGroupClosure` and its comparison lemmas with
`AddSubmonoid.toGroupClosure` are stated additively to match
`TauCeti.Algebra.Group.Submonoid.GroupCompletion`.

## Main results

* `Submonoid.powSaturation`: the elements of `M` having a positive power in `s`.
* `Submonoid.mem_powSaturation`: the membership criterion.
* `Submonoid.le_powSaturation`: `s` is contained in its saturation.
* `Submonoid.powSaturation_mono`: the saturation is monotone in `s`.
* `Submonoid.powSaturated_powSaturation`: the saturation is `PowSaturated`.
* `Submonoid.powSaturation_le_iff_le`: the saturation is the least `PowSaturated` submonoid
  containing `s`.
* `Submonoid.powSaturation_eq_self` and `Submonoid.powSaturated_iff_powSaturation_eq`: a submonoid
  is `PowSaturated` iff it equals its saturation.
* `Submonoid.powSaturation_comap` and `Submonoid.powSaturation_inf`: saturation commutes with
  `comap` and `⊓`.
* `Submonoid.closure_powSaturation_inf_closure`, `Submonoid.powSaturationInfClosureEquiv`, and
  `Submonoid.powSaturated_comap_subtype_closure_iff`: saturation inside the generated subgroup.
* `AddSubmonoid.nsmulSaturationToGroupClosure`: canonical inclusion of the saturation inside
  `AddSubgroup.closure S` into `AddSubgroup.closure S`.
-/

public section

namespace Submonoid

variable {M N : Type*} [CommMonoid M] [CommMonoid N]

/-- The saturation of a submonoid `s` is the submonoid of elements whose positive power lies in
`s`, `{x | ∃ n, 0 < n ∧ x ^ n ∈ s}`. It is the least `PowSaturated` submonoid containing `s`. -/
@[to_additive /-- The saturation of an additive submonoid `s` is the additive
submonoid of elements whose positive multiple lies in `s`, `{x | ∃ n, 0 < n ∧ n • x ∈ s}`. It is
the least `NSMulSaturated` additive submonoid containing `s`. -/]
def powSaturation (s : Submonoid M) : Submonoid M where
  carrier := {x | ∃ n, 0 < n ∧ x ^ n ∈ s}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ x ^ n ∈ s := hx
    obtain ⟨m, hmpos, hmy⟩ : ∃ m, 0 < m ∧ y ^ m ∈ s := hy
    have hkx : x ^ (n * m) ∈ s := by rw [Nat.mul_comm, pow_mul' x m n]; exact pow_mem hnx m
    have hky : y ^ (n * m) ∈ s := by rw [Nat.mul_comm, pow_mul y m n]; exact pow_mem hmy n
    exact ⟨n * m, Nat.mul_pos hnpos hmpos, by simpa [mul_pow] using mul_mem hkx hky⟩

/-- An element belongs to the saturation of `s` if and only if some positive power of it lies in
`s`. -/
@[to_additive (attr := simp) /-- An element belongs to the saturation of an additive submonoid `s`
if and only if some positive multiple of it lies in `s`. -/]
theorem mem_powSaturation {s : Submonoid M} {x : M} :
    x ∈ s.powSaturation ↔ ∃ n, 0 < n ∧ x ^ n ∈ s :=
  Iff.rfl

/-- Every submonoid is contained in its saturation. -/
@[to_additive (attr := simp) /-- Every additive submonoid is contained in its saturation. -/]
theorem le_powSaturation {s : Submonoid M} : s ≤ s.powSaturation :=
  fun _ hx => mem_powSaturation.2 ⟨1, by simpa [pow_one] using hx⟩

/-- The saturation is monotone in the submonoid. -/
@[to_additive (attr := gcongr) /-- The saturation is monotone in the additive submonoid. -/]
theorem powSaturation_mono {s t : Submonoid M} (hst : s ≤ t) :
    s.powSaturation ≤ t.powSaturation := by
  rintro x hx
  obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ x ^ n ∈ s := mem_powSaturation.mp hx
  exact mem_powSaturation.2 ⟨n, hnpos, hst hnx⟩

/-- The saturation of a submonoid is itself `PowSaturated`. -/
@[to_additive (attr := simp) /-- The saturation of an additive submonoid is itself
`NSMulSaturated`. -/]
theorem powSaturated_powSaturation {s : Submonoid M} : PowSaturated s.powSaturation := by
  intro n g hng
  obtain ⟨k, hkpos, hkg⟩ : ∃ k, 0 < k ∧ (g ^ n) ^ k ∈ s := mem_powSaturation.mp hng
  by_cases hn0 : n = 0
  · left; exact hn0
  · right
    exact mem_powSaturation.2 ⟨k * n, Nat.mul_pos hkpos (Nat.pos_of_ne_zero hn0),
      by rw [pow_mul' g k n]; exact hkg⟩

/-- The saturation of `s` is contained in the `PowSaturated` submonoid `t` if and only if `s` is:
the saturation is the least `PowSaturated` submonoid containing `s`. -/
@[to_additive /-- The saturation of `s` is contained in the `NSMulSaturated` additive submonoid `t`
if and only if `s` is: the saturation is the least `NSMulSaturated` additive submonoid containing
`s`. -/]
theorem powSaturation_le_iff_le {s t : Submonoid M} (ht : PowSaturated t) :
    s.powSaturation ≤ t ↔ s ≤ t :=
  ⟨fun h => le_trans le_powSaturation h,
   fun h => by
     rintro x hx
     obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ x ^ n ∈ s := mem_powSaturation.mp hx
     exact Or.resolve_left (ht (h hnx)) (Nat.pos_iff_ne_zero.mp hnpos)⟩

/-- The saturation of an already `PowSaturated` submonoid `s` is `s` itself. -/
@[to_additive (attr := simp) /-- The saturation of an already `NSMulSaturated` additive submonoid
`s` is `s` itself. -/]
theorem powSaturation_eq_self {s : Submonoid M} (hs : PowSaturated s) : s.powSaturation = s := by
  apply le_antisymm
  · exact (powSaturation_le_iff_le (s := s) (t := s) hs).mpr (le_refl s)
  · exact le_powSaturation

/-- A submonoid is `PowSaturated` if and only if it equals its own saturation. -/
@[to_additive /-- An additive submonoid is `NSMulSaturated` if and only if it equals its own
saturation. -/]
theorem powSaturated_iff_powSaturation_eq {s : Submonoid M} :
    PowSaturated s ↔ s.powSaturation = s :=
  ⟨powSaturation_eq_self, fun h => h ▸ powSaturated_powSaturation⟩

/-- Saturation commutes with pullback along a monoid homomorphism. -/
@[to_additive (attr := simp) /-- Saturation commutes with pullback along an additive monoid
homomorphism. -/]
theorem powSaturation_comap (s : Submonoid M) (f : N →* M) :
    (s.comap f).powSaturation = s.powSaturation.comap f := by
  ext x
  simp [map_pow]

/-- Saturation commutes with binary intersections of submonoids. -/
@[to_additive (attr := simp) /-- Saturation commutes with binary intersections of additive
submonoids. -/]
theorem powSaturation_inf (s t : Submonoid M) :
    (s ⊓ t).powSaturation = s.powSaturation ⊓ t.powSaturation := by
  refine le_antisymm (le_inf (powSaturation_mono inf_le_left) (powSaturation_mono inf_le_right)) ?_
  rintro x ⟨⟨n, hn, hns⟩, ⟨m, hm, hmt⟩⟩
  refine ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · rw [pow_mul]
    exact pow_mem hns m
  · rw [Nat.mul_comm, pow_mul]
    exact pow_mem hmt n

section Group

variable {G : Type*} [CommGroup G] (s : Submonoid G)

/-- Saturating `s` inside the subgroup it generates does not change the generated subgroup. -/
@[to_additive /-- Saturating `s` inside the additive subgroup it generates does not
change the generated additive subgroup. -/]
theorem closure_powSaturation_inf_closure :
    Subgroup.closure
        ((s.powSaturation ⊓ (Subgroup.closure (s : Set G)).toSubmonoid : Submonoid G) : Set G) =
      Subgroup.closure (s : Set G) :=
  le_antisymm
    ((Subgroup.closure_le _).mpr fun _ hx => (Submonoid.mem_inf.mp hx).2)
    (Subgroup.closure_mono <| le_inf s.le_powSaturation Subgroup.subset_closure)

/-- The pullback of `s` to the subgroup it generates is `PowSaturated` if and only if the
saturation of `s` meets `Subgroup.closure s` in `s`. -/
@[to_additive /-- The pullback of `s` to the additive subgroup it generates is `NSMulSaturated`
if and only if the saturation of `s` meets `AddSubgroup.closure s` in `s`. -/]
theorem powSaturated_comap_subtype_closure_iff :
    PowSaturated (s.comap (Subgroup.closure (s : Set G)).subtype) ↔
      s.powSaturation ⊓ (Subgroup.closure (s : Set G)).toSubmonoid = s := by
  rw [powSaturated_iff_powSaturation_eq, powSaturation_comap]
  refine ⟨fun h => le_antisymm (fun x hx => ?_) (le_inf s.le_powSaturation Subgroup.subset_closure),
    fun h => ?_⟩
  · obtain ⟨hx1, hx2⟩ := Submonoid.mem_inf.mp hx
    exact (SetLike.ext_iff.mp h ⟨x, hx2⟩).mp hx1
  · ext ⟨x, hx⟩
    exact ⟨fun hx' => (SetLike.ext_iff.mp h x).mp (Submonoid.mem_inf.mpr ⟨hx', hx⟩),
      fun hx' => s.le_powSaturation hx'⟩

/-- The canonical multiplicative equivalence identifying the saturation of `s` inside
`Subgroup.closure (s : Set G)` with the saturation of the pullback of `s` to
`Subgroup.closure (s : Set G)`. -/
@[to_additive /-- The canonical additive equivalence identifying the saturation of `s` inside
`AddSubgroup.closure (s : Set G)` with the saturation of the pullback of `s` to
`AddSubgroup.closure (s : Set G)`. -/]
def powSaturationInfClosureEquiv :
    ↥(s.powSaturation ⊓ (Subgroup.closure (s : Set G)).toSubmonoid) ≃*
      ↥(s.comap (Subgroup.closure (s : Set G)).subtype).powSaturation where
  toFun x := ⟨⟨x.1, x.2.2⟩, by rw [powSaturation_comap]; exact x.2.1⟩
  invFun | ⟨z, hz⟩ => ⟨z.1, ⟨by rwa [powSaturation_comap] at hz, z.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Group

end Submonoid

namespace AddSubmonoid

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G)

/-- The canonical inclusion of the saturation of `S` inside `AddSubgroup.closure (S : Set G)` into
`AddSubgroup.closure (S : Set G)`. -/
def nsmulSaturationToGroupClosure :
    ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →+
      AddSubgroup.closure (S : Set G) :=
  (S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid).subtype.codRestrict
    (AddSubgroup.closure (S : Set G)) fun x => x.property.2

/-- `nsmulSaturationToGroupClosure` preserves the underlying element of the ambient group. -/
@[simp]
theorem coe_nsmulSaturationToGroupClosure
    (x : ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid)) :
    (S.nsmulSaturationToGroupClosure x : G) = x :=
  (rfl)

/-- `nsmulSaturationToGroupClosure` is injective. -/
theorem nsmulSaturationToGroupClosure_injective :
    Function.Injective S.nsmulSaturationToGroupClosure :=
  ((S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid).subtype
    |>.injective_codRestrict _ _).mpr Subtype.val_injective

/-- Restricting `nsmulSaturationToGroupClosure` along the inclusion of `S` recovers
`S.toGroupClosure`. -/
@[simp]
theorem nsmulSaturationToGroupClosure_comp_inclusion :
    S.nsmulSaturationToGroupClosure.comp
        (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)) =
      S.toGroupClosure := by
  ext s
  simp

/-- The image of `nsmulSaturationToGroupClosure` inside `AddSubgroup.closure (S : Set G)` is the
saturation of `S` pulled back to its generated subgroup. -/
@[simp]
theorem mrange_nsmulSaturationToGroupClosure :
    AddMonoidHom.mrange S.nsmulSaturationToGroupClosure =
      (S.comap (AddSubgroup.closure (S : Set G)).subtype).nsmulSaturation := by
  ext ⟨x, hx⟩
  rw [AddMonoidHom.mem_mrange, nsmulSaturation_comap, mem_comap, AddSubgroup.coe_subtype]
  exact ⟨by rintro ⟨y, hy⟩; rw [← congrArg Subtype.val hy]; exact y.property.1,
    fun hxS => ⟨⟨x, hxS, hx⟩, rfl⟩⟩

/-- Coercing `nsmulSaturationInfClosureEquiv` into `AddSubgroup.closure (S : Set G)` recovers
`nsmulSaturationToGroupClosure`. -/
@[simp]
theorem coe_nsmulSaturationInfClosureEquiv
    (x : ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid)) :
    ((S.nsmulSaturationInfClosureEquiv x :
        ↥(S.comap (AddSubgroup.closure (S : Set G)).subtype).nsmulSaturation) :
      AddSubgroup.closure (S : Set G)) = S.nsmulSaturationToGroupClosure x :=
  (rfl)

end AddSubmonoid
