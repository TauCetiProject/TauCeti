/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# Restricting a group extension to a subgroup

For an extension `S : GroupExtension N E G` and `H ≤ G`, the inverse image of `H`
is an extension of `H` by the same kernel `N`. A section of `S` restricts to this
extension: its value at an element of `H` lies in the inverse image because it
projects to that element. Normalization, kernel conjugation and the noncommutative
factor set are preserved.

These comparisons allow crossed systems presented by sections to be restricted
without choosing new lifts or replacing a noncentral kernel by an abelian one.
In particular they apply to Clifford extensions with kernel the units of the
full endomorphism algebra.
-/

public section

namespace GroupExtension

variable {N E G : Type*} [Group N] [Group E] [Group G]

/-- The extension over `H` with middle group the inverse image of `H` under the
original projection. The kernel group and its inclusion are unchanged in ambient coordinates. -/
def restrict (S : GroupExtension N E G) (H : Subgroup G) :
    GroupExtension N (H.comap S.rightHom) H where
  inl := S.inl.codRestrict _ (fun n => by simp)
  rightHom := S.rightHom.restrict (fun _ he => he)
  inl_injective := fun _ _ h => S.inl_injective (congrArg Subtype.val h)
  range_inl_eq_ker_rightHom := by
    ext e
    constructor
    · rintro ⟨n, rfl⟩
      exact Subtype.ext (S.rightHom_inl n)
    · intro he
      have h : (e : E) ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
        exact congrArg Subtype.val he
      obtain ⟨n, hn⟩ := h
      exact ⟨n, Subtype.ext hn⟩
  rightHom_surjective := by
    intro h
    obtain ⟨e, he⟩ := S.rightHom_surjective (h : G)
    exact ⟨⟨e, by simpa only [Subgroup.mem_comap, he] using h.property⟩, Subtype.ext he⟩

/-- Restriction keeps the original kernel inclusion after forgetting subgroup membership. -/
@[simp]
theorem restrict_inl (S : GroupExtension N E G) (H : Subgroup G) (n : N) :
    ((S.restrict H).inl n : E) = S.inl n := (rfl)

/-- The restricted projection is the original projection, with codomain `H`. -/
@[simp]
theorem restrict_rightHom (S : GroupExtension N E G) (H : Subgroup G)
    (e : H.comap S.rightHom) :
    ((S.restrict H).rightHom e : G) = S.rightHom e := (rfl)

/-- Restricting the extension does not change its action on the kernel. -/
@[simp]
theorem restrict_conjAct (S : GroupExtension N E G) (H : Subgroup G)
    (e : H.comap S.rightHom) :
    (S.restrict H).conjAct e = S.conjAct (e : E) := by
  ext n
  apply S.inl_injective
  have h := congrArg Subtype.val ((S.restrict H).inl_conjAct_comm (e := e) (n := n))
  simpa only [restrict_inl, Subgroup.coe_mul, Subgroup.coe_inv] using
    h.trans (S.inl_conjAct_comm (e := (e : E)) (n := n)).symm

namespace Section

variable {S : GroupExtension N E G}

/-- Restrict a section to a subgroup of the quotient. Its values automatically lie
in the inverse-image subgroup; no new choice of lifts is made. -/
def restrict (s : S.Section) (H : Subgroup G) : (S.restrict H).Section where
  toFun h := ⟨s h, by simp⟩
  rightInverse_rightHom h := Subtype.ext (s.rightHom_section h)

/-- The restricted section has the same values in the ambient extension group. -/
@[simp]
theorem coe_restrict_apply (s : S.Section) (H : Subgroup G) (h : H) :
    (s.restrict H h : E) = s h := (rfl)

/-- A restricted section is normalized exactly when the original section is. -/
@[simp]
theorem restrict_one_eq_one_iff (s : S.Section) (H : Subgroup G) :
    s.restrict H 1 = 1 ↔ s 1 = 1 :=
  Subtype.ext_iff

/-- Restriction preserves the noncommutative factor set, as an equality in the
original kernel group rather than just after applying its inclusion. -/
@[simp]
theorem factorSetFun_restrict (s : S.Section) (H : Subgroup G) (g h : H) :
    TauCeti.GroupExtension.factorSetFun (s.restrict H) (g, h) =
      TauCeti.GroupExtension.factorSetFun s ((g : G), (h : G)) := by
  apply S.inl_injective
  have hf := congrArg Subtype.val
    (TauCeti.GroupExtension.inl_factorSetFun (s.restrict H) g h)
  simpa only [restrict_inl, Subgroup.coe_mul, Subgroup.coe_inv, coe_restrict_apply] using
    hf.trans (TauCeti.GroupExtension.inl_factorSetFun s (g : G) (h : G)).symm

/-- Differences of sections restrict to the same kernel-valued difference. This
identifies section changes before and after restricting the quotient. -/
@[simp]
theorem sectionDiff_restrict (s t : S.Section) (H : Subgroup G) (h : H) :
    TauCeti.GroupExtension.sectionDiff (s.restrict H) (t.restrict H) h =
      TauCeti.GroupExtension.sectionDiff s t (h : G) := by
  apply S.inl_injective
  have hd := congrArg Subtype.val
    (TauCeti.GroupExtension.inl_sectionDiff (s.restrict H) (t.restrict H) h)
  simpa only [restrict_inl, Subgroup.coe_mul, Subgroup.coe_inv, coe_restrict_apply] using
    hd.trans (TauCeti.GroupExtension.inl_sectionDiff s t (h : G)).symm

end Section

namespace Splitting

variable {S : GroupExtension N E G}

/-- A splitting restricts to the inverse-image extension of any subgroup of the quotient. -/
def restrict (s : S.Splitting) (H : Subgroup G) : (S.restrict H).Splitting where
  toFun := s.toSection.restrict H
  map_one' := Subtype.ext (map_one s)
  map_mul' g h := Subtype.ext (map_mul s (g : G) (h : G))
  rightInverse_rightHom := (s.toSection.restrict H).rightInverse_rightHom

/-- Forgetting the homomorphism law commutes with restricting a splitting. -/
@[simp]
theorem restrict_toSection (s : S.Splitting) (H : Subgroup G) :
    (s.restrict H).toSection = s.toSection.restrict H := (rfl)

/-- The restricted splitting agrees with the original splitting in the ambient group. -/
@[simp]
theorem coe_restrict_apply (s : S.Splitting) (H : Subgroup G) (h : H) :
    (s.restrict H h : E) = s h := (rfl)

end Splitting

end GroupExtension
