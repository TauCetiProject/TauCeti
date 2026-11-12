/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import TauCeti.GroupTheory.GroupAlgGeom.Separated
import Mathlib.Data.ZMod.Basic
import TauCeti.GroupTheory.FreeGroup.Centralizer
import TauCeti.GroupTheory.FreeGroup.TwoGenerator

/-!
# Coefficient-preserving retractions and roots

Let `F` be a subgroup of a group `G`, regarded as an `F`-group through its inclusion. An
`F`-homomorphism `G → F` is a retraction of `G` onto `F`. When `G` has unique roots, such a
retraction can exist only if `F` contains every element of `G` having a nonzero power in `F`: if
`gⁿ ∈ F` then the image of `g` is an `n`-th root of `gⁿ`, hence equals `g`.

This obstructs relative discrimination. In the free group `F(a, b)` the subgroup `F = ⟨a², b⟩` is
free of rank two on `a²` and `b`, so `F(a, b)` is a finitely generated `F`-group over a free
nonabelian group of finite rank, and `F(a, b)` is fully residually free
(`TauCeti.LimitGroup.isFullyResiduallyFree_of_isFreeGroup`). Yet `a² ∈ F` and `a ∉ F`, so there
is no `F`-homomorphism `F(a, b) → F` at all. Hence `F(a, b)` is neither `F`-separated nor
`F`-discriminated by `F`, and it is not `F`-isomorphic to any coordinate group over `F`. For
finitely generated `F`-groups over a free nonabelian `F`, being `F`-discriminated by `F` and being
the coordinate group of an irreducible algebraic set over `F` each imply full residual freeness;
this example shows that the converse fails for a specified inclusion of the coefficients.
Everything is stated for two distinct basis elements `a`, `b` of any free group `F(α)`.

## Main results

* `TauCeti.GroupAlgGeom.GHom.mem_of_pow_mem`: a retract of a group with unique roots contains
  every element having a nonzero power in it.
* `TauCeti.GroupAlgGeom.injective_lift_sq_of_ne`: `a²` and `b` freely generate a free group of
  rank two.
* `TauCeti.GroupAlgGeom.isEmpty_gHom_closure_sq_of_ne`: there is no `⟨a², b⟩`-homomorphism
  `F(α) → ⟨a², b⟩`.
* `TauCeti.GroupAlgGeom.not_isDiscriminatedBy_closure_sq_of_ne`: `F(α)` is not
  `⟨a², b⟩`-discriminated by `⟨a², b⟩`.
* `TauCeti.GroupAlgGeom.not_bijective_gHom_coordGroup_closure_sq_of_ne`: `F(α)` is not
  `⟨a², b⟩`-isomorphic to a coordinate group over `⟨a², b⟩`.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §1 (separation and discrimination).
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §§2.5–2.6 (`G`-separation and `G`-discrimination; finitely generated `F`-groups
  `F`-discriminated by `F`).
-/

public section

namespace TauCeti.GroupAlgGeom

open FreeGroup

section Retraction

variable {G : Type*} [Group G] [HasUniqueRoots G] {F : Subgroup G}

/-- A retract of a group with unique roots is closed under roots: if a coefficient-preserving
homomorphism `φ : G → F` fixes the subgroup `F` pointwise, then every `g` with `gⁿ ∈ F` for some
`n ≠ 0` lies in `F`. -/
theorem GHom.mem_of_pow_mem (φ : GHom F.subtype (MonoidHom.id F)) {g : G} {n : ℕ} (hn : n ≠ 0)
    (hg : g ^ n ∈ F) : g ∈ F := by
  -- `φ g` is an `n`-th root of `gⁿ`, so it is `g` by uniqueness of roots.
  have h : ((φ g : F) : G) ^ n = g ^ n := by
    simpa using congrArg Subtype.val (φ.map_coeff ⟨g ^ n, hg⟩)
  exact pow_left_injective hn h ▸ (φ g).2

end Retraction

section FreeGroup

variable {α : Type*} {a b : α}

/-- For distinct basis elements `a` and `b` of a free group, `a²` and `b` freely generate a free
group of rank two; its image is the subgroup `⟨a², b⟩` (`FreeGroup.range_lift_eq_closure`). -/
theorem injective_lift_sq_of_ne (hab : a ≠ b) :
    Function.Injective (FreeGroup.lift ![of a ^ 2, of b]) := by
  -- An element commuting with `b` is a power of `b`, and `a² = bⁿ` is impossible.
  refine IsFreeGroup.injective_lift_of_not_commute fun h => ?_
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_of_commute h)
  have := eq_of_of_zpow_eq_of_zpow hab (n := 2) (m := n) (by simpa using hn.symm)
  lia

/-- For distinct basis elements `a` and `b` of a free group, `a` does not lie in the subgroup
`⟨a², b⟩`. -/
theorem of_notMem_closure_sq_of_ne (hab : a ≠ b) : of a ∉ Subgroup.closure {of a ^ 2, of b} := by
  classical
  -- `⟨a², b⟩` lies in the kernel of the map to `ℤ/2` sending `a` to `1` and the other basis
  -- elements to `0`, and `a` does not.
  let χ : FreeGroup α →* Multiplicative (ZMod 2) :=
    FreeGroup.lift fun c => if c = a then Multiplicative.ofAdd 1 else 1
  have hle : Subgroup.closure {of a ^ 2, of b} ≤ χ.ker := by
    simpa [Subgroup.closure_le, Set.insert_subset_iff, χ, hab.symm] using
      (by decide : Multiplicative.ofAdd (1 : ZMod 2) ^ 2 = 1)
  exact fun h => absurd (hle h) (by simp [χ])

/-- For distinct basis elements `a` and `b` of a free group `F(α)`, there is no
`⟨a², b⟩`-homomorphism `F(α) → ⟨a², b⟩`, that is, no retraction of `F(α)` onto `⟨a², b⟩`. -/
theorem isEmpty_gHom_closure_sq_of_ne (hab : a ≠ b) :
    IsEmpty (GHom (Subgroup.closure {of a ^ 2, of b}).subtype (MonoidHom.id _)) :=
  -- A retraction would force the square root `a` of `a² ∈ ⟨a², b⟩` into `⟨a², b⟩`.
  ⟨fun φ => of_notMem_closure_sq_of_ne hab
    (φ.mem_of_pow_mem two_ne_zero (Subgroup.subset_closure (Set.mem_insert _ _)))⟩

/-- For distinct basis elements `a` and `b` of a free group `F(α)`, the group `F(α)` is not
separated by `⟨a², b⟩` over `⟨a², b⟩`. -/
theorem not_isSeparatedBy_closure_sq_of_ne (hab : a ≠ b) :
    ¬IsSeparatedBy (Subgroup.closure {of a ^ 2, of b}).subtype (MonoidHom.id _) := fun h =>
  (isEmpty_gHom_closure_sq_of_ne hab).false
    ((isSeparatedBy_def _ _).1 h (of a) (of_ne_one a)).choose

/-- For distinct basis elements `a` and `b` of a free group `F(α)`, the group `F(α)` is not
discriminated by `⟨a², b⟩` over `⟨a², b⟩`, although `⟨a², b⟩` is free of rank two
(`injective_lift_sq_of_ne`) and `F(α)` is fully residually free
(`TauCeti.LimitGroup.isFullyResiduallyFree_of_isFreeGroup`). -/
theorem not_isDiscriminatedBy_closure_sq_of_ne (hab : a ≠ b) :
    ¬IsDiscriminatedBy (Subgroup.closure {of a ^ 2, of b}).subtype (MonoidHom.id _) := fun h =>
  not_isSeparatedBy_closure_sq_of_ne hab h.isSeparatedBy

/-- For distinct basis elements `a` and `b` of a free group `F(α)`, the group `F(α)` is not
`⟨a², b⟩`-isomorphic to a coordinate group over `⟨a², b⟩`: for every set of variables `X` and
every system `S`, finite or not, with irreducible algebraic set or not, no coefficient-preserving
homomorphism from the coordinate group of `S` to `F(α)` is bijective. -/
theorem not_bijective_gHom_coordGroup_closure_sq_of_ne (hab : a ≠ b) {X : Type*}
    (S : Set (GX (Subgroup.closure {of a ^ 2, of b}) X))
    (φ : GHom (CoordGroup.coeff (MonoidHom.id _) S) (Subgroup.closure {of a ^ 2, of b}).subtype) :
    ¬Function.Bijective φ := fun hφ =>
  -- Coordinate groups are separated by the coefficient group, and `F(α)` is not.
  not_isSeparatedBy_closure_sq_of_ne hab <|
    (CoordGroup.isSeparatedBy_coeff S).of_injective (φ.symmOfBijective hφ)
      (φ.symmOfBijective_injective hφ)

end FreeGroup

end TauCeti.GroupAlgGeom
