/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset

/-!
# The identity double coset

Two elements have the same class in `H \ G / K` exactly when one lies in the double coset of the
other (`TauCeti.doubleCosetMk_eq_mk_iff_mem`).  Among those classes the class of `1` is
distinguished: its double coset is the set `H * K` (`TauCeti.doubleCoset_one_eq_mul`), so a double
coset is the identity one exactly when its representative lies there
(`TauCeti.doubleCosetMk_eq_mk_one_iff`).  For `K = H` that set is `H`
(`TauCeti.doubleCoset_one_self`) and the condition reads `s ∈ H`
(`TauCeti.doubleCosetMk_eq_mk_one_iff_mem`), which is what lets a statement quantified over the
non-identity double cosets `H \ G / H` be rewritten as a statement quantified over the elements
outside `H`.

## Main statements

* `TauCeti.doubleCosetMk_eq_mk_iff_mem`: the double cosets of `s` and `a` agree exactly when
  `s ∈ H a K`.
* `TauCeti.doubleCoset_one_eq_mul` and `TauCeti.doubleCoset_one_self`: the double coset of `1`
  with respect to sets `s` and `t` is `s * t`, which for a submonoid `s = t = H` is `H`.
* `TauCeti.doubleCosetMk_eq_mk_one_iff`: the double coset of `s` is the identity one exactly when
  `s ∈ H * K`.
* `TauCeti.doubleCosetMk_eq_mk_one_iff_mem`: for `K = H`, that condition is `s ∈ H`.
* `TauCeti.subsingleton_doubleCosetQuotient_iff`: the identity double coset is the only one
  exactly when `H * K` is the whole group.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Two elements have the same double coset exactly when one lies in the double coset of the
other**: `HsK = HaK` if and only if `s ∈ HaK`.  This is `DoubleCoset.eq` read through
`DoubleCoset.mem_doubleCoset`. -/
theorem doubleCosetMk_eq_mk_iff_mem (H K : Subgroup G) (a s : G) :
    DoubleCoset.mk H K s = DoubleCoset.mk H K a ↔
      s ∈ DoubleCoset.doubleCoset a (H : Set G) (K : Set G) := by
  rw [eq_comm, DoubleCoset.eq, DoubleCoset.mem_doubleCoset]
  simp

/-- **The identity double coset is the set `s * t`**: multiplying `1` by `s` on the left and `t` on
the right leaves the pointwise product of the two sets. -/
theorem doubleCoset_one_eq_mul {α : Type*} [MulOneClass α] (s t : Set α) :
    DoubleCoset.doubleCoset (1 : α) s t = s * t := by
  simp [DoubleCoset.doubleCoset]

/-- **The identity double coset of a submonoid `H` with itself is `H`.**  This is
`TauCeti.doubleCoset_one_eq_mul` for `s = t = H`, where the set `H * H` is `H`; in particular, the
identity double coset of `H \ G / H` is `H` for a subgroup `H`. -/
@[simp]
theorem doubleCoset_one_self {M S : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M]
    (H : S) :
    DoubleCoset.doubleCoset (1 : M) (H : Set M) (H : Set M) = (H : Set M) := by
  rw [doubleCoset_one_eq_mul, coe_mul_coe]

/-- **A double coset is the identity one exactly when its representative lies in `H * K`**:
`HsK = H · 1 · K` if and only if `s = a * b` with `a ∈ H` and `b ∈ K`. -/
theorem doubleCosetMk_eq_mk_one_iff (H K : Subgroup G) (s : G) :
    DoubleCoset.mk H K s = DoubleCoset.mk H K 1 ↔ s ∈ (H : Set G) * K := by
  rw [doubleCosetMk_eq_mk_iff_mem, doubleCoset_one_eq_mul]

/-- **The identity double coset of `H \ G / H` is the class of the elements of `H`.**  This is
`TauCeti.doubleCosetMk_eq_mk_one_iff` for `K = H`, where the condition `s ∈ H * H` is `s ∈ H`. -/
@[simp]
theorem doubleCosetMk_eq_mk_one_iff_mem (H : Subgroup G) (s : G) :
    DoubleCoset.mk H H s = DoubleCoset.mk H H 1 ↔ s ∈ H := by
  rw [doubleCosetMk_eq_mk_one_iff, coe_mul_coe, SetLike.mem_coe]

/-- The chosen representative of the identity double coset of `H` lies in `H`. -/
theorem _root_.Subgroup.doubleCoset_out_mk_one_mem (H : Subgroup G) :
    (DoubleCoset.mk H H 1).out ∈ H :=
  (doubleCosetMk_eq_mk_one_iff_mem H _).mp (DoubleCoset.out_eq' _)

/-- **There is a single double coset exactly when `H * K` is the whole group**: `H \ G / K` has
at most one element if and only if every element of `G` is a product of an element of `H` and an
element of `K`. -/
theorem subsingleton_doubleCosetQuotient_iff (H K : Subgroup G) :
    Subsingleton (DoubleCoset.Quotient (H : Set G) (K : Set G)) ↔
      (H : Set G) * (K : Set G) = Set.univ := by
  simp_rw [subsingleton_iff_forall_eq (DoubleCoset.mk H K 1), Set.eq_univ_iff_forall,
    ← doubleCosetMk_eq_mk_one_iff]
  exact ⟨fun h s ↦ h _, fun h q ↦ DoubleCoset.out_eq' q ▸ h q.out⟩

end TauCeti
