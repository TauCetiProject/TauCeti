/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Commuting
public import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import TauCeti.Algebra.Group.Subgroup.Centralizer

/-!
# Centralizers in free groups

A free group on at least two generators has trivial centre. Consequently, a free group with a
nontrivial central element is commutative, and, since subgroups of free groups are free
(Nielsen–Schreier), commutation is transitive on the nontrivial elements of a free group. The
centralizer of a nontrivial element of a free group is therefore abelian, hence cyclic.

These are the facts from which maximal roots of elements of a free group are built, in
`TauCeti.GroupTheory.FreeGroup.MaximalRoot.Basic`. Free groups are also shown to have unique
roots for a fixed nonzero exponent, transporting Mathlib's instance for `FreeGroup α` along a
free basis.

## Main results

* `FreeGroup.mem_zpowers_of_of_commute`: an element commuting with a generator `of a` is a power
  of `of a`.
* `FreeGroup.centralizer_singleton_of`: the centralizer of a generator `of a` is the cyclic
  subgroup it generates.
* `FreeGroup.eq_one_of_commute_of_of_commute_of`: an element commuting with two distinct generators
  is trivial.
* `FreeGroup.center_eq_bot_of_nontrivial`: the centre of a free group on at least two generators
  is trivial.
* `FreeGroup.of_zpow_mul_of_zpow_eq_one_iff`: for distinct generators, `a ^ p * b ^ q = 1` only
  for `p = q = 0`.
* `FreeGroup.commute_of_zpow_of_zpow_iff`: nonzero powers of distinct generators do not commute.
* `IsFreeGroup.commute_of_commute`: in a free group, two elements commuting with a common
  nontrivial element commute with each other.
* `IsFreeGroup.isCyclic_centralizer`: the centralizer of a nontrivial element of a free group is
  cyclic.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §2.1 (free groups are commutative transitive).
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually
  free groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, proof of Lemma 21
  (centralizers of nontrivial elements of a free group are cyclic).
-/

/- Acknowledgment: the statements of the centre and centralizer results here follow the shape of
the interface proposed in Mathlib PR #42677 (`FreeGroup/Center.lean`, centre and centralizers of
free groups). No proofs from that PR are used. -/

public section

namespace FreeGroup

variable {α : Type*}

/-- An element of a free group commuting with a generator `of a` is a power of `of a`. -/
theorem mem_zpowers_of_of_commute {a : α} {z : FreeGroup α} (h : Commute z (of a)) :
    z ∈ Subgroup.zpowers (of a) := by
  obtain ⟨r, m, n, rfl, hr⟩ := (IsFreeGroup.commute_iff_exists_common_zpow z (of a)).1 h
  have hn : n * n = 1 := by
    obtain hn | hn := Int.natAbs_eq_iff.1 (natAbs_eq_one_of_of_eq_zpow hr) <;> simp [hn]
  have hra : r = of a ^ n := by rw [hr, ← zpow_mul, hn, zpow_one]
  rw [hra, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

/-- The centralizer of a generator `of a` of a free group is the cyclic subgroup it generates. -/
theorem centralizer_singleton_of (a : α) : Subgroup.centralizer {of a} = Subgroup.zpowers (of a) :=
  le_antisymm
    (fun _ hz => mem_zpowers_of_of_commute (Subgroup.mem_centralizer_singleton_iff.1 hz))
    (Subgroup.zpowers_le_centralizer_singleton _)

/-- An element of a free group commuting with two distinct generators is trivial. -/
theorem eq_one_of_commute_of_of_commute_of {a b : α} (hab : a ≠ b) {z : FreeGroup α}
    (ha : Commute z (of a)) (hb : Commute z (of b)) : z = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_of_commute ha)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_of_commute hb)
  rw [(eq_of_of_zpow_eq_of_zpow hab hn.symm).1, zpow_zero]

/-- The centre of a free group on at least two generators is trivial. -/
theorem center_eq_bot_of_nontrivial [Nontrivial α] : Subgroup.center (FreeGroup α) = ⊥ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz ↦ ?_
  exact eq_one_of_commute_of_of_commute_of hab (Subgroup.mem_center_iff.1 hz (of a)).symm
    (Subgroup.mem_center_iff.1 hz (of b)).symm

end FreeGroup

namespace IsFreeGroup

variable {G : Type*} [Group G] [IsFreeGroup G]

/-- A free group has unique roots for every fixed nonzero exponent: `x ^ n = y ^ n` with `n ≠ 0`
forces `x = y`. In particular a free group is torsion-free. -/
instance : HasUniqueRoots G :=
  Function.Injective.hasUniqueRoots (toFreeGroup G).toMonoidHom (toFreeGroup G).injective

/-- A free group with a nontrivial central element is commutative. -/
theorem isMulCommutative_of_mem_center {x : G} (hx : x ∈ Subgroup.center G) (hx1 : x ≠ 1) :
    IsMulCommutative G := by
  let e := toFreeGroup G
  have : Subsingleton (Generators G) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    have hex : e x ∈ Subgroup.center (FreeGroup (Generators G)) :=
      Subgroup.mem_center_iff.2 fun g ↦ by
        obtain ⟨g, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx g]
    rw [FreeGroup.center_eq_bot_of_nontrivial, Subgroup.mem_bot, map_eq_one_iff e e.injective]
      at hex
    exact hx1 hex
  have : IsMulCommutative (FreeGroup (Generators G)) :=
    FreeGroup.isMulCommutative_iff_subsingleton.2 this
  exact e.symm.surjective.isMulCommutative

/-- Commutation is transitive on the nontrivial elements of a free group: if `x` and `z` both
commute with a nontrivial element `y`, then `x` and `z` commute. -/
theorem commute_of_commute {x y z : G} (hy : y ≠ 1) (hxy : Commute x y) (hyz : Commute y z) :
    Commute x z := by
  let H := Subgroup.closure ({x, y, z} : Set G)
  have hle : H ≤ Subgroup.centralizer {y} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro w (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hxy.eq
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hyz.eq.symm
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  have hcen : (⟨y, hyH⟩ : H) ∈ Subgroup.center H :=
    Subgroup.mem_center_iff.2 fun g ↦
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
  have : IsMulCommutative H :=
    isMulCommutative_of_mem_center hcen (by simpa [Subtype.ext_iff] using hy)
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hzH : z ∈ H := Subgroup.subset_closure (by simp)
  exact congrArg Subtype.val (mul_comm' (⟨x, hxH⟩ : H) ⟨z, hzH⟩)

/-- The centralizer of a nontrivial element of a free group is abelian. -/
theorem isMulCommutative_centralizer {x : G} (hx : x ≠ 1) :
    IsMulCommutative (Subgroup.centralizer {x}) :=
  ⟨⟨fun a b ↦ Subtype.ext <| commute_of_commute hx
    (Subgroup.mem_centralizer_singleton_iff.1 a.2)
    (Subgroup.mem_centralizer_singleton_iff.1 b.2).symm⟩⟩

/-- The centralizer of a nontrivial element of a free group is cyclic. -/
theorem isCyclic_centralizer {x : G} (hx : x ≠ 1) : IsCyclic (Subgroup.centralizer {x}) :=
  have := isMulCommutative_centralizer hx
  Subgroup.isCyclic_of_isMulCommutative _

end IsFreeGroup

namespace FreeGroup

variable {α : Type*}

/-- For distinct generators `a ≠ b` of a free group, `a ^ p * b ^ q = 1` only for `p = q = 0`.
In particular `a ^ p * b ^ q ≠ 1` for all `p, q ≥ 1`: the noncommuting pair `(a, b)` satisfies the
big powers condition with bound `1`. -/
theorem of_zpow_mul_of_zpow_eq_one_iff {a b : α} (hab : a ≠ b) {p q : ℤ} :
    of a ^ p * of b ^ q = 1 ↔ p = 0 ∧ q = 0 := by
  refine ⟨fun h => ?_, fun ⟨hp, hq⟩ => by simp [hp, hq]⟩
  simpa using eq_of_of_zpow_eq_of_zpow hab ((mul_eq_one_iff_eq_inv.1 h).trans (zpow_neg _ q).symm)

/-- Nonzero powers of distinct generators of a free group do not commute: `of a ^ m` and
`of b ^ n` commute only when `m = 0` or `n = 0`. -/
theorem commute_of_zpow_of_zpow_iff {a b : α} (hab : a ≠ b) {m n : ℤ} :
    Commute (of a ^ m) (of b ^ n) ↔ m = 0 ∨ n = 0 := by
  refine ⟨fun h => or_iff_not_imp_right.2 fun hn => ?_, by rintro (rfl | rfl) <;> simp⟩
  -- `of a ^ m` commutes with `of b ^ n ≠ 1`, hence with `of b`, so it is a power of `of b`.
  have hbn : of b ^ n ≠ 1 := fun h1 =>
    hn (eq_of_of_zpow_eq_of_zpow hab.symm (h1.trans (zpow_zero (of a)).symm)).1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_of_commute
    (IsFreeGroup.commute_of_commute hbn h ((Commute.refl (of b)).zpow_left n)))
  exact (eq_of_of_zpow_eq_of_zpow hab hj.symm).1

end FreeGroup
