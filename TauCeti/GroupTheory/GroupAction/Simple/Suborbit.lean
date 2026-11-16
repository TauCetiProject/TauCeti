/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Simple.Basic

/-!
# Simplicity from a primitive suborbit

Let a group `G` act faithfully and primitively on a finite set, let `x` be a point, and let `O` be
an orbit of the stabilizer `G_x` on which `G_x` acts quasi-primitively. This file shows that, for
every normal subgroup `N` of `G` in which the stabilizer `N_x` of `x` is nontrivial, `N_x` is
transitive on `O`, so the length of `O` divides the order of `N`. It deduces a simplicity
criterion that needs neither a prime dividing the degree exactly once in the group order nor an
identification of the point stabilizer.

The subgroup `N_x` is normal in `G_x`, so it either fixes `O` pointwise or is transitive on `O`.
The first case is excluded by `TauCeti.MulAction.fixedPoints_stabilizer_eq_singleton_of_normal`:
a nontrivial `N_x` has no fixed point other than `x`.

When a prime `p` divides the length of `O` but `p ^ 2` does not divide the order of `G`, every
such `N` contains each element whose `p`-th power is `1`. If one of these elements normally
generates `G`, and no normal subgroup acts regularly, then `G` is simple. The last hypothesis can
be supplied by `TauCeti.stabilizer_ne_bot_of_forall_dvd_natCard_modEq_one`.

## Main results

* `TauCeti.isPretransitive_subgroupOf_stabilizer_orbit`: a normal subgroup with a nontrivial
  stabilizer of `x` meets the stabilizer of `x` in a subgroup acting transitively on each of its
  quasi-primitive orbits.
* `TauCeti.natCard_orbit_stabilizer_dvd_natCard_of_normal`: the length of such an orbit divides
  the order of the normal subgroup.
* `TauCeti.isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card_orbit_stabilizer`: the
  simplicity criterion.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, §1.5 and §1.6 (blocks, and normal subgroups
  of primitive groups), and §3.2 (orbits of the point stabilizer).
-/

public section

namespace TauCeti

open _root_.MulAction TauCeti.MulAction

variable {G X : Type*} [Group G] [MulAction G X] [Finite X] [FaithfulSMul G X]
  [IsPreprimitive G X]

/-- In a faithful primitive action on a finite set, let the stabilizer of `x` act
quasi-primitively on its orbit `O` of `y`, and let `N` be a normal subgroup in which the
stabilizer of `x` is nontrivial. Then the elements of `N` fixing `x` act transitively on `O`: they
form a normal subgroup of the stabilizer of `x`, and they do not all fix `y` unless `y = x`. -/
theorem isPretransitive_subgroupOf_stabilizer_orbit {x : X} (y : X)
    [IsQuasiPreprimitive (stabilizer G x) (orbit (stabilizer G x) y)]
    {N : Subgroup G} [N.Normal] (hN : stabilizer N x ≠ ⊥) :
    IsPretransitive (N.subgroupOf (stabilizer G x)) (orbit (stabilizer G x) y) := by
  have hM : (N.subgroupOf (stabilizer G x)).Normal := Subgroup.Normal.subgroupOf ‹_› _
  by_cases hyx : y = x
  · -- The orbit of `x` under its own stabilizer is a single point.
    subst hyx
    have : Subsingleton (orbit (stabilizer G y) y) :=
      ⟨fun u v ↦ by
        obtain ⟨u, g, rfl⟩ := u
        obtain ⟨v, k, rfl⟩ := v
        exact Subtype.ext (g.2.trans k.2.symm)⟩
    exact ⟨fun u v ↦ ⟨1, Subsingleton.elim _ _⟩⟩
  -- Otherwise the elements of `N` fixing `x` would all fix `y`, a second fixed point.
  refine IsQuasiPreprimitive.isPretransitive_of_normal fun hfix ↦ hyx ?_
  have hy : (⟨y, mem_orbit_self y⟩ : orbit (stabilizer G x) y) ∈
      fixedPoints (N.subgroupOf (stabilizer G x)) (orbit (stabilizer G x) y) :=
    hfix ▸ Set.mem_univ _
  have hmem : y ∈ fixedPoints (stabilizer N x) X := fun n ↦
    congrArg Subtype.val (hy ⟨⟨n, n.2⟩, n.1.2⟩)
  rwa [fixedPoints_stabilizer_eq_singleton_of_normal x hN, Set.mem_singleton_iff] at hmem

/-- In a faithful primitive action on a finite set, let the stabilizer of `x` act
quasi-primitively on its orbit of `y`. Then the length of this orbit divides the order of every
normal subgroup in which the stabilizer of `x` is nontrivial. -/
theorem natCard_orbit_stabilizer_dvd_natCard_of_normal {x : X} (y : X)
    [IsQuasiPreprimitive (stabilizer G x) (orbit (stabilizer G x) y)]
    {N : Subgroup G} [N.Normal] (hN : stabilizer N x ≠ ⊥) :
    Nat.card (orbit (stabilizer G x) y) ∣ Nat.card N := by
  have := isPretransitive_subgroupOf_stabilizer_orbit y hN
  have : Nonempty (orbit (stabilizer G x) y) := (nonempty_orbit y).to_subtype
  -- The inclusion of the elements of `N` fixing `x` into `N`.
  let f : N.subgroupOf (stabilizer G x) →* N :=
    ((stabilizer G x).subtype.comp (N.subgroupOf (stabilizer G x)).subtype).codRestrict N
      fun m ↦ m.2
  have hf : Function.Injective f := fun m₁ m₂ hm ↦
    Subtype.ext (Subtype.ext (congrArg (Subtype.val : N → G) hm))
  exact (natCard_dvd_natCard_of_isPretransitive (N.subgroupOf (stabilizer G x))).trans
    (Subgroup.card_dvd_of_injective f hf)

/-- **Simplicity from a primitive suborbit.** Let `G` act faithfully and primitively on a finite
set, and let the stabilizer of `x` act quasi-primitively on its orbit of `y`. Suppose that a prime
`p` divides the length of this orbit, that `p ^ 2` does not divide the order of `G`, and that no
normal subgroup of `G` acts regularly. If an element `a` with `a ^ p = 1` normally generates `G`,
then `G` is simple. -/
theorem isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card_orbit_stabilizer
    (x y : X) [IsQuasiPreprimitive (stabilizer G x) (orbit (stabilizer G x) y)]
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card (orbit (stabilizer G x) y))
    (hcard : ¬ p ^ 2 ∣ Nat.card G)
    (hreg : ∀ (N : Subgroup G) [N.Normal] [IsPretransitive N X], stabilizer N x ≠ ⊥)
    (a : G) (ha : a ^ p = 1)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) : IsSimpleGroup G := by
  -- The orbit has at least `p` points, so two elements fixing `x` move `y` to different points.
  have : Nonempty (orbit (stabilizer G x) y) := (nonempty_orbit y).to_subtype
  have : Nontrivial (orbit (stabilizer G x) y) :=
    Finite.one_lt_card_iff_nontrivial.mp (hp.one_lt.trans_le (Nat.le_of_dvd Nat.card_pos hdvd))
  obtain ⟨⟨_, g, rfl⟩, ⟨_, k, rfl⟩, hgk⟩ := exists_pair_ne (orbit (stabilizer G x) y)
  have : Nontrivial G := ⟨⟨g, k, fun h ↦ hgk (Subtype.ext (congrArg (fun c : G ↦ c • y) h))⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun N _ ↦ ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot N hN
  apply top_unique
  rw [← hgen]
  exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr
    (mem_of_pow_eq_one_of_dvd_natCard_of_not_sq_dvd hcard
      (hdvd.trans (natCard_orbit_stabilizer_dvd_natCard_of_normal y (hreg N))) ha))

end TauCeti
