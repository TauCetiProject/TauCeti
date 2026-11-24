/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Simple
public import TauCeti.GroupTheory.GroupAction.Primitive
import TauCeti.GroupTheory.Subgroup.Simple

/-!
# Simplicity from a primitive suborbit

Let a group `G` act faithfully and primitively on a finite set, let `x` be a point, and let `O` be
an orbit of the stabilizer `G_x` on which `G_x` acts quasi-primitively. For every normal subgroup
`N` of `G` in which the stabilizer `N_x` of `x` is nontrivial, the length of `O` divides the order
of `N_x` (`TauCeti.MulAction.natCard_orbit_stabilizer_dvd_natCard_stabilizer_of_normal`). This
file deduces a simplicity criterion that needs neither a prime dividing the degree exactly once in
the group order nor an identification of the point stabilizer.

When a prime `p` divides the length of `O` but `p ^ 2` does not divide the order of `G`, every
such `N` contains each element whose `p`-th power is `1`. If one of these elements normally
generates `G`, and no normal subgroup acts regularly, then `G` is simple. The last hypothesis can
be supplied by `TauCeti.stabilizer_ne_bot_of_forall_dvd_natCard_modEq_one`.

## Main results

* `TauCeti.isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card_orbit_stabilizer`: the
  simplicity criterion.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, §1.6 (normal subgroups of primitive groups)
  and §3.2 (orbits of the point stabilizer).
-/

public section

namespace TauCeti

open _root_.MulAction TauCeti.MulAction

variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]

/-- **Simplicity from a primitive suborbit.** Let `G` act faithfully and primitively on a set,
and let the stabilizer of `x` act quasi-primitively on its orbit of `y`. Suppose that a prime
`p` divides the length of this orbit, that `p ^ 2` does not divide the order of `G`, and that no
normal subgroup of `G` acts regularly. If an element `a` with `a ^ p = 1` normally generates `G`,
then `G` is simple. The set is finite, because `G` is finite and acts transitively on it. -/
theorem isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card_orbit_stabilizer
    (x y : X) [IsQuasiPreprimitive (stabilizer G x) (orbit (stabilizer G x) y)]
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card (orbit (stabilizer G x) y))
    (hcard : ¬ p ^ 2 ∣ Nat.card G)
    (hreg : ∀ (N : Subgroup G) [N.Normal] [IsPretransitive N X], stabilizer N x ≠ ⊥)
    (a : G) (ha : a ^ p = 1)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) : IsSimpleGroup G := by
  have : Finite G := Nat.finite_of_card_ne_zero fun h0 ↦ hcard (h0 ▸ dvd_zero _)
  have : Finite X := Finite.of_surjective (· • x) (exists_smul_eq G x)
  -- The orbit has at least `p` points, so two elements fixing `x` move `y` to different points.
  have : Nonempty (orbit (stabilizer G x) y) := (nonempty_orbit y).to_subtype
  have : Nontrivial (orbit (stabilizer G x) y) :=
    Finite.one_lt_card_iff_nontrivial.mp (hp.one_lt.trans_le (Nat.le_of_dvd Nat.card_pos hdvd))
  obtain ⟨⟨_, g, rfl⟩, ⟨_, k, rfl⟩, hgk⟩ := exists_pair_ne (orbit (stabilizer G x) y)
  have : Nontrivial G :=
    ⟨⟨g, k, fun h ↦ hgk (Subtype.ext (congrArg (· • y) (Subtype.ext h)))⟩⟩
  refine isSimpleGroup_of_normalClosure_eq_top_of_forall_prime_dvd_natCard hp hcard
    (fun N _ hN ↦ ?_) a ha hgen
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot N hN
  exact (hdvd.trans (natCard_orbit_stabilizer_dvd_natCard_stabilizer_of_normal y (hreg N))).trans
    (Subgroup.card_subgroup_dvd_card _)

end TauCeti
