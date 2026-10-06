/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod

/-!
# Integer approximation at finitely many levels

Every profinite integer has the same reductions as a single natural number at any prescribed
finite set of positive levels. The representative can be chosen below the least common multiple
of the levels. Thus finite observations of a profinite integer can always be realized by an
ordinary integer, even when the levels are not pairwise coprime.

`TauCeti.zHat.exists_nat_lt_lcm_forall_toZMod_eq` is the finite-level form of integer density.
It uses the existing projections on `Additive zHat`, without introducing another presentation
of the profinite integers. For the empty set the least common multiple is `1`, so `0` is an
admissible representative; level `1` imposes no restriction.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.3 and 4.1.
-/

public section

namespace TauCeti.zHat

universe u

/-- A natural number below the least common multiple of finitely many positive levels realizes
the reductions of a profinite integer at all those levels. No coprimality assumption is needed. -/
theorem exists_nat_lt_lcm_forall_toZMod_eq (a : Additive zHat.{u}) (s : Finset ℕ+) :
    ∃ k : ℕ, k < s.lcm (fun n ↦ (n : ℕ)) ∧
      ∀ n ∈ s, toZMod n (k : Additive zHat.{u}) = toZMod n a := by
  let m : ℕ+ := ⟨s.lcm (fun n ↦ (n : ℕ)),
    Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr fun n _ ↦ n.ne_zero)⟩
  refine ⟨(toZMod m a).val, ZMod.val_lt _, fun n hn ↦ ?_⟩
  have hnm : (n : ℕ) ∣ m := s.dvd_lcm hn
  have h := congrArg (ZMod.castHom hnm (ZMod n)) (ZMod.natCast_zmod_val (toZMod m a))
  simpa only [map_natCast, ZMod.castHom_apply, cast_toZMod hnm] using h

end TauCeti.zHat
