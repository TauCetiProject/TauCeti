/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The action of `GL(V)` on the subspaces of `V`

The automorphisms of a finite-dimensional vector space `V` act on its subspaces by taking images.
An automorphism maps a subspace `U` onto `Y` as soon as it maps `U` into `Y` and the two have the
same dimension, so the orbit of `U` consists of the subspaces of the dimension of `U`. With the
orbit-stabiliser theorem this counts the subspaces of a given dimension through the stabiliser of
one of them. Every dimension up to `dim V` occurs.

## Main results

* `Submodule.units_smul_eq_of_forall_mem`: an automorphism mapping `U` into a subspace `Y` of the
  same dimension maps `U` onto `Y`.
* `Submodule.mem_invtSubmodule_of_mem_stabilizer`: an automorphism stabilising `U` leaves `U`
  invariant.
* `Submodule.mem_orbit_units_iff`: the orbit of `U` is the set of subspaces of the dimension of `U`.
* `Submodule.card_stabilizer_mul_card_finrank_eq`: `|Stab(U)|` times the number of subspaces of
  the dimension of `U` is `|GL(V)|`.
* `Submodule.range_finrank`: the dimensions of the subspaces of `V` are `0, …, dim V`.

## References

* Adapted from the counting of subspaces by their orbits in the proof of
  `New.Hall.rankInner_mul_eq_sum_skew` of `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

open Module MulAction
open scoped Pointwise

namespace Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- An automorphism stabilising `U` leaves `U` invariant. -/
theorem mem_invtSubmodule_of_mem_stabilizer {g : (Module.End K V)ˣ} {U : Submodule K V}
    (hg : g ∈ stabilizer (Module.End K V)ˣ U) : U ∈ (g : Module.End K V).invtSubmodule :=
  (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun v hv ↦ by
    rw [← mem_stabilizer_iff.1 hg]
    exact Submodule.mem_map_of_mem hv

variable [FiniteDimensional K V]

/-- An automorphism mapping `U` into a subspace `Y` of the same dimension maps `U` onto `Y`. -/
theorem units_smul_eq_of_forall_mem (g : (Module.End K V)ˣ) {U Y : Submodule K V}
    (h : ∀ x ∈ U, (g : Module.End K V) x ∈ Y) (hd : finrank K Y = finrank K U) : g • U = Y :=
  Submodule.eq_of_le_of_finrank_eq (Submodule.map_le_iff_le_comap.2 h)
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv K V) g).finrank_map_eq U |>.trans hd.symm)

/-- The subspaces in the orbit of `U` under `GL(V)` are those of the dimension of `U`. -/
theorem mem_orbit_units_iff {U Y : Submodule K V} :
    Y ∈ orbit (Module.End K V)ˣ U ↔ finrank K Y = finrank K U := by
  refine ⟨?_, fun hY ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    exact ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V) g).finrank_map_eq U
  · obtain ⟨g, hg⟩ :=
      Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq U Y hY.symm)
    refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv g,
      units_smul_eq_of_forall_mem _ (fun x hx ↦ ?_) hY⟩
    simp [← hg ⟨x, hx⟩]

/-- Orbit-stabiliser: the order of the stabiliser of `U` in `GL(V)` times the number of subspaces
of the dimension of `U` is the order of `GL(V)`. -/
theorem card_stabilizer_mul_card_finrank_eq (U : Submodule K V) :
    Nat.card (stabilizer (Module.End K V)ˣ U) *
        Nat.card {Y : Submodule K V // finrank K Y = finrank K U} =
      Nat.card (Module.End K V)ˣ := by
  have h_orbit : orbit (Module.End K V)ˣ U = {Y : Submodule K V | finrank K Y = finrank K U} :=
    Set.ext fun _ ↦ mem_orbit_units_iff
  rw [← Subgroup.card_mul_index (stabilizer (Module.End K V)ˣ U), index_stabilizer, h_orbit,
    ← Nat.card_coe_set_eq]
  -- The coercion of the set `{Y | p Y}` to a type is by definition the subtype `{Y // p Y}`.
  rfl

/-- The dimensions of the subspaces of `V` are `0, 1, …, dim V`. -/
theorem range_finrank :
    Set.range (fun U : Submodule K V ↦ finrank K U) = Set.Iic (finrank K V) := by
  refine Set.Subset.antisymm ?_ fun p hp ↦ ?_
  · rintro _ ⟨U, rfl⟩
    exact Submodule.finrank_le U
  · obtain ⟨f, hf⟩ : ∃ f : (Fin p → K) →ₗ[K] V, Function.Injective f :=
      finrank_le_iff_exists_linearMap.1 (by simpa using hp)
    exact ⟨_, (LinearMap.finrank_range_of_inj hf).trans (finrank_fin_fun K)⟩

end Submodule
