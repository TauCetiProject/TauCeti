/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Center

/-!
# Elements acting trivially on projective space

An element of a group acting linearly on a vector space fixes every projective point exactly
when its linear action is scalar. This criterion identifies the kernel of projective actions
of matrix subgroups without any finite-dimensionality assumption.

The argument generalizes the scalarity step in Mathlib's `Projectivization.SL_mulAction_ker`,
using `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`.
-/

public section

open scoped LinearAlgebra.Projectivization

open Projectivization

namespace TauCeti.Projectivization

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]
  [DistribMulAction G V] [SMulCommClass G K V]

/-- A linear group element fixes every line if and only if it acts by a single scalar on the
whole vector space. The statement also allows the zero vector space. -/
theorem forall_smul_eq_iff_exists_smul (g : G) :
    (∀ p : ℙ K V, g • p = p) ↔ ∃ c : K, ∀ v : V, g • v = c • v := by
  constructor
  · intro hg
    let f : V →ₗ[K] V := DistribMulAction.toModuleEnd K V g
    obtain ⟨c, hc⟩ := f.exists_eq_smul_id_of_forall_notLinearIndependent fun v ↦ by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · simpa [LinearIndependent.pair_iff' hv, mk_eq_mk_iff'] using! hg (mk K v hv)
    exact ⟨c, fun v ↦ by simpa [f] using DFunLike.congr_fun hc v⟩
  · rintro ⟨c, hc⟩ p
    induction p using Projectivization.ind with | _ v hv =>
    rw [smul_mk, mk_eq_mk_iff']
    exact ⟨c, (hc v).symm⟩

end TauCeti.Projectivization
