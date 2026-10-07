/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Tangent cones of linear subspaces and of curves

Two basic facts about Mathlib's tangent cone `tangentConeAt`. The subspace calculation lets
flattening charts identify their model subspaces with intrinsic tangent spaces, while the curve
lemma places velocities of invariant flows in the tangent cones of their invariant sets.

## Main results

* `Submodule.tangentConeAt_eq`: the tangent cone of a closed subspace at one of its points is the
  subspace itself.
* `HasDerivAt.mem_tangentConeAt`: the velocity of a curve lying in a set is tangent to the set.
-/

public section

open Filter Set Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Submodule

/-- The tangent cone of a closed linear subspace at one of its points is the subspace itself. -/
theorem tangentConeAt_eq (L : Submodule 𝕜 E) (hL : IsClosed (L : Set E)) {x : E} (hx : x ∈ L) :
    tangentConeAt 𝕜 (L : Set E) x = L := by
  refine Subset.antisymm (fun v hv ↦ ?_) fun v hv ↦ ?_
  · obtain ⟨ι, l, hl, c, d, -, hdL, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
    refine hL.mem_of_tendsto hcd (hdL.mono fun n hn ↦ ?_)
    exact L.smul_mem _ (by simpa using L.sub_mem hn hx)
  · refine mem_tangentConeAt_of_add_smul_mem (l := 𝓝[≠] (0 : 𝕜)) (c := id) tendsto_id
      (Eventually.of_forall fun c ↦ L.add_mem hx (L.smul_mem c hv))

end Submodule

/-- The velocity of a curve which stays in a set `S` near time `t` lies in the tangent cone of `S`
at the point reached at time `t`. -/
theorem HasDerivAt.mem_tangentConeAt {γ : 𝕜 → E} {v : E} {t : 𝕜} {S : Set E}
    (hγ : HasDerivAt γ v t) (hS : ∀ᶠ s in 𝓝 t, γ s ∈ S) : v ∈ tangentConeAt 𝕜 S (γ t) := by
  obtain ⟨U, hU, hUS⟩ := (Filter.eventually_iff_exists_mem).1 hS
  have hmaps := hγ.hasFDerivAt.hasFDerivWithinAt.mapsTo_tangent_cone (s := U)
    (by rw [tangentConeAt_of_mem_nhds hU]; exact mem_univ (1 : 𝕜))
  refine tangentConeAt_mono ?_ (by simpa using hmaps)
  rintro _ ⟨s, hs, rfl⟩
  exact hUS s hs
