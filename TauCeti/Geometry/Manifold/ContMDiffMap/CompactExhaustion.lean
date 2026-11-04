/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Smooth limits of sequences stabilizing along a compact exhaustion

A sequence of `C^n` maps `F : ℕ → C^n⟮I, M; J, Y⟯` which stops changing on each member `L r` of a
compact exhaustion of `M` from some index on has a `C^n` limit: near every point the sequence is
eventually constant, so the pointwise limit is locally one of the maps `F (N + 1)`. No
convergence argument is needed. This is the gluing step of constructions which correct a map
successively on the compact sets `L r`.
-/

public section

open Filter Set
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M Y : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace Y] [ChartedSpace H' Y]
  {n : WithTop ℕ∞}

/-- A sequence of `C^n` maps which stabilizes along a compact exhaustion `L`, in the sense that
the maps of index `r + 1` and `r + 2` agree on `L r`, has a `C^n` limit which agrees with the map
of index `N + 1` on `L N`. -/
theorem exists_eqOn_of_eqOn_compactExhaustion (L : CompactExhaustion M)
    (F : ℕ → C^n⟮I, M; J, Y⟯) (hF : ∀ r, EqOn (F (r + 2)) (F (r + 1)) (L r)) :
    ∃ g : C^n⟮I, M; J, Y⟯, ∀ N, EqOn g (F (N + 1)) (L N) := by
  classical
  -- On `L N` nothing changes after index `N + 1`.
  have hstab : ∀ N, ∀ x ∈ L N, ∀ m, N + 1 ≤ m → F m x = F (N + 1) x := by
    intro N x hx m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
      rw [← ih]
      exact hF r (L.subset (by omega) hx)
  have hloc : ∀ N, EqOn (fun x ↦ F (L.find x + 1) x) (F (N + 1)) (L N) := fun N x hx ↦
    (hstab _ x (L.mem_find x) (N + 1) (by have := L.mem_iff_find_le.mp hx; omega)).symm
  exact ⟨⟨fun x ↦ F (L.find x + 1) x, fun x ↦ by
    obtain ⟨N, hN⟩ := L.exists_mem_nhds x
    exact (F (N + 1)).contMDiff.contMDiffAt.congr_of_eventuallyEq
      (eventuallyEq_of_mem hN (hloc N))⟩, hloc⟩

end ContMDiffMap
