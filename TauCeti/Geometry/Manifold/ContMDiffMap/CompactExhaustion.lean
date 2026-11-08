/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Algebra.Order.BigOperators.Sum.Telescoping

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

namespace CompactExhaustion

open scoped ContDiff Topology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If the perturbations `F (r + 1) - F r` are supported in `interior (L (r + 2))` and the seminorm
`q` kills functions which vanish near the compact set `A`, then the limit `g` of the stages is
within `t` of `f` for `q` as soon as each stage, as long as `A` meets `L (r + 2)`, is within
`t * w r`. -/
theorem seminorm_sub_lt_of_stages (L : CompactExhaustion M)
    (q : Seminorm ℝ C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) {A : Set M} (hA : IsCompact A)
    (hq0 : ∀ u : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ y ∈ A, (u : M → ℝ) =ᶠ[𝓝 y] 0) → q u = 0) {t : ℝ}
    (ht : 0 < t) {w : ℕ → ℝ} (hw : ∀ r, 0 < w r) (hwsum : ∀ N, ∑ r ∈ Finset.range N, w r ≤ 1)
    (F : ℕ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (hgF : ∀ N, EqOn g (F (N + 1)) (L N))
    (hsupp : ∀ r, tsupport (fun x ↦ F (r + 1) x - F r x) ⊆ interior (L (r + 2)))
    (hq : ∀ r, (A ∩ L (r + 2)).Nonempty → q (F (r + 1) - F r) < t * w r) :
    q (g - F 0) < t := by
  obtain ⟨N, hN⟩ := L.exists_superset_of_isCompact hA
  have hzero : q (g - F (N + 2)) = 0 := hq0 _ fun y hy ↦ by
    filter_upwards [mem_interior_iff_mem_nhds.mp (L.subset_interior_succ N (hN hy))] with z hz
    simp [hgF (N + 1) hz]
  have hterm : ∀ r ≤ N + 1, q (F (r + 1) - F r) < t * w r := by
    intro r _
    by_cases hi : (A ∩ L (r + 2)).Nonempty
    · exact hq r hi
    · rw [hq0 _ fun y hy ↦ ?_]
      · exact mul_pos ht (hw r)
      · have hy' : y ∉ tsupport fun x ↦ F (r + 1) x - F r x := fun h ↦
          hi ⟨y, hy, interior_subset (hsupp r h)⟩
        simpa [Pi.sub_def] using notMem_tsupport_iff_eventuallyEq.mp hy'
  calc q (g - F 0) = q ((F (N + 1 + 1) - F 0) + (g - F (N + 2))) := by congr 1; abel
    _ ≤ q (F (N + 1 + 1) - F 0) + q (g - F (N + 2)) := map_add_le_add _ _ _
    _ < t := by
      rw [hzero, add_zero]
      exact TauCeti.lt_of_forall_sub_lt_mul q (map_zero _).le (map_add_le_add _) ht hwsum F (N + 1)
        hterm

/-- The limit `g` of stages which each change a point `x` by less than `ε x * w r` (and only
inside `L (r + 2)`) is within `ε x` of `F 0` at `x`. -/
theorem abs_sub_lt_of_stages (L : CompactExhaustion M) {ε : M → ℝ} (hε₀ : ∀ x, 0 < ε x)
    {w : ℕ → ℝ} (hw : ∀ r, 0 < w r) (hwsum : ∀ N, ∑ r ∈ Finset.range N, w r ≤ 1)
    (F : ℕ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
    (hgF : ∀ N, EqOn g (F (N + 1)) (L N))
    (hsupp : ∀ r, tsupport (fun x ↦ F (r + 1) x - F r x) ⊆ interior (L (r + 2)))
    (hε : ∀ r, ∀ x ∈ L (r + 2), |F (r + 1) x - F r x| < ε x * w r) (x : M) :
    |g x - F 0 x| < ε x := by
  obtain ⟨N, hN⟩ := L.exists_mem x
  have hterm : ∀ r ≤ N, |F (r + 1) x - F r x| < ε x * w r := by
    intro r _
    by_cases hx : x ∈ L (r + 2)
    · exact hε r x hx
    · have h0 : F (r + 1) x - F r x = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y ↦ F (r + 1) y - F r y) fun h ↦ hx (interior_subset (hsupp r h))
      rw [h0, abs_zero]
      exact mul_pos (hε₀ x) (hw r)
  rw [hgF N hN]
  exact TauCeti.lt_of_forall_sub_lt_mul (fun y : ℝ ↦ |y|) abs_zero.le abs_add_le (hε₀ x)
    hwsum (fun r ↦ F r x) N hterm

end CompactExhaustion
