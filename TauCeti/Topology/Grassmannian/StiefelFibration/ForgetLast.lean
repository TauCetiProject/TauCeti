/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
public import TauCeti.Topology.FiberBundle.Empty
public import TauCeti.Topology.Grassmannian.ForgetLast
public import TauCeti.Topology.Grassmannian.StiefelFibration.Unitary
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# The sphere bundles `V_(r+1)(𝕜^N) → V_r(𝕜^N)` and connectivity of Stiefel manifolds

Let `𝕜` be `ℝ` or `ℂ` (any `RCLike 𝕜`), and let `d = finrank ℝ 𝕜` be its real dimension. Deleting
the last vector of an orthonormal frame is the map
`finiteOrthonormalFrame.forgetLast : V_(r+1)(𝕜^N) → V_r(𝕜^N)`, whose fibres are the unit spheres
of the orthogonal complements of the frames (`finiteOrthonormalFrame.forgetLastFiberSphere`), unit
spheres of `𝕜^(N-r)`, of real dimension `d (N - r) - 1`. This map is a locally trivial bundle
with this sphere as fibre, and hence a Serre fibration; for `N ≤ r` the total space and the
sphere are empty. The map is equivariant for
the unitary group `U(N)`, so a continuous local section of the orbit map `U(N) → V_r(𝕜^N)` through
the standard frame (which is the unitary Stiefel fibration `TauCeti.unitaryFrameMap`) translates
the fibre over the standard frame onto the nearby fibres
(`TauCeti.equivariantLocalSectionTrivialization`).

Since the fibre is `(d (N - r) - 2)`-connected, the map is `(d (N - r) - 1)`-connected. Starting
from the one-point space `V_0(𝕜^N)`, induction along the tower
`V_r(𝕜^N) → V_(r-1)(𝕜^N) → ⋯ → V_0(𝕜^N)` shows that the homotopy groups `π_k` of `V_r(𝕜^N)` vanish
for `k + 1 < d (N - r + 1)`. Over `ℝ` this says that `V_r(ℝ^N)` is `(N - r - 1)`-connected, and
over `ℂ` that `V_r(ℂ^N)` is `2 (N - r)`-connected; in particular every complex Stiefel manifold
`V_r(ℂ^N)`, `r ≤ N`, is path-connected, including the unitary group `V_N(ℂ^N) ≅ U(N)`.

For `r = 1` the base is the unit sphere (`TauCeti.finiteOrthonormalFrame.sphereHomeomorph`), and
the map sends an orthonormal two-frame to its first vector: for `𝕜 = ℂ` this is the sphere bundle
`S^(2N-3) → V₂(ℂ^N) → S^(2N-1)` of ordered orthonormal two-frames of `ℂ^N` over their first vector.

## Main results

* `TauCeti.finiteOrthonormalFrame.exists_trivialization_forgetLast`: forgetting the last vector
  has a chart around each frame, with fibre the unit sphere of `𝕜^(N-r)`.
* `TauCeti.finiteOrthonormalFrame.forgetLast_mem_serreFibrations`: it is a Serre fibration.
* `TauCeti.finiteOrthonormalFrame.isNConnected_forgetLast`: it is a `(d (N - r) - 1)`-connected
  map.
* `TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup`: `π_k(V_r(𝕜^N))` is trivial for
  `k + 1 + d r < d (N + 1)`; `TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup_real` and
  `TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup_complex` are the cases
  `k + r < N` over `ℝ` and `k ≤ 2 (N - r)` over `ℂ`.
* `TauCeti.finiteOrthonormalFrame.nontrivial_homotopyGroup_oneFrame`: `π_(N-1)(V_1(ℝ^N))` is
  nontrivial for `N ≥ 3`.
* `TauCeti.finiteOrthonormalFrame.pathConnectedSpace`: `V_r(𝕜^N)` is path-connected for `r < N`,
  and `TauCeti.finiteOrthonormalFrame.pathConnectedSpace_complex`: `V_r(ℂ^N)` is path-connected
  for `r ≤ N`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 4.53 (the
  fibrations `S^(n-k-1) → V_(k+1)(ℝⁿ) → V_k(ℝⁿ)` and their complex analogues, and the
  connectivity of Stiefel manifolds).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §25.
-/

public section

open Metric Set Topology Module

noncomputable section

namespace TauCeti.finiteOrthonormalFrame

variable {𝕜 : Type*} [RCLike 𝕜] {r N : ℕ}

/-! ### Local triviality -/

/-- Forgetting the last vector `V_(r+1)(𝕜^N) → V_r(𝕜^N)` has a chart with fibre the unit sphere
of `𝕜^(N-r)` around each orthonormal `r`-frame. For `N ≤ r` there is no orthonormal
`(r + 1)`-frame and the sphere of `𝕜^0` is empty, so the chart is global with empty fibre. -/
theorem exists_trivialization_forgetLast (b : finiteOrthonormalFrame 𝕜 r N) :
    ∃ e : Bundle.Trivialization (sphere (0 : EuclideanSpace 𝕜 (Fin (N - r))) 1)
      (forgetLast : finiteOrthonormalFrame 𝕜 (r + 1) N → finiteOrthonormalFrame 𝕜 r N),
      b ∈ e.baseSet := by
  rcases lt_or_ge r N with h | h
  swap
  · have := isEmpty_of_lt (𝕜 := 𝕜) (Nat.lt_succ_of_le h)
    have : IsEmpty (sphere (0 : EuclideanSpace 𝕜 (Fin (N - r))) 1) := by
      rw [Nat.sub_eq_zero_of_le h]
      infer_instance
    exact ⟨Bundle.Trivialization.ofIsEmpty _ _, by simp⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
  obtain ⟨c, hb⟩ := exists_trivialization_unitaryFrameMap (r := r) (m := m + 1) b
  let := unitaryMulAction 𝕜 (r + 1) (r + m + 1)
  let := unitaryMulAction 𝕜 r (r + m + 1)
  have : ContinuousSMul (Matrix.unitaryGroup (Fin (r + m + 1)) 𝕜)
      (finiteOrthonormalFrame 𝕜 (r + 1) (r + m + 1)) :=
    ⟨continuous_unitaryMap⟩
  obtain ⟨e₀, he₀⟩ := forgetLast_surjective h (standard 𝕜 h.le)
  -- The unitary Stiefel fibration is the orbit map of the standard frame, so the inverse of its
  -- chart at the fibre coordinate `1` is a local section of that orbit map.
  let e := equivariantLocalSectionTrivialization forgetLast continuous_forgetLast
    (fun A g ↦ forgetLast_unitaryMap A g) _ ⟨e₀, he₀⟩ c.baseSet c.open_baseSet
    (fun f ↦ c.toOpenPartialHomeomorph.symm (f, 1)) c.continuousOn_symm_prodMk_left
    fun f hf ↦ (unitaryFrameMap_eq_smul_standard _).symm.trans (c.proj_symm_apply' hf)
  refine ⟨e.transFiberHomeomorph (forgetLastFiberSphere _), ?_⟩
  simpa only [Bundle.Trivialization.transFiberHomeomorph, e,
    equivariantLocalSectionTrivialization_baseSet]
    using hb

/-- Forgetting the last vector `V_(r+1)(𝕜^N) → V_r(𝕜^N)` is a Serre fibration: it is locally
trivial with fibre the unit sphere of `𝕜^(N-r)`. -/
theorem forgetLast_mem_serreFibrations :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨forgetLast, continuous_forgetLast⟩ :
        _root_.TopCat.of (finiteOrthonormalFrame 𝕜 (r + 1) N) ⟶
          _root_.TopCat.of (finiteOrthonormalFrame 𝕜 r N)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization exists_trivialization_forgetLast

/-! ### Connectivity -/

/-- For `r < N`, forgetting the last vector `V_(r+1)(𝕜^N) → V_r(𝕜^N)` is a
`(d (N - r) - 1)`-connected map, where `d = finrank ℝ 𝕜`: its fibres are unit spheres of
`𝕜^(N-r)`, of real dimension `d (N - r) - 1`, which are `(d (N - r) - 2)`-connected. -/
theorem isNConnected_forgetLast (h : r < N) :
    (⟨forgetLast, continuous_forgetLast⟩ :
      C(finiteOrthonormalFrame 𝕜 (r + 1) N, finiteOrthonormalFrame 𝕜 r N)).IsNConnected
        (finrank ℝ 𝕜 * (N - r) - 1) := by
  refine (TopCat.isNConnected_iff_of_mem_serreFibrations forgetLast_mem_serreFibrations _).2
    fun b ↦ ⟨?_, fun e k hk ↦ ?_⟩
  · obtain ⟨g, hg⟩ := forgetLast_surjective h b
    exact ⟨⟨g, hg⟩⟩
  · -- The fibre of the `TopCat` morphism is the fibre `{g // forgetLast g = b}`.
    let φ := ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).trans (forgetLastFiberSphere b)
    have hpos : 0 < finrank ℝ 𝕜 * (N - r) := Nat.mul_pos finrank_pos (by omega)
    have hfin : finrank ℝ (EuclideanSpace 𝕜 (Fin (N - r))) = finrank ℝ 𝕜 * (N - r) - 1 + 1 := by
      rw [← finrank_mul_finrank ℝ 𝕜, finrank_euclideanSpace_fin]
      omega
    have := subsingleton_homotopyGroup_sphere_of_lt hfin (N := Fin k) (by simp; omega) (φ e)
    exact (HomotopyGroup.homeomorphEquiv φ e).subsingleton

/-- **Connectivity of Stiefel manifolds.** Let `d = finrank ℝ 𝕜`. The homotopy group of the
Stiefel manifold `V_r(𝕜^N)` indexed by a finite type of `k` cube directions is trivial whenever
`k + 1 + d r < d (N + 1)`, that is `k + 1 < d (N - r + 1)`. Over `ℝ` this is `k + r < N`
(`TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup_real`), and over `ℂ` it is
`k ≤ 2 (N - r)` (`TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup_complex`). -/
theorem subsingleton_homotopyGroup {M : Type*}
    (h : Nat.card M + 1 + finrank ℝ 𝕜 * r < finrank ℝ 𝕜 * (N + 1))
    (f : finiteOrthonormalFrame 𝕜 r N) :
    Subsingleton (HomotopyGroup M (finiteOrthonormalFrame 𝕜 r N) f) := by
  -- For infinitely many cube directions every homotopy set is trivial.
  cases finite_or_infinite M
  swap
  · infer_instance
  have hd : 0 < finrank ℝ 𝕜 := finrank_pos
  induction r with
  | zero => infer_instance
  | succ r ih =>
    -- `d (r + 1) < d (N + 1)` gives `r < N`, so the last vector can be forgotten.
    have hr : r < N := by
      by_contra! hN
      nlinarith [Nat.mul_le_mul_left (finrank ℝ 𝕜) (Nat.succ_le_succ hN)]
    have := ih (by nlinarith) (forgetLast f)
    refine ((isNConnected_forgetLast hr).map_injective M ?_ f).subsingleton
    have : finrank ℝ 𝕜 * (N - r) + finrank ℝ 𝕜 * (r + 1) = finrank ℝ 𝕜 * (N + 1) := by
      rw [← mul_add]
      congr 1
      omega
    omega

/-- **Connectivity of real Stiefel manifolds.** The Stiefel manifold `V_r(ℝ^N)` of orthonormal
`r`-frames is `(N - r - 1)`-connected: its homotopy group indexed by a finite type of `k` cube
directions is trivial whenever `k + r < N`. -/
theorem subsingleton_homotopyGroup_real {M : Type*} (h : Nat.card M + r < N)
    (f : finiteOrthonormalFrame ℝ r N) :
    Subsingleton (HomotopyGroup M (finiteOrthonormalFrame ℝ r N) f) :=
  subsingleton_homotopyGroup (by simp only [finrank_self]; omega) f

/-- **Connectivity of complex Stiefel manifolds.** The Stiefel manifold `V_r(ℂ^N)` of orthonormal
`r`-frames is `2 (N - r)`-connected: its homotopy group indexed by a finite type of `k` cube
directions is trivial whenever `k ≤ 2 (N - r)`. -/
theorem subsingleton_homotopyGroup_complex {M : Type*} (h : Nat.card M ≤ 2 * (N - r))
    (f : finiteOrthonormalFrame ℂ r N) :
    Subsingleton (HomotopyGroup M (finiteOrthonormalFrame ℂ r N) f) := by
  have hr : r ≤ N := nonempty_iff_le.1 ⟨f⟩
  exact subsingleton_homotopyGroup (by simp only [Complex.finrank_real_complex]; omega) f

/-- The `(N - 1)`-th homotopy group of `V₁(ℝ^N) ≅ S^(N-1)` is nontrivial for `N ≥ 3`, modelled on
any finite index type `M` of `N - 1` cube directions. -/
theorem nontrivial_homotopyGroup_oneFrame {k : ℕ} {M : Type*} [Finite M] (hM : Nat.card M = k + 2)
    (b : finiteOrthonormalFrame ℝ 1 (k + 3)) :
    Nontrivial (HomotopyGroup M (finiteOrthonormalFrame ℝ 1 (k + 3)) b) := by
  have := nontrivial_homotopyGroup_sphere (n := k) (by simp) (sphereHomeomorph ℝ (k + 3) b)
  exact ((HomotopyGroup.homeomorphEquiv (sphereHomeomorph ℝ (k + 3)) b).trans
    (HomotopyGroup.congrEquiv (Finite.equivFinOfCardEq hM))).nontrivial

/-- For `r < N`, the Stiefel manifold `V_r(𝕜^N)` is path-connected. -/
theorem pathConnectedSpace (h : r < N) : PathConnectedSpace (finiteOrthonormalFrame 𝕜 r N) := by
  obtain ⟨f⟩ := (nonempty_iff_le (𝕜 := 𝕜)).2 h.le
  have hd : 0 < finrank ℝ 𝕜 := finrank_pos
  refine (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero f).2
    (subsingleton_homotopyGroup ?_ f)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  nlinarith

/-- For `r ≤ N`, the complex Stiefel manifold `V_r(ℂ^N)` is path-connected. For `r = N` this
includes the unitary group `U(N) ≃ₜ V_N(ℂ^N)` (`TauCeti.finiteOrthonormalFrame.unitaryHomeomorph`),
unlike the real case, where `V_N(ℝ^N) ≅ O(N)` has two components. -/
theorem pathConnectedSpace_complex (h : r ≤ N) :
    PathConnectedSpace (finiteOrthonormalFrame ℂ r N) := by
  obtain ⟨f⟩ := (nonempty_iff_le (𝕜 := ℂ)).2 h
  exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero f).2
    (subsingleton_homotopyGroup_complex (by simp) f)

end TauCeti.finiteOrthonormalFrame
