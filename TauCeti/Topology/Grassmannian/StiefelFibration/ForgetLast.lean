/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
public import TauCeti.Topology.Grassmannian.ForgetLast
public import TauCeti.Topology.Grassmannian.StiefelFibration.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# The sphere bundles `S^(N-r-1) → V_(r+1)(ℝ^N) → V_r(ℝ^N)` and connectivity of Stiefel manifolds

Deleting the last vector of an orthonormal frame is the map
`finiteOrthonormalFrame.forgetLast : V_(r+1)(ℝ^N) → V_r(ℝ^N)`, whose fibres are the unit spheres
of the orthogonal complements of the frames (`finiteOrthonormalFrame.forgetLastFiberSphere`). For
`r < N` this map is a locally trivial bundle with fibre `S^(N-r-1)`, and hence a Serre fibration.
The map is equivariant for `SO(N)`, so a continuous local section of the orbit map
`SO(N) → V_r(ℝ^N)` through the standard frame (which is the Stiefel fibration
`TauCeti.specialOrthogonalFrameMap`) translates the fibre over the standard frame onto the nearby
fibres (`TauCeti.equivariantLocalSectionTrivialization`).

Since the fibre `S^(N-r-1)` is `(N - r - 2)`-connected, the map is `(N - r - 1)`-connected.
Starting from the one-point space `V_0(ℝ^N)`, induction along the tower
`V_r(ℝ^N) → V_(r-1)(ℝ^N) → ⋯ → V_0(ℝ^N)` shows that the Stiefel manifold `V_r(ℝ^N)` is
`(N - r - 1)`-connected: its homotopy groups `π_k` vanish for `k < N - r`. For `r = 1` this is the
connectivity of the sphere `V_1(ℝ^N) ≅ S^(N-1)`; for `r = 2` it says that the first possibly
nontrivial group of `V_2(ℝ^(n+2))` is `π_n`.

## Main results

* `TauCeti.finiteOrthonormalFrame.exists_trivialization_forgetLast`: for `r < N`, forgetting the
  last vector has a chart with fibre `S^(N-r-1)` around each frame.
* `TauCeti.finiteOrthonormalFrame.forgetLast_mem_serreFibrations`: it is a Serre fibration.
* `TauCeti.finiteOrthonormalFrame.isNConnected_forgetLast`: it is an `(N - r - 1)`-connected map.
* `TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup`: `π_k(V_r(ℝ^N))` is trivial for
  `k + r < N`.
* `TauCeti.finiteOrthonormalFrame.pathConnectedSpace`: `V_r(ℝ^N)` is path-connected for `r < N`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 4.53 (the
  fibrations `S^(n-k-1) → V_(k+1)(ℝⁿ) → V_k(ℝⁿ)` and the connectivity of Stiefel manifolds).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §25.
-/

public section

open Metric Set Topology

noncomputable section

namespace TauCeti.finiteOrthonormalFrame

variable {r N : ℕ}

/-! ### Local triviality -/

/-- For `r < N`, forgetting the last vector `V_(r+1)(ℝ^N) → V_r(ℝ^N)` has a chart with fibre the
sphere `S^(N-r-1)` around each orthonormal `r`-frame. -/
theorem exists_trivialization_forgetLast (h : r < N) (b : finiteOrthonormalFrame ℝ r N) :
    ∃ e : Bundle.Trivialization (sphere (0 : EuclideanSpace ℝ (Fin (N - r))) 1)
      (forgetLast : finiteOrthonormalFrame ℝ (r + 1) N → finiteOrthonormalFrame ℝ r N),
      b ∈ e.baseSet := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
  obtain ⟨c, hb⟩ := exists_trivialization_specialOrthogonalFrameMap (r := r) (m := m + 1) b
  let := specialOrthogonalMulAction (r + 1) (r + m + 1)
  let := specialOrthogonalMulAction r (r + m + 1)
  have := continuousSMul_specialOrthogonalMulAction (r := r + 1) (N := r + m + 1)
  obtain ⟨e₀, he₀⟩ := forgetLast_surjective h (standard ℝ h.le)
  let e := equivariantLocalSectionTrivialization forgetLast continuous_forgetLast
    (fun A g ↦ by simp only [specialOrthogonal_smul_def, forgetLast_unitaryMap]) _ ⟨e₀, he₀⟩
    c.baseSet c.open_baseSet
    (fun f ↦ c.toOpenPartialHomeomorph.symm (f, 1)) c.continuousOn_symm_prodMk_left
    fun f hf ↦ (specialOrthogonalFrameMap_eq_smul_standard _).symm.trans (c.proj_symm_apply' hf)
  refine ⟨e.transFiberHomeomorph (forgetLastFiberSphere _), ?_⟩
  simpa only [Bundle.Trivialization.transFiberHomeomorph, e,
    equivariantLocalSectionTrivialization_baseSet]
    using hb

/-- For `r < N`, forgetting the last vector `V_(r+1)(ℝ^N) → V_r(ℝ^N)` is a Serre fibration: it is
locally trivial with fibre `S^(N-r-1)`. -/
theorem forgetLast_mem_serreFibrations (h : r < N) :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨forgetLast, continuous_forgetLast⟩ :
        _root_.TopCat.of (finiteOrthonormalFrame ℝ (r + 1) N) ⟶
          _root_.TopCat.of (finiteOrthonormalFrame ℝ r N)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization (exists_trivialization_forgetLast h)

/-! ### Connectivity -/

/-- For `r < N`, forgetting the last vector `V_(r+1)(ℝ^N) → V_r(ℝ^N)` is an `(N - r - 1)`-connected
map: its fibres are spheres `S^(N-r-1)`, which are `(N - r - 2)`-connected. -/
theorem isNConnected_forgetLast (h : r < N) :
    (⟨forgetLast, continuous_forgetLast⟩ :
      C(finiteOrthonormalFrame ℝ (r + 1) N, finiteOrthonormalFrame ℝ r N)).IsNConnected
        (N - r - 1) := by
  refine (TopCat.isNConnected_iff_of_mem_serreFibrations (forgetLast_mem_serreFibrations h) _).2
    fun b ↦ ⟨?_, fun e k hk ↦ ?_⟩
  · obtain ⟨g, hg⟩ := forgetLast_surjective h b
    exact ⟨⟨g, hg⟩⟩
  · -- The fibre of the `TopCat` morphism is the fibre `{g // forgetLast g = b}`.
    let φ := ((Homeomorph.refl _).subtype fun _ ↦ Iff.rfl).trans (forgetLastFiberSphere b)
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (N - r))) = N - r - 1 + 1 := by
      rw [finrank_euclideanSpace_fin]
      omega
    have := subsingleton_homotopyGroup_sphere_of_lt hfin (N := Fin k) (by simpa using hk) (φ e)
    exact (HomotopyGroup.homeomorphEquiv φ e).subsingleton

/-- **Connectivity of Stiefel manifolds.** The Stiefel manifold `V_r(ℝ^N)` of orthonormal
`r`-frames is `(N - r - 1)`-connected: its homotopy group indexed by a finite type of `k` cube
directions is trivial whenever `k + r < N`. -/
theorem subsingleton_homotopyGroup {M : Type*} [Finite M] (h : Nat.card M + r < N)
    (f : finiteOrthonormalFrame ℝ r N) :
    Subsingleton (HomotopyGroup M (finiteOrthonormalFrame ℝ r N) f) := by
  induction r with
  | zero => infer_instance
  | succ r ih =>
    have := ih (by omega) (forgetLast f)
    exact ((isNConnected_forgetLast (by omega)).map_injective M (by omega) f).subsingleton

/-- For `r < N`, the Stiefel manifold `V_r(ℝ^N)` is path-connected. -/
theorem pathConnectedSpace (h : r < N) : PathConnectedSpace (finiteOrthonormalFrame ℝ r N) := by
  obtain ⟨f⟩ : Nonempty (finiteOrthonormalFrame ℝ r N) := ⟨standard ℝ h.le⟩
  exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero f).2
    (subsingleton_homotopyGroup (by simpa using h) f)

end TauCeti.finiteOrthonormalFrame
