/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.TranslationPerturbation
public import TauCeti.Dynamics.PeriodicPts.Persistence
import TauCeti.Analysis.Calculus.FDeriv.Perturbation

/-!
# Making the points of least period `k` nondegenerate by a symplectic perturbation

Let `(V, ω)` be a finite-dimensional symplectic vector space, for instance a chart of a surface
with its area form, let `φ : V → V` be a `C¹` map and `K` a compact set every point of which with
`φ^[k] x = x` has least period exactly `k`. This file shows that a symplectic map `ψ`, arbitrarily
close to the identity in `C¹` and equal to the identity outside a compact subset of a prescribed
open set `W ⊇ K`, makes every point `x ∈ K` with `(φ ∘ ψ)^[k] x = x` a nondegenerate fixed point
of `(φ ∘ ψ)^[k]` (`TauCeti.SymplecticForm.exists_isNondegenerateFixedPt_iterate_comp`).

The map `ψ` is a finite composition of the localized Hamiltonian translations of
`TauCeti.SymplecticForm.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate`. That theorem
treats one small ball `B` at a time, and needs every orbit starting in `B` to leave `B` until time
`k`. Near a point of least period `k` the points `x, φ x, …, φ^[k-1] x` are distinct, so small
balls around it have this property. Finitely many such balls cover the compact set of points of
period `k` in `K`, and the translations are applied one ball after the other. Each translation is
chosen so small in `C¹` that it keeps the conditions that were already obtained or are still
needed, all of which are `C¹`-open:

* the periodic points of period `k` in the balls already treated stay nondegenerate, by the
  persistence of nondegenerate periodic points
  (`IsCompact.exists_pos_forall_isNondegenerateFixedPt_iterate`);
* the orbits starting in each ball still leave it until time `k`;
* the part of `K` outside the balls still contains no point of period `k`.

The `C¹`-closeness of `g ∘ ψ` to `g` for `ψ` close to the identity is the continuity of
composition (`IsCompact.exists_pos_forall_differentiableAt_comp_and_norm_sub_le`), and that of the
iterates is `IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le`.

This is the step of a fixed period in the induction over the periods `1 ≤ k ≤ N` that makes the
periodic points of an area-preserving surface map nondegenerate up to a cutoff `N`. Points of
period `k` whose least period is a proper divisor of `k` lie on the finitely many orbits of smaller
period, which are made nondegenerate in all their iterates by the localized twists of
`TauCeti.Geometry.Symplectic.Hamiltonian.ReturnMapPerturbation`; this file excludes them by the
hypothesis on the least period.

## Main results

* `TauCeti.SymplecticForm.exists_isNondegenerateFixedPt_iterate_comp`: a `C¹`-small symplectic
  perturbation localized in `W` makes the points of period `k` in `K` nondegenerate, when all of
  them have least period `k`.

## References

* R. C. Robinson, *Generic properties of conservative systems*, Amer. J. Math. 92 (1970),
  562–603, for the local perturbations making the periodic points of conservative maps
  nondegenerate and their combination over a cover by small balls.
* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 3,
  §3, for the same scheme in the proof of the Kupka–Smale theorem.
-/

public section

noncomputable section

namespace TauCeti.SymplecticForm

open Filter Function Metric Set Topology
open scoped Manifold NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A map `ψ` is `η`-close to the identity in `C¹`: it is differentiable, moves no point by more
than `η`, and its derivative is within `η` of the identity everywhere. -/
private def IsNearId (η : ℝ) (ψ : V → V) : Prop :=
  Differentiable ℝ ψ ∧ (∀ w, ‖ψ w - w‖ ≤ η) ∧
    ∀ w, ‖fderiv ℝ ψ w - ContinuousLinearMap.id ℝ V‖ ≤ η

omit [FiniteDimensional ℝ V] in
/-- Closeness to the identity in `C¹` is monotone in the bound. -/
private theorem IsNearId.mono {η η' : ℝ} {ψ : V → V} (h : IsNearId η ψ) (hη : η ≤ η') :
    IsNearId η' ψ :=
  ⟨h.1, fun w ↦ (h.2.1 w).trans hη, fun w ↦ (h.2.2 w).trans hη⟩

omit [FiniteDimensional ℝ V] in
/-- The composition of a map `a`-close to the identity in `C¹` with one `b`-close to it is
`(a + b + a * b)`-close to it. -/
private theorem IsNearId.comp {a b : ℝ} {Ψ ψ : V → V} (hΨ : IsNearId a Ψ) (hψ : IsNearId b ψ) :
    IsNearId (a + b + a * b) (Ψ ∘ ψ) := by
  obtain ⟨hΨd, hΨ₀, hΨ₁⟩ := hΨ
  obtain ⟨hψd, hψ₀, hψ₁⟩ := hψ
  have ha : 0 ≤ a := (norm_nonneg _).trans (hΨ₀ 0)
  have hb : 0 ≤ b := (norm_nonneg _).trans (hψ₀ 0)
  refine ⟨hΨd.comp hψd, fun w ↦ ?_, fun w ↦ ?_⟩
  · calc ‖Ψ (ψ w) - w‖ ≤ ‖Ψ (ψ w) - ψ w‖ + ‖ψ w - w‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ a + b := add_le_add (hΨ₀ _) (hψ₀ w)
      _ ≤ a + b + a * b := le_add_of_nonneg_right (mul_nonneg ha hb)
  · -- `DΨ ∘ Dψ - 1 = (DΨ - 1) ∘ Dψ + (Dψ - 1)`, and `‖Dψ‖ ≤ 1 + b`.
    set A := fderiv ℝ Ψ (ψ w)
    set B := fderiv ℝ ψ w
    have hB : ‖B‖ ≤ 1 + b := by
      calc ‖B‖ = ‖(B - ContinuousLinearMap.id ℝ V) + ContinuousLinearMap.id ℝ V‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖B - ContinuousLinearMap.id ℝ V‖ + ‖ContinuousLinearMap.id ℝ V‖ := norm_add_le _ _
        _ ≤ b + 1 := add_le_add (hψ₁ w) ContinuousLinearMap.norm_id_le
        _ = 1 + b := add_comm _ _
    rw [fderiv_comp w (hΨd _) (hψd w)]
    calc ‖A.comp B - ContinuousLinearMap.id ℝ V‖
        = ‖(A - ContinuousLinearMap.id ℝ V).comp B + (B - ContinuousLinearMap.id ℝ V)‖ := by
          congr 1
          ext v
          simp
      _ ≤ ‖A - ContinuousLinearMap.id ℝ V‖ * ‖B‖ + ‖B - ContinuousLinearMap.id ℝ V‖ :=
          (norm_add_le _ _).trans (add_le_add_left (ContinuousLinearMap.opNorm_comp_le _ _) _)
      _ ≤ a * (1 + b) + b := by gcongr; exacts [hΨ₁ _, hψ₁ w]
      _ = a + b + a * b := by ring

omit [FiniteDimensional ℝ V] in
/-- A conclusion about the maps `C¹`-close to a `C¹` map `g` on a compact set `U` holds for the
compositions `g ∘ ψ` with every `ψ` close enough to the identity in `C¹`. -/
private theorem eventually_forall_isNearId_comp {g : V → V} (hg : ContDiff ℝ 1 g) {U : Set V}
    (hU : IsCompact U) {Q : (V → V) → Prop}
    (h : ∃ δ > 0, ∀ g' : V → V, (∀ y ∈ U, DifferentiableAt ℝ g' y) →
      (∀ y ∈ U, ‖g' y - g y‖ ≤ δ) → (∀ y ∈ U, ‖fderiv ℝ g' y - fderiv ℝ g y‖ ≤ δ) → Q g') :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ ψ, IsNearId η ψ → Q (g ∘ ψ) := by
  obtain ⟨δ, hδ, hQ⟩ := h
  obtain ⟨η₀, hη₀, hcomp⟩ := hU.exists_pos_forall_differentiableAt_comp_and_norm_sub_le
    (f₁ := id) (f₂ := g) (fun x _ ↦ differentiableAt_id)
    ((continuousOn_const (c := ContinuousLinearMap.id ℝ V)).congr fun _ _ ↦ fderiv_id)
    (fun y _ ↦ hg.differentiable one_ne_zero y)
    (fun y _ ↦ (hg.continuous_fderiv one_ne_zero).continuousAt) hδ univ_mem
  filter_upwards [Ioo_mem_nhdsGT hη₀] with η hη ψ ⟨hψd, hψ₀, hψ₁⟩
  have H := hcomp ψ g (fun x _ ↦ hψd x) (fun x _ ↦ (hψ₀ x).trans hη.2.le)
    (fun x _ ↦ by rw [fderiv_id]; exact (hψ₁ x).trans hη.2.le)
    (fun y _ ↦ hg.differentiable one_ne_zero y) (fun y _ ↦ by simp [hη₀.le])
    (fun y _ ↦ by simp [hη₀.le])
  exact hQ _ (fun y hy ↦ (H y hy).1) (fun y hy ↦ (H y hy).2.1) fun y hy ↦ (H y hy).2.2

/-- A compact neighbourhood of the first `l` points of the orbits of a compact set under a
continuous map. -/
private theorem exists_isCompact_mem_nhdsSet_iUnion_iterate_image {g : V → V} (hg : Continuous g)
    {C : Set V} (hC : IsCompact C) (l : ℕ) :
    ∃ U, IsCompact U ∧ U ∈ 𝓝ˢ (⋃ j < l, g^[j] '' C) := by
  have hO : IsCompact (⋃ j < l, g^[j] '' C) :=
    (finite_lt_nat l).isCompact_biUnion fun j _ ↦ hC.image (hg.iterate j)
  obtain ⟨δ, hδ, hU⟩ := hO.exists_isCompact_cthickening
  exact ⟨_, hU, cthickening_mem_nhdsSet _ hδ⟩

/-- **Avoidance is `C¹`-open.** If the `l`-th iterate of a `C¹` map `g` sends every point `y` of a
compact set `C` to a point `z` with `(y, z)` off a closed set `T`, then so does the `l`-th iterate
of `g ∘ ψ` for every `ψ` close enough to the identity in `C¹`. -/
private theorem eventually_forall_isNearId_iterate_comp_notMem {g : V → V} (hg : ContDiff ℝ 1 g)
    {C : Set V} (hC : IsCompact C) (l : ℕ) {T : Set (V × V)} (hT : IsClosed T)
    (h : ∀ y ∈ C, (y, g^[l] y) ∉ T) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ ψ, IsNearId η ψ → ∀ y ∈ C, (y, (g ∘ ψ)^[l] y) ∉ T := by
  -- The graph of `g^[l]` over `C` is compact and avoids `T`, hence so does a neighbourhood of it.
  have hG : IsCompact ((fun y ↦ (y, g^[l] y)) '' C) :=
    hC.image (continuous_id.prodMk (hg.continuous.iterate l))
  obtain ⟨θ, hθ, hθT⟩ := hG.exists_cthickening_subset_open hT.isOpen_compl
    (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
  obtain ⟨U, hU, hUn⟩ := exists_isCompact_mem_nhdsSet_iUnion_iterate_image hg.continuous hC l
  obtain ⟨δ, hδ, hit⟩ := hC.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le
    (fun _ _ _ _ ↦ hg.contDiffAt) hθ hUn
  refine eventually_forall_isNearId_comp (Q := fun g' ↦ ∀ y ∈ C, (y, g'^[l] y) ∉ T) hg hU
    ⟨δ, hδ, fun g' hg' hg'₀ hg'₁ y hy ↦ hθT ?_⟩
  refine mem_cthickening_of_dist_le _ (y, g^[l] y) θ _ (mem_image_of_mem _ hy) ?_
  simpa [Prod.dist_eq, dist_eq_norm, hθ.le] using (hit g' hg' hg'₀ hg'₁ y hy).2.1

/-- **Nondegeneracy is `C¹`-open.** If the points of period `k` of a `C¹` map `g` in a compact set
`L` are nondegenerate, so are those of `g ∘ ψ` for every `ψ` close enough to the identity
in `C¹`. -/
private theorem eventually_forall_isNearId_isNondegenerateFixedPt_iterate_comp {g : V → V}
    (hg : ContDiff ℝ 1 g) {L : Set V} (hL : IsCompact L) (k : ℕ)
    (hnd : ∀ x ∈ L, IsFixedPt g^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, V) g^[k] x) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ ψ, IsNearId η ψ →
      ∀ x ∈ L, IsFixedPt (g ∘ ψ)^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, V) (g ∘ ψ)^[k] x := by
  obtain ⟨U, hU, hUn⟩ := exists_isCompact_mem_nhdsSet_iUnion_iterate_image hg.continuous hL k
  exact eventually_forall_isNearId_comp hg hU
    (hL.exists_pos_forall_isNondegenerateFixedPt_iterate (fun _ _ _ _ ↦ hg.contDiffAt) hnd hUn)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Around a point `x ∈ W` whose first `k - 1` iterates differ from it, the closed balls of small
enough radius `2 r` lie in `W` and are left by every orbit starting in them until time `k`. -/
private theorem exists_pos_closedBall_subset_and_iterate_notMem {φ : V → V} (hφ : Continuous φ)
    {W : Set V} (hW : IsOpen W) {x : V} (hx : x ∈ W) {k : ℕ}
    (hmin : ∀ j, 0 < j → j < k → φ^[j] x ≠ x) :
    ∃ r > 0, closedBall x (2 * r) ⊆ W ∧
      ∀ y ∈ closedBall x (2 * r), ∀ j, 0 < j → j < k → φ^[j] y ∉ closedBall x (2 * r) := by
  suffices h : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall x (2 * r) ⊆ W ∧
      ∀ j ∈ Finset.range k, 0 < j → ∀ y ∈ closedBall x (2 * r), φ^[j] y ∉ closedBall x (2 * r) by
    obtain ⟨r, ⟨hrW, hr⟩, hr0⟩ := (h.and self_mem_nhdsWithin).exists
    exact ⟨r, hr0, hrW, fun y hy j hj hjk ↦ hr j (Finset.mem_range.2 hjk) hj y hy⟩
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW x hx
  refine Filter.Eventually.and ?_ ((Finset.eventually_all _).2 fun j hj ↦ ?_)
  · filter_upwards [Ioo_mem_nhdsGT (half_pos hρ)] with r hr
    exact (closedBall_subset_ball (by linarith [hr.2])).trans hρW
  · -- With `d = dist (φ^[j] x) x > 0`, take `2 r < d / 2` and `2 r` below a radius on which
    -- `φ^[j]` moves points by less than `d / 2`.
    by_cases hj0 : 0 < j
    · have hd : 0 < dist (φ^[j] x) x :=
        dist_pos.2 (hmin j hj0 (Finset.mem_range.1 hj))
      obtain ⟨ρ', hρ', hcont⟩ := Metric.continuousAt_iff.1 (hφ.iterate j).continuousAt
        (dist (φ^[j] x) x / 2) (half_pos hd)
      filter_upwards [Ioo_mem_nhdsGT (lt_min (half_pos hρ') (div_pos hd four_pos))] with r hr _ y hy
      rw [mem_closedBall] at hy ⊢
      have hr₁ := hr.2.trans_le (min_le_left _ _)
      have hr₂ := hr.2.trans_le (min_le_right _ _)
      have h := hcont (hy.trans_lt (by linarith))
      have := dist_triangle (φ^[j] x) (φ^[j] y) x
      rw [dist_comm] at h
      linarith
    · exact Eventually.of_forall fun r h ↦ absurd h hj0

/-- One ball of the induction: around a point `a` whose ball `closedBall a (2 * r)` is left by
every orbit of `g` starting in it until time `k`, a localized Hamiltonian translation `η`-close to
the identity in `C¹` makes the points of period `k` in `closedBall a r` nondegenerate. -/
private theorem exists_isNearId_isNondegenerateFixedPt_iterate_comp_closedBall
    (ω : SymplecticForm V) {g : V → V} (hg : ContDiff ℝ 1 g) {k : ℕ} (hk : 0 < k) {a : V} {r : ℝ}
    (hr : 0 < r)
    (hret : ∀ y ∈ closedBall a (2 * r), ∀ j, 0 < j → j < k → g^[j] y ∉ closedBall a (2 * r))
    {η : ℝ} (hη : 0 < η) :
    ∃ ψ : V → V, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∃ S, IsCompact S ∧ S ⊆ ball a (2 * r) ∧ ∀ w ∉ S, ψ w = w) ∧ IsNearId η ψ ∧
      (∀ w u v, ω (fderiv ℝ ψ w u) (fderiv ℝ ψ w v) = ω u v) ∧
      ∀ y ∈ closedBall a r, IsFixedPt (g ∘ ψ)^[k] y →
        IsNondegenerateFixedPt 𝓘(ℝ, V) (g ∘ ψ)^[k] y := by
  obtain ⟨H, hH, hHc, hHW, ⟨L, hX⟩, hψ⟩ := ω.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate
    hk (isCompact_closedBall a r) isOpen_ball (closedBall_subset_ball (by linarith))
    (fun y _ j _ ↦ hg.differentiable one_ne_zero _)
    (fun y hy j hj hjk h ↦ hret y (ball_subset_closedBall hy) j hj hjk (ball_subset_closedBall h))
    hη
  obtain ⟨-, -, hdisp, hderiv, hnd⟩ := hψ hX
  have hH' (n : ℕ) : ContDiff ℝ (n + 2) H := hH.of_le (WithTop.coe_le_coe.2 le_top)
  have hψs (n : ℕ) : ContDiff ℝ (n + 1) (ω.hamiltonianFlow H hX 1) :=
    ω.contDiff_hamiltonianFlow_apply H n hX (hH' n) 1
  refine ⟨ω.hamiltonianFlow H hX 1, contDiff_infty.2 fun n ↦ (hψs n).of_le (by norm_cast; omega),
    ⟨tsupport H, hHc, hHW, fun w hw ↦
      (ω.hamiltonianFlow_eventuallyEq_id_of_notMem_tsupport H hX hw 1).eq_of_nhds⟩,
    ⟨(hψs 0).differentiable (by simp), hdisp, hderiv⟩,
    ω.apply_fderiv_hamiltonianFlow H hX (by simpa using hH' 0) 1, hnd⟩

/-- The invariant of the induction over the balls `closedBall x (r x)`, `x ∈ t`, after the balls of
`s ⊆ t` have been treated by the perturbation `Ψ`: `Ψ` is a smooth symplectic map, equal to the
identity outside a compact subset of `W` and `c * #s`-close to the identity in `C¹`, and the map
`φ ∘ Ψ` has orbits leaving each ball `closedBall x (2 * r x)` until time `k`, no point of period `k`
in `K'`, and only nondegenerate points of period `k` in the balls of `s`. -/
private def IsPartialPerturbation (ω : SymplecticForm V) (φ : V → V) (k : ℕ) (W : Set V)
    (t : Finset V) (r : V → ℝ) (K' : Set V) (c : ℝ) (s : Finset V) (Ψ : V → V) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ (∃ S, IsCompact S ∧ S ⊆ W ∧ ∀ w ∉ S, Ψ w = w) ∧
    IsNearId (c * s.card) Ψ ∧ (∀ w u v, ω (fderiv ℝ Ψ w u) (fderiv ℝ Ψ w v) = ω u v) ∧
    (∀ x ∈ t, ∀ y ∈ closedBall x (2 * r x), ∀ j, 0 < j → j < k →
      (φ ∘ Ψ)^[j] y ∉ closedBall x (2 * r x)) ∧
    (∀ y ∈ K', ¬IsFixedPt (φ ∘ Ψ)^[k] y) ∧
    ∀ x ∈ s, ∀ y ∈ closedBall x (r x), IsFixedPt (φ ∘ Ψ)^[k] y →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (φ ∘ Ψ)^[k] y

/-- The inductive step: one more ball `closedBall a (r a)` is treated by composing `Ψ` with a
localized Hamiltonian translation, chosen so close to the identity in `C¹` that the conditions
already obtained persist. -/
private theorem IsPartialPerturbation.exists_insert {ω : SymplecticForm V} {φ : V → V}
    (hφ : ContDiff ℝ 1 φ) {k : ℕ} (hk : 0 < k) {W : Set V} {t : Finset V} {r : V → ℝ}
    (hr : ∀ x ∈ t, 0 < r x) (hrW : ∀ x ∈ t, closedBall x (2 * r x) ⊆ W) {K' : Set V}
    (hK' : IsCompact K') {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hcε : c * t.card ≤ ε) [DecidableEq V]
    {s : Finset V} {a : V} (ha : a ∈ t) (hs : s ⊆ t) (has : a ∉ s) {Ψ : V → V}
    (hΨ : IsPartialPerturbation ω φ k W t r K' c s Ψ) :
    ∃ Ψ', IsPartialPerturbation ω φ k W t r K' c (insert a s) Ψ' := by
  obtain ⟨hΨs, ⟨S, hSc, hSW, hSΨ⟩, hΨn, hΨω, hret, hK'fix, hnd⟩ := hΨ
  have hg : ContDiff ℝ 1 (φ ∘ Ψ) := hφ.comp (hΨs.of_le (by exact_mod_cast le_top))
  have hL : IsCompact (⋃ x ∈ s, closedBall x (r x)) :=
    s.finite_toSet.isCompact_biUnion fun x _ ↦ isCompact_closedBall x _
  -- Each condition to keep holds for all small enough `η`, and so do all of them together.
  have E₁ := (Finset.eventually_all t).2 fun x hx ↦ (Finset.eventually_all (Finset.Ioo 0 k)).2
    fun j hj ↦ eventually_forall_isNearId_iterate_comp_notMem hg (isCompact_closedBall x _) j
      (isClosed_univ.prod isClosed_closedBall) fun y hy h ↦
        hret x hx y hy j (Finset.mem_Ioo.1 hj).1 (Finset.mem_Ioo.1 hj).2 h.2
  have E₂ := eventually_forall_isNearId_iterate_comp_notMem hg hK' k isClosed_diagonal
    fun y hy h ↦ hK'fix y hy (mem_diagonal_iff.1 h).symm
  have E₃ := eventually_forall_isNearId_isNondegenerateFixedPt_iterate_comp hg hL k fun y hy ↦ by
    obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 hy
    exact hnd x hx y hy
  have hcε' : 0 < c / (1 + ε) := by positivity
  obtain ⟨η, ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, hη⟩ :=
    ((((E₁.and E₂).and E₃).and (Ioo_mem_nhdsGT hcε')).and self_mem_nhdsWithin).exists
  obtain ⟨ψ, hψs, ⟨Sψ, hSψc, hSψW, hSψ⟩, hψn, hψω, hψnd⟩ :=
    exists_isNearId_isNondegenerateFixedPt_iterate_comp_closedBall ω hg hk (hr a ha)
      (fun y hy j hj hjk ↦ hret a ha y hy j hj hjk) hη
  -- The bound `c * #s + η + c * #s * η ≤ c * (#s + 1)` for the composition.
  have hcs : c * s.card ≤ ε :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hs) hc.le).trans hcε
  have hηc : η * (1 + ε) < c := (lt_div_iff₀ (by positivity)).1 h₄.2
  refine ⟨Ψ ∘ ψ, hΨs.comp hψs, ⟨Sψ ∪ S, hSψc.union hSc,
    union_subset (hSψW.trans (ball_subset_closedBall.trans (hrW a ha))) hSW, fun w hw ↦ ?_⟩,
    (hΨn.comp hψn).mono ?_, fun w u v ↦ ?_, fun x hx y hy j hj hjk h ↦
      h₁ x hx j (Finset.mem_Ioo.2 ⟨hj, hjk⟩) ψ hψn y hy ⟨mem_univ _, h⟩,
    fun y hy h ↦ h₂ ψ hψn y hy (mem_diagonal_iff.2 h.symm), fun x hx y hy hfix ↦ ?_⟩
  · rw [mem_union, not_or] at hw
    simp [hSψ w hw.1, hSΨ w hw.2]
  · rw [Finset.card_insert_of_notMem has, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_right hcs hη.le]
  · rw [fderiv_comp w (hΨs.differentiable (by simp) _) (hψn.1 w)]
    simp [hΨω, hψω]
  · rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hψnd y hy hfix
    · exact h₃ ψ hψn y (mem_iUnion₂.2 ⟨x, hx, hy⟩) hfix

/-- **A `C¹`-small symplectic perturbation makes the points of least period `k` in a compact set
nondegenerate.** Let `φ` be a `C¹` self-map of a finite-dimensional symplectic vector space `V`,
let `k > 0`, and let `K ⊆ W` be a compact subset of an open set every point of which of period `k`
has least period exactly `k`. For every `ε > 0` there is a smooth map `ψ` preserving `ω`, equal to
the identity outside a compact subset of `W`, moving no point by more than `ε` and with derivative
within `ε` of the identity everywhere, such that every point `x ∈ K` with `(φ ∘ ψ)^[k] x = x` is a
nondegenerate fixed point of `(φ ∘ ψ)^[k]`. Since `ψ` preserves `ω`, the perturbed map `φ ∘ ψ`
is symplectic whenever `φ` is. -/
theorem exists_isNondegenerateFixedPt_iterate_comp (ω : SymplecticForm V) {φ : V → V}
    (hφ : ContDiff ℝ 1 φ) {k : ℕ} (hk : 0 < k) {K W : Set V} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) (hmin : ∀ x ∈ K, IsPeriodicPt φ k x → minimalPeriod φ x = k) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ψ : V → V, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∃ S, IsCompact S ∧ S ⊆ W ∧ ∀ w ∉ S, ψ w = w) ∧
      (∀ w, ‖ψ w - w‖ ≤ ε) ∧ (∀ w, ‖fderiv ℝ ψ w - ContinuousLinearMap.id ℝ V‖ ≤ ε) ∧
      (∀ w u v, ω (fderiv ℝ ψ w u) (fderiv ℝ ψ w v) = ω u v) ∧
      ∀ x ∈ K, IsFixedPt (φ ∘ ψ)^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, V) (φ ∘ ψ)^[k] x := by
  classical
  -- Balls around the points of period `k` in `K`, left by the orbits starting in them.
  set P := K ∩ {x | IsFixedPt φ^[k] x}
  have hP : IsCompact P := hK.inter_right (isClosed_eq (hφ.continuous.iterate k) continuous_id)
  have hball (x : V) (hx : x ∈ P) : ∃ r > 0, closedBall x (2 * r) ⊆ W ∧
      ∀ y ∈ closedBall x (2 * r), ∀ j, 0 < j → j < k → φ^[j] y ∉ closedBall x (2 * r) :=
    exists_pos_closedBall_subset_and_iterate_notMem hφ.continuous hW (hKW hx.1)
      fun j hj hjk h ↦ by
        have := (hmin x hx.1 hx.2).symm ▸ IsPeriodicPt.minimalPeriod_le hj h
        omega
  choose! r hr hrW hret using hball
  -- Finitely many of the balls `ball x (r x)` cover `P`; outside them `K` has no point of
  -- period `k`.
  obtain ⟨t, htP, hPt⟩ := hP.elim_nhds_subcover (fun x ↦ ball x (r x))
    fun x hx ↦ ball_mem_nhds x (hr x hx)
  set K' := K \ ⋃ x ∈ t, ball x (r x)
  have hK' : IsCompact K' := hK.diff (isOpen_biUnion fun x _ ↦ isOpen_ball)
  -- The balls are treated one after the other, each with a budget `c` in `C¹`.
  set c := ε / (t.card + 1)
  have hc : 0 < c := by positivity
  have hcε : c * t.card ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨Ψ, hΨs, hS, hΨn, hΨω, -, hK'fix, hnd⟩ : ∃ Ψ, IsPartialPerturbation ω φ k W t r K' c t Ψ :=
    Finset.induction_on' (motive := fun s ↦ ∃ Ψ, IsPartialPerturbation ω φ k W t r K' c s Ψ) t
      ⟨id, contDiff_id, ⟨∅, isCompact_empty, empty_subset _, fun _ _ ↦ rfl⟩,
        ⟨differentiable_id, by simp, by simp [fderiv_id]⟩, by simp [fderiv_id],
        fun x hx y hy j hj hjk ↦ hret x (htP x hx) y hy j hj hjk,
        fun y hy hfix ↦ hy.2 (hPt ⟨hy.1, hfix⟩), fun x hx ↦ absurd hx (Finset.notMem_empty x)⟩
      fun _ _ ha hs has ⟨Ψ, hΨ⟩ ↦ hΨ.exists_insert hφ hk (fun x hx ↦ hr x (htP x hx))
        (fun x hx ↦ hrW x (htP x hx)) hK' hc hε hcε ha hs has
  refine ⟨Ψ, hΨs, hS, fun w ↦ (hΨn.2.1 w).trans hcε, fun w ↦ (hΨn.2.2 w).trans hcε, hΨω,
    fun x hx hfix ↦ ?_⟩
  by_cases hxb : x ∈ ⋃ y ∈ t, ball y (r y)
  · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hxb
    exact hnd y hy x (ball_subset_closedBall hxy) hfix
  · exact absurd hfix (hK'fix x ⟨hx, hxb⟩)

end TauCeti.SymplecticForm
