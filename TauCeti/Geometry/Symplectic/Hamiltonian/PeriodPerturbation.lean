/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.TranslationPerturbation
import TauCeti.Analysis.Calculus.FDeriv.Perturbation
import TauCeti.Dynamics.PeriodicPts.LocalPerturbation
import TauCeti.Dynamics.PeriodicPts.Persistence

/-!
# Making all periodic points of one period nondegenerate

Let `(V, ω)` be a finite-dimensional symplectic vector space, for instance a chart of a surface
with its area form, let `φ` be a `C¹` self-map of `V`, `K` a compact set and `k > 0` a period. A
point `x` with `φ^[k] x = x` is *nondegenerate* when the linearized return map `d(φ^[k])_x` does
not have `1` as an eigenvalue (`TauCeti.IsNondegenerateFixedPt`). This file shows that an
arbitrarily `C¹`-small perturbation `φ ∘ ψ`, by a smooth compactly supported map `ψ` preserving
`ω`, makes every point of `K` of period `k` nondegenerate, provided that this already holds at the
points of `K` whose least period is smaller than `k`
(`TauCeti.SymplecticForm.exists_forall_isNondegenerateFixedPt_iterate_comp`). The support of `ψ`
lies in any prescribed open neighbourhood of `K`, and `φ ∘ ψ` is within `ε` of `φ` in value and
derivative at every point.

This is the step for one period of the induction over the periods `1, …, N` that makes all
periodic points of period at most a cutoff `N` of an area-preserving map nondegenerate. The
hypothesis at the points of smaller least period is what the earlier steps of that induction
provide once their orbits are made nondegenerate in all iterates, for instance by the localized
twists of `TauCeti.Geometry.Symplectic.Hamiltonian.ReturnMapPerturbation`. Since `φ ∘ ψ` is
`C¹`-close to `φ` everywhere, nondegeneracy reached at the earlier steps persists
(`IsCompact.exists_pos_forall_mem_Icc_isNondegenerateFixedPt_iterate`).

The proof is a finite version of Robinson's Baire argument.

* The points of smaller least period are nondegenerate fixed points of `φ^[k]`, hence isolated
  (`TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`). Finitely many small closed balls
  around them form a compact set `L` on which every point of period `k` is nondegenerate, and the
  remaining points of period `k` in `K` have least period exactly `k`.
* A point `x` of least period exactly `k` has a ball `ball x (2 * ρ)` that every orbit starting
  in it leaves until time `k`, with a margin: `‖φ^[j] y - x‖ ≥ 3 * ρ` for
  `y ∈ closedBall x (2 * ρ)` and `0 < j < k` (`Continuous.eventually_forall_mul_le_dist_iterate`).
  Finitely many balls `ball x ρ` cover the points of period `k` of `φ` in `K` away from `L`. The
  margin keeps the orbit condition for every map whose first `k - 1` iterates are within `ρ / 2`
  of those of `φ` on these balls, which holds for all maps `C¹`-close enough to `φ`
  (`IsCompact.exists_pos_forall_differentiableAt_iterate_and_norm_sub_le`). Away from the balls
  and `L`, the map `φ^[k]` moves every point of `K` by at least some `η > 0`, and so do the
  `k`-th iterates of all maps close enough to `φ`.
* The balls are treated one at a time. On the ball `ball x (2 * ρ)` a localized Hamiltonian
  translation makes the points of period `k` in `closedBall x ρ` nondegenerate
  (`TauCeti.SymplecticForm.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate`). It is chosen
  so small in `C¹` that the composition stays within the remaining budget of `φ`
  (`IsCompact.exists_pos_forall_norm_comp_sub_le`) and that the nondegeneracy reached on `L` and
  on the earlier balls persists (`IsCompact.exists_pos_forall_isNondegenerateFixedPt_iterate`).

## Main results

* `TauCeti.SymplecticForm.exists_forall_isNondegenerateFixedPt_iterate_comp`: a `C¹`-small
  compactly supported perturbation preserving `ω` makes the points of period `k` in a compact set
  nondegenerate, given nondegeneracy at those of smaller least period.

## References

* R. C. Robinson, *Generic properties of conservative systems*, Amer. J. Math. 92 (1970),
  562–603, for the genericity of nondegenerate periodic points of conservative maps by local
  perturbations, one period at a time.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893, for the role of nondegenerate periodic orbits.
-/

public section

noncomputable section

namespace TauCeti.SymplecticForm

open Filter Function Metric Set Topology
open scoped Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- The perturbations built in this file: smooth maps preserving `ω` that are the identity outside
a compact subset of `U`. -/
private def IsPerturbation (U : Set V) (ψ : V → V) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ x u v, ω (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = ω u v) ∧
    ∃ S, IsCompact S ∧ S ⊆ U ∧ ∀ w ∉ S, ψ w = w

/-- Every point of `A` of period `k` for `g` is a nondegenerate fixed point of `g^[k]`. -/
private def NondegenerateOn (g : V → V) (k : ℕ) (A : Set V) : Prop :=
  ∀ x ∈ A, IsFixedPt g^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, V) g^[k] x

omit [FiniteDimensional ℝ V] in
private theorem isPerturbation_id (U : Set V) : IsPerturbation ω U id :=
  ⟨contDiff_id, by simp [fderiv_id], ∅, isCompact_empty, empty_subset U, fun _ _ ↦ rfl⟩

omit [FiniteDimensional ℝ V] in
private theorem IsPerturbation.comp {U : Set V} {ψ₁ ψ₂ : V → V} (h₁ : IsPerturbation ω U ψ₁)
    (h₂ : IsPerturbation ω U ψ₂) : IsPerturbation ω U (ψ₁ ∘ ψ₂) := by
  obtain ⟨hs₁, hω₁, S₁, hS₁, hS₁U, hid₁⟩ := h₁
  obtain ⟨hs₂, hω₂, S₂, hS₂, hS₂U, hid₂⟩ := h₂
  refine ⟨hs₁.comp hs₂, fun x u v ↦ ?_, S₁ ∪ S₂, hS₁.union hS₂, union_subset hS₁U hS₂U,
    fun w hw ↦ ?_⟩
  · rw [fderiv_comp x (hs₁.differentiable (by simp) _) (hs₂.differentiable (by simp) x)]
    simp [hω₁, hω₂]
  · rw [mem_union, not_or] at hw
    simp [hid₂ w hw.2, hid₁ w hw.1]

/-- The time-one map of a smooth Hamiltonian that is the identity near every point outside an open
set `W ⊆ S`, with `S` a compact subset of `U`, is one of the perturbations of this file. -/
private theorem isPerturbation_hamiltonianFlow {H : V → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {L : NNReal} (hX : LipschitzWith L (ω.hamiltonianVectorField H)) {U S W : Set V}
    (hS : IsCompact S) (hSU : S ⊆ U) (hWS : W ⊆ S)
    (hid : ∀ w ∉ W, ω.hamiltonianFlow H hX 1 =ᶠ[𝓝 w] id) :
    IsPerturbation ω U (ω.hamiltonianFlow H hX 1) :=
  ⟨contDiff_infty.2 fun n ↦ ((ω.contDiff_hamiltonianFlow_apply H n hX (hH.of_le (by simp))
      1).of_le (by simp)), ω.apply_fderiv_hamiltonianFlow H hX (hH.of_le (by simp)) 1, S, hS, hSU,
    fun w hw ↦ (hid w fun hwW ↦ hw (hWS hwW)).eq_of_nhds⟩

/-- **One ball at a time.** Let the points of period `k` of `φ` in a compact set `L` be
nondegenerate, and let `ball x (2 * ρ x)`, `x ∈ t`, be balls that every orbit of every map
`δ₀`-close to `φ` in `C¹` starting in them leaves until time `k`. For every `0 < τ ≤ δ₀` some
perturbation `ψ` makes `φ ∘ ψ` `τ`-close to `φ` in `C¹` and its points of period `k` in `L`
and in the balls `closedBall x (ρ x)` nondegenerate. -/
private theorem exists_isPerturbation_of_finset {φ : V → V} (hφ : ContDiff ℝ 1 φ) {k : ℕ}
    (hk : 0 < k) {U L : Set V} (hL : IsCompact L) (hLnd : NondegenerateOn φ k L) (t : Finset V)
    {ρ : V → ℝ} (hρ0 : ∀ x ∈ t, 0 < ρ x) (hρU : ∀ x ∈ t, closedBall x (2 * ρ x) ⊆ U) {δ₀ : ℝ}
    (hsep : ∀ g : V → V, Differentiable ℝ g → (∀ y, ‖g y - φ y‖ ≤ δ₀) →
      (∀ y, ‖fderiv ℝ g y - fderiv ℝ φ y‖ ≤ δ₀) →
      ∀ x ∈ t, ∀ y ∈ ball x (2 * ρ x), ∀ j, 0 < j → j < k → g^[j] y ∉ ball x (2 * ρ x))
    {τ : ℝ} (hτ : 0 < τ) (hτδ : τ ≤ δ₀) :
    ∃ ψ, IsPerturbation ω U ψ ∧ (∀ y, ‖φ (ψ y) - φ y‖ ≤ τ) ∧
      (∀ y, ‖fderiv ℝ (φ ∘ ψ) y - fderiv ℝ φ y‖ ≤ τ) ∧
      NondegenerateOn (φ ∘ ψ) k (L ∪ ⋃ x ∈ t, closedBall x (ρ x)) := by
  classical
  induction t using Finset.induction_on generalizing τ with
  | empty =>
    exact ⟨id, isPerturbation_id ω U, by simp [hτ.le], by simp [hτ.le], by simpa using hLnd⟩
  | insert a s _ ih =>
    have hA : IsCompact (L ∪ ⋃ x ∈ s, closedBall x (ρ x)) :=
      hL.union (s.isCompact_biUnion fun x _ ↦ isCompact_closedBall x _)
    obtain ⟨ψ₁, hψ₁, h₁₀, h₁₁, h₁nd⟩ := ih (fun x hx ↦ hρ0 x (by simp [hx]))
      (fun x hx ↦ hρU x (by simp [hx])) (fun g hg h₀ h₁ x hx ↦ hsep g hg h₀ h₁ x (by simp [hx]))
      (half_pos hτ) (by linarith)
    set g₁ := φ ∘ ψ₁
    have hg₁ : ContDiff ℝ 1 g₁ := hφ.comp (hψ₁.1.of_le (by simp))
    -- Small `C¹` perturbations of `g₁` keep the nondegeneracy on `L` and the earlier balls.
    obtain ⟨δ₁, hδ₁, hpers⟩ := hA.exists_pos_forall_isNondegenerateFixedPt_iterate
      (fun _ _ _ _ ↦ hg₁.contDiffAt) h₁nd univ_mem
    have ha0 := hρ0 a (Finset.mem_insert_self a s)
    obtain ⟨δ', hδ', hcomp⟩ := (isCompact_closedBall a (2 * ρ a)).exists_pos_forall_norm_comp_sub_le
      (fun _ _ ↦ hg₁.contDiffAt) (lt_min hδ₁ (half_pos hτ))
    -- A Hamiltonian translation on `ball a (2 * ρ a)` makes the points of period `k` in
    -- `closedBall a (ρ a)` nondegenerate.
    obtain ⟨H, hH, -, -, ⟨L', hX⟩, htr⟩ := ω.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate
      hk (isCompact_closedBall a (ρ a)) isOpen_ball (closedBall_subset_ball (by linarith))
      (fun _ _ _ _ ↦ hg₁.differentiable one_ne_zero _)
      (fun y hy ↦ hsep g₁ (hg₁.differentiable one_ne_zero) (fun y ↦ (h₁₀ y).trans (by linarith))
        (fun y ↦ (h₁₁ y).trans (by linarith)) a (Finset.mem_insert_self a s) y hy) hδ'
    obtain ⟨-, hid, hdisp, hderiv, hnd⟩ := htr hX
    set ψ₂ := ω.hamiltonianFlow H hX 1
    have hψ₂ : IsPerturbation ω U ψ₂ := ω.isPerturbation_hamiltonianFlow hH hX
      (isCompact_closedBall a _) (hρU a (Finset.mem_insert_self a s)) ball_subset_closedBall hid
    have hclose := hcomp ψ₂
      (fun w hw ↦ (hid w fun hw' ↦ hw (ball_subset_closedBall hw')).eq_of_nhds)
      (fun x _ ↦ hψ₂.1.differentiable (by simp) x) (fun x _ ↦ hdisp x) (fun x _ ↦ hderiv x)
    refine ⟨ψ₁ ∘ ψ₂, hψ₁.comp ω hψ₂, fun y ↦ ?_, fun y ↦ ?_, fun x hx hfix ↦ ?_⟩
    · exact (norm_sub_le_norm_sub_add_norm_sub _ (g₁ y) _).trans ((add_le_add (hclose y).1
        (h₁₀ y)).trans (by linarith [min_le_right δ₁ (τ / 2)]))
    · rw [← Function.comp_assoc]
      exact (norm_sub_le_norm_sub_add_norm_sub _ (fderiv ℝ g₁ y) _).trans ((add_le_add
        (hclose y).2 (h₁₁ y)).trans (by linarith [min_le_right δ₁ (τ / 2)]))
    · rw [← Function.comp_assoc] at hfix ⊢
      have hd : Differentiable ℝ (g₁ ∘ ψ₂) :=
        (hg₁.differentiable one_ne_zero).comp (hψ₂.1.differentiable (by simp))
      have hpers' := hpers (g₁ ∘ ψ₂) (fun y _ ↦ hd y)
        (fun y _ ↦ (hclose y).1.trans (min_le_left _ _))
        (fun y _ ↦ (hclose y).2.trans (min_le_left _ _))
      simp only [Finset.set_biUnion_insert, mem_union] at hx
      rcases hx with hx | hx | hx
      · exact hpers' x (Or.inl hx) hfix
      · exact hnd x hx hfix
      · exact hpers' x (Or.inr hx) hfix

/-- **Points of least period `k`.** Let the points of period `k` of `φ` in a compact set `L` be
nondegenerate, and let every point of period `k` of `φ` in a compact set `K ⊆ U` have least period
`k`. Some perturbation `ψ` makes `φ ∘ ψ` `ε`-close to `φ` in `C¹` and its points of period `k` in
`K ∪ L` nondegenerate. -/
private theorem exists_isPerturbation_of_forall_ne {φ : V → V} (hφ : ContDiff ℝ 1 φ) {k : ℕ}
    (hk : 0 < k) {K L U : Set V} (hK : IsCompact K) (hL : IsCompact L) (hU : IsOpen U)
    (hKU : K ⊆ U) (hLnd : NondegenerateOn φ k L)
    (hper : ∀ x ∈ K, IsFixedPt φ^[k] x → ∀ j, 0 < j → j < k → φ^[j] x ≠ x) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ψ, IsPerturbation ω U ψ ∧ (∀ y, ‖φ (ψ y) - φ y‖ ≤ ε) ∧
      (∀ y, ‖fderiv ℝ (φ ∘ ψ) y - fderiv ℝ φ y‖ ≤ ε) ∧ NondegenerateOn (φ ∘ ψ) k (K ∪ L) := by
  have hφk : Continuous φ^[k] := hφ.continuous.iterate k
  -- Balls around the points of period `k`, which orbits leave with a margin, cover them.
  have hP : IsCompact (K ∩ fixedPoints φ^[k]) := hK.inter_right (isClosed_fixedPoints hφk)
  have hρ : ∀ x ∈ K ∩ fixedPoints φ^[k], ∃ ρ > 0, closedBall x (2 * ρ) ⊆ U ∧
      ∀ j, 0 < j → j < k → ∀ y ∈ closedBall x (2 * ρ), 3 * ρ ≤ dist (φ^[j] y) x := fun x hx ↦ by
    obtain ⟨ρ, ⟨hρU, hρsep⟩, hρ⟩ := ((eventually_nhdsGT_zero_mul_left (two_pos : (0 : ℝ) < 2)
      (((eventually_closedBall_subset (hU.mem_nhds (hKU hx.1))).filter_mono nhdsWithin_le_nhds).and
        (hφ.continuous.eventually_forall_mul_le_dist_iterate (hper x hx.1 hx.2) (3 / 2)))).and
      self_mem_nhdsWithin).exists
    exact ⟨ρ, hρ, hρU, fun j hj hjk y hy ↦ by linarith [hρsep j hj hjk y hy]⟩
  choose! ρ hρ0 hρU hρsep using hρ
  obtain ⟨t, htP, hcover⟩ := hP.elim_nhds_subcover (fun x ↦ ball x (ρ x))
    fun x hx ↦ ball_mem_nhds x (hρ0 x hx)
  -- Away from the balls, `φ^[k]` moves the points of `K` by at least `η > 0`.
  set K₀ := K \ ⋃ x ∈ t, ball x (ρ x)
  have hK₀ : IsCompact K₀ := hK.diff (isOpen_biUnion fun _ _ ↦ isOpen_ball)
  obtain ⟨η, hη, hηK₀⟩ := hK₀.exists_forall_le' (f := fun y ↦ ‖φ^[k] y - y‖)
    ((hφk.sub continuous_id).norm.continuousOn) (a := 0)
    fun y hy ↦ norm_pos_iff.2 (sub_ne_zero.2 fun h ↦ hy.2 (hcover ⟨hy.1, h⟩))
  -- Maps close enough to `φ` in `C¹` have iterates close to those of `φ` on the balls and on `K₀`.
  obtain ⟨δ₀, ⟨hδ₀, hδ₀K₀⟩, hδ₀pos⟩ := ((((eventually_all_finset t).2 fun x hx ↦
    (eventually_all_finset (Finset.range k)).2 fun j _ ↦
      (isCompact_closedBall x (2 * ρ x)).eventually_forall_norm_iterate_sub_le hφ j
        (half_pos (hρ0 x (htP x hx)))).and
    (hK₀.eventually_forall_norm_iterate_sub_le hφ k (half_pos hη))).and self_mem_nhdsWithin).exists
  have hsep : ∀ g : V → V, Differentiable ℝ g → (∀ y, ‖g y - φ y‖ ≤ δ₀) →
      (∀ y, ‖fderiv ℝ g y - fderiv ℝ φ y‖ ≤ δ₀) →
      ∀ x ∈ t, ∀ y ∈ ball x (2 * ρ x), ∀ j, 0 < j → j < k → g^[j] y ∉ ball x (2 * ρ x) := by
    intro g hg h₀ h₁ x hx y hy j hj hjk hgy
    have h := hδ₀ x hx j (Finset.mem_range.2 hjk) g hg h₀ h₁ y (ball_subset_closedBall hy)
    linarith [hρ0 x (htP x hx), hρsep x (htP x hx) j hj hjk y (ball_subset_closedBall hy),
      mem_ball.1 hgy, dist_triangle (φ^[j] y) (g^[j] y) x, dist_eq_norm_sub' (φ^[j] y) (g^[j] y)]
  obtain ⟨ψ, hψ, hψ₀, hψ₁, hnd⟩ := exists_isPerturbation_of_finset ω hφ hk hL hLnd t
    (fun x hx ↦ hρ0 x (htP x hx)) (fun x hx ↦ hρU x (htP x hx)) hsep (lt_min hε hδ₀pos)
    (min_le_right _ _)
  refine ⟨ψ, hψ, fun y ↦ (hψ₀ y).trans (min_le_left _ _), fun y ↦ (hψ₁ y).trans (min_le_left _ _),
    fun x hx hfix ↦ ?_⟩
  rcases hx with hx | hx
  · by_cases hxt : x ∈ ⋃ z ∈ t, ball z (ρ z)
    · obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hxt
      exact hnd x (Or.inr (mem_iUnion₂.2 ⟨z, hz, ball_subset_closedBall hxz⟩)) hfix
    · -- On `K₀` the `k`-th iterate of `φ ∘ ψ` has no fixed points.
      have hg : Differentiable ℝ (φ ∘ ψ) :=
        (hφ.differentiable one_ne_zero).comp (hψ.1.differentiable (by simp))
      have h := hδ₀K₀ (φ ∘ ψ) hg (fun y ↦ (hψ₀ y).trans (min_le_right _ _))
        (fun y ↦ (hψ₁ y).trans (min_le_right _ _)) x ⟨hx, hxt⟩
      rw [hfix.eq, norm_sub_rev] at h
      linarith [hηK₀ x ⟨hx, hxt⟩]
  · exact hnd x (Or.inl hx) hfix

/-- **Making the periodic points of one period nondegenerate.** Let `φ` be a `C¹` self-map of a
finite-dimensional symplectic vector space `(V, ω)`, let `k > 0`, let `K` be a compact set and `U`
an open neighbourhood of `K`. Suppose that every point `x ∈ K` with `φ^[k] x = x` whose least
period is smaller than `k`, that is `φ^[j] x = x` for some `0 < j < k`, is a nondegenerate fixed
point of `φ^[k]`. For every `ε > 0` there is a smooth map `ψ` preserving `ω` and equal to the
identity outside a compact subset of `U` such that `φ ∘ ψ` is within `ε` of `φ` in value and
derivative at every point, and every point `x ∈ K` with `(φ ∘ ψ)^[k] x = x` is a nondegenerate fixed
point of `(φ ∘ ψ)^[k]`. -/
theorem exists_forall_isNondegenerateFixedPt_iterate_comp {φ : V → V} (hφ : ContDiff ℝ 1 φ)
    {k : ℕ} (hk : 0 < k) {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hlow : ∀ x ∈ K, IsFixedPt φ^[k] x → (∃ j, 0 < j ∧ j < k ∧ IsFixedPt φ^[j] x) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) φ^[k] x) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : V → V, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ x u v, ω (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = ω u v) ∧
      HasCompactSupport (fun w ↦ ψ w - w) ∧ tsupport (fun w ↦ ψ w - w) ⊆ U ∧
      (∀ y, ‖φ (ψ y) - φ y‖ ≤ ε) ∧ (∀ y, ‖fderiv ℝ (φ ∘ ψ) y - fderiv ℝ φ y‖ ≤ ε) ∧
      ∀ x ∈ K, IsFixedPt (φ ∘ ψ)^[k] x → IsNondegenerateFixedPt 𝓘(ℝ, V) (φ ∘ ψ)^[k] x := by
  -- The points `Z` of `K` of period `k` and smaller least period are isolated among the fixed
  -- points of `φ^[k]`.
  set Z := K ∩ fixedPoints φ^[k] ∩ ⋃ j ∈ Finset.Ioo 0 k, fixedPoints φ^[j]
  have hlowZ : ∀ z ∈ Z, IsNondegenerateFixedPt 𝓘(ℝ, V) φ^[k] z := by
    rintro z ⟨⟨hzK, hzfix⟩, hzlow⟩
    obtain ⟨j, hj, hjfix⟩ := mem_iUnion₂.1 hzlow
    exact hlow z hzK hzfix ⟨j, (Finset.mem_Ioo.1 hj).1, (Finset.mem_Ioo.1 hj).2, hjfix⟩
  have hZ : IsCompact Z :=
    (hK.inter_right (isClosed_fixedPoints (hφ.continuous.iterate k))).inter_right
    (isClosed_biUnion_finset fun j _ ↦ isClosed_fixedPoints (hφ.continuous.iterate j))
  have hr : ∀ z ∈ Z, ∃ r > 0, ∀ y ∈ closedBall z r, IsFixedPt φ^[k] y → y = z := by
    intro z hz
    obtain ⟨r, hr, hr'⟩ := Metric.mem_nhdsWithin_iff.1 (hlowZ z hz).eventually_not_isFixedPt
    exact ⟨r / 2, half_pos hr, fun y hy hyfix ↦ by_contra fun hyz ↦
      hr' ⟨mem_ball.2 ((mem_closedBall.1 hy).trans_lt (half_lt_self hr)), hyz⟩ hyfix⟩
  choose! r hr0 hrfix using hr
  obtain ⟨t, htZ, hcover⟩ := hZ.elim_nhds_subcover (fun z ↦ ball z (r z))
    fun z hz ↦ ball_mem_nhds z (hr0 z hz)
  -- Near `Z` the only points of period `k` are those of `Z`; away from it, the least period is `k`.
  have hLnd : NondegenerateOn φ k (K ∩ ⋃ z ∈ t, closedBall z (r z)) := by
    rintro x ⟨-, hx⟩ hfix
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hx
    rw [hrfix z (htZ z hz) x hxz hfix]
    exact hlowZ z (htZ z hz)
  obtain ⟨ψ, ⟨hψs, hψω, S, hS, hSU, hψS⟩, hψ₀, hψ₁, hnd⟩ := exists_isPerturbation_of_forall_ne ω hφ
    hk (hK.diff (isOpen_biUnion fun _ _ ↦ isOpen_ball))
    (hK.inter_right (isClosed_biUnion_finset fun _ _ ↦ isClosed_closedBall)) hU
    (sdiff_subset.trans hKU) hLnd (fun x hx hfix j hj hjk hjx ↦ hx.2 (hcover
      ⟨⟨hx.1, hfix⟩, mem_iUnion₂.2 ⟨j, Finset.mem_Ioo.2 ⟨hj, hjk⟩, hjx⟩⟩)) hε
  have hsupp : support (fun w ↦ ψ w - w) ⊆ S := fun w hw ↦
    by_contra fun hwS ↦ hw (by simp [hψS w hwS])
  refine ⟨ψ, hψs, hψω, HasCompactSupport.intro hS fun w hw ↦ by simp [hψS w hw],
    (closure_minimal hsupp hS.isClosed).trans hSU, hψ₀, hψ₁, fun x hx hfix ↦ ?_⟩
  by_cases hxt : x ∈ ⋃ z ∈ t, ball z (r z)
  · obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hxt
    exact hnd x (Or.inr ⟨hx, mem_iUnion₂.2 ⟨z, hz, ball_subset_closedBall hxz⟩⟩) hfix
  · exact hnd x (Or.inl ⟨hx, hxt⟩) hfix

end TauCeti.SymplecticForm
