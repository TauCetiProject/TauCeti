/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.ReturnMapPerturbation
public import TauCeti.Geometry.Symplectic.Hamiltonian.TranslationPerturbation
import TauCeti.Analysis.Calculus.FDeriv.Perturbation
import TauCeti.Dynamics.PeriodicPts.Finite
import TauCeti.Dynamics.PeriodicPts.LocalPerturbation
import TauCeti.Dynamics.PeriodicPts.Persistence
import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Making periodic points nondegenerate: one period, and all periods up to a cutoff

Let `(V, ω)` be a finite-dimensional symplectic vector space, for instance a chart of a surface
with its area form, let `φ` be a `C¹` self-map of `V`, `K` a compact set and `k > 0` a period. A
point `x` with `φ^[k] x = x` is *nondegenerate* when the linearized return map `d(φ^[k])_x` does
not have `1` as an eigenvalue (`TauCeti.IsNondegenerateFixedPt`). This file shows that, provided
every point of `K` of period `k` whose least period is smaller than `k` is already nondegenerate,
for every `ε > 0` there is a smooth compactly supported map `ψ` preserving `ω`, with `φ ∘ ψ` within
`ε` of `φ` in value and derivative at every point, such that every point of `K` of period `k` for
`φ ∘ ψ` is nondegenerate
(`TauCeti.SymplecticForm.exists_forall_isNondegenerateFixedPt_iterate_comp`). The support of `ψ`
lies in any prescribed open neighbourhood of `K`.

This is the step for one period of the induction over the periods `1, …, N` carried out on the
plane in the section *All periods up to a cutoff* below. The hypothesis at the points of smaller
least period is what the earlier stages of that induction provide once their orbits are made
nondegenerate in all iterates, by the localized twists of
`TauCeti.Geometry.Symplectic.Hamiltonian.ReturnMapPerturbation`. Since `φ ∘ ψ` is `C¹`-close to
`φ` everywhere, nondegeneracy reached at the earlier stages persists
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

**All periods up to a cutoff.** On the plane `ℂ` with its area form, the induction is carried out
(`TauCeti.exists_forall_mem_Icc_isNondegenerateFixedPt_iterate_comp`): for an area-preserving `C¹`
map `φ`, a compact set `K`, an open neighbourhood `U` of `K` and a cutoff `N`, for every `ε > 0`
there is a compactly supported area-preserving map `ψ`, supported in `U`, with `φ ∘ ψ` within `ε`
of `φ` in `C¹`, such that all points of period `1 ≤ k ≤ N` of `φ ∘ ψ` in `K` are nondegenerate. The
invariant after the stage `n` is that every point of `K` of period at most `n` is a nondegenerate
fixed point of every iterate `(φ ∘ ψ)^[k]`, `1 ≤ k ≤ N`, fixing it, so that the orbits of period
at most `n` are nondegenerate in all their covers up to period `N`. It is `C¹`-open
(`IsCompact.eventually_forall_isNondegenerateFixedPt_iterate_of_exists_isFixedPt`). The stage
`n + 1` has two parts.

* The one-period step makes the points of period `n + 1` in `K` nondegenerate, by a perturbation
  small enough to keep the invariant at `n`.
* The points of `K` of least period `n + 1` lie on finitely many orbits. A localized twist at one
  point of each orbit (`TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero_of_finite`)
  makes no nonzero power of its return map have the eigenvalue `1`, so the orbit is nondegenerate
  in all its covers, at every point of the orbit
  (`TauCeti.isNondegenerateFixedPt_iterate_apply_iterate_iff`). The twists fix the orbits of all the
  points of period `n + 1` in `K`, and, being small, create no new ones
  (`IsCompact.eventually_forall_fixedPoints_iterate_inter_eq`). The twists need the return maps to
  have determinant one, which holds for an area-preserving map of the plane
  (`TauCeti.BilinForm.IsIsometry.det_eq_one_of_isAlt`).

## Main results

* `TauCeti.SymplecticForm.exists_forall_isNondegenerateFixedPt_iterate_comp`: given nondegeneracy
  at the points of smaller least period, for every `ε > 0` some compactly supported perturbation
  preserving `ω`, `ε`-close in `C¹`, makes the points of period `k` in a compact set nondegenerate.
* `TauCeti.exists_forall_mem_Icc_isNondegenerateFixedPt_iterate_comp`: on the plane, for every
  `ε > 0` some compactly supported area-preserving perturbation of an area-preserving map,
  `ε`-close in `C¹`, makes all its points of period at most `N` in a compact set nondegenerate.

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
  refine ⟨hs₁.comp hs₂, ω.apply_fderiv_comp (hs₁.differentiable (by simp))
    (hs₂.differentiable (by simp)) hω₁ hω₂, S₁ ∪ S₂, hS₁.union hS₂, union_subset hS₁U hS₂U,
    fun w hw ↦ ?_⟩
  rw [mem_union, not_or] at hw
  simp [hid₂ w hw.2, hid₁ w hw.1]

omit [FiniteDimensional ℝ V] in
/-- The perturbations of this file in terms of the support of their displacement `ψ w - w`. -/
private theorem isPerturbation_iff {U : Set V} {ψ : V → V} :
    IsPerturbation ω U ψ ↔ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ x u v, ω (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) = ω u v) ∧
      HasCompactSupport (fun w ↦ ψ w - w) ∧ tsupport (fun w ↦ ψ w - w) ⊆ U := by
  refine and_congr_right' (and_congr_right' ⟨fun ⟨S, hS, hSU, hψS⟩ ↦ ?_, fun ⟨hc, hU⟩ ↦
    ⟨_, hc, hU, fun w hw ↦ sub_eq_zero.1 (image_eq_zero_of_notMem_tsupport (f := fun w ↦ ψ w - w)
      hw)⟩⟩)
  have hsupp : support (fun w ↦ ψ w - w) ⊆ S := fun w hw ↦
    by_contra fun hwS ↦ hw (by simp [hψS w hwS])
  exact ⟨HasCompactSupport.intro hS fun w hw ↦ by simp [hψS w hw],
    (closure_minimal hsupp hS.isClosed).trans hSU⟩

/-- The time-one map of a smooth Hamiltonian that is the identity outside a compact subset `S` of
`U` is one of the perturbations of this file. -/
private theorem isPerturbation_hamiltonianFlow {H : V → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {L : NNReal} (hX : LipschitzWith L (ω.hamiltonianVectorField H)) {U S : Set V}
    (hS : IsCompact S) (hSU : S ⊆ U) (hid : ∀ w ∉ S, ω.hamiltonianFlow H hX 1 w = w) :
    IsPerturbation ω U (ω.hamiltonianFlow H hX 1) :=
  ⟨contDiff_infty.2 fun n ↦ ((ω.contDiff_hamiltonianFlow_apply H n hX (hH.of_le (by simp))
      1).of_le (by simp)), ω.apply_fderiv_hamiltonianFlow H hX (hH.of_le (by simp)) 1, S, hS, hSU,
    hid⟩

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
      (isCompact_closedBall a _) (hρU a (Finset.mem_insert_self a s))
      fun w hw ↦ (hid w fun hw' ↦ hw (ball_subset_closedBall hw')).eq_of_nhds
    have hclose := hcomp ψ₂
      (fun w hw ↦ (hid w fun hw' ↦ hw (ball_subset_closedBall hw')).eq_of_nhds)
      (fun x _ ↦ hψ₂.1.differentiable (by simp) x) (fun x _ ↦ hdisp x) (fun x _ ↦ hderiv x)
    obtain ⟨h₂₀, h₂₁⟩ := norm_comp_comp_sub_le (c := τ) h₁₀ h₁₁ (fun y ↦ (hclose y).1)
      (fun y ↦ (hclose y).2) (by linarith [min_le_right δ₁ (τ / 2)])
    refine ⟨ψ₁ ∘ ψ₂, hψ₁.comp ω hψ₂, h₂₀, h₂₁, fun x hx hfix ↦ ?_⟩
    rw [← Function.comp_assoc] at hfix ⊢
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
  have hr : ∀ z ∈ Z, ∃ r > 0, ∀ y ∈ closedBall z r, IsFixedPt φ^[k] y → y = z :=
    fun z hz ↦ (hlowZ z hz).exists_pos_forall_mem_closedBall_isFixedPt_eq
  choose! r hr0 hrfix using hr
  obtain ⟨t, htZ, hcover⟩ := hZ.elim_nhds_subcover (fun z ↦ ball z (r z))
    fun z hz ↦ ball_mem_nhds z (hr0 z hz)
  -- Near `Z` the only points of period `k` are those of `Z`; away from it, the least period is `k`.
  have hLnd : NondegenerateOn φ k (K ∩ ⋃ z ∈ t, closedBall z (r z)) := by
    rintro x ⟨-, hx⟩ hfix
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hx
    rw [hrfix z (htZ z hz) x hxz hfix]
    exact hlowZ z (htZ z hz)
  obtain ⟨ψ, hψ, hψ₀, hψ₁, hnd⟩ := exists_isPerturbation_of_forall_ne ω hφ
    hk (hK.diff (isOpen_biUnion fun _ _ ↦ isOpen_ball))
    (hK.inter_right (isClosed_biUnion_finset fun _ _ ↦ isClosed_closedBall)) hU
    (sdiff_subset.trans hKU) hLnd (fun x hx hfix j hj hjk hjx ↦ hx.2 (hcover
      ⟨⟨hx.1, hfix⟩, mem_iUnion₂.2 ⟨j, Finset.mem_Ioo.2 ⟨hj, hjk⟩, hjx⟩⟩)) hε
  obtain ⟨hψs, hψω, hψc, hψU⟩ := (ω.isPerturbation_iff).1 hψ
  refine ⟨ψ, hψs, hψω, hψc, hψU, hψ₀, hψ₁, fun x hx hfix ↦ ?_⟩
  by_cases hxt : x ∈ ⋃ z ∈ t, ball z (r z)
  · obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hxt
    exact hnd x (Or.inr ⟨hx, mem_iUnion₂.2 ⟨z, hz, ball_subset_closedBall hxz⟩⟩) hfix
  · exact hnd x (Or.inl ⟨hx, hxt⟩) hfix


/-! ### All periods up to a cutoff -/

/-- Every point of `K` fixed by some `g^[j]`, `1 ≤ j ≤ n`, is a nondegenerate fixed point of every
`g^[k]`, `1 ≤ k ≤ N`, that fixes it. -/
private def NondegenerateUpTo (g : V → V) (K : Set V) (N n : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt g^[k] x → (∃ j ∈ Finset.Icc 1 n, IsFixedPt g^[j] x) →
    IsNondegenerateFixedPt 𝓘(ℝ, V) g^[k] x

end TauCeti.SymplecticForm

namespace TauCeti

open Filter Function Metric Set Topology SymplecticForm
open scoped Manifold

/-- Twisting finitely many periodic orbits of an area-preserving map of the plane. Let `p i` be
finitely many points of period `k` of `g` in the open set `U`, on pairwise distinct orbits of least
period `k`, all of whose orbit points lie in the finite set `O`. For every `τ > 0` some perturbation
`ψ` supported in `U` fixes every point of `O`, keeps `g ∘ ψ` within `τ` of `g` in `C¹`, and makes
each `p i` a nondegenerate fixed point of every iterate `(g ∘ ψ)^[k * m]`, `m ≠ 0`. -/
private theorem exists_isPerturbation_forall_isNondegenerateFixedPt {g : ℂ → ℂ}
    (hg : ContDiff ℝ 1 g)
    (hgω : ∀ x u v, stdComplexSymplecticForm (fderiv ℝ g x u) (fderiv ℝ g x v) =
      stdComplexSymplecticForm u v)
    {ι : Type*} [Finite ι] {p : ι → ℂ} {k : ℕ} (hk : 0 < k) (hp : ∀ i, IsFixedPt g^[k] (p i))
    {O : Set ℂ} (hO : O.Finite) (hpO : ∀ i j, g^[j] (p i) ∈ O)
    (horb : ∀ i i' j, j < k → (0 < j ∨ i' ≠ i) → g^[j] (p i') ≠ p i) {U : Set ℂ} (hU : IsOpen U)
    (hpU : ∀ i, p i ∈ U) {τ : ℝ} (hτ : 0 < τ) :
    ∃ ψ, IsPerturbation stdComplexSymplecticForm U ψ ∧ (∀ y, ‖g (ψ y) - g y‖ ≤ τ) ∧
      (∀ y, ‖fderiv ℝ (g ∘ ψ) y - fderiv ℝ g y‖ ≤ τ) ∧ (∀ w ∈ O, ψ w = w) ∧
      ∀ i, ∀ m ≠ 0, IsNondegenerateFixedPt 𝓘(ℝ, ℂ) (g ∘ ψ)^[k * m] (p i) := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- A radius `r` below which the discs about the `p i` lie in `U` and miss the rest of `O`.
  have hrad (i : ι) : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      closedBall (p i) ρ ⊆ U ∧ ∀ w ∈ O, w ≠ p i → ρ ≤ ‖w - p i‖ := by
    obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.1 (inter_mem (hU.mem_nhds (hpU i))
      ((hO.sdiff (t := {p i})).isClosed.isOpen_compl.mem_nhds fun h ↦ h.2 rfl))
    filter_upwards [Ioo_mem_nhdsGT hR] with ρ hρ
    refine ⟨(closedBall_subset_ball hρ.2).trans fun w hw ↦ (hRU hw).1, fun w hw hwp ↦ ?_⟩
    have hwR : w ∉ ball (p i) R := fun h ↦ (hRU h).2 ⟨hw, hwp⟩
    rw [mem_ball, not_lt, dist_eq_norm] at hwR
    exact hρ.2.le.trans hwR
  obtain ⟨r, hrad, hr⟩ := ((eventually_all.2 hrad).and self_mem_nhdsWithin).exists
  obtain ⟨η, hη, hcomp⟩ := (isCompact_iUnion fun i ↦ isCompact_closedBall (p i) r)
    |>.exists_pos_forall_norm_comp_sub_le (f := g) (fun x _ ↦ hg.contDiffAt) hτ
  -- The twists at the points `p i`.
  obtain ⟨H, hH, -, ⟨L, hX⟩, htw⟩ := exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero_of_finite
    (k := fun _ ↦ k) (A := fun i ↦ fderiv ℝ g^[k] (p i)) (fun _ ↦ hk) hp
    (fun i ↦ (hgd.iterate _ _).hasFDerivAt)
    (fun i ↦ BilinForm.IsIsometry.det_eq_one_of_isAlt stdComplexSymplecticForm.isAlt
      stdComplexSymplecticForm.nondegenerate
      (BilinForm.isIsometry_iff.2 (stdComplexSymplecticForm.apply_fderiv_iterate hgd hgω _ _)))
    (fun _ _ _ ↦ hg.continuous.continuousAt) hr
    (fun i i' j hj h ↦ (hrad i).2 _ (hpO i' j) (horb i i' j hj h)) hη
  obtain ⟨hψp, hid, hdisp, hderiv, hret⟩ := htw hX
  set ψ := stdComplexSymplecticForm.hamiltonianFlow H hX 1
  have hψC (w : ℂ) (hw : w ∉ ⋃ i, closedBall (p i) r) : ψ w = w := hid w fun i ↦ by
    have := not_le.1 fun h ↦ hw (mem_iUnion.2 ⟨i, mem_closedBall.2 h⟩)
    rw [dist_eq_norm] at this
    exact this.le
  have hψ : IsPerturbation stdComplexSymplecticForm U ψ :=
    stdComplexSymplecticForm.isPerturbation_hamiltonianFlow hH hX
      (isCompact_iUnion fun i ↦ isCompact_closedBall (p i) r) (iUnion_subset fun i ↦ (hrad i).1)
      hψC
  have hclose := hcomp ψ hψC (fun x _ ↦ hψ.1.differentiable (by simp) x) (fun x _ ↦ hdisp x)
    (fun x _ ↦ hderiv x)
  refine ⟨ψ, hψ, fun y ↦ (hclose y).1, fun y ↦ (hclose y).2, fun w hw ↦ ?_, fun i m hm ↦ ?_⟩
  · by_cases h : ∃ i, w = p i
    · obtain ⟨i, rfl⟩ := h
      exact hψp i
    · simp only [not_exists] at h
      exact hid w fun i ↦ (hrad i).2 w hw (h i)
  -- The return map `B` of `p i` has no nonzero power with the eigenvalue `1`.
  obtain ⟨hpfix, B, hB, hBdet⟩ := hret i
  rw [iterate_mul]
  refine ((hB.iterate hpfix m).isNondegenerateFixedPt_iff_injective_id_sub
    (IsFixedPt.iterate (f := (g ∘ ψ)^[k]) hpfix m)).2 ?_
  exact ((Module.End.isUnit_iff _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hBdet m hm)))).1

/-- If the periods at most `n` through `K` are nondegenerate in all covers up to period `N`, and
so are the orbits of least period `n + 1`, then the periods at most `n + 1` are. -/
private theorem nondegenerateUpTo_succ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : V → V} {K : Set V} {N n : ℕ}
    (hP : NondegenerateUpTo g K N n)
    (hcov : ∀ x ∈ K, IsFixedPt g^[n + 1] x → (∀ j ∈ Finset.Icc 1 n, ¬IsFixedPt g^[j] x) →
      ∀ m ≠ 0, IsNondegenerateFixedPt 𝓘(ℝ, V) g^[(n + 1) * m] x) :
    NondegenerateUpTo g K N (n + 1) := by
  rintro k hk x hxK hfix ⟨j, hj, hjx⟩
  by_cases hsmall : ∃ j ∈ Finset.Icc 1 n, IsFixedPt g^[j] x
  · exact hP k hk x hxK hfix hsmall
  simp only [not_exists, not_and] at hsmall
  obtain rfl : j = n + 1 := by
    rw [Finset.mem_Icc] at hj
    by_contra hne
    exact hsmall j (Finset.mem_Icc.2 ⟨hj.1, by omega⟩) hjx
  -- The least period of `x` is `n + 1`, so `k` is a multiple of it.
  have hmp : minimalPeriod g x = n + 1 := by
    have hpos : 0 < minimalPeriod g x := IsPeriodicPt.minimalPeriod_pos (n := n + 1) n.succ_pos hjx
    have hle : minimalPeriod g x ≤ n + 1 :=
      Nat.le_of_dvd n.succ_pos (IsPeriodicPt.minimalPeriod_dvd (n := n + 1) hjx)
    by_contra hne
    exact hsmall _ (Finset.mem_Icc.2 ⟨hpos, by omega⟩) (isPeriodicPt_minimalPeriod g x)
  obtain ⟨m, rfl⟩ : n + 1 ∣ k := hmp ▸ IsPeriodicPt.minimalPeriod_dvd (n := k) hfix
  exact hcov x hxK hjx hsmall m (by rintro rfl; simp at hk)

/-- The twisting step on the plane. Let `g` be area preserving, with the points of `K` of period
at most `n` nondegenerate in all covers up to period `N`, and all points of `K` of period `n + 1`
nondegenerate. Localized twists at one point of each orbit of least period `n + 1` through `K` make
these orbits nondegenerate in all their covers too, by an arbitrarily `C¹`-small perturbation. -/
private theorem exists_twist {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgω : ∀ x u v, stdComplexSymplecticForm (fderiv ℝ g x u) (fderiv ℝ g x v) =
      stdComplexSymplecticForm u v)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {N n : ℕ} (hnN : n + 1 ≤ N)
    (hP : NondegenerateUpTo g K N n)
    (hQ : ∀ x ∈ K, IsFixedPt g^[n + 1] x → IsNondegenerateFixedPt 𝓘(ℝ, ℂ) g^[n + 1] x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ, IsPerturbation stdComplexSymplecticForm U ψ ∧ (∀ y, ‖g (ψ y) - g y‖ ≤ ε) ∧
      (∀ y, ‖fderiv ℝ (g ∘ ψ) y - fderiv ℝ g y‖ ≤ ε) ∧ NondegenerateUpTo (g ∘ ψ) K N (n + 1) := by
  classical
  -- The points `F` of period `n + 1` in `K`, and the points `O` of their orbits, are finitely many.
  set F := fixedPoints g^[n + 1] ∩ K
  have hFfin : F.Finite := (hK.inter_left (isClosed_fixedPoints (hg.continuous.iterate _)))
    |>.finite_of_isNondegenerateFixedPt fun x hx ↦ hQ x hx.2 hx.1
  set O := ⋃ x ∈ F, (fun j ↦ g^[j] x) '' Iio (n + 1)
  have hmemO {x : ℂ} (hx : x ∈ F) (j : ℕ) : g^[j] x ∈ O := by
    rw [← IsPeriodicPt.iterate_mod_apply (n := n + 1) hx.1]
    exact mem_iUnion₂.2 ⟨x, hx, j % (n + 1), Nat.mod_lt _ n.succ_pos, rfl⟩
  -- The points `S` of `F` of least period `n + 1`, and a point `p i` on each of their orbits.
  set S := {x ∈ F | ∀ j, 0 < j → j < n + 1 → ¬IsFixedPt g^[j] x}
  obtain ⟨ι, _, p, hpS, hcover, hdistinct⟩ :=
    exists_orbit_representatives (S := S) (hFfin.subset (sep_subset _ _))
      fun x hx ↦ mk_mem_periodicPts n.succ_pos hx.1.1
  -- `δ`-small perturbations keep the earlier periods and create no new points of period `n + 1`.
  obtain ⟨δ, ⟨hδP, hδF⟩, hδ⟩ :=
    (((hK.eventually_forall_isNondegenerateFixedPt_iterate_of_exists_isFixedPt hg
      (by omega : n ≤ N) hP).and (hK.eventually_forall_fixedPoints_iterate_inter_eq hg (n + 1)
        hQ)).and self_mem_nhdsWithin).exists
  obtain ⟨ψ, hψ, h₀, h₁, hψO, hnd⟩ := exists_isPerturbation_forall_isNondegenerateFixedPt hg hgω
    n.succ_pos (fun i ↦ (hpS i).1.1) (hFfin.biUnion fun x _ ↦ (finite_Iio _).image _)
    (fun i ↦ hmemO (hpS i).1) (fun i i' j hj h heq ↦ by
      by_cases hii : i' = i
      · subst hii
        exact (hpS i').2 j (h.resolve_right (not_not_intro rfl)) hj heq
      · exact hii (hdistinct heq)) hU (fun i ↦ hKU (hpS i).1.2) (lt_min hδ hε)
  -- The perturbation fixes the orbits of the points of `F`, which remain periodic for `g ∘ ψ`.
  have hg₂F {x : ℂ} (hx : x ∈ F) (j : ℕ) : (g ∘ ψ)^[j] x = g^[j] x := by
    induction j with
    | zero => rfl
    | succ j ih => rw [iterate_succ_apply', iterate_succ_apply', ih, comp_apply, hψO _ (hmemO hx j)]
  have hg₂ : Differentiable ℝ (g ∘ ψ) :=
    (hg.differentiable one_ne_zero).comp (hψ.1.differentiable (by simp))
  have hF₂ : fixedPoints (g ∘ ψ)^[n + 1] ∩ K = F := hδF _ hg₂
    (fun y ↦ (h₀ y).trans (min_le_left _ _)) (fun y ↦ (h₁ y).trans (min_le_left _ _))
    fun x hx ↦ (hg₂F hx (n + 1)).trans hx.1
  refine ⟨ψ, hψ, fun y ↦ (h₀ y).trans (min_le_right _ _), fun y ↦ (h₁ y).trans (min_le_right _ _),
    nondegenerateUpTo_succ (hδP _ hg₂ (fun y ↦ (h₀ y).trans (min_le_left _ _))
      (fun y ↦ (h₁ y).trans (min_le_left _ _))) fun x hxK hfix hsmall m hm ↦ ?_⟩
  -- A point `x` of least period `n + 1` for `g ∘ ψ` lies on the orbit of some `p i`.
  have hxF : x ∈ F := hF₂ ▸ ⟨hfix, hxK⟩
  have hxS : x ∈ S := ⟨hxF, fun j hj hjn hjx ↦ hsmall j (Finset.mem_Icc.2 ⟨hj, by omega⟩)
    ((hg₂F hxF j).trans hjx)⟩
  obtain ⟨i, j, hjp⟩ := hcover x hxS
  rw [← hjp, ← hg₂F (hpS i).1 j]
  exact (isNondegenerateFixedPt_iterate_apply_iterate_iff
    (IsPeriodicPt.mul_const (m := n + 1) ((hg₂F (hpS i).1 (n + 1)).trans (hpS i).1.1) m)
    (fun _ ↦ (hg₂ _).mdifferentiableAt) j).2 (hnd i m hm)

/-- One step of the induction over the periods on the plane: from nondegeneracy of the periods at
most `n` in all covers up to period `N`, reach it for the periods at most `n + 1`, by an arbitrarily
`C¹`-small perturbation. First the points of period `n + 1` are made nondegenerate, then the orbits
of least period `n + 1` are twisted to make their covers nondegenerate. -/
private theorem exists_step {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgω : ∀ x u v, stdComplexSymplecticForm (fderiv ℝ g x u) (fderiv ℝ g x v) =
      stdComplexSymplecticForm u v)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {N n : ℕ} (hnN : n + 1 ≤ N)
    (hP : NondegenerateUpTo g K N n) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ, IsPerturbation stdComplexSymplecticForm U ψ ∧ (∀ y, ‖g (ψ y) - g y‖ ≤ ε) ∧
      (∀ y, ‖fderiv ℝ (g ∘ ψ) y - fderiv ℝ g y‖ ≤ ε) ∧ NondegenerateUpTo (g ∘ ψ) K N (n + 1) := by
  -- Perturbations `δ`-close to `g` keep the periods at most `n`.
  obtain ⟨δ, hδP, hδ⟩ := ((hK.eventually_forall_isNondegenerateFixedPt_iterate_of_exists_isFixedPt
    hg (by omega : n ≤ N) hP).and self_mem_nhdsWithin).exists
  obtain ⟨ψ₁, hψ₁s, hψ₁ω, hψ₁c, hψ₁U, h₁₀, h₁₁, hQ⟩ :=
    stdComplexSymplecticForm.exists_forall_isNondegenerateFixedPt_iterate_comp hg n.succ_pos hK hU
      hKU (fun x hxK hfix ⟨j, hj, hjk, hjx⟩ ↦ hP (n + 1) (Finset.mem_Icc.2 ⟨by omega, hnN⟩) x hxK
        hfix ⟨j, Finset.mem_Icc.2 ⟨hj, by omega⟩, hjx⟩) (lt_min hδ (half_pos hε))
  have hψ₁ : IsPerturbation stdComplexSymplecticForm U ψ₁ :=
    stdComplexSymplecticForm.isPerturbation_iff.2 ⟨hψ₁s, hψ₁ω, hψ₁c, hψ₁U⟩
  have hψ₁d : Differentiable ℝ ψ₁ := hψ₁s.differentiable (by simp)
  have hg₁ : ContDiff ℝ 1 (g ∘ ψ₁) := hg.comp (hψ₁s.of_le (by simp))
  obtain ⟨ψ₂, hψ₂, h₂₀, h₂₁, hP₂⟩ := exists_twist hg₁
    (stdComplexSymplecticForm.apply_fderiv_comp (hg.differentiable one_ne_zero) hψ₁d hgω hψ₁ω)
    hK hU hKU hnN (hδP _ (hg₁.differentiable one_ne_zero) (fun y ↦ (h₁₀ y).trans (min_le_left _ _))
      fun y ↦ (h₁₁ y).trans (min_le_left _ _)) hQ (half_pos hε)
  obtain ⟨h₀, h₁⟩ := norm_comp_comp_sub_le (fun y ↦ (h₁₀ y).trans (min_le_right _ _))
    (fun y ↦ (h₁₁ y).trans (min_le_right _ _)) h₂₀ h₂₁ (add_halves ε).le
  exact ⟨ψ₁ ∘ ψ₂, hψ₁.comp _ hψ₂, h₀, h₁, hP₂⟩

/-- The induction over the periods on the plane: for every `n ≤ N` an arbitrarily `C¹`-small
perturbation makes the periods at most `n` nondegenerate in all covers up to period `N`. -/
private theorem exists_nondegenerateUpTo {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hφω : ∀ x u v, stdComplexSymplecticForm (fderiv ℝ φ x u) (fderiv ℝ φ x v) =
      stdComplexSymplecticForm u v)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {N : ℕ} (n : ℕ) (hn : n ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ, IsPerturbation stdComplexSymplecticForm U ψ ∧ (∀ y, ‖φ (ψ y) - φ y‖ ≤ ε) ∧
      (∀ y, ‖fderiv ℝ (φ ∘ ψ) y - fderiv ℝ φ y‖ ≤ ε) ∧ NondegenerateUpTo (φ ∘ ψ) K N n := by
  induction n generalizing ε with
  | zero =>
    refine ⟨id, isPerturbation_id _ U, by simp [hε.le], by simp [hε.le], ?_⟩
    rintro k - x - - ⟨j, hj, -⟩
    simp at hj
  | succ n ih =>
    obtain ⟨ψ₀, hψ₀, h₀₀, h₀₁, hP₀⟩ := ih (by omega) (half_pos hε)
    have hψ₀d : Differentiable ℝ ψ₀ := hψ₀.1.differentiable (by simp)
    obtain ⟨ψ, hψ, h₀, h₁, hP⟩ := exists_step (hφ.comp (hψ₀.1.of_le (by simp)))
      (stdComplexSymplecticForm.apply_fderiv_comp (hφ.differentiable one_ne_zero) hψ₀d hφω
        hψ₀.2.1) hK hU hKU hn hP₀ (half_pos hε)
    obtain ⟨h₂₀, h₂₁⟩ := norm_comp_comp_sub_le h₀₀ h₀₁ h₀ h₁ (add_halves ε).le
    exact ⟨ψ₀ ∘ ψ, hψ₀.comp _ hψ, h₂₀, h₂₁, hP⟩

/-- **Making all periodic points up to a period cutoff nondegenerate.** Let `φ` be a `C¹` map of
the plane `ℂ` preserving the area form `ω`, let `K` be a compact set, `U` an open neighbourhood of
`K` and `N` a period cutoff. For every `ε > 0` there is a smooth map `ψ` preserving `ω` and equal
to the identity outside a compact subset of `U` such that `φ ∘ ψ` is within `ε` of `φ` in value
and derivative at every point, and for every `1 ≤ k ≤ N` every point `x ∈ K` with
`(φ ∘ ψ)^[k] x = x` is a nondegenerate fixed point of `(φ ∘ ψ)^[k]`. -/
theorem exists_forall_mem_Icc_isNondegenerateFixedPt_iterate_comp {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ)
    (hφω : ∀ x u v, stdComplexSymplecticForm (fderiv ℝ φ x u) (fderiv ℝ φ x v) =
      stdComplexSymplecticForm u v)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (N : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ψ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ x u v, stdComplexSymplecticForm (fderiv ℝ ψ x u) (fderiv ℝ ψ x v) =
        stdComplexSymplecticForm u v) ∧
      HasCompactSupport (fun w ↦ ψ w - w) ∧ tsupport (fun w ↦ ψ w - w) ⊆ U ∧
      (∀ y, ‖φ (ψ y) - φ y‖ ≤ ε) ∧ (∀ y, ‖fderiv ℝ (φ ∘ ψ) y - fderiv ℝ φ y‖ ≤ ε) ∧
      ∀ k ∈ Finset.Icc 1 N, ∀ x ∈ K, IsFixedPt (φ ∘ ψ)^[k] x →
        IsNondegenerateFixedPt 𝓘(ℝ, ℂ) (φ ∘ ψ)^[k] x := by
  obtain ⟨ψ, hψ, h₀, h₁, hnd⟩ := exists_nondegenerateUpTo hφ hφω hK hU hKU N le_rfl hε
  obtain ⟨hψs, hψω, hψc, hψU⟩ := stdComplexSymplecticForm.isPerturbation_iff.1 hψ
  exact ⟨ψ, hψs, hψω, hψc, hψU, h₀, h₁, fun k hk x hx hfix ↦ hnd k hk x hx hfix ⟨k, hk, hfix⟩⟩

end TauCeti
