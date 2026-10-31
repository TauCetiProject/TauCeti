/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.Dual.Basic
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual

/-!
# The Krein–Šmulian theorem

The **Krein–Šmulian theorem** says that a convex subset `C` of the dual of a Banach space `E` is
weak-star closed as soon as its intersection with every closed ball centred at zero is weak-star
closed. For a linear subspace it suffices that its intersection with the closed unit ball is
weak-star closed.

The heart of the theorem is a separation statement: if `C` is convex, has weak-star closed
bounded slices, and avoids the closed ball of radius `r > 0`, then a single point `x` of `E`
satisfies `1 ≤ re (f x)` for every `f ∈ C`, so that the weak-star continuous functional of
evaluation at `x` separates `C` from zero.

## Main results

* `IsCompact.exists_finset_forall_one_lt_re_apply`: finitely many points of norm at most `ρ⁻¹`
  push a weak-star compact set of functionals of norm greater than `ρ` above the real level one.
* `Convex.exists_forall_one_le_re_apply_of_tendsto`: if every functional in a convex set reaches
  real level one somewhere along a null family of points of a Banach space, a single point does
  it for all of them.
* `Convex.exists_forall_one_le_re_apply`: the separation statement above.
* `Convex.isClosed_iff_forall_isClosed_inter_closedBall`: the Krein–Šmulian theorem.
* `Submodule.isClosed_iff_isClosed_inter_closedBall_zero_one`: its form for subspaces.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, Theorem 2.7.11.
* J. B. Conway, *A Course in Functional Analysis*, Theorem V.12.1.
-/

public section

open Filter Metric RCLike Set Topology WeakDual
open scoped ZeroAtInfty

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace IsCompact

/-- A weak-star compact set of functionals of norm greater than `ρ > 0` is pushed above the real
level one by finitely many points of norm at most `ρ⁻¹`. -/
theorem exists_finset_forall_one_lt_re_apply {S : Set (WeakDual 𝕜 E)} (hS : IsCompact S)
    {ρ : ℝ} (hρ : 0 < ρ) (hSρ : ∀ f ∈ S, ρ < ‖toStrongDual f‖) :
    ∃ F : Finset E, (∀ x ∈ F, ‖x‖ ≤ ρ⁻¹) ∧ ∀ f ∈ S, ∃ x ∈ F, 1 < re (f x) := by
  -- A functional with real part at most one on `closedBall 0 ρ⁻¹` has norm at most `ρ`.
  obtain ⟨u, hu⟩ := hS.elim_finite_subfamily_closed
    (fun x : closedBall (0 : E) ρ⁻¹ ↦ {f : WeakDual 𝕜 E | re (f x) ≤ 1})
    (fun x ↦ isClosed_le (continuous_re.comp (eval_continuous _)) continuous_const) <| by
      refine Set.disjoint_left.2 fun f hf hf' ↦ (hSρ f hf).not_ge ?_
      have := StrongDual.re_apply_add_mul_norm_le (f := toStrongDual f) (x := 0)
        (inv_nonneg.2 hρ.le) fun y hy ↦ mem_iInter.1 hf' ⟨y, hy⟩
      rw [map_zero, map_zero, zero_add, inv_mul_le_iff₀ hρ, mul_one] at this
      exact this
  refine ⟨u.map (.subtype _), fun x hx ↦ ?_, fun f hf ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hx
    exact mem_closedBall_zero_iff.1 x.2
  · have := Set.disjoint_left.1 hu hf
    simp only [mem_iInter, mem_ofPred_eq, not_forall, not_le] at this
    obtain ⟨x, hxu, hx⟩ := this
    exact ⟨x, Finset.mem_map_of_mem _ hxu, hx⟩

end IsCompact

/-- For a set `C` of functionals with weak-star closed bounded slices, all of norm greater than
`r > 0`, there are finite sets `D n` of points of norm at most `(r * (n + 1))⁻¹` such that every
`f ∈ C` has real part greater than one at a point of some `D n`. -/
private theorem exists_seq_finset_forall_one_lt_re_apply {C : Set (WeakDual 𝕜 E)}
    (hCR : ∀ R, IsClosed (C ∩ toStrongDual ⁻¹' closedBall 0 R)) {r : ℝ} (hr : 0 < r)
    (hCr : ∀ f ∈ C, r < ‖toStrongDual f‖) :
    ∃ D : ℕ → Finset E, (∀ n, ∀ x ∈ D n, ‖x‖ ≤ (r * (n + 1))⁻¹) ∧
      ∀ f ∈ C, ∃ n, ∃ x ∈ D n, 1 < re (f x) := by
  classical
  -- `Good n A`: every `f ∈ C` of norm at most `r * (n + 1)` exceeds one at a point of `A`.
  let Good (n : ℕ) (A : Finset E) : Prop :=
    ∀ f ∈ C, ‖toStrongDual f‖ ≤ r * (n + 1) → ∃ x ∈ A, 1 < re (f x)
  -- One step: enlarge `A` by small points so that `Good` passes from `n` to `n + 1`.
  have step (n : ℕ) (A : Finset E) : ∃ F : Finset E,
      (∀ x ∈ F, ‖x‖ ≤ (r * (n + 1))⁻¹) ∧ (Good n A → Good (n + 1) (A ∪ F)) := by
    by_cases hA : Good n A
    swap
    · exact ⟨∅, by simp, fun h ↦ absurd h hA⟩
    -- The functionals in the next slice on which `A` does not yet exceed one.
    set S := C ∩ toStrongDual ⁻¹' closedBall 0 (r * (n + 1 + 1)) ∩
      ⋂ x ∈ A, {f : WeakDual 𝕜 E | re (f x) ≤ 1}
    have hS : IsCompact S :=
      (isCompact_closedBall (0 : StrongDual 𝕜 E) (r * (n + 1 + 1))).of_isClosed_subset
        ((hCR _).inter (isClosed_biInter fun x _ ↦
          isClosed_le (continuous_re.comp (eval_continuous x)) continuous_const))
        (inter_subset_left.trans inter_subset_right)
    obtain ⟨F, hF, hSF⟩ :=
      hS.exists_finset_forall_one_lt_re_apply (ρ := r * (n + 1)) (by positivity)
        fun f ⟨⟨hfC, _⟩, hfA⟩ ↦ by
          by_contra! hf
          obtain ⟨x, hx, hfx⟩ := hA f hfC hf
          exact (mem_iInter₂.1 hfA x hx).not_gt hfx
    refine ⟨F, hF, fun _ f hfC hf ↦ ?_⟩
    by_cases hfA : ∃ x ∈ A, 1 < re (f x)
    · obtain ⟨x, hx, hfx⟩ := hfA
      exact ⟨x, Finset.mem_union_left _ hx, hfx⟩
    · push Not at hfA
      push_cast at hf
      obtain ⟨x, hx, hfx⟩ :=
        hSF f ⟨⟨hfC, mem_closedBall_zero_iff.2 hf⟩, mem_iInter₂.2 hfA⟩
      exact ⟨x, Finset.mem_union_right _ hx, hfx⟩
  choose F hF hFgood using step
  -- Accumulate the finite sets recursively: `A (n + 1) = A n ∪ F n (A n)`.
  let A : ℕ → Finset E := fun n ↦ Nat.rec ∅ (fun n A ↦ A ∪ F n A) n
  have hgood (n : ℕ) : Good n (A n) := by
    induction n with
    | zero =>
      intro f hfC hf
      exact absurd (hCr f hfC) (by simpa using hf)
    | succ n ih => exact hFgood n _ ih
  have hA (n : ℕ) : ∀ x ∈ A n, ∃ m, x ∈ F m (A m) := by
    induction n with
    | zero => simp [A]
    | succ n ih =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact ih x hx
      · exact ⟨n, hx⟩
  refine ⟨fun n ↦ F n (A n), fun n ↦ hF n _, fun f hfC ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (‖toStrongDual f‖ / r)
  obtain ⟨x, hx, hfx⟩ := hgood n f hfC <| by
    rw [div_le_iff₀ hr] at hn
    nlinarith
  obtain ⟨m, hm⟩ := hA n x hx
  exact ⟨m, x, hm, hfx⟩

/-- Translating a set of functionals with weak-star closed bounded slices by `f₀` gives a set
which again has weak-star closed bounded slices. -/
private theorem isClosed_inter_closedBall_preimage_add {C : Set (WeakDual 𝕜 E)}
    (hCR : ∀ R, IsClosed (C ∩ toStrongDual ⁻¹' closedBall 0 R)) (f₀ : WeakDual 𝕜 E) (R : ℝ) :
    IsClosed ((f₀ + ·) ⁻¹' C ∩ toStrongDual ⁻¹' closedBall 0 R) := by
  have : (f₀ + ·) ⁻¹' C ∩ toStrongDual ⁻¹' closedBall 0 R = (f₀ + ·) ⁻¹'
      (C ∩ toStrongDual ⁻¹' closedBall 0 (R + ‖toStrongDual f₀‖) ∩
        toStrongDual ⁻¹' closedBall (toStrongDual f₀) R) := by
    ext g
    simp only [mem_inter_iff, mem_preimage, mem_closedBall, dist_zero_right, map_add,
      dist_self_add_left]
    refine ⟨fun ⟨hg, hgR⟩ ↦ ⟨⟨hg, ?_⟩, hgR⟩, fun ⟨⟨hg, _⟩, hgR⟩ ↦ ⟨hg, hgR⟩⟩
    exact (norm_add_le _ _).trans (by linarith)
  rw [this]
  exact ((hCR _).inter (isClosed_closedBall _ R)).preimage (continuous_const_add f₀)

/-- If the intersection of a set `C` of functionals with the closed unit ball is weak-star closed
and `C` does not contain zero, then the norms of the elements of `C` are bounded below by some
`ε > 0`. -/
private theorem exists_pos_forall_lt_norm_of_isClosed_inter_closedBall {C : Set (WeakDual 𝕜 E)}
    (hC : IsClosed (C ∩ toStrongDual ⁻¹' closedBall 0 1)) (h0 : (0 : WeakDual 𝕜 E) ∉ C) :
    ∃ ε > 0, ∀ g ∈ C, ε < ‖toStrongDual g‖ := by
  have hopen := hC.isOpen_compl.preimage NormedSpace.Dual.toWeakDual_continuous
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hopen 0 fun h ↦ h0 <| by
    simpa only [mem_preimage, map_zero] using h.1
  refine ⟨min (δ / 2) 1, by positivity, fun g hg ↦ ?_⟩
  by_contra! hgδ
  have hgball : toStrongDual g ∈ ball 0 δ := mem_ball_zero_iff.2 (hgδ.trans_lt
    ((min_le_left _ _).trans_lt (half_lt_self hδ)))
  have := hδsub hgball
  rw [mem_preimage, toWeakDual_toStrongDual] at this
  exact this ⟨hg, mem_closedBall_zero_iff.2 (hgδ.trans (min_le_right _ _))⟩

namespace Convex

/-- If every functional in a convex set `C` has real part at least one somewhere along a null
family `v` of points of a Banach space, then evaluation at a single point `x` satisfies
`1 ≤ re (f x)` for all `f ∈ C`. -/
theorem exists_forall_one_le_re_apply_of_tendsto [CompleteSpace E] {C : Set (WeakDual 𝕜 E)}
    (hC : Convex ℝ C) {ι : Type*} {v : ι → E} (hv : Tendsto v cofinite (𝓝 0))
    (hCv : ∀ f ∈ C, ∃ i, 1 ≤ re (f (v i))) :
    ∃ x : E, ∀ f ∈ C, 1 ≤ re (f x) := by
  classical
  -- View `ι` as a discrete space, so that null families on `ι` form the space `c₀`.
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  -- `T f` is the family of the real parts of `f` along `v`, in `c₀`.
  let T (f : WeakDual 𝕜 E) : C₀(ι, ℝ) :=
    ZeroAtInftyContinuousMap.mkOfDiscrete (fun i ↦ re (f (v i))) <| by
      have := (continuous_re.comp (toStrongDual f).continuous).tendsto' 0 0 (by simp) |>.comp hv
      simpa [Function.comp_def] using this
  have hT (f : WeakDual 𝕜 E) (i) : T f i = re (f (v i)) :=
    congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _) i
  -- `T` is real linear, so it maps `C` to a convex set.
  have hTC : Convex ℝ (T '' C) := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩ a b ha hb hab
    refine ⟨a • f + b • g, hC hf hg ha hb hab, ZeroAtInftyContinuousMap.ext fun i ↦ ?_⟩
    simp only [hT, ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
      smul_eq_mul]
    -- Mathlib has no apply lemma for sums in `WeakDual 𝕜 E`, so evaluate through `toStrongDual`;
    -- `simp` then splits the sum and applies `WeakDual.real_smul_apply`.
    rw [← toStrongDual_apply]
    simp
  -- `T` maps `C` into the complement of the open unit ball of `c₀`.
  have hdisj : Disjoint (ball (0 : C₀(ι, ℝ)) 1) (T '' C) := by
    refine Set.disjoint_right.2 ?_
    rintro _ ⟨f, hfC, rfl⟩ hf
    obtain ⟨i, hfi⟩ := hCv f hfC
    have := (T f).norm_coe_le_norm i
    rw [hT, Real.norm_eq_abs] at this
    exact (mem_ball_zero_iff.1 hf).not_ge (hfi.trans ((le_abs_self _).trans this))
  obtain ⟨Λ, u, hΛ, hΛC⟩ :=
    _root_.geometric_hahn_banach_open (convex_ball 0 1) isOpen_ball hTC hdisj
  have hu : 0 < u := by simpa using hΛ 0 (mem_ball_self one_pos)
  -- The coefficients of `Λ` are absolutely summable and `v` is bounded, so they define a point
  -- `∑' i, a i • v i` of `E`.
  set a := fun i ↦ Λ (ZeroAtInftyContinuousMap.single i 1)
  have hvM : Tendsto (‖v ·‖) cofinite (𝓝 0) := by simpa using hv.norm
  obtain ⟨M, hM⟩ := hvM.bddAbove_range_of_cofinite
  have hsum : Summable fun i ↦ (a i : 𝕜) • v i :=
    .of_norm_bounded ((ZeroAtInftyContinuousMap.summable_norm_apply_single_one Λ).mul_right M)
      fun i ↦ by
        rw [norm_smul, norm_ofReal, ← Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM ⟨i, rfl⟩) (norm_nonneg _)
  -- The real part of `f` at this point is the value of `Λ` at `T f`.
  have hΛT (f : WeakDual 𝕜 E) : re (f (∑' i, (a i : 𝕜) • v i)) = Λ (T f) := by
    have h₁ := (hsum.hasSum.mapL (toStrongDual f)).mapL reCLM
    have h₂ := ZeroAtInftyContinuousMap.hasSum_apply_single_one_mul Λ (T f)
    simp only [hT, reCLM_apply, map_smul, smul_eq_mul, re_ofReal_mul, toStrongDual_apply] at h₁ h₂
    exact h₁.unique h₂
  refine ⟨((u⁻¹ : ℝ) : 𝕜) • ∑' i, (a i : 𝕜) • v i, fun f hfC ↦ ?_⟩
  rw [map_smul, smul_eq_mul, re_ofReal_mul, hΛT, le_inv_mul_iff₀ hu, mul_one]
  exact hΛC _ ⟨f, hfC, rfl⟩

/-- **Separation lemma of the Krein–Šmulian theorem.** Let `C` be a convex set of functionals on
a Banach space whose intersection with every closed ball centred at zero is weak-star closed. If
every element of `C` has norm greater than some `r > 0`, then evaluation at a single point `x`
separates `C` from zero: `1 ≤ re (f x)` for every `f ∈ C`. -/
theorem exists_forall_one_le_re_apply [CompleteSpace E] {C : Set (WeakDual 𝕜 E)}
    (hC : Convex ℝ C) (hCR : ∀ R, IsClosed (C ∩ toStrongDual ⁻¹' closedBall 0 R)) {r : ℝ}
    (hr : 0 < r) (hCr : ∀ f ∈ C, r < ‖toStrongDual f‖) :
    ∃ x : E, ∀ f ∈ C, 1 ≤ re (f x) := by
  obtain ⟨D, hD, hDC⟩ := exists_seq_finset_forall_one_lt_re_apply hCR hr hCr
  -- Enumerate the points of all the `D n` as a family over a discrete index type.
  let v (i : Σ n, Fin (D n).card) : E := (D i.1).equivFin.symm i.2
  have hvD (i : Σ n, Fin (D n).card) : v i ∈ D i.1 := ((D i.1).equivFin.symm i.2).2
  refine hC.exists_forall_one_le_re_apply_of_tendsto (v := v) ?_ fun f hfC ↦ ?_
  · -- Only the finitely many points of `D 0, …, D (N - 1)` can have norm at least `ε`.
    refine Metric.tendsto_nhds.2 fun ε hε ↦ eventually_cofinite.2 ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (r * ε)⁻¹
    refine ((finite_Iio N).preimage' (f := Sigma.fst) fun n _ ↦ ?_).subset fun i hi ↦ ?_
    · refine (finite_range (Sigma.mk n)).subset ?_
      rintro ⟨m, x⟩ (rfl : m = n)
      exact ⟨x, rfl⟩
    · by_contra hiN
      have hiN' : (N : ℝ) ≤ i.1 := by exact_mod_cast not_lt.1 hiN
      refine hi ?_
      rw [dist_zero_right]
      refine (hD i.1 _ (hvD i)).trans_lt ?_
      rw [inv_lt_comm₀ (by positivity) hε]
      calc ε⁻¹ = r * (r * ε)⁻¹ := by field_simp
        _ < r * (i.1 + 1) := by gcongr; linarith
  · obtain ⟨n, x, hx, hfx⟩ := hDC f hfC
    refine ⟨⟨n, (D n).equivFin ⟨x, hx⟩⟩, ?_⟩
    simpa [v] using hfx.le

/-- **Krein–Šmulian theorem.** A convex subset of the dual of a Banach space is weak-star closed if
and only if its intersection with every closed ball centred at zero is weak-star closed. -/
theorem isClosed_iff_forall_isClosed_inter_closedBall [CompleteSpace E] {C : Set (WeakDual 𝕜 E)}
    (hC : Convex ℝ C) :
    IsClosed C ↔ ∀ r, IsClosed (C ∩ toStrongDual ⁻¹' closedBall 0 r) := by
  refine ⟨fun h r ↦ h.inter (isClosed_closedBall 0 r), fun hCR ↦ ?_⟩
  refine isClosed_of_closure_subset fun f₀ hf₀ ↦ ?_
  by_contra hf₀C
  -- Translate `f₀` to zero: `C'` again has weak-star closed bounded slices.
  set C' := (f₀ + ·) ⁻¹' C
  have hC' : Convex ℝ C' := by
    intro g hg h hh a b ha hb hab
    rw [mem_preimage]
    convert hC hg hh ha hb hab using 1
    linear_combination (norm := module) -hab • f₀
  have hC'R := isClosed_inter_closedBall_preimage_add hCR f₀
  -- Since `C' ∩ closedBall 0 1` is weak-star closed and misses zero, `C'` misses a norm ball.
  obtain ⟨ε, hε, hεC'⟩ := exists_pos_forall_lt_norm_of_isClosed_inter_closedBall (hC'R 1)
    fun h ↦ hf₀C <| by simpa only [C', mem_preimage, add_zero] using h
  obtain ⟨x, hx⟩ := hC'.exists_forall_one_le_re_apply hC'R hε hεC'
  -- The weak-star open set `{f | re (f x) < re (f₀ x) + 1}` contains `f₀` and misses `C`.
  obtain ⟨f, hfU, hfC⟩ := mem_closure_iff.1 hf₀ {f | re (f x) < re (f₀ x) + 1}
    (isOpen_lt (continuous_re.comp (eval_continuous x)) continuous_const)
    (mem_ofPred.2 (lt_add_one _))
  rw [mem_ofPred_eq] at hfU
  have : 1 ≤ re (f x) - re (f₀ x) := by
    simpa [← toStrongDual_apply] using hx (f - f₀) (mem_preimage.2 (by rwa [add_sub_cancel]))
  linarith

end Convex

namespace Submodule

/-- **Krein–Šmulian theorem for subspaces.** A subspace of the dual of a Banach space is weak-star
closed if and only if its intersection with the closed unit ball is weak-star closed. -/
theorem isClosed_iff_isClosed_inter_closedBall_zero_one [CompleteSpace E]
    (G : Submodule 𝕜 (WeakDual 𝕜 E)) :
    IsClosed (G : Set (WeakDual 𝕜 E)) ↔
      IsClosed ((G : Set (WeakDual 𝕜 E)) ∩ toStrongDual ⁻¹' closedBall 0 1) := by
  refine ⟨fun h ↦ h.inter (isClosed_closedBall 0 1), fun h ↦ ?_⟩
  have hG : Convex ℝ (G : Set (WeakDual 𝕜 E)) := fun f hf g hg a b _ _ _ ↦ by
    rw [WeakDual.real_smul_eq_coe_smul, WeakDual.real_smul_eq_coe_smul]
    exact G.add_mem (G.smul_mem _ hf) (G.smul_mem _ hg)
  refine hG.isClosed_iff_forall_isClosed_inter_closedBall.2 fun r ↦ ?_
  rcases le_or_gt r 1 with hr | hr
  · -- Small radii: the slice is cut out of the unit slice by a weak-star closed ball.
    convert h.inter (isClosed_closedBall 0 r) using 1
    rw [inter_assoc, ← preimage_inter,
      inter_eq_right.2 (closedBall_subset_closedBall hr)]
  · -- Large radii: the slice is the preimage of the unit slice under scaling by `r⁻¹`.
    have hr₀ : (r : 𝕜) ≠ 0 := ofReal_ne_zero.2 (by positivity)
    convert h.preimage (continuous_const_smul ((r : 𝕜)⁻¹)) using 1
    ext f
    simp only [mem_inter_iff, SetLike.mem_coe, mem_preimage,
      mem_closedBall_zero_iff, map_smul, norm_smul, G.smul_mem_iff (inv_ne_zero hr₀), norm_inv,
      norm_ofReal, abs_of_pos (zero_lt_one.trans hr), inv_mul_le_iff₀ (zero_lt_one.trans hr),
      mul_one]

end Submodule
