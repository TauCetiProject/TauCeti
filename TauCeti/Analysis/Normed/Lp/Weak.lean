/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import TauCeti.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Weak `Lᵖ` norms of finite families

For a finite family `x : ι → E` over real or complex scalars, its weak `Lᵖ` norm is
the supremum of the `Lᵖ` norms of `(f (x i))ᵢ` over the closed unit ball of the continuous dual.
It is the operator norm of the dual-evaluation map into `PiLp`, so it is
finite without completeness or finite dimensionality assumptions on `E`.

`weakLpNorm` is bundled as a `Seminorm`, providing homogeneity and the triangle
inequality through the existing seminorm API. Over real or complex scalars it
dominates each coordinate norm, and is therefore a norm on finite families in a
normed space. We prove the strong `Lᵖ` bound, invariance under reindexing, the
bounded-operator estimate, the exact value on scalar multiples of one vector, its agreement
with the strong norm at exponent `∞`, and Hölder's inequality for scalar weights:
the weak `p`-norm of `(cᵢ xᵢ)ᵢ` is at most `‖c‖ₛ` times the weak `q`-norm of `x` when
`1 / p = 1 / s + 1 / q`.
These are the finite-family estimates used for absolutely summing operators.

At exponent `1` the weak norm controls unconditional summability. The finite subfamilies of an
unconditionally summable family have uniformly bounded weak `L¹` norms, by the uniform boundedness
principle on the complete dual. Conversely, in a complete space, finite blocks whose weak `L¹`
norms are summable assemble into an unconditionally summable family.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 8.

The construction uses Mathlib's `inclusionInDoubleDual` and `PiLp`; the supremum
formula uses `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`, and the uniform bound for
summable families uses `banach_steinhaus`.
-/

public section

noncomputable section

open NormedSpace
open scoped ENNReal

namespace TauCeti

section NormedField

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [Fintype ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Send a finite vector family to its dual-evaluation operator with `Lᵖ` target norm. -/
def dualEvalLp : (ι → E) →ₗ[𝕜] (StrongDual 𝕜 E →L[𝕜] PiLp p (fun _ : ι ↦ 𝕜)) where
  toFun x := (PiLp.continuousLinearEquiv p 𝕜 (fun _ : ι ↦ 𝕜)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ inclusionInDoubleDual 𝕜 E (x i))
  map_add' x y := by ext f i; simp
  map_smul' c x := by ext f i; simp

/-- Dual evaluation is the family of scalar evaluations, viewed in `PiLp`. -/
@[simp]
theorem dualEvalLp_apply (x : ι → E) (f : StrongDual 𝕜 E) :
    dualEvalLp (𝕜 := 𝕜) p x f = WithLp.toLp p (fun i ↦ f (x i)) := (rfl)

/-- The weak `Lᵖ` seminorm of a finite family is the norm of its dual-evaluation operator. -/
def weakLpNorm : Seminorm 𝕜 (ι → E) :=
  (normSeminorm 𝕜 (StrongDual 𝕜 E →L[𝕜] PiLp p (fun _ : ι ↦ 𝕜))).comp
    (dualEvalLp (𝕜 := 𝕜) p)

/-- The operator-norm characterization of the weak `Lᵖ` seminorm. -/
theorem weakLpNorm_apply (x : ι → E) : weakLpNorm (𝕜 := 𝕜) p x = ‖dualEvalLp (𝕜 := 𝕜) p x‖ := (rfl)

/-- Scalar evaluations are bounded by the weak `Lᵖ` norm times the functional norm. -/
theorem norm_eval_le_weakLpNorm (x : ι → E) (f : StrongDual 𝕜 E) :
    ‖WithLp.toLp p (fun i ↦ f (x i))‖ ≤ weakLpNorm (𝕜 := 𝕜) p x * ‖f‖ := by
  simpa only [dualEvalLp_apply, weakLpNorm_apply] using (dualEvalLp (𝕜 := 𝕜) p x).le_opNorm f

/-- An upper bound on the weak norm is equivalent to the homogeneous evaluation bound. -/
theorem weakLpNorm_le_iff (x : ι → E) {C : ℝ} (hC : 0 ≤ C) :
    weakLpNorm (𝕜 := 𝕜) p x ≤ C ↔
      ∀ f : StrongDual 𝕜 E, ‖WithLp.toLp p (fun i ↦ f (x i))‖ ≤ C * ‖f‖ := by
  simp only [weakLpNorm_apply, ContinuousLinearMap.opNorm_le_iff hC, dualEvalLp_apply]

/-- The weak `Lᵖ` norm is at most the strong `Lᵖ` norm of the vector family. -/
theorem weakLpNorm_le_norm (x : ι → E) :
    weakLpNorm (𝕜 := 𝕜) p x ≤ ‖WithLp.toLp p x‖ := by
  apply (weakLpNorm_le_iff p x (norm_nonneg _)).2
  intro f
  rw [mul_comm]
  exact PiLp.norm_toLp_comp_le (norm_nonneg f) f.le_opNorm x

/-- Applying a bounded operator to a family multiplies its weak norm by at most the
operator norm. -/
theorem weakLpNorm_comp_le (T : E →L[𝕜] F) (x : ι → E) :
    weakLpNorm (𝕜 := 𝕜) p (T ∘ x) ≤ ‖T‖ * weakLpNorm (𝕜 := 𝕜) p x := by
  apply (weakLpNorm_le_iff p _ (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2
  intro f
  calc
    ‖WithLp.toLp p (fun i ↦ f ((T ∘ x) i))‖ ≤
        weakLpNorm (𝕜 := 𝕜) p x * ‖f.comp T‖ := norm_eval_le_weakLpNorm p x (f.comp T)
    _ ≤ weakLpNorm (𝕜 := 𝕜) p x * (‖f‖ * ‖T‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le f T
    _ = (‖T‖ * weakLpNorm (𝕜 := 𝕜) p x) * ‖f‖ := by ring

/-- Reindexing a finite family by an equivalence preserves its weak `Lᵖ` norm. -/
theorem weakLpNorm_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (x : ι → E) :
    weakLpNorm (𝕜 := 𝕜) p (x ∘ e) = weakLpNorm (𝕜 := 𝕜) p x := by
  have hn (f : StrongDual 𝕜 E) :
      ‖WithLp.toLp p (fun i ↦ f ((x ∘ e) i))‖ =
        ‖WithLp.toLp p (fun i ↦ f (x i))‖ :=
    PiLp.norm_toLp_comp_equiv e fun i ↦ f (x i)
  apply le_antisymm
  · exact (weakLpNorm_le_iff p _ (apply_nonneg _ _)).2 fun f ↦
      (hn f).trans_le (norm_eval_le_weakLpNorm p x f)
  · exact (weakLpNorm_le_iff p _ (apply_nonneg _ _)).2 fun f ↦
      (hn f).symm.trans_le (norm_eval_le_weakLpNorm p (x ∘ e) f)

/-- **Hölder's inequality for weak norms.** Multiplying a finite family by scalar weights `c`
multiplies its weak norm by at most the `ℓˢ` norm of the weights, when `1 / p = 1 / s + 1 / q`
with finite `p` and `q`. -/
theorem weakLpNorm_smul_le {q : ℝ≥0∞} [Fact (1 ≤ q)] {s : ℝ}
    (hspq : s.HolderTriple q.toReal p.toReal) (c : ι → 𝕜) (x : ι → E) :
    weakLpNorm (𝕜 := 𝕜) p (fun i ↦ c i • x i) ≤
      (∑ i, ‖c i‖ ^ s) ^ (1 / s) * weakLpNorm (𝕜 := 𝕜) q x := by
  have hs := hspq.pos
  have hq := hspq.symm.pos
  have hp := hspq.pos'
  have hc : 0 ≤ ∑ i, ‖c i‖ ^ s := Finset.sum_nonneg fun i _ ↦ by positivity
  rw [weakLpNorm_le_iff p _ (mul_nonneg (by positivity) (apply_nonneg _ _))]
  intro f
  have hb : 0 ≤ ∑ i, ‖f (x i)‖ ^ q.toReal := Finset.sum_nonneg fun i _ ↦ by positivity
  have hfx : (∑ i, ‖f (x i)‖ ^ q.toReal) ^ (1 / q.toReal) ≤
      weakLpNorm (𝕜 := 𝕜) q x * ‖f‖ := by
    rw [← PiLp.norm_eq_sum hq (WithLp.toLp q fun i ↦ f (x i))]
    exact norm_eval_le_weakLpNorm q x f
  rw [PiLp.norm_eq_sum hp]
  simp only [map_smul, smul_eq_mul, norm_mul]
  calc
    (∑ i, (‖c i‖ * ‖f (x i)‖) ^ p.toReal) ^ (1 / p.toReal)
        ≤ ((∑ i, ‖c i‖ ^ s) ^ (p.toReal / s) *
            (∑ i, ‖f (x i)‖ ^ q.toReal) ^ (p.toReal / q.toReal)) ^ (1 / p.toReal) := by
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ ↦ by positivity) ?_ (by positivity)
      simpa [abs_mul] using Real.Lr_rpow_le_Lp_mul_Lq Finset.univ
        (fun i ↦ ‖c i‖) (fun i ↦ ‖f (x i)‖) hspq
    _ = (∑ i, ‖c i‖ ^ s) ^ (1 / s) * (∑ i, ‖f (x i)‖ ^ q.toReal) ^ (1 / q.toReal) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc,
        ← Real.rpow_mul hb]
      congr 2 <;> field_simp
    _ ≤ (∑ i, ‖c i‖ ^ s) ^ (1 / s) * (weakLpNorm (𝕜 := 𝕜) q x * ‖f‖) := by gcongr
    _ = (∑ i, ‖c i‖ ^ s) ^ (1 / s) * weakLpNorm (𝕜 := 𝕜) q x * ‖f‖ := (mul_assoc _ _ _).symm

end NormedField

section DenselyNormedField

variable {𝕜 E ι : Type*} [DenselyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The weak `Lᵖ` norm is the supremum of scalar `Lᵖ` evaluations over the dual unit ball. -/
theorem weakLpNorm_eq_sSup (x : ι → E) :
    weakLpNorm (𝕜 := 𝕜) p x =
      sSup ((fun f : StrongDual 𝕜 E ↦ ‖WithLp.toLp p (fun i ↦ f (x i))‖) ''
        Metric.closedBall 0 1) := by
  let : NormedAddCommGroup (StrongDual 𝕜 E) := ContinuousLinearMap.normedAddCommGroup
  simpa only [weakLpNorm_apply, dualEvalLp_apply] using
    (dualEvalLp (𝕜 := 𝕜) p x).sSup_unitClosedBall_eq_norm.symm

/-- Bounding the weak norm is equivalent to bounding evaluations on the dual unit ball. -/
theorem weakLpNorm_le_iff_unitBall (x : ι → E) {C : ℝ} :
    weakLpNorm (𝕜 := 𝕜) p x ≤ C ↔
      ∀ f : StrongDual 𝕜 E, ‖f‖ ≤ 1 → ‖WithLp.toLp p (fun i ↦ f (x i))‖ ≤ C := by
  constructor
  · intro h f hf
    exact ((dualEvalLp (𝕜 := 𝕜) p x).unit_le_opNorm f hf).trans h
  · intro h
    rw [weakLpNorm_eq_sSup]
    apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
    rintro _ ⟨f, hf, rfl⟩
    exact h f (by simpa using hf)

end DenselyNormedField

section RCLike

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Each coordinate norm is at most the weak norm of the whole family. -/
theorem norm_le_weakLpNorm (x : ι → E) (i : ι) : ‖x i‖ ≤ weakLpNorm (𝕜 := 𝕜) p x := by
  apply norm_le_dual_bound (𝕜 := 𝕜) _ (apply_nonneg _ _)
  intro f
  exact (PiLp.norm_apply_le (WithLp.toLp p (fun j ↦ f (x j))) i).trans
    (norm_eval_le_weakLpNorm p x f)

/-- A family of multiples of one vector has weak norm equal to its scalar `Lᵖ` norm
times the vector norm. This includes the one-coordinate normalization. -/
theorem weakLpNorm_smul_const (a : ι → 𝕜) (v : E) :
    weakLpNorm (𝕜 := 𝕜) p (fun i ↦ a i • v) = ‖WithLp.toLp p a‖ * ‖v‖ := by
  have heq : dualEvalLp (𝕜 := 𝕜) p (fun i ↦ a i • v) =
      (inclusionInDoubleDual 𝕜 E v).smulRight (WithLp.toLp p a) := by
    ext f i
    simp [mul_comm]
  rw [weakLpNorm_apply, heq, ContinuousLinearMap.norm_smulRight_apply]
  rw [← (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := E)).norm_map v]
  exact mul_comm _ _

/-- A family supported at a single coordinate has weak norm equal to that vector's norm. -/
@[simp]
theorem weakLpNorm_single [DecidableEq ι] (i : ι) (v : E) :
    weakLpNorm (𝕜 := 𝕜) p (Pi.single i v) = ‖v‖ := by
  have he : (fun j ↦ (Pi.single i (1 : 𝕜) : ι → 𝕜) j • v) = Pi.single i v := by
    ext j
    by_cases h : j = i <;> simp [h]
  simpa only [he, PiLp.toLp_single, PiLp.norm_single, norm_one, one_mul] using
    weakLpNorm_smul_const p (Pi.single i (1 : 𝕜)) v

/-- At exponent `∞` the weak norm of a finite family is its strong norm, the largest norm of
its members. -/
@[simp]
theorem weakLpNorm_top (x : ι → E) :
    weakLpNorm (𝕜 := 𝕜) ∞ x = ‖WithLp.toLp ∞ x‖ :=
  le_antisymm (weakLpNorm_le_norm ∞ x)
    (Real.iSup_le (norm_le_weakLpNorm ∞ x) (apply_nonneg _ _))

end RCLike

section Summable

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The finite subfamilies of an unconditionally summable family have uniformly bounded weak `L¹`
norms. -/
theorem _root_.Summable.exists_forall_weakLpNorm_one_le {x : ι → E} (hx : Summable x) :
    ∃ C, ∀ s : Finset ι, weakLpNorm (𝕜 := 𝕜) 1 (fun i : s ↦ x i) ≤ C := by
  classical
  -- The evaluations along each finite subfamily, as operators from the dual into `ℓ¹`.
  let g (s : Finset ι) : StrongDual 𝕜 E →L[𝕜] lp (fun _ : ι ↦ 𝕜) 1 :=
    ∑ i ∈ s, (lp.singleContinuousLinearMap 𝕜 (fun _ : ι ↦ 𝕜) 1 i).comp
      (inclusionInDoubleDual 𝕜 E (x i))
  have hg (s : Finset ι) (f : StrongDual 𝕜 E) : ‖g s f‖ = ∑ i ∈ s, ‖f (x i)‖ := by
    simpa [g] using lp.norm_sum_single (p := 1) (by simp) (fun i ↦ f (x i)) s
  -- Every functional is absolutely summable along `x`, so these operators are pointwise bounded
  -- on the complete dual.
  obtain ⟨C, hC⟩ := banach_steinhaus (g := g) fun f ↦ ⟨∑' i, ‖f (x i)‖, fun s ↦
    (hg s f).trans_le ((summable_norm_iff.2 (hx.mapL f)).sum_le_tsum s fun i _ ↦ norm_nonneg _)⟩
  refine ⟨max C 0, fun s ↦ (weakLpNorm_le_iff 1 _ (le_max_right _ _)).2 fun f ↦ ?_⟩
  rw [PiLp.norm_eq_of_L1]
  simp only [Finset.sum_coe_sort s fun i ↦ ‖f (x i)‖, ← hg]
  exact ((g s).le_opNorm f).trans (by gcongr; exact (hC s).trans (le_max_left _ _))

/-- In a complete space, finite blocks whose weak `L¹` norms are summable assemble into an
unconditionally summable family. -/
theorem summable_sigma_of_summable_weakLpNorm [CompleteSpace E] {κ : Type*} {β : κ → Type*}
    [∀ k, Fintype (β k)] {y : (k : κ) → β k → E}
    (hy : Summable fun k ↦ weakLpNorm (𝕜 := 𝕜) 1 (y k)) :
    Summable fun j : (Σ k, β k) ↦ y j.1 j.2 := by
  classical
  refine summable_iff_vanishing_norm.2 fun ε hε ↦ ?_
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hy ε hε
  refine ⟨s.sigma fun _ ↦ Finset.univ, fun t ht ↦ ?_⟩
  -- The blocks met by `t` avoid `s`, and the sum over `t` is controlled by their weak norms.
  have hu : Disjoint (t.image Sigma.fst) s := by
    refine Finset.disjoint_left.2 fun k hk hks ↦ ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
    exact Finset.disjoint_left.1 ht hj (Finset.mem_sigma.2 ⟨hks, Finset.mem_univ _⟩)
  have hle : ‖∑ j ∈ t, y j.1 j.2‖ ≤ ∑ k ∈ t.image Sigma.fst, weakLpNorm (𝕜 := 𝕜) 1 (y k) := by
    refine norm_le_dual_bound (𝕜 := 𝕜) _ (Finset.sum_nonneg fun k _ ↦ apply_nonneg _ _)
      fun f ↦ ?_
    calc
      ‖f (∑ j ∈ t, y j.1 j.2)‖ ≤ ∑ j ∈ t, ‖f (y j.1 j.2)‖ := by
        rw [map_sum]
        exact norm_sum_le _ _
      _ ≤ ∑ j ∈ (t.image Sigma.fst).sigma fun _ ↦ Finset.univ, ‖f (y j.1 j.2)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun j hj ↦ Finset.mem_sigma.2 ⟨Finset.mem_image_of_mem _ hj, Finset.mem_univ _⟩)
          fun _ _ _ ↦ norm_nonneg _
      _ = ∑ k ∈ t.image Sigma.fst, ‖WithLp.toLp 1 (fun i ↦ f (y k i))‖ := by
        rw [Finset.sum_sigma]
        simp [PiLp.norm_eq_of_L1]
      _ ≤ ∑ k ∈ t.image Sigma.fst, weakLpNorm (𝕜 := 𝕜) 1 (y k) * ‖f‖ :=
        Finset.sum_le_sum fun k _ ↦ norm_eval_le_weakLpNorm 1 (y k) f
      _ = _ := (Finset.sum_mul _ _ _).symm
  exact hle.trans_lt ((le_abs_self _).trans_lt (Real.norm_eq_abs _ ▸ hs _ hu))

end Summable

/-- The weak `Lᵖ` seminorm separates finite families over real or complex scalars. -/
@[simp]
theorem weakLpNorm_eq_zero_iff {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : ι → E) :
    weakLpNorm (𝕜 := 𝕜) p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    exact norm_eq_zero.mp (le_antisymm (h ▸ norm_le_weakLpNorm p x i) (norm_nonneg _))
  · rintro rfl
    exact map_zero _

end TauCeti
