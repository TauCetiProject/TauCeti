/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Approximate identities in algebraic left ideals of C⋆-algebras

Every complex left ideal `L` of a possibly nonunital C⋆-algebra `A`, closed or not, contains a
right approximate identity of positive contractions: a net `e` of elements of `L` itself with
`x * e → x` for every `x ∈ L`. No closure of `L` is taken, so this applies to dense ideals such as
the finite-rank operators or the compactly supported functions.

For `δ > 0` and positive `b`, the element `TauCeti.CStarAlgebra.resolventCutoff δ b` is
`b (δ + b)⁻¹ = cfcₙ (t ↦ t / (δ + t)) b`. It is a positive contraction, and it satisfies
`e = δ⁻¹ • (b - e * b)`, so it lies in every complex left ideal containing `b`: no unit and no
inverse is needed in the algebra. If `star x * x ≤ b`, then `‖x - x * e‖ ^ 2 ≤ δ / 4`, because
`sup_{t ≥ 0} δ² t / (δ + t)² = δ / 4`.

Indexing by finite sets `F ⊆ L` and `δ > 0`, and taking `b_F = ∑ x ∈ F, star x * x ∈ L`, the net
`e_{F,δ} = resolventCutoff δ b_F` is the required approximate identity. Taking stars gives the
corresponding left approximate identity in a right ideal, and when `L` is norm separable,
finite initial segments of a dense sequence give an approximate identity indexed by `ℕ`.

## Main declarations

* `TauCeti.CStarAlgebra.resolventCutoff`: the element `b (δ + b)⁻¹`, with
  `resolventCutoff_nonneg`, `norm_resolventCutoff_le_one`, `resolventCutoff_mem` (membership in a
  left ideal containing `b`) and the estimate `norm_sub_mul_resolventCutoff_sq_le`.
* `TauCeti.CStarAlgebra.tendsto_mul_resolventCutoff_sum`: convergence of the net `e_{F,δ}`.
* `Submodule.exists_rightApproximateUnit`: a left ideal has a positive contractive right
  approximate identity in itself, which is a two-sided one on the elements `x ∈ L` with
  `star x ∈ L`.
* `Submodule.exists_leftApproximateUnit`: the same for right ideals, on the other side.
* `Submodule.exists_seq_rightApproximateUnit`: a separable left ideal has such an approximate
  identity indexed by `ℕ`.

## References

* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*,
  II.5.3.3 and II.5.3.13.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 3.1.1, whose net couples the two
  indices by `δ = 1 / card F`.
-/

public section

open Filter Topology

namespace TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local notation "σₙ" => quasispectrum

/-- The element `b (δ + b)⁻¹` of a C⋆-algebra, defined by the continuous functional calculus as
`cfcₙ (t ↦ t / (δ + t)) b`. For `δ > 0` and positive `b` it is a positive contraction lying in
every complex left ideal that contains `b`. -/
noncomputable def resolventCutoff (δ : ℝ) (b : A) : A :=
  cfcₙ (fun t : ℝ ↦ t / (δ + t)) b

omit [PartialOrder A] [StarOrderedRing A] in
theorem resolventCutoff_def (δ : ℝ) (b : A) :
    resolventCutoff δ b = cfcₙ (fun t : ℝ ↦ t / (δ + t)) b :=
  (rfl)

/-- `b (δ + b)⁻¹` is positive for `δ ≥ 0` and positive `b`. -/
theorem resolventCutoff_nonneg {δ : ℝ} (hδ : 0 ≤ δ) {b : A} (hb : 0 ≤ b) :
    0 ≤ resolventCutoff δ b :=
  cfcₙ_nonneg fun t ht ↦ by
    have := quasispectrum_nonneg_of_nonneg b hb t ht
    positivity

/-- `b (δ + b)⁻¹` is a contraction for `δ ≥ 0` and positive `b`. -/
theorem norm_resolventCutoff_le_one {δ : ℝ} (hδ : 0 ≤ δ) {b : A} (hb : 0 ≤ b) :
    ‖resolventCutoff δ b‖ ≤ 1 :=
  norm_cfcₙ_le fun t ht ↦ by
    have := quasispectrum_nonneg_of_nonneg b hb t ht
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_le_one_of_le₀ (by linarith) (by positivity)

/-- The function `t ↦ t / (δ + t)` is continuous on the quasispectrum of a positive element. -/
private theorem continuousOn_div_add {δ : ℝ} (hδ : 0 < δ) {b : A} (hb : 0 ≤ b) :
    ContinuousOn (fun t : ℝ ↦ t / (δ + t)) (σₙ ℝ b) :=
  continuousOn_id.div (continuousOn_const.add continuousOn_id) fun t ht ↦
    (add_pos_of_pos_of_nonneg hδ (quasispectrum_nonneg_of_nonneg b hb t ht)).ne'

/-- The identity `e = δ⁻¹ • (b - e * b)` for `e = b (δ + b)⁻¹`, which writes `e` without the
inverse of `δ + b`. -/
theorem resolventCutoff_eq_inv_smul {δ : ℝ} (hδ : 0 < δ) {b : A} (hb : 0 ≤ b) :
    resolventCutoff δ b = δ⁻¹ • (b - resolventCutoff δ b * b) := by
  have hpos : ∀ t ∈ σₙ ℝ b, δ + t ≠ 0 := fun t ht ↦
    (add_pos_of_pos_of_nonneg hδ (quasispectrum_nonneg_of_nonneg b hb t ht)).ne'
  have hf := continuousOn_div_add hδ hb
  rw [resolventCutoff_def]
  calc cfcₙ (fun t : ℝ ↦ t / (δ + t)) b
      = cfcₙ (fun t : ℝ ↦ δ⁻¹ * (t - t / (δ + t) * t)) b :=
        cfcₙ_congr fun t ht ↦ by
          have := hpos t ht
          field_simp
          ring
    _ = δ⁻¹ • (b - cfcₙ (fun t : ℝ ↦ t / (δ + t)) b * b) := by
        have hfm : ContinuousOn (fun t : ℝ ↦ t / (δ + t) * t) (σₙ ℝ b) := hf.mul continuousOn_id
        rw [cfcₙ_const_mul δ⁻¹ (fun t : ℝ ↦ t - t / (δ + t) * t) b
            (continuousOn_id.sub hfm),
          cfcₙ_sub (fun t : ℝ ↦ t) (fun t : ℝ ↦ t / (δ + t) * t) b (hg := hfm),
          cfcₙ_mul (fun t : ℝ ↦ t / (δ + t)) (fun t : ℝ ↦ t) b (hf := hf), cfcₙ_id' ℝ b]

/-- `b (δ + b)⁻¹` lies in every complex left ideal that contains the positive element `b`; the
ideal need not be closed. -/
theorem resolventCutoff_mem {L : Submodule ℂ A} (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) {δ : ℝ}
    (hδ : 0 < δ) {b : A} (hb₀ : 0 ≤ b) (hb : b ∈ L) : resolventCutoff δ b ∈ L := by
  rw [resolventCutoff_eq_inv_smul hδ hb₀]
  exact L.smul_of_tower_mem _ (L.sub_mem hb (hL _ _ hb))

/-- The elementary bound `√t · δ / (δ + t) ≤ √δ / 2` for `t ≥ 0`, the maximum being attained at
`t = δ`. -/
private theorem sqrt_mul_div_add_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    |√t - √t * (t / (δ + t))| ≤ √δ / 2 := by
  have hδt : 0 < δ + t := by positivity
  have hs := Real.sq_sqrt ht
  have hr := Real.sq_sqrt hδ.le
  have hs₀ := Real.sqrt_nonneg t
  have hr₀ := Real.sqrt_nonneg δ
  have heq : √t - √t * (t / (δ + t)) = √t * δ / (δ + t) := by
    field_simp
    ring
  rw [heq, abs_of_nonneg (by positivity), div_le_div_iff₀ hδt two_pos]
  nlinarith [mul_nonneg hr₀ (sq_nonneg (√δ - √t))]

/-- If `star x * x ≤ b`, then `e = b (δ + b)⁻¹` is a right unit for `x` up to
`‖x - x * e‖ ^ 2 ≤ δ / 4`. -/
theorem norm_sub_mul_resolventCutoff_sq_le {δ : ℝ} (hδ : 0 < δ) {x b : A}
    (hxb : star x * x ≤ b) : ‖x - x * resolventCutoff δ b‖ ^ 2 ≤ δ / 4 := by
  have hb : 0 ≤ b := (star_mul_self_nonneg x).trans hxb
  have hy : star (CFC.sqrt b) * CFC.sqrt b = b := by
    rw [(CFC.sqrt_nonneg b).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self b]
  have hf := continuousOn_div_add hδ hb
  -- Compare `x` with `√b`, whose defect is computed by the functional calculus.
  have hcmp := norm_sub_mul_le_of_star_mul_self_le (hy.symm ▸ hxb) (resolventCutoff δ b)
  have hroot : ‖CFC.sqrt b - CFC.sqrt b * resolventCutoff δ b‖ ≤ √δ / 2 := by
    rw [resolventCutoff_def, CFC.sqrt_eq_real_sqrt b,
      ← cfcₙ_mul (fun t : ℝ ↦ √t) (fun t : ℝ ↦ t / (δ + t)) b (hg := hf),
      ← cfcₙ_sub (fun t : ℝ ↦ √t) (fun t : ℝ ↦ √t * (t / (δ + t))) b
        (hg := Real.continuous_sqrt.continuousOn.mul hf)]
    exact norm_cfcₙ_le fun t ht ↦
      sqrt_mul_div_add_le hδ (quasispectrum_nonneg_of_nonneg b hb t ht)
  calc ‖x - x * resolventCutoff δ b‖ ^ 2 ≤ (√δ / 2) ^ 2 := by
        gcongr
        exact hcmp.trans hroot
    _ = δ / 4 := by
        rw [div_pow, Real.sq_sqrt hδ.le]
        norm_num

/-- For a set `S`, the net `e_{F,δ} = b_F (δ + b_F)⁻¹`, with `b_F = ∑ y ∈ F, star y * y`, indexed
by finite subsets `F` of `S` (ordered by inclusion) and `δ → 0⁺`, is a right approximate identity
for `S`: `x * e_{F,δ} → x` for every `x ∈ S`. -/
theorem tendsto_mul_resolventCutoff_sum {S : Set A} {x : A} (hx : x ∈ S) :
    Tendsto (fun p : Finset S × ℝ ↦ x * resolventCutoff p.2 (∑ y ∈ p.1, star (y : A) * y))
      (atTop ×ˢ 𝓝[>] 0) (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun p : Finset S × ℝ ↦ √(p.2 / 4)) (atTop ×ˢ 𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun δ : ℝ ↦ √(δ / 4)) (𝓝 0) (𝓝 0) := by
      simpa using (show Continuous fun δ : ℝ ↦ √(δ / 4) by fun_prop).tendsto 0
    exact (this.mono_left nhdsWithin_le_nhds).comp tendsto_snd
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hs
  filter_upwards [prod_mem_prod (eventually_ge_atTop {⟨x, hx⟩}) self_mem_nhdsWithin] with
    ⟨F, δ⟩ ⟨hF, hδ⟩
  rw [norm_sub_rev]
  refine Real.le_sqrt_of_sq_le (norm_sub_mul_resolventCutoff_sq_le hδ ?_)
  exact Finset.single_le_sum (f := fun y : S ↦ star (y : A) * y)
    (fun _ _ ↦ star_mul_self_nonneg _) (hF (Finset.mem_singleton_self _))

omit [PartialOrder A] [StarOrderedRing A] in
/-- Along a filter of eventually self-adjoint elements, `star x * e → star x` implies
`e * x → x`. -/
theorem tendsto_mul_right_of_tendsto_mul_left_star {l : Filter A} (hl : ∀ᶠ e in l, IsSelfAdjoint e)
    {x : A} (h : Tendsto (star x * ·) l (𝓝 (star x))) : Tendsto (· * x) l (𝓝 x) := by
  refine (star_star x ▸ h.star).congr' ?_
  filter_upwards [hl] with e he
  simp [he.star_eq]

end TauCeti.CStarAlgebra

namespace Submodule

open TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A complex left ideal `L` of a C⋆-algebra, not necessarily closed, has a right approximate
identity of positive contractions lying in `L` itself: a proper filter along which `x * e → x`
for every `x ∈ L`. It is a two-sided approximate identity for the elements `x ∈ L` with
`star x ∈ L`. -/
theorem exists_rightApproximateUnit (L : Submodule ℂ A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, e ∈ L) ∧ (∀ᶠ e in l, 0 ≤ e) ∧ (∀ᶠ e in l, ‖e‖ ≤ 1) ∧
      (∀ x ∈ L, Tendsto (x * ·) l (𝓝 x)) ∧
      ∀ x ∈ L, star x ∈ L → Tendsto (· * x) l (𝓝 x) := by
  set e : Finset (L : Set A) × ℝ → A := fun p ↦ resolventCutoff p.2 (∑ y ∈ p.1, star (y : A) * y)
  set l₀ : Filter (Finset (L : Set A) × ℝ) := atTop ×ˢ 𝓝[>] 0
  have hb (F : Finset (L : Set A)) : 0 ≤ ∑ y ∈ F, star (y : A) * y :=
    Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _
  have hδ : ∀ᶠ p in l₀, 0 < p.2 := tendsto_snd.eventually self_mem_nhdsWithin
  have hpos : ∀ᶠ a in Filter.map e l₀, 0 ≤ a :=
    eventually_map.mpr <| hδ.mono fun p hp ↦ resolventCutoff_nonneg hp.le (hb p.1)
  have hright (x : A) (hx : x ∈ L) : Tendsto (x * ·) (Filter.map e l₀) (𝓝 x) :=
    tendsto_map'_iff.mpr (tendsto_mul_resolventCutoff_sum (S := (L : Set A)) hx)
  refine ⟨Filter.map e l₀, inferInstance, eventually_map.mpr <| hδ.mono fun p hp ↦
    resolventCutoff_mem hL hp (hb p.1) (L.sum_mem fun y _ ↦ hL _ _ y.property), hpos,
    eventually_map.mpr <| hδ.mono fun p hp ↦ norm_resolventCutoff_le_one hp.le (hb p.1),
    hright, fun x _ hx' ↦ ?_⟩
  exact tendsto_mul_right_of_tendsto_mul_left_star (hpos.mono fun _ ↦ IsSelfAdjoint.of_nonneg)
    (hright _ hx')

/-- A complex right ideal `R` of a C⋆-algebra, not necessarily closed, has a left approximate
identity of positive contractions lying in `R` itself: a proper filter along which `e * x → x`
for every `x ∈ R`. It is a two-sided approximate identity for the elements `x ∈ R` with
`star x ∈ R`. -/
theorem exists_leftApproximateUnit (R : Submodule ℂ A) (hR : ∀ a : A, ∀ x ∈ R, x * a ∈ R) :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, e ∈ R) ∧ (∀ᶠ e in l, 0 ≤ e) ∧ (∀ᶠ e in l, ‖e‖ ≤ 1) ∧
      (∀ x ∈ R, Tendsto (· * x) l (𝓝 x)) ∧
      ∀ x ∈ R, star x ∈ R → Tendsto (x * ·) l (𝓝 x) := by
  -- The image `star R` is a left ideal; positive elements of `star R` lie in `R`.
  set L : Submodule ℂ A := R.comap (starLinearEquiv ℂ (A := A)).toLinearMap
  have hmem {x : A} : x ∈ L ↔ star x ∈ R := by
    simp [L]
  have hL (a : A) (x : A) (hx : x ∈ L) : a * x ∈ L := by
    rw [hmem, star_mul]
    exact hR _ _ (hmem.mp hx)
  obtain ⟨l, hl, hmemL, hpos, hnorm, hright, -⟩ := L.exists_rightApproximateUnit hL
  have hsa : ∀ᶠ e in l, IsSelfAdjoint e := hpos.mono fun _ ↦ IsSelfAdjoint.of_nonneg
  refine ⟨l, hl, ?_, hpos, hnorm, fun x hx ↦ ?_, fun x _ hx' ↦ ?_⟩
  · filter_upwards [hmemL, hsa] with e he hsa
    simpa [hsa.star_eq] using hmem.mp he
  · exact tendsto_mul_right_of_tendsto_mul_left_star hsa (hright _ (hmem.mpr (by simpa)))
  · exact hright x (hmem.mpr hx')

/-- A norm-separable complex left ideal `L` of a C⋆-algebra, not necessarily closed, has a
sequential right approximate identity of positive contractions lying in `L`. The `n`-th term is
`b_n (1 / (n + 1) + b_n)⁻¹`, where `b_n = ∑ k ≤ n, star (u k) * u k` for a dense sequence `u`
in `L`. -/
theorem exists_seq_rightApproximateUnit (L : Submodule ℂ A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    [TopologicalSpace.SeparableSpace L] :
    ∃ e : ℕ → A, (∀ n, e n ∈ L) ∧ (∀ n, 0 ≤ e n) ∧ (∀ n, ‖e n‖ ≤ 1) ∧
      ∀ x ∈ L, Tendsto (fun n ↦ x * e n) atTop (𝓝 x) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq L
  set b : ℕ → A := fun n ↦ ∑ k ∈ Finset.range (n + 1), star (u k : A) * u k
  set e : ℕ → A := fun n ↦ resolventCutoff (1 / (n + 1)) (b n)
  have hb (n : ℕ) : 0 ≤ b n := Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _
  have hδ (n : ℕ) : (0 : ℝ) < 1 / (n + 1) := by positivity
  have hnorm (n : ℕ) : ‖e n‖ ≤ 1 := norm_resolventCutoff_le_one (hδ n).le (hb n)
  -- Convergence holds on the dense sequence, by the estimate of
  -- `norm_sub_mul_resolventCutoff_sq_le`.
  have hdense (k : ℕ) : Tendsto (fun n ↦ (u k : A) * e n) atTop (𝓝 (u k)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hs : Tendsto (fun n : ℕ ↦ √((1 / ((n : ℝ) + 1)) / 4)) atTop (𝓝 0) := by
      have : Tendsto (fun δ : ℝ ↦ √(δ / 4)) (𝓝 0) (𝓝 0) := by
        simpa using (show Continuous fun δ : ℝ ↦ √(δ / 4) by fun_prop).tendsto 0
      exact this.comp tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hs
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [norm_sub_rev]
    refine Real.le_sqrt_of_sq_le (norm_sub_mul_resolventCutoff_sq_le (hδ n) ?_)
    exact Finset.single_le_sum (f := fun k ↦ star (u k : A) * u k)
      (fun _ _ ↦ star_mul_self_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  -- The maps `x ↦ x * e n` are `1`-Lipschitz, so the convergence set is closed.
  have hequi : Equicontinuous fun n (x : L) ↦ (x : A) * e n :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun n ↦ LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa [dist_eq_norm, ← sub_mul] using
        (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hnorm n))).equicontinuous
  refine ⟨e, fun n ↦
    resolventCutoff_mem hL (hδ n) (hb n) (L.sum_mem fun k _ ↦ hL _ _ (u k).property),
    fun n ↦ resolventCutoff_nonneg (hδ n).le (hb n), hnorm, fun x hx ↦ ?_⟩
  exact hu.induction_on (p := fun y : L ↦ Tendsto (fun n ↦ (y : A) * e n) atTop (𝓝 (y : A)))
    ⟨x, hx⟩ (hequi.isClosed_setOfPred_tendsto continuous_subtypeVal) hdense

end Submodule
