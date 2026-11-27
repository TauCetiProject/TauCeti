/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Analysis.Normed.Operator.ClosedRange

/-!
# Peetre's compact-error estimate

An estimate `‖x‖ ≤ C * ‖T x‖ + ‖K x‖`, with `K` compact, forces the kernel of `T` to be
finite dimensional; in particular a compact operator bounded below has finite-dimensional domain.
The compact operator may be replaced by any map `f`, not necessarily linear, sending the closed unit
ball into a compact set with `‖x - y‖ ≤ C * dist (f x) (f y)` on the ball
(`FiniteDimensional.of_norm_sub_le_mul_dist`); this is how a space of functionals represented by
chosen, compactly bounded fields is shown to be finite-dimensional.
If the domain is complete, the estimate also makes `T` bounded below on any closed subspace
disjoint from its kernel, and the range of `T` is closed over any
nontrivially normed field. The closed-range step needs no complement of the kernel: by the
sequential criterion `ContinuousLinearMap.isClosed_range_of_exists_subseq_tendsto` from
`TauCeti.Analysis.Normed.Operator.ClosedRange`, an operator has closed range as soon as every
bounded sequence with convergent images has a convergent subsequence.

This is the functional-analytic step that turns an elliptic estimate with a compact interior
error into finite-dimensional kernel and closed range. It does not assert finite-dimensional
cokernel: that requires a corresponding estimate for the adjoint or another argument.

The sequential form says that a bounded sequence whose `T`-images converge has a convergent
subsequence. Its limit solves the limiting equation. No completeness of either target space
is needed; the compact-error target may even be seminormed.

On a complete domain the estimate also bounds the distance to the kernel: the quotient norm of
`x` modulo `ker T` is at most `C' * ‖T x‖`, over any nontrivially normed field. Over `ℝ` or `ℂ`
(more generally, a field with `IsRCLikeNormedField`) the finite-dimensional kernel moreover has a
closed complement, and the bound is witnessed by a continuous projection `P` onto `ker T` with
`‖x - P x‖ ≤ C' * ‖T x‖`. This is the abstract form of the Deny–Lions lemma: applied to the highest
weak derivative of a Sobolev space with compact lower-order inclusion, it says that the quotient
norm modulo the kernel of the top derivative is equivalent to the top seminorm.

An estimate `‖x‖ ≤ C * (‖T x‖ + ‖K x‖)`, the usual shape of an elliptic estimate, has this form
after rescaling `K` (`ContinuousLinearMap.exists_compact_estimate_of_norm_le_mul_add_norm`).

Two consequences adapt such an estimate to a changed operator or a changed error term. A compact
perturbation `S` of `T` satisfies an estimate of the same form
(`ContinuousLinearMap.exists_compact_estimate_of_isCompactOperator_sub`), so the semi-Fredholm
conclusions pass to `S`. And on a complete domain, over any nontrivially normed field, the compact
error may be replaced by `‖j x‖` for any continuous linear `j` which is injective on `ker T`,
compact or not (`ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_of_compact_estimate`): the
pair `(T, j)` is injective and satisfies the same compact-error estimate, so it is bounded below.
For an elliptic operator with a compact lower-order perturbation, this recovers the elliptic
estimate with an `Lᵖ` error term from one whose error contains the perturbation.

The argument uses Mathlib's Riesz lemma, uniform-inducing maps, the sequential closed-range
criterion and quotient estimate, and the compact-operator subsequence API in
`TauCeti.Analysis.Normed.Operator.Compact.Basic`.
The normalization argument extends the one for `1 - K` in
`IsCompactOperator.exists_pos_mul_norm_le_of_disjoint_ker` to operators with distinct targets
for the principal term and the compact error.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1: estimates with a compact error in the Fredholm criterion.
* J. Peetre, *Another approach to elliptic boundary problems*, Comm. Pure Appl. Math. 14 (1961),
  711–731.
* L. Tartar, *An Introduction to Sobolev Spaces and Interpolation Spaces*, Springer (2007):
  the Peetre–Tartar lemma, the quotient estimate modulo the kernel.
-/

public section

namespace ContinuousLinearMap

open Filter
open scoped Topology

section Seminormed

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [Module 𝕜 E] [SeminormedAddCommGroup F] [Module 𝕜 F]
variable [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] {C : ℝ}

/-- An estimate `‖x‖ ≤ C * (‖T x‖ + ‖K x‖)` with `K` compact has the compact-error form
`‖x‖ ≤ C' * ‖T x‖ + ‖K' x‖`. The new compact error is `x ↦ a • K x` for a scalar `a` of large
enough norm. The domain need only be seminormed, and the target of `T` only enters through its
seminorm. -/
theorem exists_compact_estimate_of_norm_le_mul_add_norm {T : E →L[𝕜] F} {K : E →L[𝕜] G}
    (hK : IsCompactOperator K) (hbound : ∀ x, ‖x‖ ≤ C * (‖T x‖ + ‖K x‖)) :
    ∃ (C' : ℝ) (K' : E →L[𝕜] G), IsCompactOperator K' ∧ ∀ x, ‖x‖ ≤ C' * ‖T x‖ + ‖K' x‖ := by
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm 𝕜 |C|
  refine ⟨|C|, a • K, hK.smul a, fun x ↦ ?_⟩
  rw [smul_apply, norm_smul]
  calc ‖x‖ ≤ C * (‖T x‖ + ‖K x‖) := hbound x
    _ ≤ |C| * (‖T x‖ + ‖K x‖) := by gcongr; exact le_abs_self C
    _ ≤ |C| * ‖T x‖ + ‖a‖ * ‖K x‖ := by
        rw [mul_add]
        exact add_le_add_right (mul_le_mul_of_nonneg_right ha.le (norm_nonneg (K x))) _

end Seminormed

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {C : ℝ}

/-- An operator satisfying an a priori estimate with a compact error has finite-dimensional
kernel. The domain and the target spaces need not be complete, and the target spaces need
only be seminormed. -/
theorem finiteDimensional_ker_of_compact_estimate [CompleteSpace 𝕜]
    [SeminormedAddCommGroup F] [Module 𝕜 F] (T : E →L[𝕜] F) {K : E →L[𝕜] G}
    (hK : IsCompactOperator K) (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) :
    FiniteDimensional 𝕜 T.ker := by
  by_contra hfinite
  obtain ⟨R, v, _, hvbound, hvsep⟩ := exists_seq_norm_le_one_le_norm_sub hfinite
  have hKker : IsCompactOperator (K.comp T.ker.subtypeL : T.ker →ₗ[𝕜] G) := by
    simpa only [coe_coe, coe_comp] using hK.comp_clm T.ker.subtypeL
  obtain ⟨m, n, hmn, hclose⟩ := hKker.exists_dist_lt_of_norm_le hvbound zero_lt_one
  have h := hbound ((v m : E) - (v n : E))
  have hTv (i : ℕ) : T (v i : E) = 0 := (v i).property
  simp only [map_sub, hTv, sub_self, norm_zero, mul_zero, zero_add] at h
  have hsep : 1 ≤ ‖(v m : E) - (v n : E)‖ := hvsep hmn.ne
  exact (hsep.trans h).not_gt (by simpa [dist_eq_norm] using hclose)

/-- **Compact perturbations preserve compact-error estimates.** If
`‖x‖ ≤ C * ‖T x‖ + ‖K x‖` with `K` compact and `S - T` is compact, then `S` satisfies an estimate
of the same form. The new compact error is `x ↦ a • ((S - T) x, K x)` for a scalar `a` of large
enough norm. -/
theorem exists_compact_estimate_of_isCompactOperator_sub [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T S : E →L[𝕜] F} {K : E →L[𝕜] G} (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) (hST : IsCompactOperator (S - T)) :
    ∃ (C' : ℝ) (K' : E →L[𝕜] F × G), IsCompactOperator K' ∧
      ∀ x, ‖x‖ ≤ C' * ‖S x‖ + ‖K' x‖ := by
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm 𝕜 (2 * (|C| + 1))
  refine ⟨|C|, a • (S - T).prod K, ?_, fun x ↦ ?_⟩
  · have h := ((hST.clm_comp (inl 𝕜 F G)).add (hK.clm_comp (inr 𝕜 F G))).smul a
    convert h using 1
    funext x
    simp
  · -- `T x = S x - (S - T) x`, and both error terms are controlled by the product norm.
    have hT : ‖T x‖ ≤ ‖S x‖ + ‖(S - T) x‖ := by
      calc ‖T x‖ = ‖S x - (S - T) x‖ := by rw [sub_apply, sub_sub_cancel]
        _ ≤ ‖S x‖ + ‖(S - T) x‖ := norm_sub_le _ _
    have h₁ : ‖(S - T) x‖ ≤ ‖((S - T).prod K) x‖ := norm_fst_le ((S - T) x, K x)
    have h₂ : ‖K x‖ ≤ ‖((S - T).prod K) x‖ := norm_snd_le ((S - T) x, K x)
    set N := ‖((S - T).prod K) x‖
    have hN := norm_nonneg (((S - T).prod K) x)
    have hC := abs_nonneg C
    rw [smul_apply, norm_smul]
    calc ‖x‖ ≤ C * ‖T x‖ + ‖K x‖ := hbound x
      _ ≤ |C| * (‖S x‖ + N) + N := by
          gcongr
          exacts [le_abs_self C, hT.trans (by gcongr)]
      _ ≤ |C| * ‖S x‖ + ‖a‖ * N := by nlinarith

/-- A compact operator bounded below, `‖x‖ ≤ C * ‖K x‖`, has finite-dimensional domain. -/
theorem _root_.IsCompactOperator.finiteDimensional_of_norm_le_mul_norm [CompleteSpace 𝕜]
    {K : E →L[𝕜] G} (hK : IsCompactOperator K) (hbound : ∀ x, ‖x‖ ≤ C * ‖K x‖) :
    FiniteDimensional 𝕜 E := by
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 C
  have := (0 : E →L[𝕜] E).finiteDimensional_ker_of_compact_estimate (C := 0) (K := k • K)
    (hK.smul k) fun x ↦ by
      simpa [norm_smul] using (hbound x).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))
  rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero] at this
  exact Submodule.topEquiv.finiteDimensional

/-- **A nonlinear compact estimate.** A normed space is finite-dimensional if some map `f`, not
necessarily linear, sends its closed unit ball into a compact set and satisfies
`‖x - y‖ ≤ C * dist (f x) (f y)` there: points of the ball whose images lie in one small ball of a
finite cover of the compact set are close, so the closed unit ball is totally bounded. -/
theorem _root_.FiniteDimensional.of_norm_sub_le_mul_dist [CompleteSpace 𝕜] {Y : Type*}
    [PseudoMetricSpace Y] {f : E → Y} {K : Set Y} (hK : IsCompact K)
    (hfK : ∀ x, ‖x‖ ≤ 1 → f x ∈ K)
    (hf : ∀ x y, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x - y‖ ≤ C * dist (f x) (f y)) :
    FiniteDimensional 𝕜 E := by
  refine .of_totallyBounded_nhds_zero 𝕜 (Metric.closedBall_mem_nhds 0 one_pos)
    (Metric.totallyBounded_of_finite_discretization fun ε hε ↦ ?_)
  have hx (x : Metric.closedBall (0 : E) 1) : ‖(x : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 x.property
  -- Cover `K` by finitely many balls of radius `δ`, and send `x` to the centre of one containing
  -- `f x`.
  set δ := ε / (2 * (|C| + 1)) with hδ
  obtain ⟨t, ht, hKt⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded δ (by positivity)
  choose F hF using fun x : Metric.closedBall (0 : E) 1 ↦ by
    simpa using hKt (hfK _ (hx x))
  have := ht.fintype
  refine ⟨ULift (Fin (Fintype.card t)), inferInstance,
    fun x ↦ ULift.up (Fintype.equivFin t ⟨F x, (hF x).1⟩), fun x y hxy ↦ ?_⟩
  have hFxy : F x = F y :=
    congrArg Subtype.val ((Fintype.equivFin t).injective (ULift.up_injective hxy))
  have hd : dist (f x) (f y) < 2 * δ := by
    linarith [dist_triangle_right (f x) (f y) (F y), hFxy ▸ (hF x).2, (hF y).2]
  rw [dist_eq_norm]
  calc ‖(x : E) - y‖ ≤ C * dist (f x) (f y) := hf _ _ (hx x) (hx y)
    _ ≤ (|C| + 1) * dist (f x) (f y) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) dist_nonneg
    _ < (|C| + 1) * (2 * δ) := by gcongr
    _ = ε := by rw [hδ]; field_simp

section CompleteDomain

variable [CompleteSpace E]

/-- Under a compact-error estimate, a bounded sequence whose operator images converge has a
convergent subsequence. The subsequential limit maps to the prescribed limit of the images. -/
theorem exists_subseq_tendsto_of_compact_estimate
    [NormedAddCommGroup F] [Module 𝕜 F] (T : E →L[𝕜] F) {K : E →L[𝕜] G}
    (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖)
    {R : ℝ} {v : ℕ → E} (hvbound : ∀ n, ‖v n‖ ≤ R) {y : F}
    (hTv : Tendsto (fun n ↦ T (v n)) atTop (𝓝 y)) :
    ∃ (x : E) (ψ : ℕ → ℕ), StrictMono ψ ∧
      Tendsto (fun n ↦ v (ψ n)) atTop (𝓝 x) ∧ T x = y := by
  obtain ⟨z, ψ, hψ, hKψ⟩ := hK.exists_subseq_tendsto hvbound
  -- The estimate makes the combined map `(T, K)` a uniform embedding.
  obtain ⟨D, hanti⟩ : ∃ D, AntilipschitzWith D (T.prod K) := by
    apply antilipschitzWith_iff_exists_mul_le_norm.mpr
    refine ⟨(|C| + 1)⁻¹, by positivity, fun x ↦ ?_⟩
    have hTnorm : ‖T x‖ ≤ ‖(T.prod K) x‖ := by
      simpa only [prod_apply] using norm_fst_le (T x, K x)
    have hKnorm : ‖K x‖ ≤ ‖(T.prod K) x‖ := by
      simpa only [prod_apply] using norm_snd_le (T x, K x)
    have hx : ‖x‖ ≤ (|C| + 1) * ‖(T.prod K) x‖ := by
      nlinarith [hbound x, mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg (T x)),
        mul_le_mul_of_nonneg_left hTnorm (abs_nonneg C)]
    exact (inv_mul_le_iff₀ (by positivity : 0 < |C| + 1)).2 hx
  have hpair := (hTv.comp hψ.tendsto_atTop).prodMk_nhds hKψ
  have hcauchy : CauchySeq (fun n ↦ v (ψ n)) := by
    apply (hanti.isUniformInducing (T.prod K).uniformContinuous).cauchy_map_iff.mp
    exact hpair.cauchySeq
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨x, ψ, hψ, hx,
    tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp hx)
      (hTv.comp hψ.tendsto_atTop)⟩

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) {K : E →L[𝕜] G}

/-- A compact-error estimate makes an operator bounded below on every closed subspace
disjoint from its kernel. -/
theorem exists_pos_mul_norm_le_of_compact_estimate
    (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖)
    {M : Submodule 𝕜 E} (hM : IsClosed (M : Set E)) (hdisj : Disjoint T.ker M) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ M, c * ‖x‖ ≤ ‖T x‖ := by
  by_contra! hcon
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm 𝕜
  -- Normalize counterexamples into a fixed shell, without assuming real scalars.
  have hshell : ∀ n : ℕ, ∃ x ∈ M, ‖x‖ ≤ 1 ∧ ‖a‖⁻¹ ≤ ‖x‖ ∧
      ‖T x‖ ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨u, huM, hu⟩ := hcon (1 / (n + 1)) (by positivity)
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨d, _, hdlt, hdge, _⟩ := rescale_to_shell ha one_pos hu0
    refine ⟨d • u, M.smul_mem d huM, hdlt.le, by simpa using hdge, ?_⟩
    calc ‖T (d • u)‖ = ‖d‖ * ‖T u‖ := by rw [map_smul, norm_smul]
      _ ≤ ‖d‖ * (1 / (n + 1) * ‖u‖) := by gcongr
      _ = 1 / (n + 1) * ‖d • u‖ := by rw [norm_smul]; ring
      _ ≤ 1 / (n + 1) := mul_le_of_le_one_right (by positivity) hdlt.le
  choose v hvM hvbound hvge hTv using hshell
  obtain ⟨x, ψ, _, hx, hTx⟩ := T.exists_subseq_tendsto_of_compact_estimate hK hbound
    hvbound (squeeze_zero_norm hTv tendsto_one_div_add_atTop_nhds_zero_nat)
  have hxM : x ∈ M := hM.mem_of_tendsto hx (.of_forall fun n ↦ hvM (ψ n))
  have hxzero : x = 0 := by
    simpa using hdisj.le_bot ⟨LinearMap.mem_ker.mpr hTx, hxM⟩
  have hxge : ‖a‖⁻¹ ≤ ‖x‖ := ge_of_tendsto' hx.norm fun n ↦ hvge (ψ n)
  rw [hxzero, norm_zero] at hxge
  exact hxge.not_gt (by positivity)

/-- **Peetre's lemma**: a compact-error estimate gives closed range. Together with
`finiteDimensional_ker_of_compact_estimate`, this proves the upper semi-Fredholm property. No
completeness of the codomain or of the scalar field is required. -/
theorem isClosed_range_of_compact_estimate
    (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) : IsClosed (T.range : Set F) :=
  T.isClosed_range_of_exists_subseq_tendsto fun hv hTv ↦
    let ⟨x, ψ, hψ, hx, _⟩ := T.exists_subseq_tendsto_of_compact_estimate hK hbound hv hTv
    ⟨x, ψ, hψ, hx⟩

/-- **Abstract Deny–Lions lemma.** A compact-error estimate `‖x‖ ≤ C * ‖T x‖ + ‖K x‖` on a
complete space bounds the quotient norm of `x` modulo `ker T`, that is the distance from `x` to
`ker T`, by a constant multiple of `‖T x‖`. No completeness of the target spaces is needed. This
is the sequential quotient estimate
`ContinuousLinearMap.exists_norm_quotientMk_ker_le_of_exists_subseq_tendsto`, fed by the
subsequence form of the compact-error estimate. -/
theorem exists_norm_quotientMk_ker_le_of_compact_estimate
    (hK : IsCompactOperator K) (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x, ‖(Submodule.Quotient.mk x : E ⧸ T.ker)‖ ≤ C' * ‖T x‖ :=
  T.exists_norm_quotientMk_ker_le_of_exists_subseq_tendsto fun hv hTv ↦
    let ⟨x, ψ, hψ, hx, _⟩ := T.exists_subseq_tendsto_of_compact_estimate hK hbound hv hTv
    ⟨x, ψ, hψ, hx⟩

/-- **Changing the error term of a compact-error estimate.** Let `‖x‖ ≤ C * ‖T x‖ + ‖K x‖` on a
complete space, with `K` compact, and let `j` be a continuous linear map which is injective on the
kernel of `T`. Then the compact error may be replaced by `j`: there is `C'` with
`‖x‖ ≤ C' * (‖T x‖ + ‖j x‖)` for every `x`.

No compactness of `j` is needed, and `j` need not be injective off the kernel of `T`. For an
elliptic operator `T` on a compact base whose estimate carries a compact lower-order perturbation
in `K`, taking for `j` the inclusion into `Lᵖ` gives the elliptic estimate with an `Lᵖ` error. -/
theorem exists_norm_le_mul_norm_add_norm_of_compact_estimate {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) {j : E →L[𝕜] Z}
    (hj : Disjoint T.ker j.ker) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x, ‖x‖ ≤ C' * (‖T x‖ + ‖j x‖) := by
  -- The pair `(T, j)` is injective and satisfies a compact-error estimate, hence is bounded below.
  have hTj (x : E) : ‖T x‖ ≤ ‖(T.prod j) x‖ := by
    simpa only [prod_apply] using norm_fst_le (T x, j x)
  have hbound' (x : E) : ‖x‖ ≤ |C| * ‖(T.prod j) x‖ + ‖K x‖ :=
    (hbound x).trans (by gcongr; exacts [le_abs_self C, hTj x])
  have hker : Disjoint (T.prod j).ker (⊤ : Submodule 𝕜 E) := by
    rw [ker_prod, disjoint_top]
    exact hj.eq_bot
  obtain ⟨c, hc, hcx⟩ := (T.prod j).exists_pos_mul_norm_le_of_compact_estimate hK hbound'
    (by simp) hker
  refine ⟨c⁻¹, inv_nonneg.2 hc.le, fun x ↦ ?_⟩
  rw [le_inv_mul_iff₀ hc]
  calc c * ‖x‖ ≤ ‖(T.prod j) x‖ := hcx x Submodule.mem_top
    _ ≤ ‖T x‖ + ‖j x‖ := by
        rw [prod_apply, Prod.norm_def]
        exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

section Projection

variable [IsRCLikeNormedField 𝕜]

/-- **Peetre's estimate modulo the kernel.** Over `ℝ` or `ℂ`, a compact-error estimate
`‖x‖ ≤ C * ‖T x‖ + ‖K x‖` on a complete space yields a continuous projection `P` onto the
(finite-dimensional) kernel of `T` such that `‖x - P x‖ ≤ C' * ‖T x‖` for every `x`. -/
theorem exists_projection_norm_sub_le_of_compact_estimate
    (hK : IsCompactOperator K) (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) :
    ∃ (P : E →L[𝕜] E) (C' : ℝ), 0 ≤ C' ∧ IsIdempotentElem P ∧ P.range = T.ker ∧
      ∀ x, ‖x - P x‖ ≤ C' * ‖T x‖ := by
  -- The `RCLike` structure carried by `𝕜` makes it complete.
  let := IsRCLikeNormedField.rclike 𝕜
  have := T.finiteDimensional_ker_of_compact_estimate hK hbound
  -- A finite-dimensional kernel has a closed complement `X`, on which `T` is bounded below.
  obtain ⟨X, h⟩ := (Submodule.ClosedComplemented.of_finiteDimensional T.ker).exists_isTopCompl
  obtain ⟨c, hc, hcX⟩ :=
    T.exists_pos_mul_norm_le_of_compact_estimate hK hbound h.isClosed' h.isCompl.disjoint
  refine ⟨T.ker.projectionL X h, c⁻¹, inv_nonneg.2 hc.le, Submodule.isIdempotentElem_projectionL h,
    Submodule.range_projectionL h, fun x ↦ ?_⟩
  -- `x - P x` is the component of `x` in `X`, and `T` does not see the kernel component.
  rw [← Submodule.projectionL_eq_self_sub_projectionL, le_inv_mul_iff₀ hc,
    ← T.apply_projectionL_ker h.symm x]
  exact hcX _ (Submodule.projectionL_apply_mem h.symm x)

end Projection

end CompleteDomain

end ContinuousLinearMap
