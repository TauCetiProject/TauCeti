/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Bilinear
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# The squared norm of O'Neill's horizontal tensor

Let `f : M → N` be a Riemannian submersion and let `X_i` be the horizontal lifts at `x` of an
orthonormal basis of `T_(f x) N`. The squared norm of O'Neill's horizontal tensor is
`|A|² = ∑ i j, ‖A_(X_i) X_j‖²` (`IsRiemannianSubmersion.oneillANormSq`). It does not depend on the
horizontal orthonormal frame, vanishes exactly where `A` does, and is bounded on compact sets.
Since `A_X` is skew-adjoint and exchanges horizontal and vertical vectors, also
`∑ i a, ‖A_(X_i) V_a‖² = |A|²` for any orthonormal basis `V_a` of the vertical space `ker (df_x)`.

Hence `2 |A|²` is the Hilbert–Schmidt energy `∑ i j, ‖A_(e_i) e_j‖²` of `A` in any orthonormal basis
`e_i` of the whole tangent space, which is also the metric trace of the frame-free bilinear form
`(u, u') ↦ ⟪A_u, A_(u')⟫_HS` (`IsRiemannianSubmersion.oneillAInnerForm`). In the chart-local frame
this trace contracts against the inverse Gram matrix, so `|A|²` is a smooth function.

## Main definitions

* `TauCeti.IsRiemannianSubmersion.oneillANormSq`: the squared norm `|A|²` of O'Neill's horizontal
  tensor.
* `TauCeti.IsRiemannianSubmersion.oneillAInnerForm`: the bilinear form
  `(u, u') ↦ ⟪A_u, A_(u')⟫_HS` on `T_x M`.

## Main results

* `TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_sum`: `|A|²` may be computed in any horizontal
  orthonormal frame.
* `TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_zero_iff`: `|A|²` vanishes exactly where `A`
  does.
* `TauCeti.IsRiemannianSubmersion.exists_oneillANormSq_le_of_isCompact`: `|A|²` is bounded on
  compact sets.
* `TauCeti.IsRiemannianSubmersion.sum_sum_norm_oneillA_horizontalLift_vertical`:
  `∑ i a, ‖A_(X_i) V_a‖² = |A|²`.
* `TauCeti.IsRiemannianSubmersion.two_mul_oneillANormSq_eq_bilinearHilbertSchmidtEnergy`:
  `2 |A|²` is the Hilbert–Schmidt energy of `A` on `T_x M`.
* `TauCeti.IsRiemannianSubmersion.metricTrace_oneillAInnerForm`: `2 |A|²` is the metric trace of
  `oneillAInnerForm`.
* `TauCeti.IsRiemannianSubmersion.contMDiff_oneillANormSq`: `|A|²` is smooth.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1 and Theorem 2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C–§D.
-/

public section

open Bundle Manifold Riemannian.Tensor
open LinearMap (BilinForm)
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)
  {ι κ : Type*} [Fintype ι] [Fintype κ]

include h

/-- The squared norm `|A|² = ∑ i j, ‖A_(X_i) X_j‖²` of O'Neill's horizontal tensor at `x`, where
`X_i` are the horizontal lifts of an orthonormal basis of `T_(f x) N`. It does not depend on the
basis (`TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_sum`). -/
def oneillANormSq (x : M) : ℝ :=
  ∑ i, ∑ j, ‖h.oneillA x (h.horizontalLift x (stdOrthonormalBasis ℝ (TangentSpace J (f x)) i))
    (h.horizontalLift x (stdOrthonormalBasis ℝ (TangentSpace J (f x)) j))‖ ^ 2

omit [IsManifold J ∞ N] [IsContMDiffRiemannianBundle J ∞ F fun y : N ↦ TangentSpace J y] in
/-- `|A|²` may be computed in the horizontal lifts of any orthonormal basis of `T_(f x) N`. -/
theorem oneillANormSq_eq_sum (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace J (f x))) :
    h.oneillANormSq x =
      ∑ i, ∑ j, ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j))‖ ^ 2 := by
  simpa only [oneillANormSq, LinearMap.compl₁₂_apply, LinearIsometry.coe_toLinearMap,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using
    LinearMap.sum_sum_norm_apply_apply_sq_eq_sum_sum_norm_apply_apply_sq
      ((h.oneillA x).toLinearMap₁₂.compl₁₂ (h.horizontalLift x).toLinearMap
        (h.horizontalLift x).toLinearMap) (stdOrthonormalBasis ℝ (TangentSpace J (f x))) b

omit [IsManifold J ∞ N] [IsContMDiffRiemannianBundle J ∞ F fun y : N ↦ TangentSpace J y] in
/-- `|A|²` is nonnegative. -/
theorem oneillANormSq_nonneg (x : M) : 0 ≤ h.oneillANormSq x := by
  unfold oneillANormSq
  positivity

/-- `|A|²` vanishes at `x` exactly when O'Neill's horizontal tensor vanishes at `x`. -/
@[simp]
theorem oneillANormSq_eq_zero_iff (x : M) :
    h.oneillANormSq x = 0 ↔ h.oneillA x = 0 := by
  set b := stdOrthonormalBasis ℝ (TangentSpace J (f x))
  rw [h.oneillA_eq_zero_iff_horizontalLift, h.oneillANormSq_eq_sum x b]
  refine ⟨fun h0 u v ↦ ?_, fun h0 ↦ by simp [h0]⟩
  have hij (i j) : h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j)) = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ by positivity).1 h0 i (Finset.mem_univ _)
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ by positivity).1 hi j
      (Finset.mem_univ _)
  exact LinearMap.congr_fun₂ (LinearMap.ext_basis b.toBasis b.toBasis
    (B := (h.oneillA x).toLinearMap₁₂.compl₁₂ (h.horizontalLift x).toLinearMap
      (h.horizontalLift x).toLinearMap) (B' := 0) (by simpa using hij)) u v

/-- `|A|²` is bounded on every compact set. -/
theorem exists_oneillANormSq_le_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ x ∈ K, h.oneillANormSq x ≤ C := by
  obtain ⟨C, -, hC⟩ := h.exists_norm_oneillA_le_of_isCompact hK
  refine ⟨Module.finrank ℝ F ^ 2 * C ^ 2, fun x hx ↦ ?_⟩
  set b := stdOrthonormalBasis ℝ (TangentSpace J (f x))
  have hle (i j) : ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j))‖ ^ 2 ≤
      C ^ 2 := by
    have := hC x hx (h.horizontalLift x (b i)) (h.horizontalLift x (b j))
    simp only [LinearIsometry.norm_map, b.orthonormal.1, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  calc h.oneillANormSq x ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace J (f x))),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace J (f x))), C ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hle i j
    _ = Module.finrank ℝ F ^ 2 * C ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      -- `TangentSpace J (f x)` is `F` as a real vector space, so the two ranks agree by definition.
      change (Module.finrank ℝ F : ℝ) * ((Module.finrank ℝ F : ℝ) * C ^ 2) = _
      ring

variable {x : M}

/-- In an adapted orthonormal basis, the mixed squared norms of O'Neill's horizontal tensor add up
to `|A|²`: `∑ i a, ‖A_(X_i) V_a‖² = ∑ i j, ‖A_(X_i) X_j‖²`. -/
theorem sum_sum_norm_oneillA_horizontalLift_vertical
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) :
    ∑ i, ∑ a, ‖h.oneillA x (h.horizontalLift x (b i)) (c a)‖ ^ 2 = h.oneillANormSq x := by
  rw [h.oneillANormSq_eq_sum x b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  set X := h.horizontalLift x (b i)
  -- `A_X V_a` is horizontal and `A_X X_j` is vertical, and `A_X` is skew-adjoint, so both sides
  -- are `∑ a j, ⟪X_j, A_X V_a⟫²`.
  calc ∑ a, ‖h.oneillA x X (c a)‖ ^ 2
      = ∑ a, ∑ j, ⟪(c a : TangentSpace I x), h.oneillA x X (h.horizontalLift x (b j))⟫_ℝ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← h.sum_sq_inner_horizontalLift b
          (h.oneillA_apply_mem_orthogonal_ker X (c a).property)]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [real_inner_comm, h.inner_oneillA, neg_sq]
    _ = ∑ j, ‖h.oneillA x X (h.horizontalLift x (b j))‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        exact c.sum_sq_inner_right
          ⟨_, h.oneillA_apply_mem_ker X (h.horizontalLift_mem_orthogonal_ker x (b j))⟩

/-- `2 |A|²` is the Hilbert–Schmidt energy `∑ i j, ‖A_(e_i) e_j‖²` of `A` on `T_x M`, computed in
any orthonormal basis `e_i` of the whole tangent space. In a basis adapted to the splitting into
horizontal and vertical spaces, the pairs with a vertical first entry contribute nothing, and the
horizontal-vertical pairs contribute `|A|²` by
`TauCeti.IsRiemannianSubmersion.sum_sum_norm_oneillA_horizontalLift_vertical`. -/
theorem two_mul_oneillANormSq_eq_bilinearHilbertSchmidtEnergy (x : M) :
    2 * h.oneillANormSq x = (h.oneillA x).bilinearHilbertSchmidtEnergy := by
  let b := stdOrthonormalBasis ℝ (TangentSpace J (f x))
  let c := stdOrthonormalBasis ℝ (mfderiv I J f x).ker
  have hc (a) : h.oneillA x (c a) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr (c a).property, h.oneillA_starProjection_ker]
  rw [ContinuousLinearMap.bilinearHilbertSchmidtEnergy_eq_sum (h.horizontalVerticalBasis x b c)
    (h.horizontalVerticalBasis x b c)]
  simp only [Fintype.sum_sum_type, horizontalVerticalBasis_inl, horizontalVerticalBasis_inr, hc,
    zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib,
    h.sum_sum_norm_oneillA_horizontalLift_vertical b c, ← h.oneillANormSq_eq_sum x b, two_mul]

/-- The bilinear form `(u, u') ↦ ⟪A_u, A_(u')⟫_HS` on `T_x M`: the Hilbert–Schmidt inner product
of `A_u` and `A_(u')`, the metric trace of `(w, w') ↦ ⟪A_u w, A_(u') w'⟫`. Its metric trace is
`2 |A|²` (`TauCeti.IsRiemannianSubmersion.metricTrace_oneillAInnerForm`). -/
def oneillAInnerForm (x : M) : BilinForm ℝ (TangentSpace I x) :=
  LinearMap.mk₂ ℝ (fun u u' ↦ (h.oneillA x u).hilbertSchmidtInner (h.oneillA x u'))
    (fun u₁ u₂ u' ↦ by rw [map_add, ContinuousLinearMap.hilbertSchmidtInner_add_left])
    (fun a u u' ↦ by rw [map_smul, ContinuousLinearMap.hilbertSchmidtInner_smul_left, smul_eq_mul])
    (fun u u₁ u₂ ↦ by rw [map_add, ContinuousLinearMap.hilbertSchmidtInner_add_right])
    (fun a u u' ↦ by
      rw [map_smul, ContinuousLinearMap.hilbertSchmidtInner_smul_right, smul_eq_mul])

omit [IsManifold J ∞ N] [IsContMDiffRiemannianBundle J ∞ F fun y : N ↦ TangentSpace J y] in
/-- The defining formula for `oneillAInnerForm`. -/
theorem oneillAInnerForm_apply (u u' : TangentSpace I x) :
    h.oneillAInnerForm x u u' = (h.oneillA x u).hilbertSchmidtInner (h.oneillA x u') :=
  (rfl)

omit [IsManifold J ∞ N] [IsContMDiffRiemannianBundle J ∞ F fun y : N ↦ TangentSpace J y] in
/-- In an orthonormal basis `e_j` of `T_x M`, `oneillAInnerForm` is `∑ j, ⟪A_u e_j, A_(u') e_j⟫`. -/
theorem oneillAInnerForm_eq_sum (e : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u u' : TangentSpace I x) :
    h.oneillAInnerForm x u u' = ∑ j, ⟪h.oneillA x u (e j), h.oneillA x u' (e j)⟫_ℝ := by
  rw [oneillAInnerForm_apply, ContinuousLinearMap.hilbertSchmidtInner_eq_sum _ _ e]

/-- The metric trace of `oneillAInnerForm` is `2 |A|²`. -/
theorem metricTrace_oneillAInnerForm (x : M) :
    LinearMap.BilinMap.metricTrace (h.oneillAInnerForm x) = 2 * h.oneillANormSq x := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [LinearMap.BilinMap.metricTrace_eq_sum _ e,
    h.two_mul_oneillANormSq_eq_bilinearHilbertSchmidtEnergy x,
    ContinuousLinearMap.bilinearHilbertSchmidtEnergy_eq_sum e e]
  simp only [h.oneillAInnerForm_eq_sum e, real_inner_self_eq_norm_sq]

/-- In the chart-local frame `e_i` at `a`, `|A|²` is half the contraction
`gⁱʲ gᵏˡ ⟪A_(e_i) e_k, A_(e_j) e_l⟫` against the inverse Gram matrix of the frame. -/
private theorem oneillANormSq_eq_sum_chartInvGramMatrix (a : M) (hx : x ∈ (chartAt H a).source) :
    h.oneillANormSq x = (∑ i, ∑ j, chartInvGramMatrix (I := I) a x i j *
      ∑ k, ∑ l, chartInvGramMatrix (I := I) a x k l *
        ⟪h.oneillA x (chartLocalFrame (I := I) a i x) (chartLocalFrame (I := I) a k x),
          h.oneillA x (chartLocalFrame (I := I) a j x) (chartLocalFrame (I := I) a l x)⟫_ℝ) /
      2 := by
  rw [eq_div_iff two_ne_zero, mul_comm, ← h.metricTrace_oneillAInnerForm x,
    metricTrace_eq_sum_chartInvGramMatrix a hx]
  simp only [oneillAInnerForm_apply, ContinuousLinearMap.hilbertSchmidtInner_def,
    metricTrace_eq_sum_chartInvGramMatrix a hx, LinearMap.compl₁₂_apply,
    ContinuousLinearMap.coe_coe, innerₗ_apply_apply, smul_eq_mul]

variable [T2Space M]

/-- **`|A|²` is smooth.** -/
theorem contMDiff_oneillANormSq : ContMDiff I 𝓘(ℝ) ∞ h.oneillANormSq := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  intro a
  set s := (trivializationAt E (TangentSpace I) a).baseSet
  have hs : (chartAt H a).source = s := (TangentBundle.trivializationAt_baseSet (I := I) a).symm
  have hA := h.contMDiff_oneillA.contMDiffOn (s := s)
  have hfr (i : Fin (Module.finrank ℝ E)) := contMDiffOn_chartLocalFrame (I := I) (n := ∞) a i
  have hG (i j : Fin (Module.finrank ℝ E)) :=
    contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞) a i j
  have hsum : ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ (∑ i, ∑ j, chartInvGramMatrix (I := I) a x i j *
      ∑ k, ∑ l, chartInvGramMatrix (I := I) a x k l *
        ⟪h.oneillA x (chartLocalFrame (I := I) a i x) (chartLocalFrame (I := I) a k x),
          h.oneillA x (chartLocalFrame (I := I) a j x) (chartLocalFrame (I := I) a l x)⟫_ℝ) / 2)
      s :=
    (contMDiffOn_finsetSum fun i _ ↦ contMDiffOn_finsetSum fun j _ ↦
      (hG i j).mul <| contMDiffOn_finsetSum fun k _ ↦ contMDiffOn_finsetSum fun l _ ↦
        (hG k l).mul <| ContMDiffOn.inner_bundle (IB := I) (n := ∞) (F := E)
          (E := fun x : M ↦ TangentSpace I x) (hA.clm_bundle_apply₂ (hfr i) (hfr k))
          (hA.clm_bundle_apply₂ (hfr j) (hfr l))).div_const 2
  exact (hsum.congr fun x hx ↦ h.oneillANormSq_eq_sum_chartInvGramMatrix a (hs ▸ hx)).contMDiffAt
    (hs ▸ (chartAt H a).open_source.mem_nhds (mem_chart_source H a))

/-- `|A|²` is continuous. -/
theorem continuous_oneillANormSq : Continuous h.oneillANormSq :=
  h.contMDiff_oneillANormSq.continuous

end TauCeti.IsRiemannianSubmersion
