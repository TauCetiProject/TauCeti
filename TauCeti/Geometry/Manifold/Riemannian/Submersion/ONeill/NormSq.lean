/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import Mathlib.Analysis.InnerProductSpace.ProdL2
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# The squared norm of O'Neill's tensor `A`

For a Riemannian submersion `f : M → N`, the squared norm of O'Neill's horizontal tensor `A`
(`TauCeti.IsRiemannianSubmersion.oneillA`) is

`|A|² = ∑ᵢ ∑ⱼ |A_(cᵢ) cⱼ|²`,

summed over all ordered pairs of an orthonormal basis `(cᵢ)` of the horizontal space. This is the
quantity in O'Neill's formula `Scal_M = Scal_N ∘ f + Scal_fibre - |A|²` for the scalar curvature
of a submersion with totally geodesic fibres, which shows that the connection metric on a bundle
whose fibre has positive scalar curvature has positive scalar curvature once the fibre is scaled
down enough.

Here `|A|²` (`TauCeti.IsRiemannianSubmersion.oneillANormSq`) is defined without choosing a frame,
as half the metric trace of the bilinear form `(u, u') ↦ tr_g ⟨A_u ·, A_(u') ·⟩`
(`TauCeti.IsRiemannianSubmersion.oneillAInnerForm`). In an orthonormal basis `(eᵢ)` of the whole
tangent space this trace is `∑ᵢ ∑ⱼ |A_(eᵢ) eⱼ|²`. Taking `(eᵢ)` adapted to the splitting into
vertical and horizontal spaces, the pairs with a vertical first entry contribute nothing, since `A`
only sees the horizontal part of its first entry. Because `A_u` exchanges the two spaces and is
skew-adjoint, `∑ₐ |A_u bₐ|² = ∑ⱼ |A_u cⱼ|²` for orthonormal bases `(bₐ)` of the vertical and
`(cⱼ)` of the horizontal space (`TauCeti.IsRiemannianSubmersion.sum_norm_oneillA_sq_ker_eq`), so
the horizontal-vertical pairs contribute exactly as much as the horizontal-horizontal ones. Hence
`|A|²` is given by the formula above in every horizontal orthonormal basis, and also by
`∑ᵢ ∑ₐ |A_(cᵢ) bₐ|²`, the form in which it appears among the mixed curvatures.

In the chart-local frame the trace contracts against the inverse Gram matrix, so `|A|²` is a
smooth function (`TauCeti.IsRiemannianSubmersion.contMDiff_oneillANormSq`), bounded on a compact
manifold.

For the Hopf map from the unit `S³` onto `S²(1/2)`, `|A_X Y| = 1` for a horizontal orthonormal
pair `X, Y`, so `|A|² = 2`: the two off-diagonal ordered pairs each contribute `1`.

## Main definitions

* `TauCeti.IsRiemannianSubmersion.oneillAInnerForm`: the bilinear form
  `(u, u') ↦ tr_g ⟨A_u ·, A_(u') ·⟩`.
* `TauCeti.IsRiemannianSubmersion.oneillANormSq`: the squared norm `|A|²` of O'Neill's tensor.

## Main results

* `TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_sum`: `|A|² = ∑ᵢ ∑ⱼ |A_(cᵢ) cⱼ|²` for every
  orthonormal basis `(cᵢ)` of the horizontal space.
* `TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_sum_ker`: `|A|² = ∑ᵢ ∑ₐ |A_(cᵢ) bₐ|²` for
  orthonormal bases of the horizontal and the vertical space.
* `TauCeti.IsRiemannianSubmersion.contMDiff_oneillANormSq`: `|A|²` is smooth.
* `TauCeti.IsRiemannianSubmersion.exists_forall_oneillANormSq_le`: on a compact manifold, `|A|²`
  is bounded.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Corollary 1.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §§C–D.
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
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

/-- The bilinear form `(u, u') ↦ tr_g ⟨A_u ·, A_(u') ·⟩` on `T_x M`, the metric trace of
`(w, w') ↦ ⟨A_u w, A_(u') w'⟩`. Its metric trace is twice `|A|²`. -/
def oneillAInnerForm (h : IsRiemannianSubmersion I J f) (x : M) :
    BilinForm ℝ (TangentSpace I x) :=
  LinearMap.mk₂ ℝ
    (fun u u' ↦ bilinFormTrace ((innerₗ (TangentSpace I x)).compl₁₂
      (h.oneillA x u : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
      (h.oneillA x u' : TangentSpace I x →ₗ[ℝ] TangentSpace I x)))
    (fun u₁ u₂ u' ↦ by
      rw [← map_add]
      congr 1
      ext w w'
      simp)
    (fun a u u' ↦ by
      rw [← map_smul]
      congr 1
      ext w w'
      simp)
    (fun u u₁ u₂ ↦ by
      rw [← map_add]
      congr 1
      ext w w'
      simp [inner_add_right])
    (fun a u u' ↦ by
      rw [← map_smul]
      congr 1
      ext w w'
      simp)

/-- The squared norm `|A|²` of O'Neill's horizontal tensor at `x`: in every orthonormal basis
`(cᵢ)` of the horizontal space it is `∑ᵢ ∑ⱼ |A_(cᵢ) cⱼ|²` (`oneillANormSq_eq_sum`). It is
defined as half the metric trace of `oneillAInnerForm`, which needs no choice of frame. -/
def oneillANormSq (h : IsRiemannianSubmersion I J f) (x : M) : ℝ :=
  bilinFormTrace (h.oneillAInnerForm x) / 2

include h

/-- The defining formula for `oneillAInnerForm`. -/
theorem oneillAInnerForm_apply (x : M) (u u' : TangentSpace I x) :
    h.oneillAInnerForm x u u' = bilinFormTrace ((innerₗ (TangentSpace I x)).compl₁₂
      (h.oneillA x u : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
      (h.oneillA x u' : TangentSpace I x →ₗ[ℝ] TangentSpace I x)) :=
  (rfl)

/-- In an orthonormal basis `(eⱼ)` of `T_x M`, `oneillAInnerForm` is `∑ⱼ ⟨A_u eⱼ, A_(u') eⱼ⟩`. -/
theorem oneillAInnerForm_eq_sum {x : M} {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (TangentSpace I x)) (u u' : TangentSpace I x) :
    h.oneillAInnerForm x u u' = ∑ j, ⟪h.oneillA x u (e j), h.oneillA x u' (e j)⟫_ℝ := by
  rw [oneillAInnerForm_apply, bilinFormTrace_eq_sum _ e]
  simp

/-- The defining formula for `oneillANormSq`. -/
theorem oneillANormSq_def (x : M) :
    h.oneillANormSq x = bilinFormTrace (h.oneillAInnerForm x) / 2 :=
  (rfl)

/-- In an orthonormal basis `(eᵢ)` of the whole tangent space, `2 |A|² = ∑ᵢ ∑ⱼ |A_(eᵢ) eⱼ|²`. -/
theorem two_mul_oneillANormSq_eq_sum {x : M} {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    2 * h.oneillANormSq x = ∑ i, ∑ j, ‖h.oneillA x (e i) (e j)‖ ^ 2 := by
  rw [oneillANormSq_def, mul_div_cancel₀ _ two_ne_zero, bilinFormTrace_eq_sum _ e]
  simp only [h.oneillAInnerForm_eq_sum e, real_inner_self_eq_norm_sq]

/-- In the chart-local frame `(eᵢ)` at `a`, `|A|²` is half the contraction
`gⁱʲ gᵏˡ ⟨A_(eᵢ) eₖ, A_(eⱼ) eₗ⟩` against the inverse Gram matrix of the frame. -/
private theorem oneillANormSq_eq_sum_chartInvGramMatrix (a : M) {x : M}
    (hx : x ∈ (chartAt H a).source) :
    h.oneillANormSq x = (∑ i, ∑ j, chartInvGramMatrix (I := I) a x i j *
      ∑ k, ∑ l, chartInvGramMatrix (I := I) a x k l *
        ⟪h.oneillA x (chartLocalFrame (I := I) a i x) (chartLocalFrame (I := I) a k x),
          h.oneillA x (chartLocalFrame (I := I) a j x) (chartLocalFrame (I := I) a l x)⟫_ℝ) /
      2 := by
  rw [oneillANormSq_def, bilinFormTrace_eq_sum_chartInvGramMatrix a hx]
  simp only [oneillAInnerForm_apply, bilinFormTrace_eq_sum_chartInvGramMatrix a hx,
    LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe, innerₗ_apply_apply]

variable [IsManifold J ∞ N] [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- **`A_u` has the same size on the vertical and on the horizontal space.** For orthonormal
bases `b` of the vertical space and `c` of the horizontal space,
`∑ᵢ |A_u bᵢ|² = ∑ⱼ |A_u cⱼ|²`. Both sides are `∑ᵢ ∑ⱼ ⟨A_u bᵢ, cⱼ⟩²`, since `A_u` exchanges the
two spaces and is skew-adjoint. -/
theorem sum_norm_oneillA_sq_ker_eq {x : M} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : TangentSpace I x) (b : OrthonormalBasis ι ℝ (mfderiv I J f x).ker)
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).kerᗮ) :
    ∑ i, ‖h.oneillA x u (b i)‖ ^ 2 = ∑ j, ‖h.oneillA x u (c j)‖ ^ 2 := by
  -- Expand each horizontal image `A_u bᵢ` in `c` and each vertical image `A_u cⱼ` in `b`.
  have hb (i : ι) : ‖h.oneillA x u (b i)‖ ^ 2 =
      ∑ j, ⟪(c j : TangentSpace I x), h.oneillA x u (b i)⟫_ℝ ^ 2 := by
    simpa using (c.sum_sq_inner_right
      ⟨h.oneillA x u (b i), h.oneillA_apply_mem_orthogonal_ker u (b i).2⟩).symm
  have hc (j : κ) : ‖h.oneillA x u (c j)‖ ^ 2 =
      ∑ i, ⟪(b i : TangentSpace I x), h.oneillA x u (c j)⟫_ℝ ^ 2 := by
    simpa using (b.sum_sq_inner_right
      ⟨h.oneillA x u (c j), h.oneillA_apply_mem_ker u (c j).2⟩).symm
  simp_rw [hb, hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, ← neg_sq, inner_oneillA, neg_neg]

/-- **`|A|²` in a horizontal frame.** For every orthonormal basis `(cᵢ)` of the horizontal space,
`|A|² = ∑ᵢ ∑ⱼ |A_(cᵢ) cⱼ|²`, summed over all ordered pairs. In particular the right side does not
depend on the basis. -/
theorem oneillANormSq_eq_sum {x : M} {κ : Type*} [Fintype κ]
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).kerᗮ) :
    h.oneillANormSq x = ∑ i, ∑ j, ‖h.oneillA x (c i) (c j)‖ ^ 2 := by
  -- Compute the trace in a basis adapted to the splitting into vertical and horizontal spaces.
  let b := stdOrthonormalBasis ℝ (mfderiv I J f x).ker
  let e : OrthonormalBasis (Fin (Module.finrank ℝ (mfderiv I J f x).ker) ⊕ κ) ℝ
      (TangentSpace I x) :=
    (b.prod c).map (mfderiv I J f x).ker.orthogonalDecomposition.symm
  have he₁ (i : Fin (Module.finrank ℝ (mfderiv I J f x).ker)) : e (Sum.inl i) = b i := by
    simp [e]
  have he₂ (j : κ) : e (Sum.inr j) = c j := by simp [e]
  -- `A` vanishes on the vertical vectors `bᵢ`.
  have hb (i : Fin (Module.finrank ℝ (mfderiv I J f x).ker)) : h.oneillA x (b i) = 0 := by
    rw [← Submodule.starProjection_eq_self_iff.mpr (b i).2, h.oneillA_starProjection_ker]
  have h2 := h.two_mul_oneillANormSq_eq_sum e
  simp only [Fintype.sum_sum_type, he₁, he₂, hb,
    zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, zero_add, h.sum_norm_oneillA_sq_ker_eq _ b c] at h2
  rw [Finset.sum_add_distrib] at h2
  linarith

/-- **`|A|²` in a mixed frame.** For orthonormal bases `(cᵢ)` of the horizontal and `(bₐ)` of the
vertical space, `|A|² = ∑ᵢ ∑ₐ |A_(cᵢ) bₐ|²`. This is the form in which `|A|²` appears among the
curvatures of planes spanned by a horizontal and a vertical vector. -/
theorem oneillANormSq_eq_sum_ker {x : M} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ (mfderiv I J f x).ker)
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).kerᗮ) :
    h.oneillANormSq x = ∑ i, ∑ a, ‖h.oneillA x (c i) (b a)‖ ^ 2 := by
  simp only [h.oneillANormSq_eq_sum c, h.sum_norm_oneillA_sq_ker_eq _ b c]

/-- `|A|²` is nonnegative. -/
theorem oneillANormSq_nonneg (x : M) : 0 ≤ h.oneillANormSq x := by
  rw [h.oneillANormSq_eq_sum (stdOrthonormalBasis ℝ (mfderiv I J f x).kerᗮ)]
  positivity

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
    ((chartAt H a).open_source.mem_nhds (hs ▸ mem_chart_source H a))

/-- `|A|²` is continuous. -/
theorem continuous_oneillANormSq : Continuous h.oneillANormSq :=
  h.contMDiff_oneillANormSq.continuous

/-- On a compact manifold, `|A|²` is bounded. -/
theorem exists_forall_oneillANormSq_le [CompactSpace M] : ∃ C, ∀ x, h.oneillANormSq x ≤ C :=
  let ⟨C, hC⟩ := (isCompact_range h.continuous_oneillANormSq).bddAbove
  ⟨C, fun x ↦ hC (Set.mem_range_self x)⟩

end TauCeti.IsRiemannianSubmersion
