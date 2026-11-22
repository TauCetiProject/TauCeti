/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Curvature.Sectional
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# O'Neill's scalar-curvature formula for totally geodesic fibres

Let `f : M → N` be a Riemannian submersion. At a point `x` of `M`, horizontal lifts `X_i` of an
orthonormal basis of `T_(f x) N` together with an orthonormal basis `V_a` of the vertical space
`ker (df_x)` form an orthonormal basis of `T_x M`
(`IsRiemannianSubmersion.horizontalVerticalBasis`).

The squared norm of O'Neill's horizontal tensor is `|A|² = ∑ i j, ‖A_(X_i) X_j‖²`
(`IsRiemannianSubmersion.oneillANormSq`). It does not depend on the horizontal orthonormal frame
(`IsRiemannianSubmersion.oneillANormSq_eq_sum`) and is bounded on compact sets. Since `A_X` is
skew-adjoint and exchanges horizontal and vertical vectors, also `∑ i a, ‖A_(X_i) V_a‖² = |A|²`.

Splitting the double trace `Scal = ∑ Rm(e_β, e_α, e_α, e_β)` in this adapted basis gives three
kinds of terms. The horizontal-horizontal terms are `Scal_N(f x) - 3 |A|²` by O'Neill's horizontal
curvature equation. When the vertical tensor `T` vanishes near `x`, that is when the fibres are
totally geodesic there, each mixed term is `‖A_(X_i) V_a‖²` by O'Neill's mixed curvature equation,
and the mixed terms add up to `2 |A|²`. Hence

`Scal_M(x) = Scal_N(f x) + ∑ a b, Rm_M(V_b, V_a, V_a, V_b) - |A|²`

(`IsRiemannianSubmersion.scalarCurvature_eq_of_eventually_oneillT_eq_zero`). The middle term is the
trace of the curvature of `M` over the vertical space. For totally geodesic fibres the Gauss
equation identifies it with the scalar curvature of the fibre through `x`, which turns this into
O'Neill's formula `Scal_M = Scal_N ∘ f + Scal_F - |A|²`; that identification is not made here.
This is the formula behind the scalar curvature `Scal_N + ε⁻² Scal_F - ε² |A|²` of a connection
metric whose totally geodesic fibres are scaled by `ε²`.

## Main definitions

* `TauCeti.IsRiemannianSubmersion.horizontalVerticalBasis`: the orthonormal basis of `T_x M`
  adapted to the horizontal-vertical splitting.
* `TauCeti.IsRiemannianSubmersion.oneillANormSq`: the squared norm `|A|²` of O'Neill's horizontal
  tensor.

## Main results

* `TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_sum`: `|A|²` may be computed in any horizontal
  orthonormal frame.
* `TauCeti.IsRiemannianSubmersion.oneillANormSq_eq_zero_iff`: `|A|²` vanishes exactly where `A`
  does.
* `TauCeti.IsRiemannianSubmersion.exists_oneillANormSq_le_of_isCompact`: `|A|²` is bounded on
  compact sets.
* `TauCeti.IsRiemannianSubmersion.sum_sum_norm_oneillA_horizontalLift_vertical`:
  `∑ i a, ‖A_(X_i) V_a‖² = |A|²`.
* `TauCeti.IsRiemannianSubmersion.scalarCurvature_eq_of_eventually_oneillT_eq_zero`: O'Neill's
  scalar-curvature formula for totally geodesic fibres.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 2 and Corollaries 1–2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (Proposition 9.36 and
  Corollary 9.37).
-/

public section

open Bundle CovariantDerivative Filter Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

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

/-! ### The adapted orthonormal basis -/

section Basis

omit [IsContMDiffRiemannianBundle I ∞ E fun x : M ↦ TangentSpace I x]
  [IsContMDiffRiemannianBundle J ∞ F fun y : N ↦ TangentSpace J y] [IsManifold I ∞ M]
  [IsManifold J ∞ N]

/-- Horizontal lifts of an orthonormal basis of `T_(f x) N`, followed by an orthonormal basis of the
vertical space `ker (df_x)`, form an orthonormal family. -/
theorem orthonormal_sumElim_horizontalLift (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) :
    Orthonormal ℝ (Sum.elim (fun i ↦ h.horizontalLift x (b i))
      fun a ↦ (c a : TangentSpace I x)) := by
  classical
  rw [orthonormal_iff_ite]
  rintro (i | a) (j | a')
  · rw [Sum.elim_inl, Sum.elim_inl, LinearIsometry.inner_map_map,
      orthonormal_iff_ite.mp b.orthonormal i j]
    simp
  · rw [Sum.elim_inl, Sum.elim_inr, Submodule.inner_left_of_mem_orthogonal (c a').property
      (h.horizontalLift_mem_orthogonal_ker x (b i))]
    simp
  · rw [Sum.elim_inr, Sum.elim_inl, Submodule.inner_right_of_mem_orthogonal (c a).property
      (h.horizontalLift_mem_orthogonal_ker x (b j))]
    simp
  · rw [Sum.elim_inr, Sum.elim_inr, ← Submodule.coe_inner,
      orthonormal_iff_ite.mp c.orthonormal a a']
    simp

/-- A tangent vector orthogonal to the horizontal lifts of an orthonormal basis of `T_(f x) N` and
to an orthonormal basis of `ker (df_x)` is zero. -/
theorem eq_zero_of_forall_inner_horizontalLift_eq_zero (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) {w : TangentSpace I x}
    (hb : ∀ i, ⟪h.horizontalLift x (b i), w⟫_ℝ = 0)
    (hc : ∀ a, ⟪(c a : TangentSpace I x), w⟫_ℝ = 0) :
    w = 0 := by
  have hdw : mfderiv I J f x w = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, ← b.sum_sq_inner_right]
    simp [← h.inner_horizontalLift_left, hb]
  rw [← norm_eq_zero, ← sq_eq_zero_iff]
  calc ‖w‖ ^ 2 = ‖(⟨w, hdw⟩ : (mfderiv I J f x).ker)‖ ^ 2 := rfl
    _ = ∑ a, ⟪c a, (⟨w, hdw⟩ : (mfderiv I J f x).ker)⟫_ℝ ^ 2 := (c.sum_sq_inner_right _).symm
    _ = 0 := Finset.sum_eq_zero fun a _ ↦ by rw [Submodule.coe_inner, hc a, sq, mul_zero]

/-- The orthonormal basis of `T_x M` adapted to the splitting into horizontal and vertical spaces:
horizontal lifts of an orthonormal basis `b` of `T_(f x) N`, followed by an orthonormal basis `c` of
the vertical space `ker (df_x)`. -/
def horizontalVerticalBasis (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) :
    OrthonormalBasis (ι ⊕ κ) ℝ (TangentSpace I x) :=
  .mkOfOrthogonalEqBot (h.orthonormal_sumElim_horizontalLift x b c) <| by
    refine (Submodule.eq_bot_iff _).2 fun w hw ↦
      h.eq_zero_of_forall_inner_horizontalLift_eq_zero x b c (fun i ↦ ?_) fun a ↦ ?_
    · exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self (Sum.inl i))) hw
    · exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self (Sum.inr a))) hw

/-- The first block of the adapted basis consists of the horizontal lifts. -/
@[simp]
theorem horizontalVerticalBasis_inl (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) (i : ι) :
    h.horizontalVerticalBasis x b c (.inl i) = h.horizontalLift x (b i) := by
  simp [horizontalVerticalBasis]

/-- The second block of the adapted basis is the vertical basis. -/
@[simp]
theorem horizontalVerticalBasis_inr (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) (a : κ) :
    h.horizontalVerticalBasis x b c (.inr a) = c a := by
  simp [horizontalVerticalBasis]

/-- For a horizontal vector `w`, the squared coefficients of `w` on the horizontal lifts of an
orthonormal basis of `T_(f x) N` add up to `‖w‖²`. -/
theorem sum_sq_inner_horizontalLift {x : M} (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    {w : TangentSpace I x} (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    ∑ i, ⟪h.horizontalLift x (b i), w⟫_ℝ ^ 2 = ‖w‖ ^ 2 := by
  simp_rw [h.inner_horizontalLift_left, b.sum_sq_inner_right, (h.norm_mfderiv_eq_iff x w).2 hw]

end Basis

/-! ### The squared norm of O'Neill's horizontal tensor -/

section NormSq

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
      ∑ i, ∑ j, ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j))‖ ^ 2 :=
  LinearMap.sum_sum_norm_apply_apply_sq_eq_sum_sum_norm_apply_apply_sq
    ((h.oneillA x).toLinearMap₁₂.compl₁₂ (h.horizontalLift x).toLinearMap
      (h.horizontalLift x).toLinearMap) _ b

omit [IsManifold J ∞ N] [IsContMDiffRiemannianBundle J ∞ F fun y : N ↦ TangentSpace J y] in
/-- `|A|²` is nonnegative. -/
theorem oneillANormSq_nonneg (x : M) : 0 ≤ h.oneillANormSq x := by
  unfold oneillANormSq
  positivity

/-- `|A|²` vanishes at `x` exactly when O'Neill's horizontal tensor vanishes at `x`. -/
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

end NormSq

/-! ### The scalar-curvature formula -/

section Scalar

variable [T2Space M] [T2Space N] {x : M}

/-- **O'Neill's scalar-curvature formula for totally geodesic fibres.** If the vertical tensor `T`
vanishes near `x`, then for any orthonormal basis `V_a` of the vertical space `ker (df_x)`,
`Scal_M(x) = Scal_N(f x) + ∑ a b, Rm_M(V_b, V_a, V_a, V_b) - |A|²`. The middle term is the trace
of the curvature of `M` over the vertical space. -/
theorem scalarCurvature_eq_of_eventually_oneillT_eq_zero (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0)
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).scalarCurvature x =
      (leviCivitaConnection J N).scalarCurvature (f x) +
        (∑ a, ∑ a', (leviCivitaConnection I M).riemannCurvatureTensor x
          (c a') (c a) (c a) (c a')) - h.oneillANormSq x := by
  set b := stdOrthonormalBasis ℝ (TangentSpace J (f x))
  -- Each mixed term is `‖A_(X_i) V_a‖²`, whichever slot pair holds the horizontal vector.
  have hmixed (i) (a : κ) : (leviCivitaConnection I M).riemannCurvatureTensor x
      (h.horizontalLift x (b i)) (c a) (c a) (h.horizontalLift x (b i)) =
      ‖h.oneillA x (h.horizontalLift x (b i)) (c a)‖ ^ 2 := by
    rw [riemannCurvatureTensor_apply]
    exact h.inner_curvatureTensor_horizontal_vertical_self_of_eventually_oneillT_eq_zero hT
      (h.horizontalLift_mem_orthogonal_ker x (b i)) (c a).property
  have hmixed' (i) (a : κ) : (leviCivitaConnection I M).riemannCurvatureTensor x
      (c a) (h.horizontalLift x (b i)) (h.horizontalLift x (b i)) (c a) =
      ‖h.oneillA x (h.horizontalLift x (b i)) (c a)‖ ^ 2 := by
    rw [← hmixed, IsMetricCompatible.riemannCurvatureTensor_swap_pairs _
      (isMetricCompatible_leviCivitaConnection I) (torsion_leviCivitaConnection_eq_zero I)]
  have hA := h.sum_sum_norm_oneillA_horizontalLift_vertical b c
  have hA' : ∑ a, ∑ i, ‖h.oneillA x (h.horizontalLift x (b i)) (c a)‖ ^ 2 =
      h.oneillANormSq x := by
    rw [Finset.sum_comm]
    exact hA
  have hhor := h.scalarCurvature_eq_sum_horizontalLift b
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun j i ↦ ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j))‖ ^ 2),
    ← h.oneillANormSq_eq_sum x b] at hhor
  rw [(leviCivitaConnection I M).scalarCurvature_eq_sum_riemannCurvatureTensor x
    (h.horizontalVerticalBasis x b c)]
  simp only [Fintype.sum_sum_type, horizontalVerticalBasis_inl, horizontalVerticalBasis_inr,
    Finset.sum_add_distrib, hmixed, hmixed']
  linarith

end Scalar

end TauCeti.IsRiemannianSubmersion
