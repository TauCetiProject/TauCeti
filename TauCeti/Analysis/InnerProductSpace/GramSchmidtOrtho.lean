/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family

/-!
# The Gram-Schmidt process: coefficients, regularity, and projections

Mathlib's `InnerProductSpace.gramSchmidt_triangular` records that, in the basis `b` it is fed,
`gramSchmidt 𝕜 b i` has no component along `b j` for `i < j`.  This file supplies the diagonal
companion: the component along `b i` itself is `1`, because the Gram-Schmidt step subtracts from
`b i` only vectors spanned by the earlier basis vectors.  Together the two say that the matrix of
the Gram-Schmidt process is lower unitriangular.

The file also proves that the Gram-Schmidt process, normalized or not, depends continuously on its
input at every linearly independent family. Only an initial segment of the input has to be
linearly independent: for the `n`-th Gram-Schmidt vector, the inputs strictly before `n`; for the
`n`-th normalized one, the inputs up to and including `n`, as in Mathlib's
`InnerProductSpace.gramSchmidt_ne_zero_coe`. Likewise only the inputs up to and including `n`
have to vary continuously, since the `n`-th vector does not depend on later inputs. This
independence keeps every denominator `‖gramSchmidt 𝕜 f i‖ ^ 2`, `i < n`, of the recursive formula
`gramSchmidt_def''` away from zero, so continuity follows by well-founded induction on the index.
This is what makes orthonormalization a continuous retraction of linearly independent frames onto
orthonormal ones.
The induction is the fixed-space form of the sectionwise argument of Patrick Massot and Michael
Rothgang in Mathlib PR [#26221](https://github.com/leanprover-community/mathlib4/pull/26221), which
`ContinuousWithinAt.gramSchmidt_bundle` adapts to continuous Riemannian vector bundles.

The same recursion preserves real smoothness under the same hypotheses: the norm
is smooth away from zero, and each denominator stays nonzero. This also applies to complex
inner-product spaces, with smoothness taken over `ℝ`.

Projection onto the span of a finite family is the sum of the rank-one operators of its
normalized Gram-Schmidt vectors, including any zero vectors. This gives a formula that
continues to hold when the input family loses rank.

## Main results

* `Module.Basis.repr_gramSchmidt_self_eq_one` — the Gram-Schmidt process leaves the coefficient of a
  basis vector along itself equal to `1`.
* `InnerProductSpace.gramSchmidt_eq_self_of_inner_eq_zero`,
  `InnerProductSpace.gramSchmidtNormed_eq_self_of_inner_eq_zero` — the process fixes an input
  (unit) vector orthogonal to all earlier inputs, so it fixes an orthonormal initial segment.
* `ContinuousWithinAt.gramSchmidt`, `ContinuousWithinAt.gramSchmidtNormed` — Gram-Schmidt applied to
  a family of vectors depending continuously on a parameter, up to the index, is continuous at
  every parameter where the relevant initial segment of the family is linearly independent, with
  `ContinuousAt`, `ContinuousOn` and `Continuous` variants for the normalized process.
* `InnerProductSpace.inner_gramSchmidt_eq_norm_sq`,
  `InnerProductSpace.inner_gramSchmidtNormed_eq_norm` — pairing the residual or normalized
  vector with its original input gives its squared norm or its residual norm.
* `ContDiffWithinAt.gramSchmidt`, `ContDiffWithinAt.gramSchmidtNormed` — the corresponding real
  smoothness statements, with at-point, on-set and global versions for the normalized process.
-/

public section

open Finset InnerProductSpace Module Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- The Gram-Schmidt process does not change the coefficient of a basis vector along itself:
`gramSchmidt 𝕜 b i` differs from `b i` by a combination of the strictly earlier `gramSchmidt`
vectors, each of which has no component along `b i`. -/
@[simp]
theorem _root_.Module.Basis.repr_gramSchmidt_self_eq_one (b : Basis ι 𝕜 E) (i : ι) :
    b.repr (gramSchmidt 𝕜 b i) i = 1 := by
  have h := congrArg (fun x ↦ b.repr x i) (gramSchmidt_def'' 𝕜 (b : ι → E) i)
  simp only [Basis.repr_self, Finsupp.single_eq_same, map_add, map_sum, map_smul,
    Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at h
  rw [Finset.sum_eq_zero (fun j hj ↦ ?_), add_zero] at h
  · exact h.symm
  · rw [gramSchmidt_triangular (Finset.mem_Iio.mp hj) b, mul_zero]

end TauCeti

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

attribute [local instance] IsWellOrder.toHasWellFounded

/-- The Gram–Schmidt residual paired with its original input has squared norm. -/
@[simp]
theorem inner_gramSchmidt_eq_norm_sq (f : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidt 𝕜 f j) (f j) = (‖gramSchmidt 𝕜 f j‖ : 𝕜) ^ 2 := by
  have h := congrArg (fun w ↦ inner 𝕜 (gramSchmidt 𝕜 f j) w) (gramSchmidt_def'' 𝕜 f j)
  simp only [inner_add_right, inner_sum, inner_smul_right] at h
  rw [Finset.sum_eq_zero (fun i hi ↦ ?_), add_zero] at h
  · simpa only [inner_self_eq_norm_sq_to_K] using h
  · rw [gramSchmidt_orthogonal 𝕜 f (ne_of_gt (Finset.mem_Iio.mp hi)), mul_zero]

/-- The normalized Gram–Schmidt vector paired with its original input has residual norm. -/
@[simp]
theorem inner_gramSchmidtNormed_eq_norm (f : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f j) (f j) = (‖gramSchmidt 𝕜 f j‖ : 𝕜) := by
  by_cases h : gramSchmidt 𝕜 f j = 0
  · simp [gramSchmidtNormed, h]
  · simp [gramSchmidtNormed, inner_smul_left, h, sq]

/-- The Gram–Schmidt process fixes an input vector orthogonal to all earlier inputs. This is the
pointwise form of Mathlib's `InnerProductSpace.gramSchmidt_of_orthogonal`: every earlier
Gram–Schmidt vector lies in the span of earlier inputs, so its projection of `f i` vanishes. -/
theorem gramSchmidt_eq_self_of_inner_eq_zero {f : ι → E} {i : ι}
    (hf : ∀ j < i, inner 𝕜 (f j) (f i) = 0) : gramSchmidt 𝕜 f i = f i := by
  rw [gramSchmidt_def, sub_eq_self]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
  suffices Submodule.span 𝕜 (f '' Set.Iic j) ⟂ Submodule.span 𝕜 {f i} by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.2
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left,
      ← Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact this (gramSchmidt_mem_span 𝕜 f (le_refl j))
  rw [Submodule.isOrtho_span]
  rintro u ⟨k, hk, rfl⟩ v (rfl : v = f i)
  exact hf k (lt_of_le_of_lt hk (Finset.mem_Iio.mp hj))

/-- The normalized Gram–Schmidt process fixes an input unit vector orthogonal to all earlier
inputs. -/
theorem gramSchmidtNormed_eq_self_of_inner_eq_zero {f : ι → E} {i : ι}
    (hf : ∀ j < i, inner 𝕜 (f j) (f i) = 0) (hi : ‖f i‖ = 1) : gramSchmidtNormed 𝕜 f i = f i := by
  simp [gramSchmidtNormed, gramSchmidt_eq_self_of_inner_eq_zero hf, hi]

end InnerProductSpace

section Continuity

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
variable {X : Type*} [TopologicalSpace X] {v : ι → X → E} {s : Set X} {x : X}

attribute [local instance] IsWellOrder.toHasWellFounded

/-- The Gram-Schmidt process is continuous at every parameter where the input vectors up to and
including the index are continuous and those strictly before the index are linearly independent.
The input vector at the index itself may lie in their span. -/
theorem ContinuousWithinAt.gramSchmidt (n : ι) (hv : ∀ i ≤ n, ContinuousWithinAt (v i) s x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iio n)) :
    ContinuousWithinAt (fun y ↦ InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i y) n) s x := by
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    -- Unfold one step of the recursion `gramSchmidt_def''`.
    have hformula (y : X) : InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i y) n =
        v n y - ∑ i ∈ Iio n,
          (⟪InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j y) i, v n y⟫_𝕜 /
            (‖InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j y) i‖ : 𝕜) ^ 2) •
              InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j y) i :=
      eq_sub_of_add_eq (InnerProductSpace.gramSchmidt_def'' 𝕜 (fun i ↦ v i y) n).symm
    simp only [hformula]
    refine (hv n le_rfl).sub <| tendsto_finsetSum _ fun i hi ↦ ?_
    have hi := mem_Iio.mp hi
    have hgi := ih i hi (fun k hk ↦ hv k (hk.trans hi.le)) (hli.mono (Set.Iio_subset_Iio hi.le))
    have hnorm : ContinuousWithinAt
        (fun y ↦ ((‖InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j y) i‖ : ℝ) : 𝕜)) s x :=
      RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt hgi.norm
    exact ((hgi.inner (hv n le_rfl)).div (hnorm.pow 2) (pow_ne_zero 2 <| RCLike.ofReal_ne_zero.2 <|
      norm_ne_zero_iff.2 <| InnerProductSpace.gramSchmidt_ne_zero_coe i
        (hli.mono (Set.Iic_subset_Iio.2 hi)).linearIndependent)).smul hgi

/-- The normalized Gram-Schmidt process is continuous at every parameter where the input vectors
up to and including the index are continuous and linearly independent. -/
theorem ContinuousWithinAt.gramSchmidtNormed (n : ι) (hv : ∀ i ≤ n, ContinuousWithinAt (v i) s x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iic n)) :
    ContinuousWithinAt (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) n) s x := by
  have hg := ContinuousWithinAt.gramSchmidt n hv (hli.mono Set.Iio_subset_Iic_self)
  have hnorm : ContinuousWithinAt
      (fun y ↦ ((‖InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i y) n‖ : ℝ) : 𝕜)) s x :=
    RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt hg.norm
  exact (hnorm.inv₀ <| RCLike.ofReal_ne_zero.2 <| norm_ne_zero_iff.2 <|
    InnerProductSpace.gramSchmidt_ne_zero_coe n hli.linearIndependent).smul hg

/-- The normalized Gram-Schmidt process is continuous at every parameter where the input vectors
up to and including the index are continuous and linearly independent. -/
theorem ContinuousAt.gramSchmidtNormed (n : ι) (hv : ∀ i ≤ n, ContinuousAt (v i) x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iic n)) :
    ContinuousAt (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) n) x := by
  simp only [← continuousWithinAt_univ] at hv ⊢
  exact ContinuousWithinAt.gramSchmidtNormed n hv hli

/-- The normalized Gram-Schmidt process is continuous on a set on which the input vectors up to
and including the index are continuous and, at each point, linearly independent. -/
theorem ContinuousOn.gramSchmidtNormed (n : ι) (hv : ∀ i ≤ n, ContinuousOn (v i) s)
    (hli : ∀ y ∈ s, LinearIndepOn 𝕜 (fun i ↦ v i y) (Set.Iic n)) :
    ContinuousOn (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) n) s :=
  fun y hy ↦ ContinuousWithinAt.gramSchmidtNormed n (fun i hi ↦ hv i hi y hy) (hli y hy)

/-- The normalized Gram-Schmidt process is continuous when the input vectors up to and including
the index are continuous and linearly independent at every parameter. -/
theorem Continuous.gramSchmidtNormed (n : ι) (hv : ∀ i ≤ n, Continuous (v i))
    (hli : ∀ y, LinearIndepOn 𝕜 (fun i ↦ v i y) (Set.Iic n)) :
    Continuous (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) n) := by
  simp only [← continuousOn_univ] at hv ⊢
  exact ContinuousOn.gramSchmidtNormed n hv (fun y _ ↦ hli y)

end Continuity

section Smoothness

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {v : ι → F → E} {s : Set F} {x : F} {n : WithTop ℕ∞}

attribute [local instance] IsWellOrder.toHasWellFounded

private theorem gramSchmidt_norm_smooth
    (i : ι)
    (hg : ContDiffWithinAt ℝ n
      (fun y ↦ InnerProductSpace.gramSchmidt 𝕜 (fun k ↦ v k y) i) s x)
    (hli : LinearIndepOn 𝕜 (fun k ↦ v k x) (Set.Iic i)) :
    ContDiffWithinAt ℝ n
        (fun y ↦ (‖InnerProductSpace.gramSchmidt 𝕜 (fun k ↦ v k y) i‖ : 𝕜)) s x ∧
      (‖InnerProductSpace.gramSchmidt 𝕜 (fun k ↦ v k x) i‖ : 𝕜) ≠ 0 := by
  have hne := gramSchmidt_ne_zero_coe (f := fun k ↦ v k x) i hli.linearIndependent
  exact ⟨(RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.contDiffAt.comp_contDiffWithinAt x
    (hg.norm 𝕜 hne), RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hne)⟩

/-- Gram–Schmidt is real smooth at every parameter where the input vectors up to and including the
index are real smooth and those strictly before the index are linearly independent. The input
vector at the index itself may lie in their span. -/
theorem ContDiffWithinAt.gramSchmidt (j : ι) (hv : ∀ i ≤ j, ContDiffWithinAt ℝ n (v i) s x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iio j)) :
    ContDiffWithinAt ℝ n (fun y ↦ InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i y) j) s x := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hformula (y : F) : InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i y) j =
        v j y - ∑ i ∈ Iio j,
          (⟪InnerProductSpace.gramSchmidt 𝕜 (fun k ↦ v k y) i, v j y⟫_𝕜 /
            (‖InnerProductSpace.gramSchmidt 𝕜 (fun k ↦ v k y) i‖ : 𝕜) ^ 2) •
              InnerProductSpace.gramSchmidt 𝕜 (fun k ↦ v k y) i :=
      eq_sub_of_add_eq (gramSchmidt_def'' 𝕜 (fun i ↦ v i y) j).symm
    simp only [hformula]
    refine (hv j le_rfl).sub <| ContDiffWithinAt.sum fun i hi ↦ ?_
    have hi := mem_Iio.mp hi
    have hgi := ih i hi (fun k hk ↦ hv k (hk.trans hi.le)) (hli.mono (Set.Iio_subset_Iio hi.le))
    obtain ⟨hn, hne⟩ := gramSchmidt_norm_smooth i hgi (hli.mono (Set.Iic_subset_Iio.2 hi))
    have hc := (hgi.inner 𝕜 (hv j le_rfl)).mul ((hn.pow 2).inv (pow_ne_zero 2 hne))
    simpa only [div_eq_mul_inv, Pi.smul_def', Pi.inv_apply] using hc.smul hgi

/-- Normalized Gram–Schmidt is real smooth at every parameter where the input vectors up to and
including the index are real smooth and linearly independent. -/
theorem ContDiffWithinAt.gramSchmidtNormed (j : ι) (hv : ∀ i ≤ j, ContDiffWithinAt ℝ n (v i) s x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iic j)) :
    ContDiffWithinAt ℝ n (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) j) s x := by
  have hg := ContDiffWithinAt.gramSchmidt j hv (hli.mono Set.Iio_subset_Iic_self)
  obtain ⟨hn, hne⟩ := gramSchmidt_norm_smooth j hg hli
  exact (hn.inv hne).smul hg

/-- Normalized Gram–Schmidt is real smooth at every parameter where the input vectors up to and
including the index are real smooth and linearly independent. -/
theorem ContDiffAt.gramSchmidtNormed (j : ι) (hv : ∀ i ≤ j, ContDiffAt ℝ n (v i) x)
    (hli : LinearIndepOn 𝕜 (fun i ↦ v i x) (Set.Iic j)) :
    ContDiffAt ℝ n (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) j) x := by
  simp only [← contDiffWithinAt_univ] at hv ⊢
  exact ContDiffWithinAt.gramSchmidtNormed j hv hli

/-- Normalized Gram–Schmidt is real smooth on a set on which the input vectors up to and including
the index are real smooth and, at each point, linearly independent. -/
theorem ContDiffOn.gramSchmidtNormed (j : ι) (hv : ∀ i ≤ j, ContDiffOn ℝ n (v i) s)
    (hli : ∀ y ∈ s, LinearIndepOn 𝕜 (fun i ↦ v i y) (Set.Iic j)) :
    ContDiffOn ℝ n (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) j) s := by
  intro y hy
  exact ContDiffWithinAt.gramSchmidtNormed j (fun i hi ↦ hv i hi y hy) (hli y hy)

/-- Normalized Gram–Schmidt is real smooth when the input vectors up to and including the index
are real smooth and linearly independent at every parameter. -/
theorem ContDiff.gramSchmidtNormed (j : ι) (hv : ∀ i ≤ j, ContDiff ℝ n (v i))
    (hli : ∀ y, LinearIndepOn 𝕜 (fun i ↦ v i y) (Set.Iic j)) :
    ContDiff ℝ n (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) j) := by
  simp only [← contDiffOn_univ] at hv ⊢
  exact ContDiffOn.gramSchmidtNormed j hv (fun y _ ↦ hli y)

end Smoothness

section Projection

open InnerProductSpace Set

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [Fintype ι]

/-- Projection onto the span of a finite family is the sum of the rank-one operators
associated to its normalized Gram–Schmidt vectors, including the zero vectors. -/
theorem InnerProductSpace.starProjection_eq_sum_rankOne_gramSchmidtNormed (v : ι → E)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Submodule.span 𝕜 (range v) = U) :
    U.starProjection =
      ∑ i, rankOne 𝕜 (gramSchmidtNormed 𝕜 v i) (gramSchmidtNormed 𝕜 v i) := by
  classical
  subst hU
  have hspan : Submodule.span 𝕜
      (range fun i : {i | gramSchmidtNormed 𝕜 v i ≠ 0} ↦ gramSchmidtNormed 𝕜 v i) =
      Submodule.span 𝕜 (range v) := by
    rw [← span_gramSchmidt 𝕜 v, ← span_gramSchmidtNormed_range (𝕜 := 𝕜) v]
    apply le_antisymm
    · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact mem_range_self _)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      by_cases hi : gramSchmidtNormed 𝕜 v i = 0
      · simpa only [SetLike.mem_coe, hi] using (Submodule.zero_mem
          (Submodule.span 𝕜
            (range fun i : {i | gramSchmidtNormed 𝕜 v i ≠ 0} ↦ gramSchmidtNormed 𝕜 v i)))
      · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  ext x
  rw [(gramSchmidtNormed_orthonormal' (𝕜 := 𝕜) v).starProjection_apply_eq_sum hspan]
  simp only [_root_.sum_apply, rankOne_apply]
  simp only [Set.mem_ofPred_eq]
  rw [← Finset.sum_subtype (Finset.univ.filter fun i ↦ gramSchmidtNormed 𝕜 v i ≠ 0)
    (by simp) (fun i ↦ inner 𝕜 (gramSchmidtNormed 𝕜 v i) x • gramSchmidtNormed 𝕜 v i)]
  exact Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi ↦ by
    have hzero : gramSchmidtNormed 𝕜 v i = 0 := by simpa using hi
    simp [hzero]

end Projection
