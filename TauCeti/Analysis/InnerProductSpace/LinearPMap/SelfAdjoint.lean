/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Deficiency shifts of self-adjoint partial linear maps

For a self-adjoint partial linear map `A` on a complex Hilbert space and a unimodular purely
imaginary scalar `c` (so `c = ± i`), the shift `x ↦ c • x - A x` is an isometric embedding of the
graph norm: `‖c • x - A x‖² = ‖x‖² + ‖A x‖²`.  Its range is therefore closed; it is also dense,
because a vector orthogonal to it is an eigenvector of `A` for the eigenvalue `conj c`, which is
impossible for a self-adjoint operator.  Hence both deficiency shifts are surjective
(`IsSelfAdjoint.surjective_smul_sub`), the range condition that makes `± i • A` m-dissipative.

The development is carried out once for a scalar `c` with `c.re = 0` and `‖c‖ = 1`; the two
signs `± i` are instances.
-/

public section

noncomputable section

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A self-adjoint partial linear map is formally self-adjoint on its domain. -/
theorem _root_.IsSelfAdjoint.isFormalAdjoint [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) : A.IsFormalAdjoint A := by
  have h := adjoint_isFormalAdjoint hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h

/-- The quadratic form of a self-adjoint partial linear map is real. -/
theorem _root_.IsSelfAdjoint.im_inner_apply_eq_zero [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) (x : A.domain) : (inner ℂ (x : E) (A x)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  calc
    (starRingEnd ℂ) (inner ℂ (x : E) (A x)) = inner ℂ (A x) (x : E) :=
      inner_conj_symm (A x) (x : E)
    _ = inner ℂ (x : E) (A x) := hA.isFormalAdjoint x x

/-- For a self-adjoint partial linear map and a purely imaginary scalar `c`, the real cross term
between `c • x` and `A x` vanishes.  The complex inner product is conjugate-linear in its first
argument. -/
theorem _root_.IsSelfAdjoint.re_inner_smul_apply_eq_zero [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (x : A.domain) :
    (inner ℂ (c • (x : E)) (A x)).re = 0 := by
  rw [inner_smul_left, Complex.mul_re, Complex.conj_re, Complex.conj_im, hc,
    hA.im_inner_apply_eq_zero x]
  ring

/-- **Graph-norm identity for deficiency shifts.** For a self-adjoint partial linear map and a
unimodular purely imaginary scalar `c`, `‖c • x - A x‖² = ‖x‖² + ‖A x‖²`. -/
theorem _root_.IsSelfAdjoint.norm_smul_sub_sq [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ = 1) (x : A.domain) :
    ‖c • (x : E) - A x‖ ^ 2 = ‖x‖ ^ 2 + ‖A x‖ ^ 2 := by
  have hcross : RCLike.re (inner ℂ (c • (x : E)) (A x)) = 0 := by
    simpa using hA.re_inner_smul_apply_eq_zero hc x
  rw [@norm_sub_sq ℂ, hcross, norm_smul, hc1, one_mul]
  simp only [mul_zero, sub_zero]
  rfl

/-- A deficiency shift of a self-adjoint partial linear map is bounded below by the norm of its
input. -/
theorem _root_.IsSelfAdjoint.norm_le_norm_smul_sub [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ = 1) (x : A.domain) :
    ‖x‖ ≤ ‖c • (x : E) - A x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hA.norm_smul_sub_sq hc hc1]
  exact le_add_of_nonneg_right (sq_nonneg _)

private def graphShift (A : E →ₗ.[ℂ] E) (c : ℂ) : A.graph →L[ℂ] E :=
  ((c • ContinuousLinearMap.fst ℂ E E) -
    ContinuousLinearMap.snd ℂ E E).domRestrict A.graph

private lemma graphShift_apply (A : E →ₗ.[ℂ] E) (c : ℂ) (z : A.graph) :
    graphShift A c z = c • (z : E × E).1 - (z : E × E).2 := rfl

private lemma norm_graph_le_graphShift {A : E →ₗ.[ℂ] E} (c : ℂ)
    (hbound : ∀ x : A.domain, max ‖x‖ ‖A x‖ ≤ ‖c • (x : E) - A x‖) :
    ∀ z : A.graph, ‖(z : E × E)‖ ≤ ‖graphShift A c z‖ := by
  intro z
  obtain ⟨u, hu1, hu2⟩ := A.mem_graph_iff.mp z.property
  rw [Prod.norm_def]
  calc
    max ‖(z : E × E).1‖ ‖(z : E × E).2‖ = max ‖u‖ ‖A u‖ := by
      rw [← hu1, ← hu2, Submodule.norm_coe]
    _ ≤ ‖c • (u : E) - A u‖ := hbound u
    _ = ‖graphShift A c z‖ := by rw [graphShift_apply, ← hu1, ← hu2]

private lemma graphShift_antilipschitz {A : E →ₗ.[ℂ] E} (c : ℂ)
    (hbound : ∀ x : A.domain, max ‖x‖ ‖A x‖ ≤ ‖c • (x : E) - A x‖) :
    AntilipschitzWith 1 (graphShift A c) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rw [dist_eq_norm, dist_eq_norm, ← (graphShift A c).map_sub]
  exact norm_graph_le_graphShift c hbound (x - y)

private lemma range_graphShift (A : E →ₗ.[ℂ] E) (c : ℂ) :
    Set.range (graphShift A c) = Set.range (fun x : A.domain => c • (x : E) - A x) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hx1, hx2⟩ := A.mem_graph_iff.mp z.property
    exact ⟨x, by simp [graphShift, hx1, hx2]⟩
  · rintro ⟨x, rfl⟩
    let z : A.graph := ⟨((x : E), A x), A.mem_graph_iff.mpr ⟨x, rfl, rfl⟩⟩
    exact ⟨z, rfl⟩

/-- The range of a deficiency shift of a self-adjoint partial linear map is closed: the shift is
an isometry for the graph norm, and the graph is complete. -/
theorem _root_.IsSelfAdjoint.isClosed_range_smul_sub [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ = 1) :
    _root_.IsClosed (Set.range (fun x : A.domain => c • (x : E) - A x)) := by
  let _ : CompleteSpace A.graph := hA.isClosed.completeSpace_coe
  have hbound : ∀ x : A.domain, max ‖x‖ ‖A x‖ ≤ ‖c • (x : E) - A x‖ := by
    intro x
    apply max_le
    · exact hA.norm_le_norm_smul_sub hc hc1 x
    · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [hA.norm_smul_sub_sq hc hc1]
      exact le_add_of_nonneg_left (sq_nonneg _)
  rw [← range_graphShift A c]
  exact (graphShift_antilipschitz c hbound).isClosed_range (graphShift A c).uniformContinuous

/-- A vector orthogonal to the range of the shift `c • x - A x` pairs with `A` like the
eigenvalue `conj c`. -/
private lemma adjoint_pair_of_orthogonal_shift {A : E →ₗ.[ℂ] E} (c : ℂ) (y : E)
    (h : ∀ x : A.domain, inner ℂ y (c • (x : E) - A x) = 0) :
    ∀ x : A.domain, inner ℂ ((starRingEnd ℂ) c • y) x = inner ℂ y (A x) := by
  intro x
  have hx := h x
  rw [inner_sub_right, sub_eq_zero] at hx
  rw [inner_smul_left, Complex.conj_conj, ← hx, inner_smul_right]

/-- A self-adjoint partial linear map has no eigenvector for a nonreal unimodular eigenvalue. -/
private lemma eq_zero_of_adjoint_pair [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ = 1) (y : E)
    (hpair : ∀ x : A.domain, inner ℂ (c • y) x = inner ℂ y (A x)) : y = 0 := by
  have hyadj : y ∈ A†.domain := mem_adjoint_domain_of_exists y ⟨c • y, hpair⟩
  have hle : A† ≤ A := le_of_eq (LinearPMap.isSelfAdjoint_def.mp hA)
  let yA : A.domain := ⟨y, hle.1 hyadj⟩
  have hAy : A yA = c • y :=
    hA.dense_domain.eq_of_inner_left ℂ fun x hx =>
      (hA.isFormalAdjoint yA ⟨x, hx⟩).trans (hpair ⟨x, hx⟩).symm
  have hnorm := hA.norm_le_norm_smul_sub hc hc1 yA
  rw [hAy, sub_self, norm_zero] at hnorm
  have hyA0 : yA = 0 := norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  exact congrArg Subtype.val hyA0

/-- The range of a deficiency shift of a self-adjoint partial linear map is dense. -/
theorem _root_.IsSelfAdjoint.dense_range_smul_sub [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ = 1) :
    Dense (Set.range (fun x : A.domain => c • (x : E) - A x)) := by
  let T : A.domain →ₗ[ℂ] E := c • A.domain.subtype - A.toFun
  change Dense (T.range : Set E)
  refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  ext y
  rw [Submodule.mem_bot]
  constructor
  · intro hy
    have hortho : ∀ x : A.domain, inner ℂ y (c • (x : E) - A x) = 0 := fun x =>
      (Submodule.mem_orthogonal' T.range y).mp hy (T x) ⟨x, rfl⟩
    have hc' : ((starRingEnd ℂ) c).re = 0 := by rw [Complex.conj_re]; exact hc
    have hc1' : ‖(starRingEnd ℂ) c‖ = 1 := by rw [Complex.norm_conj]; exact hc1
    exact eq_zero_of_adjoint_pair hA hc' hc1' y (adjoint_pair_of_orthogonal_shift c y hortho)
  · rintro rfl
    exact Submodule.zero_mem _

/-- **Both deficiency shifts of a self-adjoint partial linear map are surjective**: their ranges
are closed and dense. -/
theorem _root_.IsSelfAdjoint.surjective_smul_sub [CompleteSpace E] {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ = 1) :
    Function.Surjective (fun x : A.domain => c • (x : E) - A x) := by
  intro y
  have hrange : Set.range (fun x : A.domain => c • (x : E) - A x) = Set.univ := by
    rw [← (hA.isClosed_range_smul_sub hc hc1).closure_eq,
      (hA.dense_range_smul_sub hc hc1).closure_eq]
  rw [← Set.mem_range, hrange]
  exact Set.mem_univ y

end LinearPMap

end
