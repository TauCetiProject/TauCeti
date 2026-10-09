/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Gram rigidity

Equal pullback inner products determine a canonical linear isometric equivalence between the
ranges of two linear maps. Applied to the finitely supported linear-combination maps of two
families, this gives an isometry between their spans sending corresponding vectors to each
other. No independence, finiteness of the index type, or completeness is needed.

For families in a common finite-dimensional inner-product space, the span isometry extends
to an ambient isometry. Thus equality of Gram matrices characterizes equivalence under an
ambient linear isometric equivalence, including dependent families and zero vectors.

The range construction uses Mathlib's `LinearMap.quotKerEquivRange`; the ambient extension
uses `LinearIsometry.extend`. The mathematical result is the usual Gram characterization of
unitary equivalence, as in T.-Y. Chien and S. Waldron, *A characterization of projective unitary
equivalence of finite frames and applications*, SIAM J. Discrete Math. 30 (2016).
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 M E F ι : Type*} [RCLike 𝕜]
  [AddCommGroup M] [Module 𝕜 M]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Linear maps with equal self inner products have equal kernels. The common source
need only be a module. -/
theorem ker_eq_of_inner_self_eq {S : M →ₗ[𝕜] E} {T : M →ₗ[𝕜] F}
    (h : ∀ x, ⟪S x, S x⟫_𝕜 = ⟪T x, T x⟫_𝕜) : S.ker = T.ker := by
  ext x
  have hzero : ⟪S x, S x⟫_𝕜 = 0 ↔ ⟪T x, T x⟫_𝕜 = 0 := by rw [h x]
  simpa only [LinearMap.mem_ker, inner_self_eq_zero] using hzero

/-- The canonical range isometry induced by equal pullback inner products, sending `S x`
to `T x`. -/
def rangeEquivOfInnerEq {S : M →ₗ[𝕜] E} {T : M →ₗ[𝕜] F}
    (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜) : S.range ≃ₗᵢ[𝕜] T.range := by
  let e := S.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_eq_of_inner_self_eq fun x => h x x)).trans
      T.quotKerEquivRange)
  have he (x : M) : e ⟨S x, LinearMap.mem_range_self S x⟩ =
      ⟨T x, LinearMap.mem_range_self T x⟩ := by
    apply Subtype.ext
    simp only [e, LinearEquiv.trans_apply, LinearMap.quotKerEquivRange_symm_apply_image,
      Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk]
  exact e.isometryOfInner fun x y => by
    obtain ⟨_, x, rfl⟩ := x
    obtain ⟨_, y, rfl⟩ := y
    simpa only [he, Submodule.coe_inner] using (h x y).symm

/-- The range isometry sends each image under the first map to the corresponding image
under the second map. -/
@[simp]
theorem rangeEquivOfInnerEq_apply {S : M →ₗ[𝕜] E} {T : M →ₗ[𝕜] F}
    (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜) (x : M) :
    rangeEquivOfInnerEq h ⟨S x, LinearMap.mem_range_self S x⟩ =
      ⟨T x, LinearMap.mem_range_self T x⟩ := by
  apply Subtype.ext
  simp only [rangeEquivOfInnerEq, LinearEquiv.coe_isometryOfInner, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk]

/-- A range isometry is uniquely determined by its values on the images of the common
source. -/
theorem eq_rangeEquivOfInnerEq {S : M →ₗ[𝕜] E} {T : M →ₗ[𝕜] F}
    (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜) {e : S.range ≃ₗᵢ[𝕜] T.range}
    (he : ∀ x, (e ⟨S x, LinearMap.mem_range_self S x⟩ : F) = T x) :
    e = rangeEquivOfInnerEq h := by
  ext ⟨_, x, rfl⟩
  simpa using he x

/-- Families with equal pairwise inner products have canonically isometric spans. The
isometry sends each vector of the first family to its partner in the second. -/
def spanEquivOfInnerEq {v : ι → E} {w : ι → F}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    Submodule.span 𝕜 (Set.range v) ≃ₗᵢ[𝕜] Submodule.span 𝕜 (Set.range w) :=
  (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination (v := v) 𝕜).symm).trans
    ((rangeEquivOfInnerEq (S := Finsupp.linearCombination 𝕜 v)
      (T := Finsupp.linearCombination 𝕜 w) fun a b => by
        simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
          inner_smul_left, inner_smul_right, h]).trans
      (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination (v := w) 𝕜)))

/-- The canonical span isometry sends corresponding family vectors to each other. -/
@[simp]
theorem spanEquivOfInnerEq_apply {v : ι → E} {w : ι → F}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) (i : ι) :
    spanEquivOfInnerEq h ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ =
      ⟨w i, Submodule.subset_span (Set.mem_range_self i)⟩ := by
  classical
  apply Subtype.ext
  rw [spanEquivOfInnerEq, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_ofEq_apply]
  have hcast :
      LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination (v := v) 𝕜).symm
        ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ =
      ⟨Finsupp.linearCombination 𝕜 v (Finsupp.single i 1),
        LinearMap.mem_range_self _ _⟩ := by
    apply Subtype.ext
    simp only [LinearIsometryEquiv.coe_ofEq_apply, Finsupp.linearCombination_single, one_smul]
  rw [hcast, rangeEquivOfInnerEq_apply]
  simp

/-- The canonical span isometry is the unique linear isometric equivalence sending the
first family to the second. -/
theorem eq_spanEquivOfInnerEq {v : ι → E} {w : ι → F}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜)
    {e : Submodule.span 𝕜 (Set.range v) ≃ₗᵢ[𝕜] Submodule.span 𝕜 (Set.range w)}
    (he : ∀ i, (e ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ : F) = w i) :
    e = spanEquivOfInnerEq h := by
  have hv : Submodule.span 𝕜 (Set.range fun i =>
      (⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :
        Submodule.span 𝕜 (Set.range v))) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff _ _).mpr rfl
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range hv
  intro i
  apply Subtype.ext
  simpa only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    spanEquivOfInnerEq_apply, Subtype.coe_mk] using he i

/-- Equal Gram data for two families in a finite-dimensional space can be realized by an
ambient linear isometric equivalence. The indexing type need not be finite. -/
theorem exists_linearIsometryEquiv_of_inner_eq [FiniteDimensional 𝕜 E] {v w : ι → E}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    ∃ e : E ≃ₗᵢ[𝕜] E, ∀ i, e (v i) = w i := by
  let L : Submodule.span 𝕜 (Set.range v) →ₗᵢ[𝕜] E :=
    (Submodule.span 𝕜 (Set.range w)).subtypeₗᵢ.comp
    (spanEquivOfInnerEq h).toLinearIsometry
  let U : E →ₗᵢ[𝕜] E := LinearIsometry.extend L
  refine ⟨U.toLinearIsometryEquiv rfl, fun i => ?_⟩
  have he := LinearIsometry.extend_apply L
    ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  simpa [U, L] using he

/-- Equal Gram matrices characterize ambient isometric equivalence of families in a
finite-dimensional real or complex inner-product space. The index type may be infinite. -/
theorem gram_eq_iff_exists_linearIsometryEquiv [FiniteDimensional 𝕜 E]
    {v w : ι → E} : Matrix.gram 𝕜 v = Matrix.gram 𝕜 w ↔
      ∃ e : E ≃ₗᵢ[𝕜] E, ∀ i, e (v i) = w i := by
  constructor
  · intro h
    exact exists_linearIsometryEquiv_of_inner_eq fun i j => congrArg (fun A => A i j) h
  · rintro ⟨e, he⟩
    ext i j
    simpa only [Matrix.gram_apply, ← he] using (e.inner_map_map (v i) (v j)).symm

end TauCeti
