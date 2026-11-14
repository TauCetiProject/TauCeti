/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Analysis.InnerProductSpace.LinearCombination

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
    (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜) : S.range ≃ₗᵢ[𝕜] T.range :=
  (S.quotKerEquivRange.symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (ker_eq_of_inner_self_eq fun x => h x x) ≪≫ₗ
      T.quotKerEquivRange).isometryOfInner <| by
    rintro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hy
    simpa using (h x y).symm

/-- The range isometry sends each image under the first map to the corresponding image
under the second map. -/
@[simp]
theorem rangeEquivOfInnerEq_apply {S : M →ₗ[𝕜] E} {T : M →ₗ[𝕜] F}
    (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜) (x : M) :
    rangeEquivOfInnerEq h ⟨S x, LinearMap.mem_range_self S x⟩ =
      ⟨T x, LinearMap.mem_range_self T x⟩ :=
  Subtype.ext <| by simp [rangeEquivOfInnerEq]

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
      (T := Finsupp.linearCombination 𝕜 w)
        fun a b => Finsupp.inner_linearCombination_eq_of_inner_eq a b h).trans
      (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination (v := w) 𝕜)))

/-- The canonical span isometry sends corresponding family vectors to each other. -/
@[simp]
theorem spanEquivOfInnerEq_apply {v : ι → E} {w : ι → F}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) (i : ι) :
    spanEquivOfInnerEq h ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ =
      ⟨w i, Submodule.subset_span (Set.mem_range_self i)⟩ := by
  apply Subtype.ext
  simp only [spanEquivOfInnerEq, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.coe_ofEq_apply]
  convert congrArg Subtype.val (rangeEquivOfInnerEq_apply
    (fun a b => Finsupp.inner_linearCombination_eq_of_inner_eq a b h) (Finsupp.single i 1))
    using 2 <;> simp [Subtype.ext_iff]

/-- The canonical span isometry is the unique linear isometric equivalence sending the
first family to the second. -/
theorem eq_spanEquivOfInnerEq {v : ι → E} {w : ι → F}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜)
    {e : Submodule.span 𝕜 (Set.range v) ≃ₗᵢ[𝕜] Submodule.span 𝕜 (Set.range w)}
    (he : ∀ i, (e ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ : F) = w i) :
    e = spanEquivOfInnerEq h := by
  have hv := (Submodule.span_range_subtype_eq_top_iff _
    fun i => Submodule.subset_span (R := 𝕜) (Set.mem_range_self (f := v) i)).mpr rfl
  refine LinearIsometryEquiv.toLinearEquiv_injective <| LinearEquiv.toLinearMap_injective <|
    LinearMap.ext_on_range hv fun i => Subtype.ext ?_
  simpa using he i

/-- Equal Gram data for two families in a finite-dimensional space can be realized by an
ambient linear isometric equivalence. The indexing type need not be finite. -/
theorem exists_linearIsometryEquiv_of_inner_eq [FiniteDimensional 𝕜 E] {v w : ι → E}
    (h : ∀ i j, ⟪v i, v j⟫_𝕜 = ⟪w i, w j⟫_𝕜) :
    ∃ e : E ≃ₗᵢ[𝕜] E, ∀ i, e (v i) = w i := by
  let L :=
    (Submodule.span 𝕜 (Set.range w)).subtypeₗᵢ.comp (spanEquivOfInnerEq h).toLinearIsometry
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun i => ?_⟩
  simpa [L] using L.extend_apply ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩

/-- Equal Gram matrices characterize ambient isometric equivalence of families in a
finite-dimensional real or complex inner-product space. The index type may be infinite. -/
theorem gram_eq_iff_exists_linearIsometryEquiv [FiniteDimensional 𝕜 E]
    {v w : ι → E} : Matrix.gram 𝕜 v = Matrix.gram 𝕜 w ↔
      ∃ e : E ≃ₗᵢ[𝕜] E, ∀ i, e (v i) = w i := by
  refine ⟨fun h => exists_linearIsometryEquiv_of_inner_eq fun i j => by
    simpa [Matrix.gram_apply] using congrFun₂ h i j, ?_⟩
  rintro ⟨e, he⟩
  ext i j
  simp [Matrix.gram_apply, ← he]

end TauCeti
