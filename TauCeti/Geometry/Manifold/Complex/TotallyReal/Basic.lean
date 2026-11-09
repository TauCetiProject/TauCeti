/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic

/-!
# Totally real embeddings

A totally real embedding is a `C^n` embedding of half the ambient dimension whose tangent
images are maximal totally real. The almost complex structure is supplied pointwise, without
any regularity requirement, so the definition applies to finite-regularity as well as smooth
structures.

The dimension condition is explicit even for empty source manifolds. The existing Lagrangian
embedding predicate allows empty sources of any dimension, so its comparison theorem either
assumes half-dimensionality or a nonempty source.

## Main declarations

* `IsTotallyRealEmbedding`: a native `C^n` embedding with maximal totally real tangent images.
* `IsMaximalTotallyRealMap.mfderiv_injective`: half-dimensionality forces immersion pointwise.
* `isTotallyRealEmbedding_of_contMDiff`: construct embeddings without supplying immersion.
* `SmoothTwoForm.IsNondegenerate.IsLagrangianMap.isTotallyRealEmbedding`: the pointwise tame
  comparison with an independently supplied `C^n` embedding.
* `isTotallyRealEmbedding_continuousLinearMap_iff`: the vector-space model criterion.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.
-/

public noncomputable section

open Manifold Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  {A : ∀ y : M, AlmostComplexStructure (TangentSpace I y)} {f : N → M}

/-- Every tangent image is maximal totally real for the pointwise almost complex structure.
The condition is geometric and independent of the regularity of that structure. -/
def IsMaximalTotallyRealMap (I' : ModelWithCorners ℝ F H') (I : ModelWithCorners ℝ E H)
    (A : ∀ y : M, AlmostComplexStructure (TangentSpace I y))
    (f : N → M) : Prop :=
  ∀ x, IsMaximalTotallyReal (A (f x)).toLinearMap
    (LinearMap.range (mfderiv I' I f x).toLinearMap)

/-- The maximal total reality condition is pointwise complementarity of tangent images. -/
theorem isMaximalTotallyRealMap_iff :
    IsMaximalTotallyRealMap I' I A f ↔
      ∀ x, IsMaximalTotallyReal (A (f x)).toLinearMap
        (LinearMap.range (mfderiv I' I f x).toLinearMap) := Iff.rfl

/-- Every tangent vector has a unique decomposition along a maximal totally real tangent image
and its almost complex image. -/
theorem IsMaximalTotallyRealMap.existsUnique_add (h : IsMaximalTotallyRealMap I' I A f)
    (x : N) (v : TangentSpace I (f x)) :
    ∃! w : (LinearMap.range (mfderiv I' I f x).toLinearMap) ×
        (LinearMap.range (mfderiv I' I f x).toLinearMap).map (A (f x)).toLinearMap,
      (w.1 : TangentSpace I (f x)) + w.2 = v :=
  (h x).existsUnique_add v

/-- A maximal totally real tangent image has half the ambient dimension. -/
theorem IsMaximalTotallyRealMap.two_mul_finrank_range [FiniteDimensional ℝ E]
    (h : IsMaximalTotallyRealMap I' I A f) (x : N) :
    2 * finrank ℝ (LinearMap.range (mfderiv I' I f x).toLinearMap) = finrank ℝ E := by
  have hd := (h x).two_mul_finrank_eq
    ((A (f x)).injective.comp (LinearMap.range (mfderiv I' I f x).toLinearMap).subtype_injective)
  simpa only [finrank_tangentSpace] using hd

/-- If the differential is injective at a point of a maximal totally real map, its source has
half the ambient dimension. -/
theorem IsMaximalTotallyRealMap.two_mul_finrank [FiniteDimensional ℝ E]
    (h : IsMaximalTotallyRealMap I' I A f) {x : N}
    (hx : Function.Injective (mfderiv I' I f x)) : 2 * finrank ℝ F = finrank ℝ E := by
  simpa only [LinearMap.finrank_range_of_inj hx, finrank_tangentSpace] using
    h.two_mul_finrank_range x

/-- Maximal total reality and half-dimensionality force the differential to be injective;
no separate injectivity assumption is needed. -/
theorem IsMaximalTotallyRealMap.mfderiv_injective [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (h : IsMaximalTotallyRealMap I' I A f)
    (hdim : 2 * finrank ℝ F = finrank ℝ E) (x : N) :
    Function.Injective (mfderiv I' I f x) := by
  have hr : finrank ℝ (LinearMap.range (mfderiv I' I f x).toLinearMap) =
      finrank ℝ (TangentSpace I' x) := by
    rw [finrank_tangentSpace]
    have := h.two_mul_finrank_range x
    omega
  have hker : LinearMap.ker (mfderiv I' I f x).toLinearMap = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hnull := (mfderiv I' I f x).toLinearMap.finrank_range_add_finrank_ker
    omega
  exact LinearMap.ker_eq_bot.mp hker

/-- A totally real `C^n` embedding has half the ambient dimension, and its tangent images are
maximal totally real. The structure field imposes no regularity on the almost complex field. -/
structure IsTotallyRealEmbedding (I' : ModelWithCorners ℝ F H') (I : ModelWithCorners ℝ E H)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (n : ℕ∞ω) (A : ∀ y : M, AlmostComplexStructure (TangentSpace I y)) (f : N → M) : Prop where
  /-- The parametrization is a native `C^n` embedding. -/
  isSmoothEmbedding : Manifold.IsSmoothEmbedding I' I n f
  /-- The source has half the ambient dimension, including for an empty source. -/
  two_mul_finrank : 2 * finrank ℝ F = finrank ℝ E
  /-- The tangent images are maximal totally real. -/
  isMaximalTotallyRealMap : IsMaximalTotallyRealMap I' I A f

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ∞ω}

/-- The totally real condition on an already embedded map is its dimension and tangent-image
conditions. -/
@[simp]
theorem isTotallyRealEmbedding_iff_of_isSmoothEmbedding
    (hf : Manifold.IsSmoothEmbedding I' I n f) :
    IsTotallyRealEmbedding I' I n A f ↔
      2 * finrank ℝ F = finrank ℝ E ∧ IsMaximalTotallyRealMap I' I A f :=
  ⟨fun h ↦ ⟨h.two_mul_finrank, h.isMaximalTotallyRealMap⟩,
    fun h ↦ ⟨hf, h.1, h.2⟩⟩

/-- On a nonempty source, maximal total reality supplies the dimension condition for an
embedding of positive regularity. -/
theorem isTotallyRealEmbedding_iff_of_isSmoothEmbedding_of_nonempty [Nonempty N]
    (hf : Manifold.IsSmoothEmbedding I' I n f) (hn : n ≠ 0) :
    IsTotallyRealEmbedding I' I n A f ↔ IsMaximalTotallyRealMap I' I A f := by
  rw [isTotallyRealEmbedding_iff_of_isSmoothEmbedding hf]
  exact ⟨And.right, fun h ↦ ⟨h.two_mul_finrank
    (hf.isImmersion.mfderiv_injective hn (Classical.arbitrary N)), h⟩⟩

/-- Lowering the embedding regularity preserves total reality. -/
theorem IsTotallyRealEmbedding.of_le {m : ℕ∞ω} (h : IsTotallyRealEmbedding I' I n A f)
    (hmn : m ≤ n) : IsTotallyRealEmbedding I' I m A f :=
  ⟨h.isSmoothEmbedding.of_le hmn, h.two_mul_finrank, h.isMaximalTotallyRealMap⟩

/-- The tangent differential of a totally real embedding is injective, independently of the
regularity label. This also follows from its geometric and dimension conditions. -/
theorem IsTotallyRealEmbedding.mfderiv_injective (h : IsTotallyRealEmbedding I' I n A f) (x : N) :
    Function.Injective (mfderiv I' I f x) :=
  h.isMaximalTotallyRealMap.mfderiv_injective h.two_mul_finrank x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Altering the pointwise structure away from the image does not change the geometric
condition. -/
theorem isMaximalTotallyRealMap_congr {B : ∀ y : M, AlmostComplexStructure (TangentSpace I y)}
    (hAB : ∀ x, A (f x) = B (f x)) :
    IsMaximalTotallyRealMap I' I A f ↔ IsMaximalTotallyRealMap I' I B f := by
  simp only [isMaximalTotallyRealMap_iff, hAB]

/-- Altering the structure away from the image preserves and reflects total reality. -/
theorem isTotallyRealEmbedding_congr {B : ∀ y : M, AlmostComplexStructure (TangentSpace I y)}
    (hAB : ∀ x, A (f x) = B (f x)) :
    IsTotallyRealEmbedding I' I n A f ↔ IsTotallyRealEmbedding I' I n B f := by
  constructor <;> intro h
  · exact ⟨h.isSmoothEmbedding, h.two_mul_finrank,
      (isMaximalTotallyRealMap_congr hAB).1 h.isMaximalTotallyRealMap⟩
  · exact ⟨h.isSmoothEmbedding, h.two_mul_finrank,
      (isMaximalTotallyRealMap_congr hAB).2 h.isMaximalTotallyRealMap⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Negating the almost complex field preserves and reflects maximal total reality. -/
@[simp]
theorem isMaximalTotallyRealMap_neg_iff :
    IsMaximalTotallyRealMap I' I (fun y ↦ -A y) f ↔ IsMaximalTotallyRealMap I' I A f := by
  simp only [isMaximalTotallyRealMap_iff, AlmostComplexStructure.neg_toLinearMap,
    isMaximalTotallyReal_iff, Submodule.map_neg]

/-- Totally real embeddings are independent of the sign of the almost complex field. -/
@[simp]
theorem isTotallyRealEmbedding_neg_iff :
    IsTotallyRealEmbedding I' I n (fun y ↦ -A y) f ↔ IsTotallyRealEmbedding I' I n A f := by
  constructor <;> intro h
  · exact ⟨h.isSmoothEmbedding, h.two_mul_finrank,
      isMaximalTotallyRealMap_neg_iff.1 h.isMaximalTotallyRealMap⟩
  · exact ⟨h.isSmoothEmbedding, h.two_mul_finrank,
      isMaximalTotallyRealMap_neg_iff.2 h.isMaximalTotallyRealMap⟩

/-- On boundaryless manifolds, a `C^n` topological embedding of half the ambient dimension
with maximal totally real tangent images is a totally real embedding. Its differential is
injective by the geometric condition, so immersion need not be separately supplied. -/
theorem isTotallyRealEmbedding_of_contMDiff [I'.Boundaryless] [I.Boundaryless]
    [IsManifold I' n N] [IsManifold I n M] (hn : 1 ≤ n)
    (hf : ContMDiff I' I n f) (he : Topology.IsEmbedding f)
    (hdim : 2 * finrank ℝ F = finrank ℝ E) (h : IsMaximalTotallyRealMap I' I A f) :
    IsTotallyRealEmbedding I' I n A f :=
  ⟨⟨hf.isImmersion_of_injective_mfderiv hn (h.mfderiv_injective hdim), he⟩, hdim, h⟩

section Reparametrization

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold I' n N] [IsManifold I' n P]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I' n N]
  [IsManifold I' n P] in
/-- A diffeomorphism of the source preserves and reflects the maximal total reality of tangent
images. -/
theorem _root_.Diffeomorph.isMaximalTotallyRealMap_comp_iff (φ : P ≃ₘ^n⟮I', I'⟯ N) (hn : n ≠ 0) :
    IsMaximalTotallyRealMap I' I A (f ∘ φ) ↔ IsMaximalTotallyRealMap I' I A f := by
  simp only [isMaximalTotallyRealMap_iff, φ.range_mfderiv_comp_diffeomorph hn,
    Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

/-- Reparametrizing by a diffeomorphism preserves and reflects totally real embeddings. -/
theorem _root_.Diffeomorph.isTotallyRealEmbedding_comp_iff (φ : P ≃ₘ^n⟮I', I'⟯ N) (hn : n ≠ 0) :
    IsTotallyRealEmbedding I' I n A (f ∘ φ) ↔ IsTotallyRealEmbedding I' I n A f := by
  constructor
  · intro h
    exact ⟨(isSmoothEmbedding_comp_diffeomorph_iff φ).1 h.isSmoothEmbedding,
      h.two_mul_finrank,
      (φ.isMaximalTotallyRealMap_comp_iff hn).1 h.isMaximalTotallyRealMap⟩
  · intro h
    exact ⟨isSmoothEmbedding_comp_diffeomorph φ h.isSmoothEmbedding, h.two_mul_finrank,
      (φ.isMaximalTotallyRealMap_comp_iff hn).2 h.isMaximalTotallyRealMap⟩

end Reparametrization

section Lagrangian

variable [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate}

omit [FiniteDimensional ℝ F] in
/-- A Lagrangian tangent image is maximal totally real for every pointwise structure
tame along the image.
Neither the field of almost complex structures nor its dependence on the base point needs
to be smooth. -/
theorem SmoothTwoForm.IsNondegenerate.IsLagrangianMap.isMaximalTotallyRealMap_of_tames
    (h : hσ.IsLagrangianMap I' f)
    (htame : ∀ x, (hσ.symplecticFormAt (f x)).Tames (A (f x))) :
    IsMaximalTotallyRealMap I' I A f := by
  rw [isMaximalTotallyRealMap_iff]
  intro x
  have hx := (SmoothTwoForm.IsNondegenerate.isLagrangianMap_iff_forall).1 h x
  exact hx.isMaximalTotallyReal_of_tames (htame x)

/-- A half-dimensional `C^n` embedding with Lagrangian tangent images is totally real for
any pointwise field tame along the image. This allows arbitrary finite embedding regularity. -/
theorem SmoothTwoForm.IsNondegenerate.IsLagrangianMap.isTotallyRealEmbedding
    (h : hσ.IsLagrangianMap I' f) (hf : Manifold.IsSmoothEmbedding I' I n f)
    (hdim : 2 * finrank ℝ F = finrank ℝ E)
    (htame : ∀ x, (hσ.symplecticFormAt (f x)).Tames (A (f x))) :
    IsTotallyRealEmbedding I' I n A f :=
  ⟨hf, hdim, h.isMaximalTotallyRealMap_of_tames htame⟩

/-- A half-dimensional Lagrangian embedding is totally real for every pointwise almost complex
structure tame along the image. The explicit dimension hypothesis also handles empty sources. -/
theorem SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding.isTotallyRealEmbedding_of_finrank
    (h : hσ.IsLagrangianEmbedding I' f) (hdim : 2 * finrank ℝ F = finrank ℝ E)
    (htame : ∀ x, (hσ.symplecticFormAt (f x)).Tames (A (f x))) :
    IsTotallyRealEmbedding I' I ∞ A f :=
  h.isLagrangianMap.isTotallyRealEmbedding h.isSmoothEmbedding hdim htame

/-- On a nonempty source, a Lagrangian embedding is totally real for every pointwise almost complex
field tame along the image, without a separate dimension hypothesis. -/
theorem SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding.isTotallyRealEmbedding_of_tames
    [Nonempty N] (h : hσ.IsLagrangianEmbedding I' f)
    (htame : ∀ x, (hσ.symplecticFormAt (f x)).Tames (A (f x))) :
    IsTotallyRealEmbedding I' I ∞ A f :=
  h.isTotallyRealEmbedding_of_finrank
    (h.isLagrangianMap.two_mul_finrank
      (h.isImmersion.mfderiv_injective (by simp) (Classical.arbitrary N))) htame

/-- On a nonempty source, a Lagrangian embedding is a smooth totally real embedding for every
smooth almost complex structure tamed by the ambient form. -/
theorem SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding.isTotallyRealEmbedding
    [Nonempty N] (h : hσ.IsLagrangianEmbedding I' f) {J : SmoothAlmostComplexStructure I M}
    (htame : σ.Tames J) :
    IsTotallyRealEmbedding I' I ∞ J.almostComplexStructureAt f :=
  h.isTotallyRealEmbedding_of_tames (fun x ↦ hσ.tames_iff.1 htame (f x))

end Lagrangian

section LinearModel

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {J : AlmostComplexStructure W}

/-- For a linear map in vector-space charts, the manifold condition is exactly maximal total
reality of its range. -/
theorem _root_.ContinuousLinearMap.isMaximalTotallyRealMap_iff (L : V →L[ℝ] W) :
    IsMaximalTotallyRealMap 𝓘(ℝ, V) 𝓘(ℝ, W) J.constSmooth.almostComplexStructureAt L ↔
      IsMaximalTotallyReal J.toLinearMap (LinearMap.range L.toLinearMap) := by
  simp only [TauCeti.isMaximalTotallyRealMap_iff, ContinuousLinearMap.mfderiv_eq,
    AlmostComplexStructure.constSmooth_almostComplexStructureAt]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- For a continuous linear map, half-dimensionality and maximal total reality characterize
all finite and infinite embedding regularities. Injectivity follows from those conditions. -/
theorem isTotallyRealEmbedding_continuousLinearMap_iff
    [FiniteDimensional ℝ V] (n : ℕ∞ω) (L : V →L[ℝ] W) :
    IsTotallyRealEmbedding 𝓘(ℝ, V) 𝓘(ℝ, W) n J.constSmooth.almostComplexStructureAt L ↔
      2 * finrank ℝ V = finrank ℝ W ∧
        IsMaximalTotallyReal J.toLinearMap (LinearMap.range L.toLinearMap) := by
  constructor
  · intro h
    exact ⟨h.two_mul_finrank,
      (L.isMaximalTotallyRealMap_iff).1 h.isMaximalTotallyRealMap⟩
  · rintro ⟨hdim, hJ⟩
    have hmap := (L.isMaximalTotallyRealMap_iff).2 hJ
    have hinj : Function.Injective L := by
      have hi := hmap.mfderiv_injective hdim 0
      intro v w hvw
      apply hi
      rw [ContinuousLinearMap.mfderiv_eq]
      exact hvw
    have he : Topology.IsEmbedding L :=
      (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)).isEmbedding
    exact ⟨⟨(ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj).isImmersion,
      he⟩, hdim, hmap⟩

end LinearModel

end TauCeti
