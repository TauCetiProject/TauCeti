/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Trivialization
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# The smooth Euclidean normal bundle

The normal spaces of a `C^(n+1)` immersion into a finite-dimensional real inner product space
form a `C^n` vector bundle. Its total space keeps the subspace topology inherited from `M × V`.
A `C¹` immersion already gives a continuous vector bundle.
In particular, bundle constructions and the Euclidean tubular map use the same topology.

The local normal trivializations use different reference fibres. Here each reference fibre is
identified with one fixed normed space `F` of the codimension. These identifications are constant
within each trivialization; no regularity of their dependence on the reference point is needed.
The resulting transition operators are the already established normal-coordinate changes,
conjugated by those fixed identifications.

For a `C¹` immersion, install `normalFiberBundle hf himm hdim` and
`normalVectorBundle hf himm hdim` with `letI`. A `C^(n+1)` immersion supplies the `C¹`
hypotheses via `IsManifold.of_le` and `hf.of_le le_add_self`; its smooth structure is
`normalContMDiffVectorBundle hf himm hdim`. The model fibre can, for example, be
`EuclideanSpace ℝ (Fin (Module.finrank ℝ V - Module.finrank ℝ E))`.
Neither compactness nor injectivity of the immersion is required.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), the normal-bundle construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Set Function Topology Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} [IsManifold I 1 M] {f : M → V}

/-- A fixed linear identification of a normal fibre with a model of the codimension. -/
def normalFiberEquiv
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x : M)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) :
    normalSubspace I f x ≃L[ℝ] F :=
  ContinuousLinearEquiv.ofFinrankEq ((finrank_normalSubspace himm).trans hdim.symm)

/-- A local normal trivialization with a single fixed model fibre. Its base set is the
invertibility locus of the normal compression at the reference point. -/
def normalBundleTrivialization (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M) :
    Trivialization F (π F (fun x => normalSubspace I f x)) := by
  letI : IsManifold I ((0 : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I 1 M)
  -- Changing the phantom model-fibre parameter preserves the induced topology from `M × V`.
  let h : TotalSpace F (fun x => normalSubspace I f x) ≃ₜ
      TotalSpace (normalSubspace I f x₀) (fun x => normalSubspace I f x) :=
    { toFun := fun p => ⟨p.proj, p.2⟩
      invFun := fun p => ⟨p.proj, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (isEmbedding_totalSpace_normalSubspace f).isInducing.continuous_iff.mpr
        (isEmbedding_totalSpace_normalSubspace (F := F) f).continuous
      continuous_invFun :=
        (isEmbedding_totalSpace_normalSubspace (F := F) f).isInducing.continuous_iff.mpr
          (isEmbedding_totalSpace_normalSubspace f).continuous }
  exact ((normalTrivialization (n := 0) hf himm x₀).compHomeomorph h).transFiberHomeomorph
    (normalFiberEquiv hdim x₀ (himm x₀)).toHomeomorph

/-- The base set is unchanged by choosing a fixed model fibre. -/
@[simp] theorem mem_normalBundleTrivialization_baseSet
    (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ x : M) :
    x ∈ (normalBundleTrivialization hf himm hdim x₀).baseSet ↔
      IsUnit (normalCompression I f x₀ x) := by
  have : IsManifold I ((0 : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I 1 M)
  exact mem_normalTrivialization_baseSet (n := 0) hf himm x₀ x

/-- Fixed-model normal coordinates are the original coordinates followed by the reference
fibre identification. -/
@[simp] theorem normalBundleTrivialization_apply
    (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    normalBundleTrivialization hf himm hdim x₀ p =
      (p.proj, normalFiberEquiv hdim x₀ (himm x₀) (normalCoordinateMap I f x₀ p.proj p.2)) := by
  have : IsManifold I ((0 : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I 1 M)
  exact congrArg (Prod.map id (normalFiberEquiv hdim x₀ (himm x₀)))
    (normalTrivialization_apply (n := 0) hf himm x₀ ⟨p.proj, p.2⟩)

/-- Inverse fixed-model coordinates project the reference normal vector to the moving fibre. -/
@[simp] theorem normalBundleTrivialization_symm_apply
    (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M)
    (p : M × F) :
    (normalBundleTrivialization hf himm hdim x₀).toOpenPartialHomeomorph.symm p =
      ⟨p.1, ⟨(normalSubspace I f p.1).starProjection
        ((normalFiberEquiv hdim x₀ (himm x₀)).symm p.2),
        Submodule.starProjection_apply_mem _ _⟩⟩ := by
  have : IsManifold I ((0 : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I 1 M)
  exact congrArg (fun q : TotalSpace (normalSubspace I f x₀) (fun x => normalSubspace I f x) =>
    (⟨q.proj, q.2⟩ : TotalSpace F (fun x => normalSubspace I f x)))
    (normalTrivialization_symm_apply (n := 0) hf himm x₀
      (p.1, (normalFiberEquiv hdim x₀ (himm x₀)).symm p.2))

/-- Fixed-model normal trivializations are fibrewise linear. -/
instance instIsLinearNormalBundleTrivialization
    (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M) :
    (normalBundleTrivialization hf himm hdim x₀).IsLinear ℝ where
  linear x _ := by
    constructor <;> intros <;> simp

/-- On overlaps, transition operators are the normal-coordinate changes conjugated by the
two fixed reference-fibre identifications. -/
theorem normalBundleTrivialization_coordChangeL
    (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    (x₀ x₁ : M) {x : M}
    (hx : x ∈ (normalBundleTrivialization hf himm hdim x₀).baseSet ∩
      (normalBundleTrivialization hf himm hdim x₁).baseSet) :
    ((normalBundleTrivialization hf himm hdim x₀).coordChangeL ℝ
      (normalBundleTrivialization hf himm hdim x₁) x : F →L[ℝ] F) =
      (normalFiberEquiv hdim x₁ (himm x₁)).toContinuousLinearMap ∘L
        normalCoordinateChange I f x₀ x₁ x ∘L
          (normalFiberEquiv hdim x₀ (himm x₀)).symm.toContinuousLinearMap := by
  ext v
  rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply' _ _ hx,
    normalBundleTrivialization_symm_apply, normalBundleTrivialization_apply]
  simp [normalCoordinateChange_apply]

omit [IsManifold I 1 M] in
/-- The fixed-model normal transition operators vary `C^n` on overlaps. -/
theorem contMDiffOn_normalBundleTrivialization_coordChangeL [IsManifold I (n + 1) M]
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ x₁ : M) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) n
      (fun x => ((normalBundleTrivialization (hf.of_le le_add_self) himm hdim x₀).coordChangeL ℝ
        (normalBundleTrivialization (hf.of_le le_add_self) himm hdim x₁) x : F →L[ℝ] F))
      ((normalBundleTrivialization (hf.of_le le_add_self) himm hdim x₀).baseSet ∩
        (normalBundleTrivialization (hf.of_le le_add_self) himm hdim x₁).baseSet) := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  refine ((contMDiffOn_const
    (c := (normalFiberEquiv hdim x₁ (himm x₁)).toContinuousLinearMap)).clm_comp
    (((contMDiffOn_normalCoordinateChange hf himm x₀ x₁).mono
      (fun x hx => (mem_normalBundleTrivialization_baseSet
        (hf.of_le le_add_self) himm hdim x₁ x).mp hx.2)).clm_comp
        (contMDiffOn_const
          (c := (normalFiberEquiv hdim x₀ (himm x₀)).symm.toContinuousLinearMap)))).congr ?_
  intro x hx
  exact normalBundleTrivialization_coordChangeL (hf.of_le le_add_self) himm hdim x₀ x₁ hx

/-- The normal fibres form a fibre bundle with the topology inherited from `M × V`.
Use this definition as a local instance to choose its projected normal-coordinate atlas. -/
@[instance_reducible]
def normalFiberBundle (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    FiberBundle F (fun x => normalSubspace I f x) where
  totalSpaceMk_isInducing' x := by
    rw [← (isEmbedding_totalSpace_normalSubspace (F := F) f).isInducing.of_comp_iff]
    exact isInducing_const_prod.mpr IsInducing.subtypeVal
  trivializationAtlas' := range (normalBundleTrivialization hf himm hdim)
  trivializationAt' := normalBundleTrivialization hf himm hdim
  mem_baseSet_trivializationAt' x := by simp
  trivialization_mem_atlas' x := mem_range_self x

/-- The preferred normal-bundle trivialization is the fixed-model projected trivialization
at the same point. -/
@[simp] theorem normalFiberBundle_trivializationAt
    (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x : M) :
    let := normalFiberBundle hf himm hdim
    trivializationAt F (fun x => normalSubspace I f x) x =
      normalBundleTrivialization hf himm hdim x :=
  (rfl)

/-- The normal-bundle atlas consists exactly of the projected normal trivializations. -/
@[simp] theorem mem_normalFiberBundle_trivializationAtlas_iff
    (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    (e : Trivialization F (π F (fun x => normalSubspace I f x))) :
    let := normalFiberBundle hf himm hdim
    e ∈ trivializationAtlas F (fun x => normalSubspace I f x) ↔
      ∃ x, normalBundleTrivialization hf himm hdim x = e :=
  Iff.rfl

/-- The normal fibre bundle is a real vector bundle: its atlas is linear and its transition
operators are continuous in operator norm. -/
theorem normalVectorBundle (hf : ContMDiff I 𝓘(ℝ, V) 1 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    let := normalFiberBundle hf himm hdim
    VectorBundle ℝ F (fun x => normalSubspace I f x) := by
  have : IsManifold I ((0 : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I 1 M)
  let := normalFiberBundle hf himm hdim
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro e he
    obtain ⟨x, rfl⟩ := (mem_normalFiberBundle_trivializationAtlas_iff hf himm hdim e).mp he.out
    infer_instance
  · intro e e' he he'
    obtain ⟨x, rfl⟩ := (mem_normalFiberBundle_trivializationAtlas_iff hf himm hdim e).mp he.out
    obtain ⟨x', rfl⟩ := (mem_normalFiberBundle_trivializationAtlas_iff hf himm hdim e').mp he'.out
    exact (contMDiffOn_normalBundleTrivialization_coordChangeL
      (n := 0) hf himm hdim x x').continuousOn

omit [IsManifold I 1 M] in
/-- The normal bundle of a `C^(n+1)` immersion is a `C^n` vector bundle, with the existing
subspace topology on its total space. -/
theorem normalContMDiffVectorBundle [IsManifold I (n + 1) M] (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    let := normalFiberBundle (hf.of_le le_add_self) himm hdim
    let := normalVectorBundle (hf.of_le le_add_self) himm hdim
    ContMDiffVectorBundle n F (fun x => normalSubspace I f x) I := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  let := normalVectorBundle (hf.of_le le_add_self) himm hdim
  constructor
  intro e e' he he'
  obtain ⟨x, rfl⟩ := (mem_normalFiberBundle_trivializationAtlas_iff
    (hf.of_le le_add_self) himm hdim e).mp he.out
  obtain ⟨x', rfl⟩ := (mem_normalFiberBundle_trivializationAtlas_iff
    (hf.of_le le_add_self) himm hdim e').mp he'.out
  exact contMDiffOn_normalBundleTrivialization_coordChangeL hf himm hdim x x'

end TauCeti
