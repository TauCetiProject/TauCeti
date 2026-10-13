/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Euclidean
public import TauCeti.Geometry.Manifold.TubularNeighborhood.VectorBundle

/-!
# The intrinsic Euclidean normal vector bundle

The intrinsic normal spaces of a Euclidean embedding form a vector bundle with their
existing quotient topology. Its atlas is transported from the orthogonal normal bundle
by taking orthogonal representatives. Consequently the transition operators are exactly
those of the orthogonal atlas, and a `C^(n+1)` embedding gives a `C^n` vector bundle.

These coordinates let tubular parametrizations use intrinsic normal classes rather than
chosen orthogonal vectors. Install `SmoothEmbedding.normalSpaceFiberBundle` and
`SmoothEmbedding.normalSpaceVectorBundle` locally to use this atlas.

The construction reuses `Bundle.Trivialization.compHomeomorph`, the quotient-to-orthogonal
homeomorphism, and the fixed-model orthogonal normal trivializations.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the
normal-bundle construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Set Function Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω}

/-- Intrinsic normal coordinates obtained by taking orthogonal representatives and then
using the fixed-model orthogonal normal coordinates. The quotient topology is preserved. -/
def normalSpaceTrivialization (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M) :
    Trivialization F (π F (fun x => f.NormalSpace x hn)) := by
  let e := normalBundleTrivialization
    (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
    (f.isImmersion.mfderiv_injective hn) hdim x₀
  let h := f.normalBundleHomeomorphOrthogonal (F := F) hn
  -- `compHomeomorph` initially uses `proj ∘ h`; the representative map preserves the base.
  exact { e.compHomeomorph h with
    source_eq := by
      ext p
      simp only [Trivialization.compHomeomorph, Homeomorph.transOpenPartialHomeomorph_source,
        mem_preimage, e.mem_source, h, normalBundleHomeomorphOrthogonal_apply]
    proj_toFun := by
      intro p hp
      simpa only [Function.comp_apply, h, normalBundleHomeomorphOrthogonal_apply] using
        (e.compHomeomorph h).proj_toFun p hp }

/-- Taking intrinsic coordinates is taking orthogonal coordinates of the representative. -/
@[simp] theorem normalSpaceTrivialization_apply
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M)
    (p : TotalSpace F (fun x => f.NormalSpace x hn)) :
    f.normalSpaceTrivialization hn hdim x₀ p =
      normalBundleTrivialization
        (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
        (f.isImmersion.mfderiv_injective hn) hdim x₀
        (f.normalBundleHomeomorphOrthogonal hn p) := (rfl)

/-- Intrinsic and orthogonal normal coordinates have the same base set. -/
@[simp] theorem normalSpaceTrivialization_baseSet
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M) :
    (f.normalSpaceTrivialization hn hdim x₀).baseSet =
      (normalBundleTrivialization
        (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
        (f.isImmersion.mfderiv_injective hn) hdim x₀).baseSet := (rfl)

/-- Inverse intrinsic coordinates take the normal class of inverse orthogonal coordinates. -/
@[simp] theorem normalSpaceTrivialization_symm_apply
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M)
    (p : M × F) :
    (f.normalSpaceTrivialization hn hdim x₀).toOpenPartialHomeomorph.symm p =
      (f.normalBundleHomeomorphOrthogonal hn).symm
        ((normalBundleTrivialization
          (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
          (f.isImmersion.mfderiv_injective hn) hdim x₀).toOpenPartialHomeomorph.symm p) := (rfl)

/-- Intrinsic normal coordinates are fibrewise linear. -/
instance instIsLinearNormalSpaceTrivialization
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ : M) :
    (f.normalSpaceTrivialization hn hdim x₀).IsLinear ℝ where
  linear x hx := by
    constructor <;> intros <;>
      simp [normalBundleTrivialization_apply, normalBundleHomeomorphOrthogonal_apply]

/-- Taking orthogonal representatives cancels from intrinsic coordinate changes. -/
theorem normalSpaceTrivialization_coordChangeL
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x₀ x₁ : M)
    {x : M} (hx : x ∈ (f.normalSpaceTrivialization hn hdim x₀).baseSet ∩
      (f.normalSpaceTrivialization hn hdim x₁).baseSet) :
    ((f.normalSpaceTrivialization hn hdim x₀).coordChangeL ℝ
      (f.normalSpaceTrivialization hn hdim x₁) x : F →L[ℝ] F) =
      ((normalBundleTrivialization
        (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
        (f.isImmersion.mfderiv_injective hn) hdim x₀).coordChangeL ℝ
        (normalBundleTrivialization
          (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
          (f.isImmersion.mfderiv_injective hn) hdim x₁) x : F →L[ℝ] F) := by
  ext v
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply' _ _ hx,
    Trivialization.coordChangeL_apply' _ _ (by simpa using hx)]
  simp only [normalSpaceTrivialization_apply, normalSpaceTrivialization_symm_apply,
    Homeomorph.apply_symm_apply]

/-- The intrinsic Euclidean normal bundle, with its quotient topology and transported atlas. -/
@[instance_reducible]
def normalSpaceFiberBundle (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    FiberBundle F (fun x => f.NormalSpace x hn) where
  totalSpaceMk_isInducing' x := (f.isEmbedding_normalBundle_mk hn x).isInducing
  trivializationAtlas' := range (f.normalSpaceTrivialization hn hdim)
  trivializationAt' := f.normalSpaceTrivialization hn hdim
  mem_baseSet_trivializationAt' x := by simp
  trivialization_mem_atlas' x := mem_range_self x

/-- The preferred intrinsic chart is the transported normal chart at the same point. -/
@[simp] theorem normalSpaceFiberBundle_trivializationAt
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    trivializationAt F (fun x => f.NormalSpace x hn) x =
      f.normalSpaceTrivialization hn hdim x := (rfl)

/-- The intrinsic atlas consists exactly of the transported orthogonal normal charts. -/
@[simp] theorem mem_normalSpaceFiberBundle_trivializationAtlas_iff
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    (e : Trivialization F (π F (fun x => f.NormalSpace x hn))) :
    letI := f.normalSpaceFiberBundle hn hdim
    e ∈ trivializationAtlas F (fun x => f.NormalSpace x hn) ↔
      ∃ x, f.normalSpaceTrivialization hn hdim x = e := Iff.rfl

/-- Intrinsic normal coordinates define a vector bundle: their transition operators are
those of the orthogonal normal vector bundle. -/
theorem normalSpaceVectorBundle (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    letI := f.normalSpaceFiberBundle hn hdim
    VectorBundle ℝ F (fun x => f.NormalSpace x hn) := by
  let := f.normalSpaceFiberBundle hn hdim
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · rintro e ⟨x, rfl⟩
    infer_instance
  · rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
    have : IsManifold I ((0 : ℕ∞ω) + 1) M := by
      simpa using (inferInstance : IsManifold I 1 M)
    refine (contMDiffOn_normalBundleTrivialization_coordChangeL (n := 0)
      (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
      (f.isImmersion.mfderiv_injective hn) hdim x x').continuousOn.congr ?_
    intro y hy
    exact f.normalSpaceTrivialization_coordChangeL hn hdim x x' (by simpa using hy)

omit [IsManifold I 1 M] in
/-- An embedding of regularity at least `C^(m+1)` has a `C^m` intrinsic normal vector
bundle, retaining the quotient topology on its total space. -/
theorem normalSpaceContMDiffVectorBundle {m : ℕ∞ω}
    [IsManifold I (m + 1) M]
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiffVectorBundle m F (fun x => f.NormalSpace x hn) I := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  constructor
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  refine (contMDiffOn_normalBundleTrivialization_coordChangeL
    (f.contMDiff.of_le hm) (f.isImmersion.mfderiv_injective hn) hdim x x').congr ?_
  intro y hy
  exact f.normalSpaceTrivialization_coordChangeL hn hdim x x' (by simpa using hy)

end TauCeti.SmoothEmbedding
