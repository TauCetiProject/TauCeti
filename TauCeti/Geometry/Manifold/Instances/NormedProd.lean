/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Manifold.TangentCone

/-!
# Products of manifolds charted on normed spaces, read on the product normed space

Mathlib charts a product `M × N` of spaces charted on `H` and `H'` on the type synonym
`ModelProd H H'`, with the product model `I.prod I'`. When `M` and `N` are charted on normed spaces
`E` and `E'`, many constructions are stated for manifolds charted on a normed space with the model
`𝓘(𝕜, E)`, for instance the Morse complex of an adapted pseudo-gradient. To apply them to `M × N`,
this file reads Mathlib's product charts on the normed space `E × E'`
(`TauCeti.prodNormedChartedSpace`), with the model `𝓘(𝕜, E × E')`. This model is equal, but not
definitionally equal, to `𝓘(𝕜, E).prod 𝓘(𝕜, E')` (`modelWithCornersSelf_prod`).

The file transports the basic calculus of products along that equality: smoothness of the product
(`TauCeti.isManifold_prodNormedChartedSpace`), its extended charts and maximal atlas, the
derivatives of the projections and of maps that factor through them, product vector fields and
their integral curves, and the tangent spaces of products of sets: the span of
the tangent cone of `A ×ˢ B` contains the product of the spans of the tangent cones of `A` and `B`
(`TauCeti.span_mtangentConeAt_prod_le_prodNormed`).

`TauCeti.prodNormedChartedSpace` is a definition rather than an instance: on `E × E'` itself it
would compete with `chartedSpaceSelf`. Files using it make it a local instance of low priority, so
that `chartedSpaceSelf` is still found for the normed space `E × E'`.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E' N]

variable (E E' M N) in
/-- The product `M × N` of spaces charted on normed spaces `E` and `E'`, charted on the normed
space `E × E'` by the products of charts of `M` and `N`. These are Mathlib's product charts, read
on `E × E'` rather than on the type synonym `ModelProd E E'`. Its body is exposed so that its
charts are definitionally Mathlib's product charts, which the transport along
`modelWithCornersSelf_prod` needs. -/
@[expose, instance_reducible]
noncomputable def prodNormedChartedSpace : ChartedSpace (E × E') (M × N) :=
  prodChartedSpace E M E' N

attribute [local instance 10] prodNormedChartedSpace

/-- The product of smooth manifolds charted on normed spaces is a smooth manifold for the model
`𝓘(𝕜, E × E')` of the product normed space. -/
theorem isManifold_prodNormedChartedSpace {n : WithTop ℕ∞} [IsManifold 𝓘(𝕜, E) n M]
    [IsManifold 𝓘(𝕜, E') n N] : IsManifold 𝓘(𝕜, E × E') n (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact (inferInstance : IsManifold (𝓘(𝕜, E).prod 𝓘(𝕜, E')) n (M × N))

attribute [local instance] isManifold_prodNormedChartedSpace

/-! ### Transport along `modelWithCornersSelf_prod`

The model `𝓘(𝕜, E × E')` and Mathlib's product model have the same charts but are not
definitionally equal, and rewriting one into the other inside a statement about tangent bundles
or derivatives produces ill-typed motives. Each statement below is therefore proved for a model
`I` equal to the product model, which `subst` replaces by the product model, and then specialized
to `𝓘(𝕜, E × E')`. -/

section Transport

variable {I : ModelWithCorners 𝕜 (E × E') (E × E')}

private theorem hasMFDerivAt_fst_of_eq (hI : I = 𝓘(𝕜, E).prod 𝓘(𝕜, E')) (z : M × N) :
    HasMFDerivAt I 𝓘(𝕜, E) Prod.fst z (ContinuousLinearMap.fst 𝕜 E E') := by
  subst hI; exact hasMFDerivAt_fst z

private theorem hasMFDerivAt_snd_of_eq (hI : I = 𝓘(𝕜, E).prod 𝓘(𝕜, E')) (z : M × N) :
    HasMFDerivAt I 𝓘(𝕜, E') Prod.snd z (ContinuousLinearMap.snd 𝕜 E E') := by
  subst hI; exact hasMFDerivAt_snd z

private theorem extChartAt_prod_of_eq (hI : I = 𝓘(𝕜, E).prod 𝓘(𝕜, E')) (z : M × N) :
    extChartAt I z = (extChartAt 𝓘(𝕜, E) z.1).prod (extChartAt 𝓘(𝕜, E') z.2) := by
  subst hI; exact extChartAt_prod z

private theorem mem_maximalAtlas_prod_of_eq {n : WithTop ℕ∞} [IsManifold 𝓘(𝕜, E) n M]
    [IsManifold 𝓘(𝕜, E') n N] [IsManifold I n (M × N)] (hI : I = 𝓘(𝕜, E).prod 𝓘(𝕜, E'))
    {e : OpenPartialHomeomorph M E} {e' : OpenPartialHomeomorph N E'}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E') n N) :
    e.prod e' ∈ IsManifold.maximalAtlas I n (M × N) := by
  subst hI; exact IsManifold.mem_maximalAtlas_prod he he'

private theorem contMDiff_prodMk_vectorField_of_eq {n : WithTop ℕ∞} [IsManifold 𝓘(𝕜, E) 1 M]
    [IsManifold 𝓘(𝕜, E') 1 N] [IsManifold I 1 (M × N)] (hI : I = 𝓘(𝕜, E).prod 𝓘(𝕜, E'))
    {X : (x : M) → TangentSpace 𝓘(𝕜, E) x} {Y : (y : N) → TangentSpace 𝓘(𝕜, E') y}
    (hX : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E).tangent n (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(𝕜, E) M)))
    (hY : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E').tangent n
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle 𝓘(𝕜, E') N))) :
    ContMDiff I I.tangent n
      (fun z : M × N ↦ (⟨z, ((X z.1, Y z.2) : E × E')⟩ : TangentBundle I (M × N))) := by
  subst hI
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(𝕜, E)) (M := M) (I' := 𝓘(𝕜, E'))
    (M' := N)).comp ((hX.comp contMDiff_fst).prodMk (hY.comp contMDiff_snd))

end Transport

/-- The extended chart of `M × N` at `z`, for the model `𝓘(𝕜, E × E')`, is the product of the
extended charts of `M` at `z.1` and of `N` at `z.2`. -/
theorem extChartAt_prodNormed (z : M × N) :
    extChartAt 𝓘(𝕜, E × E') z = (extChartAt 𝓘(𝕜, E) z.1).prod (extChartAt 𝓘(𝕜, E') z.2) :=
  extChartAt_prod_of_eq modelWithCornersSelf_prod z

/-- A product of charts of the maximal atlases of `M` and `N` lies in the maximal atlas of `M × N`
for the model `𝓘(𝕜, E × E')`. -/
theorem mem_maximalAtlas_prodNormed {n : WithTop ℕ∞} [IsManifold 𝓘(𝕜, E) n M]
    [IsManifold 𝓘(𝕜, E') n N] {e : OpenPartialHomeomorph M E} {e' : OpenPartialHomeomorph N E'}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E') n N) :
    e.prod e' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E × E') n (M × N) :=
  mem_maximalAtlas_prod_of_eq modelWithCornersSelf_prod he he'

/-- The first projection of `M × N` has the first projection of `E × E'` as derivative. -/
theorem hasMFDerivAt_fst_prodNormed (z : M × N) :
    HasMFDerivAt 𝓘(𝕜, E × E') 𝓘(𝕜, E) Prod.fst z (ContinuousLinearMap.fst 𝕜 E E') :=
  hasMFDerivAt_fst_of_eq modelWithCornersSelf_prod z

/-- The second projection of `M × N` has the second projection of `E × E'` as derivative. -/
theorem hasMFDerivAt_snd_prodNormed (z : M × N) :
    HasMFDerivAt 𝓘(𝕜, E × E') 𝓘(𝕜, E') Prod.snd z (ContinuousLinearMap.snd 𝕜 E E') :=
  hasMFDerivAt_snd_of_eq modelWithCornersSelf_prod z

/-- The derivative of `x ↦ F x.1`, for a map `F` of `M` differentiable at `z.1`, is the derivative
of `F` at `z.1` applied to the first component. -/
theorem mfderiv_comp_fst_apply_prodNormed {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] {F : M → F'} {z : M × N} (hF : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F') F z.1)
    (u : E × E') :
    mfderiv 𝓘(𝕜, E × E') 𝓘(𝕜, F') (fun z ↦ F z.1) z u = mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F') F z.1 u.1 := by
  rw [show (fun z : M × N ↦ F z.1) = F ∘ Prod.fst from rfl,
    (hF.hasMFDerivAt.comp z (hasMFDerivAt_fst_prodNormed z)).mfderiv]
  -- The composite with `ContinuousLinearMap.fst` evaluates to the first component.
  rfl

/-- The derivative of `x ↦ F x.2`, for a map `F` of `N` differentiable at `z.2`, is the derivative
of `F` at `z.2` applied to the second component. -/
theorem mfderiv_comp_snd_apply_prodNormed {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] {F : N → F'} {z : M × N} (hF : MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, F') F z.2)
    (u : E × E') :
    mfderiv 𝓘(𝕜, E × E') 𝓘(𝕜, F') (fun z ↦ F z.2) z u =
      mfderiv 𝓘(𝕜, E') 𝓘(𝕜, F') F z.2 u.2 := by
  rw [show (fun z : M × N ↦ F z.2) = F ∘ Prod.snd from rfl,
    (hF.hasMFDerivAt.comp z (hasMFDerivAt_snd_prodNormed z)).mfderiv]
  -- The composite with `ContinuousLinearMap.snd` evaluates to the second component.
  rfl

/-- A product of vector fields of class `C^n` on `M` and `N` is a vector field of class `C^n` on
`M × N`, for the model `𝓘(𝕜, E × E')`. -/
theorem contMDiff_prodMk_vectorField_prodNormed {n : WithTop ℕ∞}
    [IsManifold 𝓘(𝕜, E) 1 M] [IsManifold 𝓘(𝕜, E') 1 N]
    {X : (x : M) → TangentSpace 𝓘(𝕜, E) x} {Y : (y : N) → TangentSpace 𝓘(𝕜, E') y}
    (hX : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E).tangent n (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(𝕜, E) M)))
    (hY : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E').tangent n
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle 𝓘(𝕜, E') N))) :
    ContMDiff 𝓘(𝕜, E × E') 𝓘(𝕜, E × E').tangent n
      (fun z : M × N ↦ (⟨z, ((X z.1, Y z.2) : E × E')⟩ : TangentBundle 𝓘(𝕜, E × E') (M × N))) :=
  contMDiff_prodMk_vectorField_of_eq modelWithCornersSelf_prod hX hY

/-- The preimage of `A ×ˢ B` under the inverse of the extended chart of `M × N` at `z` is the
product of the preimages of `A` and `B` under the inverses of the extended charts at `z.1` and
`z.2`. -/
private theorem extChartAt_prodNormed_symm_preimage_prod_inter_range (A : Set M) (B : Set N)
    (z : M × N) :
    (extChartAt 𝓘(𝕜, E × E') z).symm ⁻¹' (A ×ˢ B) ∩ range 𝓘(𝕜, E × E') =
      ((extChartAt 𝓘(𝕜, E) z.1).symm ⁻¹' A ∩ range 𝓘(𝕜, E)) ×ˢ
        ((extChartAt 𝓘(𝕜, E') z.2).symm ⁻¹' B ∩ range 𝓘(𝕜, E')) := by
  rw [extChartAt_prodNormed]
  ext v
  simp only [mem_inter_iff, mem_preimage, PartialEquiv.prod_coe_symm, mem_prod,
    modelWithCornersSelf_coe, range_id, mem_univ, and_true]

/-- The tangent cone of `A ×ˢ B` at `z`, read in the chart of `M × N`, contains the tangent cone of
`A` at `z.1` in the first factor. -/
theorem inl_image_mtangentConeAt_subset_prodNormed {A : Set M} {B : Set N}
    {z : M × N} (hB : z.2 ∈ B) :
    ContinuousLinearMap.inl 𝕜 E E' '' mtangentConeAt 𝓘(𝕜, E) A z.1 ⊆
      mtangentConeAt 𝓘(𝕜, E × E') (A ×ˢ B) z := by
  rw [mtangentConeAt_def, mtangentConeAt_def, extChartAt_prodNormed_symm_preimage_prod_inter_range,
    extChartAt_prodNormed]
  exact subset_tangentConeAt_prod_left (subset_closure ⟨by simpa using hB, by simp⟩)

/-- The tangent cone of `A ×ˢ B` at `z`, read in the chart of `M × N`, contains the tangent cone of
`B` at `z.2` in the second factor. -/
theorem inr_image_mtangentConeAt_subset_prodNormed {A : Set M} {B : Set N}
    {z : M × N} (hA : z.1 ∈ A) :
    ContinuousLinearMap.inr 𝕜 E E' '' mtangentConeAt 𝓘(𝕜, E') B z.2 ⊆
      mtangentConeAt 𝓘(𝕜, E × E') (A ×ˢ B) z := by
  rw [mtangentConeAt_def, mtangentConeAt_def, extChartAt_prodNormed_symm_preimage_prod_inter_range,
    extChartAt_prodNormed]
  exact subset_tangentConeAt_prod_right (subset_closure ⟨by simpa using hA, by simp⟩)

/-- The span of the tangent cone of `A ×ˢ B` at `z`, read in the chart of `M × N`, contains the
product of the spans of the tangent cones of `A` at `z.1` and of `B` at `z.2`. -/
theorem span_mtangentConeAt_prod_le_prodNormed {A : Set M} {B : Set N} {z : M × N}
    (hA : z.1 ∈ A) (hB : z.2 ∈ B) :
    (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E) A z.1)).prod
        (Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E') B z.2)) ≤
      Submodule.span 𝕜 (mtangentConeAt 𝓘(𝕜, E × E') (A ×ˢ B) z) := by
  rw [LinearMap.prod_eq_sup_map, Submodule.map_span, Submodule.map_span]
  exact sup_le (Submodule.span_mono (inl_image_mtangentConeAt_subset_prodNormed hB))
    (Submodule.span_mono (inr_image_mtangentConeAt_subset_prodNormed hA))

section Real

variable {E E' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
  [ChartedSpace E' N] {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {Y : (y : N) → TangentSpace 𝓘(ℝ, E') y}

private theorem isMIntegralCurve_prodMk_of_eq {I : ModelWithCorners ℝ (E × E') (E × E')}
    (hI : I = 𝓘(ℝ, E).prod 𝓘(ℝ, E')) {γ : ℝ → M} {δ : ℝ → N} (hγ : IsMIntegralCurve γ X)
    (hδ : IsMIntegralCurve δ Y) :
    IsMIntegralCurve (I := I) (fun t ↦ (γ t, δ t))
      (fun z : M × N ↦ ((X z.1, Y z.2) : TangentSpace I z)) := by
  subst hI
  intro t
  have h (v : E) (w : E') : (1 : ℝ →L[ℝ] ℝ).smulRight ((v, w) : E × E') =
      ((1 : ℝ →L[ℝ] ℝ).smulRight v).prod ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
    ext <;> simp
  exact ((hγ t).prodMk (hδ t)).congr_mfderiv (h _ _).symm

/-- **Integral curves of a product vector field.** A pair of integral curves of vector fields `X`
on `M` and `Y` on `N` is an integral curve of the product field `(X, Y)` on `M × N`. -/
theorem isMIntegralCurve_prodMk_prodNormed {γ : ℝ → M} {δ : ℝ → N}
    (hγ : IsMIntegralCurve γ X) (hδ : IsMIntegralCurve δ Y) :
    IsMIntegralCurve (I := 𝓘(ℝ, E × E')) (fun t ↦ (γ t, δ t))
      (fun z : M × N ↦ ((X z.1, Y z.2) : TangentSpace 𝓘(ℝ, E × E') z)) :=
  isMIntegralCurve_prodMk_of_eq modelWithCornersSelf_prod hγ hδ

end Real

end TauCeti
