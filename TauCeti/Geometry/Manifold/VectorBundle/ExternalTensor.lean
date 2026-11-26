/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.Geometry.Manifold.VectorBundle.TensorProduct
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# External tensor products of vector bundles

Let `V → M` and `W → N` be finite-rank real vector bundles. Their **external tensor product**
`V ⊠ W` is the vector bundle over `M × N` with fibre `V x ⊗ W y` over `(x, y)`
(`TauCeti.ExternalTensor V W`). It is the tensor product of the pullbacks of `V` and `W` along the
two projections of `M × N`, so it is a topological vector bundle modelled on the projective tensor
product of the model fibres, and a `C^n` vector bundle on `M × N` when `V` and `W` are `C^n`
vector bundles.

For sections `s` of `V` and `t` of `W`, the section `(x, y) ↦ s x ⊗ t y` of `V ⊠ W`
(`ContMDiffSection.externalTensor`) is `C^n` when `s` and `t` are, and it is supported in the
product of their supports (`ContMDiffSection.tsupport_externalTensor_subset`). Its regularity is
read at each point in the trivialization of `V ⊠ W` induced by those of `V` and `W` there, where its
coordinates are the pure tensors of those of `s` and `t`, so it needs no regularity of the
transition maps of `V` and `W`.

External tensor products are the coefficient bundles of distributional kernels: an operator from
sections of `W` to distributional sections of a bundle over `M` has a kernel on `M × N` whose
tests are the sections of an external tensor product.

## Main definitions

* `TauCeti.ExternalTensor V W`: the external tensor product of `V` and `W`.
* `ContMDiffSection.externalTensor s t`: the section `(x, y) ↦ s x ⊗ t y`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds* (2nd ed.), Chapter 10 (constructions of vector
  bundles from pullbacks and tensor products).
-/

public noncomputable section

open Bundle Set
open scoped Manifold TensorProduct ContDiff

namespace TauCeti

section Defs

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  (W : N → Type*) [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)]

/-- The **external tensor product** `V ⊠ W` of bundles `V` over `M` and `W` over `N`: the bundle
over `M × N` whose fibre over `(x, y)` is `V x ⊗ W y`. It is the tensor product of the pullbacks of
`V` and `W` along the two projections. -/
abbrev ExternalTensor (p : M × N) : Type _ :=
  ((ContinuousMap.fst : C(M × N, M)) *ᵖ V) p ⊗[ℝ] ((ContinuousMap.snd : C(M × N, N)) *ᵖ W) p

/-- The fibres of an external tensor product carry their module topology. For finite-rank
bundles this is the topology of the fibre as a finite-dimensional real vector space. -/
instance (p : M × N) : TopologicalSpace (ExternalTensor V W p) :=
  moduleTopology ℝ _

instance (p : M × N) : IsModuleTopology ℝ (ExternalTensor V W p) :=
  ⟨rfl⟩

variable {V W} in
/-- Scalars pull out of both factors of a pure tensor in a fibre of `V ⊠ W`:
`(a • v) ⊗ (b • w) = (a * b) • (v ⊗ w)` for `v ∈ V x` and `w ∈ W y`. The fibres of `V ⊠ W` are
tensor products of fibres of pullback bundles, so this form applies directly to vectors of `V x`
and `W y`, where `TensorProduct.smul_tmul_smul` would need the scalar actions on the pullback
fibres. -/
theorem ExternalTensor.smul_tmul_smul {p : M × N} (a b : ℝ) (v : V p.1) (w : W p.2) :
    ((a • v) ⊗ₜ[ℝ] (b • w) : ExternalTensor V W p) =
      (a * b) • (v ⊗ₜ[ℝ] w : ExternalTensor V W p) := by
  let m := TensorProduct.mk ℝ (((ContinuousMap.fst : C(M × N, M)) *ᵖ V) p)
    (((ContinuousMap.snd : C(M × N, N)) *ᵖ W) p)
  calc ((a • v) ⊗ₜ[ℝ] (b • w) : ExternalTensor V W p) = a • m v (b • w) :=
        LinearMap.map_smul₂ m a v (b • w)
    _ = a • b • m v w := congrArg (a • ·) (map_smul (m v) b w)
    _ = (a * b) • (v ⊗ₜ[ℝ] w : ExternalTensor V W p) := smul_smul a b _

end Defs

section Smooth

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]

/-- The pullback of a `C^n` vector bundle on `M` along the first projection of `M × N` is a `C^n`
vector bundle. -/
instance contMDiffVectorBundle_pullback_fst [ContMDiffVectorBundle n F V I] :
    ContMDiffVectorBundle n F ((ContinuousMap.fst : C(M × N, M)) *ᵖ V) (I.prod J) :=
  Bundle.Pullback.contMDiffVectorBundle contMDiff_fst

/-- The pullback of a `C^n` vector bundle on `N` along the second projection of `M × N` is a `C^n`
vector bundle. -/
instance contMDiffVectorBundle_pullback_snd [ContMDiffVectorBundle n G W J] :
    ContMDiffVectorBundle n G ((ContinuousMap.snd : C(M × N, N)) *ᵖ W) (I.prod J) :=
  Bundle.Pullback.contMDiffVectorBundle contMDiff_snd

end Smooth

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (t' : Trivialization G (π G W)) [MemTrivializationAtlas t']

/-- The trivialization of the external tensor product `V ⊠ W` over `U × U'` induced by
trivializations of `V` over `U` and of `W` over `U'`: it reads `v ⊗ w` as `t v ⊗ t' w`. -/
def externalTensor :
    Trivialization (ProjectiveTensor ℝ F G) (π (ProjectiveTensor ℝ F G) (ExternalTensor V W)) :=
  (t.pullback (ContinuousMap.fst : C(M × N, M))).tensorProduct ℝ
    (t'.pullback (ContinuousMap.snd : C(M × N, N)))

instance : MemTrivializationAtlas (t.externalTensor t') :=
  inferInstanceAs (MemTrivializationAtlas
    ((t.pullback (ContinuousMap.fst : C(M × N, M))).tensorProduct ℝ
      (t'.pullback (ContinuousMap.snd : C(M × N, N)))))

/-- The base set of the trivialization of `V ⊠ W` induced by `t` and `t'` is the product of their
base sets. -/
@[simp]
theorem baseSet_externalTensor : (t.externalTensor t').baseSet = t.baseSet ×ˢ t'.baseSet := by
  rw [externalTensor, baseSet_tensorProduct, pullback_baseSet, pullback_baseSet, Set.prod_eq]
  -- The coercions of `ContinuousMap.fst` and `ContinuousMap.snd` are `Prod.fst` and `Prod.snd`.
  rfl

/-- Over the product of the base sets, the trivialization of `V ⊠ W` induced by `t` and `t'`
reads the pure tensor `v ⊗ w` of model vectors back as `t⁻¹ v ⊗ t'⁻¹ w`. -/
theorem externalTensor_symm_apply_tmul {p : M × N} (hp : p ∈ t.baseSet ×ˢ t'.baseSet) (v : F)
    (w : G) :
    (t.externalTensor t').symm p (ProjectiveTensor.mk (v ⊗ₜ[ℝ] w)) =
      (t.symm p.1 v ⊗ₜ[ℝ] t'.symm p.2 w : ExternalTensor V W p) := by
  rw [externalTensor, Bundle.Trivialization.tensorProduct_symm_apply_tmul (by exact hp),
    symm_pullback _ _ hp.1, symm_pullback _ _ hp.2]
  rfl

end Bundle.Trivialization

namespace ContMDiffSection

open TauCeti

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module ℝ (W y)] [∀ y, TopologicalSpace (W y)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [∀ y, Module ℝ (W y)] [VectorBundle ℝ G W] in
/-- A `C^n` section of `V`, composed with the first projection, is a `C^n` section of the
pullback of `V` to `M × N`. -/
private theorem contMDiff_pullback_fst (s : Cₛ^n⟮I; F, V⟯) :
    ContMDiff (I.prod J) ((I.prod J).prod 𝓘(ℝ, F)) n fun p : M × N ↦
      TotalSpace.mk' F (E := (ContinuousMap.fst : C(M × N, M)) *ᵖ V) p (s p.1) :=
  (Bundle.Pullback.contMDiff_iff (I := I) (ContinuousMap.fst : C(M × N, M)) contMDiff_fst).2
    ⟨contMDiff_id, s.contMDiff.comp contMDiff_fst⟩

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [∀ y, Module ℝ (W y)] [VectorBundle ℝ G W] in
/-- A `C^n` section of `W`, composed with the second projection, is a `C^n` section of the
pullback of `W` to `M × N`. -/
private theorem contMDiff_pullback_snd (t : Cₛ^n⟮J; G, W⟯) :
    ContMDiff (I.prod J) ((I.prod J).prod 𝓘(ℝ, G)) n fun p : M × N ↦
      TotalSpace.mk' G (E := (ContinuousMap.snd : C(M × N, N)) *ᵖ W) p (t p.2) :=
  (Bundle.Pullback.contMDiff_iff (I := J) (ContinuousMap.snd : C(M × N, N)) contMDiff_snd).2
    ⟨contMDiff_id, t.contMDiff.comp contMDiff_snd⟩

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul ℝ (W y)]

/-- The **external tensor product** `(x, y) ↦ s x ⊗ t y` of a `C^n` section `s` of `V` over `M`
and a `C^n` section `t` of `W` over `N`, a `C^n` section of `V ⊠ W` over `M × N`. -/
def externalTensor (s : Cₛ^n⟮I; F, V⟯) (t : Cₛ^n⟮J; G, W⟯) :
    Cₛ^n⟮I.prod J; ProjectiveTensor ℝ F G, ExternalTensor V W⟯ where
  toFun p := s p.1 ⊗ₜ[ℝ] t p.2
  contMDiff_toFun := ContMDiff.tmul_section (E₁ := (ContinuousMap.fst : C(M × N, M)) *ᵖ V)
    (E₂ := (ContinuousMap.snd : C(M × N, N)) *ᵖ W) (contMDiff_pullback_fst s)
    (contMDiff_pullback_snd t)

/-- The external tensor product of sections is `(x, y) ↦ s x ⊗ t y`. -/
@[simp]
theorem externalTensor_apply (s : Cₛ^n⟮I; F, V⟯) (t : Cₛ^n⟮J; G, W⟯) (p : M × N) :
    s.externalTensor t p = (s p.1 ⊗ₜ[ℝ] t p.2 : ExternalTensor V W p) :=
  (rfl)

/-- The external tensor product of sections is supported in the product of the supports. -/
theorem tsupport_externalTensor_subset (s : Cₛ^n⟮I; F, V⟯) (t : Cₛ^n⟮J; G, W⟯) :
    (s.externalTensor t).tsupport ⊆ s.tsupport ×ˢ t.tsupport := by
  rw [tsupport_def, tsupport_def, tsupport_def, ← closure_prod_eq]
  refine closure_mono fun p hp ↦ ⟨fun h ↦ hp ?_, fun h ↦ hp ?_⟩
  · rw [externalTensor_apply, show s p.1 = 0 from h]
    exact TensorProduct.zero_tmul _ _
  · rw [externalTensor_apply, show t p.2 = 0 from h]
    exact TensorProduct.tmul_zero _ _

end ContMDiffSection
