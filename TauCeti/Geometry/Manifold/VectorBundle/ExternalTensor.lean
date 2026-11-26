/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.TensorProduct
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# External tensor products of vector bundles

Let `V → M` and `W → N` be finite-rank vector bundles over a complete nontrivially normed field
`𝕜`. Their **external tensor product** `V ⊠ W` is the vector bundle over `M × N` with fibre
`V x ⊗[𝕜] W y` over `(x, y)` (`TauCeti.ExternalTensor 𝕜 V W`). It is the tensor product of the
pullbacks of `V` and `W` along the two projections of `M × N`, so it is a topological vector bundle
modelled on the projective tensor product of the model fibres, and a `C^n` vector bundle on
`M × N` when `V` and `W` are `C^n` vector bundles.

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

* `TauCeti.ExternalTensor 𝕜 V W`: the external tensor product of `V` and `W`.
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

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {M N : Type*} [TopologicalSpace M]
  [TopologicalSpace N]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  (W : N → Type*) [∀ y, AddCommGroup (W y)] [∀ y, Module 𝕜 (W y)]

/-- The **external tensor product** `V ⊠ W` of bundles `V` over `M` and `W` over `N`: the bundle
over `M × N` whose fibre over `(x, y)` is `V x ⊗[𝕜] W y`. It is the tensor product of the
pullbacks of `V` and `W` along the two projections. -/
abbrev ExternalTensor (p : M × N) : Type _ :=
  ((ContinuousMap.fst : C(M × N, M)) *ᵖ V) p ⊗[𝕜] ((ContinuousMap.snd : C(M × N, N)) *ᵖ W) p

/-- The fibres of an external tensor product carry their module topology. For finite-rank
bundles this is the topology of the fibre as a finite-dimensional vector space. -/
instance (p : M × N) : TopologicalSpace (ExternalTensor 𝕜 V W p) :=
  moduleTopology 𝕜 _

instance (p : M × N) : IsModuleTopology 𝕜 (ExternalTensor 𝕜 V W p) :=
  ⟨rfl⟩

variable {𝕜 V W} in
/-- Scalars pull out of both factors of a pure tensor in a fibre of `V ⊠ W`:
`(a • v) ⊗ (b • w) = (a * b) • (v ⊗ w)` for `v ∈ V x` and `w ∈ W y`. The fibres of `V ⊠ W` are
tensor products of fibres of pullback bundles, so this form applies directly to vectors of `V x`
and `W y`, where `TensorProduct.smul_tmul_smul` would need the scalar actions on the pullback
fibres. -/
theorem ExternalTensor.smul_tmul_smul {p : M × N} (a b : 𝕜) (v : V p.1) (w : W p.2) :
    ((a • v) ⊗ₜ[𝕜] (b • w) : ExternalTensor 𝕜 V W p) =
      (a * b) • (v ⊗ₜ[𝕜] w : ExternalTensor 𝕜 V W p) := by
  let m := TensorProduct.mk 𝕜 (((ContinuousMap.fst : C(M × N, M)) *ᵖ V) p)
    (((ContinuousMap.snd : C(M × N, N)) *ᵖ W) p)
  calc ((a • v) ⊗ₜ[𝕜] (b • w) : ExternalTensor 𝕜 V W p) = a • m v (b • w) :=
        LinearMap.map_smul₂ m a v (b • w)
    _ = a • b • m v w := congrArg (a • ·) (map_smul (m v) b w)
    _ = (a * b) • (v ⊗ₜ[𝕜] w : ExternalTensor 𝕜 V W p) := smul_smul a b _

end Defs

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module 𝕜 (W y)] [∀ y, TopologicalSpace (W y)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (t' : Trivialization G (π G W)) [MemTrivializationAtlas t']

/-- The trivialization of the external tensor product `V ⊠ W` over `U × U'` induced by
trivializations of `V` over `U` and of `W` over `U'`: it reads `v ⊗ w` as `t v ⊗ t' w`. -/
def externalTensor :
    Trivialization (ProjectiveTensor 𝕜 F G) (π (ProjectiveTensor 𝕜 F G) (ExternalTensor 𝕜 V W)) :=
  (t.pullback (ContinuousMap.fst : C(M × N, M))).tensorProduct 𝕜
    (t'.pullback (ContinuousMap.snd : C(M × N, N)))

instance : MemTrivializationAtlas (t.externalTensor 𝕜 t') :=
  inferInstanceAs (MemTrivializationAtlas
    ((t.pullback (ContinuousMap.fst : C(M × N, M))).tensorProduct 𝕜
      (t'.pullback (ContinuousMap.snd : C(M × N, N)))))

variable {𝕜 t t'}

/-- The base set of the trivialization of `V ⊠ W` induced by `t` and `t'` is the product of their
base sets. -/
@[simp]
theorem baseSet_externalTensor : (t.externalTensor 𝕜 t').baseSet = t.baseSet ×ˢ t'.baseSet := by
  rw [externalTensor, baseSet_tensorProduct, prod_baseSet_eq_inter_pullback]

/-- Over the product of the base sets, the trivialization of `V ⊠ W` induced by `t` and `t'`
reads the pure tensor `v ⊗ w` of vectors `v ∈ V x` and `w ∈ W y` as `t v ⊗ t' w`. -/
@[simp]
theorem externalTensor_apply_mk_tmul {p : M × N} (hp : p ∈ t.baseSet ×ˢ t'.baseSet) (v : V p.1)
    (w : W p.2) :
    t.externalTensor 𝕜 t' ⟨p, (v ⊗ₜ[𝕜] w : ExternalTensor 𝕜 V W p)⟩ =
      (p, ProjectiveTensor.mk ((t ⟨p.1, v⟩).2 ⊗ₜ[𝕜] (t' ⟨p.2, w⟩).2)) := by
  refine (Bundle.Trivialization.tensorProduct_apply_mk_tmul
    (e₁ := t.pullback (ContinuousMap.fst : C(M × N, M)))
    (e₂ := t'.pullback (ContinuousMap.snd : C(M × N, N)))
    (by rwa [prod_baseSet_eq_inter_pullback] at hp) v w).trans ?_
  -- The pulled-back trivializations read `v` and `w` as `t` and `t'` do at `p.1` and `p.2`.
  simp only [pullback_apply]
  rfl

/-- Over the product of the base sets, the trivialization of `V ⊠ W` induced by `t` and `t'`
reads the pure tensor `v ⊗ w` of model vectors back as `t⁻¹ v ⊗ t'⁻¹ w`. -/
theorem externalTensor_symm_apply_tmul {p : M × N} (hp : p ∈ t.baseSet ×ˢ t'.baseSet) (v : F)
    (w : G) :
    (t.externalTensor 𝕜 t').symm p (ProjectiveTensor.mk (v ⊗ₜ[𝕜] w)) =
      (t.symm p.1 v ⊗ₜ[𝕜] t'.symm p.2 w : ExternalTensor 𝕜 V W p) := by
  rw [externalTensor, Bundle.Trivialization.tensorProduct_symm_apply_tmul
      (by rwa [prod_baseSet_eq_inter_pullback] at hp),
    symm_pullback t ContinuousMap.fst (b := p) (by rw [ContinuousMap.fst_apply]; exact hp.1),
    symm_pullback t' ContinuousMap.snd (b := p) (by rw [ContinuousMap.snd_apply]; exact hp.2)]
  -- The fibres `(fst *ᵖ V) p` and `(snd *ᵖ W) p` of the pullbacks are `V p.1` and `W p.2` by
  -- definition, so both sides are the same pure tensor.
  rfl

end Bundle.Trivialization

namespace ContMDiffSection

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {J : ModelWithCorners 𝕜 EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {W : N → Type*} [∀ y, AddCommGroup (W y)] [∀ y, Module 𝕜 (W y)] [∀ y, TopologicalSpace (W y)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [∀ y, IsTopologicalAddGroup (W y)] [∀ y, ContinuousSMul 𝕜 (W y)]

/-- The **external tensor product** `(x, y) ↦ s x ⊗ t y` of a `C^n` section `s` of `V` over `M`
and a `C^n` section `t` of `W` over `N`, a `C^n` section of `V ⊠ W` over `M × N`. -/
def externalTensor (s : Cₛ^n⟮I; F, V⟯) (t : Cₛ^n⟮J; G, W⟯) :
    Cₛ^n⟮I.prod J; ProjectiveTensor 𝕜 F G, ExternalTensor 𝕜 V W⟯ where
  toFun p := s p.1 ⊗ₜ[𝕜] t p.2
  -- The pullbacks of `s` and `t` along the projections are `p ↦ s p.1` and `p ↦ t p.2`; the
  -- closing `rfl` unfolds `ContMDiffMap.fst p` to `p.1` and `ContMDiffMap.snd p` to `p.2`.
  contMDiff_toFun := ContMDiff.tmul_section (E₁ := (ContinuousMap.fst : C(M × N, M)) *ᵖ V)
    (E₂ := (ContinuousMap.snd : C(M × N, N)) *ᵖ W)
    ((s.pullback (ContMDiffMap.fst : C^n⟮I.prod J, M × N; I, M⟯)).contMDiff.congr fun p ↦ by
      rw [pullback_apply]; rfl)
    ((t.pullback (ContMDiffMap.snd : C^n⟮I.prod J, M × N; J, N⟯)).contMDiff.congr fun p ↦ by
      rw [pullback_apply]; rfl)

/-- The external tensor product of sections is `(x, y) ↦ s x ⊗ t y`. -/
@[simp]
theorem externalTensor_apply (s : Cₛ^n⟮I; F, V⟯) (t : Cₛ^n⟮J; G, W⟯) (p : M × N) :
    s.externalTensor t p = (s p.1 ⊗ₜ[𝕜] t p.2 : ExternalTensor 𝕜 V W p) :=
  (rfl)

/-- The external tensor product of sections is supported in the product of the supports. -/
theorem tsupport_externalTensor_subset (s : Cₛ^n⟮I; F, V⟯) (t : Cₛ^n⟮J; G, W⟯) :
    (s.externalTensor t).tsupport ⊆ s.tsupport ×ˢ t.tsupport := by
  rw [tsupport_def, tsupport_def, tsupport_def, ← closure_prod_eq]
  refine closure_mono fun p hp ↦ ?_
  rw [Set.mem_ofPred_eq] at hp
  rw [Set.mem_prod, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ hp ?_, fun h ↦ hp ?_⟩
  · rw [externalTensor_apply, h]
    exact TensorProduct.zero_tmul _ _
  · rw [externalTensor_apply, h]
    exact TensorProduct.tmul_zero _ _

end ContMDiffSection
