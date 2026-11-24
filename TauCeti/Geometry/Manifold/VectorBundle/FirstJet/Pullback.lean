/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Pullback and restriction of first-jet bundles

Let `V → M` be a `C^1` vector bundle with model fibre `F` and `f : N → M` a `C^1` map. The first
jet of the pulled-back section `s ∘ f` of `f*V` at `x` only depends on the first jet of `s` at
`f x`: its value is `s (f x)`, and by the chain rule its derivative is the derivative of `s`
composed with the differential `df_x`. This file constructs the resulting map of first jets

`f^* : J¹V_{f x} → J¹(f*V)_x`,  `(v, A) ↦ (v, A ∘ df_x)`,

in the charts and trivializations at `f x` and `x` (the trivialization of `f*V` at `x` is the
pullback of the trivialization of `V` at `f x`), and proves that it is the pullback of first jets.

## Main definitions and results

* `TauCeti.FirstJetBundle.pullbackMap f x`: the continuous linear map
  `J¹V_{f x} →L[𝕜] J¹(f*V)_x`.
* `TauCeti.FirstJetBundle.pullbackMap_jet`: it sends `j¹s(f x)` to `j¹(s ∘ f)(x)` for a section
  `s` differentiable at `f x`.
* `TauCeti.FirstJetBundle.value_pullbackMap` and `TauCeti.FirstJetBundle.pullbackMap_ofDeriv`:
  it lies over the identity of `V_{f x} = (f*V)_x` on values and is precomposition with `df_x` on
  `Hom(T_{f x}M, V_{f x})`, so it is a morphism of the first-jet exact sequences
  `0 → Hom(TM, V) → J¹V → V → 0`.
* `TauCeti.FirstJetBundle.pullbackEquiv`: along a local diffeomorphism at `x`, for instance a
  diffeomorphism `Φ : N ≃ M`, the pullback of first jets is a continuous linear equivalence
  `J¹V_{f x} ≃L[𝕜] J¹(f*V)_x`, since `df_x` is invertible.
* `TauCeti.FirstJetBundle.pullbackMap_snd_of_coe_eq_subtype_val`: for an open set `U ⊆ M`, the
  pullback along the inclusion `U → M` is the identity in coordinates, since the differential of
  the inclusion is the identity. This is the restriction `J¹V_x ≃ J¹(V|_U)_x` of first jets to `U`;
  by `pullbackMap_jet` it sends the first jet of a section to the first jet of its restriction.
* `TauCeti.FirstJetBundle.pullbackMap_id_snd`: the pullback along the identity is the identity in
  coordinates.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.16–12.17.
-/

public section

noncomputable section

open Bundle TopologicalSpace
open scoped Manifold

namespace TauCeti

namespace FirstJetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (J : ModelWithCorners 𝕜 E' H') {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsManifold I 1 M] [IsManifold J 1 N]

section

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommMonoid (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]

section Pullback

variable (f : C^1⟮J, N; I, M⟯)

/-- **The pullback of first jets** `J¹V_{f x} → J¹(f*V)_x` along a `C^1` map `f`: in the charts and
trivializations at `f x` and `x`, it keeps the value coordinate and precomposes the derivative
coordinate with the differential `df_x`. It is the first-jet transformation
`ContinuousLinearMap.firstJetPullback` with identity fibre map and base derivative `df_x`. -/
def pullbackMap (x : N) :
    FirstJetBundle I F V (f x) →L[𝕜] FirstJetBundle J F ((f : N → M) *ᵖ V) x :=
  (ContinuousLinearMap.id 𝕜 F).firstJetPullback 0 (mfderiv J I f x)

variable {I J F}

/-- The pullback of first jets keeps the value coordinate. -/
@[simp]
theorem pullbackMap_fst (x : N) (j : FirstJetBundle I F V (f x)) :
    (pullbackMap I J F f x j).1 = j.1 :=
  congrArg Prod.fst (ContinuousLinearMap.firstJetPullback_apply _ _ _ j)

/-- The pullback of first jets precomposes the derivative coordinate with the differential of
`f`. -/
@[simp]
theorem pullbackMap_snd (x : N) (j : FirstJetBundle I F V (f x)) :
    (pullbackMap I J F f x j).2 = j.2.comp (mfderiv J I f x) :=
  (congrArg Prod.snd (ContinuousLinearMap.firstJetPullback_apply _ _ _ j)).trans (by
    -- What remains is `j.2.comp (mfderiv J I f x)`, with the tangent spaces read as model spaces.
    simp only [ContinuousLinearMap.flip_zero, zero_apply, zero_add, ContinuousLinearMap.id_comp]
    exact (rfl))

/-- **First jets pull back by the chain rule.** The pullback of the first jet of a section `s`
differentiable at `f x` is the first jet at `x` of the pulled-back section `s ∘ f`. -/
theorem pullbackMap_jet {s : ∀ y, V y} {x : N}
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun y ↦ TotalSpace.mk' F y (s y)) (f x)) :
    pullbackMap I J F f x (jet I F s (f x)) =
      jet (V := (f : N → M) *ᵖ V) J F (fun y ↦ s (f y)) x := by
  -- The section `s` read in the trivialization at `f x`.
  set g : M → F := fun y ↦ (trivializationAt F V (f x) ⟨y, s y⟩).2
  have hg : MDifferentiableAt I 𝓘(𝕜, F) g (f x) :=
    ((trivializationAt F V (f x)).mdifferentiableAt_section_iff I s
      (mem_baseSet_trivializationAt F V (f x))).1 hs
  -- The trivialization of `f*V` at `x` is the pullback of the trivialization of `V` at `f x`, so
  -- the pulled-back section reads as `g ∘ f` in it, with value `g (f x)` at `x`.
  have hgf : (fun y ↦ (trivializationAt F ((f : N → M) *ᵖ V) x ⟨y, s (f y)⟩).2) = g ∘ f := by
    simp only [trivializationAt, FiberBundle.pullback_trivializationAt']
    rfl
  refine Prod.ext ((pullbackMap_fst f x _).trans ((jet_fst I F s (f x)).trans
    ((congrFun hgf x).symm.trans (jet_fst (V := (f : N → M) *ᵖ V) J F (fun y ↦ s (f y)) x).symm)))
    ((pullbackMap_snd f x _).trans ?_)
  -- By the chain rule, the derivative of `g ∘ f` at `x` is `dg_{f x} ∘ df_x`.
  have hd := mfderiv_comp x hg (f.contMDiff.mdifferentiableAt one_ne_zero)
  rw [← hgf] at hd
  exact (congrArg (fun A : E →L[𝕜] F ↦ A.comp (mfderiv J I f x))
    (jet_snd_eq_mfderiv I F s (f x))).trans
    (hd.symm.trans (jet_snd_eq_mfderiv (V := (f : N → M) *ᵖ V) J F (fun y ↦ s (f y)) x).symm)

/-- The pullback of first jets lies over the identity of `V_{f x} = (f*V)_x` on values. -/
@[simp]
theorem value_pullbackMap (x : N) (j : FirstJetBundle I F V (f x)) :
    value J F x (pullbackMap I J F f x j) = value I F (f x) j := by
  rw [value_apply, value_apply, pullbackMap_fst]
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt']
  exact (trivializationAt F V (f x)).symm_pullback f (mem_baseSet_trivializationAt F V (f x)) j.1

end Pullback

section LocalDiffeomorph

variable (f : C^1⟮J, N; I, M⟯) {x : N} (hf : IsLocalDiffeomorphAt J I 1 f x)

/-- **The pullback of first jets along a local diffeomorphism** `f` at `x` is a continuous linear
equivalence `J¹V_{f x} ≃L[𝕜] J¹(f*V)_x`: the differential `df_x` is invertible, so precomposition
with it is invertible on the derivative coordinate. This covers diffeomorphisms and the inclusions
of open subsets, along which it is the restriction of first jets. -/
def pullbackEquiv : FirstJetBundle I F V (f x) ≃L[𝕜] FirstJetBundle J F ((f : N → M) *ᵖ V) x :=
  (ContinuousLinearEquiv.refl 𝕜 F).firstJetPullback 0
    (hf.mfderivToContinuousLinearEquiv one_ne_zero)

variable {I J F}

/-- The pullback of first jets along a local diffeomorphism is the pullback of first jets along
the underlying `C^1` map. -/
@[simp]
theorem pullbackEquiv_apply (j : FirstJetBundle I F V (f x)) :
    pullbackEquiv I J F f hf j = pullbackMap I J F f x j :=
  -- The underlying map of `firstJetPullback` of equivalences is `firstJetPullback` of their
  -- underlying maps, here the identity and the differential `df_x`.
  DFunLike.congr_fun (ContinuousLinearEquiv.coe_firstJetPullback (E := E) (E' := E')
    (ContinuousLinearEquiv.refl 𝕜 F) 0 (hf.mfderivToContinuousLinearEquiv one_ne_zero)) j

/-- The inverse of the pullback of first jets along a local diffeomorphism keeps the value
coordinate. -/
@[simp]
theorem pullbackEquiv_symm_apply_fst (j : FirstJetBundle J F ((f : N → M) *ᵖ V) x) :
    ((pullbackEquiv I J F f hf).symm j).1 = j.1 :=
  congrArg Prod.fst (ContinuousLinearEquiv.firstJetPullback_symm_apply _ _ _ j)

/-- The inverse of the pullback of first jets along a local diffeomorphism precomposes the
derivative coordinate with the inverse of the differential of `f`. -/
@[simp]
theorem pullbackEquiv_symm_apply_snd (j : FirstJetBundle J F ((f : N → M) *ᵖ V) x) :
    ((pullbackEquiv I J F f hf).symm j).2 =
      j.2.comp ((hf.mfderivToContinuousLinearEquiv one_ne_zero).symm :
        TangentSpace I (f x) →L[𝕜] TangentSpace J x) := by
  refine (congrArg Prod.snd (ContinuousLinearEquiv.firstJetPullback_symm_apply _ _ _ j)).trans ?_
  simp only [ContinuousLinearMap.flip_zero, zero_apply, sub_zero, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_comp]
  -- What remains is the same composite, with the tangent spaces read as model spaces.
  exact (rfl)

end LocalDiffeomorph

/-- The pullback of first jets along the identity keeps the derivative coordinate. -/
theorem pullbackMap_id_snd (x : M) (j : FirstJetBundle I F V x) :
    (pullbackMap I I F ContMDiffMap.id x j).2 = j.2 :=
  (pullbackMap_snd ContMDiffMap.id x j).trans
    (congrArg (fun A : TangentSpace I x →L[𝕜] TangentSpace I x ↦ j.2.comp A) (mfderiv_id (I := I)))

/-- **Restriction of first jets to an open set** `U ⊆ M` is the identity in coordinates: the
pullback of first jets along the inclusion `U → M` (any `C^1` map `ι` with underlying function
`Subtype.val`), whose differential is the identity, keeps the derivative coordinate. With
`pullbackMap_fst` this identifies the first jets of `V|_U` at `x` with those of `V`, and
`pullbackMap_jet` makes this identification send the first jet of a section to the first jet of its
restriction. -/
theorem pullbackMap_snd_of_coe_eq_subtype_val (U : Opens M) {ι : C^1⟮I, U; I, M⟯}
    (hι : (ι : U → M) = Subtype.val) (x : U) (j : FirstJetBundle I F V (ι x)) :
    (pullbackMap I I F ι x j).2 = j.2 := by
  rw [pullbackMap_snd, hι, Manifold.mfderiv_subtype_val]
  -- The canonical identification of the tangent spaces of `U` and `M` is the identity on vectors.
  exact ContinuousLinearMap.ext fun v ↦
    congrArg j.2 (Manifold.tangentSpaceOpenEquiv_apply (I := I) x v)

end

section Kernel

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

variable {I J F}

/-- On the kernel `Hom(T_{f x}M, V_{f x})` of the first-jet sequence, the pullback of first jets
is precomposition with the differential `df_x`. -/
@[simp]
theorem pullbackMap_ofDeriv (f : C^1⟮J, N; I, M⟯) (x : N)
    (L : TangentSpace I (f x) →L[𝕜] V (f x)) :
    pullbackMap I J F f x (ofDeriv I F (f x) L) =
      ofDeriv (V := (f : N → M) *ᵖ V) J F x (L.comp (mfderiv J I f x)) := by
  -- The trivialization of `f*V` at `x` reads `V_{f x}` as the trivialization of `V` at `f x` does.
  have h := ((trivializationAt F V (f x)).continuousLinearMapAt_pullback (𝕜 := 𝕜) f x).symm
  refine Prod.ext ((pullbackMap_fst f x _).trans
    ((ofDeriv_fst I F (f x) L).trans (ofDeriv_fst J F x _).symm)) ((pullbackMap_snd f x _).trans ?_)
  exact ((congrArg (fun A : E →L[𝕜] F ↦ A.comp (mfderiv J I f x)) (ofDeriv_snd I F (f x) L)).trans
    ((congrArg (fun A : V (f x) →L[𝕜] F ↦ (A.comp L).comp (mfderiv J I f x)) h).trans
      (ContinuousLinearMap.comp_assoc _ _ _))).trans
    (ofDeriv_snd (V := (f : N → M) *ᵖ V) J F x (L.comp (mfderiv J I f x))).symm

end Kernel

end FirstJetBundle

end TauCeti
