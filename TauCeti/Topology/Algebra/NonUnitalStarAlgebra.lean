/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Topological and uniform constructions for non-unital star algebras

This file provides topological closure, pointwise-limit, extensionality, and uniform-extension
constructions for non-unital `⋆`-algebras and non-unital `⋆`-algebra homomorphisms.

## Main results

* `NonUnitalStarSubalgebra.topologicalClosure_coe`: identifies the underlying set of
  `s.topologicalClosure` with `closure (s : Set A)`, matching
  `StarSubalgebra.topologicalClosure_coe`.
* `NonUnitalStarAlgHom.ofTendsto`: constructs a `NonUnitalStarAlgHom` from a pointwise limit of
  non-unital `⋆`-algebra homomorphisms into a Hausdorff topological non-unital `⋆`-algebra.
* `NonUnitalStarAlgHom.ext_of_denseRange`: two continuous non-unital `⋆`-algebra homomorphisms into
  a Hausdorff space that agree along a dense-range map are equal.
* `IsDenseInducing.extendNonUnitalStarAlgHom`: extends a uniformly continuous
  `NonUnitalStarAlgHom` along a dense uniform-inducing `NonUnitalStarAlgHom` into a complete
  Hausdorff topological non-unital `⋆`-algebra, mirroring `IsDenseInducing.extendRingHom`.
-/

public section

open Filter Topology

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
  [NonUnitalSemiring A] [Module R A] [ContinuousStar A]
  [ContinuousConstSMul R A] [IsSemitopologicalSemiring A]

/-- Coercing `s.topologicalClosure` to `Set A` gives the topological closure
`closure (s : Set A)`. -/
@[simp]
theorem topologicalClosure_coe (s : NonUnitalStarSubalgebra R A) :
    (s.topologicalClosure : Set A) = _root_.closure (s : Set A) :=
  (rfl)

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgHom

section OfTendsto

variable {R A B F ι : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
  [TopologicalSpace B] [T2Space B] [ContinuousAdd B] [ContinuousMul B]
  [ContinuousConstSMul R B] [ContinuousStar B]
  [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]
  {l : Filter ι}

/-- Construct a bundled non-unital `⋆`-algebra homomorphism from a pointwise limit of non-unital
`⋆`-algebra homomorphisms along a nontrivial filter. -/
def ofTendsto [l.NeBot] (f : A → B) (g : ι → F)
    (h : ∀ x, Tendsto (fun i ↦ g i x) l (𝓝 (f x))) : A →⋆ₙₐ[R] B where
  toFun := f
  map_zero' := tendsto_nhds_unique (by simpa only [map_zero] using h 0) tendsto_const_nhds
  map_add' x y := tendsto_nhds_unique
    (by simpa only [map_add] using h (x + y)) ((h x).add (h y))
  map_mul' x y := tendsto_nhds_unique
    (by simpa only [map_mul] using h (x * y)) ((h x).mul (h y))
  map_smul' r x := tendsto_nhds_unique
    (by simpa only [map_smul] using h (r • x)) ((h x).const_smul r)
  map_star' x := tendsto_nhds_unique
    (by simpa only [map_star] using h (star x)) (h x).star

@[simp]
theorem coe_ofTendsto [l.NeBot] (f : A → B) (g : ι → F)
    (h : ∀ x, Tendsto (fun i ↦ g i x) l (𝓝 (f x))) :
    ⇑(ofTendsto f g h) = f :=
  (rfl)

/-- Applying `NonUnitalStarAlgHom.ofTendsto` evaluates the limit function `f`. -/
theorem ofTendsto_apply [l.NeBot] (f : A → B) (g : ι → F)
    (h : ∀ x, Tendsto (fun i ↦ g i x) l (𝓝 (f x))) (x : A) :
    ofTendsto f g h x = f x :=
  (rfl)

end OfTendsto

/-- Two continuous non-unital `⋆`-algebra homomorphisms into a Hausdorff space that agree along a
map with dense range are equal. -/
theorem ext_of_denseRange {R A B C : Type*} [Monoid R]
    [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    [TopologicalSpace C] [T2Space C] [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]
    {i : A → B} (dr : DenseRange i) {f g : B →⋆ₙₐ[R] C}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a, f (i a) = g (i a)) : f = g :=
  DFunLike.ext' <| dr.equalizer hf hg (funext h)

end NonUnitalStarAlgHom

section UniformExtension

variable {R A B C : Type*} [Monoid R]
  [UniformSpace A] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [UniformSpace B] [NonUnitalNonAssocSemiring B] [IsTopologicalSemiring B]
  [DistribMulAction R B] [ContinuousConstSMul R B] [Star B] [ContinuousStar B]
  [UniformSpace C] [NonUnitalNonAssocSemiring C] [IsTopologicalSemiring C]
  [DistribMulAction R C] [ContinuousConstSMul R C] [Star C] [ContinuousStar C]
  [T2Space C] [CompleteSpace C]

/-- Extend a uniformly continuous non-unital `⋆`-algebra homomorphism along a dense
uniform-inducing non-unital `⋆`-algebra homomorphism into a complete Hausdorff topological
non-unital `⋆`-algebra. -/
noncomputable def IsDenseInducing.extendNonUnitalStarAlgHom {i : A →⋆ₙₐ[R] B} {f : A →⋆ₙₐ[R] C}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) : B →⋆ₙₐ[R] C where
  toFun := (ue.isDenseInducing dr).extend f
  map_zero' := by
    convert IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 0 <;>
      simp only [map_zero]
  map_add' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x y ↦ dr.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) (fun a b ↦ ?_) x y
    simp_rw [← map_add i, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous,
      ← map_add f]
  map_mul' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x y ↦ dr.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) (fun a b ↦ ?_) x y
    simp_rw [← map_mul i, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous,
      ← map_mul f]
  map_smul' r := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x ↦ dr.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun a ↦ ?_
    simp only [MonoidHom.id_apply]
    rw [← map_smul i, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous,
      map_smul f, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous]
  map_star' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x ↦ dr.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun a ↦ ?_
    rw [← map_star i, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous,
      map_star f, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous]

/-- The dense-inducing extension of a uniformly continuous `NonUnitalStarAlgHom` is uniformly
continuous. -/
theorem IsDenseInducing.uniformContinuous_extendNonUnitalStarAlgHom
    {i : A →⋆ₙₐ[R] B} {f : A →⋆ₙₐ[R] C}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) :
    UniformContinuous (IsDenseInducing.extendNonUnitalStarAlgHom ue dr hf) :=
  uniformContinuous_uniformly_extend ue dr hf

/-- The dense-inducing extension of a uniformly continuous `NonUnitalStarAlgHom` is continuous. -/
@[fun_prop, continuity]
theorem IsDenseInducing.continuous_extendNonUnitalStarAlgHom
    {i : A →⋆ₙₐ[R] B} {f : A →⋆ₙₐ[R] C}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) :
    Continuous (IsDenseInducing.extendNonUnitalStarAlgHom ue dr hf) :=
  (IsDenseInducing.uniformContinuous_extendNonUnitalStarAlgHom ue dr hf).continuous

@[simp]
theorem IsDenseInducing.extendNonUnitalStarAlgHom_apply
    {i : A →⋆ₙₐ[R] B} {f : A →⋆ₙₐ[R] C}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) (a : A) :
    IsDenseInducing.extendNonUnitalStarAlgHom ue dr hf (i a) = f a :=
  IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous a

@[simp]
theorem IsDenseInducing.extendNonUnitalStarAlgHom_comp
    {i : A →⋆ₙₐ[R] B} {f : A →⋆ₙₐ[R] C}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) :
    (IsDenseInducing.extendNonUnitalStarAlgHom ue dr hf).comp i = f :=
  NonUnitalStarAlgHom.ext <| IsDenseInducing.extendNonUnitalStarAlgHom_apply ue dr hf

end UniformExtension
