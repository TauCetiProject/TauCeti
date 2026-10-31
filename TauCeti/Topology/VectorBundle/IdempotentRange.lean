/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic

/-!
# The image bundle of a continuous family of projections

Let `p : B → F →L[𝕜] F` be a continuous family of idempotent operators on a Banach space `F`.
The ranges `(p x).range` form a subbundle of the trivial bundle `B × F`: this file gives
their total space the topology of a subspace of `B × F`
(`TauCeti.isEmbedding_totalSpace_range`) and shows that it is a topological vector bundle, with
any model fibre `F'` that is isomorphic to every range (`TauCeti.rangeFiberBundle` and
`TauCeti.rangeVectorBundle`). Complementary projections `p` and `1 - p` give complementary
subbundles, whose direct sum is the trivial bundle (`TauCeti.rangeProdRangeOneSubHomeomorph`).
These image bundles are the bundle side of the correspondence between vector bundles and
projections used in topological K-theory: classically, over a compact Hausdorff base every
finite-rank vector bundle is isomorphic to one of them, a fact not proved here.

The local trivialization at `x₀` uses the intertwining operator
`U x = p x * p x₀ + (1 - p x) * (1 - p x₀)`, which satisfies `p x * U x = U x * p x₀` and
equals `1` at `x₀`. Where `U x` is invertible, which is an open condition containing `x₀`, it
carries the range of `p x₀` isomorphically onto the range of `p x`
(`TauCeti.rangeTrivialization`). In particular the ranges of nearby projections are isomorphic
(`TauCeti.eventually_nonempty_continuousLinearEquiv_range`), so the rank of a continuous family
of projections is locally constant (`TauCeti.isLocallyConstant_finrank_range`). No compactness,
separation or finite-dimensionality is assumed of the base or the fibres.

## Main definitions

* `TauCeti.instTopologicalSpaceTotalSpaceRange`: the subspace topology on the total space of the
  ranges of a family of operators.
* `TauCeti.rangeTrivialization`: the local trivialization at `x₀` given by the intertwining
  operator, read through an isomorphism of the model fibre with the range of `p x₀`.
* `TauCeti.rangeFiberBundle`: the fibre bundle structure on the ranges of a continuous family of
  projections.
* `TauCeti.rangeProdRangeOneSubHomeomorph`: the direct sum of the ranges of `p` and `1 - p` is
  homeomorphic to `B × F`, linearly on each fibre.

## Main results

* `TauCeti.rangeVectorBundle`: the ranges of a continuous family of projections form a
  topological vector bundle.
* `TauCeti.isLocallyConstant_finrank_range`: the rank of a continuous family of projections is
  locally constant.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6, for the
  intertwining operator of a pair of projections.
* M. F. Atiyah, *K-Theory*, Benjamin (1967), Chapter I, for sub-bundles of trivial bundles and
  their complements.
* The subspace topology, the chart and atlas, and the vector-bundle packaging follow the
  subbundles of distributions in `TauCeti/Geometry/Manifold/Distribution/VectorBundle.lean`:
  `TauCeti.instTopologicalSpaceTotalSpaceDistribution`,
  `TauCeti.IsDistributionFrameOn.trivialization`, `TauCeti.IsContMDiffDistribution.fiberBundle`
  and `TauCeti.IsContMDiffDistribution.vectorBundle`.
-/

public section

open Bundle Set Topology Filter
open scoped Ring

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

section Topology

/-- The total space of the ranges of a family `p` of operators on `F`, the pairs `(x, v)` with
`v ∈ (p x).range`, carries the topology of a subspace of `B × F`. The model-fibre
parameter `F'` of `Bundle.TotalSpace` plays no role. -/
instance instTopologicalSpaceTotalSpaceRange (F' : Type*) (p : B → F →L[𝕜] F) :
    TopologicalSpace (TotalSpace F' fun x ↦ (p x).range) :=
  .induced (fun v ↦ (v.proj, (v.2 : F))) inferInstance

/-- The total space of the ranges of a family of operators on `F` is embedded in `B × F`. -/
theorem isEmbedding_totalSpace_range (F' : Type*) (p : B → F →L[𝕜] F) :
    IsEmbedding fun v : TotalSpace F' (fun x ↦ (p x).range) ↦ (v.proj, (v.2 : F)) := by
  refine ⟨⟨rfl⟩, fun ⟨x, v⟩ ⟨y, w⟩ h ↦ ?_⟩
  obtain rfl : x = y := congrArg Prod.fst h
  exact congrArg (TotalSpace.mk x) (Subtype.ext (congrArg Prod.snd h))

/-- The projection of the total space of the ranges of a family of operators is continuous. -/
theorem continuous_proj_totalSpace_range (F' : Type*) (p : B → F →L[𝕜] F) :
    Continuous (TotalSpace.proj : TotalSpace F' (fun x ↦ (p x).range) → B) :=
  continuous_fst.comp (isEmbedding_totalSpace_range F' p).continuous

end Topology

section Trivialization

variable {p : B → F →L[𝕜] F}

/-- The operator `p x * p x₀ + (1 - p x) * (1 - p x₀)`, which intertwines `p x₀` with `p x`. -/
private def intertwiner (p : B → F →L[𝕜] F) (x₀ x : B) : F →L[𝕜] F :=
  p x * p x₀ + (1 - p x) * (1 - p x₀)

private theorem continuous_intertwiner (hp : Continuous p) (x₀ : B) :
    Continuous (intertwiner p x₀) :=
  (hp.mul continuous_const).add ((continuous_const.sub hp).mul continuous_const)

omit [TopologicalSpace B] in
private theorem intertwiner_self (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ : B) :
    intertwiner p x₀ x₀ = 1 := by
  rw [intertwiner, (hidem x₀).eq, (hidem x₀).one_sub.eq, add_sub_cancel]

omit [TopologicalSpace B] in
private theorem mul_intertwiner (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ x : B) :
    p x * intertwiner p x₀ x = intertwiner p x₀ x * p x₀ := by
  have h := (hidem x).eq
  have h₀ := (hidem x₀).eq
  simp only [intertwiner, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, ← mul_assoc, h]
  simp only [mul_assoc, h₀]
  abel

omit [TopologicalSpace B] in
/-- Where the intertwiner is invertible, its inverse intertwines `p x` with `p x₀`. -/
private theorem inverse_intertwiner_mul (hidem : ∀ x, IsIdempotentElem (p x)) {x₀ x : B}
    (hx : IsUnit (intertwiner p x₀ x)) :
    (intertwiner p x₀ x)⁻¹ʳ * p x = p x₀ * (intertwiner p x₀ x)⁻¹ʳ := by
  rw [← mul_one ((intertwiner p x₀ x)⁻¹ʳ * p x), ← Ring.mul_inverse_cancel _ hx, ← mul_assoc,
    mul_assoc _ (p x), mul_intertwiner hidem, ← mul_assoc, Ring.inverse_mul_cancel _ hx, one_mul]

omit [TopologicalSpace B] in
private theorem apply_intertwiner (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ x : B) (v : F) :
    p x (intertwiner p x₀ x v) = intertwiner p x₀ x (p x₀ v) :=
  congr($(mul_intertwiner hidem x₀ x) v)

omit [TopologicalSpace B] in
private theorem inverse_intertwiner_apply (hidem : ∀ x, IsIdempotentElem (p x)) {x₀ x : B}
    (hx : IsUnit (intertwiner p x₀ x)) (v : F) :
    (intertwiner p x₀ x)⁻¹ʳ (p x v) = p x₀ ((intertwiner p x₀ x)⁻¹ʳ v) :=
  congr($(inverse_intertwiner_mul hidem hx) v)

omit [TopologicalSpace B] in
private theorem intertwiner_inverse_apply {x₀ x : B} (hx : IsUnit (intertwiner p x₀ x)) (v : F) :
    intertwiner p x₀ x ((intertwiner p x₀ x)⁻¹ʳ v) = v :=
  congr($(Ring.mul_inverse_cancel _ hx) v)

omit [TopologicalSpace B] in
private theorem inverse_intertwiner_apply_intertwiner {x₀ x : B}
    (hx : IsUnit (intertwiner p x₀ x)) (v : F) :
    (intertwiner p x₀ x)⁻¹ʳ (intertwiner p x₀ x v) = v :=
  congr($(Ring.inverse_mul_cancel _ hx) v)

omit [TopologicalSpace B] in
private theorem apply_coe_range (hidem : ∀ x, IsIdempotentElem (p x)) {x : B}
    (w : (p x).range) : p x w = w :=
  LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap (hidem x)) |>.mp w.2

omit [TopologicalSpace B] in
/-- The intertwiner maps the range of `p x₀` back to itself after its inverse and `p x`. -/
private theorem apply_inverse_apply_intertwiner (hidem : ∀ x, IsIdempotentElem (p x)) {x₀ x : B}
    (hx : IsUnit (intertwiner p x₀ x)) (w : (p x₀).range) :
    p x₀ ((intertwiner p x₀ x)⁻¹ʳ (p x (intertwiner p x₀ x w))) = w := by
  rw [apply_intertwiner hidem, apply_coe_range hidem, inverse_intertwiner_apply_intertwiner hx,
    apply_coe_range hidem]

omit [TopologicalSpace B] in
private theorem apply_intertwiner_apply_inverse (hidem : ∀ x, IsIdempotentElem (p x)) {x₀ x : B}
    (hx : IsUnit (intertwiner p x₀ x)) (w : (p x).range) :
    p x (intertwiner p x₀ x (p x₀ ((intertwiner p x₀ x)⁻¹ʳ w))) = w := by
  rw [← inverse_intertwiner_apply hidem hx, apply_coe_range hidem, intertwiner_inverse_apply hx,
    apply_coe_range hidem]

omit [TopologicalSpace B] in
private theorem isUnit_intertwiner_self (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ : B) :
    IsUnit (intertwiner p x₀ x₀) := by
  rw [intertwiner_self hidem]
  exact isUnit_one

variable [CompleteSpace F]

/-- The base set of the trivialization at `x₀`: the points at which the intertwiner is
invertible. -/
private theorem isOpen_setOf_isUnit_intertwiner (hp : Continuous p) (x₀ : B) :
    IsOpen {x | IsUnit (intertwiner p x₀ x)} :=
  Units.isOpen.preimage (continuous_intertwiner hp x₀)

private theorem continuousOn_inverse_intertwiner (hp : Continuous p) (x₀ : B) :
    ContinuousOn (fun x ↦ (intertwiner p x₀ x)⁻¹ʳ) {x | IsUnit (intertwiner p x₀ x)} :=
  fun _ hx ↦ ((NormedRing.inverse_continuousAt hx.unit).comp_of_eq
    (continuous_intertwiner hp x₀).continuousAt hx.unit_spec.symm).continuousWithinAt

variable (hp : Continuous p) (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ : B)
  (φ : F' ≃L[𝕜] (p x₀).range)

/-- The local trivialization at `x₀` of the ranges of a continuous family `p` of projections.
Over the open set where the intertwiner `U x = p x * p x₀ + (1 - p x) * (1 - p x₀)` is
invertible, a vector `w` in the range of `p x` is sent to `φ.symm (U x)⁻¹ w`, using an
isomorphism `φ` of the model fibre with the range of `p x₀`. -/
noncomputable def rangeTrivialization :
    Trivialization F' (π F' fun x ↦ (p x).range) where
  toFun v := (v.proj, φ.symm ((p x₀).rangeRestrict
    ((intertwiner p x₀ v.proj)⁻¹ʳ v.2)))
  invFun q := TotalSpace.mk' F' (E := fun x ↦ (p x).range) q.1
    ((p q.1).rangeRestrict (intertwiner p x₀ q.1 (φ q.2)))
  source := π F' (fun x ↦ (p x).range) ⁻¹' {x | IsUnit (intertwiner p x₀ x)}
  target := {x | IsUnit (intertwiner p x₀ x)} ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' := by
    rintro ⟨x, w⟩ (hx : IsUnit (intertwiner p x₀ x))
    refine congrArg (TotalSpace.mk x) (Subtype.ext ?_)
    simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_codRestrict_apply]
    exact apply_intertwiner_apply_inverse hidem hx w
  right_inv' := by
    rintro ⟨x, v⟩ ⟨hx, -⟩
    simp only [TotalSpace.mk', ContinuousLinearMap.coe_codRestrict_apply]
    refine Prod.ext rfl ((φ.symm_apply_eq).mpr (Subtype.ext ?_))
    exact apply_inverse_apply_intertwiner hidem hx (φ v)
  open_source := (isOpen_setOf_isUnit_intertwiner hp x₀).preimage
    (continuous_proj_totalSpace_range F' p)
  open_target := (isOpen_setOf_isUnit_intertwiner hp x₀).prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_proj_totalSpace_range F' p).continuousOn.prodMk ?_
    refine (φ.symm.continuous.comp ((p x₀).rangeRestrict).continuous).comp_continuousOn ?_
    exact ((continuousOn_inverse_intertwiner hp x₀).comp
      (continuous_proj_totalSpace_range F' p).continuousOn fun _ hv ↦ hv).clm_apply
      (continuous_snd.comp (isEmbedding_totalSpace_range F' p).continuous).continuousOn
  continuousOn_invFun := by
    refine Continuous.continuousOn ((isEmbedding_totalSpace_range F' p).continuous_iff.mpr ?_)
    exact continuous_fst.prodMk ((hp.comp continuous_fst).clm_apply
      ((continuous_intertwiner hp x₀ |>.comp continuous_fst).clm_apply
        (continuous_subtype_val.comp (φ.continuous.comp continuous_snd))))
  baseSet := {x | IsUnit (intertwiner p x₀ x)}
  open_baseSet := isOpen_setOf_isUnit_intertwiner hp x₀
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The trivialization at `x₀` is defined over a neighbourhood of `x₀`. -/
theorem mem_baseSet_rangeTrivialization :
    x₀ ∈ (rangeTrivialization hp hidem x₀ φ).baseSet :=
  isUnit_intertwiner_self hidem x₀

/-- A point lies in the base set of the trivialization at `x₀` exactly when the intertwiner
`p x * p x₀ + (1 - p x) * (1 - p x₀)` is invertible. -/
theorem mem_baseSet_rangeTrivialization_iff {x : B} :
    x ∈ (rangeTrivialization hp hidem x₀ φ).baseSet ↔
      IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀)) :=
  Iff.rfl

/- The two evaluation lemmas below are not `simp` lemmas, so that the evaluations at the base point
`x₀` stay in simp normal form. -/

/-- The trivialization at `x₀` sends a vector `w` of the range of `p x` to `φ.symm (U x)⁻¹ w`,
where `U x = p x * p x₀ + (1 - p x) * (1 - p x₀)`. -/
theorem rangeTrivialization_apply (v : TotalSpace F' fun x ↦ (p x).range) :
    rangeTrivialization hp hidem x₀ φ v = (v.proj, φ.symm ((p x₀).rangeRestrict
      ((p v.proj * p x₀ + (1 - p v.proj) * (1 - p x₀))⁻¹ʳ v.2))) :=
  (rfl)

/-- The inverse of the trivialization at `x₀` sends `(x, v)` to `U x (φ v)` in the range of `p x`,
where `U x = p x * p x₀ + (1 - p x) * (1 - p x₀)`. -/
theorem rangeTrivialization_symm_apply (x : B) (v : F') :
    (rangeTrivialization hp hidem x₀ φ).toOpenPartialHomeomorph.symm (x, v) =
      ⟨x, (p x).rangeRestrict ((p x * p x₀ + (1 - p x) * (1 - p x₀)) (φ v))⟩ :=
  (rfl)

/-- At the base point `x₀`, the trivialization reads a vector of the range of `p x₀` through `φ`. -/
@[simp]
theorem rangeTrivialization_apply_self (w : (p x₀).range) :
    rangeTrivialization hp hidem x₀ φ ⟨x₀, w⟩ = (x₀, φ.symm w) := by
  refine Prod.ext rfl (congrArg φ.symm (Subtype.ext ?_))
  rw [ContinuousLinearMap.coe_codRestrict_apply, intertwiner_self hidem, Ring.inverse_one,
    one_apply_eq_self, apply_coe_range hidem]

/-- At the base point `x₀`, the inverse of the trivialization is `φ`. -/
@[simp]
theorem rangeTrivialization_symm_apply_self (v : F') :
    (rangeTrivialization hp hidem x₀ φ).toOpenPartialHomeomorph.symm (x₀, v) = ⟨x₀, φ v⟩ := by
  refine congrArg (TotalSpace.mk x₀) (Subtype.ext ?_)
  rw [ContinuousLinearMap.coe_codRestrict_apply, intertwiner_self hidem, one_apply_eq_self,
    apply_coe_range hidem]

/-- The trivialization at `x₀` is linear on every fibre. -/
instance isLinear_rangeTrivialization : (rangeTrivialization hp hidem x₀ φ).IsLinear 𝕜 where
  linear x _ := (φ.symm.toLinearMap ∘ₗ ((p x₀).rangeRestrict).toLinearMap ∘ₗ
    ((intertwiner p x₀ x)⁻¹ʳ).toLinearMap ∘ₗ ((p x).range).subtype).isLinear

/-- The coordinate changes between two trivializations given by intertwiners are continuous on
the intersection of their base sets. -/
theorem continuousOn_coordChangeL_rangeTrivialization (x₁ : B)
    (φ₁ : F' ≃L[𝕜] (p x₁).range) :
    ContinuousOn (fun x ↦ ((rangeTrivialization hp hidem x₀ φ).coordChangeL 𝕜
      (rangeTrivialization hp hidem x₁ φ₁) x : F' →L[𝕜] F'))
      ((rangeTrivialization hp hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp hidem x₁ φ₁).baseSet) := by
  -- On the overlap the coordinate change is an explicit composite of continuous operator families.
  have hc : ContinuousOn (fun x ↦ (φ₁.symm : (p x₁).range →L[𝕜] F') ∘L
      (p x₁).rangeRestrict ∘L (intertwiner p x₁ x)⁻¹ʳ ∘L
      p x ∘L intertwiner p x₀ x ∘L ((p x₀).range).subtypeL ∘L
      (φ : F' →L[𝕜] (p x₀).range))
      ((rangeTrivialization hp hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp hidem x₁ φ₁).baseSet) :=
    continuousOn_const.clm_comp (continuousOn_const.clm_comp
      (((continuousOn_inverse_intertwiner hp x₁).mono inter_subset_right).clm_comp
      (hp.continuousOn.clm_comp ((continuous_intertwiner hp x₀).continuousOn.clm_comp
      continuousOn_const))))
  refine hc.congr fun x hx ↦ ContinuousLinearMap.ext fun v ↦ ?_
  exact (rangeTrivialization hp hidem x₀ φ).coordChangeL_apply' (R := 𝕜) _ hx v

end Trivialization

section FiberBundle

variable [CompleteSpace F] {p : B → F →L[𝕜] F}

/-- **The ranges of a continuous family of projections form a fibre bundle**, the topology of
its total space being that of a subspace of `B × F`, with any model fibre `F'` isomorphic to all
the ranges. The trivializations are those of `TauCeti.rangeTrivialization`. Use this definition
as a local instance. -/
@[instance_reducible]
noncomputable def rangeFiberBundle (hp : Continuous p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜] (p x).range)) :
    FiberBundle F' fun x ↦ (p x).range where
  totalSpaceMk_isInducing' x := by
    rw [← (isEmbedding_totalSpace_range F' p).isInducing.of_comp_iff]
    exact (isInducing_prodMkRight x).comp IsInducing.subtypeVal
  trivializationAtlas' :=
    {e | ∃ (x₀ : B) (φ : F' ≃L[𝕜] (p x₀).range), rangeTrivialization hp hidem x₀ φ = e}
  trivializationAt' x := rangeTrivialization hp hidem x (hF' x).some
  mem_baseSet_trivializationAt' x := mem_baseSet_rangeTrivialization hp hidem x _
  trivialization_mem_atlas' x := ⟨x, _, rfl⟩

/-- The trivializations of `rangeFiberBundle` are the intertwiner trivializations. -/
theorem mem_trivializationAtlas_rangeFiberBundle_iff (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) (hF' : ∀ x, Nonempty (F' ≃L[𝕜] (p x).range))
    (e : Trivialization F' (π F' fun x ↦ (p x).range)) :
    letI := rangeFiberBundle hp hidem hF'
    e ∈ trivializationAtlas F' (fun x ↦ (p x).range) ↔
      ∃ (x₀ : B) (φ : F' ≃L[𝕜] (p x₀).range), rangeTrivialization hp hidem x₀ φ = e :=
  Iff.rfl

/-- **The ranges of a continuous family of projections form a vector bundle**: with the subspace
topology of `B × F`, the intertwiner trivializations are linear, with continuous coordinate
changes. -/
theorem rangeVectorBundle (hp : Continuous p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜] (p x).range)) :
    letI := rangeFiberBundle hp hidem hF'
    VectorBundle 𝕜 F' fun x ↦ (p x).range := by
  let := rangeFiberBundle hp hidem hF'
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro e he
    obtain ⟨x₀, φ, rfl⟩ := (mem_trivializationAtlas_rangeFiberBundle_iff hp hidem hF' e).mp he.out
    infer_instance
  · intro e e' he he'
    obtain ⟨x₀, φ, rfl⟩ := (mem_trivializationAtlas_rangeFiberBundle_iff hp hidem hF' e).mp he.out
    obtain ⟨x₁, φ₁, rfl⟩ :=
      (mem_trivializationAtlas_rangeFiberBundle_iff hp hidem hF' e').mp he'.out
    exact continuousOn_coordChangeL_rangeTrivialization hp hidem x₀ φ x₁ φ₁

end FiberBundle

section Complement

variable {p : B → F →L[𝕜] F}

/-- **Complementary projections give complementary subbundles of the trivial bundle.** For a
continuous family of projections `p`, adding the components is a homeomorphism from the total
space of the direct sum of the ranges of `p x` and of `1 - p x` onto `B × F`, over the identity of
`B` and linear on each fibre. The model-fibre parameters `F'` and `F''` play no role. -/
def rangeProdRangeOneSubHomeomorph (F' F'' : Type*) (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) :
    TotalSpace (F' × F'') ((fun x ↦ (p x).range) ×ᵇ fun x ↦ (1 - p x).range) ≃ₜ B × F where
  toFun v := (v.proj, (v.2.1 : F) + v.2.2)
  invFun q := ⟨q.1, ((p q.1).rangeRestrict q.2, (1 - p q.1).rangeRestrict q.2)⟩
  left_inv := by
    rintro ⟨x, w₁, w₂⟩
    have h₂ : (1 - p x) w₂ = w₂ := apply_coe_range (fun x ↦ (hidem x).one_sub) w₂
    have h₂' := congr($((hidem x).mul_one_sub_self) (w₂ : F))
    rw [mul_apply_eq_comp, h₂, zero_apply] at h₂'
    refine congrArg (TotalSpace.mk x) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · simp only [map_add, Submodule.coe_add, ContinuousLinearMap.coe_codRestrict_apply,
        apply_coe_range hidem w₁, h₂', add_zero]
    · simp only [map_add, Submodule.coe_add, ContinuousLinearMap.coe_codRestrict_apply,
        sub_apply, one_apply_eq_self, apply_coe_range hidem w₁, h₂']
      abel
  right_inv := by
    rintro ⟨x, v⟩
    simp only [ContinuousLinearMap.coe_codRestrict_apply, sub_apply,
      one_apply_eq_self, add_sub_cancel]
  continuous_toFun := by
    have hD := (FiberBundle.Prod.isInducing_diag F' (fun x ↦ (p x).range) F''
      fun x ↦ (1 - p x).range).continuous
    have h₁ := (isEmbedding_totalSpace_range F' p).continuous.comp (continuous_fst.comp hD)
    have h₂ := (isEmbedding_totalSpace_range F'' (fun x ↦ 1 - p x)).continuous.comp
      (continuous_snd.comp hD)
    exact (continuous_fst.comp h₁).prodMk ((continuous_snd.comp h₁).add (continuous_snd.comp h₂))
  continuous_invFun := by
    refine (FiberBundle.Prod.isInducing_diag F' (fun x ↦ (p x).range) F''
      fun x ↦ (1 - p x).range).continuous_iff.mpr (Continuous.prodMk ?_ ?_)
    · exact (isEmbedding_totalSpace_range F' p).continuous_iff.mpr
        (continuous_fst.prodMk ((hp.comp continuous_fst).clm_apply continuous_snd))
    · exact (isEmbedding_totalSpace_range F'' (fun x ↦ 1 - p x)).continuous_iff.mpr
        (continuous_fst.prodMk (((continuous_const.sub hp).comp continuous_fst).clm_apply
          continuous_snd))

variable (F' F'' : Type*) (hp : Continuous p) (hidem : ∀ x, IsIdempotentElem (p x))

/- The two evaluation lemmas are not `simp` lemmas: `simp` would rewrite the coercion of `1 - p x`
inside the type of the total space, so their left-hand sides are not in simp normal form. -/

/-- The homeomorphism adds the two components of a vector of the direct sum. -/
theorem rangeProdRangeOneSubHomeomorph_apply
    (v : TotalSpace (F' × F'') ((fun x ↦ (p x).range) ×ᵇ fun x ↦ (1 - p x).range)) :
    rangeProdRangeOneSubHomeomorph F' F'' hp hidem v = (v.proj, (v.2.1 : F) + v.2.2) :=
  (rfl)

/-- The inverse homeomorphism splits a vector of `F` by the projections `p x` and `1 - p x`. -/
theorem rangeProdRangeOneSubHomeomorph_symm_apply (q : B × F) :
    (rangeProdRangeOneSubHomeomorph F' F'' hp hidem).symm q =
      ⟨q.1, ((p q.1).rangeRestrict q.2, (1 - p q.1).rangeRestrict q.2)⟩ :=
  (rfl)

end Complement

section Rank

variable [CompleteSpace F] {p : B → F →L[𝕜] F}

/-- The ranges of nearby projections in a continuous family are isomorphic. -/
theorem eventually_nonempty_continuousLinearEquiv_range (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ : B) :
    ∀ᶠ x in 𝓝 x₀, Nonempty ((p x₀).range ≃L[𝕜] (p x).range) := by
  filter_upwards [(isOpen_setOf_isUnit_intertwiner hp x₀).mem_nhds
    (isUnit_intertwiner_self hidem x₀)] with x hx
  exact ⟨.equivOfInverse ((p x).rangeRestrict ∘L intertwiner p x₀ x ∘L (p x₀).range.subtypeL)
    ((p x₀).rangeRestrict ∘L (intertwiner p x₀ x)⁻¹ʳ ∘L (p x).range.subtypeL)
    (fun w ↦ Subtype.ext (apply_inverse_apply_intertwiner hidem hx w))
    (fun w ↦ Subtype.ext (apply_intertwiner_apply_inverse hidem hx w))⟩

/-- **The rank of a continuous family of projections is locally constant.** -/
theorem isLocallyConstant_finrank_range (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) :
    IsLocallyConstant fun x ↦ Module.finrank 𝕜 ((p x).range) :=
  (IsLocallyConstant.iff_eventually_eq _).mpr fun x₀ ↦
    (eventually_nonempty_continuousLinearEquiv_range hp hidem x₀).mono fun _ ⟨e⟩ ↦
      e.toLinearEquiv.finrank_eq.symm

end Rank

end TauCeti
