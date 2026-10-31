/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Topology.VectorBundle.IdempotentRange
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Analysis.InnerProductSpace.RangeProjection

/-!
# Orthogonal complements of bundle embeddings

A continuous fibrewise injection of a finite-rank vector bundle into a fixed
finite-dimensional inner product space has continuously varying orthogonal range
projections. The ranges of the complementary projections therefore form a vector
bundle, with the subspace topology inherited from the ambient trivial bundle.

The continuity argument reads the injection in one fixed bundle chart near each
base point, and uses `ContinuousAt.starProjection_range`. No norm or metric on the
original fibres is chosen. The complementary bundle uses the intertwiner charts
of `rangeFiberBundle`. Adding the two summands gives the actual total-space
homeomorphism `bundleComplementHomeomorph`, linear on each fibre. This applies
to compact-base finite trivial embeddings after transporting their ambient
coordinate space to `EuclideanSpace`; no compactness is needed once the embedding
is supplied.

This is the orthogonal-complement construction in Hatcher, *Vector Bundles and
K-Theory*, Proposition 1.4, and Atiyah, *K-Theory*, Chapter I, §1.4.
-/

public section

noncomputable section

open Bundle Set Function Topology

namespace TauCeti

variable {𝕜 B F V : Type*} [RCLike 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

local instance : CompleteSpace V := FiniteDimensional.complete 𝕜 V

variable (j : ∀ x, E x →L[𝕜] V)
  (hj : Continuous (fun p : TotalSpace F E ↦ j p.proj p.2))
  (hinj : ∀ x, Injective (j x))

include hj hinj in
/-- The range projection of a continuous fibrewise embedding into a finite-dimensional
inner product space varies continuously, without a metric on the source bundle. -/
theorem continuous_bundle_range_starProjection :
    Continuous (fun x ↦ (j x).range.starProjection) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  let e := trivializationAt F E x₀
  let A : B → F →L[𝕜] V := fun x ↦ (j x).comp (e.symmL 𝕜 x)
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F E x₀
  have hA : ContinuousAt A x₀ := by
    refine continuousAt_clm_apply.2 fun v ↦ ?_
    have hs := e.continuousOn_symm.continuousAt (x := (x₀, v))
      ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hx₀, mem_univ v⟩)
    have h := hj.continuousAt.comp
      (hs.comp (f := fun x : B ↦ (x, v)) (continuousAt_id.prodMk continuousAt_const))
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
    simp only [A, ContinuousLinearMap.comp_apply, e.symmL_apply hx]
    rfl
  have hs (x : B) (hx : x ∈ e.baseSet) : Surjective (e.symmL 𝕜 x) := by
    rw [← e.symm_continuousLinearEquivAt_eq hx]
    exact (e.continuousLinearEquivAt 𝕜 x hx).symm.surjective
  have hAi : Injective (A x₀) := (hinj x₀).comp (by
    simp only [ContinuousLinearMap.coe_coe]
    rw [← e.symm_continuousLinearEquivAt_eq hx₀]
    exact (e.continuousLinearEquivAt 𝕜 x₀ hx₀).symm.injective)
  refine (hA.starProjection_range hAi).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
  have hr : (A x).range = (j x).range :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (hs x hx))
  simp only [hr]

/-- The complementary projection associated to a fibrewise embedding into an inner
product space. Its range is the orthogonal complement of the embedded fibre. -/
def bundleComplementProjection (x : B) : V →L[𝕜] V :=
  1 - (j x).range.starProjection

omit [TopologicalSpace B] in
/-- Complementary projection is orthogonal projection onto the complementary subspace. -/
theorem bundleComplementProjection_eq (x : B) :
    bundleComplementProjection j x = (j x).rangeᗮ.starProjection := by
  exact (Submodule.starProjection_orthogonal' _).symm

include hj hinj in
/-- The complementary projection is continuous in the base point. -/
theorem continuous_bundleComplementProjection : Continuous (bundleComplementProjection j) :=
  continuous_const.sub (continuous_bundle_range_starProjection j hj hinj)

omit [TopologicalSpace B] in
/-- Each complementary projection is idempotent. -/
theorem isIdempotentElem_bundleComplementProjection (x : B) :
    IsIdempotentElem (bundleComplementProjection j x) :=
  ((j x).range.isIdempotentElem_starProjection).one_sub

omit [TopologicalSpace B] in
/-- The complementary projection has precisely the orthogonal complement as range. -/
@[simp]
theorem range_bundleComplementProjection (x : B) :
    (bundleComplementProjection j x).range = (j x).rangeᗮ := by
  rw [bundleComplementProjection_eq, Submodule.range_starProjection]

include hinj in
/-- The complementary fibre has ambient dimension minus the rank of the source bundle. -/
theorem finrank_bundleComplementProjection (x : B) :
    Module.finrank 𝕜 (bundleComplementProjection j x).range =
      Module.finrank 𝕜 V - Module.finrank 𝕜 F := by
  let := VectorBundle.finiteDimensional 𝕜 F E x
  rw [range_bundleComplementProjection,
    LinearMap.finrank_orthogonal_range_of_injective (hinj x)]
  exact congrArg (Module.finrank 𝕜 V - ·)
    (VectorBundle.continuousLinearEquivAt 𝕜 F E x).finrank_eq

private def complementModelEquiv (x : B) :
    (Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 F) → 𝕜) ≃L[𝕜]
      (bundleComplementProjection j x).range :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_fin_fun, finrank_bundleComplementProjection (F := F) j hinj])

/-- The orthogonal complements of the embedded fibres form a fibre bundle. Its total
space carries the subspace topology from `B × V`. Install this as a local instance. -/
@[instance_reducible]
def bundleComplementFiberBundle :
    FiberBundle (Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 F) → 𝕜)
      (fun x ↦ (bundleComplementProjection j x).range) :=
  rangeFiberBundle (continuous_bundleComplementProjection j hj hinj)
    (isIdempotentElem_bundleComplementProjection j)
    (fun x ↦ ⟨complementModelEquiv j hinj x⟩)

include hj hinj in
/-- The complementary fibre bundle is a vector bundle, with the expected finite model. -/
theorem bundleComplementVectorBundle :
    letI := bundleComplementFiberBundle j hj hinj
    VectorBundle 𝕜 (Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 F) → 𝕜)
      (fun x ↦ (bundleComplementProjection j x).range) :=
  rangeVectorBundle (continuous_bundleComplementProjection j hj hinj)
    (isIdempotentElem_bundleComplementProjection j)
    (fun x ↦ ⟨complementModelEquiv j hinj x⟩)

section Splitting

variable [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]

/-- Adding an embedded vector and a vector in its orthogonal complement is a linear
homeomorphism on each fibre. -/
def bundleComplementFiberEquiv (x : B) :
    (E x × (bundleComplementProjection j x).range) ≃L[𝕜] V := by
  let := FiberBundle.t2Space F E x
  let := VectorBundle.finiteDimensional 𝕜 F E x
  let e := (LinearEquiv.ofInjective (j x).toLinearMap (hinj x)).prodCongr
    (LinearEquiv.ofEq _ _ (range_bundleComplementProjection j x))
  exact (e.trans ((j x).range.prodEquivOfIsCompl _
    (j x).range.isCompl_orthogonal)).toContinuousLinearEquiv

@[simp]
theorem bundleComplementFiberEquiv_apply (x : B)
    (v : E x × (bundleComplementProjection j x).range) :
    bundleComplementFiberEquiv (F := F) j hinj x v = j x v.1 + v.2 := (rfl)

include hj hinj in
/-- The embedded bundle plus its orthogonal complement is the ambient trivial bundle.
This isomorphism covers the identity of the base and is linear on each fibre via
`bundleComplementFiberEquiv`. -/
def bundleComplementHomeomorph :
    letI := bundleComplementFiberBundle (F := F) j hj hinj
    letI := bundleComplementVectorBundle (F := F) j hj hinj
    TotalSpace (F × (Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 F) → 𝕜))
      (E ×ᵇ fun x ↦ (bundleComplementProjection j x).range) ≃ₜ B × V := by
  letI := bundleComplementFiberBundle (F := F) j hj hinj
  letI := bundleComplementVectorBundle (F := F) j hj hinj
  let D : B → Type _ := fun x ↦ (bundleComplementProjection j x).range
  let G := Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 F) → 𝕜
  have hd := (FiberBundle.Prod.isInducing_diag F E G D).continuous
  have h₁ := hj.comp (continuous_fst.comp hd)
  have h₂ := (continuous_snd.comp (isEmbedding_totalSpace_range G
    (bundleComplementProjection j)).continuous).comp (continuous_snd.comp hd)
  have h := (Bundle.Trivial.homeomorphProd B V).symm.continuous.comp
    ((FiberBundle.continuous_proj (F × G) (E ×ᵇ D)).prodMk (h₁.add h₂))
  have hc : Continuous (fun p : TotalSpace (F × G) (E ×ᵇ D) ↦
      TotalSpace.mk' V p.proj (bundleComplementFiberEquiv (F := F) j hinj p.proj p.2)) :=
    h.congr (fun _ ↦ rfl)
  exact (bundleHomeomorph (fun x ↦ bundleComplementFiberEquiv (F := F) j hinj x) hc).trans
    (Bundle.Trivial.homeomorphProd B V)

@[simp]
theorem bundleComplementHomeomorph_apply
    (p : TotalSpace (F × (Fin (Module.finrank 𝕜 V - Module.finrank 𝕜 F) → 𝕜))
      (E ×ᵇ fun x ↦ (bundleComplementProjection j x).range)) :
    bundleComplementHomeomorph (F := F) j hj hinj p = (p.proj, j p.proj p.2.1 + p.2.2) := by
  let := bundleComplementFiberBundle (F := F) j hj hinj
  let := bundleComplementVectorBundle (F := F) j hj hinj
  dsimp only [bundleComplementHomeomorph, Homeomorph.trans_apply]
  rw [bundleHomeomorph_apply]
  rfl

/-- The inverse splitting retains the base point and applies the inverse fibre equivalence. -/
@[simp]
theorem bundleComplementHomeomorph_symm_apply (q : B × V) :
    (bundleComplementHomeomorph (F := F) j hj hinj).symm q =
      ⟨q.1, (bundleComplementFiberEquiv (F := F) j hinj q.1).symm q.2⟩ := by
  let := bundleComplementFiberBundle (F := F) j hj hinj
  let := bundleComplementVectorBundle (F := F) j hj hinj
  dsimp only [bundleComplementHomeomorph]
  rw [Homeomorph.symm_trans_apply]
  rw [bundleHomeomorph_symm_apply]
  rfl

end Splitting

end TauCeti
