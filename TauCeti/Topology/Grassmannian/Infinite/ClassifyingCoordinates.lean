/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Finsupp.Flatten
public import TauCeti.Topology.Grassmannian.Infinite.Tautological
public import TauCeti.Topology.VectorBundle.WeightedCoordinates
public import Mathlib.Topology.Homotopy.Basic
import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.VectorBundle.TrivialEmbedding

/-!
# Classifying coordinates for finite-rank vector bundles

A family of fibrewise linear injections `j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)` forms **classifying
coordinates** (`TauCeti.IsClassifyingCoordinates`) when every ambient coordinate is continuous on
`TotalSpace F E` and, locally on the base, coordinates are uniformly supported in `Finset.range N`.
Unlike mere pointwise finite support in `ℕ →₀ 𝕜`, uniform local containment in `Finset.range N`
makes `x ↦ LinearMap.range (j x)` factor locally through `finiteGrassmannian 𝕜 k N`, ensuring
continuity into the direct-limit topology of `infiniteGrassmannian 𝕜 k` (`classifyContinuousMap`,
`classifyTautologicalHomeomorph`) and feeding `Classification.lean`. Over a complete nontrivially
normed `ℝ`-algebra field, every finite-rank vector bundle over a paracompact normal base admits
classifying coordinates (`exists_isClassifyingCoordinates`), while over `RCLike 𝕜`, given
`PartitionOfUnity`-weighted orthonormal frame coordinates flatten directly into
`IsClassifyingCoordinates` (`PartitionOfUnity.isClassifyingCoordinates_weightedFrameCoordinates`)
via `IsClassifyingCoordinates.of_flattenFinsupp`.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5; A. Hatcher, *Vector Bundles*, §1.2.
-/

public noncomputable section

open Bundle Set Function Filter _root_.Finsupp
open scoped Topology unitInterval

namespace TauCeti
/-- Fibrewise linear injections `j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)` with continuous coordinates on
`TotalSpace F E` and locally uniform initial-segment support bounds. -/
structure IsClassifyingCoordinates (𝕜 : Type*) [Semiring 𝕜] [TopologicalSpace 𝕜]
    {X : Type*} [TopologicalSpace X] (F : Type*) (E : X → Type*) [∀ x, AddCommMonoid (E x)]
    [∀ x, Module 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)]
    (j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)) : Prop where
  /-- Every ambient coordinate is continuous on the total space. -/
  continuous_coord : ∀ m : ℕ, Continuous fun p : TotalSpace F E ↦ j p.proj p.snd m
  /-- Locally on the base, all fibre vectors have coordinates supported in a fixed `range N`. -/
  locally_supported : ∀ x : X, ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ v : E y, (j y v).support ⊆ Finset.range N
  /-- On every fibre, the coordinate map is injective. -/
  injective : ∀ x : X, Injective (j x)

namespace IsClassifyingCoordinates
section Operations
variable {𝕜 : Type*} [Semiring 𝕜] [TopologicalSpace 𝕜] {X Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] {F G : Type*} {E : X → Type*} [∀ x, AddCommMonoid (E x)]
  [∀ x, Module 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)] {E' : X → Type*}
  [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜 (E' x)] [TopologicalSpace (TotalSpace G E')]
  {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)}
/-- Pulling back classifying coordinates along `f : C(Y, X)`. -/
theorem pullback (hj : IsClassifyingCoordinates 𝕜 F E j) (f : C(Y, X)) :
    IsClassifyingCoordinates 𝕜 F ((f : Y → X) *ᵖ E) (fun y ↦ j (f y)) where
  continuous_coord m := (hj.continuous_coord m).comp (Pullback.continuous_lift F E (f : Y → X))
  locally_supported y :=
    let ⟨N, hN⟩ := hj.locally_supported (f y); ⟨N, f.continuous.continuousAt.preimage_mem_nhds hN⟩
  injective y := hj.injective (f y)

/-- Precomposing classifying coordinates with a continuous family of fibrewise linear injections. -/
theorem compLinearMap (hj : IsClassifyingCoordinates 𝕜 F E j) (Φ : ∀ x, E' x →ₗ[𝕜] E x)
    (hΦ_inj : ∀ x, Injective (Φ x)) (hΦ_cont : Continuous fun p : TotalSpace G E' ↦
      TotalSpace.mk' F (E := E) p.proj (Φ p.proj p.snd)) :
    IsClassifyingCoordinates 𝕜 G E' (fun x ↦ (j x).comp (Φ x)) where
  continuous_coord m := (hj.continuous_coord m).comp hΦ_cont
  locally_supported x :=
    let ⟨N, hN⟩ := hj.locally_supported x; ⟨N, hN.mono fun y hy v ↦ hy (Φ y v)⟩
  injective x := (hj.injective x).comp (hΦ_inj x)

/-- Postcomposing classifying coordinates with an injective linear endomorphism of `ℕ →₀ 𝕜`. -/
theorem postcomp [IsTopologicalSemiring 𝕜] (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hπ : Continuous (π F E)) (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) :
    IsClassifyingCoordinates 𝕜 F E (fun x ↦ φ.comp (j x)) where
  continuous_coord m := continuous_iff_continuousAt.2 fun p₀ ↦ by
    obtain ⟨N, hN⟩ := hj.locally_supported p₀.proj
    have hlin : Continuous ((lapply (R := 𝕜) (M := 𝕜) m).comp (φ.comp (coordinateInclusion N))) :=
      LinearMap.continuous_on_pi _
    refine (hlin.comp (continuous_pi fun r : Fin N ↦
      hj.continuous_coord r.val)).continuousAt.congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt.preimage_mem_nhds hN] with q hq
    dsimp only [comp_def, LinearMap.comp_apply, lapply_apply]
    rw [coordinateInclusion_of_support_subset_range (hq q.snd)]
  locally_supported x :=
    let ⟨N, hN⟩ := hj.locally_supported x; let ⟨M, hM⟩ := exists_support_map_subset_range φ N
    ⟨M, hN.mono fun y hy v ↦ hM (j y v) (hy v)⟩
  injective x := hφ.comp (hj.injective x)

/-- Flattening fibrewise injective block coordinates `E x →ₗ[𝕜] (ℕ →₀ (Fin r → 𝕜))` with
continuous coordinate entries and local `Finset.range` block support yields
`IsClassifyingCoordinates`. -/
theorem of_flattenFinsupp {r : ℕ} {j₀ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ (Fin r → 𝕜))}
    (hcont : ∀ (n : ℕ) (i : Fin r), Continuous fun p : TotalSpace F E ↦ j₀ p.proj p.snd n i)
    (hsupp : ∀ x : X, ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ v : E y, (j₀ y v).support ⊆ Finset.range N)
    (hinj : ∀ x : X, Injective (j₀ x)) :
    IsClassifyingCoordinates 𝕜 F E (fun x ↦ (flattenFinsupp 𝕜 r).comp (j₀ x)) where
  continuous_coord m := by
    by_cases hr : m.unpair.2 < r
    · exact (hcont m.unpair.1 ⟨m.unpair.2, hr⟩).congr fun _ ↦ by simp [hr]
    · exact (continuous_const (y := (0 : 𝕜))).congr fun _ ↦ by simp [hr]
  locally_supported x := let ⟨N, hN⟩ := hsupp x
    ⟨max N r ^ 2, hN.mono fun y hy v ↦ support_flattenFinsupp_subset_range (hy v)⟩
  injective x := (flattenFinsupp_injective 𝕜 r).comp (hinj x)
end Operations

open finiteGrassmannian (frameSpan toInfinite coe_toInfinite coe_frameSpan
  continuous_toInfinite continuous_frameSpan)
open infiniteGrassmannian (Tautological tautologicalEquiv val_tautologicalEquiv_symm
  continuous_totalSpace_iff)
section Classify
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}

section Basic
variable (hj : IsClassifyingCoordinates 𝕜 F E j) (hk : Module.finrank 𝕜 F = k)
include hj hk
/-- The image `LinearMap.range (j x)` of classifying coordinates has cardinal rank `k`. -/
theorem rank_range_eq (x : X) : Module.rank 𝕜 (LinearMap.range (j x)) = k := by
  let e := (VectorBundle.continuousLinearEquivAt 𝕜 F E x).symm.toLinearEquiv.trans
    (LinearEquiv.ofInjective (j x) (hj.injective x))
  have : Module.Finite 𝕜 (LinearMap.range (j x)) := Module.Finite.equiv e
  exact (Module.finrank_eq_rank 𝕜 _).symm.trans (congrArg Nat.cast (e.symm.finrank_eq.trans hk))

/-- Classifying coordinates send `x` to `LinearMap.range (j x)` in `infiniteGrassmannian 𝕜 k`. -/
def classify (x : X) : infiniteGrassmannian 𝕜 k := ⟨LinearMap.range (j x), hj.rank_range_eq hk x⟩
@[simp] theorem coe_classify (x : X) : (hj.classify hk x).val = LinearMap.range (j x) := (rfl)

private theorem frameSpan_localFrame_eq (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (b : Module.Basis (Fin k) 𝕜 F) {N : ℕ} {y : X} (hy : y ∈ e.baseSet)
    (hsupp : ∀ v : E y, (j y v).support ⊆ Finset.range N) :
    ∃ hlin : LinearIndependent 𝕜 (fun (i : Fin k) (r : Fin N) ↦ j y (e.symm y (b i)) r.val),
      toInfinite (frameSpan ⟨_, hlin⟩) = hj.classify hk y := by
  let f : Fin k → Fin N → 𝕜 := fun i r ↦ j y (e.symm y (b i)) r.val
  let L : F →ₗ[𝕜] (ℕ →₀ 𝕜) := (j y).comp (e.linearEquivAt 𝕜 y hy).symm.toLinearMap
  have hL : Injective L := (hj.injective y).comp (e.linearEquivAt 𝕜 y hy).symm.injective
  have hinc (i : Fin k) : coordinateInclusion (R := 𝕜) N (f i) = L (b i) :=
    coordinateInclusion_of_support_subset_range (hsupp _)
  have hlin : LinearIndependent 𝕜 f := Fintype.linearIndependent_iff.2 fun g hg ↦
    Fintype.linearIndependent_iff.1 b.linearIndependent g <| hL <| by
      rw [map_sum, map_zero, ← (coordinateInclusion (R := 𝕜) N).map_zero, ← hg, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, map_smul, hinc]
  have hspan : Submodule.map (coordinateInclusion (R := 𝕜) N) (Submodule.span 𝕜 (range f)) =
      LinearMap.range L := by
    rw [Submodule.map_span, ← range_comp, (funext hinc : _ ∘ f = L ∘ b), range_comp,
      ← Submodule.map_span, b.span_eq, Submodule.map_top]
  refine ⟨hlin, Subtype.ext ?_⟩
  rw [coe_toInfinite, coe_frameSpan, hj.coe_classify hk y]
  exact hspan.trans (LinearMap.range_comp_of_range_eq_top (j y) (LinearEquiv.range _))

/-- The classifying map of `IsClassifyingCoordinates` is continuous. -/
@[fun_prop] theorem continuous_classify : Continuous (hj.classify hk) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  let e := trivializationAt F E x₀; let b := Module.finBasisOfFinrankEq 𝕜 F hk
  obtain ⟨N, hN⟩ := hj.locally_supported x₀
  obtain ⟨U, hU_sub, hU_open, hx₀U⟩ := mem_nhds_iff.1 <|
    inter_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E x₀)) hN
  have hraw :
      Continuous (fun (z : U) (i : Fin k) (r : Fin N) ↦ j z.val (e.symm z.val (b i)) r.val) :=
    continuous_pi fun i ↦ continuous_pi fun r ↦ continuous_iff_continuousAt.2 fun z ↦
      (hj.continuous_coord r.val).continuousAt.comp <|
        ContinuousAt.comp (f := fun u : U ↦ (u.val, b i))
        (e.continuousOn_symm.continuousAt
          ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨(hU_sub z.property).1, mem_univ _⟩))
        (continuous_subtypeVal.prodMk continuous_const).continuousAt
  have hspec (z : U) := hj.frameSpan_localFrame_eq hk e b (hU_sub z.property).1
      (hU_sub z.property).2
  exact (continuousOn_iff_continuous_domRestrict.2 <|
    (continuous_toInfinite.comp (continuous_frameSpan.comp
      (hraw.subtype_mk fun z ↦ (hspec z).1))).congr fun z ↦ by
        simpa using (hspec z).2).continuousAt (hU_open.mem_nhds hx₀U)

-- Exposed so pullback fibres along `classifyContinuousMap` reduce to `Tautological 𝕜 k (classify)`.
/-- The classifying map bundled as `C(X, infiniteGrassmannian 𝕜 k)`. -/
@[expose] def classifyContinuousMap : C(X, infiniteGrassmannian 𝕜 k) :=
  ⟨hj.classify hk, hj.continuous_classify hk⟩
@[simp] theorem classifyContinuousMap_apply (x : X) :
    hj.classifyContinuousMap hk x = hj.classify hk x := (rfl)
end Basic

section Pullback
variable {Y : Type*} [TopologicalSpace Y] (hj : IsClassifyingCoordinates 𝕜 F E j)
  (f : C(Y, X)) (hk : Module.finrank 𝕜 F = k)
@[simp] theorem classify_pullback (y : Y) :
    (hj.pullback f).classify hk y = hj.classify hk (f y) :=
  Subtype.ext (((hj.pullback f).coe_classify hk y).trans (hj.coe_classify hk (f y)).symm)
@[simp] theorem classifyContinuousMap_pullback :
    (hj.pullback f).classifyContinuousMap hk = (hj.classifyContinuousMap hk).comp f :=
  ContinuousMap.ext (hj.classify_pullback f hk)
end Pullback

section CompLinearEquiv
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {E' : X → Type*} [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜 (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G E')]
  [FiberBundle G E'] [VectorBundle 𝕜 G E'] (hj : IsClassifyingCoordinates 𝕜 F E j)
  (Φ : ∀ x, E' x ≃ₗ[𝕜] E x) (hΦ_cont : Continuous fun p : TotalSpace G E' ↦
    TotalSpace.mk' F (E := E) p.proj (Φ p.proj p.snd))
  (hk : Module.finrank 𝕜 F = k) (hk' : Module.finrank 𝕜 G = k)
/-- Precomposing with fibrewise linear equivalences preserves `classify` pointwise. -/
theorem classify_compLinearEquiv (x : X) :
    (hj.compLinearMap (E' := E') (fun x ↦ (Φ x).toLinearMap) (fun x ↦ (Φ x).injective)
      hΦ_cont).classify hk' x = hj.classify hk x :=
  Subtype.ext <| by
    rw [coe_classify, coe_classify, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
/-- Precomposing with fibrewise linear equivalences preserves `classifyContinuousMap`. -/
theorem classifyContinuousMap_compLinearEquiv :
    (hj.compLinearMap (E' := E') (fun x ↦ (Φ x).toLinearMap) (fun x ↦ (Φ x).injective)
      hΦ_cont).classifyContinuousMap hk' = hj.classifyContinuousMap hk :=
  ContinuousMap.ext (hj.classify_compLinearEquiv Φ hΦ_cont hk hk')
end CompLinearEquiv

section Postcomp
variable (hj : IsClassifyingCoordinates 𝕜 F E j) (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
  (hk : Module.finrank 𝕜 F = k)
@[simp] theorem classify_postcomp (x : X) :
    (hj.postcomp (FiberBundle.continuous_proj F E) φ hφ).classify hk x =
      infiniteGrassmannian.map φ hφ (hj.classify hk x) :=
  Subtype.ext (by simp [LinearMap.range_comp])
@[simp] theorem classifyContinuousMap_postcomp :
    (hj.postcomp (FiberBundle.continuous_proj F E) φ hφ).classifyContinuousMap hk =
      (infiniteGrassmannian.mapContinuousMap φ hφ).comp (hj.classifyContinuousMap hk) :=
  ContinuousMap.ext (hj.classify_postcomp φ hφ hk)
end Postcomp

section Equiv
variable [CompleteSpace 𝕜] (hj : IsClassifyingCoordinates 𝕜 F E j) (hk : Module.finrank 𝕜 F = k)
/-- Over a complete scalar field, `j x` identifies `E x` with `Tautological 𝕜 k (classify hk x)`. -/
def classifyTautologicalEquiv (x : X) : E x ≃L[𝕜] Tautological 𝕜 k (hj.classify hk x) :=
  let e₁ := VectorBundle.continuousLinearEquivAt 𝕜 F E x
  e₁.trans (e₁.symm.toLinearEquiv.trans ((LinearEquiv.ofInjective (j x) (hj.injective x)).trans
    (tautologicalEquiv 𝕜 k (hj.classify hk x)).symm)).toContinuousLinearEquiv
@[simp] theorem val_classifyTautologicalEquiv (x : X) (v : E x) :
    (hj.classifyTautologicalEquiv hk x v).val = j x v := by
  let e₁ := VectorBundle.continuousLinearEquivAt 𝕜 F E x
  exact (val_tautologicalEquiv_symm (hj.classify hk x) _).trans <|
    (LinearEquiv.ofInjective_apply (f := j x) (h := hj.injective x) (e₁.symm (e₁ v))).trans
      (congrArg (j x) (e₁.symm_apply_apply v))
end Equiv
end Classify

section ClassifyHomeomorph
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}
  (hj : IsClassifyingCoordinates 𝕜 F E j) (hk : Module.finrank 𝕜 F = k)
/-- Bundle homeomorphism from `TotalSpace F E` to the pullback of `Tautological 𝕜 k` along
`hj.classifyContinuousMap hk`. -/
def classifyTautologicalHomeomorph : TotalSpace F E ≃ₜ TotalSpace (Fin k → 𝕜)
    ((hj.classifyContinuousMap hk : _ → _) *ᵖ (Tautological 𝕜 k)) :=
  bundleHomeomorph (hj.classifyTautologicalEquiv hk) <| Bundle.Pullback.continuous_iff.2
    ⟨FiberBundle.continuous_proj F E, continuous_totalSpace_iff.2
      ⟨(hj.classifyContinuousMap hk).continuous.comp (FiberBundle.continuous_proj F E),
        fun m ↦ (hj.continuous_coord m).congr fun p ↦
          DFunLike.congr_fun (hj.val_classifyTautologicalEquiv hk p.proj p.snd).symm m⟩⟩
@[simp] theorem classifyTautologicalHomeomorph_apply (p : TotalSpace F E) :
    hj.classifyTautologicalHomeomorph hk p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (hj.classifyTautologicalEquiv hk p.proj p.snd) :=
  bundleHomeomorph_apply _ _ p
@[simp] theorem classifyTautologicalHomeomorph_symm_apply (p : TotalSpace (Fin k → 𝕜)
      ((hj.classifyContinuousMap hk : _ → _) *ᵖ (Tautological 𝕜 k))) :
    (hj.classifyTautologicalHomeomorph hk).symm p =
      TotalSpace.mk' F p.proj ((hj.classifyTautologicalEquiv hk p.proj).symm p.snd) :=
  bundleHomeomorph_symm_apply _ _ p
end ClassifyHomeomorph

section Cylinder
section Algebraic
variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜] {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  (j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜))
/-- Linearly interpolated coordinates `(1 - t) • j₀ x + t • j₁ x` on the cylinder bundle. -/
def cylinderLinearMap (p : I × X) :
    (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) p →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  (1 - algebraMap ℝ 𝕜 p.1.val) • j₀ p.2 + (algebraMap ℝ 𝕜 p.1.val) • j₁ p.2
theorem cylinderLinearMap_def (p : I × X) : cylinderLinearMap j₀ j₁ p =
    (1 - algebraMap ℝ 𝕜 p.1.val) • j₀ p.2 + (algebraMap ℝ 𝕜 p.1.val) • j₁ p.2 := (rfl)
@[simp] theorem cylinderLinearMap_apply (p : I × X)
    (v : (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) p) : cylinderLinearMap j₀ j₁ p v =
      (1 - algebraMap ℝ 𝕜 p.1.val) • j₀ p.2 v + (algebraMap ℝ 𝕜 p.1.val) • j₁ p.2 v := (rfl)
@[simp] theorem cylinderLinearMap_zero (x : X) : cylinderLinearMap j₀ j₁ (0, x) = j₀ x := by
  rw [cylinderLinearMap_def]; dsimp only; rw [Icc.coe_zero, map_zero, sub_zero, one_smul, zero_smul,
    add_zero]
@[simp] theorem cylinderLinearMap_one (x : X) : cylinderLinearMap j₀ j₁ (1, x) = j₁ x := by
  rw [cylinderLinearMap_def]; dsimp only; rw [Icc.coe_one, map_one, sub_self, zero_smul, one_smul,
    zero_add]
end Algebraic

/-- Linearly interpolating classifying coordinates `j₀, j₁` yields classifying coordinates on
`I × X` whenever `(1 - t) • j₀ x + t • j₁ x` is fibrewise injective. -/
theorem cylinderInterp {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
    [Algebra ℝ 𝕜] [ContinuousSMul ℝ 𝕜] {X : Type*} [TopologicalSpace X] {F : Type*}
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)] {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hinj : ∀ (t : I) (x : X),
      Injective ((1 - algebraMap ℝ 𝕜 t.val) • j₀ x + (algebraMap ℝ 𝕜 t.val) • j₁ x)) :
    IsClassifyingCoordinates 𝕜 F (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E)
      (cylinderLinearMap j₀ j₁) where
  continuous_coord m := by
    let s : I × X → X := (ContinuousMap.snd : C(I × X, X))
    have ht : Continuous fun q : TotalSpace F (s *ᵖ E) ↦ algebraMap ℝ 𝕜 q.proj.1.val :=
      ((continuous_subtypeVal.comp (continuous_fst.comp (Pullback.continuous_proj F E s))).smul
        (continuous_const (y := (1 : 𝕜)))).congr fun _ ↦ (Algebra.algebraMap_eq_smul_one _).symm
    exact ((((continuous_const (y := (1 : 𝕜))).sub ht).mul
      ((hj₀.continuous_coord m).comp (Pullback.continuous_lift F E s))).add
        (ht.mul ((hj₁.continuous_coord m).comp (Pullback.continuous_lift F E s)))).congr
          fun ⟨⟨t, x⟩, v⟩ ↦ ((add_apply ((1 - algebraMap ℝ 𝕜 t.val) • j₀ x v) _ m).trans
            (congrArg₂ (· + ·) (smul_eq_mul _ _) (smul_eq_mul _ _))).symm
  locally_supported p := by
    obtain ⟨N₀, hN₀⟩ := hj₀.locally_supported p.2; obtain ⟨N₁, hN₁⟩ := hj₁.locally_supported p.2
    refine ⟨max N₀ N₁, mem_of_superset
      (continuous_snd.continuousAt.preimage_mem_nhds (inter_mem hN₀ hN₁))
      fun q hq v r hr ↦ Finset.mem_range.2 ?_⟩
    rcases Finset.mem_union.1 (support_add hr) with h | h
    · exact (Finset.mem_range.1 (hq.1 v (support_smul h))).trans_le (le_max_left _ _)
    · exact (Finset.mem_range.1 (hq.2 v (support_smul h))).trans_le (le_max_right _ _)
  injective p := hinj p.1 p.2

section Homotopy
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {X : Type*}
  [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}
  (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
  (hinj : ∀ (t : I) (x : X),
    Injective ((1 - algebraMap ℝ 𝕜 t.val) • j₀ x + (algebraMap ℝ 𝕜 t.val) • j₁ x))
  (hk : Module.finrank 𝕜 F = k)
include hinj
/-- Homotopy between `hj₀.classifyContinuousMap hk` and `hj₁.classifyContinuousMap hk` from
fibrewise injective linear combinations `(1 - t) • j₀ + t • j₁`. -/
def homotopyOfLinearCombinationInjective :
    (hj₀.classifyContinuousMap hk).Homotopy (hj₁.classifyContinuousMap hk) where
  toContinuousMap := (hj₀.cylinderInterp hj₁ hinj).classifyContinuousMap hk
  map_zero_left x := Subtype.ext <| ((hj₀.cylinderInterp hj₁ hinj).coe_classify hk (0, x)).trans <|
    (congrArg LinearMap.range (cylinderLinearMap_zero j₀ j₁ x)).trans (hj₀.coe_classify hk x).symm
  map_one_left x := Subtype.ext <| ((hj₀.cylinderInterp hj₁ hinj).coe_classify hk (1, x)).trans <|
    (congrArg LinearMap.range (cylinderLinearMap_one j₀ j₁ x)).trans (hj₁.coe_classify hk x).symm
@[simp] theorem homotopyOfLinearCombinationInjective_toContinuousMap :
    (hj₀.homotopyOfLinearCombinationInjective hj₁ hinj hk).toContinuousMap =
      (hj₀.cylinderInterp hj₁ hinj).classifyContinuousMap hk := (rfl)
@[simp] theorem homotopyOfLinearCombinationInjective_apply (p : I × X) :
    hj₀.homotopyOfLinearCombinationInjective hj₁ hinj hk p =
      (hj₀.cylinderInterp hj₁ hinj).classify hk p := (rfl)
/-- The underlying submodule of `homotopyOfLinearCombinationInjective` at `(t, x)` is the range of
the interpolated linear map `(1 - t) • j₀ x + t • j₁ x`. -/
theorem coe_homotopyOfLinearCombinationInjective (t : I) (x : X) :
    (hj₀.homotopyOfLinearCombinationInjective hj₁ hinj hk (t, x)).val =
      LinearMap.range ((1 - algebraMap ℝ 𝕜 t.val) • j₀ x + (algebraMap ℝ 𝕜 t.val) • j₁ x) :=
  (congrArg Subtype.val <|
    hj₀.homotopyOfLinearCombinationInjective_apply hj₁ hinj hk (t, x)).trans <|
    ((hj₀.cylinderInterp hj₁ hinj).coe_classify hk (t, x)).trans <|
      congrArg LinearMap.range (cylinderLinearMap_def j₀ j₁ (t, x))
end Homotopy
end Cylinder
end IsClassifyingCoordinates

section PartitionBlock
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : X → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
section Helpers
variable (ρ : PartitionOfUnity ℕ X univ) (e : ℕ → Trivialization F (π F E))
  [∀ n, (e n).IsLinear 𝕜] {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F)
private def partitionBlockCoordinates (x : X) : E x →ₗ[𝕜] (ℕ →₀ (Fin r → 𝕜)) where
  toFun v := ofSupportFinite
    (fun n ↦ b.equivFun (weightedTrivializationMap e (fun m y ↦ algebraMap ℝ 𝕜 (ρ m y)) x v n))
    ((ρ.locallyFinite.point_finite x).subset fun n hn ↦ by
      contrapose hn; simp only [mem_ofPred_eq, mem_support, not_not] at hn; simp [hn])
  map_add' _ _ := by ext n i; simp
  map_smul' _ _ := by ext n i; simp
@[simp] private theorem partitionBlockCoordinates_apply (x : X) (v : E x) (n : ℕ) :
    partitionBlockCoordinates ρ e b x v n =
      b.equivFun (weightedTrivializationMap e (fun m y ↦ algebraMap ℝ 𝕜 (ρ m y)) x v n) := (rfl)
private theorem continuous_partitionBlockCoordinates_apply [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hρ : ρ.IsSubordinate fun n ↦ (e n).baseSet) (n : ℕ) (i : Fin r) :
    Continuous fun p : TotalSpace F E ↦ partitionBlockCoordinates ρ e b p.proj p.snd n i :=
  (continuous_apply i).comp <| b.equivFun.toLinearMap.continuous_of_finiteDimensional.comp <|
    (continuous_apply n).comp <|
      continuous_weightedTrivializationMap e (fun m y ↦ algebraMap ℝ 𝕜 (ρ m y))
        (fun m ↦ (continuous_algebraMap ℝ 𝕜).comp (ρ m).continuous) fun m ↦
          (tsupport_comp_subset (map_zero (algebraMap ℝ 𝕜)) (ρ m)).trans (hρ m)
end Helpers

/-- Every finite-rank vector bundle over a paracompact normal base over a complete nontrivially
normed `ℝ`-algebra field admits `IsClassifyingCoordinates`. -/
theorem exists_isClassifyingCoordinates [CompleteSpace 𝕜] [ParacompactSpace X] [NormalSpace X]
    [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F E] :
    ∃ j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜), IsClassifyingCoordinates 𝕜 F E j := by
  obtain ⟨e, he_lin, he_cov, -⟩ := exists_countable_locallyFinite_trivialization 𝕜 (F := F) (E := E)
  have := he_lin; let b := Module.finBasis 𝕜 F
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun n ↦ (e n).baseSet) (fun n ↦ (e n).open_baseSet) (fun x _ ↦ he_cov.ge (mem_univ x))
  refine ⟨_, IsClassifyingCoordinates.of_flattenFinsupp
    (continuous_partitionBlockCoordinates_apply ρ e b hρ) (fun x ↦ ?_) fun x ↦ ?_⟩
  · classical
    refine ⟨(ρ.fintsupport x).sup id + 1, (ρ.eventually_finsupport_subset x).mono fun y hy v n hn ↦
      Finset.mem_range.2 <| Nat.lt_succ_of_le <| Finset.le_sup (f := id) <| hy <|
        (ρ.mem_finsupport y).2 fun (h0 : ρ n y = 0) ↦ mem_support_iff.1 hn (by simp [h0])⟩
  · obtain ⟨n, hn⟩ := ρ.exists_pos (mem_univ x)
    have hwn : algebraMap ℝ 𝕜 (ρ n x) ≠ 0 := (map_ne_zero (algebraMap ℝ 𝕜)).2 hn.ne'
    exact fun _ _ h ↦ weightedTrivializationMap_injective e (fun m y ↦ algebraMap ℝ 𝕜 (ρ m y))
      ((tsupport_comp_subset (map_zero (algebraMap ℝ 𝕜)) (ρ n)).trans (hρ n)
        (subset_tsupport _ hwn))
      hwn (funext fun m ↦ b.equivFun.injective (congrArg (· m) h))
end PartitionBlock

/-- Square-root-weighted orthonormal block coordinates (`PartitionOfUnity.weightedFrameCoordinates`)
flatten directly to `IsClassifyingCoordinates`. -/
theorem _root_.PartitionOfUnity.isClassifyingCoordinates_weightedFrameCoordinates
    {𝕜 X F V : Type*} [RCLike 𝕜] [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] {E : X → Type*}
    [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
    [∀ x, InnerProductSpace 𝕜 (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    [ContinuousFiberNorm F E] {r : ℕ} (ρ : PartitionOfUnity ℕ X univ)
    (e : ℕ → Trivialization F (π F E)) [∀ n, (e n).IsLinear 𝕜]
    (he : ∀ n, {x | 0 < ρ n x} ⊆ (e n).baseSet) (c : Module.Basis (Fin r) 𝕜 F)
    (b : OrthonormalBasis (Fin r) 𝕜 V) :
    let coords : V ≃ₗ[𝕜] (Fin r → 𝕜) :=
      b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (Fin r → 𝕜))
    IsClassifyingCoordinates 𝕜 F E fun x ↦ (flattenFinsupp 𝕜 r).comp
      ((mapRange.linearEquiv coords).toLinearMap.comp (ρ.weightedFrameCoordinates e c b x)) :=
  IsClassifyingCoordinates.of_flattenFinsupp
    (fun n i ↦ (continuous_apply i).comp
      (((PiLp.continuous_ofLp 2 _).comp b.repr.continuous).comp
        (ρ.continuous_weightedFrameCoordinates_apply e c b he n)))
    (fun x ↦ let ⟨N, hN⟩ := ρ.locally_support_weightedFrameCoordinates_range c b e x
      ⟨N, hN.mono fun _ hy v ↦ (support_mapRange (hf := map_zero _)).trans (hy v)⟩)
    fun x ↦ (mapRange.linearEquiv _).injective.comp
      (ρ.weightedFrameCoordinates_injective e c b (mem_univ x))
end TauCeti
