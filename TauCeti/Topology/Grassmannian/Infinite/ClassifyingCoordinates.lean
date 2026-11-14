/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Infinite.Tautological
public import TauCeti.Topology.VectorBundle.WeightedCoordinates
public import Mathlib.Topology.Homotopy.Basic
import TauCeti.Topology.FiberBundle.Pullback
import Mathlib.Data.Nat.Pairing

/-!
# Classifying coordinates for finite-rank vector bundles

A family of fibrewise linear injections `j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)` forms **classifying
coordinates** (`TauCeti.IsClassifyingCoordinates`) when every ambient coordinate is continuous on
`TotalSpace F E` and, locally on the base, coordinates are supported in a fixed `Finset.range N`.

* `TauCeti.flattenFinsupp`: linear injection `(ℕ →₀ (Fin k → 𝕜)) →ₗ[𝕜] (ℕ →₀ 𝕜)` via `Nat.pair`.
* `TauCeti.IsClassifyingCoordinates`: closure under `pullback`, `compLinearMap`, `postcomp`, and
  linear cylinder interpolation (`cylinderInterp`, `homotopyOfLinearCombinationInjective`), together
  with the induced classifying map `classifyContinuousMap` and bundle homeomorphism
  `classifyTautologicalHomeomorph`.
* `TauCeti.exists_isClassifyingCoordinates` and
  `TauCeti.IsClassifyingCoordinates.of_weightedFrameCoordinates`: existence over paracompact normal
  bases and compatibility with `PartitionOfUnity.weightedFrameCoordinates`.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5, Lemma 5.3 and Theorem 5.6.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.16.
-/

public noncomputable section

open Bundle Set Function Filter _root_.Finsupp
open scoped Topology unitInterval

namespace TauCeti

section FlattenFinsupp

/-- Flatten finitely supported sequences of `k`-tuples `ℕ →₀ (Fin k → 𝕜)` into `ℕ →₀ 𝕜` via
Cantor pairing `Nat.pair` / `Nat.unpair`. -/
def flattenFinsupp (𝕜 : Type*) [Semiring 𝕜] (k : ℕ) :
    (ℕ →₀ (Fin k → 𝕜)) →ₗ[𝕜] (ℕ →₀ 𝕜) where
  toFun f := Finsupp.ofSupportFinite
    (fun m ↦ if h : m.unpair.2 < k then f m.unpair.1 ⟨m.unpair.2, h⟩ else 0) <| by
      refine ((f.support ×ˢ Finset.range k).finite_toSet.image
        (fun p : ℕ × ℕ ↦ Nat.pair p.1 p.2)).subset fun m hm ↦ ?_
      simp only [mem_support, ne_eq] at hm
      split_ifs at hm with hk
      · refine ⟨(m.unpair.1, m.unpair.2), ?_, Nat.pair_unpair m⟩
        simp only [Finset.coe_product, Finset.coe_range, mem_prod, Finset.mem_coe,
          Finsupp.mem_support_iff, mem_Iio]
        exact ⟨fun h0 ↦ hm (by simp [h0]), hk⟩
      · exact (hm rfl).elim
  map_add' _ _ := by
    ext m; simp only [ofSupportFinite_coe, coe_add, Pi.add_apply]; split_ifs <;> simp
  map_smul' _ _ := by
    ext m; simp only [ofSupportFinite_coe, coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

@[simp] theorem flattenFinsupp_apply {𝕜 : Type*} [Semiring 𝕜] (k : ℕ)
    (f : ℕ →₀ (Fin k → 𝕜)) (m : ℕ) :
    flattenFinsupp 𝕜 k f m = if h : m.unpair.2 < k then f m.unpair.1 ⟨m.unpair.2, h⟩ else 0 := (rfl)

theorem flattenFinsupp_apply_pair {𝕜 : Type*} [Semiring 𝕜] (k : ℕ)
    (f : ℕ →₀ (Fin k → 𝕜)) (n : ℕ) (i : Fin k) :
    flattenFinsupp 𝕜 k f (Nat.pair n i.1) = f n i := by
  simp [flattenFinsupp_apply, Nat.unpair_pair, i.2]

/-- Flattening `ℕ →₀ (Fin k → 𝕜)` into `ℕ →₀ 𝕜` is injective for every `k : ℕ`. -/
theorem flattenFinsupp_injective (𝕜 : Type*) [Semiring 𝕜] (k : ℕ) :
    Injective (flattenFinsupp 𝕜 k) := fun _ _ hfg ↦ by
  ext n i
  simpa only [flattenFinsupp_apply_pair] using congrArg (fun w : ℕ →₀ 𝕜 ↦ w (Nat.pair n i.1)) hfg

/-- If `f` is supported in the first `N` blocks, `flattenFinsupp 𝕜 k f` is supported below
`(max N k) ^ 2`. -/
theorem support_flattenFinsupp_subset_range {𝕜 : Type*} [Semiring 𝕜] {k N : ℕ}
    {f : ℕ →₀ (Fin k → 𝕜)} (hf : f.support ⊆ Finset.range N) :
    (flattenFinsupp 𝕜 k f).support ⊆ Finset.range (max N k ^ 2) := fun m hm ↦ by
  rw [Finsupp.mem_support_iff, flattenFinsupp_apply] at hm
  split_ifs at hm with hk
  · have hn : m.unpair.1 < N := Finset.mem_range.1 <| hf <|
      Finsupp.mem_support_iff.2 fun h0 ↦ hm (by simp [h0])
    have hmax : max m.unpair.1 m.unpair.2 + 1 ≤ max N k :=
      Nat.succ_le_of_lt (max_lt (hn.trans_le (le_max_left N k)) (hk.trans_le (le_max_right N k)))
    rw [Finset.mem_range, ← Nat.pair_unpair m]
    exact (Nat.pair_lt_max_add_one_sq _ _).trans_le (Nat.pow_le_pow_left hmax 2)
  · exact (hm rfl).elim

/-- A finitely supported sequence whose support lies in `Finset.range N` is recovered by restricting
to `Fin N` and applying `coordinateInclusion N`. -/
theorem coordinateInclusion_of_support_subset_range {𝕜 : Type*} [Semiring 𝕜] {N : ℕ}
    {v : ℕ →₀ 𝕜} (hv : v.support ⊆ Finset.range N) :
    coordinateInclusion (R := 𝕜) N (fun i : Fin N ↦ v i.1) = v := by
  ext m
  by_cases hm : m < N
  · exact coordinateInclusion_apply_val (fun i : Fin N ↦ v i.1) ⟨m, hm⟩
  · rw [coordinateInclusion_apply_of_le _ (Nat.le_of_not_gt hm)]
    exact (Finsupp.notMem_support_iff.1 fun hmem ↦ hm (Finset.mem_range.1 (hv hmem))).symm

end FlattenFinsupp

section ClassifyingCoordinates

/-- A family of fibrewise linear maps `j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)` forms **classifying
coordinates** for a bundle `E` with model `F` when each ambient coordinate is continuous on the
total space, the supports are locally contained in a fixed finite initial segment of `ℕ`, and each
`j x` is injective. -/
structure IsClassifyingCoordinates (𝕜 : Type*) [Field 𝕜] [TopologicalSpace 𝕜]
    {X : Type*} [TopologicalSpace X] (F : Type*) [TopologicalSpace F]
    (E : X → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)] (j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)) : Prop where
  /-- Every ambient coordinate is continuous on the total space. -/
  continuous_coord : ∀ m : ℕ, Continuous fun p : TotalSpace F E ↦ j p.proj p.2 m
  /-- Locally on the base, all fibre vectors have coordinates supported in a fixed `range N`. -/
  locally_supported : ∀ x : X, ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ v : E y, (j y v).support ⊆ Finset.range N
  /-- On every fibre, the coordinate map is injective. -/
  injective : ∀ x : X, Injective (j x)

namespace IsClassifyingCoordinates

section Operations

variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  {E' : X → Type*} [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜 (E' x)]
  [TopologicalSpace (TotalSpace G E')] {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)}

omit [IsTopologicalSemiring 𝕜] in
/-- Pulling back classifying coordinates along `f : C(Y, X)` yields classifying coordinates on
`(f : Y → X) *ᵖ E`. -/
theorem pullback (hj : IsClassifyingCoordinates 𝕜 F E j) (f : C(Y, X)) :
    IsClassifyingCoordinates 𝕜 F ((f : Y → X) *ᵖ E) (fun y ↦ j (f y)) where
  continuous_coord m := (hj.continuous_coord m).comp (Pullback.continuous_lift F E (f : Y → X))
  locally_supported y :=
    let ⟨N, hN⟩ := hj.locally_supported (f y)
    ⟨N, f.continuous.continuousAt.preimage_mem_nhds hN⟩
  injective y := hj.injective (f y)

omit [IsTopologicalSemiring 𝕜] in
/-- Precomposing classifying coordinates with a continuous family of fibrewise linear injections
preserves `IsClassifyingCoordinates`. -/
theorem compLinearMap (hj : IsClassifyingCoordinates 𝕜 F E j)
    (Φ : ∀ x, E' x →ₗ[𝕜] E x) (hΦ_inj : ∀ x, Injective (Φ x))
    (hΦ_cont : Continuous fun p : TotalSpace G E' ↦
      TotalSpace.mk' F (E := E) p.proj (Φ p.proj p.2)) :
    IsClassifyingCoordinates 𝕜 G E' (fun x ↦ (j x).comp (Φ x)) where
  continuous_coord m := (hj.continuous_coord m).comp hΦ_cont
  locally_supported x :=
    let ⟨N, hN⟩ := hj.locally_supported x; ⟨N, hN.mono fun y hy v ↦ hy (Φ y v)⟩
  injective x := (hj.injective x).comp (hΦ_inj x)

/-- Postcomposing classifying coordinates with any injective `𝕜`-linear map
`φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)` yields classifying coordinates. -/
theorem postcomp (hj : IsClassifyingCoordinates 𝕜 F E j) (hπ : Continuous (π F E))
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) :
    IsClassifyingCoordinates 𝕜 F E (fun x ↦ φ.comp (j x)) where
  continuous_coord m := by
    refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
    obtain ⟨N, hN⟩ := hj.locally_supported p₀.proj
    have hlin : Continuous ((Finsupp.lapply (R := 𝕜) (M := 𝕜) m).comp
        (φ.comp (coordinateInclusion N))) := LinearMap.continuous_on_pi _
    refine (hlin.comp (continuous_pi fun r : Fin N ↦
      hj.continuous_coord r.1)).continuousAt.congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt.preimage_mem_nhds hN] with q hq
    dsimp only [Function.comp_def, LinearMap.comp_apply, Finsupp.lapply_apply]
    rw [coordinateInclusion_of_support_subset_range (hq q.2)]
  locally_supported x := by
    obtain ⟨N, hN⟩ := hj.locally_supported x
    have hfg : ((⊤ : Submodule 𝕜 (Fin N → 𝕜)).map (φ.comp (coordinateInclusion N))).FG :=
      (Module.Finite.iff_fg.1 inferInstance).map _
    obtain ⟨M, hM⟩ := hfg.exists_le_supported_Iio
    refine ⟨M, hN.mono fun y hy v r hr ↦ Finset.mem_range.2 ?_⟩
    rw [LinearMap.comp_apply, ← coordinateInclusion_of_support_subset_range (hy v)] at hr
    exact hM ⟨fun i : Fin N ↦ j y v i.1, trivial, rfl⟩ hr
  injective x := hφ.comp (hj.injective x)

end Operations

section Classify

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}

/-- The image `LinearMap.range (j x)` of classifying coordinates has cardinal rank `k`. -/
theorem rank_range_eq (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) :
    Module.rank 𝕜 (LinearMap.range (j x)) = k := by
  let e : F ≃ₗ[𝕜] LinearMap.range (j x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F E x).symm.toLinearEquiv.trans
      (LinearEquiv.ofInjective (j x) (hj.injective x))
  have : Module.Finite 𝕜 (LinearMap.range (j x)) := Module.Finite.equiv e
  exact (Module.finrank_eq_rank 𝕜 (LinearMap.range (j x))).symm.trans
    (congrArg Nat.cast (e.symm.finrank_eq.trans hk))

/-- Classifying coordinates send each base point `x` to the `k`-dimensional subspace
`LinearMap.range (j x)` in `infiniteGrassmannian 𝕜 k`. -/
@[expose] def classify (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) : infiniteGrassmannian 𝕜 k :=
  ⟨LinearMap.range (j x), hj.rank_range_eq hk x⟩

@[simp] theorem coe_classify (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) :
    (hj.classify hk x).1 = LinearMap.range (j x) := (rfl)

private theorem frameSpan_localFrame_eq (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (b : Module.Basis (Fin k) 𝕜 F) {N : ℕ} {y : X} (hy : y ∈ e.baseSet)
    (hsupp : ∀ v : E y, (j y v).support ⊆ Finset.range N) :
    ∃ hlin : LinearIndependent 𝕜 (fun (i : Fin k) (r : Fin N) ↦ j y (e.symm y (b i)) r.1),
      finiteGrassmannian.toInfinite (finiteGrassmannian.frameSpan ⟨_, hlin⟩) =
        hj.classify hk y := by
  let f : Fin k → Fin N → 𝕜 := fun i r ↦ j y (e.symm y (b i)) r.1
  let L : F →ₗ[𝕜] (ℕ →₀ 𝕜) := (j y).comp (e.linearEquivAt 𝕜 y hy).symm.toLinearMap
  have hL : Injective L := (hj.injective y).comp (e.linearEquivAt 𝕜 y hy).symm.injective
  have hinc (i : Fin k) : coordinateInclusion (R := 𝕜) N (f i) = L (b i) :=
    coordinateInclusion_of_support_subset_range (hsupp _)
  have hlin : LinearIndependent 𝕜 f := Fintype.linearIndependent_iff.2 fun g hg ↦
    Fintype.linearIndependent_iff.1 b.linearIndependent g <| hL <| by
      rw [map_sum, map_zero, ← (coordinateInclusion (R := 𝕜) N).map_zero, ← hg, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, map_smul, hinc]
  refine ⟨hlin, Subtype.ext ?_⟩
  rw [finiteGrassmannian.coe_toInfinite, finiteGrassmannian.coe_frameSpan, Subtype.coe_mk,
    coe_classify, Submodule.map_span, ← range_comp,
    (funext hinc : coordinateInclusion (R := 𝕜) N ∘ f = L ∘ b), range_comp, ← Submodule.map_span,
    b.span_eq, Submodule.map_top, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The classifying map of `IsClassifyingCoordinates` is continuous into the direct-limit topology
of `infiniteGrassmannian 𝕜 k`. -/
@[fun_prop]
theorem continuous_classify (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) : Continuous (hj.classify hk) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  let e := trivializationAt F E x₀
  let b := Module.finBasisOfFinrankEq 𝕜 F hk
  obtain ⟨N, hN⟩ := hj.locally_supported x₀
  obtain ⟨U, hU_sub, hU_open, hx₀U⟩ := mem_nhds_iff.1
    (Filter.inter_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E x₀)) hN)
  have hraw : Continuous (fun (z : U) (i : Fin k) (r : Fin N) ↦ j z.1 (e.symm z.1 (b i)) r.1) :=
    continuous_pi fun i ↦ continuous_pi fun r ↦ continuous_iff_continuousAt.2 fun z ↦
      (hj.continuous_coord r.1).continuousAt.comp <|
        ContinuousAt.comp (f := fun u : U ↦ (u.1, b i))
          (e.continuousOn_symm.continuousAt
            ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨(hU_sub z.2).1, mem_univ _⟩))
          (continuous_subtype_val.prodMk continuous_const).continuousAt
  have hspec (z : U) := hj.frameSpan_localFrame_eq hk e b (hU_sub z.2).1 (hU_sub z.2).2
  have hon : ContinuousOn (hj.classify hk) U :=
    continuousOn_iff_continuous_domRestrict.2 <|
      (finiteGrassmannian.continuous_toInfinite.comp
        (finiteGrassmannian.continuous_frameSpan.comp
          (hraw.subtype_mk fun z ↦ (hspec z).1))).congr fun z ↦ (hspec z).2
  exact hon.continuousAt (hU_open.mem_nhds hx₀U)

/-- The classifying map bundled as `C(X, infiniteGrassmannian 𝕜 k)`. -/
@[expose] def classifyContinuousMap (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) : C(X, infiniteGrassmannian 𝕜 k) :=
  ⟨hj.classify hk, hj.continuous_classify hk⟩

@[simp] theorem classifyContinuousMap_apply (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) :
    hj.classifyContinuousMap hk x = hj.classify hk x := (rfl)

@[simp] theorem classifyContinuousMap_pullback {Y : Type*} [TopologicalSpace Y]
    (hj : IsClassifyingCoordinates 𝕜 F E j) (f : C(Y, X)) (hk : Module.finrank 𝕜 F = k) :
    (hj.pullback f).classifyContinuousMap hk = (hj.classifyContinuousMap hk).comp f :=
  ContinuousMap.ext fun _ ↦ rfl

/-- Precomposing classifying coordinates with a continuous family of fibrewise linear equivalences
leaves the classifying map unchanged. -/
theorem classifyContinuousMap_compLinearEquiv
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {E' : X → Type*} [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜 (E' x)]
    [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G E')]
    [FiberBundle G E'] [VectorBundle 𝕜 G E']
    (hj : IsClassifyingCoordinates 𝕜 F E j) (Φ : ∀ x, E' x ≃ₗ[𝕜] E x)
    (hΦ_cont : Continuous fun p : TotalSpace G E' ↦ TotalSpace.mk' F (E := E) p.proj (Φ p.proj p.2))
    (hk : Module.finrank 𝕜 F = k) (hk' : Module.finrank 𝕜 G = k) :
    (hj.compLinearMap (E' := E') (fun x ↦ (Φ x).toLinearMap) (fun x ↦ (Φ x).injective)
      hΦ_cont).classifyContinuousMap hk' = hj.classifyContinuousMap hk :=
  ContinuousMap.ext fun x ↦ Subtype.ext <| by
    rw [classifyContinuousMap_apply, classifyContinuousMap_apply, coe_classify, coe_classify,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range (Φ x))]

@[simp] theorem classifyContinuousMap_postcomp (hj : IsClassifyingCoordinates 𝕜 F E j)
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) (hk : Module.finrank 𝕜 F = k) :
    (hj.postcomp (FiberBundle.continuous_proj F E) φ hφ).classifyContinuousMap hk =
      (infiniteGrassmannian.mapContinuousMap φ hφ).comp (hj.classifyContinuousMap hk) :=
  ContinuousMap.ext fun _ ↦ Subtype.ext (by simp [LinearMap.range_comp])

/-- Over a complete scalar field, `j x` identifies each fibre `E x` continuously and linearly with
the tautological fibre over `hj.classify hk x`. -/
def classifyTautologicalEquiv [CompleteSpace 𝕜] (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) :
    E x ≃L[𝕜] infiniteGrassmannian.Tautological 𝕜 k (hj.classify hk x) :=
  let e₁ := VectorBundle.continuousLinearEquivAt 𝕜 F E x
  e₁.trans (e₁.symm.toLinearEquiv.trans
    ((LinearEquiv.ofInjective (j x) (hj.injective x)).trans
      (infiniteGrassmannian.tautologicalEquiv 𝕜 k (hj.classify hk x)).symm)).toContinuousLinearEquiv

@[simp] theorem val_classifyTautologicalEquiv [CompleteSpace 𝕜]
    (hj : IsClassifyingCoordinates 𝕜 F E j) (hk : Module.finrank 𝕜 F = k) (x : X) (v : E x) :
    (hj.classifyTautologicalEquiv hk x v).val = j x v := by
  let e₁ := VectorBundle.continuousLinearEquivAt 𝕜 F E x
  let w : (hj.classify hk x).1 := LinearEquiv.ofInjective (j x) (hj.injective x) (e₁.symm (e₁ v))
  exact (infiniteGrassmannian.val_tautologicalEquiv_symm (hj.classify hk x) w).trans <|
    (LinearEquiv.ofInjective_apply (f := j x) (h := hj.injective x) (e₁.symm (e₁ v))).trans
      (congrArg (j x) (e₁.symm_apply_apply v))

end Classify

section ClassifyHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}

/-- Over a complete scalar field, `hj.classifyTautologicalEquiv` glues to a bundle homeomorphism
from `TotalSpace F E` to the pullback of `infiniteGrassmannian.Tautological 𝕜 k` along
`hj.classifyContinuousMap hk`. -/
def classifyTautologicalHomeomorph (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) :
    TotalSpace F E ≃ₜ TotalSpace (Fin k → 𝕜)
      ((hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k)) :=
  bundleHomeomorph (𝕜 := 𝕜) (F₁ := F) (F₂ := Fin k → 𝕜) (E₁ := E)
    (E₂ := (hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k))
    (hj.classifyTautologicalEquiv hk) <|
      Bundle.Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj F E,
        infiniteGrassmannian.continuous_totalSpace_iff.2
          ⟨(hj.classifyContinuousMap hk).continuous.comp (FiberBundle.continuous_proj F E),
            fun m ↦ (hj.continuous_coord m).congr fun p ↦ by
              rw [← hj.val_classifyTautologicalEquiv hk p.proj p.2]; rfl⟩⟩

@[simp] theorem classifyTautologicalHomeomorph_apply (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (p : TotalSpace F E) :
    hj.classifyTautologicalHomeomorph hk p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (hj.classifyTautologicalEquiv hk p.proj p.2) :=
  bundleHomeomorph_apply (𝕜 := 𝕜) (F₁ := F) (F₂ := Fin k → 𝕜) (E₁ := E)
    (E₂ := (hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k))
    (hj.classifyTautologicalEquiv hk) _ p

@[simp] theorem classifyTautologicalHomeomorph_symm_apply (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k)
    (p : TotalSpace (Fin k → 𝕜)
      ((hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k))) :
    (hj.classifyTautologicalHomeomorph hk).symm p =
      TotalSpace.mk' F p.proj ((hj.classifyTautologicalEquiv hk p.proj).symm p.2) :=
  bundleHomeomorph_symm_apply (𝕜 := 𝕜) (F₁ := F) (F₂ := Fin k → 𝕜) (E₁ := E)
    (E₂ := (hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k))
    (hj.classifyTautologicalEquiv hk) _ p

end ClassifyHomeomorph

section Cylinder

section Algebraic

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜] {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  (j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜))

/-- Linearly interpolated coordinates `(1 - t) • j₀ x + t • j₁ x` on the cylinder pullback bundle
`(((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E)`. -/
@[expose] def cylinderLinearMap (p : I × X) :
    (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) p →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  (1 - algebraMap ℝ 𝕜 p.1.1) • j₀ p.2 + (algebraMap ℝ 𝕜 p.1.1) • j₁ p.2

@[simp] theorem cylinderLinearMap_apply (p : I × X)
    (v : (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) p) :
    cylinderLinearMap j₀ j₁ p v =
      (1 - algebraMap ℝ 𝕜 p.1.1) • j₀ p.2 v + (algebraMap ℝ 𝕜 p.1.1) • j₁ p.2 v := rfl

@[simp] theorem range_cylinderLinearMap_zero (x : X) :
    LinearMap.range (cylinderLinearMap j₀ j₁ (0, x)) = LinearMap.range (j₀ x) := by
  congr 1; ext v m; simp [cylinderLinearMap]

@[simp] theorem range_cylinderLinearMap_one (x : X) :
    LinearMap.range (cylinderLinearMap j₀ j₁ (1, x)) = LinearMap.range (j₁ x) := by
  congr 1; ext v m; simp [cylinderLinearMap]

end Algebraic

/-- Linearly interpolating between two families of classifying coordinates `j₀` and `j₁` on the
same bundle `E` over `X` yields classifying coordinates on the cylinder bundle over `I × X`,
whenever `(1 - algebraMap ℝ 𝕜 t) • j₀ x + (algebraMap ℝ 𝕜 t) • j₁ x` is fibrewise injective. -/
theorem cylinderInterp {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X] {F : Type*} [TopologicalSpace F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)] {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hinj : ∀ (t : I) (x : X),
      Injective ((1 - algebraMap ℝ 𝕜 t.1) • j₀ x + (algebraMap ℝ 𝕜 t.1) • j₁ x)) :
    IsClassifyingCoordinates 𝕜 F (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E)
      (cylinderLinearMap j₀ j₁) where
  continuous_coord m := by
    let π_cyl := Pullback.continuous_proj F E ((ContinuousMap.snd : C(I × X, X)) : I × X → X)
    let lift_cyl := Pullback.continuous_lift F E ((ContinuousMap.snd : C(I × X, X)) : I × X → X)
    have ht : Continuous fun q : TotalSpace F
        (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) ↦ algebraMap ℝ 𝕜 q.proj.1.1 :=
      (continuous_algebraMap ℝ 𝕜).comp (continuous_subtype_val.comp (continuous_fst.comp π_cyl))
    exact ((((continuous_const (y := (1 : 𝕜))).sub ht).mul
      ((hj₀.continuous_coord m).comp lift_cyl)).add
        (ht.mul ((hj₁.continuous_coord m).comp lift_cyl))).congr fun ⟨⟨_, _⟩, _⟩ ↦ rfl
  locally_supported p := by
    obtain ⟨N₀, hN₀⟩ := hj₀.locally_supported p.2
    obtain ⟨N₁, hN₁⟩ := hj₁.locally_supported p.2
    refine ⟨max N₀ N₁, Filter.mem_of_superset
      (continuous_snd.continuousAt.preimage_mem_nhds (Filter.inter_mem hN₀ hN₁))
      fun q hq v r hr ↦ ?_⟩
    rcases Finset.mem_union.1 (Finsupp.support_add hr) with hr₀ | hr₁
    · exact Finset.mem_range.2 ((Finset.mem_range.1
        (hq.1 v (Finsupp.support_smul hr₀))).trans_le (le_max_left N₀ N₁))
    · exact Finset.mem_range.2 ((Finset.mem_range.1
        (hq.2 v (Finsupp.support_smul hr₁))).trans_le (le_max_right N₀ N₁))
  injective p := hinj p.1 p.2

/-- If `(1 - t) • j₀ + t • j₁` is fibrewise injective for every `(t, x) : I × X`, its classifying
map on `I × X` is a homotopy between `hj₀.classifyContinuousMap hk` and
`hj₁.classifyContinuousMap hk`. -/
def homotopyOfLinearCombinationInjective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hinj : ∀ (t : I) (x : X),
      Injective ((1 - algebraMap ℝ 𝕜 t.1) • j₀ x + (algebraMap ℝ 𝕜 t.1) • j₁ x))
    (hk : Module.finrank 𝕜 F = k) :
    (hj₀.classifyContinuousMap hk).Homotopy (hj₁.classifyContinuousMap hk) where
  toContinuousMap := (hj₀.cylinderInterp hj₁ hinj).classifyContinuousMap hk
  map_zero_left x := Subtype.ext <|
    ((hj₀.cylinderInterp hj₁ hinj).coe_classify hk (0, x)).trans
      ((range_cylinderLinearMap_zero j₀ j₁ x).trans (hj₀.coe_classify hk x).symm)
  map_one_left x := Subtype.ext <|
    ((hj₀.cylinderInterp hj₁ hinj).coe_classify hk (1, x)).trans
      ((range_cylinderLinearMap_one j₀ j₁ x).trans (hj₁.coe_classify hk x).symm)

end Cylinder

end IsClassifyingCoordinates

end ClassifyingCoordinates

section Existence

section PartitionBlock

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : X → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]

private def partitionBlockCoordinates
    (ρ : PartitionOfUnity ℕ X univ) (e : ℕ → Trivialization F (π F E)) [∀ n, (e n).IsLinear 𝕜]
    {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (x : X) : E x →ₗ[𝕜] (ℕ →₀ (Fin r → 𝕜)) where
  toFun v := Finsupp.ofSupportFinite
    (fun n ↦ (algebraMap ℝ 𝕜 (ρ n x)) • b.equivFun ((e n).linearMapAt 𝕜 x v))
    ((ρ.locallyFinite.point_finite x).subset fun n hn ↦ by
      contrapose hn
      have hz : ρ n x = 0 := by simpa only [mem_ofPred_eq, mem_support, not_not] using hn
      simp [hz])
  map_add' _ _ := by ext n i; simp [smul_add]
  map_smul' _ _ := by
    ext n i
    simp only [ofSupportFinite_coe, LinearMap.map_smul, LinearEquiv.map_smul, coe_smul,
      Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

@[simp] private theorem partitionBlockCoordinates_apply
    (ρ : PartitionOfUnity ℕ X univ) (e : ℕ → Trivialization F (π F E)) [∀ n, (e n).IsLinear 𝕜]
    {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (x : X) (v : E x) (n : ℕ) :
    partitionBlockCoordinates ρ e b x v n =
      (algebraMap ℝ 𝕜 (ρ n x)) • b.equivFun ((e n).linearMapAt 𝕜 x v) := (rfl)

private theorem continuous_partitionBlockCoordinates_apply [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 F] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    (ρ : PartitionOfUnity ℕ X univ) (e : ℕ → Trivialization F (π F E)) [∀ n, (e n).IsLinear 𝕜]
    (hρ : ρ.IsSubordinate fun n ↦ (e n).baseSet)
    {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (n : ℕ) (i : Fin r) :
    Continuous fun p : TotalSpace F E ↦ partitionBlockCoordinates ρ e b p.proj p.2 n i := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  by_cases hp : p.proj ∈ tsupport (ρ n)
  · have hsrc : p ∈ (e n).source := (e n).mem_source.2 (hρ n hp)
    have hw : Continuous (fun q : TotalSpace F E ↦ algebraMap ℝ 𝕜 (ρ n q.proj)) :=
      (continuous_algebraMap ℝ 𝕜).comp ((ρ n).continuous.comp (FiberBundle.continuous_proj F E))
    have htriv : ContinuousAt (fun q : TotalSpace F E ↦ b.equivFun ((e n) q).2 i) p :=
      ((continuous_apply i).comp
        b.equivFun.toLinearMap.continuous_of_finiteDimensional).continuousAt.comp
          (((e n).continuousOn.continuousAt ((e n).open_source.mem_nhds hsrc)).snd)
    refine (hw.continuousAt.mul htriv).congr_of_eventuallyEq ?_
    filter_upwards [(e n).open_source.mem_nhds hsrc] with q hq
    simp only [partitionBlockCoordinates_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
      (e n).coe_linearMapAt_of_mem ((e n).mem_source.1 hq)]
  · refine (continuousAt_const (y := (0 : 𝕜))).congr_of_eventuallyEq ?_
    filter_upwards [(FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
      (notMem_tsupport_iff_eventuallyEq.1 hp)] with q (hq : ρ n q.proj = 0)
    simp [hq]

/-- Every finite-rank vector bundle over a paracompact normal base over a complete nontrivially
normed `ℝ`-algebra field admits `IsClassifyingCoordinates`. -/
theorem exists_isClassifyingCoordinates [CompleteSpace 𝕜] [ParacompactSpace X] [NormalSpace X]
    [FiniteDimensional 𝕜 F] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E] :
    ∃ j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜), IsClassifyingCoordinates 𝕜 F E j := by
  obtain ⟨e, he_lin, he_cov, -⟩ :=
    exists_countable_locallyFinite_trivialization 𝕜 (B := X) (F := F) (E := E)
  have := he_lin
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun n ↦ (e n).baseSet) (fun n ↦ (e n).open_baseSet) (fun x _ ↦ he_cov.ge (mem_univ x))
  let b := Module.finBasis 𝕜 F
  let j₀ := partitionBlockCoordinates ρ e b
  refine ⟨fun x ↦ (flattenFinsupp 𝕜 (Module.finrank 𝕜 F)).comp (j₀ x), ⟨?_, ?_, ?_⟩⟩
  · intro m
    by_cases hk : m.unpair.2 < Module.finrank 𝕜 F
    · exact (continuous_partitionBlockCoordinates_apply ρ e hρ b
        m.unpair.1 ⟨m.unpair.2, hk⟩).congr fun _ ↦ by simp [j₀, flattenFinsupp_apply, hk]
    · exact (continuous_const (y := (0 : 𝕜))).congr fun _ ↦ by simp [flattenFinsupp_apply, hk]
  · intro x
    classical
    refine ⟨max ((ρ.fintsupport x).sup id + 1) (Module.finrank 𝕜 F) ^ 2,
      (ρ.eventually_finsupport_subset x).mono fun y hy v ↦
        support_flattenFinsupp_subset_range fun n hn ↦ Finset.mem_range.2 ?_⟩
    have hn_supp : n ∈ ρ.finsupport y := (ρ.mem_finsupport y).2 fun (h0 : ρ n y = 0) ↦
      Finsupp.mem_support_iff.1 hn (by simp [j₀, h0])
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (hy hn_supp))
  · intro x
    refine (flattenFinsupp_injective 𝕜 _).comp fun v w hvw ↦ ?_
    have ⟨n, hn⟩ : ∃ n, ρ n x ≠ 0 := by
      by_contra! hall; have := ρ.sum_eq_one (mem_univ x); simp [hall] at this
    have hx_base : x ∈ (e n).baseSet := hρ n (subset_tsupport (ρ n) hn)
    have hvn : (algebraMap ℝ 𝕜 (ρ n x)) • b.equivFun ((e n).linearMapAt 𝕜 x v) =
        (algebraMap ℝ 𝕜 (ρ n x)) • b.equivFun ((e n).linearMapAt 𝕜 x w) := congrArg (· n) hvw
    have hsc : algebraMap ℝ 𝕜 (ρ n x) ≠ 0 :=
      map_zero (algebraMap ℝ 𝕜) ▸ (RingHom.injective (algebraMap ℝ 𝕜)).ne hn
    have hlin := b.equivFun.injective ((smul_right_inj hsc).1 hvn)
    rw [← (e n).symm_linearMapAt (R := 𝕜) hx_base v,
      ← (e n).symm_linearMapAt (R := 𝕜) hx_base w, hlin]

end PartitionBlock

/-- Square-root-weighted orthonormal block coordinates (`PartitionOfUnity.weightedFrameCoordinates`)
for a Riemannian or Hermitian vector bundle flatten directly to `IsClassifyingCoordinates`. -/
theorem IsClassifyingCoordinates.of_weightedFrameCoordinates
    {𝕜 X F V : Type*} [RCLike 𝕜] [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    {E : X → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
    {r : ℕ} (ρ : PartitionOfUnity ℕ X univ) (e : ℕ → Trivialization F (π F E))
    [∀ n, (e n).IsLinear 𝕜] (he : ∀ n, {x | 0 < ρ n x} ⊆ (e n).baseSet)
    (c : Module.Basis (Fin r) 𝕜 F) (b : OrthonormalBasis (Fin r) 𝕜 V) :
    let coords : V ≃ₗ[𝕜] (Fin r → 𝕜) :=
      b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (Fin r → 𝕜))
    IsClassifyingCoordinates 𝕜 F E fun x ↦
      (flattenFinsupp 𝕜 r).comp
        ((Finsupp.mapRange.linearEquiv coords).toLinearMap.comp
          (ρ.weightedFrameCoordinates e c b x)) := by
  intro coords
  have hcoords_cont : Continuous coords := (PiLp.continuous_ofLp 2 _).comp b.repr.continuous
  refine ⟨fun m ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · by_cases hr : m.unpair.2 < r
    · exact ((continuous_apply ⟨m.unpair.2, hr⟩).comp
        (hcoords_cont.comp (ρ.continuous_weightedFrameCoordinates_apply e c b he m.unpair.1))).congr
          fun _ ↦ by simp [flattenFinsupp_apply, hr]
    · exact (continuous_const (y := (0 : 𝕜))).congr fun _ ↦ by simp [flattenFinsupp_apply, hr]
  · obtain ⟨N, hN⟩ := ρ.locally_support_weightedFrameCoordinates_range c b e x
    exact ⟨max N r ^ 2, hN.mono fun y hy v ↦
      support_flattenFinsupp_subset_range
        ((Finsupp.support_mapRange (f := coords) (hf := map_zero coords)).trans (hy v))⟩
  · exact (flattenFinsupp_injective 𝕜 r).comp <|
      (Finsupp.mapRange.linearEquiv coords).injective.comp
        (ρ.weightedFrameCoordinates_injective e c b (mem_univ x))

end Existence

end TauCeti
