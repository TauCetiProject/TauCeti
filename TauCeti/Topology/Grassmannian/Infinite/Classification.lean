/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Infinite.ClassifyingCoordinates
public import TauCeti.Topology.VectorBundle.Core.Hom
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance
public import Mathlib.CategoryTheory.IsomorphismClasses
import TauCeti.LinearAlgebra.Finsupp.LMapDomain
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Universal vector bundle classification over paracompact bases

Over `RCLike 𝕜`, homotopy classes of maps `C(X, infiniteGrassmannian 𝕜 k)` from a paracompact `R₁`
space `X` classify rank-`k` `𝕜`-vector bundles over `X` up to isomorphism via pullback of
`Tautological 𝕜 k` (`homotopic_iff_exists_continuousLinearEquiv_pullback`, `tautologicalCore`,
`classificationEquiv`). Coordinate-shift homotopies and homotopy uniqueness of classifying maps
(`homotopic_id_mapContinuousMap_lmapDomain`, `homotopic_classifyContinuousMap`) hold over any
nontrivially normed `ℝ`-algebra field.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5; A. Hatcher, *Vector Bundles*, §1.2.
-/

public noncomputable section

open Bundle Set Function Filter CategoryTheory _root_.Finsupp
open scoped Topology unitInterval

namespace TauCeti
section HomotopyUniqueness
namespace infiniteGrassmannian
section StageCoordinates
private def stageTautologicalLinearMap {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] {k n : ℕ}
    (V : finiteGrassmannian 𝕜 k n) :
    ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k)) V →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Tautological.subtype (finiteGrassmannian.toInfinite V)

private theorem isClassifyingCoordinates_stageTautological
    {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] {k n : ℕ} :
    IsClassifyingCoordinates 𝕜 (Fin k → 𝕜)
      ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k)) (stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) (n := n)) where
  continuous_coord m :=
    ((continuous_evalCoord m).comp
      (Pullback.continuous_lift (Fin k → 𝕜) (Tautological 𝕜 k)
        (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _))).congr
          fun ⟨_, v⟩ ↦ by
            simp only [Function.comp_apply, Pullback.lift, stageTautologicalLinearMap]
            exact (congrArg (· m) (Tautological.subtype_apply _ v)).symm
  locally_supported _ := ⟨n, Filter.Eventually.of_forall fun V v m hm ↦ by
    have hm' : m ∈ v.val.support := congrArg Finsupp.support (Tautological.subtype_apply _ v) ▸ hm
    exact Finset.mem_range.2 (((finiteGrassmannian.mem_range_toInfinite_iff _).1 ⟨V, rfl⟩ v.2) hm')⟩
  injective V := Tautological.subtype_injective (finiteGrassmannian.toInfinite V)

private theorem homotopic_of_stage_isClassifyingCoordinates
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    {f₀ f₁ : C(infiniteGrassmannian 𝕜 k, infiniteGrassmannian 𝕜 k)}
    (L₀ L₁ : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜))
    (hf₀ : ∀ W, (f₀ W).1 = LinearMap.range (L₀ W)) (hf₁ : ∀ W, (f₁ W).1 = LinearMap.range (L₁ W))
    (hL₀ : ∀ n, IsClassifyingCoordinates 𝕜 (Fin k → 𝕜)
      ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k)) (fun V ↦ L₀ (finiteGrassmannian.toInfinite V)))
    (hL₁ : ∀ n, IsClassifyingCoordinates 𝕜 (Fin k → 𝕜)
      ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k)) (fun V ↦ L₁ (finiteGrassmannian.toInfinite V)))
    (hinj : ∀ (t : I) (W : infiniteGrassmannian 𝕜 k),
      Injective ((1 - algebraMap ℝ 𝕜 t.1) • L₀ W + (algebraMap ℝ 𝕜 t.1) • L₁ W)) :
    f₀.Homotopic f₁ := by
  let J (t : I) (W : infiniteGrassmannian 𝕜 k) : Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜) :=
    (1 - algebraMap ℝ 𝕜 t.1) • L₀ W + (algebraMap ℝ 𝕜 t.1) • L₁ W
  let H : I × infiniteGrassmannian 𝕜 k → infiniteGrassmannian 𝕜 k := fun p ↦
    ⟨LinearMap.range (J p.1 p.2),
      (LinearEquiv.ofInjective (J p.1 p.2) (hinj p.1 p.2)).symm.rank_eq.trans
        ((tautologicalEquiv 𝕜 k p.2).rank_eq.trans p.2.2)⟩
  refine ⟨{ toFun := H
            continuous_toFun := continuous_prod_left_iff.2 fun n ↦
              (((hL₀ n).cylinderInterp (hL₁ n)
                fun t V ↦ hinj t V.toInfinite).continuous_classify
                  (Module.finrank_fin_fun 𝕜)).congr fun q ↦ Subtype.ext <| by
                    rw [IsClassifyingCoordinates.coe_classify]
                    refine Submodule.ext fun x ↦ exists_congr fun v ↦ ?_
                    have hcyl : IsClassifyingCoordinates.cylinderLinearMap
                        (E := (finiteGrassmannian.toInfiniteContinuousMap
                          (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ (Tautological 𝕜 k))
                        (fun V ↦ L₀ V.toInfinite) (fun V ↦ L₁ V.toInfinite) q v =
                        J q.1 q.2.toInfinite v :=
                      IsClassifyingCoordinates.cylinderLinearMap_apply _ _ q v
                    rw [hcyl]
            map_zero_left W := Subtype.ext <| by
              have h0 : J 0 W = L₀ W := by ext; simp [J]
              rw [show (H (0, W)).1 = LinearMap.range (J 0 W) from rfl, h0, hf₀]
            map_one_left W := Subtype.ext <| by
              have h1 : J 1 W = L₁ W := by ext; simp [J]
              rw [show (H (1, W)).1 = LinearMap.range (J 1 W) from rfl, h1, hf₁] }⟩
end StageCoordinates

/-- Over `[NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]`, any strictly monotone shift `s : ℕ → ℕ`
induces a self-map of `infiniteGrassmannian 𝕜 k` homotopic to the identity. -/
theorem homotopic_id_mapContinuousMap_lmapDomain
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ} {s : ℕ → ℕ}
    (hs : StrictMono s)
    (hφ : Injective (Finsupp.lmapDomain 𝕜 𝕜 s) := Finsupp.mapDomain_injective hs.injective) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (mapContinuousMap (Finsupp.lmapDomain 𝕜 𝕜 s) hφ) :=
  homotopic_of_stage_isClassifyingCoordinates (fun W ↦ Tautological.subtype W)
    (fun W ↦ (Finsupp.lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W))
    (fun W ↦ (Tautological.range_subtype W).symm)
    (fun W ↦ by
      rw [mapContinuousMap_apply, coe_map, LinearMap.range_comp, Tautological.range_subtype])
    (fun n ↦ isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n))
    (fun n ↦ (isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)).postcomp
      (FiberBundle.continuous_proj (Fin k → 𝕜) _) (Finsupp.lmapDomain 𝕜 𝕜 s) hφ)
    fun t W ↦ by
      have heq : (1 - algebraMap ℝ 𝕜 t.1) • Tautological.subtype W +
          (algebraMap ℝ 𝕜 t.1) • (Finsupp.lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W) =
        ((1 - algebraMap ℝ 𝕜 t.1) • (LinearMap.id : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) +
          (algebraMap ℝ 𝕜 t.1) • Finsupp.lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W) := by
        ext; simp
      rw [heq]
      exact (Finsupp.one_sub_smul_id_add_smul_lmapDomain_injective hs hs.id_le _).comp
        (Tautological.subtype_injective W)

private theorem strictMono_even : StrictMono (fun m : ℕ ↦ 2 * m) :=
  fun _ _ h ↦ Nat.mul_lt_mul_of_pos_left h Nat.two_pos
private theorem strictMono_odd : StrictMono (fun m : ℕ ↦ 2 * m + 1) :=
  fun _ _ h ↦ Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left h Nat.two_pos)
private theorem disjoint_range_even_odd :
    Disjoint (range fun m : ℕ ↦ 2 * m) (range fun m : ℕ ↦ 2 * m + 1) :=
  Set.disjoint_left.2 fun _ ⟨a, ha⟩ ⟨b, hb⟩ ↦ by dsimp only at ha hb; omega
end infiniteGrassmannian

/-- Over `[NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]`, any two families of classifying
coordinates on the same vector bundle `E` induce homotopic classifying maps. -/
theorem IsClassifyingCoordinates.homotopic_classifyContinuousMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hk : Module.finrank 𝕜 F = k) :
    (hj₀.classifyContinuousMap hk).Homotopic (hj₁.classifyContinuousMap hk) := by
  have hπ : Continuous (π F E) := FiberBundle.continuous_proj F E
  let φ₀ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) := Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m)
  let φ₁ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) := Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m + 1)
  have hφ₀ : Injective φ₀ :=
    Finsupp.mapDomain_injective infiniteGrassmannian.strictMono_even.injective
  have hφ₁ : Injective φ₁ :=
    Finsupp.mapDomain_injective infiniteGrassmannian.strictMono_odd.injective
  have hmid : ((hj₀.postcomp hπ φ₀ hφ₀).classifyContinuousMap hk).Homotopic
      ((hj₁.postcomp hπ φ₁ hφ₁).classifyContinuousMap hk) :=
    ⟨(hj₀.postcomp hπ φ₀ hφ₀).homotopyOfLinearCombinationInjective (hj₁.postcomp hπ φ₁ hφ₁)
      (fun t x ↦ Finsupp.one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
        infiniteGrassmannian.strictMono_even.injective infiniteGrassmannian.strictMono_odd.injective
        infiniteGrassmannian.disjoint_range_even_odd (hj₀.injective x) (hj₁.injective x) _) hk⟩
  rw [hj₀.classifyContinuousMap_postcomp hπ φ₀ hφ₀ hk,
    hj₁.classifyContinuousMap_postcomp hπ φ₁ hφ₁ hk] at hmid
  exact (ContinuousMap.Homotopic.comp
    (infiniteGrassmannian.homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k)
      infiniteGrassmannian.strictMono_even) (.refl _)).trans
    (hmid.trans (ContinuousMap.Homotopic.comp
      (infiniteGrassmannian.homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k)
        infiniteGrassmannian.strictMono_odd) (.refl _)).symm)

namespace infiniteGrassmannian
/-- Over `[NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]`, classifying coordinates on
`Tautological 𝕜 k` induce a classifying map homotopic to `id`. -/
theorem homotopic_id_classifyContinuousMap_tautological
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    {j : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) j) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (hj.classifyContinuousMap (Module.finrank_fin_fun 𝕜)) := by
  let c := hj.classifyContinuousMap (Module.finrank_fin_fun 𝕜)
  let φ₀ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) := Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m)
  let φ₁ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) := Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m + 1)
  have hφ₀ : Injective φ₀ := Finsupp.mapDomain_injective strictMono_even.injective
  have hφ₁ : Injective φ₁ := Finsupp.mapDomain_injective strictMono_odd.injective
  have hmid : (mapContinuousMap φ₀ hφ₀).Homotopic ((mapContinuousMap φ₁ hφ₁).comp c) :=
    homotopic_of_stage_isClassifyingCoordinates (fun W ↦ φ₀.comp (Tautological.subtype W))
      (fun W ↦ φ₁.comp (j W))
      (fun W ↦ by
        rw [mapContinuousMap_apply, coe_map, LinearMap.range_comp, Tautological.range_subtype])
      (fun W ↦ by
        rw [ContinuousMap.comp_apply, mapContinuousMap_apply, coe_map,
          IsClassifyingCoordinates.classifyContinuousMap_apply,
          IsClassifyingCoordinates.coe_classify, LinearMap.range_comp])
      (fun n ↦ (isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)).postcomp
        (FiberBundle.continuous_proj (Fin k → 𝕜) _) φ₀ hφ₀)
      (fun n ↦ (hj.pullback
        (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n))).postcomp
        (FiberBundle.continuous_proj (Fin k → 𝕜) _) φ₁ hφ₁)
      fun t W ↦ Finsupp.one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
        strictMono_even.injective strictMono_odd.injective disjoint_range_even_odd
        (Tautological.subtype_injective W) (hj.injective W) (algebraMap ℝ 𝕜 t.1)
  exact (homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k) strictMono_even).trans
    (hmid.trans (ContinuousMap.Homotopic.comp
      (homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k) strictMono_odd) (.refl c)).symm)

/-- Over `RCLike 𝕜`, if the pullbacks of `Tautological 𝕜 k` along `f₀, f₁` admit a continuous
fibrewise linear equivalence, then `f₀` and `f₁` are homotopic. -/
theorem homotopic_of_continuousLinearEquiv_pullback
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) p.proj (Φ p.proj p.2)) :
    f₀.Homotopic f₁ := by
  obtain ⟨j_univ, hj_univ⟩ := exists_isClassifyingCoordinates (𝕜 := 𝕜)
    (X := infiniteGrassmannian 𝕜 k) (F := Fin k → 𝕜) (E := Tautological 𝕜 k)
  have hk := Module.finrank_fin_fun (R := 𝕜) (n := k)
  let c := hj_univ.classifyContinuousMap hk
  have hc := homotopic_id_classifyContinuousMap_tautological hj_univ
  have hmid : (c.comp f₀).Homotopic (c.comp f₁) := by
    rw [← hj_univ.classifyContinuousMap_pullback f₀ hk,
      ← hj_univ.classifyContinuousMap_pullback f₁ hk,
      ← (hj_univ.pullback f₁).classifyContinuousMap_compLinearEquiv (G := Fin k → 𝕜)
          (E' := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) (fun x ↦ (Φ x).toLinearEquiv) hΦ hk hk]
    exact (hj_univ.pullback f₀).homotopic_classifyContinuousMap
      ((hj_univ.pullback f₁).compLinearMap (G := Fin k → 𝕜)
        (E' := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) (fun x ↦ (Φ x).toLinearMap)
        (fun x ↦ (Φ x).injective) hΦ) hk
  exact (ContinuousMap.Homotopic.comp hc (.refl f₀)).trans
    (hmid.trans (ContinuousMap.Homotopic.comp hc (.refl f₁)).symm)

/-- Over `RCLike 𝕜` and paracompact `R₁` `X`, `f₀, f₁` are homotopic iff their pullbacks of
`Tautological 𝕜 k` are continuously fibrewise linearly equivalent. -/
theorem homotopic_iff_exists_continuousLinearEquiv_pullback
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X] [ParacompactSpace X] [R1Space X]
    {k : ℕ} {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)} :
    f₀.Homotopic f₁ ↔ ∃ Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x),
      Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (Φ p.proj p.2) :=
  ⟨fun h ↦ by
    obtain ⟨Φ, hΦ, _⟩ := h.exists_continuousLinearEquiv_pullback (𝕜 := 𝕜) (F := Fin k → 𝕜)
      (E := Tautological 𝕜 k); exact ⟨Φ, hΦ⟩,
   fun ⟨Φ, hΦ⟩ ↦ homotopic_of_continuousLinearEquiv_pullback Φ hΦ⟩
end infiniteGrassmannian
end HomotopyUniqueness

section SmallClassification
namespace infiniteGrassmannian
section CoreComparisons
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]
variable (𝕜) in
/-- `Tautological 𝕜 k` as an object of `FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k)`. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin k → 𝕜`.
@[expose, implicit_reducible]
def tautologicalCore (k : ℕ) : FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k) where
  rank := k
  core := pointIndexedCore 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  indexAt_eq := pointIndexedCore_indexAt 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
@[simp] theorem rank_tautologicalCore (k : ℕ) : (tautologicalCore 𝕜 k).rank = k := (rfl)
@[simp] theorem core_tautologicalCore (k : ℕ) :
    (tautologicalCore 𝕜 k).core = pointIndexedCore 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) := (rfl)
theorem tautologicalCore_eq_ofBundle (k : ℕ) :
    tautologicalCore 𝕜 k = .ofBundle 𝕜 k (Tautological 𝕜 k) := (rfl)
/-- Pulling back `tautologicalCore 𝕜 k` along `const X (basepoint 𝕜 k)` gives `trivial 𝕜 X k`. -/
theorem pullback_tautologicalCore_const_basepoint (k : ℕ) :
    (tautologicalCore 𝕜 k).pullback (ContinuousMap.const X (basepoint 𝕜 k)) =
      FiniteRankBundleCore.trivial 𝕜 X k := (tautologicalCore 𝕜 k).pullback_const (basepoint 𝕜 k)

/-- Continuous fibrewise linear equivalences of `Tautological` pullbacks yield core isomorphisms. -/
theorem nonempty_pullback_iso_of_continuousLinearEquiv_pullback [CompleteSpace 𝕜] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) p.proj (Φ p.proj p.2)) :
    Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :=
  ⟨(FiniteRankBundleCore.pullbackOfBundleIso (Tautological 𝕜 k) f₀).trans
    ((FiniteRankBundleCore.ofBundleIso (E₀ := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k))
      (E₁ := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) Φ hΦ).trans
      (FiniteRankBundleCore.pullbackOfBundleIso (Tautological 𝕜 k) f₁).symm)⟩

/-- Core isomorphisms of `tautologicalCore` pullbacks yield continuous fibrewise equivalences. -/
theorem exists_continuousLinearEquiv_pullback_of_pullback_iso [CompleteSpace 𝕜] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (α : (tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :
    ∃ Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x),
      Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (Φ p.proj p.2) :=
  FiniteRankBundleCore.exists_continuousLinearEquiv_of_ofBundle_iso
    (E₀ := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) (E₁ := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
    ((FiniteRankBundleCore.pullbackOfBundleIso (Tautological 𝕜 k) f₀).symm.trans
      (α.trans (FiniteRankBundleCore.pullbackOfBundleIso (Tautological 𝕜 k) f₁)))

private theorem continuous_pullbackTautologicalCoreToPullback
    {Y : Type*} [TopologicalSpace Y] {k : ℕ} (f : C(Y, infiniteGrassmannian 𝕜 k)) :
    Continuous fun p : ((tautologicalCore 𝕜 k).pullback f).core.TotalSpace ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f : _ → _) *ᵖ (Tautological 𝕜 k)) p.proj
        (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) (f p.proj) p.2) := by
  let eT := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  let hT := pointIndexedCoreHomeomorph 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  have hmid : Continuous fun p : TotalSpace (Fin k → 𝕜)
      ((f : _ → _) *ᵖ (tautologicalCore 𝕜 k).core.Fiber) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (eT (f p.proj) p.2) :=
    Bundle.Pullback.continuous_iff (F := Fin k → 𝕜) (E := Tautological 𝕜 k)
      (f := (f : Y → infiniteGrassmannian 𝕜 k)).2
        ⟨Pullback.continuous_proj (Fin k → 𝕜) (tautologicalCore 𝕜 k).core.Fiber f,
          (hT.continuous.comp
            (Pullback.continuous_lift (Fin k → 𝕜) (tautologicalCore 𝕜 k).core.Fiber f)).congr
              fun ⟨_, _⟩ ↦ by simp [hT, eT, Pullback.lift]⟩
  exact (hmid.comp ((tautologicalCore 𝕜 k).pullbackHomeomorph f).continuous).congr fun ⟨_, _⟩ ↦ by
    dsimp only [Function.comp_def]; rw [FiniteRankBundleCore.pullbackHomeomorph_apply]

/-- Classifying coordinates on `A` identify `(tautologicalCore 𝕜 k).pullback` with `A`. -/
def tautologicalPullbackIsoOfClassifyingCoordinates [CompleteSpace 𝕜] {k : ℕ}
    {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k) {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j)
    (hk : Module.finrank 𝕜 (Fin A.rank → 𝕜) = k := (Module.finrank_fin_fun 𝕜).trans hA) :
    (tautologicalCore 𝕜 k).pullback (hj.classifyContinuousMap hk) ≅ A :=
  let f := hj.classifyContinuousMap hk
  let eT := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  FiniteRankBundleCore.isoOfContinuousEquiv
    (fun x ↦ (eT (f x)).trans (hj.classifyTautologicalEquiv hk x).symm)
    (((hj.classifyTautologicalHomeomorph hk).symm.continuous.comp
      (continuous_pullbackTautologicalCoreToPullback f)).congr
        fun ⟨x, v⟩ ↦ hj.classifyTautologicalHomeomorph_symm_apply hk ⟨x, eT (f x) v⟩)
@[simp] theorem fiberMap_tautologicalPullbackIsoOfClassifyingCoordinates_hom
    [CompleteSpace 𝕜] {k : ℕ} {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k)
    {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j)
    (hk : Module.finrank 𝕜 (Fin A.rank → 𝕜) = k := (Module.finrank_fin_fun 𝕜).trans hA) (x : X) :
    (tautologicalPullbackIsoOfClassifyingCoordinates hA hj hk).hom.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) (hj.classify hk x)).trans
          (hj.classifyTautologicalEquiv hk x).symm) :=
  FiniteRankBundleCore.fiberMap_isoOfContinuousEquiv_hom (𝕜 := 𝕜) _ _ x
@[simp] theorem fiberMap_tautologicalPullbackIsoOfClassifyingCoordinates_inv
    [CompleteSpace 𝕜] {k : ℕ} {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k)
    {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j)
    (hk : Module.finrank 𝕜 (Fin A.rank → 𝕜) = k := (Module.finrank_fin_fun 𝕜).trans hA) (x : X) :
    (tautologicalPullbackIsoOfClassifyingCoordinates hA hj hk).inv.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((hj.classifyTautologicalEquiv hk x).trans
          (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) (hj.classify hk x)).symm) :=
  (FiniteRankBundleCore.fiberMap_isoOfContinuousEquiv_inv (𝕜 := 𝕜) _ _ x).trans
    (ContinuousLinearMap.ext fun _ ↦ rfl)
/-- Over a paracompact normal base, every rank-`k` core is isomorphic to a `tautologicalCore`
pullback. -/
theorem exists_pullback_tautologicalCore_iso [CompleteSpace 𝕜] [NormedAlgebra ℝ 𝕜]
    [ParacompactSpace X] [NormalSpace X] {k : ℕ} (A : FiniteRankBundleCore 𝕜 X) (hA : A.rank = k) :
    ∃ f : C(X, infiniteGrassmannian 𝕜 k), Nonempty ((tautologicalCore 𝕜 k).pullback f ≅ A) :=
  let ⟨_, hj⟩ := exists_isClassifyingCoordinates (𝕜 := 𝕜) (X := X)
    (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  ⟨_, ⟨tautologicalPullbackIsoOfClassifyingCoordinates hA hj⟩⟩
end CoreComparisons

section Bijection
variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X]
/-- Over `RCLike 𝕜`, pulling back `tautologicalCore 𝕜 k` along `toInfiniteContinuousMap` is
isomorphic to `ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n)`. -/
def _root_.TauCeti.finiteGrassmannian.pullbackTautologicalCoreIso (k n : ℕ) :
    (tautologicalCore 𝕜 k).pullback
        (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)) ≅
      FiniteRankBundleCore.ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n) :=
  let f := finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)
  let eT := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  let hF := pointIndexedCoreHomeomorph 𝕜 (Fin k → 𝕜) (finiteGrassmannian.Tautological 𝕜 k n)
  let hstage := finiteGrassmannian.toInfiniteTautologicalHomeomorph 𝕜 k n
  FiniteRankBundleCore.isoOfContinuousEquiv
    (fun V ↦ (eT (f V)).trans ((finiteGrassmannian.toInfiniteTautologicalEquiv V).symm.trans
      (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (finiteGrassmannian.Tautological 𝕜 k n) V).symm))
    ((hF.symm.continuous.comp (hstage.symm.continuous.comp
      (continuous_pullbackTautologicalCoreToPullback f))).congr fun ⟨_, _⟩ ↦ by
        dsimp only [Function.comp_def, hF, hstage]
        rw [finiteGrassmannian.toInfiniteTautologicalHomeomorph_symm_apply,
          pointIndexedCoreHomeomorph_symm_apply]; rfl)
@[simp] theorem _root_.TauCeti.finiteGrassmannian.fiberMap_pullbackTautologicalCoreIso_hom
    (k n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    (finiteGrassmannian.pullbackTautologicalCoreIso (𝕜 := 𝕜) k n).hom.fiberMap V =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).trans
          (V.toInfiniteTautologicalEquiv.symm.trans
            (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
              (finiteGrassmannian.Tautological 𝕜 k n) V).symm)) :=
  FiniteRankBundleCore.fiberMap_isoOfContinuousEquiv_hom (𝕜 := 𝕜) _ _ V
@[simp] theorem _root_.TauCeti.finiteGrassmannian.fiberMap_pullbackTautologicalCoreIso_inv
    (k n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    (finiteGrassmannian.pullbackTautologicalCoreIso (𝕜 := 𝕜) k n).inv.fiberMap V =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (finiteGrassmannian.Tautological 𝕜 k n) V).trans
          (V.toInfiniteTautologicalEquiv.trans
            (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).symm)) :=
  (FiniteRankBundleCore.fiberMap_isoOfContinuousEquiv_inv (𝕜 := 𝕜) _ _ V).trans
    (ContinuousLinearMap.ext fun _ ↦ rfl)

/-- Over `RCLike 𝕜` and paracompact `R₁` `X`, `f₀, f₁` are homotopic iff their pulled-back
`tautologicalCore`s are isomorphic. -/
theorem homotopic_iff_nonempty_pullback_iso [ParacompactSpace X] [R1Space X] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)} :
    f₀.Homotopic f₁ ↔
      Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :=
  homotopic_iff_exists_continuousLinearEquiv_pullback.trans
    ⟨fun ⟨Φ, hΦ⟩ ↦ nonempty_pullback_iso_of_continuousLinearEquiv_pullback Φ hΦ,
     fun ⟨α⟩ ↦ exists_continuousLinearEquiv_pullback_of_pullback_iso α⟩

variable (𝕜 X) in
/-- **Universal vector bundle classification (`BO(k)` / `BU(k)`):** bijection from homotopy classes
`[X, infiniteGrassmannian 𝕜 k]` to rank-`k` core isomorphism classes over paracompact `R₁` `X`. -/
def classificationEquiv [ParacompactSpace X] [R1Space X] (k : ℕ) :
    Quotient ⟨ContinuousMap.Homotopic (X := X) (Y := infiniteGrassmannian 𝕜 k),
        ContinuousMap.Homotopic.equivalence⟩ ≃
      Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _)) :=
  Equiv.ofBijective
    (Quotient.map (sa := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
      (sb := (CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap Subtype.val)
      (fun f ↦ ⟨(tautologicalCore 𝕜 k).pullback f, rfl⟩)
      fun _ _ h ↦ homotopic_iff_nonempty_pullback_iso.1 h)
    ⟨Quotient.ind₂ fun _ _ h ↦
        Quotient.sound (homotopic_iff_nonempty_pullback_iso.2 (Quotient.exact h)),
     Quotient.ind fun A ↦ let ⟨f, hf⟩ := exists_pullback_tautologicalCore_iso A.1 A.2
        ⟨Quotient.mk _ f, Quotient.sound hf⟩⟩
@[simp] theorem classificationEquiv_mk [ParacompactSpace X] [R1Space X] (k : ℕ)
    (f : C(X, infiniteGrassmannian 𝕜 k)) : classificationEquiv 𝕜 X k (Quotient.mk _ f) =
      Quotient.mk _ ⟨(tautologicalCore 𝕜 k).pullback f, rfl⟩ := (rfl)
/-- `(classificationEquiv 𝕜 X k).symm` sends `[A]` to `[hj.classifyContinuousMap hk]`. -/
theorem classificationEquiv_symm_mk_of_isClassifyingCoordinates [ParacompactSpace X] [R1Space X]
    {k : ℕ} (A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k})
    {j : ∀ x, A.1.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.1.rank → 𝕜) A.1.core.Fiber j)
    (hk : Module.finrank 𝕜 (Fin A.1.rank → 𝕜) = k := (Module.finrank_fin_fun 𝕜).trans A.2) :
    (classificationEquiv 𝕜 X k).symm (Quotient.mk _ A) =
      Quotient.mk _ (hj.classifyContinuousMap hk) :=
  (classificationEquiv 𝕜 X k).injective <| by
    rw [Equiv.apply_symm_apply, classificationEquiv_mk]
    exact Quotient.sound ⟨(tautologicalPullbackIsoOfClassifyingCoordinates A.2 hj hk).symm⟩
/-- Any constant map into `infiniteGrassmannian 𝕜 k` classifies `FiniteRankBundleCore.trivial`. -/
theorem classificationEquiv_const [ParacompactSpace X] [R1Space X] (k : ℕ)
    (W : infiniteGrassmannian 𝕜 k) :
    classificationEquiv 𝕜 X k (Quotient.mk _ (ContinuousMap.const X W)) =
      Quotient.mk _ ⟨FiniteRankBundleCore.trivial 𝕜 X k, rfl⟩ :=
  congrArg (Quotient.mk _) (Subtype.ext ((tautologicalCore 𝕜 k).pullback_const W))
/-- `(classificationEquiv 𝕜 X k).symm` sends `trivial 𝕜 X k` to `[const X (basepoint 𝕜 k)]`. -/
@[simp] theorem classificationEquiv_symm_trivial [ParacompactSpace X] [R1Space X] (k : ℕ) :
    (classificationEquiv 𝕜 X k).symm (Quotient.mk _ ⟨FiniteRankBundleCore.trivial 𝕜 X k, rfl⟩) =
      Quotient.mk _ (ContinuousMap.const X (basepoint 𝕜 k)) :=
  (classificationEquiv 𝕜 X k).injective <| by rw [Equiv.apply_symm_apply, classificationEquiv_const]
/-- The identity map of `infiniteGrassmannian 𝕜 k` classifies `tautologicalCore 𝕜 k`. -/
theorem classificationEquiv_id (k : ℕ) :
    classificationEquiv 𝕜 (infiniteGrassmannian 𝕜 k) k
        (Quotient.mk _ (ContinuousMap.id (infiniteGrassmannian 𝕜 k))) =
      Quotient.mk _ ⟨tautologicalCore 𝕜 k, rfl⟩ :=
  congrArg (Quotient.mk _) (Subtype.ext (tautologicalCore 𝕜 k).pullback_id)
/-- `(classificationEquiv _ _ k).symm` sends `tautologicalCore 𝕜 k` to `[id]`. -/
@[simp] theorem classificationEquiv_symm_tautologicalCore (k : ℕ) :
    (classificationEquiv 𝕜 (infiniteGrassmannian 𝕜 k) k).symm
        (Quotient.mk _ ⟨tautologicalCore 𝕜 k, rfl⟩) =
      Quotient.mk _ (ContinuousMap.id (infiniteGrassmannian 𝕜 k)) :=
  (classificationEquiv 𝕜 (infiniteGrassmannian 𝕜 k) k).injective <| by
    rw [Equiv.apply_symm_apply, classificationEquiv_id]
/-- `finiteGrassmannian.toInfiniteContinuousMap` classifies `finiteGrassmannian.Tautological`. -/
theorem classificationEquiv_toInfiniteContinuousMap (k n : ℕ) :
    classificationEquiv 𝕜 (finiteGrassmannian 𝕜 k n) k
        (Quotient.mk _ (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n))) =
      Quotient.mk _
        ⟨FiniteRankBundleCore.ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n), rfl⟩ :=
  Quotient.sound ⟨finiteGrassmannian.pullbackTautologicalCoreIso k n⟩
/-- `(classificationEquiv _ _ k).symm` sends `finiteGrassmannian.Tautological` to
`[toInfiniteContinuousMap]`. -/
@[simp] theorem classificationEquiv_symm_finiteTautological (k n : ℕ) :
    (classificationEquiv 𝕜 (finiteGrassmannian 𝕜 k n) k).symm
        (Quotient.mk _
          ⟨FiniteRankBundleCore.ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n), rfl⟩) =
      Quotient.mk _ (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)) :=
  (classificationEquiv 𝕜 (finiteGrassmannian 𝕜 k n) k).injective <| by
    rw [Equiv.apply_symm_apply, classificationEquiv_toInfiniteContinuousMap]
/-- Naturality of `classificationEquiv` under pullback along `g : C(X', X)`. -/
theorem classificationEquiv_comp {X' : Type*} [TopologicalSpace X']
    [ParacompactSpace X] [R1Space X] [ParacompactSpace X'] [R1Space X']
    (g : C(X', X)) (k : ℕ) (f : C(X, infiniteGrassmannian 𝕜 k)) :
    classificationEquiv 𝕜 X' k (Quotient.mk _ (f.comp g)) =
      FiniteRankBundleCore.pullbackRankClass g k (classificationEquiv 𝕜 X k (Quotient.mk _ f)) := by
  rw [classificationEquiv_mk, classificationEquiv_mk, FiniteRankBundleCore.pullbackRankClass_mk]
  exact congrArg (Quotient.mk _) (Subtype.ext ((tautologicalCore 𝕜 k).pullback_comp g f).symm)
/-- Naturality of `(classificationEquiv 𝕜 X k).symm` under `pullbackRankClass g k`. -/
theorem classificationEquiv_symm_pullbackRankClass {X' : Type*} [TopologicalSpace X']
    [ParacompactSpace X] [R1Space X] [ParacompactSpace X'] [R1Space X'] (g : C(X', X)) (k : ℕ)
    (c : Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
      (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _))) :
    (classificationEquiv 𝕜 X' k).symm (FiniteRankBundleCore.pullbackRankClass g k c) =
      Quotient.map (sa := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
        (sb := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
        (fun f : C(X, infiniteGrassmannian 𝕜 k) ↦ f.comp g) (fun _ _ h ↦ h.comp (.refl g))
        ((classificationEquiv 𝕜 X k).symm c) := by
  rcases (classificationEquiv 𝕜 X k).surjective c with ⟨q, rfl⟩
  refine Quotient.inductionOn q fun f ↦ ?_
  rw [← classificationEquiv_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply]; rfl
end Bijection
end infiniteGrassmannian
end SmallClassification
end TauCeti
