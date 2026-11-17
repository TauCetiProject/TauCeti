/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Infinite.ClassifyingCoordinates
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance
public import Mathlib.CategoryTheory.IsomorphismClasses
import TauCeti.LinearAlgebra.Finsupp.LMapDomain
import TauCeti.Topology.Category.TopCat.Limits.Homotopy

/-!
# Universal vector bundle classification over paracompact bases

Over `RCLike 𝕜`, homotopy classes of maps `C(X, infiniteGrassmannian 𝕜 k)` from a paracompact `R₁`
space `X` classify rank-`k` `𝕜`-vector bundles over `X` up to isomorphism via pullback of
`Tautological 𝕜 k` (`homotopic_iff_exists_continuousLinearEquiv_pullback`, `tautologicalCore`,
`classificationEquiv`). Ambient-endomorphism homotopies and homotopy uniqueness of classifying maps
(`homotopic_id_mapContinuousMap`, `homotopic_classifyContinuousMap`) hold over any nontrivially
normed `ℝ`-algebra field.

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
      Function.Injective ((1 - algebraMap ℝ 𝕜 t.1) • L₀ W + (algebraMap ℝ 𝕜 t.1) • L₁ W)) :
    f₀.Homotopic f₁ := by
  let hk := Module.finrank_fin_fun (R := 𝕜) (n := k)
  let ιStage (n : ℕ) : C((diagram 𝕜 k).obj n, finiteGrassmannian 𝕜 k n) :=
    ⟨fun V ↦ V, continuous_id⟩
  let ιPt : C((cocone 𝕜 k).pt, infiniteGrassmannian 𝕜 k) := ⟨fun W ↦ W, continuous_id⟩
  let f₀' : C((cocone 𝕜 k).pt, infiniteGrassmannian 𝕜 k) := f₀.comp ιPt
  let f₁' : C((cocone 𝕜 k).pt, infiniteGrassmannian 𝕜 k) := f₁.comp ιPt
  have hc₀ (n : ℕ) : ((hL₀ n).classifyContinuousMap hk).comp (ιStage n) =
      f₀'.comp ((cocone 𝕜 k).ι.app n).hom :=
    ContinuousMap.ext fun V ↦
      Subtype.ext (((hL₀ n).coe_classify hk V).trans (hf₀ (finiteGrassmannian.toInfinite V)).symm)
  have hc₁ (n : ℕ) : ((hL₁ n).classifyContinuousMap hk).comp (ιStage n) =
      f₁'.comp ((cocone 𝕜 k).ι.app n).hom :=
    ContinuousMap.ext fun V ↦
      Subtype.ext (((hL₁ n).coe_classify hk V).trans (hf₁ (finiteGrassmannian.toInfinite V)).symm)
  let H (n : ℕ) :=
    (((hL₀ n).homotopyOfLinearCombinationInjective (hL₁ n)
      (fun t V ↦ hinj t V.toInfinite) hk).compContinuousMap (ιStage n)).cast (hc₀ n) (hc₁ n)
  have hH_val (n : ℕ) (t : I) (U : (diagram 𝕜 k).obj n) :
      (H n (t, U)).1 = LinearMap.range
        ((1 - algebraMap ℝ 𝕜 t.1) • L₀ (finiteGrassmannian.toInfinite U) +
          (algebraMap ℝ 𝕜 t.1) • L₁ (finiteGrassmannian.toInfinite U)) := by
    rw [ContinuousMap.Homotopy.cast_apply, ContinuousMap.Homotopy.compContinuousMap_apply]
    refine (congrArg Subtype.val ((hL₀ n).homotopyOfLinearCombinationInjective_apply (hL₁ n)
      (fun t V ↦ hinj t V.toInfinite) hk (t, ιStage n U))).trans ?_
    refine (((hL₀ n).cylinderInterp (hL₁ n)
      (fun t V ↦ hinj t V.toInfinite)).coe_classify hk (t, ιStage n U)).trans ?_
    refine (congrArg LinearMap.range (IsClassifyingCoordinates.cylinderLinearMap_def
      (E := (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k))
      (fun V ↦ L₀ V.toInfinite) (fun V ↦ L₁ V.toInfinite) (t, ιStage n U))).trans ?_
    exact congrArg (fun V : finiteGrassmannian 𝕜 k n ↦ LinearMap.range
      ((1 - algebraMap ℝ 𝕜 t.1) • L₀ V.toInfinite + (algebraMap ℝ 𝕜 t.1) • L₁ V.toInfinite))
      (congrFun (ContinuousMap.coe_mk (fun V ↦ V) continuous_id) U)
  let H_colim := (isColimit 𝕜 k).homotopyDesc H fun m n u t V ↦ Subtype.ext <| by
    have hmap : finiteGrassmannian.toInfinite ((diagram 𝕜 k).map u V) =
        finiteGrassmannian.toInfinite V :=
      (congrArg finiteGrassmannian.toInfinite (diagram_map_apply k u V)).trans
        (finiteGrassmannian.toInfinite_ambientInclusion (leOfHom u) V)
    refine (hH_val n t ((diagram 𝕜 k).map u V)).trans ?_
    exact (congrArg (fun W ↦ LinearMap.range
      ((1 - algebraMap ℝ 𝕜 t.1) • L₀ W + (algebraMap ℝ 𝕜 t.1) • L₁ W)) hmap).trans
        (hH_val m t V).symm
  let ιPtInv : C(infiniteGrassmannian 𝕜 k, (cocone 𝕜 k).pt) := ⟨fun W ↦ W, continuous_id⟩
  have hPt (W : infiniteGrassmannian 𝕜 k) : ιPt (ιPtInv W) = W :=
    (congrFun (ContinuousMap.coe_mk (fun X ↦ X) continuous_id) (ιPtInv W)).trans
      (congrFun (ContinuousMap.coe_mk (fun X ↦ X) continuous_id) W)
  exact ⟨(H_colim.compContinuousMap ιPtInv).cast
    (ContinuousMap.ext fun W ↦ (ContinuousMap.comp_apply _ _ W).trans
      ((ContinuousMap.comp_apply _ _ _).trans (congrArg f₀ (hPt W))))
    (ContinuousMap.ext fun W ↦ (ContinuousMap.comp_apply _ _ W).trans
      ((ContinuousMap.comp_apply _ _ _).trans (congrArg f₁ (hPt W))))⟩

private theorem homotopic_id_mapContinuousMap_lmapDomain_of_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ} {s : ℕ → ℕ}
    (hs : Function.Injective s) (hle : ∀ m, m ≤ s m) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (mapContinuousMap (Finsupp.lmapDomain 𝕜 𝕜 s) (Finsupp.mapDomain_injective hs)) :=
  homotopic_of_stage_isClassifyingCoordinates (fun W ↦ Tautological.subtype W)
    (fun W ↦ (Finsupp.lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W))
    (fun W ↦ (Tautological.range_subtype W).symm)
    (fun W ↦ (coe_map _ _ W).trans (by rw [LinearMap.range_comp, Tautological.range_subtype]))
    (fun n ↦ isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n))
    (fun n ↦ (isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)).postcomp
      (FiberBundle.continuous_proj (Fin k → 𝕜) _) (Finsupp.lmapDomain 𝕜 𝕜 s)
      (Finsupp.mapDomain_injective hs))
    fun t W ↦ by
      have heq : (1 - algebraMap ℝ 𝕜 t.1) • Tautological.subtype W +
          (algebraMap ℝ 𝕜 t.1) • (Finsupp.lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W) =
        ((1 - algebraMap ℝ 𝕜 t.1) • (LinearMap.id : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) +
          (algebraMap ℝ 𝕜 t.1) • Finsupp.lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W) := by
        ext; simp
      rw [heq]
      exact (Finsupp.one_sub_smul_id_add_smul_lmapDomain_injective hs hle _).comp
        (Tautological.subtype_injective W)

private theorem strictMono_even : StrictMono (fun m : ℕ ↦ 2 * m) :=
  fun _ _ h ↦ Nat.mul_lt_mul_of_pos_left h Nat.two_pos
private theorem strictMono_odd : StrictMono (fun m : ℕ ↦ 2 * m + 1) :=
  fun _ _ h ↦ Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left h Nat.two_pos)
private theorem disjoint_range_even_odd :
    Disjoint (range fun m : ℕ ↦ 2 * m) (range fun m : ℕ ↦ 2 * m + 1) :=
  Set.disjoint_left.2 fun _ ⟨a, ha⟩ ⟨b, hb⟩ ↦ by dsimp only at ha hb; omega

private theorem homotopic_id_of_stage_isClassifyingCoordinates
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    {f : C(infiniteGrassmannian 𝕜 k, infiniteGrassmannian 𝕜 k)}
    (L : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜))
    (hf : ∀ W, (f W).1 = LinearMap.range (L W))
    (hL : ∀ n, IsClassifyingCoordinates 𝕜 (Fin k → 𝕜)
      ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k)) (fun V ↦ L V.toInfinite))
    (hinj : ∀ W, Function.Injective (L W)) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic f := by
  let φ₀ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) := Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m)
  let φ₁ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) := Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m + 1)
  have hφ₀ : Function.Injective φ₀ := Finsupp.mapDomain_injective strictMono_even.injective
  have hφ₁ : Function.Injective φ₁ := Finsupp.mapDomain_injective strictMono_odd.injective
  have hmid : (mapContinuousMap φ₀ hφ₀).Homotopic ((mapContinuousMap φ₁ hφ₁).comp f) :=
    homotopic_of_stage_isClassifyingCoordinates (fun W ↦ φ₀.comp (Tautological.subtype W))
      (fun W ↦ φ₁.comp (L W))
      (fun W ↦ (coe_map _ _ W).trans (by rw [LinearMap.range_comp, Tautological.range_subtype]))
      (fun W ↦ (coe_map _ _ (f W)).trans (by rw [LinearMap.range_comp, ← hf W]))
      (fun n ↦ (isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)).postcomp
        (FiberBundle.continuous_proj (Fin k → 𝕜) _) φ₀ hφ₀)
      (fun n ↦ (hL n).postcomp (FiberBundle.continuous_proj (Fin k → 𝕜) _) φ₁ hφ₁)
      fun t W ↦ Finsupp.one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
        strictMono_even.injective strictMono_odd.injective disjoint_range_even_odd
        (Tautological.subtype_injective W) (hinj W) (algebraMap ℝ 𝕜 t.1)
  exact (homotopic_id_mapContinuousMap_lmapDomain_of_le (𝕜 := 𝕜) (k := k)
      strictMono_even.injective strictMono_even.id_le).trans
    (hmid.trans (ContinuousMap.Homotopic.comp
      (homotopic_id_mapContinuousMap_lmapDomain_of_le (𝕜 := 𝕜) (k := k)
        strictMono_odd.injective strictMono_odd.id_le) (.refl f)).symm)
end StageCoordinates

/-- Over `[NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]`, any injective linear endomorphism
`φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)` induces a self-map of `infiniteGrassmannian 𝕜 k` homotopic to the
identity. -/
theorem homotopic_id_mapContinuousMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Function.Injective φ) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic (mapContinuousMap (k := k) φ hφ) :=
  homotopic_id_of_stage_isClassifyingCoordinates (fun W ↦ φ.comp (Tautological.subtype W))
    (fun W ↦ (coe_map _ _ W).trans (by rw [LinearMap.range_comp, Tautological.range_subtype]))
    (fun n ↦ (isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)).postcomp
      (FiberBundle.continuous_proj (Fin k → 𝕜) _) φ hφ)
    fun W ↦ hφ.comp (Tautological.subtype_injective W)
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
  have hφ₀ : Function.Injective φ₀ :=
    Finsupp.mapDomain_injective infiniteGrassmannian.strictMono_even.injective
  have hφ₁ : Function.Injective φ₁ :=
    Finsupp.mapDomain_injective infiniteGrassmannian.strictMono_odd.injective
  have hmid : ((hj₀.postcomp hπ φ₀ hφ₀).classifyContinuousMap hk).Homotopic
      ((hj₁.postcomp hπ φ₁ hφ₁).classifyContinuousMap hk) :=
    ⟨(hj₀.postcomp hπ φ₀ hφ₀).homotopyOfLinearCombinationInjective (hj₁.postcomp hπ φ₁ hφ₁)
      (fun t x ↦ Finsupp.one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
        infiniteGrassmannian.strictMono_even.injective infiniteGrassmannian.strictMono_odd.injective
        infiniteGrassmannian.disjoint_range_even_odd (hj₀.injective x) (hj₁.injective x) _) hk⟩
  rw [hj₀.classifyContinuousMap_postcomp φ₀ hφ₀ hk,
    hj₁.classifyContinuousMap_postcomp φ₁ hφ₁ hk] at hmid
  exact (ContinuousMap.Homotopic.comp
    (infiniteGrassmannian.homotopic_id_mapContinuousMap (k := k) φ₀ hφ₀) (.refl _)).trans
    (hmid.trans (ContinuousMap.Homotopic.comp
      (infiniteGrassmannian.homotopic_id_mapContinuousMap (k := k) φ₁ hφ₁) (.refl _)).symm)

namespace infiniteGrassmannian
/-- Over `[NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]`, classifying coordinates on
`Tautological 𝕜 k` induce a classifying map homotopic to `id`. -/
theorem homotopic_id_classifyContinuousMap_tautological
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    {j : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) j) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (hj.classifyContinuousMap (Module.finrank_fin_fun 𝕜)) :=
  homotopic_id_of_stage_isClassifyingCoordinates j (fun _ ↦ by simp)
    (fun n ↦ hj.pullback (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)))
    hj.injective

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
abbrev tautologicalCore (k : ℕ) : FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k) :=
  FiniteRankBundleCore.ofBundle 𝕜 k (Tautological 𝕜 k)

/-- Continuous fibrewise linear equivalences of `Tautological` pullbacks yield core isomorphisms. -/
theorem nonempty_pullback_iso_of_continuousLinearEquiv_pullback [CompleteSpace 𝕜] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) p.proj (Φ p.proj p.2)) :
    Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) := by
  rw [FiniteRankBundleCore.pullback_ofBundle, FiniteRankBundleCore.pullback_ofBundle]
  exact ⟨FiniteRankBundleCore.ofBundleIso (E₀ := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k))
    (E₁ := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) Φ hΦ⟩

/-- Core isomorphisms of `tautologicalCore` pullbacks yield continuous fibrewise equivalences. -/
theorem exists_continuousLinearEquiv_pullback_of_pullback_iso {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (α : (tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :
    ∃ Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x),
      Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (Φ p.proj p.2) :=
  FiniteRankBundleCore.exists_continuousLinearEquiv_of_ofBundle_iso
    (E₀ := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) (E₁ := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
    ((eqToIso (FiniteRankBundleCore.pullback_ofBundle _ f₀)).symm.trans
      (α.trans (eqToIso (FiniteRankBundleCore.pullback_ofBundle _ f₁))))

/-- Classifying coordinates on `A` identify `(tautologicalCore 𝕜 k).pullback` with `A`. -/
def tautologicalPullbackIsoOfClassifyingCoordinates [CompleteSpace 𝕜] {k : ℕ}
    {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k) {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j) :
    (tautologicalCore 𝕜 k).pullback
      (hj.classifyContinuousMap ((Module.finrank_fin_fun 𝕜).trans hA)) ≅ A :=
  let hk := (Module.finrank_fin_fun (R := 𝕜)).trans hA
  let f := hj.classifyContinuousMap hk
  let eT := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  FiniteRankBundleCore.isoOfContinuousEquiv
    (fun x ↦ (eT (f x)).trans (hj.classifyTautologicalEquiv hk x).symm)
    (((hj.classifyTautologicalHomeomorph hk).symm.continuous.comp
      (FiniteRankBundleCore.pullbackOfBundleHomeomorph (Tautological 𝕜 k) f).continuous).congr
        fun ⟨x, v⟩ ↦ by
          rw [Function.comp_apply, FiniteRankBundleCore.pullbackOfBundleHomeomorph_apply]
          exact hj.classifyTautologicalHomeomorph_symm_apply hk ⟨x, eT (f x) v⟩)

@[simp] theorem fiberMap_tautologicalPullbackIsoOfClassifyingCoordinates_hom
    [CompleteSpace 𝕜] {k : ℕ} {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k)
    {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j) (x : X) :
    (tautologicalPullbackIsoOfClassifyingCoordinates hA hj).hom.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
          (hj.classify ((Module.finrank_fin_fun 𝕜).trans hA) x)).trans
            (hj.classifyTautologicalEquiv ((Module.finrank_fin_fun 𝕜).trans hA) x).symm) := by
  rw [tautologicalPullbackIsoOfClassifyingCoordinates]
  exact FiniteRankBundleCore.fiberMap_isoOfContinuousEquiv_hom (𝕜 := 𝕜) _ _ x

@[simp] theorem fiberMap_tautologicalPullbackIsoOfClassifyingCoordinates_inv
    [CompleteSpace 𝕜] {k : ℕ} {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k)
    {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j) (x : X) :
    (tautologicalPullbackIsoOfClassifyingCoordinates hA hj).inv.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((hj.classifyTautologicalEquiv ((Module.finrank_fin_fun 𝕜).trans hA) x).trans
          (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
            (hj.classify ((Module.finrank_fin_fun 𝕜).trans hA) x)).symm) := by
  refine (FiniteRankBundleCore.fiberMap_isoOfContinuousEquiv_inv (𝕜 := 𝕜)
    (A := (tautologicalCore 𝕜 k).pullback
      (hj.classifyContinuousMap ((Module.finrank_fin_fun 𝕜).trans hA)))
    (D := A) _ _ x).trans (ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦
      ContinuousLinearEquiv.symm_trans_apply
        (hj.classifyTautologicalEquiv ((Module.finrank_fin_fun 𝕜).trans hA) x).symm
        (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
          (hj.classify ((Module.finrank_fin_fun 𝕜).trans hA) x)) v)

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

private theorem pointIndexedCoreFiberEquiv_toInfinite_pullback_symm_apply
    {k n : ℕ} (V : finiteGrassmannian 𝕜 k n) (w : Tautological 𝕜 k V.toInfinite) :
    (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
      ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k)) V).symm w =
      (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).symm w := by
  let f := finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)
  let z : TotalSpace (Fin k → 𝕜) ((f : _ → _) *ᵖ (Tautological 𝕜 k)) := ⟨V, w⟩
  refine (pointIndexedCoreFiberEquiv_symm_apply 𝕜 (Fin k → 𝕜)
    ((f : _ → _) *ᵖ (Tautological 𝕜 k)) V z.2).trans ?_
  rw [trivializationAt, FiberBundle.pullback_trivializationAt', Trivialization.pullback_apply]
  exact (congrArg (fun p ↦ (trivializationAt (Fin k → 𝕜) (Tautological 𝕜 k) (f V) p).2)
    (Pullback.lift_mk (F := Fin k → 𝕜) (E := Tautological 𝕜 k) f V w)).trans
      (pointIndexedCoreFiberEquiv_symm_apply 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) (f V) w).symm

private theorem pointIndexedCoreFiberEquiv_toInfinite_pullback_apply
    {k n : ℕ} (V : finiteGrassmannian 𝕜 k n) (v : Fin k → 𝕜) :
    pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
      ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k)) V v =
      pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite v :=
  (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).symm.injective <|
    (pointIndexedCoreFiberEquiv_toInfinite_pullback_symm_apply V _).symm.trans <|
      ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
        ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
          (Tautological 𝕜 k)) V).symm_apply_apply v).trans
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
          (Tautological 𝕜 k) V.toInfinite).symm_apply_apply v).symm

/-- Over `RCLike 𝕜`, pulling back `tautologicalCore 𝕜 k` along `toInfiniteContinuousMap` is
isomorphic to `ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n)`. -/
def _root_.TauCeti.finiteGrassmannian.pullbackTautologicalCoreIso (k n : ℕ) :
    (tautologicalCore 𝕜 k).pullback
        (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)) ≅
      FiniteRankBundleCore.ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n) :=
  (eqToIso (FiniteRankBundleCore.pullback_ofBundle (Tautological 𝕜 k)
    (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)))).trans
    (FiniteRankBundleCore.ofBundleIso
      (E₀ := finiteGrassmannian.Tautological 𝕜 k n)
      (E₁ := (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k))
      finiteGrassmannian.toInfiniteTautologicalEquiv
      ((finiteGrassmannian.toInfiniteTautologicalHomeomorph 𝕜 k n).continuous.congr
        finiteGrassmannian.toInfiniteTautologicalHomeomorph_apply)).symm

@[simp] theorem _root_.TauCeti.finiteGrassmannian.fiberMap_pullbackTautologicalCoreIso_hom
    (k n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    (finiteGrassmannian.pullbackTautologicalCoreIso (𝕜 := 𝕜) k n).hom.fiberMap V =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).trans
          (V.toInfiniteTautologicalEquiv.symm.trans
            (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
              (finiteGrassmannian.Tautological 𝕜 k n) V).symm)) := by
  rw [finiteGrassmannian.pullbackTautologicalCoreIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    FiniteRankBundleCore.fiberMap_comp]
  have hIso := DFunLike.congr_fun (FiniteRankBundleCore.fiberMap_ofBundleIso_inv
    (E₀ := finiteGrassmannian.Tautological 𝕜 k n)
    (E₁ := (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k))
    finiteGrassmannian.toInfiniteTautologicalEquiv
    ((finiteGrassmannian.toInfiniteTautologicalHomeomorph 𝕜 k n).continuous.congr
      finiteGrassmannian.toInfiniteTautologicalHomeomorph_apply) V)
  have hv (v : Fin k → 𝕜) :
      (eqToHom (FiniteRankBundleCore.pullback_ofBundle (Tautological 𝕜 k)
        (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)))).fiberMap V v =
          v := funext fun i ↦ by
    simp only [FiniteRankBundleCore.fiberMap_eqToHom_apply, Fin.cast_refl, id_eq]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [ContinuousLinearMap.comp_apply, hv, hIso]
  exact congrArg
    ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (finiteGrassmannian.Tautological 𝕜 k n) V).symm ∘
      V.toInfiniteTautologicalEquiv.symm)
    (pointIndexedCoreFiberEquiv_toInfinite_pullback_apply V v)

@[simp] theorem _root_.TauCeti.finiteGrassmannian.fiberMap_pullbackTautologicalCoreIso_inv
    (k n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    (finiteGrassmannian.pullbackTautologicalCoreIso (𝕜 := 𝕜) k n).inv.fiberMap V =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (finiteGrassmannian.Tautological 𝕜 k n) V).trans
          (V.toInfiniteTautologicalEquiv.trans
            (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).symm)) := by
  rw [finiteGrassmannian.pullbackTautologicalCoreIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
    FiniteRankBundleCore.fiberMap_comp]
  have hIso := DFunLike.congr_fun (FiniteRankBundleCore.fiberMap_ofBundleIso_hom
    (E₀ := finiteGrassmannian.Tautological 𝕜 k n)
    (E₁ := (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k))
    finiteGrassmannian.toInfiniteTautologicalEquiv
    ((finiteGrassmannian.toInfiniteTautologicalHomeomorph 𝕜 k n).continuous.congr
      finiteGrassmannian.toInfiniteTautologicalHomeomorph_apply) V)
  refine ContinuousLinearMap.ext fun v ↦ funext fun i ↦ ?_
  rw [ContinuousLinearMap.comp_apply, FiniteRankBundleCore.fiberMap_eqToHom_apply, hIso]
  simp only [Fin.cast_refl, id_eq]
  exact congrArg (· i) (pointIndexedCoreFiberEquiv_toInfinite_pullback_symm_apply V _)

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
/-- `(classificationEquiv 𝕜 X k).symm` sends `[A]` to `[hj.classifyContinuousMap ...]`. -/
theorem classificationEquiv_symm_mk_of_isClassifyingCoordinates [ParacompactSpace X] [R1Space X]
    {k : ℕ} (A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k})
    {j : ∀ x, A.1.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.1.rank → 𝕜) A.1.core.Fiber j) :
    (classificationEquiv 𝕜 X k).symm (Quotient.mk _ A) =
      Quotient.mk _ (hj.classifyContinuousMap ((Module.finrank_fin_fun 𝕜).trans A.2)) :=
  (classificationEquiv 𝕜 X k).injective <| by
    rw [Equiv.apply_symm_apply, classificationEquiv_mk]
    exact Quotient.sound ⟨(tautologicalPullbackIsoOfClassifyingCoordinates A.2 hj).symm⟩
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
  refine Quotient.inductionOn q fun f ↦ (classificationEquiv 𝕜 X' k).injective ?_
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Quotient.map_mk, classificationEquiv_comp]
end Bijection
end infiniteGrassmannian
end SmallClassification
end TauCeti
