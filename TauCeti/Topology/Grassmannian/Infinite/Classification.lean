/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Infinite.ClassifyingCoordinates
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance.Basic
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

open Bundle Set Function Filter _root_.Finsupp
open CategoryTheory (Iso eqToIso eqToHom isIsomorphicSetoid leOfHom)
open scoped Topology unitInterval

namespace TauCeti
namespace infiniteGrassmannian
open finiteGrassmannian (toInfinite toInfiniteContinuousMap toInfinite_ambientInclusion
  mem_range_toInfinite_iff)
private abbrev stagePullback {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] (k n : ℕ) :=
  (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ (Tautological 𝕜 k)
section Base
variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] {k n : ℕ}
private def stageTautologicalLinearMap (V : finiteGrassmannian 𝕜 k n) :
    stagePullback k n V →ₗ[𝕜] (ℕ →₀ 𝕜) := Tautological.subtype V.toInfinite
private theorem isClassifyingCoordinates_stageTautological :
    IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (stagePullback k n)
      (stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) (n := n)) where
  continuous_coord m :=
    ((continuous_evalCoord m).comp
      (Pullback.continuous_lift (Fin k → 𝕜) (Tautological 𝕜 k)
        (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _))).congr fun ⟨_, v⟩ ↦ by
      simp only [comp_apply, Pullback.lift, stageTautologicalLinearMap]
      exact (congrArg (· m) (Tautological.subtype_apply _ v)).symm
  locally_supported _ := ⟨n, Eventually.of_forall fun V v m hm ↦ by
    have hm' : m ∈ v.val.support := congrArg Finsupp.support (Tautological.subtype_apply _ v) ▸ hm
    exact Finset.mem_range.2 (((mem_range_toInfinite_iff _).1 ⟨V, rfl⟩ v.property) hm')⟩
  injective V := Tautological.subtype_injective V.toInfinite
end Base
private theorem strictMono_even : StrictMono (fun m : ℕ ↦ 2 * m) := fun _ _ _ ↦ by dsimp; omega
private theorem strictMono_odd : StrictMono (fun m : ℕ ↦ 2 * m + 1) := fun _ _ _ ↦ by dsimp; omega
private theorem disjoint_range_even_odd :
    Disjoint (range fun m : ℕ ↦ 2 * m) (range fun m : ℕ ↦ 2 * m + 1) :=
  disjoint_left.2 fun _ ⟨_, ha⟩ ⟨_, hb⟩ ↦ by dsimp only at ha hb; omega

section Normed
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
private theorem homotopic_of_stage_isClassifyingCoordinates
    {f₀ f₁ : C(infiniteGrassmannian 𝕜 k, infiniteGrassmannian 𝕜 k)}
    (L₀ L₁ : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜))
    (hf₀ : ∀ W, (f₀ W).val = LinearMap.range (L₀ W)) (hf₁ : ∀ W, (f₁ W).val = LinearMap.range
        (L₁ W))
    (hL₀ : ∀ n, IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (stagePullback k n) fun V ↦ L₀ V.toInfinite)
    (hL₁ : ∀ n, IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (stagePullback k n) fun V ↦ L₁ V.toInfinite)
    (hinj : ∀ (t : I) (W : infiniteGrassmannian 𝕜 k),
      Injective ((1 - algebraMap ℝ 𝕜 t.val) • L₀ W + (algebraMap ℝ 𝕜 t.val) • L₁ W)) :
    f₀.Homotopic f₁ := by
  let hk := Module.finrank_fin_fun (R := 𝕜) (n := k)
  -- Phase 1 (stage construction): restrict `f₀, f₁` to each finite stage
  -- `finiteGrassmannian 𝕜 k n` and build linear-combination homotopies between them.
  let ιStage (n : ℕ) : C((diagram 𝕜 k).obj n, finiteGrassmannian 𝕜 k n) := ⟨id, continuous_id⟩
  have hc₀ (n : ℕ) : ((hL₀ n).classifyContinuousMap hk).comp (ιStage n) =
      f₀.comp ((cocone 𝕜 k).ι.app n).hom :=
    ContinuousMap.ext fun V ↦ Subtype.ext <| ((hL₀ n).coe_classify hk V).trans (hf₀ _).symm
  have hc₁ (n : ℕ) : ((hL₁ n).classifyContinuousMap hk).comp (ιStage n) =
      f₁.comp ((cocone 𝕜 k).ι.app n).hom :=
    ContinuousMap.ext fun V ↦ Subtype.ext <| ((hL₁ n).coe_classify hk V).trans (hf₁ _).symm
  let H (n : ℕ) :=
    (((hL₀ n).homotopyOfLinearCombinationInjective (hL₁ n)
      (fun t V ↦ hinj t V.toInfinite) hk).compContinuousMap (ιStage n)).cast (hc₀ n) (hc₁ n)
  have hH_val (n : ℕ) (t : I) (U : (diagram 𝕜 k).obj n) :
      (H n (t, U)).val = LinearMap.range
        ((1 - algebraMap ℝ 𝕜 t.val) • L₀ (toInfinite U) +
          (algebraMap ℝ 𝕜 t.val) • L₁ (toInfinite U)) := by
    rw [ContinuousMap.Homotopy.cast_apply, ContinuousMap.Homotopy.compContinuousMap_apply]
    exact (hL₀ n).coe_homotopyOfLinearCombinationInjective (hL₁ n)
      (fun t V ↦ hinj t V.toInfinite) hk t (ιStage n U)
  -- Phase 2 (colimit descent): verify compatibility along stage inclusions and glue via
  -- `isColimit.homotopyDesc`.
  exact ⟨(isColimit 𝕜 k).homotopyDesc (f := f₀) (g := f₁) H fun m n u t V ↦ Subtype.ext <| by
    have hmap : toInfinite ((diagram 𝕜 k).map u V) = toInfinite V :=
      (congrArg toInfinite (diagram_map_apply k u V)).trans
        (toInfinite_ambientInclusion (leOfHom u) V)
    exact (hH_val n t ((diagram 𝕜 k).map u V)).trans <|
      (congrArg (fun W ↦ LinearMap.range
        ((1 - algebraMap ℝ 𝕜 t.val) • L₀ W + (algebraMap ℝ 𝕜 t.val) • L₁ W)) hmap).trans
        (hH_val m t V).symm⟩

private theorem homotopic_id_mapContinuousMap_lmapDomain_of_le {s : ℕ → ℕ}
    (hs : Injective s) (hle : ∀ m, m ≤ s m) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (mapContinuousMap (lmapDomain 𝕜 𝕜 s) (mapDomain_injective hs)) :=
  homotopic_of_stage_isClassifyingCoordinates (fun W ↦ Tautological.subtype W)
    (fun W ↦ (lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W))
    (fun W ↦ (Tautological.range_subtype W).symm)
    (fun W ↦ (coe_map _ _ W).trans (by rw [LinearMap.range_comp, Tautological.range_subtype]))
    (fun _ ↦ isClassifyingCoordinates_stageTautological)
    (fun _ ↦ isClassifyingCoordinates_stageTautological.postcomp
      (FiberBundle.continuous_proj (Fin k → 𝕜) _) (lmapDomain 𝕜 𝕜 s) (mapDomain_injective hs))
    fun t W ↦ by
      have heq : (1 - algebraMap ℝ 𝕜 t.val) • Tautological.subtype W +
          (algebraMap ℝ 𝕜 t.val) • (lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W) =
        ((1 - algebraMap ℝ 𝕜 t.val) • (LinearMap.id : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) +
          (algebraMap ℝ 𝕜 t.val) • lmapDomain 𝕜 𝕜 s).comp (Tautological.subtype W) := by ext; simp
      rw [heq]
      exact (one_sub_smul_id_add_smul_lmapDomain_injective hs hle _).comp
        (Tautological.subtype_injective W)

private theorem homotopic_id_of_stage_isClassifyingCoordinates
    {f : C(infiniteGrassmannian 𝕜 k, infiniteGrassmannian 𝕜 k)}
    (L : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜))
    (hf : ∀ W, (f W).val = LinearMap.range (L W))
    (hL : ∀ n, IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (stagePullback k n) (fun V ↦ L V.toInfinite))
    (hinj : ∀ W, Injective (L W)) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic f := by
  let φ₀ := lmapDomain (M := 𝕜) (R := 𝕜) (fun m ↦ 2 * m)
  let φ₁ := lmapDomain (M := 𝕜) (R := 𝕜) (fun m ↦ 2 * m + 1)
  have hφ₀ := mapDomain_injective (M := 𝕜) strictMono_even.injective
  have hφ₁ := mapDomain_injective (M := 𝕜) strictMono_odd.injective
  have hmid : (mapContinuousMap φ₀ hφ₀).Homotopic ((mapContinuousMap φ₁ hφ₁).comp f) :=
    homotopic_of_stage_isClassifyingCoordinates (fun W ↦ φ₀.comp (Tautological.subtype W))
      (fun W ↦ φ₁.comp (L W))
      (fun W ↦ (coe_map _ _ W).trans (by rw [LinearMap.range_comp, Tautological.range_subtype]))
      (fun W ↦ (coe_map _ _ (f W)).trans (by rw [LinearMap.range_comp, ← hf W]))
      (fun _ ↦ isClassifyingCoordinates_stageTautological.postcomp
        (FiberBundle.continuous_proj (Fin k → 𝕜) _) φ₀ hφ₀)
      (fun n ↦ (hL n).postcomp (FiberBundle.continuous_proj (Fin k → 𝕜) _) φ₁ hφ₁)
      fun t W ↦ one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
        strictMono_even.injective strictMono_odd.injective disjoint_range_even_odd
        (Tautological.subtype_injective W) (hinj W) (algebraMap ℝ 𝕜 t.val)
  exact (homotopic_id_mapContinuousMap_lmapDomain_of_le (𝕜 := 𝕜) (k := k)
      strictMono_even.injective strictMono_even.id_le).trans
    (hmid.trans (ContinuousMap.Homotopic.comp
      (homotopic_id_mapContinuousMap_lmapDomain_of_le (𝕜 := 𝕜) (k := k)
        strictMono_odd.injective strictMono_odd.id_le) (.refl f)).symm)
end Normed

/-- Over `[NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]`, any injective linear endomorphism
`φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)` induces a self-map of `infiniteGrassmannian 𝕜 k` homotopic to the
identity. -/
theorem homotopic_id_mapContinuousMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic (mapContinuousMap (k := k) φ hφ) :=
  homotopic_id_of_stage_isClassifyingCoordinates (fun W ↦ φ.comp (Tautological.subtype W))
    (fun W ↦ (coe_map _ _ W).trans (by rw [LinearMap.range_comp, Tautological.range_subtype]))
    (fun _ ↦ isClassifyingCoordinates_stageTautological.postcomp
      (FiberBundle.continuous_proj (Fin k → 𝕜) _) φ hφ)
    fun W ↦ hφ.comp (Tautological.subtype_injective W)

/-- Over `[NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]`, any two families of classifying
coordinates on the same vector bundle `E` induce homotopic classifying maps. -/
theorem _root_.TauCeti.IsClassifyingCoordinates.homotopic_classifyContinuousMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hk : Module.finrank 𝕜 F = k) :
    (hj₀.classifyContinuousMap hk).Homotopic (hj₁.classifyContinuousMap hk) := by
  have hπ : Continuous (π F E) := FiberBundle.continuous_proj F E
  let φ₀ := lmapDomain (M := 𝕜) (R := 𝕜) (fun m ↦ 2 * m)
  let φ₁ := lmapDomain (M := 𝕜) (R := 𝕜) (fun m ↦ 2 * m + 1)
  have hφ₀ := mapDomain_injective (M := 𝕜) strictMono_even.injective
  have hφ₁ := mapDomain_injective (M := 𝕜) strictMono_odd.injective
  have hmid : ((hj₀.postcomp hπ φ₀ hφ₀).classifyContinuousMap hk).Homotopic
      ((hj₁.postcomp hπ φ₁ hφ₁).classifyContinuousMap hk) :=
    ⟨(hj₀.postcomp hπ φ₀ hφ₀).homotopyOfLinearCombinationInjective (hj₁.postcomp hπ φ₁ hφ₁)
      (fun _ x ↦ one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
        strictMono_even.injective strictMono_odd.injective disjoint_range_even_odd
        (hj₀.injective x) (hj₁.injective x) _) hk⟩
  rw [hj₀.classifyContinuousMap_postcomp φ₀ hφ₀ hk,
    hj₁.classifyContinuousMap_postcomp φ₁ hφ₁ hk] at hmid
  exact (ContinuousMap.Homotopic.comp
    (homotopic_id_mapContinuousMap (k := k) φ₀ hφ₀) (.refl _)).trans
    (hmid.trans (ContinuousMap.Homotopic.comp
      (homotopic_id_mapContinuousMap (k := k) φ₁ hφ₁) (.refl _)).symm)

/-- Over `[NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]`, classifying coordinates on
`Tautological 𝕜 k` induce a classifying map homotopic to `id`. -/
theorem homotopic_id_classifyContinuousMap_tautological
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    {j : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) j) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (hj.classifyContinuousMap (Module.finrank_fin_fun 𝕜)) :=
  homotopic_id_of_stage_isClassifyingCoordinates j (fun _ ↦ by simp)
    (fun n ↦ hj.pullback (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n))) hj.injective

/-- Over `RCLike 𝕜`, if the pullbacks of `Tautological 𝕜 k` along `f₀, f₁` admit a continuous
fibrewise linear equivalence, then `f₀` and `f₁` are homotopic. -/
theorem homotopic_of_continuousLinearEquiv_pullback
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) p.proj
          (Φ p.proj p.snd)) :
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
          p.proj (Φ p.proj p.snd) :=
  ⟨fun h ↦ (h.exists_continuousLinearEquiv_pullback (𝕜 := 𝕜) (F := Fin k → 𝕜)
      (E := Tautological 𝕜 k)).imp fun _ hΦ ↦ hΦ.1,
   fun ⟨Φ, hΦ⟩ ↦ homotopic_of_continuousLinearEquiv_pullback Φ hΦ⟩

open FiniteRankBundleCore (ofBundle ofBundleIso pullback_ofBundle pullbackOfBundleHomeomorph
  pullbackOfBundleHomeomorph_apply isoOfContinuousEquiv fiberMap_isoOfContinuousEquiv_hom
  fiberMap_isoOfContinuousEquiv_inv fiberMap_ofBundleIso_hom fiberMap_ofBundleIso_inv
  fiberMap_eqToHom_apply fiberMap_comp pullbackRankClass pullbackRankClass_mk)
section CoreComparisons
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]
variable (𝕜) in
/-- `Tautological 𝕜 k` as an object of `FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k)`. -/
abbrev tautologicalCore (k : ℕ) : FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k) :=
  ofBundle 𝕜 k (Tautological 𝕜 k)

/-- Continuous fibrewise linear equivalences of `Tautological` pullbacks yield core isomorphisms. -/
theorem nonempty_pullback_iso_of_continuousLinearEquiv_pullback [CompleteSpace 𝕜] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) p.proj
          (Φ p.proj p.snd)) :
    Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) := by
  rw [pullback_ofBundle, pullback_ofBundle]
  exact ⟨ofBundleIso (E₀ := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k))
    (E₁ := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) Φ hΦ⟩

/-- Core isomorphisms of `tautologicalCore` pullbacks yield continuous fibrewise equivalences. -/
theorem exists_continuousLinearEquiv_pullback_of_pullback_iso {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (α : (tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :
    ∃ Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x),
      Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (Φ p.proj p.snd) :=
  FiniteRankBundleCore.exists_continuousLinearEquiv_of_ofBundle_iso
    (E₀ := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) (E₁ := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
    ((eqToIso (pullback_ofBundle _ f₀)).symm.trans (α.trans (eqToIso (pullback_ofBundle _ f₁))))

section OfClassifying
variable [CompleteSpace 𝕜] {k : ℕ} {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k)
  {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
  (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j)
/-- Classifying coordinates on `A` identify `(tautologicalCore 𝕜 k).pullback` with `A`. -/
def tautologicalPullbackIsoOfClassifyingCoordinates :
    (tautologicalCore 𝕜 k).pullback
      (hj.classifyContinuousMap ((Module.finrank_fin_fun 𝕜).trans hA)) ≅ A :=
  let hk := (Module.finrank_fin_fun (R := 𝕜)).trans hA
  let f := hj.classifyContinuousMap hk
  let eT := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  isoOfContinuousEquiv (fun x ↦ (eT (f x)).trans (hj.classifyTautologicalEquiv hk x).symm)
    (((hj.classifyTautologicalHomeomorph hk).symm.continuous.comp
      (pullbackOfBundleHomeomorph (Tautological 𝕜 k) f).continuous).congr fun ⟨x, v⟩ ↦ by
        rw [comp_apply, pullbackOfBundleHomeomorph_apply]
        exact hj.classifyTautologicalHomeomorph_symm_apply hk ⟨x, eT (f x) v⟩)
@[simp] theorem fiberMap_tautologicalPullbackIsoOfClassifyingCoordinates_hom (x : X) :
    (tautologicalPullbackIsoOfClassifyingCoordinates hA hj).hom.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
          (hj.classify ((Module.finrank_fin_fun 𝕜).trans hA) x)).trans
            (hj.classifyTautologicalEquiv ((Module.finrank_fin_fun 𝕜).trans hA) x).symm) := by
  rw [tautologicalPullbackIsoOfClassifyingCoordinates]
  exact fiberMap_isoOfContinuousEquiv_hom (𝕜 := 𝕜) _ _ x
@[simp] theorem fiberMap_tautologicalPullbackIsoOfClassifyingCoordinates_inv (x : X) :
    (tautologicalPullbackIsoOfClassifyingCoordinates hA hj).inv.fiberMap x =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((hj.classifyTautologicalEquiv ((Module.finrank_fin_fun 𝕜).trans hA) x).trans
          (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
            (hj.classify ((Module.finrank_fin_fun 𝕜).trans hA) x)).symm) :=
  (fiberMap_isoOfContinuousEquiv_inv (𝕜 := 𝕜) _ _ x).trans <|
    ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦
      ContinuousLinearEquiv.symm_trans_apply _ _ v
end OfClassifying

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
open finiteGrassmannian (toInfiniteContinuousMap toInfiniteTautologicalEquiv
  toInfiniteTautologicalHomeomorph toInfiniteTautologicalHomeomorph_apply)
private theorem pointIndexedCoreFiberEquiv_toInfinite_pullback_symm_apply
    {k n : ℕ} (V : finiteGrassmannian 𝕜 k n) (w : Tautological 𝕜 k V.toInfinite) :
    (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (stagePullback k n) V).symm w =
      (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).symm w := by
  let f := toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)
  let z : TotalSpace (Fin k → 𝕜) ((f : _ → _) *ᵖ (Tautological 𝕜 k)) := ⟨V, w⟩
  refine (pointIndexedCoreFiberEquiv_symm_apply 𝕜 (Fin k → 𝕜)
    ((f : _ → _) *ᵖ (Tautological 𝕜 k)) V z.snd).trans ?_
  rw [trivializationAt, FiberBundle.pullback_trivializationAt', Trivialization.pullback_apply]
  exact (congrArg (fun p ↦ (trivializationAt (Fin k → 𝕜) (Tautological 𝕜 k) (f V) p).2)
    (Pullback.lift_mk (F := Fin k → 𝕜) (E := Tautological 𝕜 k) f V w)).trans
      (pointIndexedCoreFiberEquiv_symm_apply 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) (f V) w).symm
private theorem pointIndexedCoreFiberEquiv_toInfinite_pullback_apply
    {k n : ℕ} (V : finiteGrassmannian 𝕜 k n) (v : Fin k → 𝕜) :
    pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (stagePullback k n) V v =
      pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite v :=
  let eS := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (stagePullback k n) V
  let eT := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite
  eT.symm.injective <| (pointIndexedCoreFiberEquiv_toInfinite_pullback_symm_apply V _).symm.trans <|
    (eS.symm_apply_apply v).trans (eT.symm_apply_apply v).symm
private theorem continuous_toInfiniteTautologicalEquiv (k n : ℕ) :
    Continuous fun p : TotalSpace (Fin k → 𝕜) (finiteGrassmannian.Tautological 𝕜 k n) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := stagePullback k n)
        p.proj (toInfiniteTautologicalEquiv p.proj p.snd) :=
  (toInfiniteTautologicalHomeomorph 𝕜 k n).continuous.congr toInfiniteTautologicalHomeomorph_apply

/-- Over `RCLike 𝕜`, pulling back `tautologicalCore 𝕜 k` along `toInfiniteContinuousMap` is
isomorphic to `ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n)`. -/
def _root_.TauCeti.finiteGrassmannian.pullbackTautologicalCoreIso (k n : ℕ) :
    (tautologicalCore 𝕜 k).pullback (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)) ≅
      ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n) :=
  (eqToIso (pullback_ofBundle (Tautological 𝕜 k)
    (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)))).trans
    (ofBundleIso (E₀ := finiteGrassmannian.Tautological 𝕜 k n) (E₁ := stagePullback k n)
      toInfiniteTautologicalEquiv (continuous_toInfiniteTautologicalEquiv k n)).symm
@[simp] theorem _root_.TauCeti.finiteGrassmannian.fiberMap_pullbackTautologicalCoreIso_hom
    (k n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    (finiteGrassmannian.pullbackTautologicalCoreIso (𝕜 := 𝕜) k n).hom.fiberMap V =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).trans
          (V.toInfiniteTautologicalEquiv.symm.trans
            (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
              (finiteGrassmannian.Tautological 𝕜 k n) V).symm)) := by
  rw [finiteGrassmannian.pullbackTautologicalCoreIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    fiberMap_comp]
  have hIso := DFunLike.congr_fun (fiberMap_ofBundleIso_inv
    (E₀ := finiteGrassmannian.Tautological 𝕜 k n) (E₁ := stagePullback k n)
    toInfiniteTautologicalEquiv (continuous_toInfiniteTautologicalEquiv k n) V)
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv : (eqToHom (pullback_ofBundle (Tautological 𝕜 k)
      (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n)))).fiberMap V v = v :=
    funext fun _ ↦ by simp only [fiberMap_eqToHom_apply, Fin.cast_refl, id_eq]
  rw [ContinuousLinearMap.comp_apply, hv, hIso]
  exact congrArg ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
      (finiteGrassmannian.Tautological 𝕜 k n) V).symm ∘ V.toInfiniteTautologicalEquiv.symm)
    (pointIndexedCoreFiberEquiv_toInfinite_pullback_apply V v)
@[simp] theorem _root_.TauCeti.finiteGrassmannian.fiberMap_pullbackTautologicalCoreIso_inv
    (k n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    (finiteGrassmannian.pullbackTautologicalCoreIso (𝕜 := 𝕜) k n).inv.fiberMap V =
      ContinuousLinearEquiv.toContinuousLinearMap
        ((pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (finiteGrassmannian.Tautological 𝕜 k n) V).trans
          (V.toInfiniteTautologicalEquiv.trans
            (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) V.toInfinite).symm)) := by
  rw [finiteGrassmannian.pullbackTautologicalCoreIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
    fiberMap_comp]
  have hIso := DFunLike.congr_fun (fiberMap_ofBundleIso_hom
    (E₀ := finiteGrassmannian.Tautological 𝕜 k n) (E₁ := stagePullback k n)
    toInfiniteTautologicalEquiv (continuous_toInfiniteTautologicalEquiv k n) V)
  refine ContinuousLinearMap.ext fun v ↦ funext fun i ↦ ?_
  rw [ContinuousLinearMap.comp_apply, fiberMap_eqToHom_apply, hIso]
  simp only [Fin.cast_refl, id_eq]
  exact congrArg (· i) (pointIndexedCoreFiberEquiv_toInfinite_pullback_symm_apply V _)

section Paracompact
variable [ParacompactSpace X] [R1Space X]
/-- Over `RCLike 𝕜` and paracompact `R₁` `X`, `f₀, f₁` are homotopic iff their pulled-back
`tautologicalCore`s are isomorphic. -/
theorem homotopic_iff_nonempty_pullback_iso {k : ℕ} {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)} :
    f₀.Homotopic f₁ ↔
      Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :=
  homotopic_iff_exists_continuousLinearEquiv_pullback.trans
    ⟨fun ⟨Φ, hΦ⟩ ↦ nonempty_pullback_iso_of_continuousLinearEquiv_pullback Φ hΦ,
     fun ⟨α⟩ ↦ exists_continuousLinearEquiv_pullback_of_pullback_iso α⟩
variable (𝕜 X) in
/-- **Universal vector bundle classification (`BO(k)` / `BU(k)`):** bijection from homotopy classes
`[X, infiniteGrassmannian 𝕜 k]` to rank-`k` core isomorphism classes over paracompact `R₁` `X`. -/
def classificationEquiv (k : ℕ) :
    Quotient ⟨ContinuousMap.Homotopic (X := X) (Y := infiniteGrassmannian 𝕜 k),
        ContinuousMap.Homotopic.equivalence⟩ ≃
      Quotient ((isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _)) :=
  Equiv.ofBijective
    (Quotient.map (sa := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
      (sb := (isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap Subtype.val)
      (fun f ↦ ⟨(tautologicalCore 𝕜 k).pullback f, rfl⟩)
      fun _ _ h ↦ homotopic_iff_nonempty_pullback_iso.1 h)
    ⟨Quotient.ind₂ fun _ _ h ↦
        Quotient.sound (homotopic_iff_nonempty_pullback_iso.2 (Quotient.exact h)),
     Quotient.ind fun A ↦ let ⟨f, hf⟩ := exists_pullback_tautologicalCore_iso A.val A.property
        ⟨Quotient.mk _ f, Quotient.sound hf⟩⟩
@[simp] theorem classificationEquiv_mk (k : ℕ) (f : C(X, infiniteGrassmannian 𝕜 k)) :
    classificationEquiv 𝕜 X k (Quotient.mk _ f) =
      Quotient.mk _ ⟨(tautologicalCore 𝕜 k).pullback f, rfl⟩ := (rfl)
/-- `(classificationEquiv 𝕜 X k).symm` sends `[A]` to `[hj.classifyContinuousMap ...]`. -/
theorem classificationEquiv_symm_mk_of_isClassifyingCoordinates
    {k : ℕ} (A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k})
    {j : ∀ x, A.val.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.val.rank → 𝕜) A.val.core.Fiber j) :
    (classificationEquiv 𝕜 X k).symm (Quotient.mk _ A) =
      Quotient.mk _ (hj.classifyContinuousMap ((Module.finrank_fin_fun 𝕜).trans A.property)) :=
  (classificationEquiv 𝕜 X k).injective <| by
    rw [Equiv.apply_symm_apply, classificationEquiv_mk]
    exact Quotient.sound ⟨(tautologicalPullbackIsoOfClassifyingCoordinates A.property hj).symm⟩
/-- Any constant map into `infiniteGrassmannian 𝕜 k` classifies `FiniteRankBundleCore.trivial`. -/
theorem classificationEquiv_const (k : ℕ) (W : infiniteGrassmannian 𝕜 k) :
    classificationEquiv 𝕜 X k (Quotient.mk _ (ContinuousMap.const X W)) =
      Quotient.mk _ ⟨FiniteRankBundleCore.trivial 𝕜 X k, rfl⟩ :=
  congrArg (Quotient.mk _) (Subtype.ext ((tautologicalCore 𝕜 k).pullback_const W))
/-- `(classificationEquiv 𝕜 X k).symm` sends `trivial 𝕜 X k` to `[const X (basepoint 𝕜 k)]`. -/
@[simp] theorem classificationEquiv_symm_trivial (k : ℕ) :
    (classificationEquiv 𝕜 X k).symm (Quotient.mk _ ⟨FiniteRankBundleCore.trivial 𝕜 X k, rfl⟩) =
      Quotient.mk _ (ContinuousMap.const X (basepoint 𝕜 k)) :=
  (classificationEquiv 𝕜 X k).injective <| by rw [Equiv.apply_symm_apply, classificationEquiv_const]
end Paracompact
/-- The identity map of `infiniteGrassmannian 𝕜 k` classifies `tautologicalCore 𝕜 k`. -/
theorem classificationEquiv_id (k : ℕ) :
    classificationEquiv 𝕜 (infiniteGrassmannian 𝕜 k) k (Quotient.mk _ (ContinuousMap.id _)) =
      Quotient.mk _ ⟨tautologicalCore 𝕜 k, rfl⟩ :=
  congrArg (Quotient.mk _) (Subtype.ext (tautologicalCore 𝕜 k).pullback_id)
/-- `(classificationEquiv _ _ k).symm` sends `tautologicalCore 𝕜 k` to `[id]`. -/
@[simp] theorem classificationEquiv_symm_tautologicalCore (k : ℕ) :
    (classificationEquiv 𝕜 (infiniteGrassmannian 𝕜 k) k).symm
      (Quotient.mk _ ⟨tautologicalCore 𝕜 k, rfl⟩) = Quotient.mk _ (ContinuousMap.id _) :=
  (classificationEquiv 𝕜 (infiniteGrassmannian 𝕜 k) k).injective <| by
    rw [Equiv.apply_symm_apply, classificationEquiv_id]
/-- `finiteGrassmannian.toInfiniteContinuousMap` classifies `finiteGrassmannian.Tautological`. -/
theorem classificationEquiv_toInfiniteContinuousMap (k n : ℕ) :
    classificationEquiv 𝕜 (finiteGrassmannian 𝕜 k n) k (Quotient.mk _ toInfiniteContinuousMap) =
      Quotient.mk _ ⟨ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n), rfl⟩ :=
  Quotient.sound ⟨finiteGrassmannian.pullbackTautologicalCoreIso k n⟩
/-- `(classificationEquiv _ _ k).symm` sends `finiteGrassmannian.Tautological` to
`[toInfiniteContinuousMap]`. -/
@[simp] theorem classificationEquiv_symm_finiteTautological (k n : ℕ) :
    (classificationEquiv 𝕜 (finiteGrassmannian 𝕜 k n) k).symm
      (Quotient.mk _ ⟨ofBundle 𝕜 k (finiteGrassmannian.Tautological 𝕜 k n), rfl⟩) =
        Quotient.mk _ toInfiniteContinuousMap :=
  (classificationEquiv 𝕜 (finiteGrassmannian 𝕜 k n) k).injective <| by
    rw [Equiv.apply_symm_apply, classificationEquiv_toInfiniteContinuousMap]
section Naturality
variable {X' : Type*} [TopologicalSpace X'] [ParacompactSpace X] [R1Space X]
  [ParacompactSpace X'] [R1Space X'] (g : C(X', X)) (k : ℕ)
/-- Naturality of `classificationEquiv` under pullback along `g : C(X', X)`. -/
theorem classificationEquiv_comp (f : C(X, infiniteGrassmannian 𝕜 k)) :
    classificationEquiv 𝕜 X' k (Quotient.mk _ (f.comp g)) =
      pullbackRankClass g k (classificationEquiv 𝕜 X k (Quotient.mk _ f)) := by
  rw [classificationEquiv_mk, classificationEquiv_mk, pullbackRankClass_mk]
  exact congrArg (Quotient.mk _) (Subtype.ext ((tautologicalCore 𝕜 k).pullback_comp g f).symm)
/-- Naturality of `(classificationEquiv 𝕜 X k).symm` under `pullbackRankClass g k`. -/
theorem classificationEquiv_symm_pullbackRankClass
    (c : Quotient ((isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
      (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _))) :
    (classificationEquiv 𝕜 X' k).symm (pullbackRankClass g k c) =
      Quotient.map (sa := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
        (sb := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
        (fun f : C(X, infiniteGrassmannian 𝕜 k) ↦ f.comp g) (fun _ _ h ↦ h.comp (.refl g))
        ((classificationEquiv 𝕜 X k).symm c) := by
  rcases (classificationEquiv 𝕜 X k).surjective c with ⟨q, rfl⟩
  refine Quotient.inductionOn q fun f ↦ (classificationEquiv 𝕜 X' k).injective ?_
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Quotient.map_mk, classificationEquiv_comp]
end Naturality
end Bijection
end infiniteGrassmannian
end TauCeti
