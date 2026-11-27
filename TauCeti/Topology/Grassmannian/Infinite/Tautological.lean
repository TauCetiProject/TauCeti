/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Infinite.Basic
public import TauCeti.Topology.Grassmannian.Tautological
public import TauCeti.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Pullback
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The universal tautological bundle over the infinite Grassmannian

For a field `𝕜` and `k : ℕ`, `TauCeti.infiniteGrassmannian.Tautological 𝕜 k` is the universal
rank-`k` bundle over `TauCeti.infiniteGrassmannian 𝕜 k` whose pullbacks classify rank-`k` vector
bundles (`TauCeti.Topology.Grassmannian.Infinite.Classification`). Each plane carries the canonical
`𝕜`-module topology, and the total space embeds into `infiniteGrassmannian 𝕜 k × (ℕ → 𝕜)`
(`isEmbedding_totalSpaceEmbed`, `continuous_totalSpace_iff`). Over
`[IsTopologicalDivisionRing 𝕜] [T1Space 𝕜]` it is a rank-`k` `FiberBundle` over the
coordinate-minor charts `chartDomain u` (`u : Fin k ↪ ℕ`), functorial under ambient injections
(`mapTautologicalHomeomorph`); over `[NontriviallyNormedField 𝕜]` it is a `VectorBundle`, and over
`[RCLike 𝕜]` its pullback along finite-stage inclusions agrees with the finite Grassmannian bundle
(`finiteGrassmannian.toInfiniteTautologicalHomeomorph`).

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5; A. Hatcher, *Vector Bundles*, §1.2.
-/

public noncomputable section

open Bundle Set Function Topology _root_.Finsupp
open scoped Matrix

namespace TauCeti
namespace infiniteGrassmannian
open finiteGrassmannian

section TautologicalFiber
variable (𝕜 : Type*) [Field 𝕜] (k : ℕ)
/-- The **universal tautological bundle** `γ^k(𝕜^∞)` over `infiniteGrassmannian 𝕜 k`. -/
@[ext] structure Tautological (W : infiniteGrassmannian 𝕜 k) where
  /-- The underlying ambient coordinate vector in `ℕ →₀ 𝕜`. -/
  val : ℕ →₀ 𝕜
  /-- Membership of the vector in the subspace `W`. -/
  property : val ∈ W.val

section Algebraic
variable {𝕜 k} (W : infiniteGrassmannian 𝕜 k)
theorem Tautological.val_injective : Injective (Tautological.val : Tautological 𝕜 k W → ℕ →₀ 𝕜) :=
  fun _ _ ↦ Tautological.ext
instance : Zero (Tautological 𝕜 k W) := ⟨⟨0, W.val.zero_mem⟩⟩
instance : Add (Tautological 𝕜 k W) := ⟨fun v w ↦ ⟨v.val + w.val,
    W.val.add_mem v.property w.property⟩⟩
instance : Neg (Tautological 𝕜 k W) := ⟨fun v ↦ ⟨-v.val, W.val.neg_mem v.property⟩⟩
instance : Sub (Tautological 𝕜 k W) := ⟨fun v w ↦ ⟨v.val - w.val,
    W.val.sub_mem v.property w.property⟩⟩
instance {M : Type*} [SMul M 𝕜] [SMul M (ℕ →₀ 𝕜)] [IsScalarTower M 𝕜 (ℕ →₀ 𝕜)] :
    SMul M (Tautological 𝕜 k W) :=
  ⟨fun c v ↦ ⟨c • v.val, smul_one_smul 𝕜 c v.val ▸ W.val.smul_mem (c • (1 : 𝕜)) v.property⟩⟩
@[simp] theorem Tautological.val_zero : (0 : Tautological 𝕜 k W).val = 0 := (rfl)
@[simp] theorem Tautological.val_add (v w : Tautological 𝕜 k W) :
    (v + w).val = v.val + w.val := (rfl)
@[simp] theorem Tautological.val_neg (v : Tautological 𝕜 k W) : (-v).val = -v.val := (rfl)
@[simp] theorem Tautological.val_sub (v w : Tautological 𝕜 k W) :
    (v - w).val = v.val - w.val := (rfl)
@[simp] theorem Tautological.val_smul {M : Type*} [SMul M 𝕜] [SMul M (ℕ →₀ 𝕜)]
    [IsScalarTower M 𝕜 (ℕ →₀ 𝕜)] (c : M) (v : Tautological 𝕜 k W) : (c • v).val = c • v.val := (rfl)
instance : AddCommGroup (Tautological 𝕜 k W) :=
  (Tautological.val_injective W).addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
instance : Module 𝕜 (Tautological 𝕜 k W) :=
  (Tautological.val_injective W).module 𝕜
    { toFun := Tautological.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl } fun _ _ ↦ rfl
/-- The canonical linear inclusion of the tautological fibre over `W` into `ℕ →₀ 𝕜`. -/
def Tautological.subtype : Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  { toFun := Tautological.val, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
@[simp] theorem Tautological.subtype_apply (v : Tautological 𝕜 k W) :
    Tautological.subtype W v = v.val := (rfl)
theorem Tautological.subtype_injective : Injective (Tautological.subtype W) :=
  Tautological.val_injective W
/-- The image of `Tautological.subtype W` is the underlying submodule `W.1`. -/
@[simp] theorem Tautological.range_subtype : LinearMap.range (Tautological.subtype W) = W.val :=
  le_antisymm (by rintro _ ⟨v, rfl⟩; exact v.property) fun w hw ↦ ⟨⟨w, hw⟩, rfl⟩
variable (𝕜 k) in
/-- The tautological fibre over `W` identified `𝕜`-linearly with the submodule `W.1`. -/
def tautologicalEquiv (W : infiniteGrassmannian 𝕜 k) : Tautological 𝕜 k W ≃ₗ[𝕜] W.val :=
  { toFun := fun v ↦ ⟨v.val, v.property⟩, invFun := fun v ↦ ⟨v.val, v.property⟩,
    map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl,
    left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
@[simp] theorem coe_tautologicalEquiv_apply (v : Tautological 𝕜 k W) :
    (tautologicalEquiv 𝕜 k W v : ℕ →₀ 𝕜) = v.val := (rfl)
@[simp] theorem val_tautologicalEquiv_symm (v : W.val) :
    ((tautologicalEquiv 𝕜 k W).symm v).val = v.val := (rfl)
instance : FiniteDimensional 𝕜 (Tautological 𝕜 k W) :=
  have : FiniteDimensional 𝕜 W.val := .of_rank_eq_nat W.property
  Module.Finite.equiv (tautologicalEquiv 𝕜 k W).symm
@[simp] theorem finrank_tautological : Module.finrank 𝕜 (Tautological 𝕜 k W) = k :=
  (tautologicalEquiv 𝕜 k W).finrank_eq.trans (Module.finrank_eq_of_rank_eq W.property)
end Algebraic

section FiberTopology
variable {𝕜 k} [TopologicalSpace 𝕜] (W : infiniteGrassmannian 𝕜 k)
/-- Each fibre of `Tautological 𝕜 k` carries its canonical `𝕜`-module topology. -/
instance : TopologicalSpace (Tautological 𝕜 k W) := moduleTopology 𝕜 (Tautological 𝕜 k W)
instance : IsModuleTopology 𝕜 (Tautological 𝕜 k W) := ⟨rfl⟩
instance : IsTopologicalAddGroup (Tautological 𝕜 k W) :=
  IsModuleTopology.isTopologicalAddGroup 𝕜 (Tautological 𝕜 k W)
instance : ContinuousSMul 𝕜 (Tautological 𝕜 k W) :=
  ModuleTopology.continuousSMul 𝕜 (Tautological 𝕜 k W)
instance [IsTopologicalSemiring 𝕜] [T2Space 𝕜] : T2Space (Tautological 𝕜 k W) :=
  ModuleTopology.t2Space (Module.finBasis 𝕜 (Tautological 𝕜 k W))
end FiberTopology
end TautologicalFiber

section CoordProj
variable {𝕜 : Type*} [Semiring 𝕜] {k : ℕ}
/-- Projection of `ℕ →₀ 𝕜` onto the `k` coordinates selected by `u : Fin k ↪ ℕ`. -/
def coordProj (u : Fin k ↪ ℕ) : (ℕ →₀ 𝕜) →ₗ[𝕜] (Fin k → 𝕜) := LinearMap.pi fun i ↦ lapply (u i)
@[simp] theorem coordProj_apply (u : Fin k ↪ ℕ) (v : ℕ →₀ 𝕜) (i : Fin k) :
    coordProj u v i = v (u i) := (rfl)
end CoordProj

section ChartAlgebra
variable {𝕜 : Type*} [Field 𝕜] {k : ℕ}
/-- Restriction of the `u`-coordinate projection to the tautological fibre over `W`. -/
def chartLinearMap (u : Fin k ↪ ℕ) (W : infiniteGrassmannian 𝕜 k) :
    Tautological 𝕜 k W →ₗ[𝕜] (Fin k → 𝕜) := (coordProj u).comp (Tautological.subtype W)
@[simp] theorem chartLinearMap_apply (u : Fin k ↪ ℕ) (W : infiniteGrassmannian 𝕜 k)
    (v : Tautological 𝕜 k W) (i : Fin k) : chartLinearMap u W v i = v.val (u i) := (rfl)
/-- The chart domain for `u : Fin k ↪ ℕ`: `k`-planes projecting bijectively onto `u`. -/
def chartDomain (u : Fin k ↪ ℕ) : Set (infiniteGrassmannian 𝕜 k) :=
  {W | Bijective (chartLinearMap u W)}
@[simp] theorem mem_chartDomain_iff {u : Fin k ↪ ℕ} {W : infiniteGrassmannian 𝕜 k} :
    W ∈ chartDomain u ↔ Bijective (chartLinearMap u W) := Iff.rfl
theorem mem_chartDomain_iff_injective {u : Fin k ↪ ℕ} {W : infiniteGrassmannian 𝕜 k} :
    W ∈ chartDomain u ↔ Injective (chartLinearMap u W) :=
  ⟨Bijective.injective, fun h ↦ ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((finrank_tautological W).trans (Module.finrank_fin_fun 𝕜).symm)).1 h⟩⟩
theorem mem_chartDomain_iff_surjective {u : Fin k ↪ ℕ} {W : infiniteGrassmannian 𝕜 k} :
    W ∈ chartDomain u ↔ Surjective (chartLinearMap u W) :=
  mem_chartDomain_iff_injective.trans <| LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((finrank_tautological W).trans (Module.finrank_fin_fun 𝕜).symm)
private def frameCoordMatrix (u : Fin k ↪ ℕ) {n : ℕ} (f : finiteFullRankFrame 𝕜 k n) :
    Matrix (Fin k) (Fin k) 𝕜 := Matrix.of fun j i ↦ coordinateInclusion (R := 𝕜) n (f.val i) (u j)
private def stageFrameBasis {n : ℕ} (f : finiteFullRankFrame 𝕜 k n) :
    Module.Basis (Fin k) 𝕜 (Tautological 𝕜 k (toInfinite (frameSpan f))) :=
  (Module.Basis.span f.property).map <| (LinearEquiv.ofEq _ _ (coe_frameSpan f).symm).trans <|
    (Submodule.equivMapOfInjective _ (coordinateInclusion_injective n) _).trans <|
      (LinearEquiv.ofEq _ _ (coe_toInfinite _).symm).trans (tautologicalEquiv 𝕜 k _).symm
private theorem val_stageFrameBasis_apply {n : ℕ} (f : finiteFullRankFrame 𝕜 k n) (i : Fin k) :
    (stageFrameBasis f i).val = coordinateInclusion (R := 𝕜) n (f.val i) := by
  simp [stageFrameBasis]
private theorem chartLinearMap_stageFrameBasis_symm (u : Fin k ↪ ℕ) {n : ℕ}
    (f : finiteFullRankFrame 𝕜 k n) (c : Fin k → 𝕜) :
    chartLinearMap u (toInfinite (frameSpan f)) ((stageFrameBasis f).equivFun.symm c) =
      frameCoordMatrix u f *ᵥ c := by
  rw [Module.Basis.equivFun_symm_apply, map_sum]; ext j
  simp [Matrix.mulVec, dotProduct, val_stageFrameBasis_apply, frameCoordMatrix, mul_comm]
private theorem toInfinite_frameSpan_mem_chartDomain_iff (u : Fin k ↪ ℕ) {n : ℕ}
    (f : finiteFullRankFrame 𝕜 k n) :
    toInfinite (frameSpan f) ∈ chartDomain u ↔ IsUnit (frameCoordMatrix u f) := by
  have hcomp : chartLinearMap u (toInfinite (frameSpan f)) ∘ (stageFrameBasis f).equivFun.symm =
      (frameCoordMatrix u f).mulVec := funext (chartLinearMap_stageFrameBasis_symm u f)
  rw [mem_chartDomain_iff_injective, ← Matrix.mulVec_injective_iff_isUnit, ← hcomp]
  exact ⟨fun h ↦ h.comp (stageFrameBasis f).equivFun.symm.injective, fun h _ _ hxy ↦
    (stageFrameBasis f).equivFun.injective (h (by simpa [comp_apply] using hxy))⟩
/-- Every `k`-plane in `ℕ →₀ 𝕜` lies in `chartDomain u` for some `u : Fin k ↪ ℕ`. -/
theorem exists_mem_chartDomain (W : infiniteGrassmannian 𝕜 k) :
    ∃ u : Fin k ↪ ℕ, W ∈ chartDomain u := by
  obtain ⟨n, V, rfl⟩ := exists_toInfinite_eq W; obtain ⟨f, rfl⟩ := frameSpan_surjective V
  obtain ⟨e, he⟩ := Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero.1 f.property
  let u : Fin k ↪ ℕ := e.trans (Fin.valEmbedding (n := n))
  refine ⟨u, (toInfinite_frameSpan_mem_chartDomain_iff u f).2 ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hmat : frameCoordMatrix u f = ((Matrix.of f.val).submatrix id e)ᵀ := by
    ext j i; simp [frameCoordMatrix, u, coordinateInclusion_apply_val]
  rwa [hmat, Matrix.det_transpose]
/-- A chosen coordinate chart index `u : Fin k ↪ ℕ` whose domain contains `W`. -/
def chartIndex (W : infiniteGrassmannian 𝕜 k) : Fin k ↪ ℕ := (exists_mem_chartDomain W).choose
/-- Every point `W` lies in the chart domain of `chartIndex W`. -/
theorem mem_chartDomain_chartIndex (W : infiniteGrassmannian 𝕜 k) :
    W ∈ chartDomain (chartIndex W) := (exists_mem_chartDomain W).choose_spec
/-- Canonical embedding of `TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)` into
`infiniteGrassmannian 𝕜 k × (ℕ → 𝕜)`. -/
def totalSpaceEmbed (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :
    infiniteGrassmannian 𝕜 k × (ℕ → 𝕜) := (p.proj, fun m ↦ p.snd.val m)
@[simp] theorem totalSpaceEmbed_fst (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :
    (totalSpaceEmbed p).1 = p.proj := (rfl)
@[simp] theorem totalSpaceEmbed_snd_apply (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) (m : ℕ) :
    (totalSpaceEmbed p).2 m = p.snd.val m := (rfl)
theorem totalSpaceEmbed_injective :
    Injective (totalSpaceEmbed : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) → _) := by
  rintro ⟨W₁, v₁⟩ ⟨W₂, v₂⟩ h; obtain rfl : W₁ = W₂ := congrArg Prod.fst h
  exact congrArg (TotalSpace.mk W₁)
    (Tautological.ext (Finsupp.ext (congrFun (congrArg Prod.snd h))))
end ChartAlgebra

section TotalSpaceTopology
variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] {k : ℕ}
variable (𝕜 k) in
/-- The total space of `Tautological 𝕜 k` carries the topology induced by `totalSpaceEmbed`. -/
instance : TopologicalSpace (TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :=
  TopologicalSpace.induced totalSpaceEmbed inferInstance
/-- `totalSpaceEmbed` is a topological embedding into `infiniteGrassmannian 𝕜 k × (ℕ → 𝕜)`. -/
theorem isEmbedding_totalSpaceEmbed :
    IsEmbedding (totalSpaceEmbed : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) → _) :=
  ⟨⟨rfl⟩, totalSpaceEmbed_injective⟩
/-- A map into `TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)` is continuous iff its base map and all
ambient coordinates `m : ℕ` are continuous. -/
theorem continuous_totalSpace_iff {Z : Type*} [TopologicalSpace Z]
    {f : Z → TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)} :
    Continuous f ↔ Continuous (fun z ↦ (f z).proj) ∧ ∀ m : ℕ, Continuous fun z ↦ (f z).snd.val m
        := by
  rw [isEmbedding_totalSpaceEmbed.isInducing.continuous_iff]
  simp only [comp_def, totalSpaceEmbed, continuous_prodMk, continuous_pi_iff]
/-- Evaluating coordinate `m : ℕ` is continuous on the total space of `Tautological 𝕜 k`. -/
@[fun_prop] theorem continuous_evalCoord (m : ℕ) :
    Continuous fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦ p.snd.val m :=
  (continuous_totalSpace_iff.1 continuous_id).2 m
/-- An injective linear endomorphism `φ` of `ℕ →₀ 𝕜` acts fibrewise on `Tautological 𝕜 k`. -/
def mapTautologicalEquiv (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (W : infiniteGrassmannian 𝕜 k) : Tautological 𝕜 k W ≃L[𝕜] Tautological 𝕜 k (map φ hφ W) :=
  ((tautologicalEquiv 𝕜 k W).trans <| (Submodule.equivMapOfInjective φ hφ W.val).trans <|
    (LinearEquiv.ofEq _ _ (coe_map φ hφ W).symm).trans
      (tautologicalEquiv 𝕜 k (map φ hφ W)).symm).toContinuousLinearEquivOfIsModuleTopology
@[simp] theorem val_mapTautologicalEquiv (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (W : infiniteGrassmannian 𝕜 k) (v : Tautological 𝕜 k W) :
    (mapTautologicalEquiv φ hφ W v).val = φ v.val := by simp [mapTautologicalEquiv]
end TotalSpaceTopology

section ChartEquiv
variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜] {k : ℕ}
section Maps
variable (u : Fin k ↪ ℕ) {W : infiniteGrassmannian 𝕜 k} (hW : W ∈ chartDomain u)
/-- Continuous linear equivalence `Tautological 𝕜 k W ≃L[𝕜] (Fin k → 𝕜)` over `chartDomain u`. -/
def chartEquiv : Tautological 𝕜 k W ≃L[𝕜] (Fin k → 𝕜) :=
  (LinearEquiv.ofBijective (chartLinearMap u W) hW).toContinuousLinearEquivOfIsModuleTopology
@[simp] theorem chartEquiv_apply (v : Tautological 𝕜 k W) :
    chartEquiv u hW v = chartLinearMap u W v :=
  congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology _) v
@[simp] theorem chartLinearMap_chartEquiv_symm (v : Fin k → 𝕜) :
    chartLinearMap u W ((chartEquiv u hW).symm v) = v := by
  rw [← chartEquiv_apply u hW, ContinuousLinearEquiv.apply_symm_apply]
@[simp] theorem chartEquiv_symm_chartLinearMap (v : Tautological 𝕜 k W) :
    (chartEquiv u hW).symm (chartLinearMap u W v) = v := by
  rw [← chartEquiv_apply u hW, ContinuousLinearEquiv.symm_apply_apply]
end Maps
private theorem continuous_frameCoordMatrix (u : Fin k ↪ ℕ) (n : ℕ) :
    Continuous (frameCoordMatrix (𝕜 := 𝕜) u (n := n)) :=
  continuous_matrix fun j i ↦ (LinearMap.continuous_on_pi ((lapply (R := 𝕜) (M := 𝕜) (u j)).comp
    (coordinateInclusion (R := 𝕜) n))).comp ((continuous_apply i).comp continuous_subtypeVal)
private theorem chartEquiv_symm_stageFrameBasis (u : Fin k ↪ ℕ) {n : ℕ}
    (f : finiteFullRankFrame 𝕜 k n) (hf : toInfinite (frameSpan f) ∈ chartDomain u)
    (v : Fin k → 𝕜) : (chartEquiv u hf).symm v =
      (stageFrameBasis f).equivFun.symm ((frameCoordMatrix u f)⁻¹ *ᵥ v) := by
  have hu := (toInfinite_frameSpan_mem_chartDomain_iff u f).1 hf; apply hf.1
  rw [chartLinearMap_chartEquiv_symm, chartLinearMap_stageFrameBasis_symm, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.one_mulVec]
/-- Inclusion of a fibre `Tautological 𝕜 k W` into the total space is a topological inducing map. -/
theorem isInducing_totalSpaceMk (W : infiniteGrassmannian 𝕜 k) :
    IsInducing
      (TotalSpace.mk W : Tautological 𝕜 k W → TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) := by
  obtain ⟨u, hu⟩ := exists_mem_chartDomain W; let e := chartEquiv u hu
  have hmk : Continuous (TotalSpace.mk W : Tautological 𝕜 k W → _) :=
    continuous_totalSpace_iff.2 ⟨continuous_const, fun m ↦
      IsModuleTopology.continuous_of_linearMap ((lapply m).comp (Tautological.subtype W))⟩
  have hcomp : (fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦
      fun i : Fin k ↦ p.snd.val (u i)) ∘ TotalSpace.mk W = e := by
    ext v i; rw [comp_apply, chartEquiv_apply, chartLinearMap_apply]
  exact .of_comp hmk (continuous_pi fun i ↦ continuous_evalCoord (u i))
    (hcomp ▸ e.toHomeomorph.isInducing)
open Classical in
private def chartComp (u : Fin k ↪ ℕ) {F : Type*} [AddCommMonoid F] [Module 𝕜 F]
    (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) (W : infiniteGrassmannian 𝕜 k) : (Fin k → 𝕜) →ₗ[𝕜] F :=
  if hW : W ∈ chartDomain u then
    ψ.comp ((Tautological.subtype W).comp (chartEquiv u hW).symm.toLinearMap) else 0
private theorem chartComp_apply_of_mem (u : Fin k ↪ ℕ) {F : Type*} [AddCommMonoid F] [Module 𝕜 F]
    (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) {W : infiniteGrassmannian 𝕜 k} (hW : W ∈ chartDomain u)
    (v : Fin k → 𝕜) : chartComp u ψ W v = ψ (((chartEquiv u hW).symm v).val) := by
  simp [chartComp, hW]
open Classical in
private def chartSymm (u : Fin k ↪ ℕ) (W : infiniteGrassmannian 𝕜 k) (v : Fin k → 𝕜) :
    Tautological 𝕜 k W := if hW : W ∈ chartDomain u then (chartEquiv u hW).symm v else 0
end ChartEquiv

/-- Every coordinate-projection chart domain `chartDomain u` is open in `infiniteGrassmannian`. -/
theorem isOpen_chartDomain {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
    [T1Space 𝕜] {k : ℕ} (u : Fin k ↪ ℕ) : IsOpen (chartDomain (𝕜 := 𝕜) u) := by
  refine isOpen_iff.2 fun n ↦ isQuotientMap_frameSpan.isOpen_preimage.1 ?_
  convert (isOpen_ne (x := (0 : 𝕜))).preimage
    (continuous_frameCoordMatrix (𝕜 := 𝕜) u n).matrix_det using 1
  ext f; exact (toInfinite_frameSpan_mem_chartDomain_iff u f).trans
    ((Matrix.isUnit_iff_isUnit_det _).trans isUnit_iff_ne_zero)

section FiberBundle
variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalDivisionRing 𝕜] [T1Space 𝕜]
  {k : ℕ}
section ChartCompCont
variable (u : Fin k ↪ ℕ) {F : Type*} [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousSMul 𝕜 F] (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F)
private theorem continuousOn_chartComp_stage (r : Fin k) (n : ℕ) : ContinuousOn
    (fun V : finiteGrassmannian 𝕜 k n ↦ chartComp u ψ (toInfinite V) (Pi.single r 1))
    (toInfinite ⁻¹' chartDomain u) := by
  rw [isQuotientMap_frameSpan.continuousOn_isOpen_iff
    ((isOpen_chartDomain u).preimage continuous_toInfinite),
    (Set.ext (toInfinite_frameSpan_mem_chartDomain_iff u) :
      (frameSpan ⁻¹' (toInfinite ⁻¹' chartDomain (𝕜 := 𝕜) u) : Set (finiteFullRankFrame 𝕜 k n)) =
        {f | IsUnit (frameCoordMatrix u f)})]
  have hinv : ContinuousOn (fun f : finiteFullRankFrame 𝕜 k n ↦ (frameCoordMatrix u f)⁻¹)
      {f | IsUnit (frameCoordMatrix u f)} := fun f hf ↦
    ((continuous_frameCoordMatrix u n).continuousAt.matrix_inv
      ((Matrix.isUnit_iff_isUnit_det _).1 hf).ne_zero).continuousWithinAt
  have hψn : Continuous (ψ.comp (coordinateInclusion n)) := LinearMap.continuous_on_pi _
  refine (continuousOn_finsetSum Finset.univ fun i _ ↦
    (((continuous_id.matrix_elem i r).comp_continuousOn hinv).smul
      (hψn.comp ((continuous_apply i).comp continuous_subtypeVal)).continuousOn)).congr
    fun f hf ↦ ?_
  have hf' := (toInfinite_frameSpan_mem_chartDomain_iff u f).2 hf
  rw [comp_apply, chartComp_apply_of_mem u ψ hf', chartEquiv_symm_stageFrameBasis u f hf',
    Module.Basis.equivFun_symm_apply, ← Tautological.subtype_apply, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp [comp_apply, val_stageFrameBasis_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
private theorem continuousOn_chartComp_eval (r : Fin k) :
    ContinuousOn (fun W ↦ chartComp u ψ W (Pi.single r 1)) (chartDomain u) :=
  (continuousOn_iff_of_isOpen (isOpen_chartDomain u)).2 (continuousOn_chartComp_stage u ψ r)
private theorem continuousOn_chartComp_prod :
    ContinuousOn (fun q : infiniteGrassmannian 𝕜 k × (Fin k → 𝕜) ↦ chartComp u ψ q.1 q.2)
      (chartDomain u ×ˢ univ) := by
  refine (continuousOn_finsetSum Finset.univ fun r _ ↦
    ((continuous_apply r).comp continuous_snd).continuousOn.smul
      ((continuousOn_chartComp_eval u ψ r).comp continuousOn_fst
        fun _ (hq : _ ∈ chartDomain u ×ˢ univ) ↦ hq.1)).congr fun q _ ↦ ?_
  have hv : q.2 = ∑ r : Fin k, q.2 r • Pi.single r 1 := by ext j; simp [Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  exact Finset.sum_congr rfl fun r _ ↦ map_smul _ _ _
end ChartCompCont

section Triv
variable (u : Fin k ↪ ℕ)
/-- The local trivialization of `Tautological 𝕜 k` over `chartDomain u` (`u : Fin k ↪ ℕ`). -/
def trivialization : Trivialization (Fin k → 𝕜) (π (Fin k → 𝕜) (Tautological 𝕜 k)) where
  toFun p := (p.proj, chartLinearMap u p.proj p.snd)
  invFun q := ⟨q.1, chartSymm u q.1 q.2⟩
  source := π (Fin k → 𝕜) (Tautological 𝕜 k) ⁻¹' chartDomain u
  target := chartDomain u ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p hp := by
    ext1; · rfl
    simp only [mem_preimage] at hp; dsimp only
    rw [chartSymm, dite_eq_left hp, chartEquiv_symm_chartLinearMap]
  right_inv' q hq := by
    ext1; · rfl
    dsimp only; rw [chartSymm, dite_eq_left hq.1, chartLinearMap_chartEquiv_symm]
  open_source := (isOpen_chartDomain u).preimage
    (continuous_fst.comp isEmbedding_totalSpaceEmbed.continuous)
  open_target := (isOpen_chartDomain u).prod isOpen_univ
  continuousOn_toFun := ((continuous_fst.comp isEmbedding_totalSpaceEmbed.continuous).prodMk
    (continuous_pi fun i ↦ continuous_evalCoord (u i))).continuousOn
  continuousOn_invFun := by
    rw [isEmbedding_totalSpaceEmbed.isInducing.continuousOn_iff]
    refine continuousOn_fst.prodMk (continuousOn_pi.2 fun m ↦
      (continuousOn_chartComp_prod u (lapply m)).congr fun q hq ↦ ?_)
    dsimp only [comp_def, totalSpaceEmbed]
    rw [chartSymm, dite_eq_left hq.1, chartComp_apply_of_mem u (lapply m) hq.1, lapply_apply]
  baseSet := chartDomain u; open_baseSet := isOpen_chartDomain u
  source_eq := rfl; target_eq := rfl; proj_toFun _ _ := rfl
@[simp] theorem trivialization_baseSet :
    (trivialization (𝕜 := 𝕜) u).baseSet = chartDomain u := (rfl)
@[simp] theorem trivialization_apply (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :
    trivialization u p = (p.proj, chartLinearMap u p.proj p.snd) := (rfl)
theorem trivialization_symm_apply {W : infiniteGrassmannian 𝕜 k} (hW : W ∈ chartDomain u)
    (v : Fin k → 𝕜) : (trivialization u).symm W v = (chartEquiv u hW).symm v :=
  hW.1 <| by simpa only [trivialization_apply, chartLinearMap_chartEquiv_symm] using
    (congrArg Prod.snd ((trivialization u).apply_mk_symm hW v))
instance isLinear_trivialization : (trivialization (𝕜 := 𝕜) u).IsLinear 𝕜 where
  linear W _ := (chartLinearMap u W).isLinear
end Triv

variable (𝕜 k) in
/-- The rank-`k` fiber-bundle structure on `Tautological 𝕜 k` given by the coordinate-projection
trivializations `trivialization u` over `chartDomain u` (`u : Fin k ↪ ℕ`). -/
instance : FiberBundle (Fin k → 𝕜) (Tautological 𝕜 k) where
  totalSpaceMk_isInducing' := isInducing_totalSpaceMk
  trivializationAtlas' := range (trivialization (𝕜 := 𝕜) (k := k))
  trivializationAt' W := trivialization (chartIndex W)
  mem_baseSet_trivializationAt' W :=
    (trivialization_baseSet (𝕜 := 𝕜) _).symm ▸ mem_chartDomain_chartIndex W
  trivialization_mem_atlas' W := ⟨chartIndex W, rfl⟩
/-- Every `trivialization u` belongs to the trivialization atlas of `Tautological 𝕜 k`. -/
instance (u : Fin k ↪ ℕ) : MemTrivializationAtlas (trivialization (𝕜 := 𝕜) u) := ⟨⟨u, rfl⟩⟩
/-- The trivialization atlas of `Tautological 𝕜 k` is `range trivialization`. -/
theorem trivializationAtlas_tautological :
    FiberBundle.trivializationAtlas (Fin k → 𝕜) (Tautological 𝕜 k) =
      range (trivialization (𝕜 := 𝕜) (k := k)) := (rfl)
theorem mem_trivializationAtlas_tautological_iff
    {e : Trivialization (Fin k → 𝕜) (π (Fin k → 𝕜) (Tautological 𝕜 k))} :
    e ∈ FiberBundle.trivializationAtlas (Fin k → 𝕜) (Tautological 𝕜 k) ↔
      ∃ u : Fin k ↪ ℕ, trivialization u = e := Iff.rfl
/-- The preferred local trivialization of `Tautological 𝕜 k` at `W` is
`trivialization (chartIndex W)`. -/
@[simp] theorem trivializationAt_tautological (W : infiniteGrassmannian 𝕜 k) :
    trivializationAt (Fin k → 𝕜) (Tautological 𝕜 k) W = trivialization (chartIndex W) := (rfl)

/-- Every linear map `ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F` into a topological `𝕜`-module is continuous on the
total space of `Tautological 𝕜 k`. -/
theorem continuous_linearMap_totalSpace {F : Type*} [AddCommMonoid F] [Module 𝕜 F]
    [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F] (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) :
    Continuous fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦ ψ p.snd.val := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  let u := chartIndex p.proj; let e := trivialization (𝕜 := 𝕜) u
  have hp : p.proj ∈ chartDomain u := mem_chartDomain_chartIndex p.proj
  have hp_src : p ∈ e.source := by rwa [e.mem_source, trivialization_baseSet]
  refine (((continuousOn_chartComp_prod u ψ).continuousAt
    (((isOpen_chartDomain u).prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).comp
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hp_src))).congr_of_eventuallyEq ?_
  filter_upwards [e.open_source.mem_nhds hp_src] with q hq
  dsimp only [comp_def]
  rw [trivialization_apply, chartComp_apply_of_mem u ψ
    (by rwa [e.mem_source, trivialization_baseSet] at hq), chartEquiv_symm_chartLinearMap]

section MapHomeo
variable (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
/-- `Tautological 𝕜 k` is bundle-homeomorphic to its pullback along `mapContinuousMap φ hφ`. -/
def mapTautologicalHomeomorph : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ≃ₜ
    TotalSpace (Fin k → 𝕜) ((mapContinuousMap (k := k) φ hφ : _ → _) *ᵖ (Tautological 𝕜 k)) where
  toFun p := TotalSpace.mk' (Fin k → 𝕜) p.proj (mapTautologicalEquiv φ hφ p.proj p.snd)
  invFun p := TotalSpace.mk' (Fin k → 𝕜) p.proj ((mapTautologicalEquiv φ hφ p.proj).symm p.snd)
  left_inv := fun ⟨W, v⟩ ↦ congrArg (TotalSpace.mk W)
    ((mapTautologicalEquiv φ hφ W).symm_apply_apply v)
  right_inv := fun ⟨W, w⟩ ↦ congrArg (TotalSpace.mk W)
    ((mapTautologicalEquiv φ hφ W).apply_symm_apply w)
  continuous_toFun := Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj _ _,
    continuous_totalSpace_iff.2 ⟨(continuous_map φ hφ).comp (FiberBundle.continuous_proj _ _),
      fun m ↦ (continuous_linearMap_totalSpace (k := k) ((lapply m).comp φ)).congr
        fun _ ↦ by simp⟩⟩
  continuous_invFun := continuous_totalSpace_iff.2
    ⟨Pullback.continuous_proj _ _ (mapContinuousMap (k := k) φ hφ : _ → _), fun m ↦
      ((continuous_linearMap_totalSpace (k := k) ((lapply m).comp φ.leftInverse)).comp
        (Pullback.continuous_lift _ _ (mapContinuousMap (k := k) φ hφ : _ → _))).congr
        fun ⟨W, w⟩ ↦ by
          have hw : φ ((mapTautologicalEquiv φ hφ W).symm w).val = w.val :=
            (val_mapTautologicalEquiv φ hφ W _).symm.trans
              (congrArg Tautological.val ((mapTautologicalEquiv φ hφ W).apply_symm_apply w))
          simp [← hw, LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.2 hφ)]⟩
@[simp] theorem mapTautologicalHomeomorph_apply (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :
    mapTautologicalHomeomorph φ hφ p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (mapTautologicalEquiv φ hφ p.proj p.snd) := (rfl)
@[simp] theorem mapTautologicalHomeomorph_symm_apply (p : TotalSpace (Fin k → 𝕜)
      ((mapContinuousMap (k := k) φ hφ : _ → _) *ᵖ (Tautological 𝕜 k))) :
    (mapTautologicalHomeomorph φ hφ).symm p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj ((mapTautologicalEquiv φ hφ p.proj).symm p.snd) := (rfl)
end MapHomeo
end FiberBundle

section VectorBundle
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k : ℕ}
private theorem continuousOn_coordChangeL_trivialization (u u' : Fin k ↪ ℕ) :
    ContinuousOn (fun W ↦ ((trivialization (𝕜 := 𝕜) u).coordChangeL 𝕜 (trivialization u') W :
        (Fin k → 𝕜) →L[𝕜] (Fin k → 𝕜))) (chartDomain u ∩ chartDomain u') := by
  refine ((continuousOn_finsetSum Finset.univ fun r _ ↦
    (StrongDual.smulRightL 𝕜 (Fin k → 𝕜) (Fin k → 𝕜)
      (ContinuousLinearMap.proj r)).continuous.comp_continuousOn
        (continuousOn_chartComp_eval u (coordProj u') r)).mono inter_subset_left).congr
    fun W hW ↦ ContinuousLinearMap.ext fun v ↦ ?_
  have hv : v = ∑ r : Fin k, v r • Pi.single r 1 := by ext j; simp [Pi.single_apply]
  rw [ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply (trivialization u) (trivialization u') hW v,
    trivialization_apply, trivialization_symm_apply u hW.1 v, FunLike.coe_sum, Finset.sum_apply]
  refine (chartComp_apply_of_mem u (coordProj u') hW.1 v).symm.trans ?_
  conv_lhs => rw [hv, map_sum]
  exact Finset.sum_congr rfl fun r _ ↦ map_smul _ (v r) (Pi.single r 1)
variable (𝕜 k) in
/-- The rank-`k` `𝕜`-vector-bundle structure on `Tautological 𝕜 k` over a nontrivially normed
field `𝕜`. -/
instance : VectorBundle 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) where
  trivialization_linear' := by rintro _ ⟨u, rfl⟩; exact isLinear_trivialization u
  continuousOn_coordChange' := by
    rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩; exact continuousOn_coordChangeL_trivialization u u'
end VectorBundle
end infiniteGrassmannian

namespace finiteGrassmannian
variable {𝕜 : Type*} [RCLike 𝕜] {k n : ℕ}
/-- Over `RCLike 𝕜`, coordinate inclusion identifies `Tautological 𝕜 k n V` with
`infiniteGrassmannian.Tautological 𝕜 k V.toInfinite`. -/
def toInfiniteTautologicalEquiv (V : finiteGrassmannian 𝕜 k n) :
    Tautological 𝕜 k n V ≃L[𝕜] infiniteGrassmannian.Tautological 𝕜 k V.toInfinite :=
  ((tautologicalEquiv 𝕜 k n V).trans <|
    (Submodule.equivMapOfInjective (coordinateInclusion n) (coordinateInclusion_injective n)
      V.val).trans <| (LinearEquiv.ofEq _ _ (coe_toInfinite V).symm).trans
        (infiniteGrassmannian.tautologicalEquiv 𝕜 k V.toInfinite).symm).toContinuousLinearEquiv
@[simp] theorem val_toInfiniteTautologicalEquiv (V : finiteGrassmannian 𝕜 k n)
    (v : Tautological 𝕜 k n V) :
    (V.toInfiniteTautologicalEquiv v).val = coordinateInclusion (R := 𝕜) n (WithLp.ofLp v.val) := by
  simp [toInfiniteTautologicalEquiv]
@[simp] theorem coe_toInfiniteTautologicalEquiv_symm_apply (V : finiteGrassmannian 𝕜 k n)
    (w : infiniteGrassmannian.Tautological 𝕜 k V.toInfinite) :
    (V.toInfiniteTautologicalEquiv.symm w : EuclideanSpace 𝕜 (Fin n)) =
      WithLp.toLp 2 (fun i : Fin n ↦ w.val i) := by
  have h := val_toInfiniteTautologicalEquiv V (V.toInfiniteTautologicalEquiv.symm w)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact WithLp.ofLp_injective 2 (funext fun i ↦ by simp [h, coordinateInclusion_apply_val])
variable (𝕜 k n) in
/-- Over `RCLike 𝕜`, `finiteGrassmannian.Tautological 𝕜 k n` is bundle-homeomorphic to the pullback
of `infiniteGrassmannian.Tautological 𝕜 k` along `toInfiniteContinuousMap`. -/
def toInfiniteTautologicalHomeomorph : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k n) ≃ₜ
    TotalSpace (Fin k → 𝕜) ((toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (infiniteGrassmannian.Tautological 𝕜 k)) :=
  bundleHomeomorph toInfiniteTautologicalEquiv <| Pullback.continuous_iff.2
    ⟨FiberBundle.continuous_proj _ _, infiniteGrassmannian.continuous_totalSpace_iff.2
      ⟨continuous_toInfinite.comp (FiberBundle.continuous_proj _ _), fun m ↦
        ((LinearMap.continuous_on_pi ((lapply (R := 𝕜) (M := 𝕜) m).comp
          (coordinateInclusion n))).comp ((PiLp.continuous_ofLp 2 _).comp
            (continuous_snd.comp (isEmbedding_totalSpace_range _ _).continuous))).congr fun p ↦ by
              simp only [comp_apply, LinearMap.comp_apply, lapply_apply]
              exact DFunLike.congr_fun (val_toInfiniteTautologicalEquiv p.proj p.snd).symm m⟩⟩
@[simp] theorem toInfiniteTautologicalHomeomorph_apply
    (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k n)) :
    toInfiniteTautologicalHomeomorph 𝕜 k n p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (p.proj.toInfiniteTautologicalEquiv p.snd) :=
  bundleHomeomorph_apply _ _ p
@[simp] theorem toInfiniteTautologicalHomeomorph_symm_apply (p : TotalSpace (Fin k → 𝕜)
      ((toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (infiniteGrassmannian.Tautological 𝕜 k))) :
    (toInfiniteTautologicalHomeomorph 𝕜 k n).symm p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (p.proj.toInfiniteTautologicalEquiv.symm p.snd) :=
  bundleHomeomorph_symm_apply _ _ p
end finiteGrassmannian
end TauCeti
