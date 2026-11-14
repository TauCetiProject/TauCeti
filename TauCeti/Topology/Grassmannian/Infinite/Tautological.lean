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
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.Paracompact
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.Topology.Category.TopCat.Paracompact
import TauCeti.Topology.FiberBundle.Pullback
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The universal tautological bundle over the infinite Grassmannian

For a field `𝕜` and a rank `k : ℕ`, each point `W` of `TauCeti.infiniteGrassmannian 𝕜 k` is a
`k`-dimensional subspace of `ℕ →₀ 𝕜`. Its vectors, packaged in the structure
`TauCeti.infiniteGrassmannian.Tautological 𝕜 k W` and equipped with the canonical `𝕜`-module
topology, form the **universal tautological vector bundle** `γ^k(𝕜^∞)` over the infinite
Grassmannian.

We first record the topological properties of `infiniteGrassmannian 𝕜 k` inherited from its
colimit presentation:
* `TauCeti.infiniteGrassmannian.isQuotientMap_sigmaToInfinite` presents the infinite Grassmannian
  as a quotient of the disjoint union `Σ n, finiteGrassmannian 𝕜 k n` of the finite stages, and
  `TauCeti.infiniteGrassmannian.continuousOn_iff_of_isOpen` tests `ContinuousOn` on an open subset
  stage by stage.
* Over `ℝ` or `ℂ` (more generally `RCLike 𝕜`), the stage inclusions are closed embeddings between
  compact Hausdorff spaces, so `infiniteGrassmannian 𝕜 k` is `T4` (hence Hausdorff and normal),
  Lindelöf, and paracompact.
* Any injective linear map `φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)` induces a continuous self-map
  `TauCeti.infiniteGrassmannian.map φ hφ` of `infiniteGrassmannian 𝕜 k`: on each finite stage the
  image of `𝕜^n` is finitely generated, hence lands in a finite coordinate stage where `φ` is a
  linear map between finite-dimensional coordinate spaces.

Over any nontrivially normed field `𝕜` (without completeness or inner-product assumptions), the
total space of `Tautological 𝕜 k` carries the subspace topology induced by its canonical embedding
`TauCeti.infiniteGrassmannian.totalSpaceEmbed` into `infiniteGrassmannian 𝕜 k × (ℕ → 𝕜)`, and we
equip it with `FiberBundle` and `VectorBundle` structures using the Plücker coordinate charts
indexed by injections `u : Fin k ↪ ℕ`:
* `TauCeti.infiniteGrassmannian.chartDomain u` is the set of `k`-planes on which the coordinate
  projection `v ↦ fun i ↦ v.val (u i)` is bijective. On frames at stage `n`, membership is
  invertibility of the `k × k` minor on columns `u`, so `chartDomain u` is open and these domains
  cover `infiniteGrassmannian 𝕜 k`.
* Transition maps and arbitrary ambient linear maps `ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F` into topological
  `𝕜`-modules vary continuously across charts: on frames at stage `n`, the inverse chart is
  multiplication by the inverse of the `k × k` frame minor, whose entries are rational functions of
  the frame coordinates, composed with `ψ` restricted to `𝕜^n`.
* `TauCeti.infiniteGrassmannian.continuous_totalSpace_iff` characterizes continuity into the total
  space of `Tautological 𝕜 k` by continuity of the base projection together with continuity of
  every ambient coordinate `m : ℕ`.

Finally, we identify the tautological bundle under pullbacks:
* `TauCeti.infiniteGrassmannian.mapTautologicalHomeomorph` identifies `Tautological 𝕜 k` with its
  pullback along `mapContinuousMap φ hφ` for any ambient linear injection `φ` over a complete normed
  field.
* `TauCeti.finiteGrassmannian.toInfiniteTautologicalHomeomorph` identifies the finite
  Grassmannian's tautological bundle `finiteGrassmannian.Tautological 𝕜 k n` with the pullback of
  `infiniteGrassmannian.Tautological 𝕜 k` along `toInfiniteContinuousMap` over `RCLike 𝕜`.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5, for the infinite Grassmannian `G_k(ℝ^∞)`
  and its universal `k`-plane bundle `γ^k`.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, for coordinate-projection charts on the
  universal bundle over the Grassmannian of `k`-planes in `𝕜^∞`.
-/

public noncomputable section

open Bundle Set Function Topology
open _root_.Finsupp
open scoped Matrix

namespace TauCeti

namespace finiteGrassmannian

variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] {k n : ℕ}

/-- The stage inclusion `finiteGrassmannian.toInfinite` bundled as a `ContinuousMap`. -/
@[expose] def toInfiniteContinuousMap : C(finiteGrassmannian 𝕜 k n, infiniteGrassmannian 𝕜 k) :=
  ⟨toInfinite, continuous_toInfinite⟩

@[simp]
theorem toInfiniteContinuousMap_apply (V : finiteGrassmannian 𝕜 k n) :
    toInfiniteContinuousMap V = toInfinite V := (rfl)

end finiteGrassmannian

namespace infiniteGrassmannian

open finiteGrassmannian

section QuotientAndTopology

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ}

/-- The canonical map from the disjoint union of all finite Grassmannians to the infinite
Grassmannian. -/
def sigmaToInfinite (p : Σ n, finiteGrassmannian 𝕜 k n) : infiniteGrassmannian 𝕜 k :=
  toInfinite p.2

@[simp]
theorem sigmaToInfinite_mk (n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    sigmaToInfinite ⟨n, V⟩ = toInfinite V := (rfl)

/-- Every point of the infinite Grassmannian lies in the image of `sigmaToInfinite`. -/
theorem sigmaToInfinite_surjective :
    Surjective (sigmaToInfinite : (Σ n, finiteGrassmannian 𝕜 k n) → infiniteGrassmannian 𝕜 k) :=
  fun W ↦ by
    obtain ⟨n, V, rfl⟩ := exists_toInfinite_eq W
    exact ⟨⟨n, V⟩, rfl⟩

/-- The infinite Grassmannian carries the quotient topology of the disjoint union of its finite
coordinate stages. -/
theorem isQuotientMap_sigmaToInfinite [TopologicalSpace 𝕜] :
    IsQuotientMap
      (sigmaToInfinite : (Σ n, finiteGrassmannian 𝕜 k n) → infiniteGrassmannian 𝕜 k) :=
  ⟨.of_isOpen_preimage_iff_isOpen fun U ↦ by
      rw [isOpen_iff, isOpen_sigma_iff]
      rfl,
    sigmaToInfinite_surjective⟩

/-- On an open subset of the infinite Grassmannian, a function is continuous if and only if its
restriction to every finite coordinate stage is continuous on the preimage. -/
theorem continuousOn_iff_of_isOpen [TopologicalSpace 𝕜] {X : Type*} [TopologicalSpace X]
    {U : Set (infiniteGrassmannian 𝕜 k)} (hU : IsOpen U) {f : infiniteGrassmannian 𝕜 k → X} :
    ContinuousOn f U ↔
      ∀ n, ContinuousOn (f ∘ (toInfinite : finiteGrassmannian 𝕜 k n → _)) (toInfinite ⁻¹' U) := by
  refine ⟨fun h n ↦ (continuousOn_open_iff (hU.preimage continuous_toInfinite)).2 fun t ht ↦ ?_,
    fun h ↦ (continuousOn_open_iff hU).2 fun t ht ↦ isOpen_iff.2 fun n ↦ ?_⟩
  · rw [preimage_comp, ← preimage_inter]
    exact (isOpen_iff.1 ((continuousOn_open_iff hU).1 h t ht)) n
  · rw [preimage_inter, ← preimage_comp]
    exact (continuousOn_open_iff (hU.preimage continuous_toInfinite)).1 (h n) t ht

end QuotientAndTopology

section RCLikeTopology

variable {𝕜 : Type*} [RCLike 𝕜] {k : ℕ}

/-- Over `ℝ` or `ℂ` (more generally `RCLike 𝕜`), the infinite Grassmannian is `T4` (normal and
Hausdorff), as a sequential colimit of compact Hausdorff Grassmannians along closed embeddings. -/
instance : T4Space (infiniteGrassmannian 𝕜 k) :=
  let _ (n : ℕ) : T4Space ((diagram 𝕜 k).obj n) :=
    inferInstanceAs (T4Space (finiteGrassmannian 𝕜 k n))
  TopCat.t4Space_of_isColimit (F := diagram 𝕜 k)
    (fun n ↦ isClosedEmbedding_ambientInclusion (Nat.le_succ n)) (isColimit 𝕜 k)

/-- Over `RCLike 𝕜`, the infinite Grassmannian is Lindelöf, as a countable colimit of compact
stages. -/
instance : LindelofSpace (infiniteGrassmannian 𝕜 k) :=
  let _ (n : ℕ) : LindelofSpace ((diagram 𝕜 k).obj n) :=
    inferInstanceAs (LindelofSpace (finiteGrassmannian 𝕜 k n))
  TopCat.lindelofSpace_of_isColimit (F := diagram 𝕜 k) (isColimit 𝕜 k)

/-- Over `RCLike 𝕜`, the infinite Grassmannian is paracompact for its direct-limit topology. -/
instance : ParacompactSpace (infiniteGrassmannian 𝕜 k) :=
  let _ (n : ℕ) : NormalSpace ((diagram 𝕜 k).obj n) :=
    inferInstanceAs (NormalSpace (finiteGrassmannian 𝕜 k n))
  let _ (n : ℕ) : T1Space ((diagram 𝕜 k).obj n) :=
    inferInstanceAs (T1Space (finiteGrassmannian 𝕜 k n))
  let _ (n : ℕ) : LindelofSpace ((diagram 𝕜 k).obj n) :=
    inferInstanceAs (LindelofSpace (finiteGrassmannian 𝕜 k n))
  TopCat.paracompactSpace_of_isColimit (F := diagram 𝕜 k)
    (fun n ↦ isClosedEmbedding_ambientInclusion (Nat.le_succ n)) (isColimit 𝕜 k)

end RCLikeTopology

section Map

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ}

/-- An injective linear endomorphism of `ℕ →₀ 𝕜` acts on `infiniteGrassmannian 𝕜 k` by sending each
`k`-dimensional subspace to its image. -/
def map (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (W : infiniteGrassmannian 𝕜 k) : infiniteGrassmannian 𝕜 k :=
  ⟨W.1.map φ, by rw [rank_map_eq hφ, W.2]⟩

@[simp]
theorem coe_map (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (W : infiniteGrassmannian 𝕜 k) : (map φ hφ W).1 = W.1.map φ := (rfl)

@[simp]
theorem map_id (W : infiniteGrassmannian 𝕜 k) :
    map LinearMap.id injective_id W = W :=
  Subtype.ext (Submodule.map_id W.1)

@[simp]
theorem map_comp (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hψ : Injective ψ) (W : infiniteGrassmannian 𝕜 k) :
    map (ψ.comp φ) (hψ.comp hφ) W = map ψ hψ (map φ hφ W) :=
  Subtype.ext (Submodule.map_comp φ ψ W.1)

/-- An injective ambient linear map induces an injective map on the infinite Grassmannian. -/
theorem map_injective (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) :
    Injective (map (k := k) φ hφ) := fun _ _ h ↦
  Subtype.ext (Submodule.map_injective_of_injective hφ (congrArg Subtype.val h))

/-- Restrict an ambient map whose image of `𝕜^n` is supported below `m` to a linear map
`(Fin n → 𝕜) →ₗ[𝕜] (Fin m → 𝕜)`. -/
private def stageRestriction (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (n m : ℕ) :
    (Fin n → 𝕜) →ₗ[𝕜] (Fin m → 𝕜) :=
  (LinearMap.pi fun j : Fin m ↦ Finsupp.lapply (R := 𝕜) (M := 𝕜) j.1).comp
    (φ.comp (coordinateInclusion n))

private theorem coordinateInclusion_comp_stageRestriction {φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)}
    {n m : ℕ} (hm : (⊤ : Submodule 𝕜 (Fin n → 𝕜)).map (φ.comp (coordinateInclusion n)) ≤
      Finsupp.supported 𝕜 𝕜 (Iio m)) :
    (coordinateInclusion m).comp (stageRestriction φ n m) = φ.comp (coordinateInclusion n) := by
  refine LinearMap.ext fun v ↦ Finsupp.ext fun r ↦ ?_
  have hmem : φ (coordinateInclusion n v) ∈ Finsupp.supported 𝕜 𝕜 (Iio m) :=
    hm ⟨v, trivial, rfl⟩
  by_cases hr : r < m
  · simp [stageRestriction, coordinateInclusion_apply_val _ ⟨r, hr⟩]
  · rw [LinearMap.comp_apply, coordinateInclusion_apply_of_le _ (Nat.le_of_not_gt hr)]
    have hnot : r ∉ (φ (coordinateInclusion n v)).support := fun h ↦ hr (hmem h)
    exact (Finsupp.notMem_support_iff.1 hnot).symm

/-- Any injective `𝕜`-linear endomorphism of `ℕ →₀ 𝕜` induces a continuous self-map of
`infiniteGrassmannian 𝕜 k`. No continuity hypothesis on `φ` is needed: on each finite coordinate
stage `𝕜^n`, the image of `φ` lands in some finite coordinate stage `𝕜^m`, where `φ` is a linear
map out of `Fin n → 𝕜`. -/
@[fun_prop]
theorem continuous_map [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) :
    Continuous (map (k := k) φ hφ) := by
  refine continuous_iff.2 fun n ↦ ?_
  have hfg : ((⊤ : Submodule 𝕜 (Fin n → 𝕜)).map (φ.comp (coordinateInclusion n))).FG :=
    (Module.Finite.iff_fg.1 inferInstance).map _
  obtain ⟨m, hm⟩ := hfg.exists_le_supported_Iio
  have hcomp := coordinateInclusion_comp_stageRestriction hm
  have hinj : Injective (stageRestriction φ n m) :=
    .of_comp (f := coordinateInclusion m) <| by
      rw [← LinearMap.coe_comp, hcomp]
      exact hφ.comp (coordinateInclusion_injective n)
  have hfac (V : finiteGrassmannian 𝕜 k n) :
      map φ hφ (toInfinite V) =
        toInfinite (finiteGrassmannian.map (stageRestriction φ n m) hinj V) := by
    apply Subtype.ext
    rw [coe_map, coe_toInfinite, coe_toInfinite, finiteGrassmannian.coe_map,
      ← Submodule.map_comp, ← Submodule.map_comp, hcomp]
  exact (continuous_toInfinite.comp
    (finiteGrassmannian.continuous_map _ hinj (stageRestriction φ n m).continuous_on_pi)).congr
      fun V ↦ (hfac V).symm

/-- `infiniteGrassmannian.map` bundled as a `ContinuousMap`. -/
@[expose] def mapContinuousMap [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) :
    C(infiniteGrassmannian 𝕜 k, infiniteGrassmannian 𝕜 k) :=
  ⟨map φ hφ, continuous_map φ hφ⟩

@[simp]
theorem mapContinuousMap_apply [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) (W : infiniteGrassmannian 𝕜 k) :
    mapContinuousMap φ hφ W = map φ hφ W := (rfl)

@[simp]
theorem mapContinuousMap_id [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜] :
    mapContinuousMap (k := k) (LinearMap.id : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) injective_id =
      ContinuousMap.id (infiniteGrassmannian 𝕜 k) :=
  ContinuousMap.ext map_id

@[simp]
theorem mapContinuousMap_comp [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hψ : Injective ψ) :
    mapContinuousMap (k := k) (ψ.comp φ) (hψ.comp hφ) =
      (mapContinuousMap ψ hψ).comp (mapContinuousMap φ hφ) :=
  ContinuousMap.ext (map_comp φ hφ ψ hψ)

end Map

section TautologicalFiber

variable (𝕜 : Type*) [Field 𝕜] (k : ℕ)

/-- The **universal tautological bundle** `γ^k(𝕜^∞)` over `infiniteGrassmannian 𝕜 k`: a vector in
the fibre over a `k`-dimensional subspace `W` of `ℕ →₀ 𝕜` is an ambient vector belonging to `W.1`.
Packaged as a structure so its `ModuleTopology` and bundle instances stay localized to
`Tautological`. -/
@[ext]
structure Tautological (W : infiniteGrassmannian 𝕜 k) where
  /-- The underlying ambient coordinate vector in `ℕ →₀ 𝕜`. -/
  val : ℕ →₀ 𝕜
  /-- Membership of the vector in the subspace `W`. -/
  property : val ∈ W.1

section Algebraic

variable {𝕜 k} (W : infiniteGrassmannian 𝕜 k)

theorem Tautological.val_injective : Injective (Tautological.val : Tautological 𝕜 k W → ℕ →₀ 𝕜) :=
  fun _ _ ↦ Tautological.ext

instance : Zero (Tautological 𝕜 k W) := ⟨⟨0, W.1.zero_mem⟩⟩

instance : Add (Tautological 𝕜 k W) :=
  ⟨fun v w ↦ ⟨v.val + w.val, W.1.add_mem v.property w.property⟩⟩

instance : Neg (Tautological 𝕜 k W) := ⟨fun v ↦ ⟨-v.val, W.1.neg_mem v.property⟩⟩

instance : Sub (Tautological 𝕜 k W) :=
  ⟨fun v w ↦ ⟨v.val - w.val, W.1.sub_mem v.property w.property⟩⟩

instance {M : Type*} [SMul M 𝕜] [SMul M (ℕ →₀ 𝕜)] [IsScalarTower M 𝕜 (ℕ →₀ 𝕜)] :
    SMul M (Tautological 𝕜 k W) :=
  ⟨fun c v ↦ ⟨c • v.val, by
    rw [← smul_one_smul 𝕜 c v.val]
    exact W.1.smul_mem (c • (1 : 𝕜)) v.property⟩⟩

@[simp]
theorem Tautological.val_zero : (0 : Tautological 𝕜 k W).val = 0 := (rfl)

@[simp]
theorem Tautological.val_add (v w : Tautological 𝕜 k W) :
    (v + w).val = v.val + w.val := (rfl)

@[simp]
theorem Tautological.val_neg (v : Tautological 𝕜 k W) : (-v).val = -v.val := (rfl)

@[simp]
theorem Tautological.val_sub (v w : Tautological 𝕜 k W) :
    (v - w).val = v.val - w.val := (rfl)

@[simp]
theorem Tautological.val_smul {M : Type*} [SMul M 𝕜] [SMul M (ℕ →₀ 𝕜)]
    [IsScalarTower M 𝕜 (ℕ →₀ 𝕜)] (c : M) (v : Tautological 𝕜 k W) :
    (c • v).val = c • v.val := (rfl)

instance : AddCommGroup (Tautological 𝕜 k W) :=
  (Tautological.val_injective W).addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module 𝕜 (Tautological 𝕜 k W) :=
  (Tautological.val_injective W).module 𝕜
    { toFun := Tautological.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    fun _ _ ↦ rfl

/-- The canonical linear inclusion of the tautological fibre over `W` into the ambient coordinate
space `ℕ →₀ 𝕜`. -/
def Tautological.subtype : Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜) where
  toFun := Tautological.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem Tautological.subtype_apply (v : Tautological 𝕜 k W) :
    Tautological.subtype W v = v.val := (rfl)

theorem Tautological.subtype_injective : Injective (Tautological.subtype W) :=
  Tautological.val_injective W

variable (𝕜 k) in
/-- The tautological fibre over `W` identified `𝕜`-linearly with the submodule `W.1`. -/
def tautologicalEquiv (W : infiniteGrassmannian 𝕜 k) : Tautological 𝕜 k W ≃ₗ[𝕜] W.1 where
  toFun v := ⟨v.val, v.property⟩
  invFun v := ⟨v.1, v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem tautologicalEquiv_coe (v : Tautological 𝕜 k W) :
    (tautologicalEquiv 𝕜 k W v : ℕ →₀ 𝕜) = v.val := (rfl)

@[simp]
theorem val_tautologicalEquiv_symm (v : W.1) :
    ((tautologicalEquiv 𝕜 k W).symm v).val = v.1 := (rfl)

instance : FiniteDimensional 𝕜 (Tautological 𝕜 k W) :=
  have : FiniteDimensional 𝕜 W.1 := .of_rank_eq_nat W.2
  Module.Finite.equiv (tautologicalEquiv 𝕜 k W).symm

@[simp]
theorem finrank_tautological : Module.finrank 𝕜 (Tautological 𝕜 k W) = k :=
  (tautologicalEquiv 𝕜 k W).finrank_eq.trans (Module.finrank_eq_of_rank_eq W.2)

end Algebraic

section FiberTopology

variable {𝕜 k} [TopologicalSpace 𝕜] (W : infiniteGrassmannian 𝕜 k)

/-- Each fibre of `Tautological 𝕜 k` carries its canonical `𝕜`-module topology. -/
instance : TopologicalSpace (Tautological 𝕜 k W) :=
  moduleTopology 𝕜 (Tautological 𝕜 k W)

instance : IsModuleTopology 𝕜 (Tautological 𝕜 k W) := ⟨rfl⟩

instance : IsTopologicalAddGroup (Tautological 𝕜 k W) :=
  IsModuleTopology.isTopologicalAddGroup 𝕜 (Tautological 𝕜 k W)

instance : ContinuousSMul 𝕜 (Tautological 𝕜 k W) :=
  ModuleTopology.continuousSMul 𝕜 (Tautological 𝕜 k W)

instance [IsTopologicalSemiring 𝕜] [T2Space 𝕜] : T2Space (Tautological 𝕜 k W) :=
  ModuleTopology.t2Space (Module.finBasis 𝕜 (Tautological 𝕜 k W))

end FiberTopology

end TautologicalFiber

section VectorBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k : ℕ}

/-- Projection of `ℕ →₀ 𝕜` onto the `k` coordinates selected by an injection `u : Fin k ↪ ℕ`. -/
def coordProj (u : Fin k ↪ ℕ) : (ℕ →₀ 𝕜) →ₗ[𝕜] (Fin k → 𝕜) :=
  LinearMap.pi fun i ↦ Finsupp.lapply (u i)

@[simp]
theorem coordProj_apply (u : Fin k ↪ ℕ) (v : ℕ →₀ 𝕜) (i : Fin k) :
    coordProj u v i = v (u i) := (rfl)

/-- Restriction of the `u`-coordinate projection to the tautological fibre over `W`. -/
def chartLinearMap (u : Fin k ↪ ℕ) (W : infiniteGrassmannian 𝕜 k) :
    Tautological 𝕜 k W →ₗ[𝕜] (Fin k → 𝕜) :=
  (coordProj u).comp (Tautological.subtype W)

@[simp]
theorem chartLinearMap_apply (u : Fin k ↪ ℕ) (W : infiniteGrassmannian 𝕜 k)
    (v : Tautological 𝕜 k W) (i : Fin k) :
    chartLinearMap u W v i = v.val (u i) := (rfl)

/-- The coordinate chart domain indexed by `u : Fin k ↪ ℕ`: the `k`-planes on which projection onto
the `u`-coordinates is bijective. -/
def chartDomain (u : Fin k ↪ ℕ) : Set (infiniteGrassmannian 𝕜 k) :=
  {W | Bijective (chartLinearMap u W)}

theorem mem_chartDomain_iff_injective {u : Fin k ↪ ℕ} {W : infiniteGrassmannian 𝕜 k} :
    W ∈ chartDomain u ↔ Injective (chartLinearMap u W) := by
  refine ⟨Bijective.injective, fun h ↦ ⟨h, ?_⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((finrank_tautological W).trans (Module.finrank_fin_fun 𝕜).symm)).1 h

theorem mem_chartDomain_iff_surjective {u : Fin k ↪ ℕ} {W : infiniteGrassmannian 𝕜 k} :
    W ∈ chartDomain u ↔ Surjective (chartLinearMap u W) := by
  rw [mem_chartDomain_iff_injective]
  exact LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((finrank_tautological W).trans (Module.finrank_fin_fun 𝕜).symm)

/-- The continuous linear equivalence `Tautological 𝕜 k W ≃L[𝕜] (Fin k → 𝕜)` over a point of
`chartDomain u`. -/
def chartEquiv (u : Fin k ↪ ℕ) {W : infiniteGrassmannian 𝕜 k}
    (hW : W ∈ chartDomain u) : Tautological 𝕜 k W ≃L[𝕜] (Fin k → 𝕜) :=
  (LinearEquiv.ofBijective (chartLinearMap u W) hW).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem chartEquiv_apply (u : Fin k ↪ ℕ) {W : infiniteGrassmannian 𝕜 k}
    (hW : W ∈ chartDomain u) (v : Tautological 𝕜 k W) :
    chartEquiv u hW v = chartLinearMap u W v := by
  rw [chartEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]
  rfl

@[simp]
theorem chartLinearMap_chartEquiv_symm (u : Fin k ↪ ℕ) {W : infiniteGrassmannian 𝕜 k}
    (hW : W ∈ chartDomain u) (v : Fin k → 𝕜) :
    chartLinearMap u W ((chartEquiv u hW).symm v) = v := by
  rw [← chartEquiv_apply u hW, ContinuousLinearEquiv.apply_symm_apply]

@[simp]
theorem chartEquiv_symm_chartLinearMap (u : Fin k ↪ ℕ) {W : infiniteGrassmannian 𝕜 k}
    (hW : W ∈ chartDomain u) (v : Tautological 𝕜 k W) :
    (chartEquiv u hW).symm (chartLinearMap u W v) = v := by
  rw [← chartEquiv_apply u hW, ContinuousLinearEquiv.symm_apply_apply]

/-- The `k × k` matrix whose `(j, i)` entry is the `(u j)`-th coordinate of the `i`-th vector of a
finite frame `f`. Multiplication by this matrix expresses `chartLinearMap u` in the frame basis. -/
private def frameCoordMatrix (u : Fin k ↪ ℕ) {n : ℕ}
    (f : finiteFullRankFrame 𝕜 k n) : Matrix (Fin k) (Fin k) 𝕜 :=
  Matrix.of fun j i ↦ coordinateInclusion n (f.1 i) (u j)

private theorem continuous_frameCoordMatrix (u : Fin k ↪ ℕ) (n : ℕ) :
    Continuous (frameCoordMatrix (𝕜 := 𝕜) u (n := n)) := by
  refine continuous_matrix fun j i ↦ ?_
  have hlin : Continuous ((Finsupp.lapply (R := 𝕜) (M := 𝕜) (u j)).comp (coordinateInclusion n)) :=
    LinearMap.continuous_on_pi _
  exact hlin.comp ((continuous_apply i).comp continuous_subtype_val)

private theorem continuousOn_inv_frameCoordMatrix (u : Fin k ↪ ℕ) (n : ℕ) :
    ContinuousOn (fun f : finiteFullRankFrame 𝕜 k n ↦ (frameCoordMatrix u f)⁻¹)
      {f | IsUnit (frameCoordMatrix u f)} := by
  have hdet : ContinuousOn (fun f : finiteFullRankFrame 𝕜 k n ↦ ((frameCoordMatrix u f).det)⁻¹)
      {f | IsUnit (frameCoordMatrix u f)} :=
    continuousOn_inv₀.comp (continuous_frameCoordMatrix u n).matrix_det.continuousOn fun _ hf ↦
      ((Matrix.isUnit_iff_isUnit_det _).1 hf).ne_zero
  refine (hdet.smul (continuous_frameCoordMatrix u n).matrix_adjugate.continuousOn).congr
      fun f _ ↦ ?_
  change (frameCoordMatrix u f)⁻¹ = (frameCoordMatrix u f).det⁻¹ • (frameCoordMatrix u f).adjugate
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

/-- Basis of the tautological fibre over `toInfinite (frameSpan f)` given by the vectors of `f`. -/
private def stageFrameBasis {n : ℕ} (f : finiteFullRankFrame 𝕜 k n) :
    Module.Basis (Fin k) 𝕜 (Tautological 𝕜 k (toInfinite (frameSpan f))) :=
  (Module.Basis.span f.2).map <|
    (LinearEquiv.ofEq _ _ (coe_frameSpan f).symm).trans <|
      (Submodule.equivMapOfInjective (coordinateInclusion n)
        (coordinateInclusion_injective n) (frameSpan f).1).trans <|
          (LinearEquiv.ofEq _ _ (coe_toInfinite (frameSpan f)).symm).trans
            (tautologicalEquiv 𝕜 k (toInfinite (frameSpan f))).symm

private theorem val_stageFrameBasis_apply {n : ℕ} (f : finiteFullRankFrame 𝕜 k n) (i : Fin k) :
    (stageFrameBasis f i).val = coordinateInclusion n (f.1 i) := by
  simp [stageFrameBasis]

private theorem chartLinearMap_stageFrameBasis_symm (u : Fin k ↪ ℕ) {n : ℕ}
    (f : finiteFullRankFrame 𝕜 k n) (c : Fin k → 𝕜) :
    chartLinearMap u (toInfinite (frameSpan f)) ((stageFrameBasis f).equivFun.symm c) =
      frameCoordMatrix u f *ᵥ c := by
  ext j
  rw [Module.Basis.equivFun_symm_apply, map_sum, Finset.sum_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, Pi.smul_apply, chartLinearMap_apply, val_stageFrameBasis_apply,
    frameCoordMatrix, Matrix.of_apply, smul_eq_mul, mul_comm]

private theorem toInfinite_frameSpan_mem_chartDomain_iff (u : Fin k ↪ ℕ) {n : ℕ}
    (f : finiteFullRankFrame 𝕜 k n) :
    toInfinite (frameSpan f) ∈ chartDomain u ↔ IsUnit (frameCoordMatrix u f) := by
  have hcomp :
      chartLinearMap u (toInfinite (frameSpan f)) ∘ (stageFrameBasis f).equivFun.symm =
        (frameCoordMatrix u f).mulVec :=
    funext (chartLinearMap_stageFrameBasis_symm u f)
  rw [mem_chartDomain_iff_injective, ← Matrix.mulVec_injective_iff_isUnit, ← hcomp]
  refine ⟨fun h ↦ h.comp (stageFrameBasis f).equivFun.symm.injective, fun h x y hxy ↦ ?_⟩
  apply (stageFrameBasis f).equivFun.injective
  apply h
  simpa [Function.comp_apply] using hxy

private theorem chartEquiv_symm_stageFrameBasis (u : Fin k ↪ ℕ) {n : ℕ}
    (f : finiteFullRankFrame 𝕜 k n) (hf : toInfinite (frameSpan f) ∈ chartDomain u)
    (v : Fin k → 𝕜) :
    (chartEquiv u hf).symm v =
      (stageFrameBasis f).equivFun.symm ((frameCoordMatrix u f)⁻¹ *ᵥ v) := by
  have hu : IsUnit (frameCoordMatrix u f) :=
    (toInfinite_frameSpan_mem_chartDomain_iff u f).1 hf
  apply hf.1
  rw [chartLinearMap_chartEquiv_symm, chartLinearMap_stageFrameBasis_symm,
    Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.one_mulVec]

/-- Every coordinate-projection chart domain `chartDomain u` is open in the infinite
Grassmannian. -/
theorem isOpen_chartDomain (u : Fin k ↪ ℕ) : IsOpen (chartDomain (𝕜 := 𝕜) u) := by
  refine isOpen_iff.2 fun n ↦ isQuotientMap_frameSpan.isOpen_preimage.1 ?_
  have hset : (frameSpan ⁻¹' (toInfinite ⁻¹' chartDomain (𝕜 := 𝕜) u) :
      Set (finiteFullRankFrame 𝕜 k n)) =
      {f | (frameCoordMatrix u f).det ≠ 0} := by
    ext f
    simp [toInfinite_frameSpan_mem_chartDomain_iff, Matrix.isUnit_iff_isUnit_det]
  rw [hset]
  exact isOpen_ne.preimage (continuous_frameCoordMatrix u n).matrix_det

/-- Every `k`-plane in `ℕ →₀ 𝕜` lies in `chartDomain u` for some `u : Fin k ↪ ℕ`. -/
theorem exists_mem_chartDomain (W : infiniteGrassmannian 𝕜 k) :
    ∃ u : Fin k ↪ ℕ, W ∈ chartDomain u := by
  obtain ⟨n, V, rfl⟩ := exists_toInfinite_eq W
  obtain ⟨f, rfl⟩ := frameSpan_surjective V
  have hrow : LinearIndependent 𝕜 (Matrix.of f.1).row := f.2
  obtain ⟨e, he⟩ := Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero.1 hrow
  let u : Fin k ↪ ℕ := e.trans (Fin.valEmbedding (n := n))
  refine ⟨u, (toInfinite_frameSpan_mem_chartDomain_iff u f).2 ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hmat : frameCoordMatrix u f = ((Matrix.of f.1).submatrix id e)ᵀ := by
    ext j i
    simp [frameCoordMatrix, u, coordinateInclusion_apply_val]
  rwa [hmat, Matrix.det_transpose]

open Classical in
/-- Express an ambient linear map `ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F` in the inverse `u`-chart over `W`. -/
private def chartComp (u : Fin k ↪ ℕ) {F : Type*} [AddCommMonoid F] [Module 𝕜 F]
    (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) (W : infiniteGrassmannian 𝕜 k) : (Fin k → 𝕜) →ₗ[𝕜] F :=
  if hW : W ∈ chartDomain u then
    ψ.comp ((Tautological.subtype W).comp (chartEquiv u hW).symm.toLinearMap)
  else 0

private theorem chartComp_apply_of_mem (u : Fin k ↪ ℕ) {F : Type*} [AddCommMonoid F]
    [Module 𝕜 F] (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) {W : infiniteGrassmannian 𝕜 k}
    (hW : W ∈ chartDomain u) (v : Fin k → 𝕜) :
    chartComp u ψ W v = ψ (((chartEquiv u hW).symm v).val) := by
  rw [chartComp, dite_eq_left hW]
  rfl

private theorem continuousOn_chartComp_stage (u : Fin k ↪ ℕ) {F : Type*}
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]
    (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) (r : Fin k) (n : ℕ) :
    ContinuousOn
      (fun V : finiteGrassmannian 𝕜 k n ↦ chartComp u ψ (toInfinite V) (Pi.single r 1))
      (toInfinite ⁻¹' chartDomain u) := by
  rw [isQuotientMap_frameSpan.continuousOn_isOpen_iff
    ((isOpen_chartDomain u).preimage continuous_toInfinite)]
  have hdom : (frameSpan ⁻¹' (toInfinite ⁻¹' chartDomain (𝕜 := 𝕜) u) :
      Set (finiteFullRankFrame 𝕜 k n)) = {f | IsUnit (frameCoordMatrix u f)} := by
    ext f
    exact toInfinite_frameSpan_mem_chartDomain_iff u f
  rw [hdom]
  have hinv := continuousOn_inv_frameCoordMatrix (𝕜 := 𝕜) u n
  have hψn : Continuous (ψ.comp (coordinateInclusion n)) := LinearMap.continuous_on_pi _
  have hsum : ContinuousOn
      (fun f : finiteFullRankFrame 𝕜 k n ↦
        ∑ i : Fin k, ((frameCoordMatrix u f)⁻¹ *ᵥ Pi.single r 1) i •
          (ψ.comp (coordinateInclusion n)) (f.1 i))
      {f | IsUnit (frameCoordMatrix u f)} := by
    refine continuousOn_finsetSum (Finset.univ : Finset (Fin k)) fun i _ ↦ ?_
    have hcoeff : ContinuousOn (fun f : finiteFullRankFrame 𝕜 k n ↦
        ((frameCoordMatrix u f)⁻¹ *ᵥ Pi.single r 1) i) {f | IsUnit (frameCoordMatrix u f)} := by
      have hentry : ContinuousOn (fun f : finiteFullRankFrame 𝕜 k n ↦
          (frameCoordMatrix u f)⁻¹ i r) {f | IsUnit (frameCoordMatrix u f)} :=
        (continuous_apply r).comp_continuousOn ((continuous_apply i).comp_continuousOn hinv)
      refine hentry.congr fun f _ ↦ ?_
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hvec : Continuous fun f : finiteFullRankFrame 𝕜 k n ↦
        (ψ.comp (coordinateInclusion n)) (f.1 i) :=
      hψn.comp ((continuous_apply i).comp continuous_subtype_val)
    exact hcoeff.smul hvec.continuousOn
  refine hsum.congr fun f hf ↦ ?_
  have hf' : toInfinite (frameSpan f) ∈ chartDomain u :=
    (toInfinite_frameSpan_mem_chartDomain_iff u f).2 hf
  dsimp only [Function.comp_def]
  rw [chartComp_apply_of_mem u ψ hf', chartEquiv_symm_stageFrameBasis u f hf',
    Module.Basis.equivFun_symm_apply]
  have hval : (∑ i : Fin k, ((frameCoordMatrix u f)⁻¹ *ᵥ Pi.single r 1) i •
      stageFrameBasis f i).val =
      ∑ i : Fin k, ((frameCoordMatrix u f)⁻¹ *ᵥ Pi.single r 1) i •
        coordinateInclusion n (f.1 i) := by
    have h := map_sum (Tautological.subtype (toInfinite (frameSpan f)))
      (fun i : Fin k ↦ ((frameCoordMatrix u f)⁻¹ *ᵥ Pi.single r 1) i • stageFrameBasis f i)
      Finset.univ
    simpa only [Tautological.subtype_apply, map_smul, val_stageFrameBasis_apply] using h
  rw [hval, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, LinearMap.comp_apply]

private theorem continuousOn_chartComp_eval (u : Fin k ↪ ℕ) {F : Type*}
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]
    (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) (r : Fin k) :
    ContinuousOn
      (fun W : infiniteGrassmannian 𝕜 k ↦ chartComp u ψ W (Pi.single r 1)) (chartDomain u) :=
  (continuousOn_iff_of_isOpen (isOpen_chartDomain u)).2
    (continuousOn_chartComp_stage u ψ r)

/-- On `chartDomain u ×ˢ univ`, any ambient linear map `ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F` into a topological
`𝕜`-module varies continuously when evaluated in the inverse `u`-chart. -/
private theorem continuousOn_chartComp_prod (u : Fin k ↪ ℕ) {F : Type*}
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]
    (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) :
    ContinuousOn
      (fun q : infiniteGrassmannian 𝕜 k × (Fin k → 𝕜) ↦ chartComp u ψ q.1 q.2)
      (chartDomain u ×ˢ univ) := by
  have hfst (r : Fin k) : ContinuousOn
      (fun q : infiniteGrassmannian 𝕜 k × (Fin k → 𝕜) ↦ chartComp u ψ q.1 (Pi.single r 1))
      (chartDomain u ×ˢ univ) :=
    (continuousOn_chartComp_eval u ψ r).comp continuousOn_fst fun _ hq ↦ hq.1
  have hsum : ContinuousOn
      (fun q : infiniteGrassmannian 𝕜 k × (Fin k → 𝕜) ↦
        ∑ r : Fin k, q.2 r • chartComp u ψ q.1 (Pi.single r 1))
      (chartDomain u ×ˢ univ) :=
    continuousOn_finsetSum (Finset.univ : Finset (Fin k)) fun r _ ↦
      ((continuous_apply r).comp continuous_snd).continuousOn.smul (hfst r)
  refine hsum.congr fun q _ ↦ ?_
  have hv : q.2 = ∑ r : Fin k, q.2 r • Pi.single r 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  dsimp only
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul]

/-- Promote any `𝕜`-linear endomorphism of `Fin k → 𝕜` to a continuous linear map, without
requiring completeness of `𝕜`. -/
private def piEndToCLM (L : (Fin k → 𝕜) →ₗ[𝕜] (Fin k → 𝕜)) :
    (Fin k → 𝕜) →L[𝕜] (Fin k → 𝕜) :=
  ∑ r : Fin k, ContinuousLinearMap.smulRightL 𝕜 (Fin k → 𝕜) (Fin k → 𝕜)
    (ContinuousLinearMap.proj r) (L (Pi.single r 1))

private theorem piEndToCLM_apply (L : (Fin k → 𝕜) →ₗ[𝕜] (Fin k → 𝕜)) (v : Fin k → 𝕜) :
    piEndToCLM L v = L v := by
  have hv : v = ∑ r : Fin k, v r • Pi.single r 1 := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hv, map_sum]
  rw [piEndToCLM, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, map_smul]

/-- Canonical embedding of the total space of `Tautological 𝕜 k` into
`infiniteGrassmannian 𝕜 k × (ℕ → 𝕜)` recording the base plane and all ambient coordinates. -/
def totalSpaceEmbed (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :
    infiniteGrassmannian 𝕜 k × (ℕ → 𝕜) :=
  (p.proj, fun m ↦ p.2.val m)

@[simp]
theorem totalSpaceEmbed_fst (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :
    (totalSpaceEmbed p).1 = p.proj := (rfl)

@[simp]
theorem totalSpaceEmbed_snd_apply (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) (m : ℕ) :
    (totalSpaceEmbed p).2 m = p.2.val m := (rfl)

theorem totalSpaceEmbed_injective :
    Injective (totalSpaceEmbed : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) → _) := by
  rintro ⟨W₁, v₁⟩ ⟨W₂, v₂⟩ h
  have hW : W₁ = W₂ := congrArg Prod.fst h
  subst hW
  refine congrArg (TotalSpace.mk W₁) (Tautological.ext (Finsupp.ext fun m ↦ ?_))
  exact congrFun (congrArg Prod.snd h) m

variable (𝕜 k) in
/-- The total space of `Tautological 𝕜 k` carries the topology induced by `totalSpaceEmbed`. -/
instance : TopologicalSpace (TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :=
  TopologicalSpace.induced totalSpaceEmbed inferInstance

/-- `totalSpaceEmbed` is a topological embedding into `infiniteGrassmannian 𝕜 k × (ℕ → 𝕜)`. -/
theorem isEmbedding_totalSpaceEmbed :
    IsEmbedding (totalSpaceEmbed : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) → _) :=
  ⟨⟨rfl⟩, totalSpaceEmbed_injective⟩

/-- **Universal total-space continuity criterion.** A map into the total space of
`Tautological 𝕜 k` is continuous if and only if its base map into `infiniteGrassmannian 𝕜 k` is
continuous and every ambient coordinate `m : ℕ` is continuous. -/
theorem continuous_totalSpace_iff {Z : Type*} [TopologicalSpace Z]
    {f : Z → TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)} :
    Continuous f ↔
      Continuous (fun z ↦ (f z).proj) ∧
        ∀ m : ℕ, Continuous fun z ↦ (f z).2.val m := by
  rw [isEmbedding_totalSpaceEmbed.isInducing.continuous_iff]
  simp only [Function.comp_def, totalSpaceEmbed, continuous_prodMk, continuous_pi_iff]

/-- Evaluating the `m`-th coordinate in `ℕ →₀ 𝕜` is continuous on the total space of
`Tautological 𝕜 k`. -/
@[fun_prop]
theorem continuous_evalCoord (m : ℕ) :
    Continuous fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦ p.2.val m :=
  (continuous_totalSpace_iff.1 continuous_id).2 m

/-- Inclusion of a fibre `Tautological 𝕜 k W` into the total space is a topological inducing map. -/
theorem isInducing_totalSpaceMk (W : infiniteGrassmannian 𝕜 k) :
    IsInducing
      (TotalSpace.mk W : Tautological 𝕜 k W → TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) := by
  obtain ⟨u, hu⟩ := exists_mem_chartDomain W
  let e := chartEquiv u hu
  have hmk : Continuous (TotalSpace.mk W : Tautological 𝕜 k W → _) :=
    continuous_totalSpace_iff.2 ⟨continuous_const, fun m ↦
      IsModuleTopology.continuous_of_linearMap ((Finsupp.lapply m).comp (Tautological.subtype W))⟩
  have hproj : Continuous fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦
      (fun i : Fin k ↦ p.2.val (u i)) :=
    continuous_pi fun i ↦ continuous_evalCoord (u i)
  have hcomp : (fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦
      fun i : Fin k ↦ p.2.val (u i)) ∘ TotalSpace.mk W = e := by
    ext v i
    rw [Function.comp_apply, chartEquiv_apply, chartLinearMap_apply]
  exact .of_comp hmk hproj (hcomp ▸ e.toHomeomorph.isInducing)

open Classical in
private def chartSymm (u : Fin k ↪ ℕ) (W : infiniteGrassmannian 𝕜 k) (v : Fin k → 𝕜) :
    Tautological 𝕜 k W :=
  if hW : W ∈ chartDomain u then (chartEquiv u hW).symm v else 0

private theorem chartSymm_of_mem (u : Fin k ↪ ℕ) {W : infiniteGrassmannian 𝕜 k}
    (hW : W ∈ chartDomain u) (v : Fin k → 𝕜) :
    chartSymm u W v = (chartEquiv u hW).symm v :=
  dite_eq_left hW

/-- The local trivialization of `Tautological 𝕜 k` over `chartDomain u` given by coordinate
projection onto `u : Fin k ↪ ℕ`. -/
def trivialization (u : Fin k ↪ ℕ) :
    Trivialization (Fin k → 𝕜) (π (Fin k → 𝕜) (Tautological 𝕜 k)) where
  toFun p := (p.proj, chartLinearMap u p.proj p.2)
  invFun q := ⟨q.1, chartSymm u q.1 q.2⟩
  source := π (Fin k → 𝕜) (Tautological 𝕜 k) ⁻¹' chartDomain u
  target := chartDomain u ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p hp := by
    ext1
    · rfl
    · simp only [mem_preimage] at hp
      dsimp only
      rw [chartSymm_of_mem u hp, chartEquiv_symm_chartLinearMap]
  right_inv' q hq := by
    ext1
    · rfl
    · dsimp only
      rw [chartSymm_of_mem u hq.1, chartLinearMap_chartEquiv_symm]
  open_source := (isOpen_chartDomain u).preimage
    (continuous_fst.comp isEmbedding_totalSpaceEmbed.continuous)
  open_target := (isOpen_chartDomain u).prod isOpen_univ
  continuousOn_toFun :=
    ((continuous_fst.comp isEmbedding_totalSpaceEmbed.continuous).prodMk
      (continuous_pi fun i ↦ continuous_evalCoord (u i))).continuousOn
  continuousOn_invFun := by
    rw [isEmbedding_totalSpaceEmbed.isInducing.continuousOn_iff]
    refine continuousOn_fst.prodMk (continuousOn_pi.2 fun m ↦ ?_)
    refine (continuousOn_chartComp_prod u (Finsupp.lapply m)).congr fun q hq ↦ ?_
    dsimp only [Function.comp_def, totalSpaceEmbed]
    rw [chartSymm_of_mem u hq.1, chartComp_apply_of_mem u (Finsupp.lapply m) hq.1]
    rfl
  baseSet := chartDomain u
  open_baseSet := isOpen_chartDomain u
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem trivialization_baseSet (u : Fin k ↪ ℕ) :
    (trivialization (𝕜 := 𝕜) u).baseSet = chartDomain u := (rfl)

@[simp]
theorem trivialization_apply (u : Fin k ↪ ℕ)
    (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :
    trivialization u p = (p.proj, chartLinearMap u p.proj p.2) := (rfl)

theorem trivialization_symm_apply (u : Fin k ↪ ℕ) {W : infiniteGrassmannian 𝕜 k}
    (hW : W ∈ chartDomain u) (v : Fin k → 𝕜) :
    (trivialization u).symm W v = (chartEquiv u hW).symm v := by
  apply hW.1
  have h := congrArg Prod.snd ((trivialization u).apply_mk_symm hW v)
  simpa only [trivialization_apply, chartLinearMap_chartEquiv_symm] using h

instance isLinear_trivialization (u : Fin k ↪ ℕ) :
    (trivialization (𝕜 := 𝕜) u).IsLinear 𝕜 where
  linear W _ := (chartLinearMap u W).isLinear

/-- A chosen coordinate chart index `u : Fin k ↪ ℕ` whose domain contains `W`. -/
def chartIndex (W : infiniteGrassmannian 𝕜 k) : Fin k ↪ ℕ :=
  (exists_mem_chartDomain W).choose

/-- Every point `W` lies in the chart domain of `chartIndex W`. -/
theorem mem_chartDomain_chartIndex (W : infiniteGrassmannian 𝕜 k) :
    W ∈ chartDomain (chartIndex W) :=
  (exists_mem_chartDomain W).choose_spec

variable (𝕜 k) in
instance : FiberBundle (Fin k → 𝕜) (Tautological 𝕜 k) where
  totalSpaceMk_isInducing' := isInducing_totalSpaceMk
  trivializationAtlas' := range (trivialization (𝕜 := 𝕜) (k := k))
  trivializationAt' W := trivialization (chartIndex W)
  mem_baseSet_trivializationAt' W := by
    rw [trivialization_baseSet]
    exact mem_chartDomain_chartIndex W
  trivialization_mem_atlas' W := ⟨chartIndex W, rfl⟩

private theorem continuousOn_coordChangeL_trivialization (u u' : Fin k ↪ ℕ) :
    ContinuousOn
      (fun W ↦ ((trivialization (𝕜 := 𝕜) u).coordChangeL 𝕜 (trivialization u') W :
        (Fin k → 𝕜) →L[𝕜] (Fin k → 𝕜)))
      (chartDomain u ∩ chartDomain u') := by
  have hsum : ContinuousOn
      (fun W : infiniteGrassmannian 𝕜 k ↦ piEndToCLM (chartComp u (coordProj u') W))
      (chartDomain u) :=
    continuousOn_finsetSum (Finset.univ : Finset (Fin k)) fun r _ ↦
      (ContinuousLinearMap.smulRightL 𝕜 (Fin k → 𝕜) (Fin k → 𝕜)
        (ContinuousLinearMap.proj r)).continuous.comp_continuousOn
          (continuousOn_chartComp_eval u (coordProj u') r)
  refine (hsum.mono inter_subset_left).congr fun W hW ↦ ContinuousLinearMap.ext fun v ↦ ?_
  have hcoord :
      ((trivialization (𝕜 := 𝕜) u).coordChangeL 𝕜 (trivialization u') W) v =
        (trivialization u' ⟨W, (trivialization u).symm W v⟩).2 :=
    Trivialization.coordChangeL_apply (trivialization u) (trivialization u') hW v
  rw [ContinuousLinearEquiv.coe_coe, hcoord, trivialization_apply,
    trivialization_symm_apply u hW.1 v, piEndToCLM_apply,
    chartComp_apply_of_mem u (coordProj u') hW.1 v]
  rfl

variable (𝕜 k) in
instance : VectorBundle 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) where
  trivialization_linear' := by
    rintro e he
    rcases he.out with ⟨u, rfl⟩
    exact isLinear_trivialization u
  continuousOn_coordChange' := by
    rintro e e' he he'
    rcases he.out with ⟨u, rfl⟩
    rcases he'.out with ⟨u', rfl⟩
    exact continuousOn_coordChangeL_trivialization u u'

/-- Every linear map `ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F` into a topological `𝕜`-module is continuous on the
total space of the universal tautological bundle. -/
theorem continuous_linearMap_totalSpace {F : Type*} [AddCommMonoid F] [Module 𝕜 F]
    [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F] (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] F) :
    Continuous fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦ ψ p.2.val := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  let u := chartIndex p.proj
  let e := trivialization (𝕜 := 𝕜) u
  have hp_base : p.proj ∈ chartDomain u := mem_chartDomain_chartIndex p.proj
  have hp_src : p ∈ e.source := hp_base
  have hp_tgt : e p ∈ chartDomain u ×ˢ (univ : Set (Fin k → 𝕜)) := ⟨hp_base, mem_univ _⟩
  have happ : ContinuousAt
      (fun q : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦ chartComp u ψ (e q).1 (e q).2) p :=
    ((continuousOn_chartComp_prod u ψ).continuousAt
      (((isOpen_chartDomain u).prod isOpen_univ).mem_nhds hp_tgt)).comp
        (e.continuousOn.continuousAt (e.open_source.mem_nhds hp_src))
  refine happ.congr_of_eventuallyEq ?_
  filter_upwards [e.open_source.mem_nhds hp_src] with q hq
  have hq_base : q.proj ∈ chartDomain u := hq
  rw [trivialization_apply, chartComp_apply_of_mem u ψ hq_base, chartEquiv_symm_chartLinearMap]

/-- Every ambient linear form `ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] 𝕜` is continuous on the total space of
`Tautological 𝕜 k`. -/
theorem continuous_linearForm_totalSpace (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] 𝕜) :
    Continuous fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ↦ ψ p.2.val :=
  continuous_linearMap_totalSpace ψ

end VectorBundle

section PullbackComparisons

section AmbientMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k : ℕ}

/-- An injective linear endomorphism `φ` of `ℕ →₀ 𝕜` maps each tautological fibre `W`
isomorphically onto the tautological fibre over `map φ hφ W`. -/
def mapTautologicalEquiv (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (W : infiniteGrassmannian 𝕜 k) :
    Tautological 𝕜 k W ≃L[𝕜] Tautological 𝕜 k (map φ hφ W) :=
  ((tautologicalEquiv 𝕜 k W).trans
    ((Submodule.equivMapOfInjective φ hφ W.1).trans
      (tautologicalEquiv 𝕜 k (map φ hφ W)).symm)).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem val_mapTautologicalEquiv (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (W : infiniteGrassmannian 𝕜 k) (v : Tautological 𝕜 k W) :
    (mapTautologicalEquiv φ hφ W v).val = φ v.val := by
  rw [mapTautologicalEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]
  rfl

/-- Over a complete normed field, `Tautological 𝕜 k` is isomorphic over the identity to its
pullback along `mapContinuousMap φ hφ` for any ambient linear injection
`φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)`. -/
def mapTautologicalHomeomorph [CompleteSpace 𝕜]
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) :
    TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k) ≃ₜ
      TotalSpace (Fin k → 𝕜) ((mapContinuousMap (k := k) φ hφ : _ → _) *ᵖ (Tautological 𝕜 k)) :=
  bundleHomeomorph (E₁ := Tautological 𝕜 k)
    (E₂ := (mapContinuousMap (k := k) φ hφ : _ → _) *ᵖ (Tautological 𝕜 k))
    (mapTautologicalEquiv φ hφ) <|
      Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj _ _, by
        refine continuous_totalSpace_iff.2
          ⟨(continuous_map φ hφ).comp (FiberBundle.continuous_proj _ _), fun m ↦ ?_⟩
        refine (continuous_linearForm_totalSpace (k := k) ((Finsupp.lapply m).comp φ)).congr
          fun p ↦ ?_
        rw [LinearMap.comp_apply, Finsupp.lapply_apply,
          ← val_mapTautologicalEquiv φ hφ p.proj p.2]
        rfl⟩

@[simp]
theorem mapTautologicalHomeomorph_apply [CompleteSpace 𝕜]
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k)) :
    mapTautologicalHomeomorph φ hφ p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (mapTautologicalEquiv φ hφ p.proj p.2) :=
  bundleHomeomorph_apply (E₁ := Tautological 𝕜 k)
    (E₂ := (mapContinuousMap (k := k) φ hφ : _ → _) *ᵖ (Tautological 𝕜 k))
    (mapTautologicalEquiv φ hφ) _ p

@[simp]
theorem mapTautologicalHomeomorph_symm_apply [CompleteSpace 𝕜]
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
    (p : TotalSpace (Fin k → 𝕜)
      ((mapContinuousMap (k := k) φ hφ : _ → _) *ᵖ (Tautological 𝕜 k))) :
    (mapTautologicalHomeomorph φ hφ).symm p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj ((mapTautologicalEquiv φ hφ p.proj).symm p.2) :=
  bundleHomeomorph_symm_apply (E₁ := Tautological 𝕜 k)
    (E₂ := (mapContinuousMap (k := k) φ hφ : _ → _) *ᵖ (Tautological 𝕜 k))
    (mapTautologicalEquiv φ hφ) _ p

end AmbientMap

end PullbackComparisons

end infiniteGrassmannian

namespace finiteGrassmannian

section StageComparison

variable {𝕜 : Type*} [RCLike 𝕜] {k n : ℕ}

/-- Over `RCLike 𝕜`, the coordinate inclusion identifies the finite Grassmannian's tautological
fibre over `V` with the infinite Grassmannian's tautological fibre over `V.toInfinite`. -/
def toInfiniteTautologicalEquiv (V : finiteGrassmannian 𝕜 k n) :
    Tautological 𝕜 k n V ≃L[𝕜] infiniteGrassmannian.Tautological 𝕜 k V.toInfinite :=
  ((tautologicalEquiv 𝕜 k n V).trans <|
    (Submodule.equivMapOfInjective (coordinateInclusion n)
      (coordinateInclusion_injective n) V.1).trans <|
        (LinearEquiv.ofEq _ _ (coe_toInfinite V).symm).trans
          (infiniteGrassmannian.tautologicalEquiv 𝕜 k V.toInfinite).symm).toContinuousLinearEquiv

@[simp]
theorem val_toInfiniteTautologicalEquiv (V : finiteGrassmannian 𝕜 k n)
    (v : Tautological 𝕜 k n V) :
    (V.toInfiniteTautologicalEquiv v).val = coordinateInclusion n (WithLp.ofLp v.1) := by
  simp [toInfiniteTautologicalEquiv]

variable (𝕜 k n) in
/-- Over `RCLike 𝕜`, the tautological bundle `finiteGrassmannian.Tautological 𝕜 k n` over the
`n`-th finite Grassmannian is homeomorphic, linearly on each fibre, to the pullback of
`infiniteGrassmannian.Tautological 𝕜 k` along `toInfiniteContinuousMap`. -/
def toInfiniteTautologicalHomeomorph :
    TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k n) ≃ₜ
      TotalSpace (Fin k → 𝕜)
        ((toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
          (infiniteGrassmannian.Tautological 𝕜 k)) :=
  bundleHomeomorph
    (E₁ := Tautological 𝕜 k n)
    (E₂ := (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (infiniteGrassmannian.Tautological 𝕜 k))
    toInfiniteTautologicalEquiv <|
      Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj _ _, by
        refine infiniteGrassmannian.continuous_totalSpace_iff.2
          ⟨continuous_toInfinite.comp (FiberBundle.continuous_proj _ _), fun m ↦ ?_⟩
        have hlin : Continuous
            ((Finsupp.lapply (R := 𝕜) (M := 𝕜) m).comp (coordinateInclusion n)) :=
          LinearMap.continuous_on_pi _
        have hemb : Continuous fun p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k n) ↦
            WithLp.ofLp p.2.1 :=
          (PiLp.continuous_ofLp 2 _).comp
            (continuous_snd.comp (isEmbedding_totalSpace_range _ _).continuous)
        refine (hlin.comp hemb).congr fun p ↦ ?_
        rw [Function.comp_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
          ← val_toInfiniteTautologicalEquiv p.proj p.2]
        rfl⟩

@[simp]
theorem toInfiniteTautologicalHomeomorph_apply
    (p : TotalSpace (Fin k → 𝕜) (Tautological 𝕜 k n)) :
    toInfiniteTautologicalHomeomorph 𝕜 k n p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (p.proj.toInfiniteTautologicalEquiv p.2) :=
  bundleHomeomorph_apply
    (E₁ := Tautological 𝕜 k n)
    (E₂ := (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (infiniteGrassmannian.Tautological 𝕜 k))
    toInfiniteTautologicalEquiv _ p

@[simp]
theorem toInfiniteTautologicalHomeomorph_symm_apply
    (p : TotalSpace (Fin k → 𝕜)
      ((toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (infiniteGrassmannian.Tautological 𝕜 k))) :
    (toInfiniteTautologicalHomeomorph 𝕜 k n).symm p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (p.proj.toInfiniteTautologicalEquiv.symm p.2) :=
  bundleHomeomorph_symm_apply
    (E₁ := Tautological 𝕜 k n)
    (E₂ := (toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (infiniteGrassmannian.Tautological 𝕜 k))
    toInfiniteTautologicalEquiv _ p

end StageComparison

end finiteGrassmannian

end TauCeti
