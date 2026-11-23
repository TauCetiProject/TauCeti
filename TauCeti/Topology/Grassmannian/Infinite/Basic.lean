/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Stabilization
public import TauCeti.LinearAlgebra.Finsupp.CoordinateInclusion
public import TauCeti.LinearAlgebra.Finsupp.Supported
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.Paracompact
import TauCeti.Topology.Category.TopCat.Lindelof
import TauCeti.Topology.Category.TopCat.Normal
import TauCeti.Topology.Compactness.Paracompact
import TauCeti.Topology.Grassmannian.Map

/-!
# The infinite Grassmannian of a fixed rank

For a field `𝕜` and `k : ℕ`, `TauCeti.infiniteGrassmannian 𝕜 k` is the set of `k`-dimensional
subspaces of the countable coordinate space `ℕ →₀ 𝕜`. A subspace of the finite coordinate space
`Fin n → 𝕜` is sent into it by the coordinate inclusion `e_i ↦ e_i`
(`TauCeti.finiteGrassmannian.toInfinite`), and this inclusion is compatible with the ambient
stabilization `𝕜^n → 𝕜^(n + 1)` that appends a zero last coordinate. Every finite-dimensional
subspace of `ℕ →₀ 𝕜` lies in a finite coordinate stage, so the infinite Grassmannian is the union
of the finite Grassmannians along these inclusions. It carries the final topology for the stage
inclusions.

We show that this union is the colimit, in `TopCat`, of the sequence of finite Grassmannians
`Gr_k(𝕜^n)` along ambient stabilization (`TauCeti.infiniteGrassmannian.isColimit`); the stages
with `n < k` are empty, so this is the same as the colimit of the stages `Gr_k(𝕜^(N + k))`.
Points are closed whenever they are closed in each finite stage. Over the real or complex
numbers, where the finite Grassmannians are compact Hausdorff, each stage inclusion is a closed
embedding, equipping `infiniteGrassmannian 𝕜 k` with `LindelofSpace`, `T4Space`, and
`ParacompactSpace` instances; we also record functoriality under ambient injections (`map`,
`mapContinuousMap`).

Over `ℝ` and `ℂ` these are the standard models `BO(k)` and `BU(k)` for classifying rank-`k` real
and complex vector bundles, and the rank-one case is the infinite projective space `ℝP∞` or
`ℂP∞`; the tautological bundle and the classification theorem are not part of this file.
The basepoint in rank `k` is the span of the first `k` coordinate vectors; in rank zero it is the
only point.

The construction of the infinite Grassmannian as the union of the finite ones with the direct
limit topology follows J. Milnor and J. Stasheff, *Characteristic Classes*, §5.
-/

public section

open Set Function Topology CategoryTheory Limits
open _root_.Finsupp

namespace TauCeti

section

variable (𝕜 : Type*) [Field 𝕜] (k : ℕ)

/-- The infinite Grassmannian of `k`-dimensional subspaces of the countable coordinate space
`ℕ →₀ 𝕜`. The rank is a cardinal, so every point is a finite-dimensional subspace, including in
rank zero. -/
abbrev infiniteGrassmannian : Type _ :=
  {V : Submodule 𝕜 (ℕ →₀ 𝕜) // Module.rank 𝕜 V = k}

namespace finiteGrassmannian

variable {𝕜 k} {n : ℕ}

/-- A `k`-dimensional subspace of `𝕜^n`, viewed in `ℕ →₀ 𝕜` through the coordinate inclusion. -/
noncomputable def toInfinite (V : finiteGrassmannian 𝕜 k n) : infiniteGrassmannian 𝕜 k :=
  ⟨V.val.map (coordinateInclusion n), by
    rw [rank_map_eq (coordinateInclusion_injective n), ← Module.finrank_eq_rank, V.property]⟩

theorem coe_toInfinite (V : finiteGrassmannian 𝕜 k n) :
    (toInfinite V).val = V.val.map (coordinateInclusion n) := (rfl)

/-- Membership in a finite stage is detected by restricting to its coordinates and checking
that all later coordinates vanish. -/
@[simp]
theorem mem_toInfinite (V : finiteGrassmannian 𝕜 k n) (v : ℕ →₀ 𝕜) :
    v ∈ (toInfinite V).val ↔ (fun i : Fin n ↦ v i) ∈ V.val ∧ ∀ i, n ≤ i → v i = 0 := by
  rw [coe_toInfinite, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨by simpa only [coordinateInclusion_apply_val] using hw,
      fun i hi ↦ coordinateInclusion_apply_of_le w hi⟩
  · rintro ⟨hv, hz⟩
    refine ⟨fun i ↦ v i, hv, ?_⟩
    ext i
    by_cases hi : i < n
    · exact coordinateInclusion_apply_val _ ⟨i, hi⟩
    · rw [coordinateInclusion_apply_of_le _ (Nat.le_of_not_gt hi),
        hz i (Nat.le_of_not_gt hi)]

theorem toInfinite_injective : Function.Injective (toInfinite : finiteGrassmannian 𝕜 k n → _) :=
  fun _ _ h ↦ Subtype.ext
    (Submodule.map_injective_of_injective (coordinateInclusion_injective n) congr(($h).val))

@[simp]
theorem toInfinite_inj {V W : finiteGrassmannian 𝕜 k n} : toInfinite V = toInfinite W ↔ V = W :=
  toInfinite_injective.eq_iff

/-- Including into a larger coordinate space does not change the subspace of `ℕ →₀ 𝕜`. -/
@[simp]
theorem toInfinite_ambientInclusion {m : ℕ} (h : n ≤ m) (V : finiteGrassmannian 𝕜 k n) :
    toInfinite (ambientInclusion h V) = toInfinite V := by
  apply Subtype.ext
  rw [coe_toInfinite, coe_ambientInclusion, ← Submodule.map_comp,
    coordinateInclusion_comp_extendByZero_castLE, coe_toInfinite]

/-- Appending a zero last coordinate does not change the subspace of `ℕ →₀ 𝕜`. -/
@[simp]
theorem toInfinite_ambientStabilization (V : finiteGrassmannian 𝕜 k n) :
    toInfinite (ambientStabilization V) = toInfinite V := by
  rw [← ambientInclusion_succ, toInfinite_ambientInclusion]

/-- Two stages map to the same point of the infinite Grassmannian exactly when they agree in the
larger stage. -/
theorem toInfinite_eq_toInfinite_iff {m : ℕ} (h : n ≤ m) {V : finiteGrassmannian 𝕜 k n}
    {W : finiteGrassmannian 𝕜 k m} : toInfinite V = toInfinite W ↔ ambientInclusion h V = W := by
  rw [← toInfinite_ambientInclusion h V, toInfinite_inj]

/-- A point of the infinite Grassmannian comes from the `n`-th finite stage exactly when it
consists of functions vanishing from coordinate `n` on. -/
theorem mem_range_toInfinite_iff (W : infiniteGrassmannian 𝕜 k) :
    W ∈ range (toInfinite : finiteGrassmannian 𝕜 k n → _) ↔
      W.val ≤ Finsupp.supported 𝕜 𝕜 (Iio n) := by
  constructor
  · rintro ⟨V, rfl⟩
    rw [coe_toInfinite, ← range_coordinateInclusion]
    exact LinearMap.map_le_range
  · intro hW
    rw [← range_coordinateInclusion] at hW
    have hmap : (W.val.comap (coordinateInclusion n)).map (coordinateInclusion n) = W.val :=
      Submodule.map_comap_eq_of_le hW
    have hrank : Module.rank 𝕜 (W.val.comap (coordinateInclusion n)) = k := by
      rw [← rank_map_eq (coordinateInclusion_injective n), hmap, W.property]
    exact ⟨⟨_, Module.finrank_eq_of_rank_eq hrank⟩, Subtype.ext hmap⟩

end finiteGrassmannian

end

namespace infiniteGrassmannian

open finiteGrassmannian

section

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ}

/-- Every point of the infinite Grassmannian comes from some finite stage. -/
theorem exists_toInfinite_eq (W : infiniteGrassmannian 𝕜 k) :
    ∃ (n : ℕ) (V : finiteGrassmannian 𝕜 k n), toInfinite V = W := by
  have : FiniteDimensional 𝕜 W.val := .of_rank_eq_nat W.property
  obtain ⟨n, hn⟩ := (Module.Finite.iff_fg.1 this).exists_le_supported_Iio
  exact ⟨n, (mem_range_toInfinite_iff W).2 hn⟩

theorem iUnion_range_toInfinite :
    ⋃ n, range (toInfinite : finiteGrassmannian 𝕜 k n → _) = univ :=
  eq_univ_of_forall fun W ↦ mem_iUnion.2 <| by
    obtain ⟨n, V, rfl⟩ := exists_toInfinite_eq W
    exact ⟨n, V, rfl⟩

variable (𝕜 k) in
/-- The basepoint in rank `k`: the span of the first `k` coordinate vectors. -/
noncomputable def basepoint : infiniteGrassmannian 𝕜 k :=
  toInfinite (⟨⊤, finrank_top 𝕜 _ |>.trans (Module.finrank_fin_fun 𝕜)⟩ : finiteGrassmannian 𝕜 k k)

@[simp]
theorem coe_basepoint : (basepoint 𝕜 k).val = Finsupp.supported 𝕜 𝕜 (Iio k) := by
  rw [basepoint, coe_toInfinite, Submodule.map_top, range_coordinateInclusion]

noncomputable instance : Inhabited (infiniteGrassmannian 𝕜 k) :=
  ⟨basepoint 𝕜 k⟩

/-- In rank zero the only point is the zero subspace. -/
noncomputable instance : Unique (infiniteGrassmannian 𝕜 0) where
  default := basepoint 𝕜 0
  uniq W := Subtype.ext <| by
    have hW : W.val = ⊥ := Submodule.rank_eq_zero.1 (by simpa using W.property)
    simp [hW]

section Topology

variable [TopologicalSpace 𝕜]

/-- The final topology for the inclusions of the finite Grassmannians. -/
noncomputable instance : TopologicalSpace (infiniteGrassmannian 𝕜 k) :=
  ⨆ n, .coinduced (toInfinite : finiteGrassmannian 𝕜 k n → _) inferInstance

@[fun_prop]
theorem _root_.TauCeti.finiteGrassmannian.continuous_toInfinite {n : ℕ} :
    Continuous (toInfinite : finiteGrassmannian 𝕜 k n → infiniteGrassmannian 𝕜 k) :=
  continuous_iff_coinduced_le.2 <| le_iSup
    (fun n ↦ TopologicalSpace.coinduced (toInfinite : finiteGrassmannian 𝕜 k n → _) inferInstance) n

/-- `finiteGrassmannian.toInfinite` as a `ContinuousMap` (exposed for pullback fibre reduction). -/
@[expose] noncomputable def _root_.TauCeti.finiteGrassmannian.toInfiniteContinuousMap {n : ℕ} :
    C(finiteGrassmannian 𝕜 k n, infiniteGrassmannian 𝕜 k) := ⟨toInfinite, continuous_toInfinite⟩

@[simp] theorem _root_.TauCeti.finiteGrassmannian.toInfiniteContinuousMap_apply {n : ℕ}
    (V : finiteGrassmannian 𝕜 k n) : toInfiniteContinuousMap V = toInfinite V := (rfl)

/-- A subset of the infinite Grassmannian is open exactly when its preimage in every finite
coordinate stage is open. -/
theorem isOpen_iff {U : Set (infiniteGrassmannian 𝕜 k)} :
    IsOpen U ↔ ∀ n, IsOpen ((toInfinite : finiteGrassmannian 𝕜 k n → _) ⁻¹' U) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]

/-- A subset of the infinite Grassmannian is closed exactly when its preimage in every finite
coordinate stage is closed. -/
theorem isClosed_iff {C : Set (infiniteGrassmannian 𝕜 k)} :
    IsClosed C ↔ ∀ n, IsClosed ((toInfinite : finiteGrassmannian 𝕜 k n → _) ⁻¹' C) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- Points are closed in the final topology whenever they are closed in every finite stage. -/
instance [∀ n, T1Space (finiteGrassmannian 𝕜 k n)] :
    T1Space (infiniteGrassmannian 𝕜 k) where
  t1 W := isClosed_iff.2 fun n ↦ by
    apply Set.Subsingleton.isClosed
    intro V hV V' hV'
    exact toInfinite_injective (hV.trans hV'.symm)

/-- A map out of the infinite Grassmannian is continuous exactly when it is continuous on every
finite stage. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : infiniteGrassmannian 𝕜 k → X} :
    Continuous f ↔ ∀ n, Continuous (f ∘ (toInfinite : finiteGrassmannian 𝕜 k n → _)) := by
  simp only [continuous_def, isOpen_iff, preimage_comp]
  exact ⟨fun h n U hU ↦ h U hU n, fun h U hU n ↦ h n U hU⟩

/-- On an open set, continuity on `infiniteGrassmannian 𝕜 k` reduces to every finite stage. -/
theorem continuousOn_iff_of_isOpen {X : Type*} [TopologicalSpace X]
    {U : Set (infiniteGrassmannian 𝕜 k)} (hU : IsOpen U) {f : infiniteGrassmannian 𝕜 k → X} :
    ContinuousOn f U ↔
      ∀ n, ContinuousOn (f ∘ (toInfinite : finiteGrassmannian 𝕜 k n → _)) (toInfinite ⁻¹' U) :=
  ⟨fun h n ↦ (continuousOn_open_iff (hU.preimage continuous_toInfinite)).2 fun t ht ↦ by
      rw [preimage_comp, ← preimage_inter]
      exact (isOpen_iff.1 ((continuousOn_open_iff hU).1 h t ht)) n,
   fun h ↦ (continuousOn_open_iff hU).2 fun t ht ↦ isOpen_iff.2 fun n ↦ by
      rw [preimage_inter, ← preimage_comp]
      exact (continuousOn_open_iff (hU.preimage continuous_toInfinite)).1 (h n) t ht⟩

end Topology

end

section Colimit

variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] (k : ℕ)

variable (𝕜) in
/-- The sequence of finite Grassmannians `Gr_k(𝕜^n)` along the inclusions onto the first
coordinates; its one-step maps are ambient stabilization. The body is exposed so that its objects
are the finite Grassmannians themselves and its maps apply to their points. -/
@[expose] noncomputable def diagram : ℕ ⥤ TopCat where
  obj n := TopCat.of (finiteGrassmannian 𝕜 k n)
  map φ := TopCat.ofHom ⟨ambientInclusion (leOfHom φ), continuous_ambientInclusion _⟩
  map_id _ := TopCat.ext fun V ↦ ambientInclusion_refl V
  map_comp _ _ := TopCat.ext fun V ↦ (ambientInclusion_ambientInclusion _ _ V).symm

@[simp]
theorem diagram_map_apply {m n : ℕ} (φ : m ⟶ n) (V : finiteGrassmannian 𝕜 k m) :
    (diagram 𝕜 k).map φ V = ambientInclusion (leOfHom φ) V := (rfl)

variable (𝕜) in
/-- The infinite Grassmannian as a cocone over the finite Grassmannians. The body is exposed so
that its point is the infinite Grassmannian itself and its maps are the stage inclusions. -/
@[expose] noncomputable def cocone : Cocone (diagram 𝕜 k) where
  pt := TopCat.of (infiniteGrassmannian 𝕜 k)
  ι.app _ := TopCat.ofHom ⟨toInfinite, continuous_toInfinite⟩
  ι.naturality _ _ φ := TopCat.ext fun V ↦ toInfinite_ambientInclusion (leOfHom φ) V

@[simp]
theorem cocone_ι_app_apply (n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    ((cocone 𝕜 k).ι.app n).hom (Y := (cocone 𝕜 k).pt) V = toInfinite V := (rfl)

/-- The underlying set of the infinite Grassmannian is the colimit of the underlying sets. -/
noncomputable def isColimitForget : IsColimit ((forget TopCat).mapCocone (cocone 𝕜 k)) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun (W : infiniteGrassmannian 𝕜 k) ↦
      (exists_toInfinite_eq W).imp fun _ ⟨V, hV⟩ ↦ ⟨V, hV.symm⟩)
    fun n (V W : finiteGrassmannian 𝕜 k n) h ↦ by
      have h' : toInfinite V = toInfinite W := by
        rw [← cocone_ι_app_apply k n V, ← cocone_ι_app_apply k n W]
        exact h
      exact ⟨n, 𝟙 n, congrArg _ (toInfinite_injective h')⟩

variable (𝕜) in
/-- The infinite Grassmannian is the colimit in `TopCat` of the finite Grassmannians along
ambient stabilization. -/
noncomputable def isColimit : IsColimit (cocone 𝕜 k) :=
  Classical.choice <|
    (TopCat.nonempty_isColimit_iff_eq_coinduced _ (isColimitForget (𝕜 := 𝕜) k)).2 (by
      -- The topology instance is the supremum of the topologies coinduced by `toInfinite`;
      -- the cocone legs are these same maps, bundled as morphisms of `TopCat`.
      rfl)

/-- The infinite Grassmannian is Lindelöf whenever every finite stage is Lindelöf. -/
instance {k : ℕ} [∀ n, LindelofSpace (finiteGrassmannian 𝕜 k n)] :
    LindelofSpace (infiniteGrassmannian 𝕜 k) :=
  let _ (n : ℕ) : LindelofSpace ((diagram 𝕜 k).obj n) :=
    inferInstanceAs (LindelofSpace (finiteGrassmannian 𝕜 k n))
  TopCat.lindelofSpace_of_isColimit (F := diagram 𝕜 k) (isColimit 𝕜 k)

end Colimit

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {k : ℕ}

/-- Over the real or complex numbers, the image of a closed set of a finite stage is closed in
the infinite Grassmannian. -/
theorem isClosed_image_toInfinite {n : ℕ} {C : Set (finiteGrassmannian 𝕜 k n)} (hC : IsClosed C) :
    IsClosed (toInfinite '' C) := by
  refine isClosed_iff.2 fun m ↦ ?_
  rcases le_total m n with h | h
  · -- From a lower stage, the preimage is the preimage of `C` under the inclusion.
    convert hC.preimage (continuous_ambientInclusion h) using 1
    ext W
    simp only [mem_preimage, mem_image, ← toInfinite_ambientInclusion h W, toInfinite_inj]
    exact ⟨fun ⟨_, hV, hVW⟩ ↦ hVW ▸ hV, fun hW ↦ ⟨_, hW, rfl⟩⟩
  · -- From a higher stage, the preimage is the image of `C`, closed by compactness.
    convert (isClosedEmbedding_ambientInclusion h).isClosedMap C hC using 1
    ext W
    simp only [mem_preimage, mem_image, toInfinite_eq_toInfinite_iff h]

/-- Over the real or complex numbers, each finite Grassmannian is a closed subspace of the
infinite Grassmannian. -/
theorem _root_.TauCeti.finiteGrassmannian.isClosedEmbedding_toInfinite {n : ℕ} :
    IsClosedEmbedding (toInfinite : finiteGrassmannian 𝕜 k n → infiniteGrassmannian 𝕜 k) :=
  .of_continuous_injective_isClosedMap continuous_toInfinite toInfinite_injective
    fun _ ↦ isClosed_image_toInfinite

/-- Over `RCLike 𝕜`, the infinite Grassmannian is `T4` (normal and Hausdorff). -/
instance : T4Space (infiniteGrassmannian 𝕜 k) :=
  let _ (n : ℕ) : T4Space ((diagram 𝕜 k).obj n) :=
    inferInstanceAs (T4Space (finiteGrassmannian 𝕜 k n))
  TopCat.t4Space_of_isColimit (F := diagram 𝕜 k)
    (fun n ↦ isClosedEmbedding_ambientInclusion (Nat.le_succ n)) (isColimit 𝕜 k)

/-- Over `RCLike 𝕜`, the infinite Grassmannian is paracompact for its direct-limit topology. -/
instance : ParacompactSpace (infiniteGrassmannian 𝕜 k) :=
  paracompactSpace_of_regularSpace_lindelofSpace
end RCLike

section Map
variable {𝕜 : Type*} [Field 𝕜] {k : ℕ}
section MapAlg
variable (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
/-- An injective linear endomorphism of `ℕ →₀ 𝕜` acts on `infiniteGrassmannian 𝕜 k` by image. -/
noncomputable def map (W : infiniteGrassmannian 𝕜 k) : infiniteGrassmannian 𝕜 k :=
  ⟨W.val.map φ, by rw [rank_map_eq hφ, W.property]⟩
@[simp] theorem coe_map (W : infiniteGrassmannian 𝕜 k) : (map φ hφ W).val = W.val.map φ := (rfl)
@[simp] theorem map_id (W : infiniteGrassmannian 𝕜 k) : map LinearMap.id injective_id W = W :=
  Subtype.ext (Submodule.map_id W.val)
@[simp] theorem map_comp (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hψ : Injective ψ)
    (W : infiniteGrassmannian 𝕜 k) : map (ψ.comp φ) (hψ.comp hφ) W = map ψ hψ (map φ hφ W) :=
  Subtype.ext (Submodule.map_comp φ ψ W.val)
/-- An injective ambient linear map induces an injective map on the infinite Grassmannian. -/
theorem map_injective : Function.Injective (map (k := k) φ hφ) := fun _ _ h ↦
  Subtype.ext (Submodule.map_injective_of_injective hφ (congrArg Subtype.val h))
end MapAlg

section MapTopology
variable [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]
  (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ)
/-- Any injective `𝕜`-linear endomorphism of `ℕ →₀ 𝕜` induces a continuous self-map. -/
@[fun_prop] theorem continuous_map : Continuous (map (k := k) φ hφ) := by
  refine continuous_iff.2 fun n ↦ ?_
  obtain ⟨m, hm⟩ := Finsupp.exists_support_map_subset_range φ n
  let g := (LinearMap.pi fun j : Fin m ↦ Finsupp.lapply j.val).comp (φ.comp (coordinateInclusion n))
  have hcomp : (coordinateInclusion m).comp g = φ.comp (coordinateInclusion n) :=
    LinearMap.ext fun v ↦ coordinateInclusion_of_support_subset_range
      (hm _ (support_coordinateInclusion_subset_range n v))
  have hinj : Injective g := .of_comp (f := coordinateInclusion m) <| by
    rw [← LinearMap.coe_comp, hcomp]; exact hφ.comp (coordinateInclusion_injective n)
  refine (continuous_toInfinite.comp
    (finiteGrassmannian.continuous_map _ hinj g.continuous_on_pi)).congr fun V ↦ Subtype.ext ?_
  simp [coe_toInfinite, ← Submodule.map_comp, hcomp]
/-- `infiniteGrassmannian.map` as a `ContinuousMap` (exposed for pullback fibre reduction). -/
@[expose] noncomputable def mapContinuousMap :
    C(infiniteGrassmannian 𝕜 k, infiniteGrassmannian 𝕜 k) := ⟨map φ hφ, continuous_map φ hφ⟩
@[simp] theorem mapContinuousMap_apply (W : infiniteGrassmannian 𝕜 k) :
    mapContinuousMap φ hφ W = map φ hφ W := (rfl)
@[simp] theorem mapContinuousMap_id :
    mapContinuousMap (k := k) (LinearMap.id : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) injective_id =
      ContinuousMap.id (infiniteGrassmannian 𝕜 k) := ContinuousMap.ext map_id
@[simp] theorem mapContinuousMap_comp (ψ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hψ : Injective ψ) :
    mapContinuousMap (k := k) (ψ.comp φ) (hψ.comp hφ) =
      (mapContinuousMap ψ hψ).comp (mapContinuousMap φ hφ) :=
  ContinuousMap.ext (map_comp φ hφ ψ hψ)
end MapTopology
end Map
end infiniteGrassmannian
end TauCeti
