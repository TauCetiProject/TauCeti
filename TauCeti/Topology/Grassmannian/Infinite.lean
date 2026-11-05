/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Stabilization
public import TauCeti.LinearAlgebra.Finsupp.Supported
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Category.TopCat.Limits.Basic

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
Over the real or complex numbers, where the finite Grassmannians are compact Hausdorff, each
stage inclusion is a closed embedding and points are closed.

Over `ℝ` and `ℂ` these are the standard models `BO(k)` and `BU(k)` for classifying rank-`k` real
and complex vector bundles, and the rank-one case is the infinite projective space `ℝP∞` or
`ℂP∞`; the tautological bundle and the classification theorem are not part of this file.
The basepoint in rank `k` is the span of the first `k` coordinate vectors; in rank zero it is the
only point.

The construction of the infinite Grassmannian as the union of the finite ones with the direct
limit topology follows J. Milnor and J. Stasheff, *Characteristic Classes*, §5.
-/

public section

open Set Topology CategoryTheory Limits

namespace TauCeti

variable (𝕜 : Type*) [Field 𝕜] (k : ℕ)

/-- The infinite Grassmannian of `k`-dimensional subspaces of the countable coordinate space
`ℕ →₀ 𝕜`. The rank is a cardinal, so every point is a finite-dimensional subspace, including in
rank zero. -/
abbrev infiniteGrassmannian : Type _ :=
  {V : Submodule 𝕜 (ℕ →₀ 𝕜) // Module.rank 𝕜 V = k}

namespace infiniteGrassmannian

variable {𝕜}

/-- The coordinate inclusion `𝕜^n → ℕ →₀ 𝕜`, sending the `i`-th coordinate vector to the
`i`-th coordinate vector. -/
noncomputable def coordinateInclusion (n : ℕ) : (Fin n → 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Finsupp.lmapDomain 𝕜 𝕜 Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin n)).symm.toLinearMap

@[simp]
theorem coordinateInclusion_single (n : ℕ) (i : Fin n) (a : 𝕜) :
    coordinateInclusion n (Pi.single i a) = Finsupp.single (i : ℕ) a := by
  simp [coordinateInclusion]

@[simp]
theorem coordinateInclusion_apply_val {n : ℕ} (v : Fin n → 𝕜) (i : Fin n) :
    coordinateInclusion n v i = v i := by
  simp [coordinateInclusion, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

theorem coordinateInclusion_apply_of_le {n : ℕ} (v : Fin n → 𝕜) {i : ℕ} (hi : n ≤ i) :
    coordinateInclusion n v i = 0 := by
  simp only [coordinateInclusion, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simpa [Fin.range_val] using hi)

theorem coordinateInclusion_injective (n : ℕ) :
    Function.Injective (coordinateInclusion (𝕜 := 𝕜) n) :=
  (Finsupp.mapDomain_injective Fin.val_injective).comp
    (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin n)).symm.injective

/-- The image of the coordinate inclusion of `𝕜^n` consists of the finitely supported functions
vanishing from coordinate `n` on. -/
theorem range_coordinateInclusion (n : ℕ) :
    LinearMap.range (coordinateInclusion (𝕜 := 𝕜) n) = Finsupp.supported 𝕜 𝕜 (Iio n) := by
  rw [coordinateInclusion, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    LinearMap.range_eq_map, ← Finsupp.supported_univ, Finsupp.lmapDomain_supported, image_univ,
    Fin.range_val]

/-- The coordinate inclusions are compatible with the inclusions `𝕜^m → 𝕜^n` onto the first
coordinates. -/
@[simp]
theorem coordinateInclusion_comp_extendByZero_castLE {m n : ℕ} (h : m ≤ n) :
    coordinateInclusion (𝕜 := 𝕜) n ∘ₗ Function.ExtendByZero.linearMap 𝕜 𝕜 (Fin.castLE h) =
      coordinateInclusion m := by
  refine LinearMap.pi_ext fun i a ↦ ?_
  simp [Function.ExtendByZero.linearMap_single 𝕜 (Fin.castLE_injective h)]

end infiniteGrassmannian

namespace finiteGrassmannian

open infiniteGrassmannian

variable {𝕜 k} {n : ℕ}

/-- A `k`-dimensional subspace of `𝕜^n`, viewed in `ℕ →₀ 𝕜` through the coordinate inclusion. -/
noncomputable def toInfinite (V : finiteGrassmannian 𝕜 k n) : infiniteGrassmannian 𝕜 k :=
  ⟨V.1.map (coordinateInclusion n), by
    rw [rank_map_eq (coordinateInclusion_injective n), ← Module.finrank_eq_rank, V.2]⟩

theorem coe_toInfinite (V : finiteGrassmannian 𝕜 k n) :
    (toInfinite V).1 = V.1.map (coordinateInclusion n) := (rfl)

theorem toInfinite_injective : Function.Injective (toInfinite : finiteGrassmannian 𝕜 k n → _) :=
  fun _ _ h ↦ Subtype.ext
    (Submodule.map_injective_of_injective (coordinateInclusion_injective n) congr($h.1))

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
      W.1 ≤ Finsupp.supported 𝕜 𝕜 (Iio n) := by
  constructor
  · rintro ⟨V, rfl⟩
    rw [coe_toInfinite, ← range_coordinateInclusion]
    exact LinearMap.map_le_range
  · intro hW
    rw [← range_coordinateInclusion] at hW
    have hmap : (W.1.comap (coordinateInclusion n)).map (coordinateInclusion n) = W.1 :=
      Submodule.map_comap_eq_of_le hW
    have hrank : Module.rank 𝕜 (W.1.comap (coordinateInclusion n)) = k := by
      rw [← rank_map_eq (coordinateInclusion_injective n), hmap, W.2]
    exact ⟨⟨_, Module.finrank_eq_of_rank_eq hrank⟩, Subtype.ext hmap⟩

end finiteGrassmannian

namespace infiniteGrassmannian

open finiteGrassmannian

variable {𝕜 k}

/-- Every point of the infinite Grassmannian comes from some finite stage. -/
theorem exists_toInfinite_eq (W : infiniteGrassmannian 𝕜 k) :
    ∃ (n : ℕ) (V : finiteGrassmannian 𝕜 k n), toInfinite V = W := by
  have : FiniteDimensional 𝕜 W.1 := .of_rank_eq_nat W.2
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
theorem coe_basepoint : (basepoint 𝕜 k).1 = Finsupp.supported 𝕜 𝕜 (Iio k) := by
  rw [basepoint, coe_toInfinite, Submodule.map_top, range_coordinateInclusion]

noncomputable instance : Inhabited (infiniteGrassmannian 𝕜 k) :=
  ⟨basepoint 𝕜 k⟩

/-- In rank zero the only point is the zero subspace. -/
noncomputable instance : Unique (infiniteGrassmannian 𝕜 0) where
  default := basepoint 𝕜 0
  uniq W := Subtype.ext <| by
    have hW : W.1 = ⊥ := Submodule.rank_eq_zero.1 (by simpa using W.2)
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

theorem isOpen_iff {U : Set (infiniteGrassmannian 𝕜 k)} :
    IsOpen U ↔ ∀ n, IsOpen ((toInfinite : finiteGrassmannian 𝕜 k n → _) ⁻¹' U) := by
  rw [isOpen_iSup_iff]
  rfl

theorem isClosed_iff {C : Set (infiniteGrassmannian 𝕜 k)} :
    IsClosed C ↔ ∀ n, IsClosed ((toInfinite : finiteGrassmannian 𝕜 k n → _) ⁻¹' C) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- A map out of the infinite Grassmannian is continuous exactly when it is continuous on every
finite stage. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : infiniteGrassmannian 𝕜 k → X} :
    Continuous f ↔ ∀ n, Continuous (f ∘ (toInfinite : finiteGrassmannian 𝕜 k n → _)) := by
  simp only [continuous_def, isOpen_iff, preimage_comp]
  exact ⟨fun h n U hU ↦ h U hU n, fun h U hU n ↦ h n U hU⟩

end Topology

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

theorem cocone_ι_app_apply (n : ℕ) (V : finiteGrassmannian 𝕜 k n) :
    (cocone 𝕜 k).ι.app n V = toInfinite V := (rfl)

/-- The underlying set of the infinite Grassmannian is the colimit of the underlying sets. -/
noncomputable def isColimitForget : IsColimit ((forget TopCat).mapCocone (cocone 𝕜 k)) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun (W : infiniteGrassmannian 𝕜 k) ↦
      (exists_toInfinite_eq W).imp fun _ ⟨V, hV⟩ ↦ ⟨V, hV.symm⟩)
    fun n (_ _ : finiteGrassmannian 𝕜 k n) h ↦
      ⟨n, 𝟙 n, congrArg _ (toInfinite_injective (n := n) h)⟩

variable (𝕜) in
/-- The infinite Grassmannian is the colimit in `TopCat` of the finite Grassmannians along
ambient stabilization. -/
noncomputable def isColimit : IsColimit (cocone 𝕜 k) :=
  Classical.choice <|
    (TopCat.nonempty_isColimit_iff_eq_coinduced _ (isColimitForget (𝕜 := 𝕜) k)).2 rfl

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
    exact ⟨fun ⟨V, hV, hVW⟩ ↦ hVW ▸ hV, fun hW ↦ ⟨_, hW, rfl⟩⟩
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

instance : T1Space (infiniteGrassmannian 𝕜 k) where
  t1 W := by
    obtain ⟨n, V, rfl⟩ := exists_toInfinite_eq W
    simpa using isClosed_image_toInfinite (isClosed_singleton (x := V))

end RCLike

end infiniteGrassmannian

end TauCeti
