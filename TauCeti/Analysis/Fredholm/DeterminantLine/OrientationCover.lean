/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Basic
public import TauCeti.Analysis.Fredholm.DeterminantLine.Bundle
public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
public import TauCeti.LinearAlgebra.Orientation.RankOne
public import TauCeti.Topology.VectorBundle.Orientation.Cover
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Analysis.Convex.PathConnected
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.LinearAlgebra.Ray

/-!
# The orientation double cover of the Fredholm determinant line bundle

The determinant lines of Fredholm operators `T : E →L[ℝ] F` form a real line bundle
`TauCeti.FredholmDetLine ℝ E F` over `{T : E →L[ℝ] F // T.IsFredholm}`
(`TauCeti.FredholmDetLine.vectorBundle`). Since each fibre has dimension one, its `ι`-indexed
orientations (`[Unique ι]`) correspond to rays in `(T.1 : E →ₗ[ℝ] F).detLine`
(`TauCeti.FredholmDetLine.orientationEquivRay`), identifying the fibres of
`TauCeti.VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι` with
`Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine` (`TauCeti.FredholmDetLine.orientationCoverFiberEquiv`) and
intertwining the deck involution with ray negation.

In any kernel chart `TauCeti.FredholmDetLine.trivialization D₂ q`, sheet equality is ray equality
under `ContinuousLinearMap.detLineChartEquiv`
(`TauCeti.FredholmDetLine.mapOrientation_trivialization_eq_iff`), so coherence
(`TauCeti.IsDetLineCoherentOn`) is equivalent to continuity of the lift into the orientation double
cover (`TauCeti.isDetLineCoherentOn_iff_continuous_orientationCoverMk`), identifying orientations of
`f *ᵖ FredholmDetLine ℝ E F` with coherent ray families
(`TauCeti.FredholmDetLine.pullbackOrientationEquiv`). Because the cover projection is a covering map
(`TauCeti.FredholmDetLine.isCoveringMap_orientationCover_proj`),
`IsCoveringMap.existsUnique_continuousMap_lifts` extends any nonzero determinant vector at `x₀ ∈ s`
over simply-connected locally path-connected sets
(`TauCeti.exists_isDetLineCoherentOn_of_simplyConnectedSpace`) and convex sets
(`TauCeti.exists_isDetLineCoherentOn_of_convex`).
-/

public section

noncomputable section

open Bundle ContinuousLinearMap Filter Module Set TensorProduct Topology

namespace TauCeti

namespace FredholmDetLine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Unique ι]

/-- Canonical equivalence between `ι`-indexed orientations of `FredholmDetLine ℝ E F T` and rays in
`(T.val : E →ₗ[ℝ] F).detLine`. -/
def orientationEquivRay (T : {T : E →L[ℝ] F // T.IsFredholm}) :
    Orientation ℝ (FredholmDetLine ℝ E F T) ι ≃ Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine :=
  (Orientation.equivRay (ι := ι) finrank_eq_one).trans (Module.Ray.map (linearEquiv T))

theorem orientationEquivRay_def (T : {T : E →L[ℝ] F // T.IsFredholm}) :
    orientationEquivRay (ι := ι) T =
      (Orientation.equivRay (ι := ι) finrank_eq_one).trans (Module.Ray.map (linearEquiv T)) := (rfl)

@[simp]
theorem orientationEquivRay_neg (T : {T : E →L[ℝ] F // T.IsFredholm})
    (o : Orientation ℝ (FredholmDetLine ℝ E F T) ι) :
    orientationEquivRay (ι := ι) T (-o) = -orientationEquivRay (ι := ι) T o := by
  let : AddCommGroup (T.val : E →ₗ[ℝ] F).detLine := TensorProduct.addCommGroup
  rw [orientationEquivRay_def, Equiv.trans_apply, Equiv.trans_apply, Orientation.equivRay_neg]
  exact Module.Ray.map_neg (linearEquiv T) _

@[simp]
theorem orientationEquivRay_symm_neg (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) :
    (orientationEquivRay (ι := ι) T).symm (-r) = -(orientationEquivRay (ι := ι) T).symm r :=
  (orientationEquivRay (ι := ι) T).injective <| by
    rw [Equiv.apply_symm_apply, orientationEquivRay_neg, Equiv.apply_symm_apply]

@[simp]
theorem orientationEquivRay_units_smul (T : {T : E →L[ℝ] F // T.IsFredholm})
    (u : ℝˣ) (o : Orientation ℝ (FredholmDetLine ℝ E F T) ι) :
    orientationEquivRay (ι := ι) T (u • o) = u • orientationEquivRay (ι := ι) T o := by
  let : AddCommGroup (T.val : E →ₗ[ℝ] F).detLine := TensorProduct.addCommGroup
  exact Module.Ray.units_smul_of_map_neg (orientationEquivRay_neg T) u o

@[simp]
theorem orientationEquivRay_symm_units_smul (T : {T : E →L[ℝ] F // T.IsFredholm})
    (u : ℝˣ) (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) :
    (orientationEquivRay (ι := ι) T).symm (u • r) = u • (orientationEquivRay (ι := ι) T).symm r :=
  (orientationEquivRay (ι := ι) T).injective <| by
    rw [Equiv.apply_symm_apply, orientationEquivRay_units_smul, Equiv.apply_symm_apply]

@[simp]
theorem orientationEquivRay_reindex {ι' : Type*} [Unique ι']
    (T : {T : E →L[ℝ] F // T.IsFredholm}) (σ : ι ≃ ι')
    (o : Orientation ℝ (FredholmDetLine ℝ E F T) ι) :
    orientationEquivRay (ι := ι') T (Orientation.reindex ℝ (FredholmDetLine ℝ E F T) σ o) =
      orientationEquivRay (ι := ι) T o := by
  rw [orientationEquivRay_def, orientationEquivRay_def, Equiv.trans_apply, Equiv.trans_apply,
    Orientation.equivRay_reindex]

@[simp]
theorem reindex_orientationEquivRay_symm {ι' : Type*} [Unique ι']
    (T : {T : E →L[ℝ] F // T.IsFredholm}) (σ : ι ≃ ι')
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) :
    Orientation.reindex ℝ (FredholmDetLine ℝ E F T) σ ((orientationEquivRay (ι := ι) T).symm r) =
      (orientationEquivRay (ι := ι') T).symm r :=
  (orientationEquivRay (ι := ι') T).injective <| by
    rw [orientationEquivRay_reindex, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- For a singleton basis `b` of `FredholmDetLine ℝ E F T`, `orientationEquivRay` sends
`b.orientation` to the ray of `linearEquiv T (b default)`. -/
@[simp]
theorem orientationEquivRay_basis_orientation [Fintype ι] [DecidableEq ι]
    (T : {T : E →L[ℝ] F // T.IsFredholm}) (b : Basis ι ℝ (FredholmDetLine ℝ E F T)) :
    orientationEquivRay (ι := ι) T b.orientation =
      rayOfNeZero ℝ (linearEquiv T (b default))
        ((linearEquiv T).map_ne_zero_iff.2 (b.ne_zero default)) := by
  rw [orientationEquivRay_def, Equiv.trans_apply, Orientation.equivRay_basis_orientation,
    Module.Ray.map_apply]

variable (ι) in
/-- Point of the orientation double cover of `FredholmDetLine ℝ E F` over `T` determined by `r`. -/
def orientationCoverMk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) :
    VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι :=
  ⟨T, (orientationEquivRay (ι := ι) T).symm r⟩

theorem orientationCoverMk_def (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) :
    orientationCoverMk ι T r = ⟨T, (orientationEquivRay (ι := ι) T).symm r⟩ := (rfl)

@[simp]
theorem proj_orientationCoverMk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) : (orientationCoverMk ι T r).proj = T := (rfl)

@[simp]
theorem orientationCoverMk_inj {T : {T : E →L[ℝ] F // T.IsFredholm}}
    {r₁ r₂ : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine} :
    orientationCoverMk ι T r₁ = orientationCoverMk ι T r₂ ↔ r₁ = r₂ := by
  rw [orientationCoverMk_def, orientationCoverMk_def, VectorBundleOrientationCover.mk_eq_mk_iff,
    Equiv.apply_eq_iff_eq]

variable (ι) in
/-- Canonical equivalence between the fibre of the orientation double cover over `T` and
`Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine`. -/
def orientationCoverFiberEquiv (T : {T : E →L[ℝ] F // T.IsFredholm}) :
    ((VectorBundleOrientationCover.proj :
        VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι → _) ⁻¹' {T}) ≃
      Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine :=
  (VectorBundleOrientationCover.fiberEquiv ℝ (FredholmDetLine ℝ E F) ι T).trans
    (orientationEquivRay (ι := ι) T)

theorem orientationCoverFiberEquiv_def (T : {T : E →L[ℝ] F // T.IsFredholm}) :
    orientationCoverFiberEquiv ι T =
      (VectorBundleOrientationCover.fiberEquiv ℝ (FredholmDetLine ℝ E F) ι T).trans
        (orientationEquivRay (ι := ι) T) := (rfl)

@[simp]
theorem orientationCoverFiberEquiv_apply_mk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (o : Orientation ℝ (FredholmDetLine ℝ E F T) ι)
    {h : (⟨T, o⟩ : VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι) ∈
      VectorBundleOrientationCover.proj ⁻¹' {T}} :
    orientationCoverFiberEquiv ι T ⟨⟨T, o⟩, h⟩ = orientationEquivRay (ι := ι) T o := by
  obtain rfl : h = rfl := Subsingleton.elim h rfl
  simp [orientationCoverFiberEquiv_def]

-- Companion for equality-typed subtype proofs (`rfl : T = T` is not reducible to `∈ proj ⁻¹' {T}`).
@[simp]
theorem orientationCoverFiberEquiv_apply_mk' (T : {T : E →L[ℝ] F // T.IsFredholm})
    (o : Orientation ℝ (FredholmDetLine ℝ E F T) ι)
    {h : (⟨T, o⟩ : VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι).proj = T} :
    orientationCoverFiberEquiv ι T
      (⟨⟨T, o⟩, h⟩ : (VectorBundleOrientationCover.proj :
        VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι → _) ⁻¹' {T}) =
      orientationEquivRay (ι := ι) T o :=
  orientationCoverFiberEquiv_apply_mk T o

@[simp]
theorem orientationCoverFiberEquiv_symm_apply (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) :
    (orientationCoverFiberEquiv ι T).symm r =
      ⟨orientationCoverMk ι T r, proj_orientationCoverMk T r⟩ := by
  simp [orientationCoverFiberEquiv_def, orientationCoverMk_def]

@[simp]
theorem orientationCoverFiberEquiv_mk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine)
    {h : orientationCoverMk ι T r ∈ VectorBundleOrientationCover.proj ⁻¹' {T}} :
    orientationCoverFiberEquiv ι T ⟨orientationCoverMk ι T r, h⟩ = r := by
  have hsub : (⟨orientationCoverMk ι T r, h⟩ :
      (VectorBundleOrientationCover.proj :
        VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι → _) ⁻¹' {T}) =
      (orientationCoverFiberEquiv ι T).symm r :=
    Subtype.ext (by rw [orientationCoverFiberEquiv_symm_apply])
  rw [hsub, Equiv.apply_symm_apply]

@[simp]
theorem orientationCoverFiberEquiv_mk' (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) {h : (orientationCoverMk ι T r).proj = T} :
    orientationCoverFiberEquiv ι T
      (⟨orientationCoverMk ι T r, h⟩ : (VectorBundleOrientationCover.proj :
        VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι → _) ⁻¹' {T}) = r :=
  orientationCoverFiberEquiv_mk T r

variable [CompleteSpace E] [CompleteSpace F]

/-- The deck involution of the orientation double cover negates the determinant-line ray. -/
@[simp]
theorem deck_orientationCoverMk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) :
    VectorBundleOrientationCover.deck (orientationCoverMk ι T r) =
      orientationCoverMk ι T (-r) := by
  rw [orientationCoverMk_def, orientationCoverMk_def, VectorBundleOrientationCover.deck_apply]
  exact VectorBundleOrientationCover.mk_eq_mk_iff.2 (orientationEquivRay_symm_neg T r).symm

/-- The projection of the orientation double cover of `FredholmDetLine ℝ E F` is a covering map. -/
theorem isCoveringMap_orientationCover_proj :
    IsCoveringMap (VectorBundleOrientationCover.proj :
      VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι →
        {T : E →L[ℝ] F // T.IsFredholm}) := by
  let : Fintype ι := Fintype.ofFinite ι
  exact VectorBundleOrientationCover.isCoveringMap_proj
    (Fintype.card_unique.trans (Module.finrank_self ℝ).symm)

section Trivialization

variable {n m : ℕ} (D₂ : (Fin n → ℝ) →L[ℝ] F) (q : E × (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))

/-- Two determinant-line rays over operators in the base set of `trivialization D₂ q` are read as
the same orientation of `ℝ` if and only if `detLineChartEquiv` maps them to the same ray. -/
theorem mapOrientation_trivialization_eq_iff (T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm})
    (h₁ : ((T₁.val.coprod D₂).prod q).IsInvertible) (h₂ : ((T₂.val.coprod D₂).prod q).IsInvertible)
    (r₁ : Module.Ray ℝ (T₁.val : E →ₗ[ℝ] F).detLine)
    (r₂ : Module.Ray ℝ (T₂.val : E →ₗ[ℝ] F).detLine) :
    (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h₁)
        ((orientationEquivRay (ι := ι) T₁).symm r₁) =
      (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h₂)
        ((orientationEquivRay (ι := ι) T₂).symm r₂) ↔
      Module.Ray.map (detLineChartEquiv T₁.val D₂ q h₁) r₁ =
        Module.Ray.map (detLineChartEquiv T₂.val D₂ q h₂) r₂ := by
  let L : (detLine ℝ (Fin m → ℝ) ⊗[ℝ] Dual ℝ (detLine ℝ (Fin n → ℝ))) ≃ₗ[ℝ] ℝ :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq, TauCeti.finrank_detLine,
        TauCeti.finrank_detLine, Module.finrank_self])
  have hcoord (T : {T : E →L[ℝ] F // T.IsFredholm}) (h : ((T.val.coprod D₂).prod q).IsInvertible)
      (r : Module.Ray ℝ (T.val : E →ₗ[ℝ] F).detLine) :
      (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h)
          ((orientationEquivRay (ι := ι) T).symm r) =
        Orientation.ringRayEquiv ι (Module.Ray.map L (Module.Ray.map
          (detLineChartEquiv T.val D₂ q h) r)) := by
    induction r using Module.Ray.ind with | h v hv =>
    refine ((trivialization D₂ q).mapOrientation_apply _ _).trans ?_
    rw [linearEquivAt_trivialization D₂ q h]
    simp only [orientationEquivRay_def, Equiv.symm_trans_apply, Module.Ray.map_symm,
      Module.Ray.map_apply, Orientation.map_equivRay_symm, Orientation.equivRay_self,
      Equiv.symm_symm]
    congr 1
    rw [ray_eq_iff, chartCoord_def]
    simpa only [L, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using SameRay.rfl
  exact ⟨fun h ↦ (Module.Ray.map L).injective ((Orientation.ringRayEquiv ι).injective
      ((hcoord T₁ h₁ r₁).symm.trans (h.trans (hcoord T₂ h₂ r₂)))),
    fun h ↦ (hcoord T₁ h₁ r₁).trans
      ((congrArg (Orientation.ringRayEquiv ι) (congrArg (Module.Ray.map L) h)).trans
        (hcoord T₂ h₂ r₂).symm)⟩

/-- Specialization of `mapOrientation_trivialization_eq_iff` to rays of nonzero vectors. -/
theorem mapOrientation_trivialization_rayOfNeZero_eq_iff
    (T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm})
    (h₁ : ((T₁.val.coprod D₂).prod q).IsInvertible) (h₂ : ((T₂.val.coprod D₂).prod q).IsInvertible)
    {v₁ : (T₁.val : E →ₗ[ℝ] F).detLine} (hv₁ : v₁ ≠ 0)
    {v₂ : (T₂.val : E →ₗ[ℝ] F).detLine} (hv₂ : v₂ ≠ 0) :
    (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h₁)
        ((orientationEquivRay (ι := ι) T₁).symm (rayOfNeZero ℝ v₁ hv₁)) =
      (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h₂)
        ((orientationEquivRay (ι := ι) T₂).symm (rayOfNeZero ℝ v₂ hv₂)) ↔
      SameRay ℝ (detLineChartEquiv T₁.val D₂ q h₁ v₁) (detLineChartEquiv T₂.val D₂ q h₂ v₂) :=
  (mapOrientation_trivialization_eq_iff D₂ q T₁ T₂ h₁ h₂ _ _).trans (ray_eq_iff _ _)

end Trivialization

end FredholmDetLine

section CoherenceEquivalence

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace X] {ι : Type*} [Unique ι]

/-- A coherent determinant-line family `v` along a continuous Fredholm family `T` on `s` induces a
continuous lift over `s` into `VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι`. -/
theorem IsDetLineCoherentOn.continuous_orientationCoverMk {T : X → E →L[ℝ] F}
    {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} (hv : IsDetLineCoherentOn T v s)
    (hT : ContinuousOn T s) (hF : ∀ x ∈ s, (T x).IsFredholm) :
    Continuous fun x : s ↦ FredholmDetLine.orientationCoverMk ι
      ⟨T x.val, hF x.val x.property⟩ (rayOfNeZero ℝ (v x.val) (hv.ne_zero x.property)) := by
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = finrank ℝ ℝ :=
    Fintype.card_unique.trans (Module.finrank_self ℝ).symm
  let f : s → {T : E →L[ℝ] F // T.IsFredholm} := fun x ↦ ⟨T x.val, hF x.val x.property⟩
  have hf : Continuous f := (continuousOn_iff_continuous_domRestrict.1 hT).subtype_mk _
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  -- Read `v` in an atlas kernel chart around `f x₀`; coherence keeps the sheet constant locally.
  obtain ⟨n, m, D₂, q, hx₀⟩ := (f x₀).property.exists_isInvertible_prod_coprod
  have hx₀e : f x₀ ∈ (FredholmDetLine.trivialization D₂ q).baseSet :=
    (FredholmDetLine.mem_trivialization_baseSet_iff D₂ q).2 hx₀
  let o₀ := (FredholmDetLine.trivialization D₂ q).mapOrientation ι hx₀e
    ((FredholmDetLine.orientationEquivRay (ι := ι) (f x₀)).symm
      (rayOfNeZero ℝ (v x₀.val) (hv.ne_zero x₀.property)))
  have htend : Tendsto (Subtype.val : s → X) (𝓝 x₀) (𝓝[s] x₀.val) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      continuous_subtypeVal.continuousAt (Eventually.of_forall fun y ↦ y.property)
  obtain ⟨W, hWsub, hWopen, hx₀W⟩ := mem_nhds_iff.1 ((htend.eventually
    ((isDetLineCoherentOn_iff.1 hv x₀.val x₀.property).eventually_sameRay
      (hT x₀.val x₀.property) hx₀)).and
    (((FredholmDetLine.trivialization D₂ q).open_baseSet.preimage hf).mem_nhds hx₀e))
  have hgW : ContinuousOn (fun x : s ↦ FredholmDetLine.orientationCoverMk ι (f x)
      (rayOfNeZero ℝ (v x.val) (hv.ne_zero x.property))) W := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine ((VectorBundleOrientationCover.continuous_mk_mapOrientation_symm hcard
      (FredholmDetLine.trivialization D₂ q) o₀).comp
      ((hf.comp continuous_subtypeVal).subtype_mk fun w : W ↦ (hWsub w.property).2)).congr
        fun w ↦ ?_
    obtain ⟨⟨hy', hsr⟩, hwU⟩ := hWsub w.property
    exact congrArg (VectorBundleOrientationCover.mk (f w.val))
      ((Equiv.symm_apply_eq ((FredholmDetLine.trivialization D₂ q).mapOrientation ι hwU)).2
        (((FredholmDetLine.mapOrientation_trivialization_rayOfNeZero_eq_iff D₂ q (f w.val) (f x₀)
          hy' hx₀ (hv.ne_zero w.val.property) (hv.ne_zero x₀.property)).2 hsr).symm))
  exact hgW.continuousAt (hWopen.mem_nhds hx₀W)

/-- Conversely, a nowhere-zero determinant-line family `v` over `s` whose lift into
`VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι` is continuous is coherent on `s`. -/
theorem isDetLineCoherentOn_of_continuous_orientationCoverMk {T : X → E →L[ℝ] F}
    {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, (T x).IsFredholm) (hv0 : ∀ x ∈ s, v x ≠ 0)
    (hg : Continuous fun x : s ↦ FredholmDetLine.orientationCoverMk ι
      ⟨T x.val, hF x.val x.property⟩ (rayOfNeZero ℝ (v x.val) (hv0 x.val x.property))) :
    IsDetLineCoherentOn T v s := by
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = finrank ℝ ℝ :=
    Fintype.card_unique.trans (Module.finrank_self ℝ).symm
  let f : s → {T : E →L[ℝ] F // T.IsFredholm} := fun x ↦ ⟨T x.val, hF x.val x.property⟩
  rw [isDetLineCoherentOn_iff]
  intro x₀ hx₀s
  let p₀ : s := ⟨x₀, hx₀s⟩
  obtain ⟨n, m, D₂, q, hx₀⟩ := (hF x₀ hx₀s).exists_isInvertible_prod_coprod
  have hx₀e : f p₀ ∈ (FredholmDetLine.trivialization D₂ q).baseSet :=
    (FredholmDetLine.mem_trivialization_baseSet_iff D₂ q).2 hx₀
  let o₀ := (FredholmDetLine.trivialization D₂ q).mapOrientation ι hx₀e
    ((FredholmDetLine.orientationEquivRay (ι := ι) (f p₀)).symm
      (rayOfNeZero ℝ (v x₀) (hv0 x₀ hx₀s)))
  have hsheet := hg.continuousAt.preimage_mem_nhds
    ((VectorBundleOrientationCover.isOpen_sheet hcard (FredholmDetLine.trivialization D₂ q)
      o₀).mem_nhds (VectorBundleOrientationCover.mem_sheet_iff.2 ⟨hx₀e, rfl⟩))
  rw [nhds_subtype_eq_comap] at hsheet
  obtain ⟨V, hV, hVs⟩ := Filter.mem_comap.1 hsheet
  refine isDetLineCoherentWithinAt_of_eventually_sameRay (hT x₀ hx₀s) (hF x₀ hx₀s) (hv0 x₀ hx₀s)
    hx₀ ?_
  filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with y hyV hys
  have hy_mem : (⟨y, hys⟩ : s) ∈ Subtype.val ⁻¹' V := hyV
  obtain ⟨hye, hyo⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 (hVs hy_mem)
  have hy' := (FredholmDetLine.mem_trivialization_baseSet_iff D₂ q).1 hye
  exact ⟨hy', (FredholmDetLine.mapOrientation_trivialization_rayOfNeZero_eq_iff D₂ q
    (f ⟨y, hys⟩) (f p₀) hy' hx₀ (hv0 y hys) (hv0 x₀ hx₀s)).1 hyo⟩

/-- **Coherence via the orientation double cover.** For `T : X → E →L[ℝ] F` continuous and Fredholm
on `s : Set X`, `v` is coherent on `s` iff `v` is nowhere zero on `s` and its lift over `s` into
`VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι` is continuous. -/
theorem isDetLineCoherentOn_iff_continuous_orientationCoverMk {T : X → E →L[ℝ] F}
    {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, (T x).IsFredholm) :
    IsDetLineCoherentOn T v s ↔ ∃ hv : ∀ x ∈ s, v x ≠ 0,
      Continuous fun x : s ↦ FredholmDetLine.orientationCoverMk ι
        ⟨T x.val, hF x.val x.property⟩ (rayOfNeZero ℝ (v x.val) (hv x.val x.property)) :=
  ⟨fun hv ↦ ⟨fun _ hx ↦ hv.ne_zero hx, hv.continuous_orientationCoverMk hT hF⟩,
    fun ⟨hv, hg⟩ ↦ isDetLineCoherentOn_of_continuous_orientationCoverMk hT hF hv hg⟩

variable (ι) in
/-- **Bundle orientations versus coherent ray families.** Bundle orientations of
`f *ᵖ (FredholmDetLine ℝ E F)` correspond to families of determinant-line rays whose representative
vectors are coherent on `univ`. -/
def FredholmDetLine.pullbackOrientationEquiv (f : C(X, {T : E →L[ℝ] F // T.IsFredholm})) :
    VectorBundleOrientation ℝ ((⇑f) *ᵖ (FredholmDetLine ℝ E F)) ι ≃
      {r : ∀ x, Module.Ray ℝ ((f x).val : E →ₗ[ℝ] F).detLine //
        IsDetLineCoherentOn (fun x ↦ (f x).val) (fun x ↦ (r x).someVector) univ} where
  toFun o := ⟨fun x ↦ FredholmDetLine.orientationEquivRay (ι := ι) (f x) (o x), by
    let : Fintype ι := Fintype.ofFinite ι
    have hcard : Fintype.card ι = finrank ℝ ℝ :=
      Fintype.card_unique.trans (Module.finrank_self ℝ).symm
    have hT : ContinuousOn (fun x ↦ (f x).val) univ :=
      (continuous_subtypeVal.comp f.continuous).continuousOn
    rw [isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := ι) hT
      (fun x _ ↦ (f x).property)]
    refine ⟨fun _ _ ↦ (_ : Module.Ray ℝ _).someVector_ne_zero,
      ((o.continuous_mk_cover_pullback f hcard).comp continuous_subtypeVal).congr fun x ↦ ?_⟩
    refine congrArg (VectorBundleOrientationCover.mk (f x.val)) ?_
    rw [Module.Ray.someVector_ray]
    exact ((FredholmDetLine.orientationEquivRay (ι := ι) (f x.val)).symm_apply_apply
      (o x.val)).symm⟩
  invFun r := VectorBundleOrientation.ofContinuousPullback f
    (fun x ↦ (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).symm (r.val x)) (by
      have hT : ContinuousOn (fun x ↦ (f x).val) univ :=
        (continuous_subtypeVal.comp f.continuous).continuousOn
      obtain ⟨hv, hg⟩ := (isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := ι) hT
        (fun x _ ↦ (f x).property)).1 r.property
      refine (hg.comp (continuous_id.subtype_mk fun _ ↦ mem_univ _)).congr fun x ↦ ?_
      exact congrArg (VectorBundleOrientationCover.mk (f x))
        (congrArg (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).symm
          (r.val x).someVector_ray))
  left_inv o := by
    ext x
    simp only [VectorBundleOrientation.ofContinuousPullback_apply]
    exact (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).symm_apply_apply (o x)
  right_inv r := by
    ext x
    simp only [VectorBundleOrientation.ofContinuousPullback_apply]
    exact (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).apply_symm_apply (r.val x)

@[simp]
theorem FredholmDetLine.pullbackOrientationEquiv_apply
    (f : C(X, {T : E →L[ℝ] F // T.IsFredholm}))
    (o : VectorBundleOrientation ℝ ((⇑f) *ᵖ (FredholmDetLine ℝ E F)) ι) (x : X) :
    (FredholmDetLine.pullbackOrientationEquiv ι f o).val x =
      FredholmDetLine.orientationEquivRay (ι := ι) (f x) (o x) := (rfl)

@[simp]
theorem FredholmDetLine.pullbackOrientationEquiv_symm_apply
    (f : C(X, {T : E →L[ℝ] F // T.IsFredholm}))
    (r : {r : ∀ x, Module.Ray ℝ ((f x).val : E →ₗ[ℝ] F).detLine //
      IsDetLineCoherentOn (fun x ↦ (f x).val) (fun x ↦ (r x).someVector) univ}) (x : X) :
    (FredholmDetLine.pullbackOrientationEquiv ι f).symm r x =
      (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).symm (r.val x) :=
  VectorBundleOrientation.ofContinuousPullback_apply f _ _ x

end CoherenceEquivalence

section Lifting

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Existence of coherent families over simply-connected parameter sets.** Every nonzero
determinant vector `v₀` at `x₀ ∈ s` extends to a coherent family on any simply-connected, locally
path-connected `s : Set X`. -/
theorem exists_isDetLineCoherentOn_of_simplyConnectedSpace [TopologicalSpace X] {s : Set X}
    [SimplyConnectedSpace s] [LocallyPathConnectedSpace s] {T : X → E →L[ℝ] F}
    (hT : ContinuousOn T s) (hF : ∀ x ∈ s, (T x).IsFredholm) {x₀ : X} (hx₀ : x₀ ∈ s)
    {v₀ : (T x₀ : E →ₗ[ℝ] F).detLine} (hv₀ : v₀ ≠ 0) :
    ∃ v : ∀ x, (T x : E →ₗ[ℝ] F).detLine, v x₀ = v₀ ∧ IsDetLineCoherentOn T v s := by
  let f : C(s, {T : E →L[ℝ] F // T.IsFredholm}) :=
    ⟨fun x ↦ ⟨T x.val, hF x.val x.property⟩,
      (continuousOn_iff_continuous_domRestrict.1 hT).subtype_mk _⟩
  let p₀ := FredholmDetLine.orientationCoverMk (Fin 1) (f ⟨x₀, hx₀⟩) (rayOfNeZero ℝ v₀ hv₀)
  obtain ⟨L, ⟨hL₀, hLproj⟩, -⟩ :=
    (FredholmDetLine.isCoveringMap_orientationCover_proj (E := E) (F := F)
      (ι := Fin 1)).existsUnique_continuousMap_lifts f ⟨x₀, hx₀⟩ p₀ rfl
  let r (x : s) : Module.Ray ℝ (T x.val : E →ₗ[ℝ] F).detLine :=
    FredholmDetLine.orientationCoverFiberEquiv (Fin 1) (f x) ⟨L x, congrFun hLproj x⟩
  classical
  let w : ∀ x, (T x : E →ₗ[ℝ] F).detLine := fun x ↦
    if hx : x ∈ s then (r ⟨x, hx⟩).someVector else 0
  have hw_ne (x : X) (hx : x ∈ s) : w x ≠ 0 := by
    simpa only [w, dite_eq_left hx] using (r ⟨x, hx⟩).someVector_ne_zero
  have hr (x : s) : rayOfNeZero ℝ (w x.val) (hw_ne x.val x.property) = r x := by
    rw [← (r x).someVector_ray, ray_eq_iff]
    simpa only [w, dite_eq_left x.property, Subtype.coe_eta] using SameRay.rfl
  have hw_coh : IsDetLineCoherentOn T w s :=
    (isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := Fin 1) hT hF).2
      ⟨hw_ne, L.continuous.congr fun x ↦ by
        have hL : (⟨L x, congrFun hLproj x⟩ : VectorBundleOrientationCover.proj ⁻¹' {f x}) =
            (FredholmDetLine.orientationCoverFiberEquiv (Fin 1) (f x)).symm (r x) :=
          ((FredholmDetLine.orientationCoverFiberEquiv (Fin 1) (f x)).symm_apply_apply _).symm
        have hL_val : L x = FredholmDetLine.orientationCoverMk (Fin 1) (f x) (r x) := by
          simpa only [FredholmDetLine.orientationCoverFiberEquiv_symm_apply] using
            congrArg Subtype.val hL
        rw [hr x]
        exact hL_val⟩
  have hr₀ : r ⟨x₀, hx₀⟩ = rayOfNeZero ℝ v₀ hv₀ := by
    have hsub : (⟨L ⟨x₀, hx₀⟩, congrFun hLproj ⟨x₀, hx₀⟩⟩ :
        VectorBundleOrientationCover.proj ⁻¹' {f ⟨x₀, hx₀⟩}) = ⟨p₀, rfl⟩ := Subtype.ext hL₀
    exact (congrArg (FredholmDetLine.orientationCoverFiberEquiv (Fin 1) (f ⟨x₀, hx₀⟩)) hsub).trans
      (FredholmDetLine.orientationCoverFiberEquiv_mk (f ⟨x₀, hx₀⟩) (rayOfNeZero ℝ v₀ hv₀))
  have hsr₀ : SameRay ℝ (w x₀) v₀ :=
    (ray_eq_iff _ _).1 ((hr ⟨x₀, hx₀⟩).trans hr₀)
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := hsr₀.exists_pos (hw_ne x₀ hx₀) hv₀
  have hscale : (c₁ / c₂) • w x₀ = v₀ := by
    rw [div_eq_inv_mul, mul_smul, hc, inv_smul_smul₀ hc₂.ne']
  exact ⟨fun x ↦ (c₁ / c₂) • w x, hscale, hw_coh.smul (div_ne_zero hc₁.ne' hc₂.ne')⟩

/-- **Existence of coherent families over convex parameter sets.** Every nonzero determinant vector
`v₀` at `x₀ ∈ s` extends to a coherent family on any convex `s : Set V`. -/
theorem exists_isDetLineCoherentOn_of_convex {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {s : Set V}
    (hs : Convex ℝ s) {T : V → E →L[ℝ] F} (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, (T x).IsFredholm) {x₀ : V} (hx₀ : x₀ ∈ s)
    {v₀ : (T x₀ : E →ₗ[ℝ] F).detLine} (hv₀ : v₀ ≠ 0) :
    ∃ v : ∀ x, (T x : E →ₗ[ℝ] F).detLine, v x₀ = v₀ ∧ IsDetLineCoherentOn T v s := by
  have : ContractibleSpace s := hs.contractibleSpace ⟨x₀, hx₀⟩
  have : SimplyConnectedSpace s := SimplyConnectedSpace.ofContractible s
  have : LocallyPathConnectedSpace s := hs.locallyPathConnectedSpace'
  exact exists_isDetLineCoherentOn_of_simplyConnectedSpace hT hF hx₀ hv₀

end Lifting

end TauCeti
