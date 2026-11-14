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
public import TauCeti.Topology.VectorBundle.Orientation.Cover
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Analysis.Convex.PathConnected
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.LinearAlgebra.Orientation.RankOne
import TauCeti.LinearAlgebra.Ray

/-!
# The orientation double cover of the Fredholm determinant line bundle

The determinant lines of Fredholm operators `T : E →L[ℝ] F` form a real line bundle
`TauCeti.FredholmDetLine ℝ E F` over `{T : E →L[ℝ] F // T.IsFredholm}`
(`TauCeti.FredholmDetLine.vectorBundle`). Because each fibre has dimension one, its `ι`-indexed
orientations (`[Unique ι]`) are canonically in bijection with rays in the determinant line of `T`
(`TauCeti.FredholmDetLine.orientationEquivRay`). Packaging a Fredholm operator together with a ray
in its determinant line (`TauCeti.FredholmDetLine.orientationCoverMk`) identifies the fibres of the
orientation double cover `TauCeti.VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι` with the
two-point spaces `Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine`
(`TauCeti.FredholmDetLine.orientationCoverFiberEquiv`), intertwining the deck involution with ray
negation.

In any standard-model kernel chart `TauCeti.FredholmDetLine.trivialization D₂ q`, two points of the
orientation cover lie in the same sheet if and only if `ContinuousLinearMap.detLineChartEquiv` sends
their determinant-line rays to the same ray in `det G ⊗ (det Λ)^*`
(`TauCeti.FredholmDetLine.mapOrientation_trivialization_eq_iff`). Consequently, a family `v` of
determinant-line elements along a continuous Fredholm family `T : X → E →L[ℝ] F` on `s : Set X` is
coherent in the sense of `TauCeti.IsDetLineCoherentOn` if and only if `v` is nowhere zero on `s` and
the induced lift into the orientation double cover is continuous
(`TauCeti.isDetLineCoherentOn_iff_continuous_orientationCoverMk`). For a globally defined continuous
family `f : C(X, {T // T.IsFredholm})`, this identifies orientations of the pullback bundle
`f *ᵖ FredholmDetLine ℝ E F` with coherent ray families
(`TauCeti.FredholmDetLine.pullbackOrientationEquiv`).

Because the projection of the orientation double cover is a covering map
(`TauCeti.FredholmDetLine.isCoveringMap_orientationCover_proj`), Mathlib's lifting theorem for
covering spaces (`IsCoveringMap.existsUnique_continuousMap_lifts`) extends any nonzero determinant
vector at a basepoint `x₀ ∈ s` to a coherent family over any simply-connected, locally
path-connected parameter set `s` (`TauCeti.exists_isDetLineCoherentOn_of_simplyConnectedSpace`), and
in particular over any convex subset of a real topological vector space such as a parameter
rectangle (`TauCeti.exists_isDetLineCoherentOn_of_convex`).

## Main definitions

* `TauCeti.FredholmDetLine.orientationEquivRay`: canonical equivalence between fibre orientations
  of `FredholmDetLine ℝ E F T` and rays in `(T.1 : E →ₗ[ℝ] F).detLine`.
* `TauCeti.FredholmDetLine.orientationCoverMk`: point of the orientation double cover over `T` from
  a ray in `(T.1 : E →ₗ[ℝ] F).detLine`.
* `TauCeti.FredholmDetLine.orientationCoverFiberEquiv`: equivalence between the fibre of the
  orientation double cover over `T` and `Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine`.
* `TauCeti.FredholmDetLine.pullbackOrientationEquiv`: equivalence between bundle orientations of
  `f *ᵖ FredholmDetLine ℝ E F` and coherent families of determinant-line rays along `f`.

## Main results

* `TauCeti.IsDetLineCoherentWithinAt.congr_sameRay`, `TauCeti.IsDetLineCoherentOn.congr_sameRay`:
  coherence depends only on pointwise nonzero rays.
* `TauCeti.IsDetLineCoherentOn.comp`: coherence pulls back along continuous maps.
* `TauCeti.isDetLineCoherentOn_iff_continuous_orientationCoverMk`: coherence on `s` is equivalent to
  continuity of the lift to `VectorBundleOrientationCover`.
* `TauCeti.exists_isDetLineCoherentOn_of_simplyConnectedSpace`,
  `TauCeti.exists_isDetLineCoherentOn_of_convex`: existence of coherent families over
  simply-connected locally path-connected and convex parameter sets.
-/

public section

noncomputable section

open Bundle ContinuousLinearMap Filter Module Set TensorProduct Topology

namespace TauCeti

section CoherentRay

variable {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X] [TopologicalSpace Y]
  {T : X → E →L[ℝ] F} {v w : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} {x₀ : X}

/-- Coherence within `s` at `x₀` depends only on the rays and vanishing locus of the family near
`x₀`. -/
theorem IsDetLineCoherentWithinAt.congr_sameRay (hv : IsDetLineCoherentWithinAt T v s x₀)
    (hx₀ : w x₀ ≠ 0 ∧ SameRay ℝ (v x₀) (w x₀))
    (hvw : ∀ᶠ x in 𝓝[s] x₀, (v x = 0 ↔ w x = 0) ∧ SameRay ℝ (v x) (w x)) :
    IsDetLineCoherentWithinAt T w s x₀ := by
  obtain ⟨hv₀, S, hS, G, hG, q, h₀, hev⟩ := isDetLineCoherentWithinAt_iff.1 hv
  refine isDetLineCoherentWithinAt_iff.2 ⟨hx₀.1, S, hS, G, hG, q, h₀, ?_⟩
  have hc₀ : detLineChartEquiv (T x₀) S.subtypeL q h₀ (v x₀) ≠ 0 :=
    (detLineChartEquiv (T x₀) S.subtypeL q h₀).map_ne_zero_iff.2 hv₀
  have hcw₀ : SameRay ℝ (detLineChartEquiv (T x₀) S.subtypeL q h₀ (v x₀))
      (detLineChartEquiv (T x₀) S.subtypeL q h₀ (w x₀)) :=
    (SameRay.sameRay_map_iff _).2 hx₀.2
  filter_upwards [hev, hvw] with x ⟨h, hx⟩ ⟨hz, hvwx⟩
  refine ⟨h, ?_⟩
  by_cases hvx : v x = 0
  · rw [hz.1 hvx, LinearEquiv.map_zero]
    exact SameRay.zero_left _
  · have hcx : detLineChartEquiv (T x) S.subtypeL q h (v x) ≠ 0 :=
      (detLineChartEquiv (T x) S.subtypeL q h).map_ne_zero_iff.2 hvx
    have hcwx : SameRay ℝ (detLineChartEquiv (T x) S.subtypeL q h (w x))
        (detLineChartEquiv (T x) S.subtypeL q h (v x)) :=
      (SameRay.sameRay_map_iff _).2 hvwx.symm
    exact (hcwx.trans_of_ne_zero hx hcx).trans_of_ne_zero hcw₀ hc₀

/-- Coherence on `s` depends only on the pointwise nonzero rays of the family on `s`. -/
theorem IsDetLineCoherentOn.congr_sameRay (hv : IsDetLineCoherentOn T v s)
    (hw : ∀ x ∈ s, w x ≠ 0) (hvw : ∀ x ∈ s, SameRay ℝ (v x) (w x)) :
    IsDetLineCoherentOn T w s :=
  isDetLineCoherentOn_iff.2 fun x hx ↦
    (isDetLineCoherentOn_iff.1 hv x hx).congr_sameRay ⟨hw x hx, hvw x hx⟩ <|
      Filter.mem_of_superset self_mem_nhdsWithin
        fun y hy ↦ ⟨iff_of_false (hv.ne_zero hy) (hw y hy), hvw y hy⟩

/-- Coherence on `s` pulls back along a map `f : Y → X` continuous on `t` with `MapsTo f t s`. -/
theorem IsDetLineCoherentOn.comp {f : Y → X} {t : Set Y} (hv : IsDetLineCoherentOn T v s)
    (hf : ContinuousOn f t) (hfts : MapsTo f t s) :
    IsDetLineCoherentOn (T ∘ f) (fun y ↦ v (f y)) t :=
  isDetLineCoherentOn_iff.2 fun y hy ↦
    (isDetLineCoherentOn_iff.1 hv (f y) (hfts hy)).comp ((hf y hy).tendsto_nhdsWithin hfts)

end CoherentRay

namespace FredholmDetLine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Unique ι]

/-- Canonical equivalence between `ι`-indexed orientations of the fibre `FredholmDetLine ℝ E F T`
and rays in `(T.1 : E →ₗ[ℝ] F).detLine`. -/
def orientationEquivRay (T : {T : E →L[ℝ] F // T.IsFredholm}) :
    Orientation ℝ (FredholmDetLine ℝ E F T) ι ≃ Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine :=
  (Orientation.equivRay (ι := ι) finrank_eq_one).trans (Module.Ray.map (linearEquiv T))

@[simp]
theorem orientationEquivRay_neg (T : {T : E →L[ℝ] F // T.IsFredholm})
    (o : Orientation ℝ (FredholmDetLine ℝ E F T) ι) :
    orientationEquivRay (ι := ι) T (-o) = -orientationEquivRay (ι := ι) T o := by
  rw [orientationEquivRay, Equiv.trans_apply, Equiv.trans_apply, Orientation.equivRay_neg]
  -- Like `LinearMap.instNegRayDetLine`, supply `TensorProduct.addCommGroup` directly so typeclass
  -- search does not traverse the nested tensor product `detLine`.
  exact @Module.Ray.map_neg ℝ _ _ _ _ (T.1 : E →ₗ[ℝ] F).detLine _ TensorProduct.addCommGroup _ _
    (linearEquiv T) _

@[simp]
theorem orientationEquivRay_symm_neg (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) :
    (orientationEquivRay (ι := ι) T).symm (-r) = -(orientationEquivRay (ι := ι) T).symm r := by
  apply (orientationEquivRay (ι := ι) T).injective
  rw [Equiv.apply_symm_apply, orientationEquivRay_neg, Equiv.apply_symm_apply]

variable (ι) in
/-- Point of the orientation double cover of `FredholmDetLine ℝ E F` over `T` determined by a ray
in `(T.1 : E →ₗ[ℝ] F).detLine`. -/
def orientationCoverMk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) :
    VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι :=
  ⟨T, (orientationEquivRay (ι := ι) T).symm r⟩

theorem orientationCoverMk_def (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) :
    orientationCoverMk ι T r = ⟨T, (orientationEquivRay (ι := ι) T).symm r⟩ :=
  (rfl)

@[simp]
theorem proj_orientationCoverMk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) :
    (orientationCoverMk ι T r).proj = T :=
  (rfl)

@[simp]
theorem orientationCoverMk_inj {T : {T : E →L[ℝ] F // T.IsFredholm}}
    {r₁ r₂ : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine} :
    orientationCoverMk ι T r₁ = orientationCoverMk ι T r₂ ↔ r₁ = r₂ := by
  rw [orientationCoverMk_def, orientationCoverMk_def, VectorBundleOrientationCover.mk_eq_mk_iff,
    Equiv.apply_eq_iff_eq]

variable (ι) in
/-- Canonical equivalence between the fibre of the orientation double cover over `T` and the space
of rays in `(T.1 : E →ₗ[ℝ] F).detLine`. -/
def orientationCoverFiberEquiv (T : {T : E →L[ℝ] F // T.IsFredholm}) :
    ((VectorBundleOrientationCover.proj :
        VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι → _) ⁻¹' {T}) ≃
      Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine where
  toFun p := orientationEquivRay (ι := ι) T
    (cast (congrArg (fun x ↦ Orientation ℝ (FredholmDetLine ℝ E F x) ι) p.2) p.1.orientation)
  invFun r := ⟨orientationCoverMk ι T r, proj_orientationCoverMk T r⟩
  left_inv := by
    rintro ⟨⟨T', o⟩, hT : T' = T⟩
    cases hT
    simp [orientationCoverMk_def]
  right_inv r := by
    dsimp [orientationCoverMk]
    simp

@[simp]
theorem orientationCoverFiberEquiv_symm_apply (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) :
    (orientationCoverFiberEquiv ι T).symm r =
      ⟨orientationCoverMk ι T r, proj_orientationCoverMk T r⟩ :=
  (rfl)

@[simp]
theorem orientationCoverFiberEquiv_mk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) {h} :
    orientationCoverFiberEquiv ι T ⟨orientationCoverMk ι T r, h⟩ = r :=
  (orientationCoverFiberEquiv ι T).apply_symm_apply r

variable [CompleteSpace E] [CompleteSpace F]

/-- The deck involution of the orientation double cover negates the determinant-line ray. -/
@[simp]
theorem deck_orientationCoverMk (T : {T : E →L[ℝ] F // T.IsFredholm})
    (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) :
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

/-- Membership in the base set of `trivialization D₂ q` is invertibility of the bordered operator
`((T.1.coprod D₂).prod q)`. -/
theorem mem_trivialization_baseSet_iff {T : {T : E →L[ℝ] F // T.IsFredholm}} :
    T ∈ (trivialization D₂ q).baseSet ↔ ((T.1.coprod D₂).prod q).IsInvertible := by
  simp

omit [Unique ι] in
/-- Over its base set, the fibrewise linear equivalence of `trivialization D₂ q` is
`chartCoord D₂ q`. -/
theorem linearEquivAt_trivialization {T : {T : E →L[ℝ] F // T.IsFredholm}}
    (h : ((T.1.coprod D₂).prod q).IsInvertible) :
    (trivialization D₂ q).linearEquivAt ℝ T ((mem_trivialization_baseSet_iff D₂ q).2 h) =
      chartCoord D₂ q h := by
  ext v
  simp [Trivialization.linearEquivAt_apply, trivialization_apply_mk D₂ q h]

/-- Two determinant-line rays over operators in the base set of `trivialization D₂ q` are read as
the same orientation of `ℝ` if and only if `detLineChartEquiv` maps them to the same ray. -/
theorem mapOrientation_trivialization_eq_iff (T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm})
    (h₁ : ((T₁.1.coprod D₂).prod q).IsInvertible) (h₂ : ((T₂.1.coprod D₂).prod q).IsInvertible)
    (r₁ : Module.Ray ℝ (T₁.1 : E →ₗ[ℝ] F).detLine)
    (r₂ : Module.Ray ℝ (T₂.1 : E →ₗ[ℝ] F).detLine) :
    (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h₁)
        ((orientationEquivRay (ι := ι) T₁).symm r₁) =
      (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h₂)
        ((orientationEquivRay (ι := ι) T₂).symm r₂) ↔
      Module.Ray.map (detLineChartEquiv T₁.1 D₂ q h₁) r₁ =
        Module.Ray.map (detLineChartEquiv T₂.1 D₂ q h₂) r₂ := by
  let L : (detLine ℝ (Fin m → ℝ) ⊗[ℝ] Dual ℝ (detLine ℝ (Fin n → ℝ))) ≃ₗ[ℝ] ℝ :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq, TauCeti.finrank_detLine,
        TauCeti.finrank_detLine, Module.finrank_self])
  have hcoord (T : {T : E →L[ℝ] F // T.IsFredholm}) (h : ((T.1.coprod D₂).prod q).IsInvertible)
      (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) :
      (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h)
          ((orientationEquivRay (ι := ι) T).symm r) =
        Orientation.ringRayEquiv ι (Module.Ray.map L (Module.Ray.map
          (detLineChartEquiv T.1 D₂ q h) r)) := by
    induction r using Module.Ray.ind with | h v hv =>
    refine ((trivialization D₂ q).mapOrientation_apply _ _).trans ?_
    rw [linearEquivAt_trivialization D₂ q h]
    simp only [orientationEquivRay, Equiv.symm_trans_apply, Module.Ray.map_symm,
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
    (h₁ : ((T₁.1.coprod D₂).prod q).IsInvertible) (h₂ : ((T₂.1.coprod D₂).prod q).IsInvertible)
    {v₁ : (T₁.1 : E →ₗ[ℝ] F).detLine} (hv₁ : v₁ ≠ 0)
    {v₂ : (T₂.1 : E →ₗ[ℝ] F).detLine} (hv₂ : v₂ ≠ 0) :
    (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h₁)
        ((orientationEquivRay (ι := ι) T₁).symm (rayOfNeZero ℝ v₁ hv₁)) =
      (trivialization D₂ q).mapOrientation ι ((mem_trivialization_baseSet_iff D₂ q).2 h₂)
        ((orientationEquivRay (ι := ι) T₂).symm (rayOfNeZero ℝ v₂ hv₂)) ↔
      SameRay ℝ (detLineChartEquiv T₁.1 D₂ q h₁ v₁) (detLineChartEquiv T₂.1 D₂ q h₂ v₂) :=
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
      ⟨T x.1, hF x.1 x.2⟩ (rayOfNeZero ℝ (v x.1) (hv.ne_zero x.2)) := by
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = finrank ℝ ℝ :=
    Fintype.card_unique.trans (Module.finrank_self ℝ).symm
  let f : s → {T : E →L[ℝ] F // T.IsFredholm} := fun x ↦ ⟨T x.1, hF x.1 x.2⟩
  have hf : Continuous f := (continuousOn_iff_continuous_domRestrict.1 hT).subtype_mk _
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  -- Near `x₀`, read `v` in an atlas kernel chart containing `f x₀`; coherence makes the sheet
  -- reading constant, so the lift agrees on an open neighbourhood with
  -- `continuous_mk_mapOrientation_symm`.
  obtain ⟨n, m, D₂, q, hx₀⟩ := (f x₀).2.exists_isInvertible_prod_coprod
  have hx₀e : f x₀ ∈ (FredholmDetLine.trivialization D₂ q).baseSet :=
    (FredholmDetLine.mem_trivialization_baseSet_iff D₂ q).2 hx₀
  let o₀ := (FredholmDetLine.trivialization D₂ q).mapOrientation ι hx₀e
    ((FredholmDetLine.orientationEquivRay (ι := ι) (f x₀)).symm
      (rayOfNeZero ℝ (v x₀.1) (hv.ne_zero x₀.2)))
  have hU : IsOpen (f ⁻¹' (FredholmDetLine.trivialization D₂ q).baseSet) :=
    (FredholmDetLine.trivialization D₂ q).open_baseSet.preimage hf
  have htend : Tendsto (Subtype.val : s → X) (𝓝 x₀) (𝓝[s] x₀.1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      continuous_subtype_val.continuousAt (Eventually.of_forall fun y ↦ y.2)
  have hev_nhds := htend.eventually
    ((isDetLineCoherentOn_iff.1 hv x₀.1 x₀.2).eventually_sameRay (hT x₀.1 x₀.2) hx₀)
  obtain ⟨W, hWsub, hWopen, hx₀W⟩ := mem_nhds_iff.1 (hev_nhds.and (hU.mem_nhds hx₀e))
  have hψ := VectorBundleOrientationCover.continuous_mk_mapOrientation_symm hcard
    (FredholmDetLine.trivialization D₂ q) o₀
  have hφ : Continuous fun w : W ↦
      (⟨f w.1, (hWsub w.2).2⟩ : (FredholmDetLine.trivialization D₂ q).baseSet) :=
    (hf.comp continuous_subtype_val).subtype_mk fun w ↦ (hWsub w.2).2
  have hgW : ContinuousOn (fun x : s ↦ FredholmDetLine.orientationCoverMk ι (f x)
      (rayOfNeZero ℝ (v x.1) (hv.ne_zero x.2))) W := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine (hψ.comp hφ).congr fun w ↦ ?_
    obtain ⟨⟨hy', hsr⟩, hwU⟩ := hWsub w.2
    exact congrArg (VectorBundleOrientationCover.mk (f w.1))
      ((Equiv.symm_apply_eq ((FredholmDetLine.trivialization D₂ q).mapOrientation ι hwU)).2
        (((FredholmDetLine.mapOrientation_trivialization_rayOfNeZero_eq_iff D₂ q (f w.1) (f x₀)
          hy' hx₀ (hv.ne_zero w.1.2) (hv.ne_zero x₀.2)).2 hsr).symm))
  exact hgW.continuousAt (hWopen.mem_nhds hx₀W)

/-- Conversely, a nowhere-zero determinant-line family `v` over `s` whose lift into
`VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι` is continuous is coherent on `s`. -/
theorem isDetLineCoherentOn_of_continuous_orientationCoverMk {T : X → E →L[ℝ] F}
    {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, (T x).IsFredholm) (hv0 : ∀ x ∈ s, v x ≠ 0)
    (hg : Continuous fun x : s ↦ FredholmDetLine.orientationCoverMk ι
      ⟨T x.1, hF x.1 x.2⟩ (rayOfNeZero ℝ (v x.1) (hv0 x.1 x.2))) :
    IsDetLineCoherentOn T v s := by
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = finrank ℝ ℝ :=
    Fintype.card_unique.trans (Module.finrank_self ℝ).symm
  let f : s → {T : E →L[ℝ] F // T.IsFredholm} := fun x ↦ ⟨T x.1, hF x.1 x.2⟩
  -- Continuity into the open sheet of an atlas chart gives `SameRay` in that chart, which
  -- transfers to a submodule kernel chart by `eventually_detLineChartEquiv_symm_eq_smul`.
  rw [isDetLineCoherentOn_iff]
  intro x₀ hx₀s
  let p₀ : s := ⟨x₀, hx₀s⟩
  obtain ⟨n, m, D₂, q, hx₀⟩ := (hF x₀ hx₀s).exists_isInvertible_prod_coprod
  have hx₀e : f p₀ ∈ (FredholmDetLine.trivialization D₂ q).baseSet :=
    (FredholmDetLine.mem_trivialization_baseSet_iff D₂ q).2 hx₀
  let o₀ := (FredholmDetLine.trivialization D₂ q).mapOrientation ι hx₀e
    ((FredholmDetLine.orientationEquivRay (ι := ι) (f p₀)).symm
      (rayOfNeZero ℝ (v x₀) (hv0 x₀ hx₀s)))
  have hmem : FredholmDetLine.orientationCoverMk ι (f p₀)
      (rayOfNeZero ℝ (v x₀) (hv0 x₀ hx₀s)) ∈
        VectorBundleOrientationCover.sheet (FredholmDetLine.trivialization D₂ q) o₀ :=
    VectorBundleOrientationCover.mem_sheet_iff.2 ⟨hx₀e, rfl⟩
  have hsheet := hg.continuousAt.preimage_mem_nhds
    ((VectorBundleOrientationCover.isOpen_sheet hcard
      (FredholmDetLine.trivialization D₂ q) o₀).mem_nhds hmem)
  rw [nhds_subtype_eq_comap] at hsheet
  obtain ⟨V, hV, hVs⟩ := Filter.mem_comap.1 hsheet
  have hev_atlas : ∀ᶠ y in 𝓝[s] x₀, ∃ hy : (((T y).coprod D₂).prod q).IsInvertible,
      SameRay ℝ (detLineChartEquiv (T y) D₂ q hy (v y))
        (detLineChartEquiv (T x₀) D₂ q hx₀ (v x₀)) := by
    filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with y hyV hys
    let py : s := ⟨y, hys⟩
    have hyp : py ∈ Subtype.val ⁻¹' V := hyV
    obtain ⟨hye, hyo⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 (hVs hyp)
    have hy' : (((T y).coprod D₂).prod q).IsInvertible :=
      (FredholmDetLine.mem_trivialization_baseSet_iff D₂ q).1 hye
    exact ⟨hy', (FredholmDetLine.mapOrientation_trivialization_rayOfNeZero_eq_iff D₂ q
      (f py) (f p₀) hy' hx₀ (hv0 y hys) (hv0 x₀ hx₀s)).1 hyo⟩
  obtain ⟨S, hS, G, hG, q₁, U₁, -, hx₀U₁, hinv₁⟩ := (hF x₀ hx₀s).exists_isOpen_kernelChart
  have h₁ := hinv₁ _ hx₀U₁
  refine isDetLineCoherentWithinAt_iff.2 ⟨hv0 x₀ hx₀s, S, hS, G, hG, q₁, h₁, ?_⟩
  filter_upwards [hev_atlas,
    (hT x₀ hx₀s).tendsto.eventually (eventually_detLineChartEquiv_symm_eq_smul h₁ hx₀)]
    with y hx hcy
  obtain ⟨_, hsr⟩ := hx
  obtain ⟨hy₁, hy₀, c, hc, hcu⟩ := hcy
  refine ⟨hy₁, ?_⟩
  have hmap := (hsr.map ((detLineChartEquiv (T x₀) D₂ q hx₀).symm.trans
    (detLineChartEquiv (T x₀) S.subtypeL q₁ h₁)).toLinearMap).pos_smul_left hc
  simpa only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, ← hcu]
    using hmap

/-- **Coherence via the orientation double cover.** For a family `T : X → E →L[ℝ] F` that is
continuous and Fredholm on `s : Set X`, a family `v` of elements of the determinant lines is
coherent on `s` if and only if `v` is nowhere zero on `s` and the induced lift over `s` into
`VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι` is continuous. -/
theorem isDetLineCoherentOn_iff_continuous_orientationCoverMk {T : X → E →L[ℝ] F}
    {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, (T x).IsFredholm) :
    IsDetLineCoherentOn T v s ↔ ∃ hv : ∀ x ∈ s, v x ≠ 0,
      Continuous fun x : s ↦ FredholmDetLine.orientationCoverMk ι
        ⟨T x.1, hF x.1 x.2⟩ (rayOfNeZero ℝ (v x.1) (hv x.1 x.2)) :=
  ⟨fun hv ↦ ⟨fun _ hx ↦ hv.ne_zero hx, hv.continuous_orientationCoverMk hT hF⟩,
    fun ⟨hv, hg⟩ ↦ isDetLineCoherentOn_of_continuous_orientationCoverMk hT hF hv hg⟩

/-- For a continuous family `f : C(X, {T // T.IsFredholm})`, a family of fibre orientations of
`f *ᵖ (FredholmDetLine ℝ E F)` is a bundle orientation if and only if its lift to the orientation
double cover is continuous. -/
private theorem FredholmDetLine.continuous_mk_pullback_iff
    (f : C(X, {T : E →L[ℝ] F // T.IsFredholm}))
    (o : ∀ x, Orientation ℝ (((⇑f) *ᵖ (FredholmDetLine ℝ E F)) x) ι) :
    Continuous (fun x ↦
        (⟨f x, o x⟩ : VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι)) ↔
      ∀ x₀ : X, ∀ᶠ x in 𝓝 x₀,
        ∀ hx : x ∈ (trivializationAt ℝ ((⇑f) *ᵖ (FredholmDetLine ℝ E F)) x₀).baseSet,
          (trivializationAt ℝ ((⇑f) *ᵖ (FredholmDetLine ℝ E F)) x₀).mapOrientation ι hx (o x) =
            (trivializationAt ℝ ((⇑f) *ᵖ (FredholmDetLine ℝ E F)) x₀).mapOrientation ι
              (FiberBundle.mem_baseSet_trivializationAt' x₀) (o x₀) := by
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = finrank ℝ ℝ :=
    Fintype.card_unique.trans (Module.finrank_self ℝ).symm
  refine ⟨fun hg x₀ ↦ ?_, fun ho ↦ ?_⟩
  · have hb₀ := FiberBundle.mem_baseSet_trivializationAt'
      (F := ℝ) (E := FredholmDetLine ℝ E F) (f x₀)
    have hmem : (⟨f x₀, o x₀⟩ : VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) ι) ∈
        VectorBundleOrientationCover.sheet (trivializationAt ℝ (FredholmDetLine ℝ E F) (f x₀))
          ((trivializationAt ℝ (FredholmDetLine ℝ E F) (f x₀)).mapOrientation ι hb₀ (o x₀)) :=
      VectorBundleOrientationCover.mem_sheet_iff.2 ⟨hb₀, rfl⟩
    filter_upwards [hg.continuousAt.preimage_mem_nhds
      ((VectorBundleOrientationCover.isOpen_sheet_trivializationAt _ _).mem_nhds hmem)]
      with x hx hx'
    obtain ⟨_, hxo⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hx
    exact ((trivializationAt ℝ (FredholmDetLine ℝ E F) (f x₀)).mapOrientation_pullback
      f hx' _).trans
      (hxo.trans ((trivializationAt ℝ (FredholmDetLine ℝ E F) (f x₀)).mapOrientation_pullback f
        (FiberBundle.mem_baseSet_trivializationAt' x₀) _).symm)
  · let bo : VectorBundleOrientation ℝ ((⇑f) *ᵖ (FredholmDetLine ℝ E F)) ι := ⟨o, ho⟩
    refine VectorBundleOrientationCover.continuous_of_isOpen_preimage_sheet f.continuous
      fun b o' ↦ isOpen_iff_mem_nhds.2 fun x₀ hx₀s ↦ ?_
    obtain ⟨hx₀, hxo⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hx₀s
    have hpull : x₀ ∈ ((trivializationAt ℝ (FredholmDetLine ℝ E F) b).pullback f).baseSet := hx₀
    filter_upwards [bo.eventually_mapOrientation_eq hcard
        ((trivializationAt ℝ (FredholmDetLine ℝ E F) b).pullback f) hpull,
      f.continuous.continuousAt.eventually
        ((trivializationAt ℝ (FredholmDetLine ℝ E F) b).open_baseSet.mem_nhds hx₀)]
      with x hx hx'
    refine VectorBundleOrientationCover.mem_sheet_iff.2 ⟨hx', ?_⟩
    exact (((trivializationAt ℝ (FredholmDetLine ℝ E F) b).mapOrientation_pullback f
      hx' (o x)).symm.trans (hx hx')).trans
      (((trivializationAt ℝ (FredholmDetLine ℝ E F) b).mapOrientation_pullback f
        hpull (o x₀)).trans hxo)

variable (ι) in
/-- **Bundle orientations versus coherent ray families.** For a continuous family
`f : C(X, {T : E →L[ℝ] F // T.IsFredholm})`, bundle orientations of `f *ᵖ (FredholmDetLine ℝ E F)`
are canonically equivalent to families of determinant-line rays whose representative vectors are
coherent on `univ`. -/
def FredholmDetLine.pullbackOrientationEquiv (f : C(X, {T : E →L[ℝ] F // T.IsFredholm})) :
    VectorBundleOrientation ℝ ((⇑f) *ᵖ (FredholmDetLine ℝ E F)) ι ≃
      {r : ∀ x, Module.Ray ℝ ((f x).1 : E →ₗ[ℝ] F).detLine //
        IsDetLineCoherentOn (fun x ↦ (f x).1) (fun x ↦ (r x).someVector) univ} where
  toFun o := ⟨fun x ↦ FredholmDetLine.orientationEquivRay (ι := ι) (f x) (o x), by
    have hT : ContinuousOn (fun x ↦ (f x).1) univ :=
      (continuous_subtype_val.comp f.continuous).continuousOn
    rw [isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := ι) hT (fun x _ ↦ (f x).2)]
    refine ⟨fun x _ ↦ (_ : Module.Ray ℝ _).someVector_ne_zero, ?_⟩
    have hg := (FredholmDetLine.continuous_mk_pullback_iff (ι := ι) f o).2
      o.eventually_mapOrientation_eq'
    refine (hg.comp continuous_subtype_val).congr fun x ↦ ?_
    refine congrArg (VectorBundleOrientationCover.mk (f x.1)) ?_
    rw [Module.Ray.someVector_ray]
    exact ((FredholmDetLine.orientationEquivRay (ι := ι) (f x.1)).symm_apply_apply (o x.1)).symm⟩
  invFun r :=
    let oFun : ∀ x, Orientation ℝ (((⇑f) *ᵖ (FredholmDetLine ℝ E F)) x) ι :=
      fun x ↦ (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).symm (r.1 x)
    ⟨oFun, by
      have hT : ContinuousOn (fun x ↦ (f x).1) univ :=
        (continuous_subtype_val.comp f.continuous).continuousOn
      obtain ⟨hv, hg⟩ := (isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := ι) hT
        (fun x _ ↦ (f x).2)).1 r.2
      refine (FredholmDetLine.continuous_mk_pullback_iff (ι := ι) f oFun).1 ?_
      have hg' : Continuous fun x : X ↦ FredholmDetLine.orientationCoverMk ι (f x)
          (rayOfNeZero ℝ (r.1 x).someVector (hv x (mem_univ x))) :=
        hg.comp (continuous_id.subtype_mk fun _ ↦ mem_univ _)
      refine hg'.congr fun x ↦ congrArg (VectorBundleOrientationCover.mk (f x)) ?_
      exact congrArg (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).symm
        (r.1 x).someVector_ray⟩
  left_inv o := by
    ext x
    exact (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).symm_apply_apply (o x)
  right_inv r := by
    ext x
    exact (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).apply_symm_apply (r.1 x)

@[simp]
theorem FredholmDetLine.pullbackOrientationEquiv_apply
    (f : C(X, {T : E →L[ℝ] F // T.IsFredholm}))
    (o : VectorBundleOrientation ℝ ((⇑f) *ᵖ (FredholmDetLine ℝ E F)) ι) (x : X) :
    (FredholmDetLine.pullbackOrientationEquiv ι f o).1 x =
      FredholmDetLine.orientationEquivRay (ι := ι) (f x) (o x) :=
  (rfl)

@[simp]
theorem FredholmDetLine.pullbackOrientationEquiv_symm_apply
    (f : C(X, {T : E →L[ℝ] F // T.IsFredholm}))
    (r : {r : ∀ x, Module.Ray ℝ ((f x).1 : E →ₗ[ℝ] F).detLine //
      IsDetLineCoherentOn (fun x ↦ (f x).1) (fun x ↦ (r x).someVector) univ}) (x : X) :
    (FredholmDetLine.pullbackOrientationEquiv ι f).symm r x =
      (FredholmDetLine.orientationEquivRay (ι := ι) (f x)).symm (r.1 x) :=
  (rfl)

end CoherenceEquivalence

section Lifting

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Existence of coherent families over simply-connected parameter sets.** If `s : Set X` is
simply connected and locally path-connected and `T : X → E →L[ℝ] F` is continuous and Fredholm on
`s`, then every nonzero determinant vector `v₀` at a basepoint `x₀ ∈ s` extends to a coherent family
on `s`. -/
theorem exists_isDetLineCoherentOn_of_simplyConnectedSpace [TopologicalSpace X] {s : Set X}
    [SimplyConnectedSpace s] [LocallyPathConnectedSpace s] {T : X → E →L[ℝ] F}
    (hT : ContinuousOn T s) (hF : ∀ x ∈ s, (T x).IsFredholm) {x₀ : X} (hx₀ : x₀ ∈ s)
    {v₀ : (T x₀ : E →ₗ[ℝ] F).detLine} (hv₀ : v₀ ≠ 0) :
    ∃ v : ∀ x, (T x : E →ₗ[ℝ] F).detLine, v x₀ = v₀ ∧ IsDetLineCoherentOn T v s := by
  let f : C(s, {T : E →L[ℝ] F // T.IsFredholm}) :=
    ⟨fun x ↦ ⟨T x.1, hF x.1 x.2⟩, (continuousOn_iff_continuous_domRestrict.1 hT).subtype_mk _⟩
  let p₀ := FredholmDetLine.orientationCoverMk (Fin 1) (f ⟨x₀, hx₀⟩) (rayOfNeZero ℝ v₀ hv₀)
  obtain ⟨L, ⟨hL₀, hLproj⟩, -⟩ :=
    (FredholmDetLine.isCoveringMap_orientationCover_proj (E := E) (F := F)
      (ι := Fin 1)).existsUnique_continuousMap_lifts f ⟨x₀, hx₀⟩ p₀ rfl
  have hproj (x : s) : (L x).proj = f x := congrFun hLproj x
  let r (x : s) : Module.Ray ℝ (T x.1 : E →ₗ[ℝ] F).detLine :=
    FredholmDetLine.orientationCoverFiberEquiv (Fin 1) (f x) ⟨L x, hproj x⟩
  classical
  let w : ∀ x, (T x : E →ₗ[ℝ] F).detLine := fun x ↦
    if hx : x ∈ s then (r ⟨x, hx⟩).someVector else 0
  have hw_ne (x : X) (hx : x ∈ s) : w x ≠ 0 := by
    simpa only [w, dite_eq_left hx] using (r ⟨x, hx⟩).someVector_ne_zero
  have hw_coh : IsDetLineCoherentOn T w s := by
    refine (isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := Fin 1) hT hF).2 ⟨hw_ne, ?_⟩
    refine L.continuous.congr fun x ↦ ?_
    have hr : rayOfNeZero ℝ (w x.1) (hw_ne x.1 x.2) = r x := by
      rw [← (r x).someVector_ray, ray_eq_iff]
      simpa only [w, dite_eq_left x.2, Subtype.coe_eta] using SameRay.rfl
    have hL_eq : (⟨L x, hproj x⟩ : (VectorBundleOrientationCover.proj ⁻¹' {f x})) =
        (FredholmDetLine.orientationCoverFiberEquiv (Fin 1) (f x)).symm (r x) := by
      simp [r]
    have hL_val : L x = FredholmDetLine.orientationCoverMk (Fin 1) (f x) (r x) := by
      simpa only [FredholmDetLine.orientationCoverFiberEquiv_symm_apply] using
        congrArg Subtype.val hL_eq
    rw [hr]
    exact hL_val
  -- At `x₀`, `w x₀` lies in the ray of `v₀`, so a positive scalar multiple matches `v₀`.
  have hr₀ : r ⟨x₀, hx₀⟩ = rayOfNeZero ℝ v₀ hv₀ := by
    simp [r, hL₀, p₀]
  have hsr₀ : SameRay ℝ (w x₀) v₀ := by
    have hw₀ : rayOfNeZero ℝ (w x₀) (hw_ne x₀ hx₀) = rayOfNeZero ℝ v₀ hv₀ := by
      rw [← hr₀, ← (r ⟨x₀, hx₀⟩).someVector_ray, ray_eq_iff]
      simpa only [w, dite_eq_left hx₀] using SameRay.rfl
    exact (ray_eq_iff _ _).1 hw₀
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := hsr₀.exists_pos (hw_ne x₀ hx₀) hv₀
  have hscale : (c₁ / c₂) • w x₀ = v₀ := by
    rw [div_eq_inv_mul, mul_smul, hc, inv_smul_smul₀ hc₂.ne']
  exact ⟨fun x ↦ (c₁ / c₂) • w x, hscale, hw_coh.smul (div_ne_zero hc₁.ne' hc₂.ne')⟩

/-- **Existence of coherent families over convex parameter sets.** In any real topological vector
space `V`, if `s : Set V` is convex and `T : V → E →L[ℝ] F` is continuous and Fredholm on `s`, then
every nonzero determinant vector `v₀` at a basepoint `x₀ ∈ s` extends to a coherent family on `s`.
-/
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
