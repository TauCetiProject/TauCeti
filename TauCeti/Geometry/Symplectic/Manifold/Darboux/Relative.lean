/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Darboux.Relative

/-!
# The point-germ relative Darboux theorem on manifolds

Let `M` be a boundaryless smooth manifold with finite-dimensional model space, and let
`i : Q → M` be a smooth map from a boundaryless manifold which is an immersion at `q₀`; near
`q₀` it parametrizes an embedded submanifold through `p = i q₀`. Let `σ₀` and `σ₁` be closed
smooth two-forms on `M`, nondegenerate at `p`, whose pullbacks along `i` agree near `q₀`. The
pullbacks may be degenerate, of any rank, and away from the image of `i` the two forms are
unrelated.

The **relative Darboux theorem**
(`TauCeti.SmoothTwoForm.exists_partialDiffeomorph_fix_eval₂_mfderiv_eq_of_mpullback_eq`) says
that `σ₀` and `σ₁` have symplectomorphic germs at `p` by a germ fixing the submanifold: some
smooth partial diffeomorphism `Φ` of `M` defined near `p` fixes `i q` for every `q` near `q₀`, and
pulls `σ₁` back to `σ₀` on its source. No normal-bundle data along the image of `i` is involved;
the statement is local at `p`.

The proof reads both forms in the adapted coordinates `E_Q × F` supplied by the immersion, in which
the image of `i` is the zero section `E_Q × {0}`, and applies the relative Darboux theorem in
adapted coordinates
(`TauCeti.exists_diffeomorph_fix_zeroSection_eventually_compContinuousLinearMap_fderiv_eq`). The
coordinate expression of a form in a partial diffeomorphism `χ` is obtained from its expression
in the preferred extended chart by the flat pullback along the smooth transition map, so it is
smooth, and closed when the form is.

## References

* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346 (the relative Darboux theorem).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lectures 7–8 (Moser's theorems and Darboux–Moser–Weinstein theory).
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Coordinates

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (χ : PartialDiffeomorph I 𝓘(ℝ, X) M X ∞) (p : M)

/-- The transition from the coordinates of `χ` to the preferred extended chart at `p`. -/
private def coordTransition : X → E :=
  extChartAt I p ∘ χ.symm

/-- The open set of `χ`-coordinates of the points of the preferred chart domain at `p`. -/
private def coordDomain : Set X :=
  χ.target ∩ χ.symm ⁻¹' (extChartAt I p).source

omit [I.Boundaryless] [IsManifold I ∞ M] in
private theorem isOpen_coordDomain : IsOpen (coordDomain χ p) :=
  χ.symm.toOpenPartialHomeomorph.isOpen_inter_preimage (isOpen_extChartAt_source p)

omit [I.Boundaryless] [IsManifold I ∞ M] in
private theorem mapsTo_coordTransition :
    MapsTo (coordTransition χ p) (coordDomain χ p) (extChartAt I p).target :=
  fun _ hy ↦ (extChartAt I p).map_source hy.2

omit [I.Boundaryless] in
private theorem contDiffOn_coordTransition :
    ContDiffOn ℝ ∞ (coordTransition χ p) (coordDomain χ p) := by
  have h : ContMDiffOn 𝓘(ℝ, X) 𝓘(ℝ, E) ∞ (extChartAt I p ∘ χ.symm) (coordDomain χ p) :=
    (contMDiffOn_extChartAt (n := ∞)).comp (χ.symm.contMDiffOn.mono inter_subset_left)
      fun _ hy ↦ by simpa only [extChartAt_source] using hy.2
  exact h.contDiffOn

/-- The coordinate expression of a two-form `σ` in the partial diffeomorphism `χ`: the flat
pullback of its expression in the preferred extended chart at `p` along the transition map. -/
private def coordForm (σ : SmoothTwoForm I M) : X → X [⋀^Fin 2]→L[ℝ] ℝ :=
  fun y ↦ (RoughForm.inChartAt σ.1 p (coordTransition χ p y)).compContinuousLinearMap
    (fderiv ℝ (coordTransition χ p) y)

private theorem contDiffOn_inChartAt_target (σ : SmoothTwoForm I M) :
    ContDiffOn ℝ ∞ (RoughForm.inChartAt σ.1 p) (extChartAt I p).target := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  simpa only [(isOpen_extChartAt_target p).interior_eq] using
    σ.isSmoothForm.contDiffOn_inChartAt_interior_target p

private theorem contDiffOn_coordForm (σ : SmoothTwoForm I M) :
    ContDiffOn ℝ ∞ (coordForm χ p σ) (coordDomain χ p) := by
  have hτ := contDiffOn_coordTransition χ p
  have hDτ : ContDiffOn ℝ ∞ (fderiv ℝ (coordTransition χ p)) (coordDomain χ p) :=
    hτ.fderiv_of_isOpen (isOpen_coordDomain χ p) (by simp)
  exact ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (𝕜 := ℝ) (E := X) (F := E)
    (G := ℝ) (ι := Fin 2) ∞).comp_contDiffOn hDτ).clm_apply
    ((contDiffOn_inChartAt_target p σ).comp hτ (mapsTo_coordTransition χ p))

private theorem extDeriv_coordForm {σ : SmoothTwoForm I M} (hσ : σ.IsClosed) {y : X}
    (hy : y ∈ coordDomain χ p) : extDeriv (coordForm χ p σ) y = 0 := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have hτ : ContDiffAt ℝ ∞ (coordTransition χ p) y :=
    (contDiffOn_coordTransition χ p).contDiffAt ((isOpen_coordDomain χ p).mem_nhds hy)
  have hz : coordTransition χ p y ∈ interior (extChartAt I p).target := by
    rw [(isOpen_extChartAt_target p).interior_eq]
    exact mapsTo_coordTransition χ p hy
  have hη : DifferentiableAt ℝ (RoughForm.inChartAt σ.1 p) (coordTransition χ p y) :=
    ((contDiffOn_inChartAt_target p σ).differentiableOn (by simp)).differentiableAt
      ((isOpen_extChartAt_target p).mem_nhds (interior_subset hz))
  unfold coordForm
  rw [extDeriv_pullback hη hτ (by simp), hσ.extDeriv_inChartAt_eq_zero p hz]
  ext v
  simp

omit [I.Boundaryless] in
/-- A two-form evaluated at a point of the chart domains agrees with its coordinate expression
evaluated on the `χ`-derivatives of the tangent vectors. -/
private theorem eval₂_eq_coordForm (σ : SmoothTwoForm I M) {x : M} (hx : x ∈ χ.source)
    (hxp : x ∈ (extChartAt I p).source) (v w : TangentSpace I x) :
    σ.eval₂ x v w = coordForm χ p σ (χ x) ![mvfderiv I χ x v, mvfderiv I χ x w] := by
  have hxD : χ x ∈ coordDomain χ p :=
    ⟨χ.toPartialEquiv.map_source hx, by
      rw [mem_preimage, PartialDiffeomorph.symm_toPartialEquiv, χ.toPartialEquiv.left_inv hx]
      exact hxp⟩
  have heq : coordTransition χ p ∘ χ =ᶠ[𝓝 x] extChartAt I p := by
    filter_upwards [χ.open_source.mem_nhds hx] with x' hx'
    exact congrArg (extChartAt I p) (χ.toPartialEquiv.left_inv hx')
  have hτ : DifferentiableAt ℝ (coordTransition χ p) (χ x) :=
    ((contDiffOn_coordTransition χ p).differentiableOn (by simp)).differentiableAt
      ((isOpen_coordDomain χ p).mem_nhds hxD)
  have hd (u : TangentSpace I x) : mvfderiv I (extChartAt I p) x u =
      fderiv ℝ (coordTransition χ p) (χ x) (mvfderiv I χ x u) := by
    rw [← heq.mvfderiv_eq,
      mvfderiv_comp_apply_of_differentiableAt hτ (χ.mdifferentiableAt (by simp) hx)]
  have hvec : (fun j ↦ mvfderiv I (extChartAt I p) x (![v, w] j)) =
      fun j ↦ fderiv ℝ (coordTransition χ p) (χ x) (![mvfderiv I χ x v, mvfderiv I χ x w] j) := by
    ext j
    fin_cases j <;> exact hd _
  rw [SmoothBundleForm.eval₂_apply, RoughForm.apply_eq_inChartAt_mvfderiv σ.1 hxp, hvec,
    ← heq.eq_of_nhds]
  rfl

omit [I.Boundaryless] [IsManifold I ∞ M] in
/-- The `χ`-derivative at a point of the source of `χ` is surjective. -/
private theorem surjective_mvfderiv {x : M} (hx : x ∈ χ.source) :
    Surjective (mvfderiv I χ x) := by
  intro u
  obtain ⟨v, hv⟩ := ((PartialDiffeomorph.isLocalDiffeomorphAt I 𝓘(ℝ, X) ∞ χ hx).isInvertible_mfderiv
    (by simp)).surjective u
  exact ⟨v, by rw [mvfderiv_apply_eq_mfderiv_apply, hv]⟩

omit [I.Boundaryless] in
/-- A two-form nondegenerate at a point of the chart domains has nondegenerate coordinate
expression there. -/
private theorem coordForm_nondegenerate {σ : SmoothTwoForm I M} {x : M} (hx : x ∈ χ.source)
    (hxp : x ∈ (extChartAt I p).source) (hnd : (σ.bilinFormAt x).Nondegenerate) (u : X)
    (hu : ∀ u', coordForm χ p σ (χ x) ![u, u'] = 0) : u = 0 := by
  obtain ⟨v, rfl⟩ := surjective_mvfderiv χ hx u
  have hv : v = 0 := hnd.1 v fun w ↦ by
    rw [SmoothForm.bilinFormAt_apply, eval₂_eq_coordForm χ p σ hx hxp]
    exact hu _
  rw [hv, map_zero]

omit [I.Boundaryless] in
/-- If `χ ∘ Φ` agrees near `x` with `Ψ ∘ χ` for a map `Ψ` of the coordinate space whose flat
pullback of the coordinate expression of `σ₁` at `χ x` is that of `σ₀`, then `Φ` pulls `σ₁` back
to `σ₀` at `x`. -/
private theorem eval₂_mfderiv_eq_of_comp_eventuallyEq {σ₀ σ₁ : SmoothTwoForm I M} {Φ : M → M}
    {Ψ : X → X} {x : M} (hx : x ∈ χ.source) (hxp : x ∈ (extChartAt I p).source)
    (hΦx : Φ x ∈ χ.source) (hΦxp : Φ x ∈ (extChartAt I p).source)
    (hΦ : MDifferentiableAt I I Φ x) (hΨ : DifferentiableAt ℝ Ψ (χ x))
    (hcomm : χ ∘ Φ =ᶠ[𝓝 x] Ψ ∘ χ)
    (hpull : (coordForm χ p σ₁ (Ψ (χ x))).compContinuousLinearMap (fderiv ℝ Ψ (χ x)) =
      coordForm χ p σ₀ (χ x)) (v w : TangentSpace I x) :
    σ₁.eval₂ (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) = σ₀.eval₂ x v w := by
  have hχΦ : χ (Φ x) = Ψ (χ x) := hcomm.eq_of_nhds
  have hd (u : TangentSpace I x) :
      mvfderiv I χ (Φ x) (mfderiv I I Φ x u) = fderiv ℝ Ψ (χ x) (mvfderiv I χ x u) := by
    rw [← mvfderiv_comp_apply x (χ.mdifferentiableAt (by simp) hΦx) hΦ, hcomm.mvfderiv_eq,
      mvfderiv_comp_apply_of_differentiableAt hΨ (χ.mdifferentiableAt (by simp) hx)]
  rw [eval₂_eq_coordForm χ p σ₁ hΦx hΦxp, eval₂_eq_coordForm χ p σ₀ hx hxp, hd, hd, hχΦ, ← hpull]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

end Coordinates

section Adapted

variable {X N : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

/-- The relative Darboux theorem in a partial diffeomorphism `χ` to `X × N`. If two closed
two-forms, nondegenerate at `p`, have coordinate expressions agreeing on `X × {0}` at the points
`(u, 0)` with `u` near the first coordinate of `χ p`, and `χ p` lies in `X × {0}`, then a partial
diffeomorphism pulling `σ₁` back to `σ₀` fixes every point near `p` whose coordinates lie in
`X × {0}`. -/
private theorem exists_partialDiffeomorph_of_coordForm
    (χ : PartialDiffeomorph I 𝓘(ℝ, X × N) M (X × N) ∞) {p : M} (hp : p ∈ χ.source)
    (hχp : (χ p).2 = 0) {σ₀ σ₁ : SmoothTwoForm I M} (hσ₀ : σ₀.IsClosed) (hσ₁ : σ₁.IsClosed)
    (hnd₀ : (σ₀.bilinFormAt p).Nondegenerate) (hnd₁ : (σ₁.bilinFormAt p).Nondegenerate)
    (htan : ∀ᶠ u in 𝓝 (χ p).1,
      (coordForm χ p σ₁ (u, 0)).compContinuousLinearMap (.inl ℝ X N) =
        (coordForm χ p σ₀ (u, 0)).compContinuousLinearMap (.inl ℝ X N)) :
    ∃ Φ : PartialDiffeomorph I I M M ∞, p ∈ Φ.source ∧
      (∀ᶠ x in 𝓝 p, (χ x).2 = 0 → x ∈ Φ.source ∧ Φ x = x) ∧
      ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
        σ₁.eval₂ (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) = σ₀.eval₂ x v w := by
  set u₀ := (χ p).1
  have hy₀ : χ p = (u₀, 0) := Prod.ext rfl hχp
  have hpp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have hy₀D : (u₀, (0 : N)) ∈ coordDomain χ p :=
    hy₀ ▸ ⟨χ.toPartialEquiv.map_source hp, by
      rw [mem_preimage, PartialDiffeomorph.symm_toPartialEquiv, χ.toPartialEquiv.left_inv hp]
      exact hpp⟩
  -- Shrink the coordinate domain so that every point of the zero section in it satisfies the
  -- tangency hypothesis.
  obtain ⟨t, htP, ht, hu₀t⟩ := eventually_nhds_iff.1 htan
  let W : Set (X × N) := coordDomain χ p ∩ Prod.fst ⁻¹' t
  have hW : IsOpen W := (isOpen_coordDomain χ p).inter (ht.preimage continuous_fst)
  have hy₀W : (u₀, (0 : N)) ∈ W := ⟨hy₀D, hu₀t⟩
  have hnd (σ : SmoothTwoForm I M) (hnd : (σ.bilinFormAt p).Nondegenerate) (u : X × N)
      (hu : ∀ u', coordForm χ p σ (u₀, 0) ![u, u'] = 0) : u = 0 :=
    coordForm_nondegenerate χ p hp hpp hnd u (hy₀ ▸ hu)
  obtain ⟨Ψ, hfix, hpull⟩ :=
    exists_diffeomorph_fix_zeroSection_eventually_compContinuousLinearMap_fderiv_eq
      (r := (⊤ : ℕ∞)) le_top hW hy₀W
      ((contDiffOn_coordForm χ p σ₀).mono inter_subset_left)
      ((contDiffOn_coordForm χ p σ₁).mono inter_subset_left)
      (fun y hy ↦ extDeriv_coordForm χ p hσ₀ hy.1) (fun y hy ↦ extDeriv_coordForm χ p hσ₁ hy.1)
      (fun q hq ↦ htP q hq.2) (hnd σ₀ hnd₀) (hnd σ₁ hnd₁)
  have hΨy₀ : Ψ (u₀, 0) = (u₀, 0) := hfix.self_of_nhds
  -- A neighbourhood of `(u₀, 0)` on which the flat pullback identity holds and which, together
  -- with its image under `Ψ`, lies in the coordinate domain.
  have hU : {y | y ∈ coordDomain χ p ∧ Ψ y ∈ coordDomain χ p ∧
      (coordForm χ p σ₁ (Ψ y)).compContinuousLinearMap (fderiv ℝ Ψ y) = coordForm χ p σ₀ y} ∈
      𝓝 (u₀, (0 : N)) := by
    have hΨ : ∀ᶠ y in 𝓝 (u₀, (0 : N)), Ψ y ∈ coordDomain χ p :=
      Ψ.continuous.continuousAt.preimage_mem_nhds
        (by rw [hΨy₀]; exact (isOpen_coordDomain χ p).mem_nhds hy₀D)
    filter_upwards [(isOpen_coordDomain χ p).mem_nhds hy₀D, hΨ, hpull] with y h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨U, hUsub, hUo, hy₀U⟩ := mem_nhds_iff.1 hU
  -- `Φ = χ⁻¹ ∘ Ψ ∘ χ` on the points whose coordinates lie in `U`.
  let S : Set M := χ.source ∩ χ ⁻¹' U
  have hS : IsOpen S := χ.toOpenPartialHomeomorph.isOpen_inter_preimage hUo
  let Φ : PartialDiffeomorph I I M M ∞ :=
    ((χ.trans Ψ.toPartialDiffeomorph).trans χ.symm).restrOpen S hS
  have hΦ (x : M) : Φ x = χ.symm (Ψ (χ x)) := by
    simp [Φ, PartialDiffeomorph.trans_toPartialEquiv]
  have hΦS : Φ.source = S := by
    rw [PartialDiffeomorph.restrOpen_source]
    refine Subset.antisymm inter_subset_right fun x hx ↦ ⟨?_, hx⟩
    simpa [PartialDiffeomorph.trans_toPartialEquiv] using ⟨hx.1, (hUsub hx.2).2.1.1⟩
  have hχΦ {x : M} (hx : x ∈ S) : χ (Φ x) = Ψ (χ x) := by
    rw [hΦ]
    exact χ.toPartialEquiv.right_inv (hUsub hx.2).2.1.1
  have hχc : ContinuousAt χ p := (χ.mdifferentiableAt (by simp) hp).continuousAt
  have hpS : p ∈ S := ⟨hp, by rw [mem_preimage, hy₀]; exact hy₀U⟩
  refine ⟨Φ, hΦS ▸ hpS, ?_, fun x hx v w ↦ ?_⟩
  · -- Points near `p` with coordinates in `X × {0}` are fixed.
    have hfst : ContinuousAt (fun x ↦ (χ x).1) p := continuous_fst.continuousAt.comp hχc
    filter_upwards [hS.mem_nhds hpS,
      hfst.eventually (hfix : ∀ᶠ q in 𝓝 u₀, Ψ (q, 0) = (q, 0))] with x hxS hxfix hx0
    have hχx : χ x = ((χ x).1, 0) := Prod.ext rfl hx0
    refine ⟨hΦS ▸ hxS, ?_⟩
    rw [hΦ, hχx, hxfix, ← hχx]
    exact χ.toPartialEquiv.left_inv hxS.1
  · -- The pullback identity, transported from the flat one.
    rw [hΦS] at hx
    obtain ⟨-, hΨD, hpullx⟩ := hUsub hx.2
    have hxp : x ∈ (extChartAt I p).source := by
      have h := (hUsub hx.2).1.2
      rwa [mem_preimage, PartialDiffeomorph.symm_toPartialEquiv,
        χ.toPartialEquiv.left_inv hx.1] at h
    refine eval₂_mfderiv_eq_of_comp_eventuallyEq χ p hx.1 hxp ?_ ?_
      (Φ.mdifferentiableAt (by simp) (hΦS ▸ hx))
      (Ψ.contMDiff.contDiff.differentiable (by simp) _) ?_ hpullx v w
    · rw [hΦ]
      exact χ.toPartialEquiv.map_target hΨD.1
    · rw [hΦ]
      exact hΨD.2
    · filter_upwards [hS.mem_nhds hx] with x' hx' using hχΦ hx'

end Adapted

section Immersion

variable {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] {i : Q → M} {q₀ : Q}
  (hi : Manifold.IsImmersionAt J I ∞ i q₀)

/-- Adapted coordinates of an immersion: its codomain chart followed by the inverse of its
splitting `E' × F ≃ E`. In them `i` reads `q ↦ (φ q, 0)` on the source of its domain chart
`φ`. -/
private def immersionChart :
    PartialDiffeomorph I 𝓘(ℝ, E' × hi.complement) M (E' × hi.complement) ∞ :=
  (hi.codChart.toPartialDiffeomorphOfMemMaximalAtlas hi.codChart_mem_maximalAtlas).trans
    hi.equiv.symm.toPartialDiffeomorph

omit [IsManifold I ∞ M] [J.Boundaryless] in
private theorem mem_immersionChart_source {q : Q} (hq : q ∈ hi.domChart.source) :
    i q ∈ (immersionChart hi).source := by
  simpa [immersionChart, PartialDiffeomorph.trans_toPartialEquiv] using
    hi.source_subset_preimage_source hq

omit [IsManifold I ∞ M] [J.Boundaryless] in
private theorem immersionChart_apply {q : Q} (hq : q ∈ hi.domChart.source) :
    immersionChart hi (i q) = (hi.domChart.extend J q, 0) := by
  have hq' : q ∈ (hi.domChart.extend J).source := by rwa [hi.domChart.extend_source]
  have h := hi.writtenInCharts ((hi.domChart.extend J).map_source hq')
  simp only [comp_apply, (hi.domChart.extend J).left_inv hq'] at h
  have hχ : immersionChart hi (i q) = hi.equiv.symm (hi.codChart.extend I (i q)) := by
    simp [immersionChart]
  rw [hχ, h, ContinuousLinearEquiv.symm_apply_apply]

/-- Equal pullbacks along `i` at `q` give coordinate expressions in the adapted coordinates which
agree on `E' × {0}` at the coordinates of `i q`. -/
private theorem coordForm_immersionChart_inl (p : M) {q : Q} (hq : q ∈ hi.domChart.source)
    (hqp : i q ∈ (extChartAt I p).source) {σ₀ σ₁ : SmoothTwoForm I M}
    (h : mpullback J I i σ₁.1 q = mpullback J I i σ₀.1 q) :
    (coordForm (immersionChart hi) p σ₁ (hi.domChart.extend J q, 0)).compContinuousLinearMap
        (.inl ℝ E' hi.complement) =
      (coordForm (immersionChart hi) p σ₀ (hi.domChart.extend J q, 0)).compContinuousLinearMap
        (.inl ℝ E' hi.complement) := by
  set χ := immersionChart hi
  -- The extended domain chart, as a partial diffeomorphism.
  set φ := hi.domChart.toPartialDiffeomorphOfMemMaximalAtlas hi.domChart_mem_maximalAtlas
  have hφ : ⇑φ.toPartialEquiv = hi.domChart.extend J := by
    rw [OpenPartialHomeomorph.coe_toPartialDiffeomorphOfMemMaximalAtlas,
      OpenPartialHomeomorph.extend_coe]
  have hqφ : q ∈ φ.source := by simpa [φ] using hq
  -- The derivative of `i` in adapted coordinates is `inl` after the derivative of the chart.
  have hcomm : χ ∘ i =ᶠ[𝓝 q] ContinuousLinearMap.inl ℝ E' hi.complement ∘ φ := by
    filter_upwards [hi.domChart.open_source.mem_nhds hq] with q' hq'
    rw [comp_apply, immersionChart_apply hi hq', hφ]
    rfl
  have hd (a : TangentSpace J q) :
      mvfderiv I χ (i q) (mfderiv J I i q a) = (mvfderiv J φ q a, 0) := by
    rw [← mvfderiv_comp_apply q (χ.mdifferentiableAt (by simp) (mem_immersionChart_source hi hq))
      ((hi.contMDiffOn.mdifferentiableOn (by simp)).mdifferentiableAt
        (hi.domChart.open_source.mem_nhds hq)), hcomm.mvfderiv_eq,
      ContinuousLinearMap.mvfderiv_comp_apply _ (φ.mdifferentiableAt (by simp) hqφ)]
    rfl
  have hχq : χ (i q) = (hi.domChart.extend J q, 0) := immersionChart_apply hi hq
  ext a
  obtain ⟨a₀, ha₀⟩ := surjective_mvfderiv φ hqφ (a 0)
  obtain ⟨a₁, ha₁⟩ := surjective_mvfderiv φ hqφ (a 1)
  have key (σ : SmoothTwoForm I M) :
      (coordForm χ p σ (hi.domChart.extend J q, 0)).compContinuousLinearMap
          (.inl ℝ E' hi.complement) a = mpullback J I i σ.1 q ![a₀, a₁] := by
    rw [mpullback_apply_pair, ← SmoothBundleForm.eval₂_apply,
      eval₂_eq_coordForm χ p σ (mem_immersionChart_source hi hq) hqp, hd, hd, ha₀, ha₁, hχq,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [key, key, h]

end Immersion

variable [FiniteDimensional ℝ E]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q]

/-- **The point-germ relative Darboux theorem.** Let `i : Q → M` be an immersion at `q₀` between
boundaryless manifolds, `M` finite-dimensional, and let `σ₀`, `σ₁` be closed two-forms on `M`,
nondegenerate at `i q₀`, whose pullbacks along `i` agree near `q₀`. Then some smooth partial
diffeomorphism `Φ` of `M`, whose source contains `i q₀`, fixes `i q` for every `q` near `q₀` and
pulls `σ₁` back to `σ₀` on its source. The pullbacks along `i` may be degenerate, of any rank. -/
theorem exists_partialDiffeomorph_fix_eval₂_mfderiv_eq_of_mpullback_eq
    {σ₀ σ₁ : SmoothTwoForm I M} (hσ₀ : σ₀.IsClosed) (hσ₁ : σ₁.IsClosed)
    {i : Q → M} {q₀ : Q} (hi : Manifold.IsImmersionAt J I ∞ i q₀)
    (hnd₀ : (σ₀.bilinFormAt (i q₀)).Nondegenerate) (hnd₁ : (σ₁.bilinFormAt (i q₀)).Nondegenerate)
    (htan : ∀ᶠ q in 𝓝 q₀, mpullback J I i σ₁.1 q = mpullback J I i σ₀.1 q) :
    ∃ Φ : PartialDiffeomorph I I M M ∞, i q₀ ∈ Φ.source ∧
      (∀ᶠ q in 𝓝 q₀, i q ∈ Φ.source ∧ Φ (i q) = i q) ∧
      ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
        σ₁.eval₂ (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) = σ₀.eval₂ x v w := by
  have : FiniteDimensional ℝ (E' × hi.complement) :=
    LinearEquiv.finiteDimensional hi.equiv.symm.toLinearEquiv
  have : FiniteDimensional ℝ E' :=
    Module.Finite.of_surjective (LinearMap.fst ℝ E' hi.complement) Prod.fst_surjective
  have : FiniteDimensional ℝ hi.complement :=
    Module.Finite.of_surjective (LinearMap.snd ℝ E' hi.complement) Prod.snd_surjective
  set φ := hi.domChart.extend J
  have hq₀ : q₀ ∈ φ.source := by rw [hi.domChart.extend_source]; exact hi.mem_domChart_source
  have hφo : hi.domChart.source ∈ 𝓝 q₀ :=
    hi.domChart.open_source.mem_nhds hi.mem_domChart_source
  have hχp : immersionChart hi (i q₀) = (φ q₀, 0) :=
    immersionChart_apply hi hi.mem_domChart_source
  -- The tangency hypothesis in adapted coordinates, at the points `(u, 0)` with `u` near `φ q₀`.
  have htan' : ∀ᶠ u in 𝓝 (immersionChart hi (i q₀)).1,
      (coordForm (immersionChart hi) (i q₀) σ₁ (u, 0)).compContinuousLinearMap
          (.inl ℝ E' hi.complement) =
        (coordForm (immersionChart hi) (i q₀) σ₀ (u, 0)).compContinuousLinearMap
          (.inl ℝ E' hi.complement) := by
    have hq : ∀ᶠ q in 𝓝 q₀, q ∈ hi.domChart.source ∧ i q ∈ (extChartAt I (i q₀)).source ∧
        mpullback J I i σ₁.1 q = mpullback J I i σ₀.1 q := by
      filter_upwards [hφo, hi.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := I) (i q₀)).mem_nhds (mem_extChartAt_source _)), htan]
        with q h₁ h₂ h₃
      exact ⟨h₁, h₂, h₃⟩
    have hc := (hi.domChart.continuousAt_extend_symm (I := J) hi.mem_domChart_source).tendsto
    rw [φ.left_inv hq₀] at hc
    rw [hχp]
    filter_upwards [hi.domChart.isOpen_extend_target.mem_nhds (φ.map_source hq₀),
      hc.eventually hq] with u hu ⟨hqs, hqp, hqt⟩
    rw [← φ.right_inv hu]
    exact coordForm_immersionChart_inl hi (i q₀) hqs hqp hqt
  obtain ⟨Φ, hpΦ, hfix, hpull⟩ := exists_partialDiffeomorph_of_coordForm (immersionChart hi)
    (mem_immersionChart_source hi hi.mem_domChart_source) (by rw [hχp]) hσ₀ hσ₁ hnd₀ hnd₁ htan'
  refine ⟨Φ, hpΦ, ?_, hpull⟩
  filter_upwards [hφo, hi.continuousAt.eventually hfix] with q hq hqfix
  exact hqfix (by rw [immersionChart_apply hi hq])

end TauCeti.SmoothTwoForm
