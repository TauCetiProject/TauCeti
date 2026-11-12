/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.GroupAction.CompactLinearization
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Darboux.Basic
import TauCeti.RepresentationTheory.Continuous.InvariantNeighborhood

/-!
# Equivariant Darboux charts at fixed points of compact group actions

Let a compact group `G`, itself a manifold without boundary, act smoothly on a boundaryless
manifold `M` with finite-dimensional model space `E`, preserving a symplectic form `σ`, and let
`x₀` be a fixed point of the action. This file proves the **equivariant Darboux theorem**: there is
a smooth partial diffeomorphism `chart` from a `G`-invariant neighbourhood of `x₀` into `E`, with
`chart x₀ = 0`, in which

* `G` acts linearly, through its isotropy representation `ρ g = d(g • ·)ₓ₀` on `T_{x₀} M = E`:
  `chart (g • z) = ρ g (chart z)`;
* `σ` is the constant form `σ_{x₀}`: `σ_z(v, w) = σ_{x₀}(d chart_z v, d chart_z w)`

(`TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart`). Since `ρ g` is the
differential of a symplectomorphism fixing `x₀`, it preserves `σ_{x₀}`, so `G` acts on the chart
by linear symplectic maps of `(E, σ_{x₀})`. This is the local model of a compact symplectic action
near a fixed point, in which the action and the form are both linear.

The proof combines two existing results. Bochner's linearization theorem
(`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`) gives a smooth chart `e` at `x₀`,
with invariant domain and derivative the identity at `x₀`, in which `G` acts by `ρ`. Read in `e`,
the form `σ` becomes a closed `ρ`-invariant two-form `ζ` on an open subset of `E`, equal to
`σ_{x₀}` at `0`; it is computed through the preferred extended chart at `x₀`, where closedness of
`σ` is the vanishing of the flat exterior derivative, and transported to `e` by naturality of the
exterior derivative under pullback. The flat equivariant Darboux theorem
(`TauCeti.exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq`), applied on a
`ρ`-invariant convex neighbourhood of `0`, gives a `ρ`-equivariant diffeomorphism `ψ` of `E` fixing
`0` with `ψ^* ζ = ζ(0) = σ_{x₀}`, and the chart is `ψ⁻¹ ∘ e`.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart`: equivariant Darboux charts
  at a fixed point of a smooth symplectic action of a compact Lie group.

## References

* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984 (the equivariant Darboux theorem, by an equivariant Moser argument).
* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
-/

public section

noncomputable section

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

section ChartForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A two-form `form` read in the coordinates of a chart `e : M → E`: its coordinate expression in
the preferred extended chart at `x₀`, pulled back along the transition `y ↦ χ (e⁻¹ y)` from `e` to
that chart. It represents `form` on the open set `e.target ∩ e⁻¹ ⁻¹' χ.source`
(`chartForm_apply`). -/
private def chartForm (form : SmoothTwoForm I M) (x₀ : M) (e : OpenPartialHomeomorph M E) :
    E → E [⋀^Fin 2]→L[ℝ] ℝ :=
  fun y ↦ (RoughForm.inChartAt form.1 x₀ (extChartAt I x₀ (e.symm y))).compContinuousLinearMap
    (fderiv ℝ (fun y ↦ extChartAt I x₀ (e.symm y)) y)

/-- The transition from a smooth chart `e` to the preferred extended chart at `x₀` is smooth on the
open set where it is defined, and takes values in the interior of the extended chart target. -/
private theorem contDiffOn_extChartAt_comp_symm {e : OpenPartialHomeomorph M E}
    (he : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target) (x₀ : M) :
    IsOpen (e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source) ∧
      ContDiffOn ℝ ∞ (fun y ↦ extChartAt I x₀ (e.symm y))
        (e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source) ∧
      MapsTo (fun y ↦ extChartAt I x₀ (e.symm y))
        (e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source) (interior (extChartAt I x₀).target) := by
  refine ⟨e.isOpen_inter_preimage_symm (isOpen_extChartAt_source x₀), ?_, fun y hy ↦ ?_⟩
  · rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (n := ∞)).comp (he.mono inter_subset_left)
      fun y hy ↦ by simpa only [extChartAt_source] using hy.2
  · rw [(isOpen_extChartAt_target x₀).interior_eq]
    exact (extChartAt I x₀).map_source hy.2

/-- The coordinate expression of a smooth two-form in a smooth chart is smooth. -/
private theorem contDiffOn_chartForm (form : SmoothTwoForm I M) {e : OpenPartialHomeomorph M E}
    (he : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target) (x₀ : M) :
    ContDiffOn ℝ ∞ (chartForm form x₀ e) (e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source) := by
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨hD, hτ, hτW⟩ := contDiffOn_extChartAt_comp_symm he x₀
  have hη := form.isSmoothForm.contDiffOn_inChartAt_interior_target (n := ∞) x₀
  exact (((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (E := E) (F := E) (G := ℝ)
    (ι := Fin 2) ∞).comp_contDiffOn (hτ.fderiv_of_isOpen hD (by simp))).clm_apply
    (hη.comp hτ hτW)).congr fun y _ ↦ by simp [chartForm]

/-- The coordinate expression of a closed two-form in a smooth chart is closed. -/
private theorem extDeriv_chartForm {form : SmoothTwoForm I M} (hform : form.IsClosed)
    {e : OpenPartialHomeomorph M E} (he : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target) (x₀ : M)
    {y : E} (hy : y ∈ e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source) :
    extDeriv (chartForm form x₀ e) y = 0 := by
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨hD, hτ, hτW⟩ := contDiffOn_extChartAt_comp_symm he x₀
  have hη := form.isSmoothForm.contDiffOn_inChartAt_interior_target (n := ∞) x₀
  unfold chartForm
  rw [extDeriv_pullback (f := fun y ↦ extChartAt I x₀ (e.symm y))
    ((hη.differentiableOn (by simp)).differentiableAt (isOpen_interior.mem_nhds (hτW hy)))
    (hτ.contDiffAt (hD.mem_nhds hy)) (by simp),
    hform.extDeriv_inChartAt_eq_zero x₀ (hτW hy)]
  ext
  simp

omit [I.Boundaryless] in
/-- On the open set where it is defined, the coordinate expression of `form` in a smooth chart `e`
evaluates `form` on the images of vectors under the differential of `e⁻¹`. -/
private theorem chartForm_apply (form : SmoothTwoForm I M) {e : OpenPartialHomeomorph M E}
    (he : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target) (x₀ : M) {y : E}
    (hy : y ∈ e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source) (u w : E) :
    chartForm form x₀ e y ![u, w] = form.eval₂ (e.symm y)
      (mfderiv 𝓘(ℝ, E) I e.symm y u) (mfderiv 𝓘(ℝ, E) I e.symm y w) := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hesd : MDifferentiableAt 𝓘(ℝ, E) I e.symm y :=
    (he.contMDiffAt (e.open_target.mem_nhds hy.1)).mdifferentiableAt (by simp)
  have hχd : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) (e.symm y) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source, mem_preimage] using hy.2)
  -- The chain rule for the transition `χ ∘ e⁻¹`.
  have hd (a : E) : fderiv ℝ (fun y ↦ extChartAt I x₀ (e.symm y)) y a =
      mvfderiv I (extChartAt I x₀) (e.symm y) (mfderiv 𝓘(ℝ, E) I e.symm y a) :=
    (mvfderiv_eq_fderiv_apply _ y a).symm.trans (mvfderiv_comp_apply y hχd hesd a)
  rw [SmoothBundleForm.eval₂_apply, RoughForm.apply_eq_inChartAt_mvfderiv form.1 hy.2]
  simp only [chartForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i
  · exact hd u
  · exact hd w

omit [I.Boundaryless] in
/-- Evaluation of a two-form only depends on the base point through its value. -/
private theorem eval₂_eq_of_eq (form : SmoothTwoForm I M) {p q : M} (h : p = q) (a b : E) :
    form.eval₂ p a b = form.eval₂ q a b := by
  subst h
  rfl

end ChartForm

variable {E H M EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [MulAction G M] [ContMDiffSMul IG I ∞ G M]

variable (IG) in
/-- A two-form invariant under the action is preserved by the differential of every element. -/
private theorem eval₂_smul_mfderiv {form : SmoothTwoForm I M}
    (hG : ∀ g : G, SmoothForm.mpullback (g • ·)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) form = form)
    (g : G) (z : M) (a b : TangentSpace I z) :
    form.eval₂ (g • z) (mfderiv I I (g • ·) z a) (mfderiv I I (g • ·) z b) =
      form.eval₂ z a b := by
  simpa only [SmoothForm.eval₂_mpullback] using
    congrArg (fun φ : SmoothTwoForm I M ↦ φ.eval₂ z a b) (hG g)

variable (IG) in
/-- If a chart `e` intertwines the action of `G` with a linear representation `ρ`, then the
coordinate expression in `e` of a `G`-invariant two-form is `ρ`-invariant. -/
private theorem compContinuousLinearMap_chartForm_eq {form : SmoothTwoForm I M}
    (hG : ∀ g : G, SmoothForm.mpullback (g • ·)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) form = form)
    {e : OpenPartialHomeomorph M E} (he : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    {ρ : ContRepresentation ℝ G E}
    (hequiv : ∀ g : G, ∀ z ∈ e.source, g • z ∈ e.source ∧ e (g • z) = ρ g (e z))
    (x₀ : M) (g : G) {y : E} (hy : y ∈ e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source)
    (hgy : ρ g y ∈ e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source) :
    (chartForm form x₀ e (ρ g y)).compContinuousLinearMap (ρ g) = chartForm form x₀ e y := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- Near `y`, `e⁻¹ ∘ ρ g = (g • ·) ∘ e⁻¹`; differentiate this identity at `y`.
  have hesρ {y' : E} (hy' : y' ∈ e.target) : e.symm (ρ g y') = g • e.symm y' := by
    obtain ⟨hgz, hegz⟩ := hequiv g (e.symm y') (e.map_target hy')
    rw [e.right_inv hy'] at hegz
    rw [← hegz, e.left_inv hgz]
  have hesd {y' : E} (hy' : y' ∈ e.target) : MDifferentiableAt 𝓘(ℝ, E) I e.symm y' :=
    (he.contMDiffAt (e.open_target.mem_nhds hy')).mdifferentiableAt hinf
  have hsmul : MDifferentiableAt I I (g • ·) (e.symm y) :=
    ((ContMDiffSMul.contMDiff_const_smul (I := IG) (n := ∞) g).mdifferentiable hinf) _
  have hcomp : (e.symm ∘ ρ g : E → M) =ᶠ[𝓝 y] (g • ·) ∘ e.symm :=
    eventually_of_mem (e.open_target.mem_nhds hy.1) fun y' hy' ↦ hesρ hy'
  have hder (a : E) : mfderiv 𝓘(ℝ, E) I e.symm (ρ g y) (ρ g a) =
      mfderiv I I (g • ·) (e.symm y) (mfderiv 𝓘(ℝ, E) I e.symm y a) := by
    have h := hcomp.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := I)
    rw [mfderiv_comp y (hesd hgy.1)
        ((ρ g).mdifferentiableAt : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (ρ g) y),
      mfderiv_comp y hsmul (hesd hy.1), (ρ g).mfderiv_eq] at h
    exact DFunLike.congr_fun h a
  -- Evaluate both sides on a pair of vectors.
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  have hρv : ρ g ∘ v = ![ρ g (v 0), ρ g (v 1)] := by
    ext i
    fin_cases i <;> rfl
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hρv]
  conv_rhs => rw [hv]
  rw [chartForm_apply form he x₀ hgy, chartForm_apply form he x₀ hy, hder, hder]
  exact (eval₂_eq_of_eq form (hesρ hy.1) _ _).trans (eval₂_smul_mfderiv IG hG g _ _ _)

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IG.Boundaryless] [IsTopologicalGroup G]
  [CompactSpace G] [IsManifold IG ∞ G]

variable (IG) in
/-- **Equivariant Darboux theorem.** Let a compact group `G`, a boundaryless manifold, act smoothly
on a boundaryless manifold `M` by symplectomorphisms of a symplectic form `form`, and let `x₀` be a
fixed point. Then there is a smooth partial diffeomorphism `chart` into the model space `E`, with
`G`-invariant source containing `x₀` and `chart x₀ = 0`, which intertwines the action with the
isotropy representation `ρ g = mfderiv I I (g • ·) x₀` of `G` on `T_{x₀} M = E`, and in which
`form` is the constant form `form_{x₀}`. The isotropy representation preserves `form_{x₀}`, so `G`
acts in the chart by linear symplectic maps. -/
theorem IsSymplectic.exists_equivariant_darbouxChart {form : SmoothTwoForm I M}
    (hform : form.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (g • ·)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) form = form)
    {x₀ : M} (hx₀ : ∀ g : G, g • x₀ = x₀) :
    ∃ (ρ : ContRepresentation ℝ G E) (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞),
      Continuous ρ ∧ (∀ g : G, ρ g = mfderiv I I (g • ·) x₀) ∧
      (∀ g : G, ∀ u w : E, form.eval₂ x₀ (ρ g u) (ρ g w) = form.eval₂ x₀ u w) ∧
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ g : G, ∀ z ∈ chart.source, g • z ∈ chart.source ∧ chart (g • z) = ρ g (chart z)) ∧
      ∀ z ∈ chart.source, ∀ v w : TangentSpace I z,
        form.eval₂ z v w = form.eval₂ x₀ (mvfderiv I chart z v) (mvfderiv I chart z w) := by
  -- Bochner's linearizing chart `e` at `x₀`, as a partial diffeomorphism `eP`.
  obtain ⟨ρ, e, hρc, hx₀e, he0, hes, hesymm, hequiv, hρ, hde⟩ :=
    exists_equivariant_contMDiff_chart_of_compactSpace (I := I) (n := ⊤) IG le_top hx₀
  let eP : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := hes
      contMDiffOn_invFun := hesymm }
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hed {z : M} (hz : z ∈ e.source) : MDifferentiableAt I 𝓘(ℝ, E) e z :=
    (hes.contMDiffAt (e.open_source.mem_nhds hz)).mdifferentiableAt hinf
  have hesd {y : E} (hy : y ∈ e.target) : MDifferentiableAt 𝓘(ℝ, E) I e.symm y :=
    (hesymm.contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt hinf
  -- `d(e⁻¹)` undoes `de`, and `de` is the identity at `x₀`.
  have hese {z : M} (hz : z ∈ e.source) (v : TangentSpace I z) :
      mfderiv 𝓘(ℝ, E) I e.symm (e z) (mfderiv I 𝓘(ℝ, E) e z v) = v :=
    e.mfderiv_symm_apply_mfderiv_apply hz (hed hz) (hesd (e.map_source hz)) v
  have hes0 (a : E) : mfderiv 𝓘(ℝ, E) I e.symm 0 a = a := by
    have h := hese hx₀e a
    rw [hde.mfderiv, he0] at h
    exact h
  -- `form` read in the coordinates of `e` is a smooth closed form `ζ` on the open set `D`, equal
  -- to `form_{x₀}` at `0`.
  let D : Set E := e.target ∩ e.symm ⁻¹' (extChartAt I x₀).source
  let ζ := chartForm form x₀ e
  have hD : IsOpen D := (contDiffOn_extChartAt_comp_symm hesymm x₀).1
  have h0D : 0 ∈ D := by
    refine ⟨he0 ▸ e.map_source hx₀e, ?_⟩
    rw [mem_preimage, ← he0, e.left_inv hx₀e]
    exact mem_extChartAt_source x₀
  have hζ0 (u w : E) : ζ 0 ![u, w] = form.eval₂ x₀ u w := by
    rw [chartForm_apply form hesymm x₀ h0D, hes0, hes0,
      eval₂_eq_of_eq form (by rw [← he0, e.left_inv hx₀e])]
  -- An invariant convex neighbourhood of `0` inside `D`, and the flat equivariant Darboux theorem.
  have hρb : Bornology.IsBounded (range ρ) := (isCompact_range hρc).isBounded
  have hρ0 (g : G) : ρ g 0 = 0 := map_zero (ρ g)
  obtain ⟨U₀, ⟨hU₀o, -, h0U₀, hU₀ρ⟩, hU₀D⟩ :=
    (ContRepresentation.nhds_basis_isOpen_convex_mapsTo ρ hρb hρ0).mem_iff.1 (hD.mem_nhds h0D)
  have hU₀D : U₀ ⊆ D := hU₀D
  have hζinv (g : G) (y : E) (hy : y ∈ U₀) :
      (ζ (ρ g y)).compContinuousLinearMap (ρ g) = ζ y :=
    compContinuousLinearMap_chartForm_eq IG hG hesymm hequiv x₀ g (hU₀D hy) (hU₀D (hU₀ρ g hy))
  have hnd (v : E) (hv : ∀ w, ζ 0 ![v, w] = 0) : v = 0 :=
    isNondegenerate_iff_separatingLeft.1 hform.isNondegenerate x₀ v fun w ↦
      (hζ0 v w).symm.trans (hv w)
  obtain ⟨ψ, U, hUo, h0U, -, hUρ, hψ0, hψρ, hψζ⟩ :=
    exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq hρb hρ0 (r := ⊤) le_top
      hU₀o h0U₀ ((contDiffOn_chartForm form hesymm x₀).mono hU₀D)
      (fun y hy ↦ extDeriv_chartForm hform.isClosed hesymm x₀ (hU₀D hy)) hnd hζinv
  -- The chart is `ψ⁻¹ ∘ e`, on the invariant open set where `ψ⁻¹ ∘ e` lands in `U ∩ ψ⁻¹ U₀`.
  let U' : Set E := U ∩ ψ ⁻¹' U₀
  have hU'ρ (g : G) {y : E} (hy : y ∈ U') : ρ g y ∈ U' :=
    ⟨hUρ g hy.1, by rw [mem_preimage, hψρ g y hy.1]; exact hU₀ρ g hy.2⟩
  let S : Set M := e.source ∩ e ⁻¹' (ψ.symm ⁻¹' U')
  have hS : IsOpen S :=
    e.isOpen_inter_preimage ((hUo.inter (hU₀o.preimage ψ.continuous)).preimage ψ.symm.continuous)
  let chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    (eP.restrOpen S hS).trans ψ.symm.toPartialDiffeomorph
  have hsrc : chart.source = S := by
    simp [chart, eP, S, PartialDiffeomorph.restrOpen_source]
  have hcoe : ⇑chart = ψ.symm ∘ e := by
    rw [PartialDiffeomorph.coe_trans, PartialDiffeomorph.coe_restrOpen]
    simp [eP]
  have hψs0 : ψ.symm 0 = 0 := (congrArg ψ.symm hψ0.symm).trans (ψ.symm_apply_apply 0)
  refine ⟨ρ, chart, hρc, hρ, fun g u w ↦ ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ g]
    exact (eval₂_eq_of_eq form (hx₀ g).symm _ _).trans (eval₂_smul_mfderiv IG hG g x₀ u w)
  · rw [hsrc]
    refine ⟨hx₀e, ?_⟩
    simp only [mem_preimage, he0, hψs0]
    exact ⟨h0U, by rw [mem_preimage, hψ0]; exact h0U₀⟩
  · rw [hcoe, comp_apply, he0, hψs0]
  · intro g z hz
    rw [hsrc] at hz ⊢
    obtain ⟨hgz, hegz⟩ := hequiv g z hz.1
    have hy : ψ.symm (e z) ∈ U' := hz.2
    have hψ' : ψ.symm (ρ g (e z)) = ρ g (ψ.symm (e z)) := by
      have h := hψρ g _ hy.1
      rw [ψ.apply_symm_apply] at h
      rw [← h, ψ.symm_apply_apply]
    refine ⟨⟨hgz, ?_⟩, ?_⟩
    · rw [mem_preimage, mem_preimage, hegz, hψ']
      exact hU'ρ g hy
    · rw [hcoe, comp_apply, comp_apply, hegz, hψ']
  · intro z hz v w
    rw [hsrc] at hz
    have hpD : e z ∈ D := hU₀D (by simpa only [mem_preimage, ψ.apply_symm_apply] using hz.2.2)
    have hψψ (a : E) : fderiv ℝ ψ (ψ.symm (e z)) (fderiv ℝ ψ.symm (e z) a) = a :=
      ψ.fderiv_apply_fderiv_symm_apply hinf (e z) a
    have hψζ' (a b : E) : ζ (e z) ![fderiv ℝ ψ (ψ.symm (e z)) a, fderiv ℝ ψ (ψ.symm (e z)) b] =
        ζ 0 ![a, b] := by
      have h := DFunLike.congr_fun (hψζ _ hz.2.1) ![a, b]
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, ψ.apply_symm_apply] at h
      rw [← h]
      congr 1
      ext i
      fin_cases i <;> rfl
    have hchart (a : TangentSpace I z) :
        mvfderiv I chart z a = fderiv ℝ ψ.symm (e z) (mfderiv I 𝓘(ℝ, E) e z a) := by
      rw [hcoe]
      exact (mvfderiv_comp_apply_of_differentiableAt (ψ.symm.differentiable hinf (e z))
        (hed hz.1) a).trans (congrArg _ (mvfderiv_apply_eq_mfderiv_apply _ _ _))
    have he' := chartForm_apply form hesymm x₀ hpD (mfderiv I 𝓘(ℝ, E) e z v)
      (mfderiv I 𝓘(ℝ, E) e z w)
    rw [hese hz.1 v, hese hz.1 w] at he'
    calc form.eval₂ z v w = form.eval₂ (e.symm (e z)) v w :=
          eval₂_eq_of_eq form (e.left_inv hz.1).symm v w
      _ = ζ (e z) ![mfderiv I 𝓘(ℝ, E) e z v, mfderiv I 𝓘(ℝ, E) e z w] := he'.symm
      _ = ζ 0 ![fderiv ℝ ψ.symm (e z) (mfderiv I 𝓘(ℝ, E) e z v),
            fderiv ℝ ψ.symm (e z) (mfderiv I 𝓘(ℝ, E) e z w)] :=
          (congrArg₂ (fun a b : E ↦ ζ (e z) ![a, b]) (hψψ _).symm (hψψ _).symm).trans (hψζ' _ _)
      _ = form.eval₂ x₀ (mvfderiv I chart z v) (mvfderiv I chart z w) :=
          (hζ0 _ _).trans (congrArg₂ (form.eval₂ x₀) (hchart v) (hchart w)).symm

end SmoothTwoForm

end TauCeti
