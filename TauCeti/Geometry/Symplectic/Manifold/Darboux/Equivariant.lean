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

import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.TwoForm.Pullback
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
differential of a symplectomorphism fixing `x₀`, it preserves `σ_{x₀}`
(`TauCeti.SmoothTwoForm.eval₂_mfderiv_of_mpullback_eq`), so `G` acts on the chart
by linear symplectic maps of `(E, σ_{x₀})`. This is the local model of a compact symplectic action
near a fixed point, in which the action and the form are both linear.

The proof combines two existing results. Bochner's linearization theorem
(`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`) gives a smooth chart `e` at `x₀`,
with invariant domain and derivative the identity at `x₀`, in which `G` acts by `ρ`. Pulled back
along `e⁻¹`, the form `σ` becomes a two-form `ζ` on the open set `e.target ⊆ E`, equal to `σ_{x₀}`
at `0`. It is closed by naturality of the exterior derivative under pullback, and `ρ`-invariant
because `e⁻¹ ∘ ρ g = (g • ·) ∘ e⁻¹` and `σ` is `G`-invariant. The flat equivariant Darboux theorem
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

variable {E H M EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [MulAction G M] [ContMDiffSMul IG I ∞ G M]

/-- Evaluation of a two-form only depends on the base point through its value. -/
private theorem eval₂_eq_of_eq (form : SmoothTwoForm I M) {p q : M} (h : p = q) (a b : E) :
    form.eval₂ p a b = form.eval₂ q a b := by
  subst h
  rfl

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
  -- `form` read in the coordinates of `e`, that is pulled back along `e⁻¹`, is a smooth closed
  -- form `ζ` on the open set `D = e.target`, equal to `form_{x₀}` at `0`.
  let D : Set E := e.target
  let ζ : E → E [⋀^Fin 2]→L[ℝ] ℝ := TauCeti.mpullback 𝓘(ℝ, E) I e.symm form.1
  have hD : IsOpen D := e.open_target
  have h0D : 0 ∈ D := he0 ▸ e.map_source hx₀e
  have hζapp (y u w : E) : ζ y ![u, w] =
      form.eval₂ (e.symm y) (mfderiv 𝓘(ℝ, E) I e.symm y u) (mfderiv 𝓘(ℝ, E) I e.symm y w) := by
    rw [SmoothBundleForm.eval₂_apply]
    exact mpullback_apply_pair _ _ _ _ _
  have hζ0 (u w : E) : ζ 0 ![u, w] = form.eval₂ x₀ u w := by
    rw [hζapp, hes0, hes0, eval₂_eq_of_eq form (by rw [← he0, e.left_inv hx₀e])]
  have hζs : ContDiffOn ℝ ∞ ζ D := fun y hy ↦
    RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      ((form.contMDiff (e.symm y)).mpullback_form (hesymm.contMDiffAt (hD.mem_nhds hy))
        (by simp)).contMDiffWithinAt
  -- Closedness of `ζ` is naturality of the exterior derivative under pullback.
  have hζc {y : E} (hy : y ∈ D) : extDeriv ζ y = 0 := by
    have hloc : ζ =ᶠ[𝓝[D] y] mpullbackWithin 𝓘(ℝ, E) I e.symm D form.1 :=
      eventually_nhdsWithin_of_forall fun y' hy' ↦
        (mpullbackWithin_eq_mpullback (hD.uniqueMDiffOn y' hy') (hesd hy') _).symm
    rw [← extDerivWithin_of_isOpen hD hy, hloc.extDerivWithin_eq (hloc.self_of_nhdsWithin hy),
      extDerivWithin_mpullbackWithin ((hesymm.of_le (by simp)) y hy) hD.uniqueDiffOn
        (subset_closure (hD.interior_eq.symm ▸ hy)) hy (form.mdifferentiableAt _),
      (SmoothForm.isClosed_def _).1 hform.isClosed, mpullbackWithin_zero]
    rfl
  -- An invariant convex neighbourhood of `0` inside `D`, and the flat equivariant Darboux theorem.
  have hρb : Bornology.IsBounded (range ρ) := (isCompact_range hρc).isBounded
  have hρ0 (g : G) : ρ g 0 = 0 := map_zero (ρ g)
  obtain ⟨U₀, ⟨hU₀o, -, h0U₀, hU₀ρ⟩, hU₀D⟩ :=
    (ContRepresentation.nhds_basis_isOpen_convex_mapsTo ρ hρb hρ0).mem_iff.1 (hD.mem_nhds h0D)
  have hU₀D : U₀ ⊆ D := hU₀D
  -- Near `y ∈ D`, `e⁻¹ ∘ ρ g = (g • ·) ∘ e⁻¹`, so the invariance of `form` makes `ζ` invariant.
  have hesρ (g : G) {y : E} (hy : y ∈ D) : e.symm (ρ g y) = g • e.symm y := by
    obtain ⟨hgz, hegz⟩ := hequiv g (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at hegz
    rw [← hegz, e.left_inv hgz]
  have hζinv (g : G) (y : E) (hy : y ∈ U₀) :
      (ζ (ρ g y)).compContinuousLinearMap (ρ g) = ζ y := by
    have hcomp : (e.symm ∘ ρ g : E → M) =ᶠ[𝓝 y] (g • ·) ∘ e.symm :=
      eventually_of_mem (hD.mem_nhds (hU₀D hy)) fun y' hy' ↦ hesρ g hy'
    have hsmul : MDifferentiableAt I I (g • ·) (e.symm y) :=
      ((ContMDiffSMul.contMDiff_const_smul (I := IG) (n := ∞) g).mdifferentiable hinf) _
    refine (mpullback_comp_apply_of_hasFDerivAt (ρ g).hasFDerivAt
      (hesd (hU₀D (hU₀ρ g hy))) form.1).symm.trans <| (hcomp.mpullback_eq _).trans <|
        (mpullback_comp_at (hesd (hU₀D hy)) hsmul _).trans ?_
    rw [← SmoothForm.coe_mpullback (g • ·) (ContMDiffSMul.contMDiff_const_smul (I := IG) g), hG g]
  have hnd (v : E) (hv : ∀ w, ζ 0 ![v, w] = 0) : v = 0 :=
    isNondegenerate_iff_separatingLeft.1 hform.isNondegenerate x₀ v fun w ↦
      (hζ0 v w).symm.trans (hv w)
  obtain ⟨ψ, U, hUo, h0U, -, hUρ, hψ0, hψρ, hψζ⟩ :=
    exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq hρb hρ0 (r := ⊤) le_top
      hU₀o h0U₀ (hζs.mono hU₀D) (fun y hy ↦ hζc (hU₀D hy)) hnd hζinv
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
    exact (eval₂_eq_of_eq form (hx₀ g).symm _ _).trans
      (eval₂_mfderiv_of_mpullback_eq _ (hG g) x₀ u w)
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
    have he' := hζapp (e z) (mfderiv I 𝓘(ℝ, E) e z v) (mfderiv I 𝓘(ℝ, E) e z w)
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
