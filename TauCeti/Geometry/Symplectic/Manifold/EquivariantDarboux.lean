/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.CompactLinearization
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Symplectic.Darboux.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The equivariant Darboux theorem on manifolds

Let a compact group `G`, itself a manifold without boundary, act smoothly on a finite-dimensional
manifold `M` without boundary, preserving a symplectic form `ω` (`g^* ω = ω` for every `g`), and
let `x₀` be a fixed point of the action. The **equivariant Darboux theorem** says that near `x₀`
there are coordinates in which, simultaneously, `ω` is constant and `G` acts linearly: there is a
smooth chart `φ` around `x₀`, with `G`-invariant domain and `φ x₀ = 0`, such that

* `φ (g • x) = σ g (φ x)`, where `σ g = d(g • ·)_{x₀}` is the isotropy representation of `G` on
  `T_{x₀} M`, and
* `ω_x(v, w) = ω_{x₀}(dφ_x v, dφ_x w)` for every `x` in the domain of `φ`

(`TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart`). So `φ` identifies a
neighbourhood of `x₀` with an invariant open subset of the symplectic representation
`(T_{x₀} M, ω_{x₀}, σ)`, and the action, the form and the fixed point all become linear data.

The proof combines two existing local theorems. Bochner's linearization theorem
(`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`) gives a chart `e` around `x₀` with
`G`-invariant domain and derivative the identity at `x₀`, in which `G` acts by `σ`. The form
`ω' = (e⁻¹)^* ω` on the target of `e` is then closed, smooth and `σ`-invariant, and equals `ω_{x₀}`
at `0`. The flat equivariant Darboux theorem
(`TauCeti.exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq`), whose hypothesis on
`σ` holds because a compact group has bounded image under a continuous representation, gives a
diffeomorphism `ψ` of `T_{x₀} M` commuting with `σ` on an invariant neighbourhood `U` of `0` and
pulling `ω'` back to the constant form `ω'(0)` there. The chart is `φ = ψ⁻¹ ∘ e` on the preimage
of `ψ(U)`.

This is the local model at fixed points of compact symplectic actions, in particular of torus
actions, in the Atiyah–Guillemin–Sternberg convexity theorem: there, choosing a weight
decomposition of the symplectic representation `(T_{x₀} M, ω_{x₀}, σ)` puts a moment map into
its quadratic normal form.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart`: equivariant Darboux
  charts at fixed points of compact group actions by symplectomorphisms.

## References

* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984 (the equivariant Darboux theorem, by an equivariant Moser argument).
* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Mathematica 94 (1994), 129–180, Lemmas 2.1–2.2 (the local model at a fixed point).
* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
-/

public section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

variable {E H M EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless] [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [IsTopologicalGroup G] [CompactSpace G] [IsManifold IG ∞ G] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M]

variable (IG) in
/-- **The equivariant Darboux theorem.** Let a compact group `G`, a manifold without boundary, act
smoothly on a finite-dimensional manifold `M` without boundary, every `g` preserving a symplectic
form `form`, and let `x₀` be fixed by `G`. Then there is a smooth chart `chart` around `x₀`, with
`chart x₀ = 0` and `G`-invariant domain, which conjugates the action to the isotropy
representation `σ g = d(g • ·)_{x₀}` on `T_{x₀} M = E` and in which `form` is constant, equal to
its value at `x₀`. -/
theorem IsSymplectic.exists_equivariant_darbouxChart {form : SmoothTwoForm I M}
    (hform : form.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) form = form)
    {x₀ : M} (hx₀ : ∀ g : G, g • x₀ = x₀) :
    ∃ (σ : ContRepresentation ℝ G E) (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧ (∀ g : G, σ g = mfderiv I I (g • ·) x₀) ∧
      (∀ g : G, ∀ x ∈ chart.source, g • x ∈ chart.source ∧ chart (g • x) = σ g (chart x)) ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form.eval₂ x₀ (mvfderiv I chart x v) (mvfderiv I chart x w) := by
  -- Bochner's linearization: a chart `e` at `x₀` in which `G` acts by `σ`.
  obtain ⟨σ, e, hσc, hx₀e, hex₀, he, hes, hequiv, hσ, hderiv⟩ :=
    exists_equivariant_contMDiff_chart_of_compactSpace (I := I) (n := ⊤) IG le_top hx₀
  have h0 : (0 : E) ∈ e.target := hex₀ ▸ e.map_source hx₀e
  have hes0 : e.symm 0 = x₀ := by rw [← hex₀, e.left_inv hx₀e]
  have hmd {x : M} (hx : x ∈ e.source) : MDifferentiableAt I 𝓘(ℝ, E) e x :=
    ((he x hx).contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hmds {y : E} (hy : y ∈ e.target) : MDifferentiableAt 𝓘(ℝ, E) I e.symm y :=
    ((hes y hy).contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  -- In the coordinates of `e`, `g` acts on the target of `e` by `σ g`.
  have hsymm (g : G) {y : E} (hy : y ∈ e.target) :
      σ g y ∈ e.target ∧ e.symm (σ g y) = g • e.symm y := by
    obtain ⟨hgz, hez⟩ := hequiv g (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at hez
    exact ⟨hez ▸ e.map_source hgz, by rw [← hez, e.left_inv hgz]⟩
  -- The form `ω' = (e⁻¹)^* form` on the target of `e`.
  let ω' : E → E [⋀^Fin 2]→L[ℝ] ℝ := mpullback 𝓘(ℝ, E) I e.symm form.1
  have hω' (y : E) (m : Fin 2 → E) :
      ω' y m = form.1 (e.symm y) (fun i ↦ mfderiv 𝓘(ℝ, E) I e.symm y (m i)) :=
    mpullback_apply _ _ _ _
  have hsec (x : M) : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ) x (form.1 x)) x :=
    form.isSmoothForm.contMDiff.contMDiffAt
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) ω' e.target := fun y hy ↦
    (RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      ((hsec (e.symm y)).mpullback_form ((hes y hy).contMDiffAt (e.open_target.mem_nhds hy))
        (by simp)).contMDiffWithinAt)
  have hclosed : ∀ y ∈ e.target, extDeriv ω' y = 0 := fun y hy ↦ by
    have h := mpullback_mextDeriv_at
      (((hes y hy).contMDiffAt (e.open_target.mem_nhds hy)).of_le (by simp))
      ((hsec (e.symm y)).of_le (by simp))
    have hc : mextDeriv (form : RoughForm I M ℝ 2) = 0 :=
      (SmoothForm.isClosed_def form).1 hform.isClosed
    rw [← mextDeriv_eq_extDeriv, ← h, hc, mpullback_zero]
    rfl
  -- At `0`, the differential of `e⁻¹` is the identity, so `ω'` is the form at `x₀`.
  have hderiv0 (v : E) : mfderiv 𝓘(ℝ, E) I e.symm 0 v = v := by
    have h := e.mfderiv_apply_mfderiv_symm_apply h0 (hes0 ▸ hmd hx₀e) (hmds h0) v
    rwa [hes0, hderiv.mfderiv] at h
  have hω'0 (m : Fin 2 → E) : ω' 0 m = form.1 x₀ m := by
    have key : ∀ (z : M), z = x₀ → ∀ D : E →L[ℝ] TangentSpace I z, (∀ v, D v = v) →
        form.1 z (fun i ↦ D (m i)) = form.1 x₀ m := by
      rintro z rfl D hD
      simp only [hD]
    exact (hω' 0 m).trans (key _ hes0 _ hderiv0)
  have hnd : ∀ v, (∀ w, ω' 0 ![v, w] = 0) → v = 0 := fun v hv ↦
    isNondegenerate_iff_separatingLeft.1 hform.isNondegenerate x₀ v fun w ↦ by
      let v' : TangentSpace I x₀ := v
      let w' : TangentSpace I x₀ := w
      exact (SmoothBundleForm.eval₂_apply form x₀ v' w').trans ((hω'0 _).symm.trans (hv w))
  -- The form `ω'` is invariant under the linear action `σ`.
  have hinv : ∀ g : G, ∀ y ∈ e.target, (ω' (σ g y)).compContinuousLinearMap (σ g) = ω' y := by
    intro g y hy
    obtain ⟨hgy, hgy'⟩ := hsymm g hy
    have hcomp : (e.symm ∘ σ g : E → M) =ᶠ[𝓝 y] (fun x : M ↦ g • x) ∘ e.symm :=
      eventually_of_mem (e.open_target.mem_nhds hy) fun y' hy' ↦ (hsymm g hy').2
    have hσd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (σ g) y :=
      (σ g).differentiableAt.mdifferentiableAt
    have hgd : MDifferentiableAt I I (fun x : M ↦ g • x) (e.symm y) :=
      ((ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) (n := ∞) g).mdifferentiableAt
        (by simp))
    have hD : mfderiv 𝓘(ℝ, E) I (e.symm ∘ σ g) y =
        mfderiv 𝓘(ℝ, E) I ((fun x : M ↦ g • x) ∘ e.symm) y := hcomp.mfderiv_eq
    rw [mfderiv_comp y (hmds hgy) hσd, mfderiv_comp y hgd (hmds hy)] at hD
    ext m
    have hpull := congrArg (fun φ : SmoothTwoForm I M ↦ φ.1 (e.symm y)
      (fun i ↦ mfderiv 𝓘(ℝ, E) I e.symm y (m i))) (hG g)
    simp only [SmoothForm.mpullback_apply] at hpull
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hω', hω', ← hpull, hgy']
    congr 1
    funext i
    have := DFunLike.congr_fun hD (m i)
    simp only [mfderiv_eq_fderiv, (σ g).fderiv] at this
    exact this
  -- The flat equivariant Darboux theorem for `ω'`.
  have hbdd : Bornology.IsBounded (range σ) := (isCompact_range hσc).isBounded
  obtain ⟨ψ, U, hUo, h0U, -, hUσ, hψ0, hψσ, hψ⟩ :=
    exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq hbdd
      (fun g ↦ map_zero (σ g)) (r := ⊤) le_top e.open_target h0 hsmooth hclosed hnd hinv
  -- The chart `ψ⁻¹ ∘ e` on the preimage under `e` of `ψ(U)`.
  have hV : IsOpen (ψ '' U) := ψ.toHomeomorph.isOpenMap U hUo
  let eP : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := he
      contMDiffOn_invFun := hes }
  have hS : IsOpen (e.source ∩ e ⁻¹' (ψ '' U)) := e.isOpen_inter_preimage hV
  let chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    (eP.restrOpen _ hS).trans ψ.symm.toPartialDiffeomorph
  have hsrc : chart.source = e.source ∩ e ⁻¹' (ψ '' U) := by
    simp [chart, eP]
  have hcoe (x : M) : chart x = ψ.symm (e x) := by
    simp [chart, eP]
  have hmem {x : M} (hx : x ∈ chart.source) :
      x ∈ e.source ∧ ψ.symm (e x) ∈ U ∧ ψ (ψ.symm (e x)) = e x := by
    rw [hsrc] at hx
    obtain ⟨u, hu, hux⟩ := hx.2
    exact ⟨hx.1, by rwa [← hux, ψ.symm_apply_apply], ψ.apply_symm_apply _⟩
  refine ⟨σ, chart, ?_, ?_, hσ, fun g x hx ↦ ?_, fun x hx v w ↦ ?_⟩
  · rw [hsrc]
    exact ⟨hx₀e, 0, h0U, by rw [hψ0, hex₀]⟩
  · simpa [hcoe, hex₀] using congrArg ψ.symm hψ0.symm
  · obtain ⟨hxe, hu, hψu⟩ := hmem hx
    obtain ⟨hgx, hegx⟩ := hequiv g x hxe
    have hψσu : ψ (σ g (ψ.symm (e x))) = e (g • x) := by
      rw [hψσ g _ hu, hψu, hegx]
    refine ⟨?_, ?_⟩
    · rw [hsrc]
      exact ⟨hgx, _, hUσ g hu, hψσu⟩
    · rw [hcoe, hcoe, ← hψσu, ψ.symm_apply_apply]
  · obtain ⟨hxe, hu, hψu⟩ := hmem hx
    -- The differential of the chart is that of `ψ⁻¹` after that of `e`.
    have hdchart (a : TangentSpace I x) : mvfderiv I chart x a =
        fderiv ℝ ψ.symm (e x) (mfderiv I 𝓘(ℝ, E) e x a) := by
      have hfun : (chart : M → E) = ψ.symm ∘ e := funext hcoe
      rw [hfun, mvfderiv_comp_apply_of_differentiableAt (ψ.symm.differentiable (by simp) _)
        (hmd hxe), mvfderiv_apply_eq_mfderiv_apply]
    -- The flat Darboux identity at `ψ⁻¹ (e x)`, read through the inverse differential.
    have hflat (a b : E) : ω' (e x) ![a, b] =
        ω' 0 ![fderiv ℝ ψ.symm (e x) a, fderiv ℝ ψ.symm (e x) b] := by
      have h := congrArg (fun A ↦ A ![fderiv ℝ ψ.symm (e x) a, fderiv ℝ ψ.symm (e x) b])
        (hψ _ hu)
      have hinv' (c : E) : fderiv ℝ ψ (ψ.symm (e x)) (fderiv ℝ ψ.symm (e x) c) = c :=
        ψ.fderiv_apply_fderiv_symm_apply (by simp) (e x) c
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hψu] at h
      rw [← h]
      congr 1
      ext i
      fin_cases i <;> simp [hinv']
    -- Reading `form` at `x` through `e` gives `ω'` at `e x`.
    have hback : form.eval₂ x v w = ω' (e x)
        ![mfderiv I 𝓘(ℝ, E) e x v, mfderiv I 𝓘(ℝ, E) e x w] := by
      rw [SmoothBundleForm.eval₂_apply, hω', e.left_inv hxe]
      congr 1
      ext i
      fin_cases i <;>
        exact (e.mfderiv_symm_apply_mfderiv_apply hxe (hmd hxe) (hmds (e.map_source hxe)) _).symm
    refine hback.trans ((hflat _ _).trans ?_)
    rw [hdchart, hdchart]
    exact (hω'0 _).trans (SmoothBundleForm.eval₂_apply form x₀ _ _).symm

end SmoothTwoForm

end TauCeti
