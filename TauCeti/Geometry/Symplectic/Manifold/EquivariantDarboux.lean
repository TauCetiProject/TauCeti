/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Manifold.GroupAction.CompactLinearization
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Darboux.Basic
import TauCeti.Logic.Equiv.PartialEquiv

/-!
# The equivariant Darboux theorem on manifolds

Let a compact group `G`, itself a manifold without boundary, act smoothly on a finite-dimensional
manifold `M` without boundary, preserving a symplectic form `σ`, and let `x₀` be a fixed point of
the action. The **equivariant Darboux theorem**
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_equivariant_darbouxChart`) gives a smooth chart
`chart` of `M` around `x₀`, with values in the model space `E = T_{x₀} M` and `chart x₀ = 0`, such
that

* its source is `G`-invariant and `G` acts in it linearly, through the isotropy representation
  `g ↦ d(g • ·)_{x₀}` of `G` on `T_{x₀} M`: `chart (g • x) = d(g • ·)_{x₀} (chart x)`;
* it carries `σ` to the constant form `σ_{x₀}` on `T_{x₀} M`: for every `x` in its source,
  `σ_x (v, w) = σ_{x₀} (d chart_x v, d chart_x w)`;
* a point of its source is fixed by `G` exactly when its image is fixed by the isotropy
  representation.

So near a fixed point a compact symplectic action is its linear isotropy representation on the
symplectic vector space `(T_{x₀} M, σ_{x₀})`, and the fixed set is, in symplectic coordinates, the
subspace of invariant vectors, which is symplectic
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation`). This is the
local model from which the weight normal form of a torus action near a fixed point, and with it
the local form of its moment map, are read off.

The proof composes two equivariant linearizations. Bochner's theorem
(`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`) gives a chart `e` at `x₀` in which
`G` acts through its isotropy representation `ρ` and whose derivative at `x₀` is the identity. The
form `σ` read in `e` is a closed `ρ`-invariant two-form on the target of `e`, equal to `σ_{x₀}` at
the origin. The flat equivariant Darboux theorem
(`TauCeti.exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq`), an equivariant Moser
argument, gives a diffeomorphism `ψ` of `E`, commuting with `ρ` near the origin, which pulls this
form back to the constant `σ_{x₀}`, and the chart is `ψ⁻¹ ∘ e`. Compactness of `G` makes the
operators `ρ g` a bounded set, which is what the Moser argument needs to find invariant
neighbourhoods.

## References

* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984 (the equivariant Darboux theorem, by an equivariant Moser argument).
* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381 (linearization of compact group actions at fixed points).
-/

public section

noncomputable section

open Set Filter Function MulAction
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Chart

/-! ### Forms read in a chart -/

variable {e : OpenPartialHomeomorph M E} {G : Type*} (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
  (hes : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)

include he hes in
/-- Let `e` be a chart in which `g • ·` acts by the linear map `ρ g`, and in which the form `η` on
`M` reads as the flat form `η'`. Let `ψ` be a diffeomorphism of `E` which commutes with `ρ` on a
`ρ`-invariant open neighbourhood `U` of `0` and pulls `η'` back to the constant `η' 0` there. Then
`ψ⁻¹ ∘ e`, on the points sent into `ψ '' U`, is a chart in which `g • ·` still acts by `ρ g` and in
which `η` reads as the constant `η' 0`. -/
private theorem exists_chart_comp_symm [SMul G M] {ρ : G → E →L[ℝ] E}
    (hequiv : ∀ g : G, ∀ z ∈ e.source, g • z ∈ e.source ∧ e (g • z) = ρ g (e z)) {k : ℕ}
    {η : RoughForm I M ℝ k} {η' : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hηe : ∀ {x : M}, x ∈ e.source → mpullback I 𝓘(ℝ, E) e η' x = η x)
    (ψ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E) {U : Set E} (hUo : IsOpen U) (h0U : (0 : E) ∈ U)
    (hUρ : ∀ g : G, MapsTo (ρ g) U U) (hψ0 : ψ 0 = 0)
    (hψρ : ∀ g : G, ∀ u ∈ U, ψ (ρ g u) = ρ g (ψ u))
    (hψ : ∀ u ∈ U, mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) ψ η' u = η' 0) {x₀ : M} (hx₀e : x₀ ∈ e.source)
    (hex₀ : e x₀ = 0) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞, x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ g : G, ∀ x ∈ chart.source, g • x ∈ chart.source ∧ chart (g • x) = ρ g (chart x)) ∧
      ∀ x ∈ chart.source, ∀ v : Fin k → TangentSpace I x,
        η x v = η' 0 (fun i ↦ mfderiv I 𝓘(ℝ, E) chart x (v i)) := by
  have hS : IsOpen (e.source ∩ e ⁻¹' (ψ '' U)) :=
    e.continuousOn.isOpen_inter_preimage e.open_source (ψ.toHomeomorph.isOpenMap U hUo)
  let e' : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := e.toPartialEquiv, open_source := e.open_source,
      open_target := e.open_target, contMDiffOn_toFun := he, contMDiffOn_invFun := hes }
  let chart := (e'.restrOpen _ hS).trans ψ.symm.toPartialDiffeomorph
  have hchart (x : M) : chart x = ψ.symm (e x) := by simp [chart, e']
  have hmem {x : M} : x ∈ chart.source ↔ x ∈ e.source ∧ e x ∈ ψ '' U := by simp [chart, e']
  refine ⟨chart, hmem.2 ⟨hx₀e, 0, h0U, hψ0.trans hex₀.symm⟩,
    by rw [hchart, hex₀]; exact ψ.symm_apply_eq.2 hψ0.symm, fun g x hx ↦ ?_, fun x hx v ↦ ?_⟩
  · obtain ⟨hxe, u, hu, hux⟩ := hmem.1 hx
    obtain ⟨hgx, hegx⟩ := hequiv g x hxe
    rw [← hux, ← hψρ g u hu] at hegx
    refine ⟨hmem.2 ⟨hgx, ρ g u, hUρ g hu, hegx.symm⟩, ?_⟩
    rw [hchart, hchart, hegx, ← hux, ψ.symm_apply_apply, ψ.symm_apply_apply]
  · obtain ⟨hxe, u, hu, hux⟩ := hmem.1 hx
    have hd : MDifferentiableAt I 𝓘(ℝ, E) chart x :=
      ((chart.contMDiffOn_toFun x hx).contMDiffAt
        (chart.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
    -- Since `e = ψ ∘ chart`, `η` reads in `chart` as `ψ^* η'`, which is constant on `U`.
    have heq : (e : M → E) =ᶠ[𝓝 x] ψ ∘ chart :=
      .of_forall fun z ↦ by rw [comp_apply, hchart, ψ.apply_symm_apply]
    have hψx : mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) ψ η' (chart x) = η' 0 := by
      rw [hchart, ← hux, ψ.symm_apply_apply]
      exact hψ u hu
    rw [← hηe hxe, heq.mpullback_eq η',
      mpullback_comp_at hd (ψ.contMDiff.mdifferentiable (by simp) _) η', mpullback_apply, hψx]
    -- The two sides differ only in the tangent-space type of the vectors, which is `E` by
    -- definition.
    rfl

end Chart

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  {EG HG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless] [TopologicalSpace G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [Group G] [IsTopologicalGroup G] [CompactSpace G] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M]

/-- **The equivariant Darboux theorem.** Let a compact group `G`, a manifold without boundary, act
smoothly on a finite-dimensional manifold `M` without boundary, preserving a symplectic form
`form`, and let `x₀` be a fixed point. Then there is a smooth chart `chart` of `M` around `x₀`,
with values in `E = T_{x₀} M` and `chart x₀ = 0`, whose source is `G`-invariant, in which `G` acts
through its isotropy representation `g ↦ d(g • ·)_{x₀}`, and which pulls the constant form
`form_{x₀}` back to `form`. A point of the source is fixed by `G` exactly when its image is fixed
by the isotropy representation. -/
theorem IsSymplectic.exists_equivariant_darbouxChart {form : SmoothTwoForm I M}
    (hform : form.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) form = form)
    {x₀ : M} (hx₀ : ∀ g : G, g • x₀ = x₀) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ g : G, ∀ x ∈ chart.source,
        g • x ∈ chart.source ∧ chart (g • x) = mfderiv I I (g • ·) x₀ (chart x)) ∧
      (∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = hform.isNondegenerate.symplecticFormAt x₀
          (mvfderiv I chart x v) (mvfderiv I chart x w)) ∧
      ∀ x ∈ chart.source,
        (∀ g : G, g • x = x) ↔ ∀ g : G, mfderiv I I (g • ·) x₀ (chart x) = chart x := by
  -- Bochner coordinates `e` at `x₀`, in which `G` acts through its isotropy representation `ρ`.
  obtain ⟨ρ, e, hρc, hx₀e, hex₀, he, hes, hequiv, hρ, hderiv⟩ :=
    exists_equivariant_contMDiff_chart_of_compactSpace (I := I) (n := ⊤) IG le_top hx₀
  have hds {y : E} (hy : y ∈ e.target) : MDifferentiableAt 𝓘(ℝ, E) I e.symm y :=
    (hes.contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  -- The form read in `e`: a closed `ρ`-invariant form on the target of `e`, equal to `form x₀` at
  -- the origin.
  let η : E → E [⋀^Fin 2]→L[ℝ] ℝ := mpullback 𝓘(ℝ, E) I e.symm form.val
  have hηe {x : M} (hx : x ∈ e.source) : mpullback I 𝓘(ℝ, E) e η x = form.val x :=
    e.mpullback_mpullback_symm_apply form.val hx
      ((he.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp))
      (hds (e.map_source hx))
  have hη0 (a b : TangentSpace I x₀) : η 0 ![a, b] = form.eval₂ x₀ a b := by
    have hid (v : TangentSpace I x₀) : mfderiv I 𝓘(ℝ, E) e x₀ v = v := by
      rw [hderiv.mfderiv]
      -- `TangentSpace I x₀` is `E` by definition, so `v` is a vector of `E` for the identity.
      exact ContinuousLinearMap.id_apply (R₁ := ℝ) (M₁ := E) v
    rw [SmoothBundleForm.eval₂_apply, ← hηe hx₀e, mpullback_apply_pair, hid, hid, hex₀]
    -- The two sides differ only in the type of the entries of `![a, b]`, `TangentSpace I x₀` on
    -- one side and `E` on the other, which agree by definition.
    rfl
  have hηρ (g : G) (y : E) (hy : y ∈ e.target) :
      (η (ρ g y)).compContinuousLinearMap (ρ g) = η y := by
    have h := e.mpullback_mpullback_symm_eq_mpullback_symm_apply_of_intertwines
      (by simpa using congrArg Subtype.val (hG g)) (hequiv g) hy (hds hy)
      (hds (e.toPartialEquiv.symm_map_of_intertwines (hequiv g) hy).1) (ρ g).mdifferentiableAt
      ((ContMDiffSMul.contMDiff_const_smul (I := IG) (n := ∞) g).mdifferentiable (by simp) _)
    calc _ = (η (ρ g y)).compContinuousLinearMap (fderiv ℝ (ρ g) y) := by rw [(ρ g).fderiv]
      _ = η y := by rwa [mpullback_eq_flat] at h
  -- The flat equivariant Darboux theorem for `η`, transported back to `M` along `e`.
  obtain ⟨ψ, U, hUo, h0U, -, hUρ, hψ0, hψρ, hψ⟩ :=
    exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq (r := ⊤)
      (isCompact_range hρc).isBounded (fun g ↦ map_zero (ρ g)) le_top e.open_target
      (hex₀ ▸ e.map_source hx₀e) (form.contDiffOn_mpullback e.open_target hes)
      (fun y hy ↦ hform.isClosed.extDeriv_mpullback_eq_zero
        ((hes.contMDiffAt (e.open_target.mem_nhds hy)).of_le (by simp)))
      (fun v hv ↦ isNondegenerate_iff_separatingLeft.1 hform.isNondegenerate x₀ v fun w ↦
        (hη0 v w).symm.trans (hv w)) hηρ
  obtain ⟨chart, hx₀c, hc0, hcequiv, hcη⟩ := exists_chart_comp_symm he hes hequiv hηe ψ hUo h0U
    hUρ hψ0 hψρ (fun u hu ↦ by rw [mpullback_eq_flat]; exact hψ u hu) hx₀e hex₀
  simp only [← hρ]
  refine ⟨chart, hx₀c, hc0, hcequiv, fun x hx v w ↦ ?_, fun x hx ↦ ?_⟩
  · have hvec : (fun i ↦ mfderiv I 𝓘(ℝ, E) chart x (![v, w] i)) =
        ![mvfderiv I chart x v, mvfderiv I chart x w] := by
      ext i
      fin_cases i <;> simp [mvfderiv_apply_eq_mfderiv_apply]
    rw [SmoothBundleForm.eval₂_apply, hcη x hx, hvec]
    exact (hη0 _ _).trans (hform.isNondegenerate.symplecticFormAt_apply x₀ _ _).symm
  · refine forall_congr' fun g ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact (hcequiv g x hx).2.symm.trans (congrArg _ h)
    · exact chart.toPartialEquiv.injOn (hcequiv g x hx).1 hx ((hcequiv g x hx).2.trans h)

end SmoothTwoForm

end TauCeti
