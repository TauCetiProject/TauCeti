/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Normed.Module.Alternating.Bilinear
import TauCeti.Analysis.ODE.Straightening
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Symplectic.Darboux.Basic
import TauCeti.Geometry.Symplectic.Restrict
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Darboux charts with a prescribed momentum

Let `f` be a smooth function near a point `x₀` of a symplectic manifold, with `df_{x₀} ≠ 0`. The
**Carathéodory–Jacobi–Lie theorem** for one function says that `f` is a coordinate of a Darboux
chart: there are Darboux coordinates `(q₁, …, qₙ, p₁, …, pₙ)` around `x₀` with `f = f x₀ + p₁`.
This is the first case of the normal form of a family of independent Poisson-commuting functions,
which can be taken as the momenta `p₁, …, p_k` of a Darboux chart.

On a finite-dimensional symplectic vector space `(V, σ)` the statement is
`TauCeti.SymplecticForm.exists_openPartialHomeomorph_eq_add_fderiv`: a smooth chart `κ` around
`x₀`, with `κ x₀ = 0` and `σ(dκ u, dκ v) = σ(u, v)`, in which `f = f x₀ + df_{x₀} ∘ κ`. On a
symplectic manifold, composing with a Darboux chart gives
`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_eq_add_of_isInteriorPoint` (in
`TauCeti.Geometry.Symplectic.Manifold.Darboux`).

The proof constructs the inverse chart. Cut `f` off to a compactly supported `F` and choose a
conjugate function `G` with `{G, F} = 1` near `x₀`
(`TauCeti.SymplecticForm.exists_fderiv_apply_hamiltonianVectorField_eq_one`); it is built from a
linear coordinate in a chart straightening the Hamiltonian vector field `X_F`.
At `x₀` the vectors `e = X_F(x₀)` and `e' = X_G(x₀)` span a symplectic plane, with symplectic
complement `W`. Along the flow `φ^G` of `G` the function `F` decreases at unit rate, and along
the flow `φ^F` it is conserved. On the slice `s(w) = x₀ + w + (G(x₀ + w) - G x₀) e +
(F(x₀ + w) - F x₀) e'` through `x₀`, the closed form `η = s^* σ` is nondegenerate at `0`, and
Darboux's theorem on `W`
(`TauCeti.exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv`) gives a
diffeomorphism `D` of `W` with `D^* σ|_W = η`. In the coordinates `y = A e + B e' + Z`
of `V`, with `Z ∈ W`, the map

`χ y = φ^F_{A - G(k) + G x₀} (φ^G_{B + F(k) - F x₀} k)`, `k = x₀ + D⁻¹ Z`,

satisfies `F ∘ χ = F x₀ - B`, and its pullback of `σ` is computed by the formula for the pullback
along a Hamiltonian flow with varying time
(`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow_comp`): it is `σ`. Hence `χ` is a local
symplectic diffeomorphism near `0`, and its local inverse is the chart `κ`.

## Main results

* `TauCeti.SymplecticForm.exists_fderiv_apply_hamiltonianVectorField_eq_one`: a function with
  nonzero differential has a conjugate function near the point.
* `TauCeti.SymplecticForm.exists_openPartialHomeomorph_eq_add_fderiv`: the normal form on a
  symplectic vector space.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 43 (Darboux's theorem, constructed from a first
  coordinate `p₁` and a conjugate coordinate `q₁` with commuting flows).
* P. Libermann and C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, Reidel, 1987,
  Chapter III (the Carathéodory–Jacobi–Lie theorem).
-/

public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (σ : SymplecticForm V)

/-- **A conjugate function.** Let `F` be smooth near `x₀` with `dF_{x₀} ≠ 0`. Then some smooth
compactly supported function `G` has derivative `1` along the Hamiltonian vector field of `F` near
`x₀`, that is `{G, F} = 1` near `x₀`. -/
theorem exists_fderiv_apply_hamiltonianVectorField_eq_one {F : V → ℝ} {U : Set V} {x₀ : V}
    (hU : U ∈ 𝓝 x₀) (hF : ContDiffOn ℝ ∞ F U) (hx₀ : fderiv ℝ F x₀ ≠ 0) :
    ∃ G : V → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      ∀ᶠ z in 𝓝 x₀, fderiv ℝ G z (σ.hamiltonianVectorField F z) = 1 := by
  obtain ⟨F', hF', -, hF'F⟩ := hF.exists_contDiff_eventuallyEq_of_finiteDimensional hU
  set X := σ.hamiltonianVectorField F'
  have hX : ContDiff ℝ ∞ X := σ.contDiff_hamiltonianVectorField (by simpa using hF')
  have hXx₀ : X x₀ ≠ 0 := by rwa [Ne, σ.hamiltonianVectorField_eq_zero_iff, hF'F.fderiv_eq]
  obtain ⟨φ, hx₀φ, hφ, -, hφX⟩ := exists_openPartialHomeomorph_fderiv_eq_const (n := ⊤) le_top
    hX.contDiffOn univ_mem hXx₀
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hXx₀
  have hg : ContDiffOn ℝ ∞ (fun z ↦ ℓ (φ z)) φ.source := fun z hz ↦
    (ℓ.contDiff.contDiffAt.comp z (hφ z hz)).contDiffWithinAt
  obtain ⟨G, hG, hGc, hGg⟩ := hg.exists_contDiff_eventuallyEq_of_finiteDimensional
    (φ.open_source.mem_nhds hx₀φ)
  refine ⟨G, hG, hGc, ?_⟩
  filter_upwards [hGg.eventuallyEq_nhds, φ.open_source.mem_nhds hx₀φ, hF'F.eventuallyEq_nhds]
    with z hz hzφ hzF
  have hφz : HasFDerivAt φ (fderiv ℝ φ z) z :=
    ((hφ z hzφ).differentiableAt (by simp)).hasFDerivAt
  have hd : HasFDerivAt (fun z ↦ ℓ (φ z)) (ℓ.comp (fderiv ℝ φ z)) z :=
    ℓ.hasFDerivAt.comp z hφz
  rw [σ.hamiltonianVectorField_congr_of_eventuallyEq hzF.symm, hz.fderiv_eq, hd.fderiv,
    ContinuousLinearMap.comp_apply]
  exact (congrArg ℓ (hφX z hzφ)).trans hℓ

/-! ### The normal form -/

/-- **The slice through `x₀`.** Let `σ e' e = 1` and let `W` be the symplectic complement of the
plane of `e` and `e'`. The slice `s(w) = x₀ + w + (G(x₀ + w) - G x₀) e + (F(x₀ + w) - F x₀) e'`
pulls `σ` back to a smooth closed two-form `η` on `W`, which is `σ|_W + dF ∧ dG`. -/
private theorem exists_closed_slice_form {F G : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) {e e' : V} (hee' : σ e' e = 1) (x₀ : V) :
    ∃ η : σ.orthogonal (Submodule.span ℝ {e, e'}) →
        σ.orthogonal (Submodule.span ℝ {e, e'}) [⋀^Fin 2]→L[ℝ] ℝ,
      ContDiff ℝ ∞ η ∧ (∀ w, extDeriv η w = 0) ∧ ∀ w a b,
        η w ![a, b] = σ a b + fderiv ℝ F (x₀ + (w : V)) a * fderiv ℝ G (x₀ + (w : V)) b -
          fderiv ℝ F (x₀ + (w : V)) b * fderiv ℝ G (x₀ + (w : V)) a := by
  set W := σ.orthogonal (Submodule.span ℝ {e, e'})
  let s : W → V := fun w ↦ x₀ + (w : V) + (G (x₀ + w) - G x₀) • e + (F (x₀ + w) - F x₀) • e'
  have hk (w : W) : HasFDerivAt (fun w : W ↦ x₀ + (w : V)) W.subtypeL w :=
    W.subtypeL.hasFDerivAt.const_add x₀
  have hFd (z : V) : HasFDerivAt F (fderiv ℝ F z) z := (hF.differentiable (by simp) z).hasFDerivAt
  have hGd (z : V) : HasFDerivAt G (fderiv ℝ G z) z := (hG.differentiable (by simp) z).hasFDerivAt
  have hsd (w : W) : HasFDerivAt s (W.subtypeL +
      ((fderiv ℝ G (x₀ + w)).comp W.subtypeL).smulRight e +
      ((fderiv ℝ F (x₀ + w)).comp W.subtypeL).smulRight e') w :=
    ((hk w).add ((((hGd _).comp w (hk w)).sub_const _).smul_const e)).add
      ((((hFd _).comp w (hk w)).sub_const _).smul_const e')
  have hs : ContDiff ℝ ∞ s := by
    have hk' : ContDiff ℝ ∞ (fun w : W ↦ x₀ + (w : V)) := contDiff_const.add W.subtypeL.contDiff
    exact (hk'.add (((hG.comp hk').sub contDiff_const).smul contDiff_const)).add
      (((hF.comp hk').sub contDiff_const).smul contDiff_const)
  let σA : V [⋀^Fin 2]→L[ℝ] ℝ :=
    AlternatingMap.toContinuousAlternatingMap σ.isAlt.toAlternatingMap
  refine ⟨fun w ↦ σA.compContinuousLinearMap (fderiv ℝ s w), ?_, fun w ↦ ?_, fun w a b ↦ ?_⟩
  · exact contDiff_iff_contDiffAt.2 fun w ↦
      (hs.contDiffAt.of_le (by exact_mod_cast le_top)).differentialForm_pullback contDiffAt_const
  · have h := extDeriv_pullback (f := s) (x := w) (r := ∞) (differentiableAt_const (c := σA))
      hs.contDiffAt (by simp [minSmoothness_of_isRCLikeNormedField])
    rw [ContinuousAlternatingMap.extDeriv_const] at h
    refine h.trans ?_
    ext
    simp
  -- `SymplecticForm.isAlt` is stated for `LinearMap.BilinForm.IsAlt`, so the evaluation lemma is
  -- applied as a term.
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_vecCons_two,
    AlternatingMap.coe_toContinuousAlternatingMap, LinearMap.IsAlt.toAlternatingMap_apply σ.isAlt,
    (hsd w).fderiv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact (σ.apply_add_smul_add_smul hee' a.property b.property _ _ _ _).trans (by ring)

/-- **Darboux's theorem on the slice.** Let `σ e' e = 1`, and let `F`, `G` be smooth with
`dF_{x₀} = σ(e, ·)` and `dG_{x₀} = σ(e', ·)`. On the symplectic complement `W` of the plane of
`e` and `e'`, the form `σ|_W + dF ∧ dG` pulled back by the slice through `x₀` is nondegenerate
at `0`; a diffeomorphism `D` of `W` fixing `0` pulls `σ|_W` back to it near `0`. -/
private theorem exists_diffeomorph_orthogonal_span_pair {F G : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) {e e' x₀ : V} (hee' : σ e' e = 1) (hFe : ∀ v, σ e v = fderiv ℝ F x₀ v)
    (hGe : ∀ v, σ e' v = fderiv ℝ G x₀ v) :
    ∃ D : σ.orthogonal (Submodule.span ℝ {e, e'}) ≃ₘ^((⊤ : ℕ∞) : WithTop ℕ∞)⟮𝓘(ℝ,
        σ.orthogonal (Submodule.span ℝ {e, e'})), 𝓘(ℝ, σ.orthogonal (Submodule.span ℝ {e, e'}))⟯
        σ.orthogonal (Submodule.span ℝ {e, e'}),
      D 0 = 0 ∧ ∀ᶠ w : σ.orthogonal (Submodule.span ℝ {e, e'}) in 𝓝 0,
        ∀ a b : σ.orthogonal (Submodule.span ℝ {e, e'}),
        σ a b + fderiv ℝ F (x₀ + (w : V)) a * fderiv ℝ G (x₀ + (w : V)) b -
          fderiv ℝ F (x₀ + (w : V)) b * fderiv ℝ G (x₀ + (w : V)) a =
        σ (fderiv ℝ D w a) (fderiv ℝ D w b) := by
  set W := σ.orthogonal (Submodule.span ℝ {e, e'})
  obtain ⟨η, hηc, hηd, hη⟩ := σ.exists_closed_slice_form hF hG hee' x₀
  have hη₀ (a b : W) : η 0 ![a, b] = σ a b := by
    have hdF₀ (a : W) : fderiv ℝ F x₀ a = 0 :=
      (hFe a).symm.trans (mem_orthogonal_span_pair_iff.1 a.property).1
    have hdG₀ (a : W) : fderiv ℝ G x₀ a = 0 :=
      (hGe a).symm.trans (mem_orthogonal_span_pair_iff.1 a.property).2
    simp [hη, hdF₀, hdG₀]
  have hηnd : ∀ v : W, (∀ w : W, η 0 ![v, w] = 0) → v = 0 := fun v hv ↦
    (σ.nondegenerate_restrict_orthogonal_of_isCompl
      (σ.isAlt.isCompl_span_pair_orthogonal hee')).1 v fun w ↦ (hη₀ v w).symm.trans (hv w)
  -- Darboux's theorem on `W` straightens `η` to the constant form `σ|_W`.
  obtain ⟨D, V₀, hD0, hV₀o, h0V₀, -, hηD⟩ :=
    exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv (r := (⊤ : ℕ∞))
      le_top isOpen_univ (mem_univ (0 : W)) hηc.contDiffOn (fun w _ ↦ hηd w) hηnd
  refine ⟨D, hD0, ?_⟩
  filter_upwards [hV₀o.mem_nhds h0V₀] with w hw a b
  rw [← hη, hηD w hw, ContinuousAlternatingMap.compContinuousLinearMap_apply_vecCons_two, hη₀]

/-- **The slice parametrization.** With `e`, `e'`, `F`, `G` as in
`exists_diffeomorph_orthogonal_span_pair`, there is a smooth map `k` with `k 0 = x₀` along which,
near `0`, the form `σ + dF ∧ dG` pulls back to `σ` minus the area form of the plane of `e` and
`e'`: `k y = x₀ + D⁻¹ (Z y)`, with `Z` the projection onto the symplectic complement. -/
private theorem exists_contDiff_slice {F G : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) {e e' x₀ : V} (hee' : σ e' e = 1) (hFe : ∀ v, σ e v = fderiv ℝ F x₀ v)
    (hGe : ∀ v, σ e' v = fderiv ℝ G x₀ v) :
    ∃ k : V → V, ContDiff ℝ ∞ k ∧ k 0 = x₀ ∧ ∀ᶠ y in 𝓝 0, ∀ u v,
      σ (fderiv ℝ k y u) (fderiv ℝ k y v) +
          fderiv ℝ F (k y) (fderiv ℝ k y u) * fderiv ℝ G (k y) (fderiv ℝ k y v) -
          fderiv ℝ F (k y) (fderiv ℝ k y v) * fderiv ℝ G (k y) (fderiv ℝ k y u) =
        σ u v - (σ e' u * σ e v - σ e' v * σ e u) := by
  set W := σ.orthogonal (Submodule.span ℝ {e, e'})
  set Z : V →L[ℝ] W := LinearMap.toContinuousLinearMap (σ.orthogonalSpanPairProj hee')
  obtain ⟨D, hD0, hDev⟩ := σ.exists_diffeomorph_orthogonal_span_pair hF hG hee' hFe hGe
  obtain ⟨V₀, hV₀D, hV₀o, h0V₀⟩ := mem_nhds_iff.1 hDev
  have hDs0 : D.symm 0 = 0 := D.injective ((D.apply_symm_apply 0).trans hD0.symm)
  have hDsc : ContDiff ℝ ∞ (D.symm : W → W) := D.symm.contMDiff.contDiff
  have hV : ∀ᶠ y in 𝓝 0, D.symm (Z y) ∈ V₀ :=
    (hDsc.comp Z.contDiff).continuous.continuousAt.eventually_mem
      (by simpa [hDs0] using hV₀o.mem_nhds h0V₀)
  refine ⟨fun y ↦ x₀ + (D.symm (Z y) : V),
    contDiff_const.add (W.subtypeL.contDiff.comp (hDsc.comp Z.contDiff)), by simp [hDs0],
    hV.mono fun y hy u v ↦ ?_⟩
  have hD' : HasFDerivAt (D.symm : W → W) (fderiv ℝ D.symm (Z y)) (Z y) :=
    (hDsc.differentiable (by simp) _).hasFDerivAt
  have hk : HasFDerivAt (fun y ↦ x₀ + (D.symm (Z y) : V))
      (W.subtypeL.comp ((fderiv ℝ D.symm (Z y)).comp (Z : V →L[ℝ] W))) y :=
    (W.subtypeL.hasFDerivAt.comp y (hD'.comp y Z.hasFDerivAt)).const_add x₀
  have h := hV₀D hy (fderiv ℝ D.symm (Z y) (Z u)) (fderiv ℝ D.symm (Z y) (Z v))
  rw [D.fderiv_apply_fderiv_symm_apply (by simp), D.fderiv_apply_fderiv_symm_apply (by simp)] at h
  rw [hk.fderiv, σ.apply_eq_apply_orthogonalSpanPairProj_add hee' u v]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [h]
  simp only [Z, LinearMap.coe_toContinuousLinearMap']
  ring

/-- **The pullback along two flows.** For a map `k` with derivative `dk` at `y`, the map
`χ y = φ^F_{A y - G (k y) + c₁} (φ^G_{B y + F (k y) - c₂} (k y))` pulls `σ` back at `y` to the
pullback of `σ + dF ∧ dG` along `k` plus `B ∧ A`, provided `F` is `c₂ - B` along the inner flow
near `y`. -/
private theorem apply_fderiv_hamiltonianFlow_hamiltonianFlow {F G : V → ℝ} {KF KG : ℝ≥0}
    (hXF : LipschitzWith KF (σ.hamiltonianVectorField F))
    (hXG : LipschitzWith KG (σ.hamiltonianVectorField G)) (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) {k : V → V} {dk : V →L[ℝ] V} {A B : V →L[ℝ] ℝ} {c₁ c₂ : ℝ} {y : V}
    (hk : HasFDerivAt k dk y)
    (hFk : ∀ᶠ y' in 𝓝 y, F (σ.hamiltonianFlow G hXG (B y' + F (k y') - c₂) (k y')) = c₂ - B y')
    (u v : V) :
    σ (fderiv ℝ (fun y' ↦ σ.hamiltonianFlow F hXF (A y' - G (k y') + c₁)
          (σ.hamiltonianFlow G hXG (B y' + F (k y') - c₂) (k y'))) y u)
        (fderiv ℝ (fun y' ↦ σ.hamiltonianFlow F hXF (A y' - G (k y') + c₁)
          (σ.hamiltonianFlow G hXG (B y' + F (k y') - c₂) (k y'))) y v) =
      σ (dk u) (dk v) + fderiv ℝ F (k y) (dk u) * fderiv ℝ G (k y) (dk v) -
        fderiv ℝ F (k y) (dk v) * fderiv ℝ G (k y) (dk u) + (A v * B u - A u * B v) := by
  have hτ₂ : HasFDerivAt (fun y' ↦ B y' + F (k y') - c₂) (B + (fderiv ℝ F (k y)).comp dk) y :=
    (B.hasFDerivAt.add ((hF.differentiable (by simp) _).hasFDerivAt.comp y hk)).sub_const _
  have hτ₁ : HasFDerivAt (fun y' ↦ A y' - G (k y') + c₁) (A - (fderiv ℝ G (k y)).comp dk) y :=
    (A.hasFDerivAt.sub ((hG.differentiable (by simp) _).hasFDerivAt.comp y hk)).add_const _
  have hk₁ := σ.hasFDerivAt_hamiltonianFlow_comp G hXG hG hτ₂ hk
  -- `F` is `c₂ - B` along the inner flow near `y`, so `dF (dk₁ w) = -B w`.
  have hFk₁ (w : V) : fderiv ℝ F (σ.hamiltonianFlow G hXG (B y + F (k y) - c₂) (k y))
      (fderiv ℝ (fun y' ↦ σ.hamiltonianFlow G hXG (B y' + F (k y') - c₂) (k y')) y w) = -B w := by
    have h₁ := (hF.differentiable (by simp) _).hasFDerivAt.comp y
      hk₁.differentiableAt.hasFDerivAt
    have h₂ : HasFDerivAt (fun y' ↦ c₂ - B y') (-B) y := by
      simpa using B.hasFDerivAt.const_sub c₂
    exact congrArg (fun L : V →L[ℝ] ℝ ↦ L w) (h₁.unique (h₂.congr_of_eventuallyEq hFk))
  rw [σ.apply_fderiv_hamiltonianFlow_comp F hXF hF hτ₁ hk₁.differentiableAt.hasFDerivAt, hFk₁,
    hFk₁, σ.apply_fderiv_hamiltonianFlow_comp G hXG hG hτ₂ hk]
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply]
  ring

/-- The parametrization behind `exists_openPartialHomeomorph_eq_add_fderiv`, for a smooth `F` with
a conjugate function `G` near `x₀` and globally Lipschitz Hamiltonian vector fields: a smooth map
`χ` with `χ 0 = x₀` which near `0` preserves `σ` and along which `F` is `F x₀ + dF_{x₀}`. -/
private theorem exists_contDiff_eventually_apply_eq_add_fderiv_of_conjugate {F G : V → ℝ}
    {KF KG : ℝ≥0} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hXF : LipschitzWith KF (σ.hamiltonianVectorField F))
    (hXG : LipschitzWith KG (σ.hamiltonianVectorField G)) {x₀ : V}
    (hGF : ∀ᶠ z in 𝓝 x₀, fderiv ℝ G z (σ.hamiltonianVectorField F z) = 1) :
    ∃ χ : V → V, ContDiff ℝ ∞ χ ∧ χ 0 = x₀ ∧ ∀ᶠ y in 𝓝 0,
      F (χ y) = F x₀ + fderiv ℝ F x₀ y ∧ ∀ u v, σ (fderiv ℝ χ y u) (fderiv ℝ χ y v) = σ u v := by
  -- Near `x₀` the function `F` decreases at unit rate along the flow of `G`.
  have hrate : ∀ᶠ z in 𝓝 x₀,
      DifferentiableAt ℝ F z ∧ fderiv ℝ F z (σ.hamiltonianVectorField G z) = -1 := by
    filter_upwards [hGF] with z hz
    refine ⟨hF.differentiable (by simp) z, ?_⟩
    rw [← σ.apply_hamiltonianVectorField F z, ← σ.neg_eq, σ.apply_hamiltonianVectorField G z, hz]
  obtain ⟨δ, hδ, hshift⟩ := σ.exists_pos_eventually_apply_hamiltonianFlow_eq_add_mul G hXG hrate
  -- The slice `k` through `x₀`, transverse to the plane of `e = X_F(x₀)` and `e' = X_G(x₀)`.
  have hee' : σ (σ.hamiltonianVectorField G x₀) (σ.hamiltonianVectorField F x₀) = 1 :=
    (σ.apply_hamiltonianVectorField G x₀ _).trans hGF.self_of_nhds
  obtain ⟨k, hkc, hk0, hkev⟩ := σ.exists_contDiff_slice hF hG hee'
    (σ.apply_hamiltonianVectorField F x₀) (σ.apply_hamiltonianVectorField G x₀)
  -- With `A y = σ(e', y)` and `B y = -σ(e, y)`, the parametrization is
  -- `χ y = φ^F_{τ₁ y} (φ^G_{τ₂ y} (k y))`, the times being chosen so that `F ∘ χ = F x₀ - B`.
  let A : V →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (σ.toBilinForm (σ.hamiltonianVectorField G x₀))
  let B : V →L[ℝ] ℝ :=
    -LinearMap.toContinuousLinearMap (σ.toBilinForm (σ.hamiltonianVectorField F x₀))
  have hflow {H : V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (σ.hamiltonianVectorField H))
      (hH : ContDiff ℝ ∞ H) :
      ContDiff ℝ ∞ (Function.uncurry fun t x ↦ σ.hamiltonianFlow H hX t x) :=
    (σ.contDiff_uncurry_hamiltonianFlow H ⊤ hX (hH.of_le (by simp))).of_le le_self_add
  have hτ₂c : ContDiff ℝ ∞ fun y ↦ B y + F (k y) - F x₀ :=
    (B.contDiff.add (hF.comp hkc)).sub contDiff_const
  have hk₁c := (hflow hXG hG).comp (hτ₂c.prodMk hkc)
  have hFk₁ : ∀ᶠ y in 𝓝 0, F (σ.hamiltonianFlow G hXG (B y + F (k y) - F x₀) (k y)) =
      F x₀ - B y := by
    filter_upwards [hkc.continuous.continuousAt.eventually (hk0 ▸ hshift),
      hτ₂c.continuous.continuousAt.eventually_mem
        (by simpa [hk0] using Ioo_mem_nhds (neg_lt_zero.2 hδ) hδ)] with y hy hyδ
    rw [hy _ hyδ]
    ring
  let χ : V → V := fun y ↦ σ.hamiltonianFlow F hXF (A y - G (k y) + G x₀)
    (σ.hamiltonianFlow G hXG (B y + F (k y) - F x₀) (k y))
  have hχc : ContDiff ℝ ∞ χ :=
    (hflow hXF hF).comp (((A.contDiff.sub (hG.comp hkc)).add contDiff_const).prodMk hk₁c)
  refine ⟨χ, hχc, by simp [χ, hk0], ?_⟩
  filter_upwards [hFk₁.eventually_nhds, hkev] with y hy hyk
  refine ⟨?_, fun u v ↦ ?_⟩
  · refine (σ.hamiltonianFlow_conserves F hXF _ _).trans ?_
    rw [hy.self_of_nhds, ← σ.apply_hamiltonianVectorField F x₀ y]
    simp [B, sub_eq_add_neg]
  · have h := σ.apply_fderiv_hamiltonianFlow_hamiltonianFlow hXF hXG (A := A) (c₁ := G x₀)
      (hF.of_le (by simp)) (hG.of_le (by simp)) (hkc.differentiable (by simp) y).hasFDerivAt hy u v
    rw [hyk u v] at h
    refine h.trans ?_
    simp only [A, B, neg_apply, LinearMap.coe_toContinuousLinearMap']
    ring

/-- The parametrization behind `exists_openPartialHomeomorph_eq_add_fderiv`: a smooth map `χ`
with `χ 0 = x₀` which near `0` preserves `σ`, maps into `U`, and along which `f` is the affine
function `f x₀ + df_{x₀}`. -/
private theorem exists_contDiff_eventually_apply_eq_add_fderiv {f : V → ℝ} {U : Set V} {x₀ : V}
    (hU : U ∈ 𝓝 x₀) (hf : ContDiffOn ℝ ∞ f U) (hx₀ : fderiv ℝ f x₀ ≠ 0) :
    ∃ χ : V → V, ContDiff ℝ ∞ χ ∧ χ 0 = x₀ ∧ ∀ᶠ y in 𝓝 0, χ y ∈ U ∧
      f (χ y) = f x₀ + fderiv ℝ f x₀ y ∧
      ∀ u v, σ (fderiv ℝ χ y u) (fderiv ℝ χ y v) = σ u v := by
  -- Cut `f` off to a compactly supported `F`, and choose a conjugate function `G`.
  obtain ⟨F, hF, hFc, hFf⟩ := hf.exists_contDiff_eventuallyEq_of_finiteDimensional hU
  have hdF : fderiv ℝ F x₀ = fderiv ℝ f x₀ := hFf.fderiv_eq
  obtain ⟨G, hG, hGc, hGF⟩ :=
    σ.exists_fderiv_apply_hamiltonianVectorField_eq_one univ_mem hF.contDiffOn (hdF ▸ hx₀)
  obtain ⟨KF, hXF⟩ := σ.exists_lipschitzWith_hamiltonianVectorField (hF.of_le (by simp)) hFc
  obtain ⟨KG, hXG⟩ := σ.exists_lipschitzWith_hamiltonianVectorField (hG.of_le (by simp)) hGc
  obtain ⟨χ, hχc, hχ0, hχ⟩ :=
    σ.exists_contDiff_eventually_apply_eq_add_fderiv_of_conjugate hF hG hXF hXG hGF
  have hQ : U ∩ {z | F z = f z} ∈ 𝓝 (χ 0) := hχ0 ▸ inter_mem hU hFf
  refine ⟨χ, hχc, hχ0, ?_⟩
  filter_upwards [hχ, hχc.continuous.continuousAt.eventually_mem hQ] with y hy hyQ
  refine ⟨hyQ.1, ?_, hy.2⟩
  rw [← hyQ.2, hy.1, hFf.self_of_nhds, hdF]

/-- **The Carathéodory–Jacobi–Lie normal form for one function.** Let `f` be smooth near a point
`x₀` of a finite-dimensional symplectic vector space `(V, σ)`, with `df_{x₀} ≠ 0`. Then there is a
smooth chart `κ` around `x₀`, with `κ x₀ = 0`, which is symplectic, `σ(dκ u, dκ v) = σ(u, v)`,
and in which `f` is affine: `f = f x₀ + df_{x₀} ∘ κ` on the source of `κ`.

Take linear Darboux coordinates `(q₁, …, qₙ, p₁, …, pₙ)` on `(V, σ)` whose first momentum
coordinate `p₁` is the functional `df_{x₀}` (the coordinates dual to a Darboux basis whose first
`q`-vector is `X_f(x₀)`). Then `(q, p) ∘ κ` are Darboux coordinates in which `f = f x₀ + p₁`:
every function without critical point is locally a momentum of a Darboux chart. -/
theorem exists_openPartialHomeomorph_eq_add_fderiv {f : V → ℝ} {U : Set V} {x₀ : V}
    (hU : U ∈ 𝓝 x₀) (hf : ContDiffOn ℝ ∞ f U) (hx₀ : fderiv ℝ f x₀ ≠ 0) :
    ∃ κ : OpenPartialHomeomorph V V, x₀ ∈ κ.source ∧ κ x₀ = 0 ∧ κ.source ⊆ U ∧
      ContDiffOn ℝ ∞ κ κ.source ∧ ContDiffOn ℝ ∞ κ.symm κ.target ∧
      (∀ x ∈ κ.source, ∀ u v, σ (fderiv ℝ κ x u) (fderiv ℝ κ x v) = σ u v) ∧
      ∀ x ∈ κ.source, f x = f x₀ + fderiv ℝ f x₀ (κ x) := by
  obtain ⟨χ, hχ, hχ0, hev⟩ := σ.exists_contDiff_eventually_apply_eq_add_fderiv hU hf hx₀
  obtain ⟨O, hOsub, hOo, h0O⟩ := mem_nhds_iff.1 hev
  -- The derivative of `χ` at `0` is an isometry of `σ`, so it is injective, hence invertible.
  have hinj : Function.Injective (fderiv ℝ χ 0) :=
    BilinForm.IsIsometry.injective σ.separatingLeft
      (BilinForm.isIsometry_iff.2 fun u v ↦ (hOsub h0O).2.2 u v)
  let L : V ≃L[ℝ] V :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ χ 0 : V →ₗ[ℝ] V) hinj).toContinuousLinearEquiv
  have hL : (L : V →L[ℝ] V) = fderiv ℝ χ 0 := by
    ext
    simp [L]
  obtain ⟨Θ, hΘ, h0Θ, hΘO, hΘs⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hχ.contDiffOn hOo h0O (by simp) hL
  have hΘ0 : Θ 0 = x₀ := by rw [hΘ, hχ0]
  have hΘr (x : V) (hx : x ∈ Θ.target) : χ (Θ.symm x) = x := hΘ ▸ Θ.right_inv hx
  refine ⟨Θ.symm, ?_, ?_, fun x hx ↦ ?_, hΘs, ?_, fun x hx u v ↦ ?_, fun x hx ↦ ?_⟩
  · rw [OpenPartialHomeomorph.symm_source, ← hΘ0]
    exact Θ.map_source h0Θ
  · rw [← hΘ0]
    exact Θ.left_inv h0Θ
  · rw [← hΘr x hx]
    exact (hOsub (hΘO (Θ.map_target hx))).1
  · rw [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target, hΘ]
    exact hχ.contDiffOn
  · -- Differentiate `χ ∘ Θ.symm = id` near `x`: `dχ ∘ dκ = id`, and `dχ` preserves `σ`.
    set y := Θ.symm x
    have hκd : HasFDerivAt Θ.symm (fderiv ℝ Θ.symm x) x :=
      ((hΘs.differentiableOn (by simp) x hx).differentiableAt
        (Θ.open_target.mem_nhds hx)).hasFDerivAt
    have hχd : HasFDerivAt χ (fderiv ℝ χ y) y := (hχ.differentiable (by simp) y).hasFDerivAt
    have hid : (fderiv ℝ χ y).comp (fderiv ℝ Θ.symm x) = ContinuousLinearMap.id ℝ V := by
      refine (hχd.comp x hκd).unique ((hasFDerivAt_id x).congr_of_eventuallyEq ?_)
      filter_upwards [Θ.open_target.mem_nhds hx] with z hz
      exact hΘr z hz
    have h := (hOsub (hΘO (Θ.map_target hx))).2.2 (fderiv ℝ Θ.symm x u) (fderiv ℝ Θ.symm x v)
    rwa [← ContinuousLinearMap.comp_apply, hid, ← ContinuousLinearMap.comp_apply (fderiv ℝ χ y),
      hid, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply, eq_comm] at h
  · rw [OpenPartialHomeomorph.symm_source] at hx
    rw [← (hOsub (hΘO (Θ.map_target hx))).2.1, hΘr x hx]

end TauCeti.SymplecticForm
