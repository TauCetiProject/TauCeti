/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.Geometry.Symplectic.Manifold.Darboux
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.ODE.Straightening
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Darboux.Basic
import TauCeti.Geometry.Symplectic.Restrict
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
`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_eq_add`.

The proof constructs the inverse chart. Cut `f` off to a compactly supported `F` and choose a
conjugate function `G` with `{G, F} = 1` near `x₀`, a linear coordinate in a chart straightening
the Hamiltonian vector field `X_F`
(`TauCeti.SymplecticForm.exists_fderiv_apply_hamiltonianVectorField_eq_one`).
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
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_eq_add`: the normal form on a symplectic
  manifold.

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

/-- **A conjugate function.** Where `dF` does not vanish, some smooth compactly supported function
`G` has derivative `1` along the Hamiltonian vector field of `F`, that is `{G, F} = 1` near `x₀`.
In coordinates straightening that vector field, `G` is a linear coordinate. -/
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

/-- **Darboux's theorem on the slice.** Let `σ e' e = 1`, and let `F`, `G` be smooth with
`dF_{x₀} = σ(e, ·)` and `dG_{x₀} = σ(e', ·)`. On the symplectic complement `W` of the plane of
`e` and `e'`, the slice `s(w) = x₀ + w + (G(x₀ + w) - G x₀) e + (F(x₀ + w) - F x₀) e'` pulls `σ`
back to the closed form `σ|_W + dF ∧ dG`, nondegenerate at `0`; a diffeomorphism `D` of `W`
fixing `0` pulls `σ|_W` back to it near `0`. -/
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
  have hdF₀ (a : W) : fderiv ℝ F x₀ a = 0 :=
    (hFe a).symm.trans (mem_orthogonal_span_pair_iff.1 a.2).1
  have hdG₀ (a : W) : fderiv ℝ G x₀ a = 0 :=
    (hGe a).symm.trans (mem_orthogonal_span_pair_iff.1 a.2).2
  -- The slice `s : W → V` and the closed two-form `η = s^* σ` on `W`.
  let s : W → V := fun w ↦ x₀ + (w : V) + (G (x₀ + w) - G x₀) • e + (F (x₀ + w) - F x₀) • e'
  have hk (w : W) : HasFDerivAt (fun w : W ↦ x₀ + (w : V)) W.subtypeL w :=
    W.subtypeL.hasFDerivAt.const_add x₀
  have hFd (z : V) : HasFDerivAt F (fderiv ℝ F z) z :=
    (hF.differentiable (by simp) z).hasFDerivAt
  have hGd (z : V) : HasFDerivAt G (fderiv ℝ G z) z :=
    (hG.differentiable (by simp) z).hasFDerivAt
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
  let η : W → W [⋀^Fin 2]→L[ℝ] ℝ := fun w ↦ σA.compContinuousLinearMap (fderiv ℝ s w)
  have hη (w a b : W) : η w ![a, b] = σ a b + fderiv ℝ F (x₀ + w) a * fderiv ℝ G (x₀ + w) b -
      fderiv ℝ F (x₀ + w) b * fderiv ℝ G (x₀ + w) a := by
    calc η w ![a, b] = σ (fderiv ℝ s w a) (fderiv ℝ s w b) := by
          simp only [η, σA, ContinuousAlternatingMap.compContinuousLinearMap_apply,
            AlternatingMap.coe_toContinuousAlternatingMap]
          -- `SymplecticForm.isAlt` is stated for `LinearMap.BilinForm.IsAlt`, so the evaluation
          -- lemma is applied as a term.
          rw [LinearMap.IsAlt.toAlternatingMap_apply σ.isAlt]
          rfl
      _ = σ (a + fderiv ℝ G (x₀ + w) a • e + fderiv ℝ F (x₀ + w) a • e')
            (b + fderiv ℝ G (x₀ + w) b • e + fderiv ℝ F (x₀ + w) b • e') := by
          rw [(hsd w).fderiv]
          rfl
      _ = _ := by
          rw [σ.apply_add_smul_add_smul hee' a.2 b.2]
          ring
  have hη₀ (a b : W) : η 0 ![a, b] = σ a b := by
    simp [hη, hdF₀, hdG₀]
  have hηc : ContDiff ℝ ∞ η :=
    ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (ι := Fin 2) (G := ℝ) _).comp
      (hs.fderiv_right le_rfl)).clm_apply contDiff_const
  have hηd (w : W) : extDeriv η w = 0 := by
    have h := extDeriv_pullback (f := s) (x := w) (r := ∞) (differentiableAt_const (c := σA))
      hs.contDiffAt (by simp [minSmoothness_of_isRCLikeNormedField])
    rw [ContinuousAlternatingMap.extDeriv_const] at h
    refine h.trans ?_
    ext
    simp
  have hηnd : ∀ v : W, (∀ w : W, η 0 ![v, w] = 0) → v = 0 := by
    intro v hv
    refine (σ.nondegenerate_restrict_orthogonal_of_isCompl
      (σ.isAlt.isCompl_span_pair_orthogonal hee')).1 v fun w ↦ ?_
    have h := hv w
    rwa [hη₀] at h
  -- Darboux's theorem on `W` straightens `η` to the constant form `σ|_W`.
  obtain ⟨D, V₀, hD0, hV₀o, h0V₀, -, hηD⟩ :=
    exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv (r := (⊤ : ℕ∞))
      le_top isOpen_univ (mem_univ (0 : W)) hηc.contDiffOn (fun w _ ↦ hηd w) hηnd
  refine ⟨D, hD0, ?_⟩
  filter_upwards [hV₀o.mem_nhds h0V₀] with w hw a b
  rw [← hη, hηD w hw, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  refine Eq.trans ?_ (hη₀ _ _)
  congr 1
  ext i
  fin_cases i <;> rfl

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
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by simp
  have hF2 : ContDiff ℝ 2 F := hF.of_le h2
  have hG2 : ContDiff ℝ 2 G := hG.of_le h2
  obtain ⟨KF, hXF⟩ := σ.exists_lipschitzWith_hamiltonianVectorField hF2 hFc
  obtain ⟨KG, hXG⟩ := σ.exists_lipschitzWith_hamiltonianVectorField hG2 hGc
  have hflow {H : V → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (σ.hamiltonianVectorField H))
      (hH : ContDiff ℝ ∞ H) :
      ContDiff ℝ ∞ (Function.uncurry fun t x ↦ σ.hamiltonianFlow H hX t x) :=
    contDiff_infty.2 fun n ↦ (σ.contDiff_uncurry_hamiltonianFlow H n hX
      (hH.of_le (by simp))).of_le (by simp)
  -- Near `x₀` the function `F` decreases at unit rate along the flow of `G`.
  have hrate : ∀ᶠ z in 𝓝 x₀,
      DifferentiableAt ℝ F z ∧ fderiv ℝ F z (σ.hamiltonianVectorField G z) = -1 := by
    filter_upwards [hGF] with z hz
    refine ⟨hF.differentiable (by simp) z, ?_⟩
    rw [← σ.apply_hamiltonianVectorField F z, ← σ.neg_eq, σ.apply_hamiltonianVectorField G z, hz]
  obtain ⟨δ, hδ, hshift⟩ := σ.exists_pos_eventually_apply_hamiltonianFlow_eq_add_mul G hXG hrate
  obtain ⟨N, hNshift, hNo, hx₀N⟩ := mem_nhds_iff.1 hshift
  -- The symplectic plane of `e = X_F(x₀)` and `e' = X_G(x₀)`, and its complement `W`.
  set e := σ.hamiltonianVectorField F x₀
  set e' := σ.hamiltonianVectorField G x₀
  have hee' : σ e' e = 1 := (σ.apply_hamiltonianVectorField G x₀ e).trans hGF.self_of_nhds
  set W := σ.orthogonal (Submodule.span ℝ {e, e'})
  set Z : V →L[ℝ] W := LinearMap.toContinuousLinearMap (σ.orthogonalSpanPairProj hee')
  -- Darboux's theorem on `W` for the pullback of `σ` to the slice through `x₀`.
  obtain ⟨D, hD0, hDev⟩ := σ.exists_diffeomorph_orthogonal_span_pair hF hG hee'
    (σ.apply_hamiltonianVectorField F x₀) (σ.apply_hamiltonianVectorField G x₀)
  obtain ⟨V₀, hV₀D, hV₀o, h0V₀⟩ := mem_nhds_iff.1 hDev
  have hFd (z : V) : HasFDerivAt F (fderiv ℝ F z) z :=
    (hF.differentiable (by simp) z).hasFDerivAt
  have hGd (z : V) : HasFDerivAt G (fderiv ℝ G z) z :=
    (hG.differentiable (by simp) z).hasFDerivAt
  have hDs0 : D.symm 0 = 0 := D.injective ((D.apply_symm_apply 0).trans hD0.symm)
  have hDsc : ContDiff ℝ ∞ (D.symm : W → W) := D.symm.contMDiff.contDiff
  -- Write `y = A y • e + B y • e' + Z y` with `A y = σ(e', y)`, `B y = -σ(e, y)` and `Z y ∈ W`.
  -- The parametrization is `χ y = φ^F_{τ₁ y} (φ^G_{τ₂ y} (x₀ + D⁻¹ (Z y)))`, the times being
  -- chosen so that `G ∘ χ = G x₀ + A` and `F ∘ χ = F x₀ - B`.
  let A : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (σ.toBilinForm e')
  let B : V →L[ℝ] ℝ := -LinearMap.toContinuousLinearMap (σ.toBilinForm e)
  let k₂ : V → V := fun y ↦ x₀ + (D.symm (Z y) : V)
  let τ₂ : V → ℝ := fun y ↦ B y + F (k₂ y) - F x₀
  let k₁ : V → V := fun y ↦ σ.hamiltonianFlow G hXG (τ₂ y) (k₂ y)
  let τ₁ : V → ℝ := fun y ↦ A y - G (k₂ y) + G x₀
  let χ : V → V := fun y ↦ σ.hamiltonianFlow F hXF (τ₁ y) (k₁ y)
  have hk₂c : ContDiff ℝ ∞ k₂ :=
    contDiff_const.add (W.subtypeL.contDiff.comp (hDsc.comp Z.contDiff))
  have hτ₂c : ContDiff ℝ ∞ τ₂ := (B.contDiff.add (hF.comp hk₂c)).sub contDiff_const
  have hk₁c : ContDiff ℝ ∞ k₁ := (hflow hXG hG).comp (hτ₂c.prodMk hk₂c)
  have hτ₁c : ContDiff ℝ ∞ τ₁ := (A.contDiff.sub (hG.comp hk₂c)).add contDiff_const
  have hχc : ContDiff ℝ ∞ χ := (hflow hXF hF).comp (hτ₁c.prodMk hk₁c)
  have hk₂0 : k₂ 0 = x₀ := by simp [k₂, hDs0]
  have hτ₂0 : τ₂ 0 = 0 := by simp [τ₂, hk₂0]
  have hk₁0 : k₁ 0 = x₀ := by simp [k₁, hτ₂0, hk₂0]
  have hτ₁0 : τ₁ 0 = 0 := by simp [τ₁, hk₂0]
  have hχ0 : χ 0 = x₀ := by simp [χ, hτ₁0, hk₁0]
  -- Along `χ`, the function `F` is `F x₀ - B`.
  have hFk₁ (y : V) (hy₁ : k₂ y ∈ N) (hy₂ : τ₂ y ∈ Ioo (-δ) δ) : F (k₁ y) = F x₀ - B y := by
    simp only [k₁, hNshift hy₁ _ hy₂, τ₂]
    ring
  have hFχ (y : V) : F (χ y) = F (k₁ y) := σ.hamiltonianFlow_conserves F hXF _ _
  -- The open conditions near `0` under which the identities hold.
  have hQ : U ∩ {z | F z = f z} ∈ 𝓝 x₀ := inter_mem hU hFf
  have hev : ∀ᶠ y in 𝓝 (0 : V), D.symm (Z y) ∈ V₀ ∧ k₂ y ∈ N ∧ τ₂ y ∈ Ioo (-δ) δ ∧
      χ y ∈ U ∩ {z | F z = f z} := by
    refine ((hDsc.comp Z.contDiff).continuous.continuousAt.eventually_mem ?_).and
      ((hk₂c.continuous.continuousAt.eventually_mem ?_).and
      ((hτ₂c.continuous.continuousAt.eventually_mem ?_).and
      (hχc.continuous.continuousAt.eventually_mem ?_)))
    · simpa [hDs0] using hV₀o.mem_nhds h0V₀
    · rw [hk₂0]
      exact hNo.mem_nhds hx₀N
    · rw [hτ₂0]
      exact Ioo_mem_nhds (by linarith) hδ
    · rwa [hχ0]
  refine ⟨χ, hχc, hχ0, ?_⟩
  filter_upwards [hev, hev.eventually_nhds] with y hy hyn
  obtain ⟨hyV₀, hyN, hyδ, hyU, hyf⟩ := hy
  refine ⟨hyU, ?_, fun u v ↦ ?_⟩
  · -- `f (χ y) = F (χ y) = F x₀ - B y`, and `-B = σ(e, ·) = dF_{x₀} = df_{x₀}`.
    rw [← hyf, hFχ, hFk₁ y hyN hyδ, ← hFf.self_of_nhds, ← hdF,
      ← σ.apply_hamiltonianVectorField F x₀ y]
    simp [B, sub_eq_add_neg, e]
  -- The derivatives of the building blocks of `χ` at `y`.
  set w := D.symm (Z y) with hw
  let dk₂ : V →L[ℝ] V := W.subtypeL.comp ((fderiv ℝ D.symm (Z y)).comp (Z : V →L[ℝ] W))
  have hk₂d : HasFDerivAt k₂ dk₂ y := by
    have hD' : HasFDerivAt (D.symm : W → W) (fderiv ℝ D.symm (Z y)) (Z y) :=
      (hDsc.differentiable (by simp) _).hasFDerivAt
    exact (W.subtypeL.hasFDerivAt.comp y (hD'.comp y Z.hasFDerivAt)).const_add x₀
  have hτ₂d : HasFDerivAt τ₂ (B + (fderiv ℝ F (k₂ y)).comp dk₂) y :=
    (B.hasFDerivAt.add ((hFd _).comp y hk₂d)).sub_const _
  have hτ₁d : HasFDerivAt τ₁ (A - (fderiv ℝ G (k₂ y)).comp dk₂) y :=
    (A.hasFDerivAt.sub ((hGd _).comp y hk₂d)).add_const _
  have hk₁d : HasFDerivAt k₁ (fderiv ℝ k₁ y) y := (hk₁c.differentiable (by simp) y).hasFDerivAt
  -- `F ∘ k₁ = F x₀ - B` near `y`, so `dF (dk₁ v) = -B v`.
  have hFk₁d (v : V) : fderiv ℝ F (k₁ y) (fderiv ℝ k₁ y v) = -B v := by
    have h₁ : HasFDerivAt (fun y' ↦ F (k₁ y')) ((fderiv ℝ F (k₁ y)).comp (fderiv ℝ k₁ y)) y :=
      (hFd _).comp y hk₁d
    have h₂ : HasFDerivAt (fun y' ↦ F x₀ - B y') (-B) y := by
      simpa using B.hasFDerivAt.const_sub (F x₀)
    have heq : (fun y' ↦ F (k₁ y')) =ᶠ[𝓝 y] fun y' ↦ F x₀ - B y' := by
      filter_upwards [hyn] with y' hy'
      exact hFk₁ y' hy'.2.1 hy'.2.2.1
    exact congrArg (fun L : V →L[ℝ] ℝ ↦ L v) (h₁.unique (h₂.congr_of_eventuallyEq heq))
  -- The two flow pullback formulas.
  have hχ' : σ (fderiv ℝ χ y u) (fderiv ℝ χ y v) =
      σ (fderiv ℝ k₁ y u) (fderiv ℝ k₁ y v) +
        (A - (fderiv ℝ G (k₂ y)).comp dk₂) u * fderiv ℝ F (k₁ y) (fderiv ℝ k₁ y v) -
        (A - (fderiv ℝ G (k₂ y)).comp dk₂) v * fderiv ℝ F (k₁ y) (fderiv ℝ k₁ y u) :=
    σ.apply_fderiv_hamiltonianFlow_comp F hXF hF2 hτ₁d hk₁d u v
  have hk₁' : σ (fderiv ℝ k₁ y u) (fderiv ℝ k₁ y v) =
      σ (dk₂ u) (dk₂ v) + (B + (fderiv ℝ F (k₂ y)).comp dk₂) u * fderiv ℝ G (k₂ y) (dk₂ v) -
        (B + (fderiv ℝ F (k₂ y)).comp dk₂) v * fderiv ℝ G (k₂ y) (dk₂ u) :=
    σ.apply_fderiv_hamiltonianFlow_comp G hXG hG2 hτ₂d hk₂d u v
  -- Darboux on `W`: the slice terms combine to `η w`, which is `σ` on `Z u, Z v`.
  have hslice : σ (dk₂ u) (dk₂ v) + fderiv ℝ F (k₂ y) (dk₂ u) * fderiv ℝ G (k₂ y) (dk₂ v) -
      fderiv ℝ F (k₂ y) (dk₂ v) * fderiv ℝ G (k₂ y) (dk₂ u) = σ (Z u) (Z v) := by
    have h := hV₀D hyV₀ (fderiv ℝ D.symm (Z y) (Z u)) (fderiv ℝ D.symm (Z y) (Z v))
    rwa [hw, D.fderiv_apply_fderiv_symm_apply (by simp),
      D.fderiv_apply_fderiv_symm_apply (by simp)] at h
  have hσuv : σ u v = σ (Z u) (Z v) + (σ e' u * σ e v - σ e' v * σ e u) :=
    σ.apply_eq_orthogonalSpanPairProj hee' u v
  -- `filter_upwards` beta-reduced the goal, so the coercion of `σ` is unfolded there.
  beta_reduce at hχ' hk₁' hslice hσuv
  rw [hχ', hk₁', hFk₁d, hFk₁d, hσuv, ← hslice]
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply, neg_apply, A, B,
    LinearMap.coe_toContinuousLinearMap']
  ring

/-- **The Carathéodory–Jacobi–Lie normal form for one function.** Let `f` be smooth near a point
`x₀` of a finite-dimensional symplectic vector space `(V, σ)`, with `df_{x₀} ≠ 0`. Then there is a
smooth chart `κ` around `x₀`, with `κ x₀ = 0`, which is symplectic, `σ(dκ u, dκ v) = σ(u, v)`,
and in which `f` is affine: `f = f x₀ + df_{x₀} ∘ κ` on the source of `κ`.

In a symplectic basis `(q₁, …, qₙ, p₁, …, pₙ)` of `V` whose first momentum `p₁` is `df_{x₀}`, the
coordinates `(q, p) ∘ κ` are therefore Darboux coordinates in which `f = f x₀ + p₁`: every function
without critical point is locally a momentum of a Darboux chart. -/
theorem exists_openPartialHomeomorph_eq_add_fderiv {f : V → ℝ} {U : Set V} {x₀ : V}
    (hU : U ∈ 𝓝 x₀) (hf : ContDiffOn ℝ ∞ f U) (hx₀ : fderiv ℝ f x₀ ≠ 0) :
    ∃ κ : OpenPartialHomeomorph V V, x₀ ∈ κ.source ∧ κ x₀ = 0 ∧ κ.source ⊆ U ∧
      ContDiffOn ℝ ∞ κ κ.source ∧ ContDiffOn ℝ ∞ κ.symm κ.target ∧
      (∀ x ∈ κ.source, ∀ u v, σ (fderiv ℝ κ x u) (fderiv ℝ κ x v) = σ u v) ∧
      ∀ x ∈ κ.source, f x = f x₀ + fderiv ℝ f x₀ (κ x) := by
  obtain ⟨χ, hχ, hχ0, hev⟩ := σ.exists_contDiff_eventually_apply_eq_add_fderiv hU hf hx₀
  obtain ⟨O, hOsub, hOo, h0O⟩ := mem_nhds_iff.1 hev
  -- The derivative of `χ` at `0` preserves `σ`, so it is injective, hence invertible.
  have hinj : Function.Injective (fderiv ℝ χ 0) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu ↦ σ.nondegenerate.1 u fun w ↦ ?_
    have h := (hOsub h0O).2.2 u w
    rw [hu] at h
    exact h.symm.trans (LinearMap.map_zero₂ σ.toBilinForm _)
  let L : V ≃L[ℝ] V :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ χ 0 : V →ₗ[ℝ] V) hinj).toContinuousLinearEquiv
  have hL : (L : V →L[ℝ] V) = fderiv ℝ χ 0 := by
    ext
    rfl
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

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The Carathéodory–Jacobi–Lie normal form for one function on a symplectic manifold.** Let
`f` be smooth near a point `x₀` of a finite-dimensional boundaryless symplectic manifold
`(M, form)`, with nonzero differential at `x₀`. Then some Darboux chart around `x₀`, pulling a
constant symplectic form `form₀` on the model space back to `form`, makes `f` affine:
`f = f x₀ + ℓ ∘ chart` for a nonzero linear functional `ℓ`. In a symplectic basis of `form₀`
whose first momentum is `ℓ`, the function `f - f x₀` is the momentum coordinate `p₁` of a
Darboux chart. -/
theorem IsSymplectic.exists_darbouxChart_eq_add {form : SmoothTwoForm I M}
    (hform : form.IsSymplectic) {f : M → ℝ} {U : Set M} {x₀ : M} (hU : U ∈ 𝓝 x₀)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hx₀ : mvfderiv I f x₀ ≠ 0) :
    ∃ (chart : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (form₀ : SymplecticForm E) (ℓ : E →L[ℝ] ℝ),
      ℓ ≠ 0 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧ chart.source ⊆ U ∧
      (∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        form.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w)) ∧
      ∀ x ∈ chart.source, f x = f x₀ + ℓ (chart x) := by
  obtain ⟨c, form₀, hx₀c, hc0, hc⟩ := hform.exists_darbouxChart x₀
  -- Read `f` in the Darboux chart `c`, on an open neighbourhood `T` of `0 = c x₀`.
  let g : E → ℝ := fun y ↦ f (c.toPartialEquiv.symm y)
  set T := c.target ∩ c.toPartialEquiv.symm ⁻¹' interior U
  have hTo : IsOpen T := c.toOpenPartialHomeomorph.continuousOn_symm.isOpen_inter_preimage
    c.open_target isOpen_interior
  have hlinv (x : M) (hx : x ∈ c.source) : c.toPartialEquiv.symm (c x) = x :=
    c.toPartialEquiv.left_inv hx
  have hcs0 : c.toPartialEquiv.symm 0 = x₀ := by rw [← hc0, hlinv x₀ hx₀c]
  have h0T : (0 : E) ∈ T := by
    refine ⟨hc0 ▸ c.toPartialEquiv.map_source hx₀c, ?_⟩
    rw [mem_preimage, hcs0]
    exact mem_interior_iff_mem_nhds.2 hU
  have hg : ContDiffOn ℝ ∞ g T :=
    contMDiffOn_iff_contDiffOn.1 ((hf.mono interior_subset).comp
      (c.contMDiffOn_invFun.mono inter_subset_left) fun y hy ↦ hy.2)
  have hgd : DifferentiableAt ℝ g 0 := (hg.differentiableOn (by simp) 0 h0T).differentiableAt
    (hTo.mem_nhds h0T)
  have hcd (x : M) (hx : x ∈ c.source) : MDifferentiableAt I 𝓘(ℝ, E) c x :=
    (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  -- `f = g ∘ c` near `x₀`, so `dg_0 ≠ 0`.
  have hg0 : fderiv ℝ g 0 ≠ 0 := by
    intro h
    refine hx₀ (ContinuousLinearMap.ext fun v ↦ ?_)
    have hfg : f =ᶠ[𝓝 x₀] g ∘ c := by
      filter_upwards [c.open_source.mem_nhds hx₀c] with x hx
      simp [g, hlinv x hx]
    rw [hfg.mvfderiv_eq, mvfderiv_comp_apply_of_differentiableAt (hc0 ▸ hgd) (hcd x₀ hx₀c), hc0,
      h]
    rfl
  obtain ⟨κ, h0κ, hκ0, hκT, hκc, hκs, hκσ, hκg⟩ :=
    form₀.exists_openPartialHomeomorph_eq_add_fderiv (hTo.mem_nhds h0T) hg hg0
  let κ' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { κ.toPartialEquiv with
      open_source := κ.open_source
      open_target := κ.open_target
      contMDiffOn_toFun := hκc.contMDiffOn
      contMDiffOn_invFun := hκs.contMDiffOn }
  have hsrc (x : M) : x ∈ (c.trans κ').source ↔ x ∈ c.source ∧ c x ∈ κ.source := by
    rw [PartialDiffeomorph.trans_source]
    rfl
  have hcoe (x : M) : (c.trans κ') x = κ (c x) := by
    rw [PartialDiffeomorph.coe_trans]
    rfl
  refine ⟨c.trans κ', form₀, fderiv ℝ g 0, hg0, (hsrc x₀).2 ⟨hx₀c, hc0 ▸ h0κ⟩,
    by rw [hcoe, hc0, hκ0], fun x hx ↦ ?_, fun x hx v w ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨hxc, hxκ⟩ := (hsrc x).1 hx
    rw [← hlinv x hxc]
    exact interior_subset (hκT hxκ).2
  · obtain ⟨hxc, hxκ⟩ := (hsrc x).1 hx
    have hκd : DifferentiableAt ℝ κ (c x) :=
      (hκc.differentiableOn (by simp) _ hxκ).differentiableAt (κ.open_source.mem_nhds hxκ)
    have hd (u : TangentSpace I x) :
        mvfderiv I (c.trans κ') x u = fderiv ℝ κ (c x) (mvfderiv I c x u) := by
      have heq : ⇑(c.trans κ') = ⇑κ ∘ ⇑c := funext hcoe
      rw [heq]
      exact mvfderiv_comp_apply_of_differentiableAt hκd (hcd x hxc) u
    rw [hd, hd, hκσ _ hxκ, hc x hxc]
  · obtain ⟨hxc, hxκ⟩ := (hsrc x).1 hx
    have h := hκg (c x) hxκ
    simp only [g, hlinv x hxc, hcs0] at h
    rw [h, hcoe]

end TauCeti.SmoothTwoForm
