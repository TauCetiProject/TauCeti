/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.RegularValue.Section
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Angle

/-!
# Isotropic local sections of a Liouville integrable system

Let `σ` be a symplectic form on a boundaryless manifold `M`, and let `F : M → (ι → ℝ)` be a smooth
family of pairwise Poisson-commuting functions with complete Hamiltonian vector fields, with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Their flows generate an action
`v • y` of `ι → ℝ` on `M` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`) preserving
the levels of `F`.

A local section `s` of `F`, with `F (s c) = c`, is **isotropic** when `s^* σ = 0`. This file shows
that every smooth section over an open star-convex set `t` can be made isotropic by moving it along
the flow action. Moving `s` by `h : (ι → ℝ) → (ι → ℝ)` changes `s^* σ` by `∑ᵢ dhᵢ ∧ dcᵢ`
(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_hamiltonianFlowAction_section`). The two-form
`s^* σ` on `t` is closed, because `σ` is, so by the Poincaré lemma it is `dβ` for a one-form
`β = ∑ᵢ βᵢ dcᵢ` on `t`. Since `dβ = ∑ᵢ dβᵢ ∧ dcᵢ`, the choice `hᵢ = -βᵢ` gives `(h • s)^* σ = 0`
(`IsSymplectic.exists_contDiffOn_eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero`).
The primitive may be chosen to vanish at a given centre `c₀` of `t`, and then `h • s` agrees with
`s` at `c₀`.

Combined with the existence of smooth local sections through regular points
(`TauCeti.IsRegularPoint.exists_contMDiffOn_section`), every regular point `x` of `F` lies on an
isotropic smooth local section of `F` through `x`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_contMDiffOn_section_eval₂_mfderiv_eq_zero`).

Near a compact connected component of a level consisting of regular points, on a manifold of
dimension `2 |ι|`, take such an isotropic section together with the periods `λ⁽ⁱ⁾` along it and the
action variables `A` (`IsSymplectic.exists_isLocalDiffeomorphAt_action_of_isCompact`).
Then the angle map `Ψ(θ, c) = (∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)) • s(c)`
(`TauCeti.SmoothTwoForm.IsSymplectic.angleMap`) pulls `σ` back to the standard form

`Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ`

for all values `c` near `F x`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_eval₂_mfderiv_angleMap_eq_of_isCompact`). In particular
the term `s^* σ` of the general formula `Ψ^* σ = ∑ᵢ dθᵢ ∧ dAᵢ + s^* σ`
(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_angleMap`) can always be removed by the choice of
section.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `exists_contDiffOn_eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero`: a smooth section over an
  open star-convex set, moved by a suitable smooth `h` vanishing at the centre, is isotropic.
* `exists_contMDiffOn_section_eval₂_mfderiv_eq_zero`: every regular point of `F` lies on an
  isotropic smooth local section.
* `exists_eval₂_mfderiv_angleMap_eq_of_isCompact`: near a compact regular component of a level,
  there is an isotropic smooth local section whose angle map pulls `σ` back to `∑ᵢ dθᵢ ∧ dAᵢ`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (Lagrangian sections and the symplectic form in action-angle coordinates).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

open Set Filter Module Topology Function Real
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff Matrix

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {s : (ι → ℝ) → M}

include hσ hF hcomm hc

/-- **Making a section isotropic.** Let `s` be a smooth section of `F` over an open set `t`,
star-convex with respect to `c₀`. Then there is a smooth map `h : (ι → ℝ) → (ι → ℝ)` on `t`,
vanishing at `c₀`, such that the section `c ↦ h c • s c` of `F` is isotropic:

`(h • s)^* σ = 0` on `t`. -/
theorem exists_contDiffOn_eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero
    {t : Set (ι → ℝ)} {c₀ : ι → ℝ} (ht : IsOpen t) (htc : StarConvex ℝ c₀ t)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c) :
    ∃ h : (ι → ℝ) → ι → ℝ, ContDiffOn ℝ ∞ h t ∧ h c₀ = 0 ∧ ∀ c ∈ t, ∀ b b' : ι → ℝ,
      SmoothBundleForm.eval₂ σ ((hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
        (mfderiv 𝓘(ℝ, ι → ℝ) I
          (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c)) c b)
        (mfderiv 𝓘(ℝ, ι → ℝ) I
          (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c)) c b') = 0 := by
  classical
  -- The flat two-form `ρ = s^* σ` on `t` is smooth and closed, so the Poincaré lemma gives a
  -- primitive `β`, a one-form vanishing at `c₀`. Its coefficients `βᵢ = β(eᵢ)` satisfy
  -- `dβ = ∑ᵢ dβᵢ ∧ dcᵢ`, so `hᵢ = -βᵢ` cancels `s^* σ` in the formula
  -- `(h • s)^* σ = s^* σ + ∑ᵢ dhᵢ ∧ dcᵢ`.
  set ρ : (ι → ℝ) → (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ := mpullbackWithin 𝓘(ℝ, ι → ℝ) I s t σ.1
    with hρ
  have hρs : ContDiffOn ℝ ∞ ρ t := by
    have h := ContMDiffOn.mpullbackWithin_form (σ.contMDiff.contMDiffOn (s := univ)) hs
      (by simp) (mapsTo_univ _ _) ht.uniqueMDiffOn
    exact fun c hc ↦ RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace (h c hc)
  have hdρ : ∀ c ∈ t, extDeriv ρ c = 0 := by
    intro c hct
    have h : extDerivWithin ρ t c = 0 := by
      have h := extDerivWithin_mpullbackWithin (φ := σ.1) ((hs c hct).of_le (by simp))
        ht.uniqueDiffOn (subset_closure (ht.interior_eq.symm ▸ hct)) hct (σ.mdifferentiable _)
      rw [(SmoothForm.isClosed_def σ).1 hσ.isClosed, mpullbackWithin_zero] at h
      exact h
    rwa [← extDerivWithin_of_isOpen ht hct]
  obtain ⟨β, hβs, hβ0, hβ⟩ := htc.exists_contDiffOn_forall_extDeriv_eq ht (r := ⊤) le_top hρs hdρ
  -- `hᵢ(c) = -β_c(eᵢ)` for the standard basis vectors `eᵢ`.
  set h : (ι → ℝ) → ι → ℝ := fun c i ↦ -β c (fun _ ↦ Pi.single i 1) with hh
  have hhs : ContDiffOn ℝ ∞ h t := contDiffOn_pi.2 fun i ↦
    ((ContinuousAlternatingMap.apply ℝ (ι → ℝ) ℝ _).contDiff.comp_contDiffOn hβs).neg
  refine ⟨h, hhs, funext fun i ↦ by simp [hh, hβ0], fun c hct b b' ↦ ?_⟩
  rw [hσ.eval₂_mfderiv_hamiltonianFlowAction_section hF hcomm hc
    ((hs.contMDiffAt (ht.mem_nhds hct)).mdifferentiableAt (by simp))
    (eventually_of_mem (ht.mem_nhds hct) hFs)
    ((hhs.differentiableOn (by simp)).differentiableAt (ht.mem_nhds hct))]
  -- `s^* σ (b, b') = ρ_c (b, b') = dβ_c (b, b')`.
  have h1 : SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = extDeriv β c ![b, b'] := by
    rw [hβ c hct, SmoothBundleForm.eval₂_apply, hρ]
    refine Eq.trans ?_ (mpullbackWithin_apply s t σ.1 c ![b, b']).symm
    congr 1
    funext i
    fin_cases i <;> simp [mfderivWithin_of_isOpen ht hct]
  -- `dhᵢ = -dβᵢ` for the coefficients `βᵢ = β(eᵢ)`, and `dβ = ∑ᵢ dβᵢ ∧ dcᵢ`.
  have hβd := (hβs.differentiableOn (by simp)).differentiableAt (ht.mem_nhds hct)
  have hd : HasFDerivAt h (ContinuousLinearMap.pi fun i ↦
      -fderiv ℝ (fun y ↦ β y fun _ ↦ Pi.single i 1) c) c :=
    hasFDerivAt_pi'.2 fun i ↦ (hβd.continuousAlternatingMap_apply_const _).hasFDerivAt.neg
  rw [h1, extDeriv_apply_pair_eq_sum hβd, hd.fderiv]
  simp [dotProduct, Finset.sum_sub_distrib, mul_comm]

/-- **Isotropic sections through regular points.** Every regular point `x` of `F` lies on an
isotropic smooth local section of `F`: there are an open set `t ∋ F x` and a smooth section `s` of
`F` over `t` with `s (F x) = x` and `s^* σ = 0` on `t`. -/
theorem exists_contMDiffOn_section_eval₂_mfderiv_eq_zero {x : M}
    (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) :
    ∃ t : Set (ι → ℝ), IsOpen t ∧ F x ∈ t ∧ ∃ s : (ι → ℝ) → M, s (F x) = x ∧
      ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t ∧ (∀ c ∈ t, F (s c) = c) ∧ ∀ c ∈ t, ∀ b b' : ι → ℝ,
        SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
          (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0 := by
  obtain ⟨t₀, ht₀, hxt₀, s₀, hs₀x, hs₀, hFs₀⟩ :=
    hreg.exists_contMDiffOn_section hF.contMDiffOn isOpen_univ (mem_univ x) (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ht₀ (F x) hxt₀
  set t := Metric.ball (F x) ε
  obtain ⟨h, hh, hh0, hL⟩ :=
    hσ.exists_contDiffOn_eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero hF hcomm hc
      Metric.isOpen_ball ((convex_ball (F x) ε).starConvex (Metric.mem_ball_self hε))
      (hs₀.mono hball) fun c hct ↦ hFs₀ c (hball hct)
  refine ⟨t, Metric.isOpen_ball, Metric.mem_ball_self hε,
    fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s₀ c), ?_, ?_, fun c hct ↦ ?_, hL⟩
  · simp only [hh0, hσ.hamiltonianFlowAction_zero_apply hF hcomm hc, hs₀x]
  · exact (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).comp_contMDiffOn
      ((contMDiffOn_iff_contDiffOn.2 hh).prodMk (hs₀.mono hball))
  · rw [hσ.apply_hamiltonianFlowAction hF hcomm hc, hFs₀ c (hball hct)]

/-- **The symplectic form in action-angle variables of an isotropic section.** On a manifold of
dimension `2 · |ι|`, let the connected component of `x` in its level `F⁻¹(F x)` be compact and
consist of regular points of `F`. Then there are a local section `s` of `F` through `x`, functions
`λ⁽ⁱ⁾` and a map `A : (ι → ℝ) → (ι → ℝ)`, a local diffeomorphism at `F x`, such that for every `c`
near `F x`:

* `s` is smooth at `c` and isotropic there, `s^* σ = 0`;
* the functions `λ⁽ⁱ⁾` are smooth at `c`;
* the vectors `λ⁽ⁱ⁾ c` are linearly independent and generate the period lattice of `s c`;
* the differential of `Aᵢ` at `c` is `(2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ(c) dcⱼ`;
* the period lattice of `s c` is the transpose lattice `2π (DA_c)ᵀ ℤⁿ`
  (`ContinuousLinearMap.transposeLattice`): a vector `v` is a period of `s c` exactly when
  `v ⬝ᵥ dc = 2π ∑ᵢ nᵢ dAᵢ` for some integers `nᵢ`;
* the angle map `Ψ(θ, c) = (∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)) • s(c)` pulls `σ` back to `∑ᵢ dθᵢ ∧ dAᵢ` at
  `(θ, c)`, for every `θ`. -/
theorem exists_eval₂_mfderiv_angleMap_eq_of_isCompact (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ (s : (ι → ℝ) → M) (p : ι → (ι → ℝ) → ι → ℝ) (A : (ι → ℝ) → ι → ℝ), s (F x) = x ∧
      IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A (F x) ∧ ∀ᶠ c in 𝓝 (F x),
        F (s c) = c ∧ ContMDiffAt 𝓘(ℝ, ι → ℝ) I ∞ s c ∧
        (∀ b b' : ι → ℝ, SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
          (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0) ∧
        (∀ i, ContDiffAt ℝ ∞ (p i) c) ∧ LinearIndependent ℝ (fun i ↦ p i c) ∧
        hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
          AddSubgroup.closure (range fun i ↦ p i c) ∧
        (∀ i, HasFDerivAt (fun c ↦ A c i)
          ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c) ∧
        hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
          ((2 * π) • fderiv ℝ A c).transposeLattice ∧
        ∀ θ a a' b b' : ι → ℝ,
          SmoothBundleForm.eval₂ σ (hσ.angleMap hF hcomm hc s p (θ, c))
            (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a, b))
            (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (hσ.angleMap hF hcomm hc s p) (θ, c) (a', b')) =
          ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) c b' - a' i * fderiv ℝ (fun c ↦ A c i) c b) := by
  obtain ⟨t, ht, hxt, s, hsx, hs, hFs, hL⟩ :=
    hσ.exists_contMDiffOn_section_eval₂_mfderiv_eq_zero hF hcomm hc
      (hreg x (mem_connectedComponentIn (by simp)))
  obtain ⟨p, A, hA, hpA⟩ := hσ.exists_isLocalDiffeomorphAt_action_of_isCompact hF hcomm hc hdim
    hreg hK ht hxt hsx hs hFs
  refine ⟨s, p, A, hsx, hA, ?_⟩
  filter_upwards [hpA, hpA.eventually_nhds, ht.eventually_mem hxt,
    (ht.eventually_mem hxt).eventually_nhds] with c hcA hcA' hct hct'
  have hsc := hs.contMDiffAt (ht.mem_nhds hct)
  refine ⟨hFs c hct, hsc, hL c hct, hcA.1, hcA.2.1, hcA.2.2.1, hcA.2.2.2.1, hcA.2.2.2.2,
    fun θ a a' b b' ↦ ?_⟩
  exact hσ.eval₂_mfderiv_angleMap_of_eval₂_eq_zero hF hcomm hc (hsc.mdifferentiableAt (by simp))
    (hct'.mono fun c' hc' ↦ hFs c' hc') (hL c hct) (fun i ↦ (hcA.1 i).differentiableAt (by simp))
    (fun i ↦ hcA'.mono fun c' hc' ↦ hc'.2.2.1 ▸ AddSubgroup.subset_closure (mem_range_self i))
    hcA.2.2.2.1 θ a a' b b'

end IsSymplectic

end SmoothTwoForm

end TauCeti
