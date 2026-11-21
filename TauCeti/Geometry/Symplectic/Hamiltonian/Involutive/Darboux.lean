/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Hamiltonian.DarbouxChart
public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.PartialDiffeomorph
import TauCeti.Geometry.Manifold.Flow.Straightening
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Darboux.Momenta
import TauCeti.Geometry.Symplectic.Hamiltonian.Bracket

/-!
# Darboux charts in which commuting functions are the momenta

Let `σ` be a symplectic form on a manifold `M` of dimension `2n`, with the conventions
`ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`, and let `F = (F₁, …, Fₙ) : M → ℝⁿ` be smooth,
with pairwise Poisson-commuting components near a point `x` and independent differentials at `x`.
This file proves the case `k = n` of the **Carathéodory–Jacobi–Lie theorem**: near `x` there are
Darboux coordinates `(q, p)` with momenta `p = F`. Precisely, there is a smooth partial
diffeomorphism `chart` from `M` to `(ι → ℝ) × (ι → ℝ)` with `chart x = (0, F x)`, second component
`F`, and pulling `∑ᵢ dqᵢ ∧ dpᵢ` back to `σ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_snd_eq`). No compactness of the levels of
`F` and no completeness of the Hamiltonian vector fields is needed, in contrast with the local
action-angle coordinates near a compact regular level.

The proof has two steps.

* **A flow box.** The Hamiltonian vector fields `X_{Fᵢ}` commute near `x`, since
  `[X_{Fᵢ}, X_{Fⱼ}] = -X_{{Fᵢ, Fⱼ}}`, and they are independent at `x`. A chart `φ` straightening
  them to constant vectors `uᵢ`, followed by a linear form `T` with `T uᵢ = eᵢ`, gives the map
  `y ↦ (T(φ y), F y)`. Its differential sends `X_{Fᵢ}` to `(eᵢ, 0)`, because `dFⱼ(X_{Fᵢ}) =
  {Fⱼ, Fᵢ} = 0`, and it is injective at `x` because `ker dF_x` is spanned by the `X_{Fᵢ}(x)`. By the
  inverse function theorem it is a partial diffeomorphism (`TauCeti.SmoothTwoForm.IsSymplectic.`
  `exists_partialDiffeomorph_mvfderiv_hamiltonianVectorField_eq_of_isInteriorPoint`).
* **A shear.** In this flow box, `σ` becomes a closed two-form `μ` on `(ι → ℝ) × (ι → ℝ)` with
  `μ(∂_{tᵢ}, ·) = dcᵢ`, which is `∑ᵢ d(tᵢ + aᵢ(c)) ∧ dcᵢ` near the image of `x`
  (`TauCeti.exists_apply_eq_sum_of_apply_inl_single_eq_snd`). Composing with the shear
  `(t, c) ↦ (t - t₀ + a(c), c)` gives the Darboux chart.

## References

* P. Libermann and C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, Reidel, 1987,
  Chapter III (the Carathéodory–Jacobi–Lie theorem).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (Liouville's theorem on integrable systems).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 9.46 (the
  canonical form for commuting vector fields).
-/

public section

noncomputable section

open Set Filter Function Module VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] {F : M → ι → ℝ} {x : M}

omit [Fintype ι] in
/-- The derivative of the shear `(t, c) ↦ (t - t₀ + a(c), c)` of `(ι → ℝ) × (ι → ℝ)`. -/
private theorem fderiv_shear_apply [Finite ι] {a : (ι → ℝ) → ι → ℝ} {t₀ : ι → ℝ}
    {q : (ι → ℝ) × (ι → ℝ)} (ha : DifferentiableAt ℝ a q.2) (u : (ι → ℝ) × (ι → ℝ)) :
    fderiv ℝ (fun q : (ι → ℝ) × (ι → ℝ) ↦ (q.1 - t₀ + a q.2, q.2)) q u =
      (u.1 + fderiv ℝ a q.2 u.2, u.2) := by
  have := Fintype.ofFinite ι
  have h : HasFDerivAt (fun q : (ι → ℝ) × (ι → ℝ) ↦ (q.1 - t₀ + a q.2, q.2))
      (((ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)) +
        (fderiv ℝ a q.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).prod
          (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))) q :=
    ((hasFDerivAt_fst.sub_const _).add (ha.hasFDerivAt.comp q hasFDerivAt_snd)).prodMk
      hasFDerivAt_snd
  rw [h.fderiv]
  simp only [ContinuousLinearMap.prod_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

variable (hσ : σ.IsSymplectic) (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j, ∀ᶠ y in 𝓝 x, σ.poissonBracket (F · i) (F · j) y = 0)

include hσ in
/-- At a regular point `x` of `n` functions Poisson-commuting at `x` on a `2n`-dimensional
symplectic manifold, the map `y ↦ (T (g y), F y)` has injective differential as soon as `T ∘ dg_x`
sends each Hamiltonian vector `X_{Fᵢ}(x)` to `eᵢ`: `ker dF_x` is spanned by these vectors. -/
private theorem injective_mvfderiv_prodMk [DecidableEq ι]
    (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hcommx : ∀ i j, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {g : M → E} {T : E →L[ℝ] ι → ℝ}
    (hg : MDifferentiableAt I 𝓘(ℝ, E) g x)
    (hT : ∀ i, T (mfderiv I 𝓘(ℝ, E) g x (σ.hamiltonianVectorField (F · i) x)) = Pi.single i 1) :
    Injective (mvfderiv I (fun z ↦ ((T ∘ g) z, F z)) x) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [(T.mdifferentiableAt.comp x hg).mvfderiv_prodMk_apply hreg.mdifferentiableAt,
    T.mvfderiv_comp_apply hg, mvfderiv_apply_eq_mfderiv_apply, Prod.mk_eq_zero] at hv
  have hker : v ∈ (mfderiv I 𝓘(ℝ, ι → ℝ) F x).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← mvfderiv_apply_eq_mfderiv_apply]
    exact hv.2
  rw [hσ.isNondegenerate.ker_mfderiv_eq_span_hamiltonianVectorField hreg hcommx hdim,
    Submodule.mem_span_range_iff_exists_fun] at hker
  obtain ⟨c, rfl⟩ := hker
  -- Read `T ∘ dg_x` as one linear map on `T_x M`, where the sum lives.
  have h : (T.comp (mfderiv I 𝓘(ℝ, E) g x)) (∑ i, c i • σ.hamiltonianVectorField (F · i) x) = 0 :=
    hv.1
  have hT' (i : ι) : (T.comp (mfderiv I 𝓘(ℝ, E) g x)) (σ.hamiltonianVectorField (F · i) x) =
      Pi.single i 1 := hT i
  simp only [map_sum, map_smul, hT'] at h
  have hc : c = 0 := by
    funext j
    simpa [Finset.sum_apply, Pi.single_apply] using congrFun h j
  simp [hc]

include hσ hF hcomm in
/-- **A flow box for commuting Hamiltonians.** Let `σ` be symplectic on a manifold of dimension
`2n` and let `F : M → (ι → ℝ)`, with `n` components, be smooth, with components Poisson-commuting
near an interior point `x` and with independent differentials at `x`. Then there is a smooth
partial diffeomorphism `Φ` from `M` to `(ι → ℝ) × (ι → ℝ)` defined near `x`, with second component
`F`, sending each Hamiltonian vector field `X_{Fᵢ}` to the constant vector field `(eᵢ, 0)`. -/
theorem exists_partialDiffeomorph_mvfderiv_hamiltonianVectorField_eq_of_isInteriorPoint
    [DecidableEq ι] (hx : I.IsInteriorPoint x) (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) M ((ι → ℝ) × (ι → ℝ)) ∞,
      x ∈ Φ.source ∧ ∀ y ∈ Φ.source, (Φ y).2 = F y ∧
        ∀ i, mvfderiv I Φ y (σ.hamiltonianVectorField (F · i) y) = (Pi.single i 1, 0) := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  -- Straighten the commuting, independent Hamiltonian vector fields to constants `uᵢ`.
  obtain ⟨e, u, he, hxe, hu, heu⟩ :=
    exists_chart_mfderiv_eq_const_of_eventually_mlieBracket_eq_zero (m := ⊤) (n := ∞) le_top
      (by simp) hx (V := fun i ↦ σ.hamiltonianVectorField (F · i)) (U := univ)
      (fun i ↦ (hσ.isNondegenerate.contMDiff_hamiltonianVectorField le_rfl
        (by simpa using contMDiff_pi_module_iff.1 hF i)).contMDiffOn) univ_mem
      (hσ.isNondegenerate.linearIndependent_hamiltonianVectorField hreg)
      fun i j _ ↦ (eventually_eventually_nhds.2 (hcomm i j)).mono fun _ ↦
        hσ.isNondegenerate.mlieBracket_hamiltonianVectorField_eq_zero hσ.isClosed
          (by simpa using (contMDiff_pi_module_iff.1 hF i).of_le (by simp))
          (by simpa using (contMDiff_pi_module_iff.1 hF j).of_le (by simp))
  -- A linear form `T` with `T uᵢ = eᵢ`.
  obtain ⟨T, hT⟩ : ∃ T : E →L[ℝ] ι → ℝ, ∀ i, T (u i) = Pi.single i 1 := by
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lcoeFun : (ι →₀ ℝ) →ₗ[ℝ] ι → ℝ) ∘ₗ hu.repr)
    refine ⟨LinearMap.toContinuousLinearMap g, fun i ↦ ?_⟩
    have h := congrArg (fun f ↦ f ⟨u i, Submodule.subset_span (mem_range_self i)⟩) hg
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, comp_apply] at h
    rw [LinearMap.coe_toContinuousLinearMap', h, hu.repr_eq_single i _ rfl]
    simp [Finsupp.single_eq_pi_single]
  -- By the inverse function theorem, `y ↦ (T(I(e y)), F y)` is a local diffeomorphism at `x`.
  have hes : ContMDiffOn I 𝓘(ℝ, E) ∞ (I ∘ e) e.source := by
    simpa only [OpenPartialHomeomorph.extend_coe] using e.contMDiffOn_extend he
  have hed {y : M} (hy : y ∈ e.source) : MDifferentiableAt I 𝓘(ℝ, E) (I ∘ e) y :=
    (hes.contMDiffAt (e.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  have hFd (y : M) : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F y := hF.mdifferentiableAt (by simp)
  have hloc := isLocalDiffeomorphAt_of_injective_mfderiv
    ((T.contMDiff.comp_contMDiffOn hes).prodMk_space hF.contMDiffOn) e.open_source hxe hx
    (by simp) (injective_mvfderiv_iff.1 (injective_mvfderiv_prodMk hσ hreg
      (fun i j ↦ (hcomm i j).self_of_nhds) hdim (hed hxe) fun i ↦ by rw [heu x hxe, hT]))
    (by simp [finrank_prod, ← hdim, two_mul])
  -- Restrict to an open set inside the straightening chart on which the `Fᵢ` Poisson-commute.
  set U : Set M := e.source ∩ interior {y | ∀ i j, σ.poissonBracket (F · i) (F · j) y = 0}
  have hxU : x ∈ U := ⟨hxe, mem_interior_iff_mem_nhds.2 <|
    eventually_all.2 fun i ↦ eventually_all.2 (hcomm i)⟩
  obtain ⟨Φ, hxΦ, hΦU, hΦκ⟩ := hloc.exists_partialDiffeomorph_eqOn
    (e.open_source.inter isOpen_interior) hxU
  refine ⟨Φ, hxΦ, fun y hy ↦ ⟨(hΦκ hy).symm ▸ rfl, fun i ↦ ?_⟩⟩
  have hyU := hΦU hy
  rw [(eventuallyEq_of_mem (Φ.open_source.mem_nhds hy) fun z hz ↦ (hΦκ hz).symm).mvfderiv_eq,
    (T.mdifferentiableAt.comp y (hed hyU.1)).mvfderiv_prodMk_apply (hFd y),
    T.mvfderiv_comp_apply (hed hyU.1), mvfderiv_apply_eq_mfderiv_apply, heu y hyU.1, hT]
  congr 1
  funext k
  rw [mvfderiv_apply_apply (hFd y), ← hσ.isNondegenerate.poissonBracket_eq_mvfderiv]
  exact interior_subset hyU.2 k i

include hσ in
/-- **Composing a flow box with a shear.** If a partial diffeomorphism `Φ` defined near `x` has
second component `F` and pulls `∑ᵢ d(tᵢ + aᵢ(c)) ∧ dcᵢ` back to `σ` near `x`, with `a` vanishing at
`(Φ x).2`, then the shear `(t, c) ↦ (t - (Φ x).1 + a(c), c)` after `Φ` is a Darboux chart near
`x` with momenta `F`, sending `x` to `(0, F x)`. -/
private theorem exists_darbouxChart_of_shear (hx : I.IsInteriorPoint x)
    (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (Φ : PartialDiffeomorph I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) M ((ι → ℝ) × (ι → ℝ)) ∞)
    (hxΦ : x ∈ Φ.source) (hΦF : ∀ y ∈ Φ.source, (Φ y).2 = F y) {r : ℝ} (hr : 0 < r)
    {a : (ι → ℝ) → ι → ℝ} (ha0 : a (Φ x).2 = 0) (ha : ContDiffOn ℝ ∞ a (Metric.ball (Φ x).2 r))
    (hform : ∀ y ∈ Φ.source, Φ y ∈ Metric.ball (Φ x) r → ∀ v w : TangentSpace I y,
      SmoothBundleForm.eval₂ σ y v w = ∑ i,
        (((mvfderiv I Φ y v).1 i + fderiv ℝ a (Φ y).2 (mvfderiv I Φ y v).2 i) *
          (mvfderiv I Φ y w).2 i - ((mvfderiv I Φ y w).1 i +
            fderiv ℝ a (Φ y).2 (mvfderiv I Φ y w).2 i) * (mvfderiv I Φ y v).2 i)) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) M ((ι → ℝ) × (ι → ℝ)) ∞,
      x ∈ chart.source ∧ chart x = (0, F x) ∧ (∀ y ∈ chart.source, (chart y).2 = F y) ∧
        σ.IsDarbouxChart chart := by
  set χ : (ι → ℝ) × (ι → ℝ) → (ι → ℝ) × (ι → ℝ) := fun q ↦ (q.1 - (Φ x).1 + a q.2, q.2) with hχ
  have hball {q : (ι → ℝ) × (ι → ℝ)} (hq : q ∈ Metric.ball (Φ x) r) :
      q.2 ∈ Metric.ball (Φ x).2 r :=
    (ball_prod_same (Φ x).1 (Φ x).2 r ▸ hq).2
  have hχs : ContDiffOn ℝ ∞ χ (Metric.ball (Φ x) r) :=
    ((contDiff_fst.contDiffOn.sub contDiffOn_const).add
      (ha.comp contDiff_snd.contDiffOn fun _ hq ↦ hball hq)).prodMk contDiff_snd.contDiffOn
  set S : Set M := Φ.source ∩ Φ ⁻¹' Metric.ball (Φ x) r
  have hSo : IsOpen S :=
    Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source Metric.isOpen_ball
  have hxS : x ∈ S := ⟨hxΦ, Metric.mem_ball_self hr⟩
  -- The pullback of the standard form along `χ ∘ Φ` is `σ` on `S`.
  have hform' {y : M} (hy : y ∈ S) (v w : TangentSpace I y) : SmoothBundleForm.eval₂ σ y v w =
      ∑ i, ((mvfderiv I (χ ∘ Φ) y v).1 i * (mvfderiv I (χ ∘ Φ) y w).2 i -
        (mvfderiv I (χ ∘ Φ) y w).1 i * (mvfderiv I (χ ∘ Φ) y v).2 i) := by
    have had := (ha.differentiableOn (by simp) _ (hball hy.2)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hball hy.2))
    have hχd := (hχs.differentiableOn (by simp) _ hy.2).differentiableAt
      (Metric.isOpen_ball.mem_nhds hy.2)
    rw [mvfderiv_comp_apply_of_differentiableAt hχd (Φ.mdifferentiableAt (by simp) hy.1),
      mvfderiv_comp_apply_of_differentiableAt hχd (Φ.mdifferentiableAt (by simp) hy.1),
      fderiv_shear_apply had, fderiv_shear_apply had]
    exact hform y hy.1 hy.2 v w
  -- By the inverse function theorem, `χ ∘ Φ` is a local diffeomorphism at `x`.
  have hinj : Injective (mvfderiv I (χ ∘ Φ) x) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    refine (isNondegenerate_iff_separatingLeft.1 hσ.isNondegenerate) x v fun w ↦ ?_
    rw [hform' hxS, hv]
    simp
  have hloc := isLocalDiffeomorphAt_of_injective_mfderiv
    (hχs.contMDiffOn.comp (Φ.contMDiffOn_toFun.mono inter_subset_left) fun _ hy ↦ hy.2) hSo hxS
    hx (by simp) (injective_mvfderiv_iff.1 hinj) (by simp [finrank_prod, ← hdim, two_mul])
  obtain ⟨chart, hxc, hcS, hcκ⟩ := hloc.exists_partialDiffeomorph_eqOn hSo hxS
  refine ⟨chart, hxc, ?_, fun y hy ↦ ?_, ⟨fun y hy v w ↦ ?_⟩⟩
  · have ha0' : a (F x) = 0 := hΦF x hxΦ ▸ ha0
    rw [← hcκ hxc]
    simp [hχ, ha0', hΦF x hxΦ]
  · rw [← hcκ hy]
    exact hΦF y (hcS hy).1
  · rw [(eventuallyEq_of_mem (chart.open_source.mem_nhds hy) fun z hz ↦ (hcκ hz).symm).mvfderiv_eq]
    exact hform' (hcS hy) v w

include hσ hF hcomm in
/-- **The Carathéodory–Jacobi–Lie theorem for `n` functions, at an interior point.** Let `σ` be a
symplectic form on a manifold of dimension `2n` and let `F : M → (ι → ℝ)`, with `n` components, be
smooth, with components Poisson-commuting near an interior point `x` and with independent
differentials at `x`. Then there are Darboux coordinates near `x` whose momenta are the `Fᵢ`: a
smooth partial diffeomorphism `chart` from `M` to `(ι → ℝ) × (ι → ℝ)` with `chart x = (0, F x)`
and second component `F`, pulling the standard form `∑ᵢ dqᵢ ∧ dpᵢ` back to `σ`. -/
theorem exists_darbouxChart_snd_eq_of_isInteriorPoint (hx : I.IsInteriorPoint x)
    (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (hdim : 2 * Fintype.card ι = finrank ℝ E) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) M ((ι → ℝ) × (ι → ℝ)) ∞,
      x ∈ chart.source ∧ chart x = (0, F x) ∧ (∀ y ∈ chart.source, (chart y).2 = F y) ∧
        σ.IsDarbouxChart chart := by
  classical
  obtain ⟨Φ, hxΦ, hΦ⟩ :=
    exists_partialDiffeomorph_mvfderiv_hamiltonianVectorField_eq_of_isInteriorPoint hσ hF hcomm
      hx hreg hdim
  -- The second component of the differential of `Φ` is `dF`.
  have hsnd {y : M} (hy : y ∈ Φ.source) (v : TangentSpace I y) :
      (mvfderiv I Φ y v).2 = mvfderiv I F y v := by
    have heq : (fun z ↦ (Φ z).2) =ᶠ[𝓝 y] F :=
      eventuallyEq_of_mem (Φ.open_source.mem_nhds hy) fun z hz ↦ (hΦ z hz).1
    rw [← (Φ.mdifferentiableAt (by simp) hy).mvfderiv_snd_apply, heq.mvfderiv_eq]
  -- In the flow box, `σ` is a closed two-form `μ` with `μ(∂_{tᵢ}, ·) = dcᵢ`.
  obtain ⟨μ, hμdef⟩ : ∃ μ : (ι → ℝ) × (ι → ℝ) → ((ι → ℝ) × (ι → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ,
      μ = mpullbackWithin 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Φ.symm Φ.target σ.val := ⟨_, rfl⟩
  have hμs : ContDiffOn ℝ ∞ μ Φ.target := by
    subst hμdef
    exact Φ.contDiffOn_mpullbackWithin_symm σ
  have hμc : ∀ p ∈ Φ.target, extDeriv μ p = 0 := by
    subst hμdef
    exact fun p hp ↦ Φ.extDeriv_mpullbackWithin_symm_eq_zero hσ.isClosed hp
  have hpull {y : M} (hy : y ∈ Φ.source) (v w : TangentSpace I y) :
      μ (Φ y) ![mvfderiv I Φ y v, mvfderiv I Φ y w] = SmoothBundleForm.eval₂ σ y v w := by
    rw [hμdef, SmoothBundleForm.eval₂_apply,
      ← Φ.mpullbackWithin_symm_apply_mvfderiv (by simp) σ.val hy ![v, w]]
    congr 1
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩
  have hμh : ∀ p ∈ Φ.target, ∀ i v, μ p ![(Pi.single i 1, 0), v] = v.2 i := by
    intro p hp i v
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ Φ.source, Φ y = p := ⟨_, Φ.map_target hp, Φ.right_inv hp⟩
    obtain ⟨w, rfl⟩ := (Φ.bijective_mvfderiv (by simp) hy).2 v
    rw [← (hΦ y hy).2 i, hpull hy,
      hσ.isNondegenerate.eval₂_hamiltonianVectorField (F · i) y w, hsnd hy,
      mvfderiv_apply_apply (hF.mdifferentiableAt (by simp))]
  -- There, `σ` is `∑ᵢ d(tᵢ + aᵢ(c)) ∧ dcᵢ`; a shear gives the Darboux chart.
  obtain ⟨r, hr, -, a, ha0, ha, hμa⟩ :=
    exists_apply_eq_sum_of_apply_inl_single_eq_snd Φ.open_target (Φ.map_source hxΦ) hμs hμc hμh
  exact exists_darbouxChart_of_shear hσ hx hdim Φ hxΦ (fun y hy ↦ (hΦ y hy).1) hr ha0 ha
    fun y hy hyr v w ↦ by rw [← hpull hy, hμa _ hyr]

include hσ hF hcomm in
/-- **The Carathéodory–Jacobi–Lie theorem for `n` functions.** On a boundaryless symplectic
manifold of dimension `2n`, let `F : M → (ι → ℝ)`, with `n` components, be smooth, with components
Poisson-commuting near `x` and with independent differentials at `x`. Then there are Darboux
coordinates near `x` whose momenta are the `Fᵢ`: a smooth partial diffeomorphism `chart` from `M`
to `(ι → ℝ) × (ι → ℝ)` with `chart x = (0, F x)` and second component `F`, pulling the standard form
`∑ᵢ dqᵢ ∧ dpᵢ` back to `σ`. -/
theorem exists_darbouxChart_snd_eq [BoundarylessManifold I M]
    (hreg : IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (hdim : 2 * Fintype.card ι = finrank ℝ E) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) M ((ι → ℝ) × (ι → ℝ)) ∞,
      x ∈ chart.source ∧ chart x = (0, F x) ∧ (∀ y ∈ chart.source, (chart y).2 = F y) ∧
        σ.IsDarbouxChart chart :=
  exists_darbouxChart_snd_eq_of_isInteriorPoint hσ hF hcomm BoundarylessManifold.isInteriorPoint
    hreg hdim

end IsSymplectic

end SmoothTwoForm

end TauCeti
