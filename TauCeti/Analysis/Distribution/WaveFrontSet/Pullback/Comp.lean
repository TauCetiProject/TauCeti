/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.SmoothMap
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Topology.Algebra.Monoid
import TauCeti.Topology.Separation.Regular

/-!
# Pulling distributions back along a smooth map followed by a submersion

Let `f` be smooth from an open set `Ω` of a finite-dimensional real inner product space into an
open set `Ω'`, and let `k` be a submersion from `Ω'` into `Ω''`. A distribution `S` on `Ω''` whose
wave front set does not meet the normal set of `g = k ∘ f` has a pullback `g^* S`
(`Distribution.pullback`); its pullback `k^* S` along the submersion `k` is defined for every `S`
(`Distribution.compCLMOfSubmersion`), and its wave front set does not meet the normal set of `f`
(`Distribution.adjoint_fderiv_apply_ne_zero_compCLMOfSubmersion`). This file proves

`g^* S = f^* (k^* S)`

(`Distribution.pullback_eq_pullback_compCLMOfSubmersion`, Hörmander I, Theorem 8.2.4). Taking for
`k` a change of variables, the pullback does not depend on the coordinates in the target. The
composition with a submersion in the source, `(f ∘ k)^* T = k^* (f^* T)`, is
`Distribution.pullback_comp_of_surjective`; together they allow pullbacks to be computed chart by
chart on manifolds.

The pullback `f^* T` is defined as the restriction `Distribution.pullbackInl` to `E × {0}` of the
pullback of `T` along the submersion `(x, y) ↦ f x + y`. So the theorem reduces to the composition
rule for a submersion `F` from an open set of `E × D` and the inclusion `ι x = (x, 0)`, which is
not a submersion:

`ι^* (F^* S) = (F ∘ ι)^* S`

(`Distribution.pullbackInl_compCLMOfSubmersion`), applied to `F (x, y) = k (f x + y)`.

## The argument

Both sides of `ι^* (F^* S) = (F ∘ ι)^* S` are limits of pairings with tensor products of a test
function `ψ` and shrinking normalized bumps: `ψ ⊗ ρ_n` with bumps `ρ_n` on `D` on the left, and
`ψ ⊗ σ_k` with bumps `σ_k` on `E'` on the right (`Distribution.tendsto_pullbackInl`). They are
compared through the submersion `K (x, (y, z)) = F (x, y) + z` on `E × (D × E')` and the double
sequence `a n k = K^* S (ψ ⊗ ρ_n ⊗ σ_k)`:

* `a n k` converges jointly in `n` and `k` to the restriction of `K^* S` to `E × {0}`, because the
  products `ρ_n ⊗ σ_k` are again shrinking normalized bumps on `D × E'`;
* for fixed `n`, the fibre integral of `ψ ⊗ ρ_n ⊗ σ_k` along `K` is the mollification by `σ_k` of
  the fibre integral of `ψ ⊗ ρ_n` along `F`, so `a n k` tends to `F^* S (ψ ⊗ ρ_n)` as `k → ∞`;
* for fixed `k`, both `a n k` and the pairing of `ψ ⊗ σ_k` with the pullback of `S` along
  `(x, z) ↦ F (x, 0) + z` are integrals of the smooth regularization `w ↦ S (σ_k (· - w))` of `S`,
  against `ψ ⊗ ρ_n` along `F` and against `ψ` along `F ∘ ι`
  (`Distribution.apply_eq_integral_smul_translatePairing_comp`,
  `TestFunction.fiberIntegralCLM_apply_eq_integral`), so `a n k` tends to the latter as `n → ∞`.

In a regular space the limits of the rows and of the columns of a jointly convergent double
sequence are the joint limit (`Filter.Tendsto.tendsto_of_forall_tendsto`), which gives the
equality.

## Main results

* `Distribution.pullback_eq_pullback_compCLMOfSubmersion`: `(k ∘ f)^* S = f^* (k^* S)` for a
  submersion `k`.
* `Distribution.adjoint_fderiv_apply_ne_zero_compCLMOfSubmersion`: the hypothesis of the pullback
  along `f` for `k^* S`.
* `Distribution.pullbackInl_compCLMOfSubmersion`: `ι^* (F^* S) = (F ∘ ι)^* S` for a submersion `F`
  on an open set of `E × D`.
* `Distribution.notMem_waveFrontSet_compCLMOfSubmersion_inl`: the hypothesis of the restriction
  to `E × {0}` for `F^* S`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4.
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, arXiv:1409.7662v2, Proposition 5.1.
-/

public section

noncomputable section

open Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory WithLp TauCeti
open scoped Distributions ContDiff Topology Pointwise

namespace Distribution

/-! ### The submersion `(x, (y, z)) ↦ F (x, y) + z` -/

section Triple

variable {E D E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {W : Opens (WithLp 2 (E × D))} {Ω' : Opens E'} {F : WithLp 2 (E × D) → E'}

/-- The projection `(x, (y, z)) ↦ (x, y)`. -/
private def tripleFst : WithLp 2 (E × WithLp 2 (D × E')) →L[ℝ] WithLp 2 (E × D) :=
  (prodContinuousLinearEquiv 2 ℝ E D).symm.toContinuousLinearMap ∘L
    ((fstL 2 ℝ E (WithLp 2 (D × E'))).prod (fstL 2 ℝ D E' ∘L sndL 2 ℝ E (WithLp 2 (D × E'))))

/-- The values of the projection `(x, (y, z)) ↦ (x, y)`. -/
@[simp]
private theorem tripleFst_apply (q : WithLp 2 (E × WithLp 2 (D × E'))) :
    tripleFst q = toLp 2 (q.fst, q.snd.fst) :=
  (rfl)

/-- The map `(x, (y, z)) ↦ F (x, y) + z`, a submersion because of the last variable. -/
private def tripleAdd (F : WithLp 2 (E × D) → E') (q : WithLp 2 (E × WithLp 2 (D × E'))) : E' :=
  F (toLp 2 (q.fst, q.snd.fst)) + q.snd.snd

/-- `(x, (y, z)) ↦ F (x, y) + z` as `F` after a projection plus a projection. -/
private theorem tripleAdd_eq (F : WithLp 2 (E × D) → E') :
    tripleAdd F = F ∘ tripleFst + ⇑(sndL 2 ℝ D E' ∘L sndL 2 ℝ E (WithLp 2 (D × E'))) :=
  rfl

/-- The open set `{(x, (y, z)) | (x, y) ∈ W, F (x, y) + z ∈ Ω'}`. -/
private def tripleDomain (hF : ContinuousOn F W) (Ω' : Opens E') :
    Opens (WithLp 2 (E × WithLp 2 (D × E'))) :=
  ⟨tripleFst ⁻¹' W ∩ tripleAdd F ⁻¹' Ω', by
    refine ContinuousOn.isOpen_inter_preimage ?_ (W.isOpen.preimage tripleFst.continuous)
      Ω'.isOpen
    rw [tripleAdd_eq]
    exact (hF.comp tripleFst.continuous.continuousOn (mapsTo_preimage _ _)).add
      (ContinuousLinearMap.continuous _).continuousOn⟩

/-- Membership in `{(x, (y, z)) | (x, y) ∈ W, F (x, y) + z ∈ Ω'}`. -/
private theorem mem_tripleDomain {hF : ContinuousOn F W} {q : WithLp 2 (E × WithLp 2 (D × E'))} :
    q ∈ tripleDomain hF Ω' ↔
      toLp 2 (q.fst, q.snd.fst) ∈ W ∧ F (toLp 2 (q.fst, q.snd.fst)) + q.snd.snd ∈ Ω' :=
  Iff.rfl

/-- The map `(x, (y, z)) ↦ F (x, y) + z` is smooth on its domain. -/
private theorem contDiffOn_tripleAdd (hF : ContDiffOn ℝ ∞ F W) :
    ContDiffOn ℝ ∞ (tripleAdd F) (tripleDomain hF.continuousOn Ω') := by
  rw [tripleAdd_eq]
  exact ((hF.comp (tripleFst (E := E) (D := D) (E' := E')).contDiff.contDiffOn
    (mapsTo_preimage _ _)).add
    (ContinuousLinearMap.contDiff _).contDiffOn).mono inter_subset_left

/-- The map `(x, (y, z)) ↦ F (x, y) + z` maps its domain into `Ω'`. -/
private theorem mapsTo_tripleAdd (hF : ContinuousOn F W) :
    MapsTo (tripleAdd F) (tripleDomain hF Ω') Ω' := fun _ hq ↦ hq.2

/-- The map `(x, (y, z)) ↦ F (x, y) + z` is a submersion, already in the variable `z`. -/
private theorem surjective_fderiv_tripleAdd (hF : ContDiffOn ℝ ∞ F W) :
    ∀ q ∈ tripleDomain hF.continuousOn Ω', Surjective (fderiv ℝ (tripleAdd F) q) := by
  intro q hq z
  set π := tripleFst (E := E) (D := D) (E' := E')
  have hFq : DifferentiableAt ℝ F (π q) :=
    (hF.differentiableOn (by simp) _ hq.1).differentiableAt (W.isOpen.mem_nhds hq.1)
  -- `D K (q) = DF (x, y) ∘ (x, (y, z)) ↦ (x, y) + (x, (y, z)) ↦ z`.
  have hK : HasFDerivAt (tripleAdd F) ((fderiv ℝ F (π q)).comp π +
      (sndL 2 ℝ D E' ∘L sndL 2 ℝ E (WithLp 2 (D × E')))) q := by
    rw [tripleAdd_eq]
    exact (hFq.hasFDerivAt.comp q π.hasFDerivAt).add (ContinuousLinearMap.hasFDerivAt _)
  refine ⟨toLp 2 (0, toLp 2 (0, z)), ?_⟩
  have hπ : π (toLp 2 (0, toLp 2 (0, z))) = 0 := by simp [π]
  rw [hK.fderiv]
  simp [hπ]

end Triple

section TripleMeasure

variable {E D E' : Type*} [MeasurableSpace E] [MeasurableSpace D] [MeasurableSpace E']

/-- The identification of `E × (D × E')` with `(E × D) × E'`. -/
private def tripleEquiv : WithLp 2 (E × WithLp 2 (D × E')) ≃ᵐ WithLp 2 (E × D) × E' :=
  (((MeasurableEquiv.toLp 2 (E × WithLp 2 (D × E'))).symm.trans
    ((MeasurableEquiv.refl E).prodCongr (MeasurableEquiv.toLp 2 (D × E')).symm)).trans
    MeasurableEquiv.prodAssoc.symm).trans
    ((MeasurableEquiv.toLp 2 (E × D)).prodCongr (MeasurableEquiv.refl E'))

/-- The values of the identification of `E × (D × E')` with `(E × D) × E'`. -/
@[simp]
private theorem tripleEquiv_apply (q : WithLp 2 (E × WithLp 2 (D × E'))) :
    tripleEquiv q = (toLp 2 (q.fst, q.snd.fst), q.snd.snd) :=
  (rfl)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [BorelSpace D]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [BorelSpace E']

/-- The identification of `E × (D × E')` with `(E × D) × E'` preserves volume. -/
private theorem measurePreserving_tripleEquiv :
    MeasurePreserving (tripleEquiv (E := E) (D := D) (E' := E')) volume (volume.prod volume) := by
  have h₁ := volume_preserving_symm_measurableEquiv_toLp_prod E (WithLp 2 (D × E'))
  have h₂ := (MeasurePreserving.id (volume : Measure E)).prod
    (volume_preserving_symm_measurableEquiv_toLp_prod D E')
  have h₃ := (measurePreserving_prodAssoc (volume : Measure E) (volume : Measure D)
    (volume : Measure E')).symm
  have h₄ := (volume_preserving_symm_measurableEquiv_toLp_prod E D).symm.prod
    (MeasurePreserving.id (volume : Measure E'))
  exact h₄.comp (h₃.comp (h₂.comp h₁))

end TripleMeasure

/-! ### Restricting a pullback along a submersion -/

section Restriction

variable {E D E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup D]
  [InnerProductSpace ℝ D] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  {U : Opens E} {Ω' : Opens E'}

variable [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']

/-- The normalized bump of `σ` as a test function on the whole space. -/
private def normedBumpTest (σ : ContDiffBump (0 : E')) : 𝓓((⊤ : Opens E'), ℝ) where
  toFun := σ.normed volume
  contDiff' := σ.contDiff_normed
  hasCompactSupport' := σ.hasCompactSupport_normed
  tsupport_subset' := subset_univ _

omit [MeasurableSpace D] [BorelSpace D] [MeasurableSpace E'] [BorelSpace E'] in
/-- The compact set `{(x, (y, z)) | x ∈ supp ψ, ‖y‖ ≤ r, ‖z‖ ≤ s}`. -/
private theorem isCompact_tripleSet (ψ : 𝓓(U, ℝ)) (r s : ℝ) :
    IsCompact ((fun t : E × D × E' ↦ toLp 2 (t.1, toLp 2 t.2)) ''
      (tsupport ψ ×ˢ (closedBall (0 : D) r ×ˢ closedBall (0 : E') s))) :=
  (ψ.hasCompactSupport.isCompact.prod ((isCompact_closedBall _ _).prod
    (isCompact_closedBall _ _))).image ((prod_continuous_toLp 2 E _).comp
      (continuous_fst.prodMk ((prod_continuous_toLp 2 D E').comp continuous_snd)))

/-- The product `ψ x ρ y σ z` vanishes off `supp ψ × closedBall 0 (rOut ρ) × closedBall 0 (rOut σ)`.
-/
private theorem mul_mul_normed_eq_zero_of_notMem (ψ : 𝓓(U, ℝ)) (ρ : ContDiffBump (0 : D))
    (σ : ContDiffBump (0 : E')) {q : WithLp 2 (E × WithLp 2 (D × E'))}
    (hq : q ∉ (fun t : E × D × E' ↦ toLp 2 (t.1, toLp 2 t.2)) ''
      (tsupport ψ ×ˢ (closedBall (0 : D) ρ.rOut ×ˢ closedBall (0 : E') σ.rOut))) :
    ψ q.fst * (ρ.normed volume q.snd.fst * σ.normed volume q.snd.snd) = 0 := by
  by_contra h0
  simp only [mul_ne_zero_iff] at h0
  obtain ⟨h₁, h₂, h₃⟩ := h0
  refine hq ⟨(q.fst, q.snd.fst, q.snd.snd), ⟨subset_tsupport _ h₁, ?_, ?_⟩, rfl⟩
  · exact ball_subset_closedBall (by rw [← ρ.support_normed_eq (μ := volume)]; exact h₂)
  · exact ball_subset_closedBall (by rw [← σ.support_normed_eq (μ := volume)]; exact h₃)

/-- The test function `(x, (y, z)) ↦ ψ x ρ y σ z` for the normalized bumps `ρ`, `σ` of two bump
functions. -/
private def tripleBump (ψ : 𝓓(U, ℝ)) (ρ : ContDiffBump (0 : D)) (σ : ContDiffBump (0 : E'))
    {Wq : Opens (WithLp 2 (E × WithLp 2 (D × E')))}
    (hW : ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : D) ρ.rOut, ∀ z ∈ closedBall (0 : E') σ.rOut,
      toLp 2 (x, toLp 2 (y, z)) ∈ Wq) : 𝓓(Wq, ℝ) where
  toFun q := ψ q.fst * (ρ.normed volume q.snd.fst * σ.normed volume q.snd.snd)
  contDiff' := (ψ.contDiff.comp (fstL 2 ℝ E _).contDiff).mul
    ((ρ.contDiff_normed.comp ((fstL 2 ℝ D E').contDiff.comp (sndL 2 ℝ E _).contDiff)).mul
      (σ.contDiff_normed.comp ((sndL 2 ℝ D E').contDiff.comp (sndL 2 ℝ E _).contDiff)))
  hasCompactSupport' := HasCompactSupport.intro (isCompact_tripleSet ψ ρ.rOut σ.rOut)
    fun _ hq ↦ mul_mul_normed_eq_zero_of_notMem ψ ρ σ hq
  tsupport_subset' := (closure_minimal (support_subset_iff'.2 fun _ hq ↦
    mul_mul_normed_eq_zero_of_notMem ψ ρ σ hq)
      (isCompact_tripleSet ψ ρ.rOut σ.rOut).isClosed).trans <| by
    rintro _ ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩
    exact hW x hx y hy z hz

/-- The values `ψ x ρ y σ z` of the test function `ψ ⊗ ρ ⊗ σ`. -/
private theorem tripleBump_apply (ψ : 𝓓(U, ℝ)) (ρ : ContDiffBump (0 : D))
    (σ : ContDiffBump (0 : E')) {Wq : Opens (WithLp 2 (E × WithLp 2 (D × E')))}
    (hW : ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : D) ρ.rOut, ∀ z ∈ closedBall (0 : E') σ.rOut,
      toLp 2 (x, toLp 2 (y, z)) ∈ Wq) (q : WithLp 2 (E × WithLp 2 (D × E'))) :
    tripleBump ψ ρ σ hW q = ψ q.fst * (ρ.normed volume q.snd.fst * σ.normed volume q.snd.snd) :=
  (rfl)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The pullback along a submersion restricts to `E × {0}`.** Let `K` be a submersion from an
open set `W` of `E × D` into `Ω'` with `U × {0} ⊆ W`, and let `g x = K (x, 0)` on `U`. If no
covector of the wave front set of `S` lies in the normal set of `g`, then no covector of the wave
front set of the pullback `K^* S` over `U × {0}` is conormal to `E × {0}`, so that `K^* S`
restricts to `E × {0}` (`Distribution.pullbackInl`). -/
theorem notMem_waveFrontSet_compCLMOfSubmersion_inl {W : Opens (WithLp 2 (E × D))}
    {K : WithLp 2 (E × D) → E'} (hK : ContDiffOn ℝ ∞ K W) (hKW : MapsTo K W Ω')
    (hsurj : ∀ p ∈ W, Surjective (fderiv ℝ K p))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) {g : E → E'}
    (hgK : EqOn g (fun x ↦ K (toLp 2 (x, 0))) U) {S : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ U, ∀ η, (g x, η) ∈ S.waveFrontSet → (fderiv ℝ g x).adjoint η ≠ 0) :
    ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉
      (compCLMOfSubmersion volume volume K hK hKW hsurj S).waveFrontSet := by
  intro x hx η _ hmem
  rw [waveFrontSet_compCLMOfSubmersion] at hmem
  obtain ⟨-, ζ, hζ, hadj⟩ := hmem
  refine h x hx ζ (by simpa [hgK hx] using hζ) ?_
  -- `g = K ∘ ι` near `x` for the inclusion `ι = inlL2`, whose transpose is the first projection.
  have hKι : (fun x ↦ K (toLp 2 (x, (0 : D)))) = K ∘ inlL2 ℝ E D := by
    ext
    simp
  have hKx : DifferentiableAt ℝ K (inlL2 ℝ E D x) := by
    simpa using (hK.differentiableOn (by simp) _ (hU hx)).differentiableAt
      (W.isOpen.mem_nhds (hU hx))
  simp only at hadj
  rw [(eventuallyEq_of_mem (U.isOpen.mem_nhds hx) hgK).fderiv_eq, hKι,
    fderiv_comp x hKx (inlL2 ℝ E D).differentiableAt, (inlL2 ℝ E D).fderiv,
    ContinuousLinearMap.adjoint_comp, adjoint_inlL2, ContinuousLinearMap.comp_apply, inlL2_apply,
    hadj]
  rfl

/-- **Restricting a pullback along a submersion** (Hörmander I, Theorem 8.2.4). Let `F` be a
submersion from an open set `W` of `E × D` into `Ω'`, with `U × {0} ⊆ W`, and let the wave front
set of `S` not meet the normal set of `g = (x ↦ F (x, 0))` over `U`. Then restricting the pullback
`F^* S` to `E × {0}` gives the pullback of `S` along `g`:

`ι^* (F^* S) = g^* S`, where `ι x = (x, 0)`.

This is the composition rule `(F ∘ ι)^* = ι^* ∘ F^*` for the inclusion `ι`, which is not a
submersion.

Both sides are limits over shrinking normalized bumps `ρ_n` on `D` and `σ_k` on `E'`. The submersion
`K (x, (y, z)) = F (x, y) + z` relates them: the numbers `K^* S (ψ ⊗ ρ_n ⊗ σ_k)` converge jointly in
`n` and `k` to the restriction of `K^* S` to `E × {0}`, because `ρ_n ⊗ σ_k` are again shrinking
normalized bumps (`Distribution.tendsto_pullbackInl`). For fixed `n`, they tend as `k → ∞` to
`F^* S (ψ ⊗ ρ_n)`, since the fibre integrals along `K` are mollifications of those along `F`. For
fixed `k`, they are integrals of the smooth regularization `S_k (w) = S (σ_k (· - w))` against
`ψ ⊗ ρ_n` along `F`, which tend as `n → ∞` to its integral against `ψ` along `g`, the value of the
pullback of `S` along `(x, z) ↦ g x + z` at `ψ ⊗ σ_k`. -/
theorem pullbackInl_compCLMOfSubmersion {W : Opens (WithLp 2 (E × D))}
    {F : WithLp 2 (E × D) → E'} (hF : ContDiffOn ℝ ∞ F W) (hFW : MapsTo F W Ω')
    (hsurj : ∀ p ∈ W, Surjective (fderiv ℝ F p))
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W) {g : E → E'}
    (hg : ContDiffOn ℝ ∞ g U) (hgU : MapsTo g U Ω') (hgF : EqOn g (fun x ↦ F (toLp 2 (x, 0))) U)
    {S : 𝓓'(Ω', ℂ)}
    (h : ∀ x ∈ U, ∀ η, (g x, η) ∈ S.waveFrontSet → (fderiv ℝ g x).adjoint η ≠ 0) :
    (compCLMOfSubmersion volume volume F hF hFW hsurj S).pullbackInl hU
        (notMem_waveFrontSet_compCLMOfSubmersion_inl hF hFW hsurj hU hgF h) =
      S.pullback g hg hgU h := by
  ext ψ
  -- The submersion `K (x, (y, z)) = F (x, y) + z` and the pullback `K^* S`.
  have hK := contDiffOn_tripleAdd (Ω' := Ω') hF
  have hKΩ := mapsTo_tripleAdd (Ω' := Ω') hF.continuousOn
  have hKsurj := surjective_fderiv_tripleAdd (Ω' := Ω') hF
  set R := compCLMOfSubmersion volume volume (tripleAdd F) hK hKΩ hKsurj S
  have hUq : MapsTo (fun x ↦ toLp 2 (x, (0 : WithLp 2 (D × E')))) (U : Set E)
      (tripleDomain hF.continuousOn Ω') := fun x hx ↦
    mem_tripleDomain.2 ⟨by simpa using hU hx, by simpa using hFW (hU hx)⟩
  have hgK : EqOn g (fun x ↦ tripleAdd F (toLp 2 (x, (0 : WithLp 2 (D × E'))))) U :=
    fun x hx ↦ by simpa [tripleAdd] using hgF hx
  have hRq := notMem_waveFrontSet_compCLMOfSubmersion_inl hK hKΩ hKsurj hUq hgK h
  -- A tube `supp ψ × {‖y‖ < δ} × {‖z‖ < δ}` inside the domain of `K`.
  obtain ⟨δ, hδ, hδW⟩ := ψ.hasCompactSupport.isCompact.exists_pos_forall_toLp_mem
    (tripleDomain hF.continuousOn Ω').isOpen fun x hx ↦ hUq (ψ.tsupport_subset hx)
  set r := δ / 2 with hr_def
  have hr : 0 < r := half_pos hδ
  have hmem (x : E) (hx : x ∈ tsupport ψ) (y : D) (hy : ‖y‖ < r) (z : E') (hz : ‖z‖ ≤ r / 2) :
      toLp 2 (x, toLp 2 (y, z)) ∈ tripleDomain hF.continuousOn Ω' := by
    refine hδW x hx x _ (by simpa using hδ) ?_
    calc ‖toLp 2 (y, z)‖ ≤ ‖y‖ + ‖z‖ := by
          simpa using WithLp.prod_norm_le_norm_fst_add_norm_snd (toLp 2 (y, z))
      _ < δ := by linarith [hr_def]
  have hmemW (x : E) (hx : x ∈ tsupport ψ) (y : D) (hy : ‖y‖ < r) : toLp 2 (x, y) ∈ W := by
    simpa using (mem_tripleDomain.1 (hmem x hx y hy 0 (by simp only [norm_zero]; positivity))).1
  have hmemΩ (x : E) (hx : x ∈ tsupport ψ) (y : D) (hy : ‖y‖ < r) (z : E') (hz : ‖z‖ ≤ r / 2) :
      F (toLp 2 (x, y)) + z ∈ Ω' := by
    simpa using (mem_tripleDomain.1 (hmem x hx y hy z hz)).2
  -- Shrinking normalized bumps on `D` and on `E'`.
  set ρ : ℕ → ContDiffBump (0 : D) := fun n ↦ ContDiffBump.shrinking (half_pos hr) n
  set σ : ℕ → ContDiffBump (0 : E') := fun k ↦ ContDiffBump.shrinking (half_pos hr) k
  have hρr (n : ℕ) : (ρ n).rOut ≤ r / 2 := ContDiffBump.rOut_shrinking_le _ n
  have hσr (k : ℕ) : (σ k).rOut ≤ r / 2 := ContDiffBump.rOut_shrinking_le _ k
  have hρlt (n : ℕ) {y : D} (hy : y ∈ closedBall (0 : D) (ρ n).rOut) : ‖y‖ < r :=
    ((mem_closedBall_zero_iff.1 hy).trans (hρr n)).trans_lt (half_lt_self hr)
  have hσle (k : ℕ) {z : E'} (hz : z ∈ closedBall (0 : E') (σ k).rOut) : ‖z‖ ≤ r / 2 :=
    (mem_closedBall_zero_iff.1 hz).trans (hσr k)
  -- The test functions `ψ ⊗ ρ_n`, `ψ ⊗ σ_k` and `ψ ⊗ ρ_n ⊗ σ_k`.
  have hW₁ (n : ℕ) : ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : D) (ρ n).rOut, toLp 2 (x, y) ∈ W :=
    fun x hx y hy ↦ hmemW x hx y (hρlt n hy)
  have hW₂ (k : ℕ) : ∀ x ∈ tsupport ψ, ∀ z ∈ closedBall (0 : E') (σ k).rOut,
      toLp 2 (x, z) ∈ addSndDomain hg.continuousOn Ω' := fun x hx z hz ↦
    mem_addSndDomain.2 ⟨ψ.tsupport_subset hx, by
      simpa [hgF (ψ.tsupport_subset hx)] using hmemΩ x hx 0 (by simpa using hr) z (hσle k hz)⟩
  have hW₃ (n k : ℕ) : ∀ x ∈ tsupport ψ, ∀ y ∈ closedBall (0 : D) (ρ n).rOut,
      ∀ z ∈ closedBall (0 : E') (σ k).rOut,
      toLp 2 (x, toLp 2 (y, z)) ∈ tripleDomain hF.continuousOn Ω' := fun x hx y hy z hz ↦
    hmem x hx y (hρlt n hy) z (hσle k hz)
  set Φ : ℕ → 𝓓(W, ℝ) := fun n ↦ tensorBump ψ (ρ n) (hW₁ n)
  set Ψ : ℕ → 𝓓(addSndDomain hg.continuousOn Ω', ℝ) := fun k ↦ tensorBump ψ (σ k) (hW₂ k)
  set Θ : ℕ → ℕ → 𝓓(tripleDomain hF.continuousOn Ω', ℝ) := fun n k ↦
    tripleBump ψ (ρ n) (σ k) (hW₃ n k)
  -- The fibre integrals of `ψ ⊗ ρ_n ⊗ σ_k` along `K` and of `ψ ⊗ σ_k` along `(x, z) ↦ g x + z`.
  have hfibK (n k : ℕ) (w : E') :
      fiberIntegralCLM volume volume (tripleAdd F) hK hKΩ hKsurj (Θ n k) w =
        ∫ p, Φ n p * (σ k).normed volume (w - F p) :=
    fiberIntegralCLM_apply_eq_integral volume volume hK hKΩ hKsurj tripleEquiv
      measurePreserving_tripleEquiv
      (Φ n).continuous (Φ n).hasCompactSupport W.isOpen (Φ n).tsupport_subset hF.continuousOn
      (σ k).continuous_normed (σ k).hasCompactSupport_normed
      (fun v ↦ by simp [Θ, Φ, tripleBump_apply, mul_assoc]) (fun _ _ ↦ by simp [tripleAdd]) w
  have hfibG (k : ℕ) (w : E') :
      fiberIntegralCLM volume volume (addSnd g) (contDiffOn_addSnd hg)
        (mapsTo_addSnd hg.continuousOn)
        (surjective_fderiv_addSnd hg.continuousOn (hg.differentiableOn (by simp))) (Ψ k) w =
        ∫ x, ψ x * (σ k).normed volume (w - g x) :=
    fiberIntegralCLM_apply_eq_integral volume volume (contDiffOn_addSnd hg)
      (mapsTo_addSnd hg.continuousOn)
      (surjective_fderiv_addSnd hg.continuousOn (hg.differentiableOn (by simp)))
      (MeasurableEquiv.toLp 2 (E × E')).symm
      (volume_preserving_symm_measurableEquiv_toLp_prod E E') ψ.continuous ψ.hasCompactSupport
      U.isOpen ψ.tsupport_subset hg.continuousOn (σ k).continuous_normed
      (σ k).hasCompactSupport_normed (fun v ↦ by simp [Ψ]) (fun _ _ ↦ by simp) w
  have hRapp (Θ' : 𝓓(tripleDomain hF.continuousOn Ω', ℝ)) :
      R Θ' = S (fiberIntegralCLM volume volume (tripleAdd F) hK hKΩ hKsurj Θ') :=
    compCLMOfSubmersion_apply volume volume hK hKΩ hKsurj S Θ'
  -- The bumps `ρ_n ⊗ σ_k` on `D × E'` have integral one.
  have hprod (n k : ℕ) :
      ∫ d : WithLp 2 (D × E'), (ρ n).normed volume d.fst * (σ k).normed volume d.snd = 1 := by
    rw [← (volume_preserving_symm_measurableEquiv_toLp_prod D E').symm.integral_comp']
    simp only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp, toLp_fst, toLp_snd]
    rw [Measure.volume_eq_prod, integral_prod_mul, ContDiffBump.integral_normed,
      ContDiffBump.integral_normed, one_mul]
  -- (1) Joint convergence to the restriction of `K^* S` to `E × {0}`.
  have hJ : Tendsto (fun p : ℕ × ℕ ↦ R (Θ p.1 p.2)) (atTop ×ˢ atTop)
      (𝓝 (R.pullbackInl hUq hRq ψ)) := by
    refine tendsto_pullbackInl R hUq hRq ψ (l := atTop ×ˢ atTop)
      (ρ := fun p d ↦ (ρ p.1).normed volume d.fst * (σ p.2).normed volume d.snd)
      (r := fun p ↦ (ρ p.1).rOut + (σ p.2).rOut) (M := 1) (f := fun p ↦ Θ p.1 p.2)
      (Eventually.of_forall fun p ↦ ?_) ?_ (Eventually.of_forall fun p ↦ ?_) ?_
      (Eventually.of_forall fun p q ↦ ?_)
    · exact ((integral_congr_ae (Eventually.of_forall fun d ↦ abs_of_nonneg
        (mul_nonneg ((ρ p.1).nonneg_normed _) ((σ p.2).nonneg_normed _)))).trans
          (hprod p.1 p.2)).le
    · simp_rw [hprod]
      exact tendsto_const_nhds
    · intro d hd
      rw [mem_support, mul_ne_zero_iff] at hd
      have h₁ : d.fst ∈ ball (0 : D) (ρ p.1).rOut := by
        rw [← (ρ p.1).support_normed_eq (μ := volume)]
        exact hd.1
      have h₂ : d.snd ∈ ball (0 : E') (σ p.2).rOut := by
        rw [← (σ p.2).support_normed_eq (μ := volume)]
        exact hd.2
      rw [mem_ball_zero_iff] at h₁ h₂
      exact mem_closedBall_zero_iff.2
        ((WithLp.prod_norm_le_norm_fst_add_norm_snd d).trans (add_le_add h₁.le h₂.le))
    · have h₀ := ((ContDiffBump.tendsto_rOut_shrinking (c := (0 : D)) (half_pos hr)).comp
        tendsto_fst).add ((ContDiffBump.tendsto_rOut_shrinking (c := (0 : E')) (half_pos hr)).comp
          (tendsto_snd (f := (atTop : Filter ℕ))))
      rw [add_zero] at h₀
      exact h₀
    · simp [Θ, tripleBump_apply]
  -- (2) For fixed `n`, the fibre integrals along `K` are mollifications of those along `F`.
  have hmol (n k : ℕ) : closedBall (0 : E') (σ k).rOut +
      tsupport (fiberIntegralCLM volume volume F hF hFW hsurj (Φ n)) ⊆ (Ω' : Set E') := by
    rintro _ ⟨z, hz, t, ht, rfl⟩
    obtain ⟨p, hp, rfl⟩ := tsupport_fiberIntegralCLM_subset volume volume hF hFW hsurj (Φ n) ht
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := tsupport_tensorBump_subset ψ (ρ n) (hW₁ n) hp
    dsimp only
    rw [add_comm]
    exact hmemΩ x hx y (hρlt n hy) z (hσle k hz)
  have hR1 (n : ℕ) : Tendsto (fun k ↦ R (Θ n k)) atTop
      (𝓝 (compCLMOfSubmersion volume volume F hF hFW hsurj S (Φ n))) := by
    rw [compCLMOfSubmersion_apply]
    refine (((map_continuous S).tendsto _).comp (tendsto_mollify _ volume
      (ContDiffBump.tendsto_rOut_shrinking (half_pos hr)) (hmol n))).congr fun k ↦ ?_
    rw [Function.comp_apply, hRapp]
    congr 1
    ext w
    rw [hfibK, mollify_apply, convolution_eq_swap]
    have hint := integral_fiberIntegralCLM_smul volume volume hF hFW hsurj (Φ n)
      (g := fun t ↦ (σ k).normed volume (w - t))
      ((σ k).continuous_normed.comp (continuous_const.sub continuous_id)).continuousOn
    simp only [smul_eq_mul] at hint
    rw [← hint]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
    rfl
  have hR1' : Tendsto (fun n ↦ compCLMOfSubmersion volume volume F hF hFW hsurj S (Φ n)) atTop
      (𝓝 ((compCLMOfSubmersion volume volume F hF hFW hsurj S).pullbackInl hU
        (notMem_waveFrontSet_compCLMOfSubmersion_inl hF hFW hsurj hU hgF h) ψ)) :=
    tendsto_pullbackInl _ hU _ ψ (l := atTop) (ρ := fun n ↦ (ρ n).normed volume)
      (r := fun n ↦ (ρ n).rOut) (M := 1) (f := Φ)
      (Eventually.of_forall fun n ↦ by
        simp_rw [abs_of_nonneg ((ρ n).nonneg_normed _), (ρ n).integral_normed, le_refl])
      (by simp_rw [ContDiffBump.integral_normed, tendsto_const_nhds])
      (Eventually.of_forall fun n ↦ by
        simpa only [(ρ n).support_normed_eq] using ball_subset_closedBall)
      (ContDiffBump.tendsto_rOut_shrinking _) (Eventually.of_forall fun _ ↦ tensorBump_apply _ _ _)
  -- (3) For fixed `k`, both sides are integrals of the regularization `S_k` of `S` by `σ_k`.
  set T : ℕ → E' → ℂ := fun k ↦ S.translatePairing (normedBumpTest (σ k))
  have htsσ (k : ℕ) : tsupport (normedBumpTest (σ k)) = closedBall (0 : E') (σ k).rOut :=
    (σ k).tsupport_normed_eq
  have hadm (k : ℕ) (x : E) (hx : x ∈ tsupport ψ) (y : D) (hy : ‖y‖ < r) :
      MapsTo (· + F (toLp 2 (x, y))) (tsupport (normedBumpTest (σ k))) Ω' := fun z hz ↦ by
    rw [htsσ] at hz
    dsimp only
    rw [add_comm]
    exact hmemΩ x hx y hy z (hσle k hz)
  have hkeyK (n k : ℕ) : R (Θ n k) = ∫ p, Φ n p • T k (F p) := by
    rw [hRapp]
    refine apply_eq_integral_smul_translatePairing_comp S (normedBumpTest (σ k))
      (Φ n).continuous (Φ n).hasCompactSupport (hF.continuousOn.mono (Φ n).tsupport_subset)
      (fun p hp ↦ ?_) (hfibK n k)
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := tsupport_tensorBump_subset ψ (ρ n) (hW₁ n) hp
    exact hadm k x hx y (hρlt n hy)
  have hkeyG (k : ℕ) : addSndPullback hg S (Ψ k) = ∫ x, ψ x • T k (g x) := by
    rw [addSndPullback_apply]
    refine apply_eq_integral_smul_translatePairing_comp S (normedBumpTest (σ k))
      ψ.continuous ψ.hasCompactSupport (hg.continuousOn.mono ψ.tsupport_subset)
      (fun x hx ↦ ?_) (hfibG k)
    simpa [hgF (ψ.tsupport_subset hx)] using hadm k x hx 0 (by simpa using hr)
  have hR2 (k : ℕ) : Tendsto (fun n ↦ R (Θ n k)) atTop (𝓝 (addSndPullback hg S (Ψ k))) := by
    simp_rw [hkeyK, hkeyG]
    -- `S_k ∘ F` is continuous near `supp ψ × {0}`, as `S_k` is smooth where it is defined.
    have hlim := tendsto_integral_tensorBump_smul ψ hr hW₁ (G := fun p ↦ T k (F p))
      fun x hx y hy ↦ ((S.contDiffOn_translatePairing
        (normedBumpTest (σ k))).continuousOn.continuousAt
          ((IsCompact.isOpen_setOf_mapsTo_add (normedBumpTest (σ k)).hasCompactSupport.isCompact
            Ω'.isOpen).mem_nhds (hadm k x hx y hy))).comp
          (hF.continuousOn.continuousAt (W.isOpen.mem_nhds (hmemW x hx y hy)))
    have hH0 : ∫ x, ψ x • T k (F (toLp 2 (x, 0))) = ∫ x, ψ x • T k (g x) := by
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ U
      · simp [hgF hx]
      · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (ψ.tsupport_subset h)]
    rw [hH0] at hlim
    exact hlim
  have hR2' : Tendsto (fun k ↦ addSndPullback hg S (Ψ k)) atTop (𝓝 (S.pullback g hg hgU h ψ)) := by
    rw [pullback_eq_pullbackInl hg hgU h rfl (notMem_waveFrontSet_addSndPullback hg h)]
    exact tendsto_pullbackInl _ (mapsTo_inl_addSndDomain hg.continuousOn hgU) _ ψ (l := atTop)
      (ρ := fun k ↦ (σ k).normed volume) (r := fun k ↦ (σ k).rOut) (M := 1) (f := Ψ)
      (Eventually.of_forall fun k ↦ by
        simp_rw [abs_of_nonneg ((σ k).nonneg_normed _), (σ k).integral_normed, le_refl])
      (by simp_rw [ContDiffBump.integral_normed, tendsto_const_nhds])
      (Eventually.of_forall fun k ↦ by
        simpa only [(σ k).support_normed_eq] using ball_subset_closedBall)
      (ContDiffBump.tendsto_rOut_shrinking _) (Eventually.of_forall fun _ ↦ tensorBump_apply _ _ _)
  -- (4) The two iterated limits agree with the joint limit.
  exact (tendsto_nhds_unique hR1' (hJ.tendsto_of_forall_tendsto hR1)).trans
    (tendsto_nhds_unique hR2' (hJ.tendsto_of_forall_tendsto' hR2)).symm

end Restriction

/-! ### Composition with a submersion in the target -/

section Comp

variable {E E' E'' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] [NormedAddCommGroup E'']
  [InnerProductSpace ℝ E''] [FiniteDimensional ℝ E''] [MeasurableSpace E''] [BorelSpace E'']
  {Ω : Opens E} {Ω' : Opens E'} {Ω'' : Opens E''} {f : E → E'} {k : E' → E''}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Pulling back along a submersion and then along a smooth map.** Let `k` be a submersion from
`Ω'` into `Ω''` and `f` differentiable from `Ω` into `Ω'`. If the wave front set of `S` does not
meet the normal set of `g = k ∘ f`, then the wave front set of the pullback `k^* S` does not meet
the normal set of `f`, so that `f^* (k^* S)` is defined. -/
theorem adjoint_fderiv_apply_ne_zero_compCLMOfSubmersion (hf : DifferentiableOn ℝ f Ω)
    (hfΩ : MapsTo f Ω Ω') (hk : ContDiffOn ℝ ∞ k Ω') (hkΩ : MapsTo k Ω' Ω'')
    (hksurj : ∀ y ∈ Ω', Surjective (fderiv ℝ k y)) {g : E → E''} (hgkf : EqOn g (k ∘ f) Ω)
    {S : 𝓓'(Ω'', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (g x, η) ∈ S.waveFrontSet → (fderiv ℝ g x).adjoint η ≠ 0) :
    ∀ x ∈ Ω, ∀ η, (f x, η) ∈ (compCLMOfSubmersion volume volume k hk hkΩ hksurj S).waveFrontSet →
      (fderiv ℝ f x).adjoint η ≠ 0 := by
  intro x hx η hη
  rw [waveFrontSet_compCLMOfSubmersion] at hη
  obtain ⟨-, ζ, hζ, hζη⟩ := hη
  dsimp only at hζ hζη
  subst hζη
  have hfx : DifferentiableAt ℝ f x := (hf x hx).differentiableAt (Ω.isOpen.mem_nhds hx)
  have hkx : DifferentiableAt ℝ k (f x) := (hk.differentiableOn (by simp) _
    (hfΩ hx)).differentiableAt (Ω'.isOpen.mem_nhds (hfΩ hx))
  have hne := h x hx ζ (by rwa [hgkf hx])
  rwa [(eventuallyEq_of_mem (Ω.isOpen.mem_nhds hx) hgkf).fderiv_eq, fderiv_comp x hkx hfx,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at hne

/-- **Composition of pullbacks with a submersion in the target** (Hörmander I, Theorem 8.2.4). Let
`f` be smooth from `Ω` into `Ω'`, let `k` be a submersion from `Ω'` into `Ω''`, and let `g` be equal
to `k ∘ f` on `Ω`. If the wave front set of `S` does not meet the normal set of `g`, then the
pullback of `S` along `g` is the pullback along `f` of the pullback `k^* S` by integration over the
fibres of `k`:

`g^* S = f^* (k^* S)`.

For a change of variables `k` this is the invariance of the pullback under changes of coordinates
in the target; together with `Distribution.pullback_comp_of_surjective` for changes of coordinates
in the source, it shows that the pullback is defined chart by chart on manifolds.

The pullback `f^* (k^* S)` is by definition the restriction to `E × {0}` of the pullback of `k^* S`
along `(x, y) ↦ f x + y`, which is the pullback of `S` along the submersion
`(x, y) ↦ k (f x + y)`. Restricting it to `E × {0}` gives the pullback of `S` along
`x ↦ k (f x) = g x` (`Distribution.pullbackInl_compCLMOfSubmersion`). -/
theorem pullback_eq_pullback_compCLMOfSubmersion (hf : ContDiffOn ℝ ∞ f Ω)
    (hfΩ : MapsTo f Ω Ω') (hk : ContDiffOn ℝ ∞ k Ω') (hkΩ : MapsTo k Ω' Ω'')
    (hksurj : ∀ y ∈ Ω', Surjective (fderiv ℝ k y)) {g : E → E''} (hg : ContDiffOn ℝ ∞ g Ω)
    (hgΩ : MapsTo g Ω Ω'') (hgkf : EqOn g (k ∘ f) Ω) {S : 𝓓'(Ω'', ℂ)}
    (h : ∀ x ∈ Ω, ∀ η, (g x, η) ∈ S.waveFrontSet → (fderiv ℝ g x).adjoint η ≠ 0) :
    S.pullback g hg hgΩ h =
      (compCLMOfSubmersion volume volume k hk hkΩ hksurj S).pullback f hf hfΩ
        (adjoint_fderiv_apply_ne_zero_compCLMOfSubmersion (hf.differentiableOn (by simp)) hfΩ hk
          hkΩ hksurj hgkf h) := by
  -- The submersion `F (x, y) = k (f x + y)` on `{(x, y) | x ∈ Ω, f x + y ∈ Ω'}`.
  have hF : ContDiffOn ℝ ∞ (k ∘ addSnd f) (addSndDomain hf.continuousOn Ω') :=
    hk.comp (contDiffOn_addSnd hf) (mapsTo_addSnd hf.continuousOn)
  have hFW : MapsTo (k ∘ addSnd f) (addSndDomain hf.continuousOn Ω') Ω'' :=
    hkΩ.comp (mapsTo_addSnd hf.continuousOn)
  have hsurj₁ := surjective_fderiv_addSnd (Ω' := Ω') hf.continuousOn (hf.differentiableOn (by simp))
  have hFsurj : ∀ p ∈ addSndDomain hf.continuousOn Ω', Surjective (fderiv ℝ (k ∘ addSnd f) p) := by
    intro p hp
    have hp' := mapsTo_addSnd hf.continuousOn hp
    rw [fderiv_comp p ((hk.differentiableOn (by simp) _ hp').differentiableAt
        (Ω'.isOpen.mem_nhds hp'))
      (((contDiffOn_addSnd hf).differentiableOn (by simp) p hp).differentiableAt
        ((addSndDomain hf.continuousOn Ω').isOpen.mem_nhds hp)),
      ContinuousLinearMap.coe_comp]
    exact (hksurj _ hp').comp (hsurj₁ p hp)
  have hU := mapsTo_inl_addSndDomain hf.continuousOn hfΩ (Ω' := Ω')
  have hgF : EqOn g (fun x ↦ (k ∘ addSnd f) (toLp 2 (x, (0 : E')))) Ω := fun x hx ↦ by
    simp [hgkf hx]
  -- `(x, y) ↦ f x + y` pulls `k^* S` back to `F^* S`.
  have hTS : addSndPullback hf (compCLMOfSubmersion volume volume k hk hkΩ hksurj S) =
      compCLMOfSubmersion volume volume (k ∘ addSnd f) hF hFW hFsurj S := by
    rw [addSndPullback_eq_compCLMOfSubmersion]
    exact (compCLMOfSubmersion_comp volume volume (contDiffOn_addSnd hf)
      (mapsTo_addSnd hf.continuousOn) hsurj₁ volume hk hkΩ hksurj S).symm
  rw [pullback_eq_pullbackInl hf hfΩ _ hTS
    (notMem_waveFrontSet_compCLMOfSubmersion_inl hF hFW hFsurj hU hgF h)]
  exact (pullbackInl_compCLMOfSubmersion hF hFW hFsurj hU hg hgΩ hgF h).symm

end Comp

end Distribution
