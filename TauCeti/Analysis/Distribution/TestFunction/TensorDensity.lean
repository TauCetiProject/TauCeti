/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Prod
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Distribution.TestFunction.Convergence
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Fourier.Torus.Smooth
import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# Density of tensor products of test functions

Let `Ω ⊆ E` and `O ⊆ D` be open subsets of finite-dimensional real normed spaces. The tensor
products `(x, t) ↦ ψ t • φ x` of real test functions `φ` on `Ω` and `ψ` on `O`
(`TestFunction.prodSMulCLM`) span a dense subspace of the real test functions on `Ω × O`, for the
LF topology. Consequently a continuous linear map on the test functions on `Ω × O`, in particular
a distribution on `Ω × O`, is determined by its values on these tensor products. This is the
uniqueness half of the Schwartz kernel theorem: a distributional kernel `K` on `Ω × O` is
determined by the pairings `K (ψ ⊗ φ)`.

## The Fourier argument

Fix a test function `f` on `Ω × O`. Its support lies in the product of two compact sets, and
cutoffs `χ₁` on `Ω` and `χ₂` on `O` equal to one near them satisfy `f = (χ₁ ⊗ χ₂) f`. A linear
change of coordinates `L : E × D → ℝⁿ` sends the support of `χ₁ ⊗ χ₂` into the open unit cube,
where `f ∘ L⁻¹` is the limit in every `C^k` norm of trigonometric polynomials
`∑ n ∈ s, c n exp (2πi ⟪n, y⟫)`
(`TauCeti.UnitAddTorus.exists_tendstoUniformlyOn_iteratedFDeriv_sum_cexp`, a truncated Fourier
series of the periodic extension). A linear form in `(x, t)` is the sum of a linear form in `x`
and one in `t`, so each exponential `exp (2πi ⟪n, L (x, t)⟫)` is a product of a function of `x`
and a function of `t`, and the real part of such a product is
`Re a Re b - Im a Im b`. Hence the cut-off real parts `(χ₁ ⊗ χ₂) Re (p ∘ L)` of these polynomials
are finite sums of tensor products of real test functions. They are supported in the fixed
compact set `tsupport χ₁ ×ˢ tsupport χ₂`, and by the Leibniz rule
(`ContDiffOn.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp`) their derivatives converge
uniformly to those of `(χ₁ ⊗ χ₂) f = f`, so they converge to `f` in the LF topology
(`TestFunction.tendsto_of_tendstoUniformly_iteratedFDeriv`).

Real-valued test functions are the ones on which Mathlib's distributions `𝓓'(Ω, F)` are defined.

## Main declarations

* `TestFunction.dense_span_prodSMulCLM`: tensor products of real test functions span a dense
  subspace of the real test functions on a product.
* `TestFunction.ext_prodSMulCLM`: a continuous linear map on the test functions on a product, with
  Hausdorff target, is determined by its values on tensor products. In particular this applies to
  distributions on a product.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §5.1 (tensor products
  of distributions and of test functions) and Theorem 5.2.1 (the Schwartz kernel theorem).
-/

public section

noncomputable section

open Complex Filter Function Set TopologicalSpace
open scoped Distributions ContDiff Topology Real

namespace TestFunction

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] {Ω : Opens E} {O : Opens D} {V : Opens (E × D)}

/-- The span of the tensor products of real test functions on `Ω` and on `O`, inside the real
test functions on `V = Ω ×ˢ O`. -/
private abbrev tensorSpan (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) : Submodule ℝ 𝓓(V, ℝ) :=
  Submodule.span ℝ (range fun p : 𝓓(O, ℝ) × 𝓓(Ω, ℝ) ↦ prodSMulCLM p.1 hV p.2)

/-- The cut-off real part `(χ₁ ⊗ χ₂) Re (u ⊗ w)` of a separable smooth complex function is a
difference of two tensor products of real test functions. -/
private theorem exists_mem_tensorSpan_eq_mul_re (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V)
    (χ₁ : 𝓓(Ω, ℝ)) (χ₂ : 𝓓(O, ℝ)) {u : E → ℂ} {w : D → ℂ} (hu : ContDiff ℝ ∞ u)
    (hw : ContDiff ℝ ∞ w) :
    ∃ h ∈ tensorSpan hV, ∀ z : E × D, h z = χ₁ z.1 * χ₂ z.2 * (u z.1 * w z.2).re := by
  have hre (v : E → ℂ) (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ fun x ↦ (v x).re :=
    reCLM.contDiff.comp hv
  have him (v : E → ℂ) (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ fun x ↦ (v x).im :=
    imCLM.contDiff.comp hv
  have hre' : ContDiff ℝ ∞ fun t ↦ (w t).re := reCLM.contDiff.comp hw
  have him' : ContDiff ℝ ∞ fun t ↦ (w t).im := imCLM.contDiff.comp hw
  refine ⟨prodSMulCLM (smulLeftCLM hre' χ₂) hV (smulLeftCLM (hre u hu) χ₁) -
    prodSMulCLM (smulLeftCLM him' χ₂) hV (smulLeftCLM (him u hu) χ₁),
    sub_mem (Submodule.subset_span ⟨(_, _), rfl⟩) (Submodule.subset_span ⟨(_, _), rfl⟩),
    fun z ↦ ?_⟩
  simp only [sub_apply, prodSMulCLM_apply, smulLeftCLM_apply, smul_eq_mul, mul_re]
  ring

/-- The cut-off real part `(χ₁ ⊗ χ₂) Re (p ∘ L)` of a trigonometric polynomial `p` read through a
linear map `L : E × D → ℝⁿ` lies in the span of the tensor products. -/
private theorem exists_mem_tensorSpan_eq_mul_re_sum (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V)
    (χ₁ : 𝓓(Ω, ℝ)) (χ₂ : 𝓓(O, ℝ)) {ι : Type*} [Fintype ι] (L : E × D →L[ℝ] ι → ℝ)
    (c : (ι → ℤ) → ℂ) (s : Finset (ι → ℤ)) :
    ∃ h ∈ tensorSpan hV, ∀ z : E × D, h z = χ₁ z.1 * χ₂ z.2 *
      (∑ n ∈ s, c n * cexp (2 * π * I * ∑ i, (n i : ℂ) * (L z i : ℂ))).re := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, zero_mem _, fun z ↦ by simp⟩
  | insert n s hn ih =>
    obtain ⟨h, hh, hhz⟩ := ih
    -- The phase is the sum of a linear form in `z.1` and one in `z.2`.
    set ℓ : E × D →L[ℝ] ℝ := (∑ i, (n i : ℝ) • ContinuousLinearMap.proj i) ∘L L
    have hℓ (z : E × D) : ∑ i, (n i : ℂ) * (L z i : ℂ) = ((ℓ (z.1, 0) + ℓ (0, z.2) : ℝ) : ℂ) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      simp [ℓ]
    have hof : ContDiff ℝ ∞ fun r : ℝ ↦ (r : ℂ) := ofRealCLM.contDiff
    have hu : ContDiff ℝ ∞ fun x : E ↦ c n * cexp (2 * π * I * (ℓ (x, 0) : ℂ)) := by
      have : ContDiff ℝ ∞ fun x : E ↦ ℓ (x, 0) := ℓ.contDiff.comp (by fun_prop)
      fun_prop
    have hw : ContDiff ℝ ∞ fun t : D ↦ cexp (2 * π * I * (ℓ (0, t) : ℂ)) := by
      have : ContDiff ℝ ∞ fun t : D ↦ ℓ (0, t) := ℓ.contDiff.comp (by fun_prop)
      fun_prop
    obtain ⟨h', hh', hh'z⟩ := exists_mem_tensorSpan_eq_mul_re hV χ₁ χ₂ hu hw
    refine ⟨h' + h, add_mem hh' hh, fun z ↦ ?_⟩
    rw [add_apply, hh'z, hhz, Finset.sum_insert hn, add_re, mul_add, hℓ, ofReal_add, mul_add,
      exp_add]
    simp only [mul_assoc]

/-- The functions `(χ₁ ⊗ χ₂) Re (P s ∘ L)` converge to `f = (χ₁ ⊗ χ₂) Re (g ∘ L)` in the LF
topology, as soon as the derivatives of the `P s` converge to those of `g`, uniformly on a set
containing the image under `L` of the support of `χ₁ ⊗ χ₂`. -/
private theorem tendsto_of_eq_mul_re {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ι : Type*} {l : Filter ι} {f : 𝓓(V, ℝ)} {χ₁ : 𝓓(Ω, ℝ)} {χ₂ : 𝓓(O, ℝ)}
    (hCV : tsupport (χ₁ : E → ℝ) ×ˢ tsupport (χ₂ : D → ℝ) ⊆ V)
    (L : E × D →L[ℝ] G) {U : Set G}
    (hLU : MapsTo L (tsupport (χ₁ : E → ℝ) ×ˢ tsupport (χ₂ : D → ℝ)) U)
    {g : G → ℂ} (hg : ContDiff ℝ ∞ g) (hfg : ∀ z, f z = χ₁ z.1 * χ₂ z.2 * (g (L z)).re)
    {P : ι → G → ℂ} (hP : ∀ s, ContDiff ℝ ∞ (P s))
    (hc : ∀ k : ℕ, TendstoUniformlyOn (fun s ↦ iteratedFDeriv ℝ k (P s)) (iteratedFDeriv ℝ k g) l U)
    {h : ι → 𝓓(V, ℝ)} (hhz : ∀ s z, h s z = χ₁ z.1 * χ₂ z.2 * (P s (L z)).re) :
    Tendsto h l (𝓝 f) := by
  set C := tsupport (χ₁ : E → ℝ) ×ˢ tsupport (χ₂ : D → ℝ)
  have hC : IsCompact C := χ₁.hasCompactSupport.prod χ₂.hasCompactSupport
  -- Every function of the form `(χ₁ ⊗ χ₂) q` is supported in `C`.
  have hsuppC {r q : E × D → ℝ} (hr : ∀ z, r z = χ₁ z.1 * χ₂ z.2 * q z) : tsupport r ⊆ C := by
    refine closure_minimal (fun z hz ↦ ?_) ((isClosed_tsupport _).prod (isClosed_tsupport _))
    rw [mem_support, hr] at hz
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul hz)),
      subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul hz))⟩
  have hle (m : ℕ) : (m : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := mod_cast le_top
  refine tendsto_of_tendstoUniformly_iteratedFDeriv hC hCV (fun s ↦ hsuppC (hhz s)) (hsuppC hfg)
    fun k _ ↦ ?_
  -- `f - h s` is `z ↦ Λ z ((g - P s) (L z))`, where `Λ z = (χ₁ ⊗ χ₂)(z) • Re`.
  set Λ : E × D → ℂ →L[ℝ] ℝ := fun z ↦ (χ₁ z.1 * χ₂ z.2) • reCLM
  have hΛ : ContDiff ℝ ∞ Λ :=
    ((χ₁.contDiff.comp contDiff_fst).mul (χ₂.contDiff.comp contDiff_snd)).smul contDiff_const
  have hdiff (s : ι) (z : E × D) : f z - h s z = Λ z ((g - P s) (L z)) := by
    simp [hfg, hhz, Λ]
    ring
  -- The derivatives of `g - P s` along `L` tend to zero uniformly on `C`.
  have hφ₀ (j : ℕ) (_ : j ≤ k) : TendstoUniformlyOn
      (fun s z ↦ iteratedFDerivWithin ℝ j (g - P s) univ (L z)) (fun _ ↦ 0) l C := by
    have h1 := ((hc j).comp L).mono fun z hz ↦ hLU hz
    rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
    intro ε hε
    filter_upwards [h1 ε hε] with s hs z hz
    rw [iteratedFDerivWithin_univ, iteratedFDeriv_sub_apply (hg.contDiffAt.of_le (hle j))
      ((hP s).contDiffAt.of_le (hle j)), dist_zero_left, ← dist_eq_norm]
    exact hs z hz
  have key := ContDiffOn.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp (n := k)
    (hΛ.of_le (hle k)).contDiffOn (L.contDiff.of_le (hle k)).contDiffOn uniqueDiffOn_univ
    uniqueDiffOn_univ (mapsTo_univ _ _) hC (subset_univ _)
    (Eventually.of_forall fun s ↦ ((hg.sub (hP s)).of_le (hle k)).contDiffOn) hφ₀
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 key ε hε] with s hs z
  have hfs : iteratedFDeriv ℝ k (⇑f - ⇑(h s)) =
      iteratedFDeriv ℝ k (fun y ↦ Λ y ((g - P s) (L y))) :=
    congrArg _ (funext (hdiff s))
  rw [dist_eq_norm, ← iteratedFDeriv_sub_apply (f.contDiff.contDiffAt.of_le (hle k))
    ((h s).contDiff.contDiffAt.of_le (hle k))]
  by_cases hz : z ∈ C
  · rw [hfs]
    simpa [iteratedFDerivWithin_univ, dist_zero_left] using hs z hz
  · -- Off `C` the difference vanishes near `z`.
    have hz' : z ∉ tsupport (⇑f - ⇑(h s)) := fun h' ↦ hz (hsuppC (q := fun y ↦
      (g (L y)).re - (P s (L y)).re) (fun y ↦ by rw [Pi.sub_apply, hfg, hhz]; ring) h')
    rw [Function.notMem_support.1 fun h' ↦ hz' (support_iteratedFDeriv_subset k h'), norm_zero]
    exact hε

/-- **Density of tensor products of test functions.** For open sets `Ω ⊆ E` and `O ⊆ D` of
finite-dimensional real normed spaces and `V = Ω ×ˢ O`, the tensor products
`(x, t) ↦ ψ t • φ x` of real test functions `φ` on `Ω` and `ψ` on `O` span a dense subspace of
the real test functions on `V`. -/
theorem dense_span_prodSMulCLM [FiniteDimensional ℝ E] [FiniteDimensional ℝ D]
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    Dense (Submodule.span ℝ (range fun p : 𝓓(O, ℝ) × 𝓓(Ω, ℝ) ↦
      prodSMulCLM p.1 hV.symm.subset p.2) : Set 𝓓(V, ℝ)) := by
  intro f
  have hK : IsCompact (tsupport (f : E × D → ℝ)) := f.hasCompactSupport
  have hKV : tsupport (f : E × D → ℝ) ⊆ (Ω : Set E) ×ˢ (O : Set D) := hV ▸ f.tsupport_subset
  -- Cutoffs `χ₁` on `Ω` and `χ₂` on `O` with `χ₁ ⊗ χ₂ = 1` on the support of `f`.
  obtain ⟨χ₁, hχ₁, -⟩ := exists_eventually_eq_one (n := ⊤) (hK.image continuous_fst)
    (image_subset_iff.2 fun p hp ↦ (hKV hp).1)
  obtain ⟨χ₂, hχ₂, -⟩ := exists_eventually_eq_one (n := ⊤) (hK.image continuous_snd)
    (image_subset_iff.2 fun p hp ↦ (hKV hp).2)
  have hχf (z : E × D) (hz : z ∈ tsupport (f : E × D → ℝ)) : χ₁ z.1 = 1 ∧ χ₂ z.2 = 1 :=
    ⟨hχ₁.self_of_nhdsSet _ (mem_image_of_mem _ hz), hχ₂.self_of_nhdsSet _ (mem_image_of_mem _ hz)⟩
  set C := tsupport (χ₁ : E → ℝ) ×ˢ tsupport (χ₂ : D → ℝ)
  have hC : IsCompact C := χ₁.hasCompactSupport.prod χ₂.hasCompactSupport
  have hCV : C ⊆ V := hV ▸ prod_mono χ₁.tsupport_subset χ₂.tsupport_subset
  have hKC : tsupport (f : E × D → ℝ) ⊆ C := fun z hz ↦
    ⟨subset_tsupport _ (by simp [(hχf z hz).1]), subset_tsupport _ (by simp [(hχf z hz).2])⟩
  -- Linear coordinates `L` sending `C` into the open unit cube.
  obtain ⟨L, hLC⟩ := hC.exists_continuousLinearEquiv_mapsTo_ball one_half_pos
  -- `f` read in these coordinates is approximated by trigonometric polynomials on the cube.
  set g : (Fin (Module.finrank ℝ (E × D)) → ℝ) → ℂ := fun y ↦ (f (L.symm y) : ℂ)
  have hg : ContDiff ℝ ∞ g := ofRealCLM.contDiff.comp (f.contDiff.comp L.symm.contDiff)
  have hgsupp : support g ⊆ Metric.ball 0 (1 / 2) := fun y hy ↦ by
    have hAy : L.symm y ∈ tsupport (f : E × D → ℝ) := subset_tsupport _ (by simpa [g] using hy)
    simpa using hLC (hKC hAy)
  obtain ⟨c, hc⟩ := TauCeti.UnitAddTorus.exists_tendstoUniformlyOn_iteratedFDeriv_sum_cexp hg hgsupp
  set L' : E × D →L[ℝ] Fin (Module.finrank ℝ (E × D)) → ℝ := L.toContinuousLinearMap
  choose h hh hhz using exists_mem_tensorSpan_eq_mul_re_sum hV.symm.subset χ₁ χ₂ L' c
  refine mem_closure_of_tendsto
    (tendsto_of_eq_mul_re hCV L' hLC hg (fun z ↦ ?_) (fun s ↦ ?_) hc hhz) (Eventually.of_forall hh)
  · by_cases hz : z ∈ tsupport (f : E × D → ℝ)
    · simp [g, L', (hχf z hz).1, (hχf z hz).2]
    · simp [g, L', image_eq_zero_of_notMem_tsupport hz]
  · have hof : ContDiff ℝ ∞ fun r : ℝ ↦ (r : ℂ) := ofRealCLM.contDiff
    fun_prop

/-- **Uniqueness on tensor products.** A continuous linear map on the real test functions on
`V = Ω ×ˢ O`, with values in a Hausdorff space, is determined by its values on the tensor products
`(x, t) ↦ ψ t • φ x`. This applies in particular to distributions `𝓓'(V, F)` on `V`: a
distributional kernel on a product is determined by its pairings with tensor products. -/
theorem ext_prodSMulCLM [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] {G 𝓕 : Type*}
    [AddCommMonoid G] [Module ℝ G] [TopologicalSpace G] [T2Space G] [FunLike 𝓕 𝓓(V, ℝ) G]
    [ContinuousLinearMapClass 𝓕 ℝ 𝓓(V, ℝ) G]
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) {T₁ T₂ : 𝓕}
    (h : ∀ (ψ : 𝓓(O, ℝ)) (φ : 𝓓(Ω, ℝ)),
      T₁ (prodSMulCLM ψ hV.symm.subset φ) = T₂ (prodSMulCLM ψ hV.symm.subset φ)) :
    T₁ = T₂ := by
  let B (T : 𝓕) : 𝓓(V, ℝ) →L[ℝ] G := ⟨T, map_continuous T⟩
  have hT : B T₁ = B T₂ :=
    ContinuousLinearMap.ext_on (dense_span_prodSMulCLM hV) <| by rintro _ ⟨p, rfl⟩; exact h p.1 p.2
  exact DFunLike.coe_injective congr($hT)

end TestFunction
