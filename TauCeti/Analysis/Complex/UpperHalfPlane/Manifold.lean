/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.Algebra.SMul

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Analysis.Polynomial.SymmetricPower
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.DiscreteSeparation

/-!
# Smoothness and analyticity through `ofComplex`

Near `τ`, the chart of `ℍ` at `τ` reads a function `f` as its extension `f ∘ ofComplex`
(`comp_chartAt_symm_eventuallyEq` and `UpperHalfPlane.writtenInExtChartAt_eventuallyEq`), so its
manifold derivative in tangent coordinates is the Fréchet derivative of
`extChartAt J (f τ) ∘ f ∘ ofComplex` (`UpperHalfPlane.tangentSpaceCastModel_mfderiv_apply`), and
the real coordinate functions `z ↦ Im z` and `z ↦ log (Im z)` are real-analytic (`contMDiff_im`,
`contMDiff_log_im`). A function holomorphic on the upper half-plane, extended to `ℂ` by
`ofComplex`, is analytic at every point of the open upper half-plane, and a locally uniform limit
of holomorphic functions on `ℍ` is holomorphic.

Holomorphy on `ℍ` is invariant under the Möbius action of a positive-determinant real matrix, the
biholomorphism `UpperHalfPlane.mdifferentiable_smul` exhibits (`mdifferentiable_comp_smul_iff`),
while the reflection `UpperHalfPlane.J : z ↦ -conj z` is real-analytic (`contMDiff_J_smul`), so
every element of `GL(2, ℝ)`, `PGL(2, ℝ)`, and `SL(2, R)` acts on `ℍ` by a real-analytic map for
`𝓘(ℝ, ℂ)`. Polynomial functions of the coordinate, such as `z ↦ P(z, 1)` for a binary form `P`,
are holomorphic, and so are the coefficients of a product `∏ (X - aᵢ(τ))` of linear factors whose
roots `aᵢ` are holomorphic.

## Main declarations

* `TauCeti.UpperHalfPlane.comp_chartAt_symm_eventuallyEq`,
  `UpperHalfPlane.writtenInExtChartAt_eventuallyEq`, and
  `UpperHalfPlane.tangentSpaceCastModel_mfderiv_apply` — near `τ`, a function read in the chart of
  `ℍ` at `τ` is its extension by `ofComplex`, and its differential in tangent coordinates is the
  Fréchet derivative of `extChartAt J (f τ) ∘ f ∘ ofComplex`.
* `TauCeti.UpperHalfPlane.contMDiff_im` and `TauCeti.UpperHalfPlane.contMDiff_log_im` — `Im` and
  `log ∘ Im` are real-analytic on `ℍ`.
* `TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex`.
* `MvPolynomial.mdifferentiable_aeval_coe` — `z ↦ P(z, 1)` is holomorphic for a polynomial `P`
  in two variables.
* `TauCeti.UpperHalfPlane.mdifferentiable_coeff_prod_X_sub_C` — the coefficients of
  `∏ (X - aᵢ(τ))` are holomorphic when every `aᵢ` is.
* `TauCeti.UpperHalfPlane.mdifferentiable_comp_smul_iff` — `τ ↦ f (g • τ)` is holomorphic
  exactly when `f` is, for `g : GL (Fin 2) ℝ` of positive determinant.
* `TauCeti.UpperHalfPlane.contMDiff_J_smul`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulGLReal`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulPGLReal`, and
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulSL2Real` — `J`, `GL(2, ℝ)`, `PGL(2, ℝ)`, and
  `SL(2, R)` act on `ℍ` by real-analytic maps (`𝓘(ℝ, ℂ)`).
* `TauCeti.UpperHalfPlane.not_accPt_zeros_comp_ofComplex` and
  `TauCeti.UpperHalfPlane.exists_isOpen_zeros_inter` — a subset's zeros isolate in an
  open neighbourhood.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press (1992), §1.1.
* Alan Beardon, *The Geometry of Discrete Groups*, Springer GTM 91 (1983), §7.2.
-/

public section

open Filter Topology UpperHalfPlane

open scoped ContDiff Manifold MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- The representative of `f` in the chart of `ℍ` at `τ` agrees with `f ∘ ofComplex` near `τ`. -/
theorem comp_chartAt_symm_eventuallyEq {α : Type*} (f : ℍ → α) (τ : ℍ) :
    f ∘ (chartAt ℂ τ).symm =ᶠ[𝓝 (τ : ℂ)] f ∘ ofComplex := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
  have hwt : w ∈ (chartAt ℂ τ).target := by simpa using hw
  rw [Function.comp_apply, Function.comp_apply, ofComplex_apply_of_im_pos hw]
  congr 1
  ext
  simpa using (chartAt ℂ τ).right_inv hwt

/-- In the inclusion chart of `ℍ` at `z` for the manifold structure `𝓘(𝕜, ℂ)`,
`writtenInExtChartAt 𝓘(𝕜, ℂ) J z f` agrees near `(z : ℂ)` with
`extChartAt J (f z) ∘ f ∘ ofComplex`. -/
theorem _root_.UpperHalfPlane.writtenInExtChartAt_eventuallyEq (z : ℍ)
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (J : ModelWithCorners 𝕜 E H)
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] (f : ℍ → N) :
    writtenInExtChartAt 𝓘(𝕜, ℂ) J z f =ᶠ[𝓝 (z : ℂ)] extChartAt J (f z) ∘ f ∘ ofComplex := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  have hsymm : (extChartAt 𝓘(𝕜, ℂ) z).symm w = ofComplex w := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos hw, coe_mk]
    simpa using (extChartAt 𝓘(𝕜, ℂ) z).right_inv (by simpa using hw)
  simp only [writtenInExtChartAt, Function.comp_apply, hsymm]

/-- In the inclusion chart of `ℍ` at `z`, the manifold derivative of a differentiable map
`f : ℍ → N` read through `tangentSpaceCastModel` is the Fréchet derivative of
`extChartAt J (f z) ∘ f ∘ ofComplex` at `(z : ℂ)`. -/
theorem _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_apply (z : ℍ)
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners 𝕜 E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] {f : ℍ → N}
    (hf : MDifferentiableAt 𝓘(𝕜, ℂ) J f z) (v : TangentSpace 𝓘(𝕜, ℂ) z) :
    tangentSpaceCastModel J (f z) (mfderiv 𝓘(𝕜, ℂ) J f z v) =
      fderiv 𝕜 (extChartAt J (f z) ∘ f ∘ ofComplex) (z : ℂ)
        (tangentSpaceCastModel 𝓘(𝕜, ℂ) z v) := by
  have hchart : extChartAt 𝓘(𝕜, ℂ) z z = (z : ℂ) := by simp
  rw [hf.tangentSpaceCastModel_mfderiv_apply, hchart,
    (z.writtenInExtChartAt_eventuallyEq J f).fderiv_eq]

/-- The imaginary-part coordinate `z ↦ Im z` is real-analytic on `ℍ` (and hence `C^n` of every
order `n : ℕ∞ω`). -/
theorem contMDiff_im {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n UpperHalfPlane.im := fun z ↦
  Complex.imCLM.contMDiff.contMDiffAt.comp z contMDiffAt_extChartAt

/-- The logarithmic height `z ↦ log (Im z)` is real-analytic on `ℍ` (and hence `C^n` of every
order `n : ℕ∞ω`). -/
theorem contMDiff_log_im {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n (fun z : ℍ ↦ Real.log z.im) := fun z ↦
  (Real.contDiffAt_log.2 z.im_ne_zero).contMDiffAt.comp z (contMDiff_im z)

/-- For a polynomial `P` in two variables with coefficients mapping to `ℂ`, the function
`z ↦ P(z, 1)` is holomorphic on `ℍ`. -/
lemma _root_.MvPolynomial.mdifferentiable_aeval_coe {R : Type*} [CommSemiring R] [Algebra R ℂ]
    (P : MvPolynomial (Fin 2) R) : MDiff fun z : ℍ ↦ MvPolynomial.aeval ![(z : ℂ), 1] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using mdifferentiable_const
  | add p q hp hq =>
    simp only [map_add]
    exact MDifferentiable.add hp hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    refine MDifferentiable.mul hp ?_
    fin_cases i
    · simpa using mdifferentiable_coe
    · simpa using mdifferentiable_const

open _root_.Polynomial in
/-- The coefficients of `∏ (X - C (aᵢ τ))` are holomorphic functions of `τ` when every `aᵢ` is. -/
theorem mdifferentiable_coeff_prod_X_sub_C {ι : Type*} (s : Finset ι) {a : ι → ℍ → ℂ}
    (ha : ∀ i ∈ s, MDiff (a i)) (k : ℕ) :
    MDiff fun τ : ℍ ↦ ((∏ i ∈ s, (X - C (a i τ))).coeff k : ℂ) := by
  -- index the roots by `s`: the coefficient is an analytic function of the tuple of roots
  have hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, s → ℂ) fun τ : ℍ ↦ fun i : s ↦ a i τ :=
    mdifferentiable_pi_space_iff.2 fun i ↦ ha i i.2
  have hg : Differentiable ℂ fun v : s → ℂ ↦ (∏ i : s, (X - C (v i))).coeff k := fun v ↦
    (TauCeti.Polynomial.analyticAt_coeff_prod_X_sub_C Finset.univ k v).differentiableAt
  convert Differentiable.comp_mdifferentiable hg hv using 1
  ext τ
  rw [Function.comp_apply, Finset.prod_coe_sort s fun i ↦ X - C (a i τ)]

/-- A function holomorphic on `ℍ` composes with `ofComplex` to a function analytic at
every point of the open upper half-plane. -/
lemma analyticAt_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) {w : ℂ} (hw : 0 < w.im) :
    AnalyticAt ℂ (f ∘ ofComplex) w :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hw)

/-- The zeros of a nonzero holomorphic function's complex extension do not accumulate at
any point of the upper half-plane. -/
lemma not_accPt_zeros_comp_ofComplex {g : ℍ → ℂ} (hg : MDiff g) (hg0 : g ≠ 0)
    {x : ℂ} (hx : 0 < x.im) :
    ¬AccPt x (Filter.principal {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0}) := by
  have hall : AnalyticOnNhd ℂ (g ∘ ofComplex) {z : ℂ | 0 < z.im} := fun w hw =>
    analyticAt_comp_ofComplex hg hw
  obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hg0
  have hcod := hall.preimage_zero_mem_codiscreteWithin (x := (τ : ℂ))
    (by simpa [Function.comp, ofComplex_apply] using hτ) τ.2
    ⟨⟨Complex.I, by simp⟩, (convex_halfSpace_im_gt 0).isPreconnected⟩
  have hne := mem_codiscreteWithin_accPt.mp hcod x hx
  have hset : {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0} =
      {z : ℂ | 0 < z.im} \ (g ∘ ofComplex) ⁻¹' {0}ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_not]
  rwa [hset]

/-- Any subset of the upper half-plane has an open neighbourhood in the upper half-plane
containing no zeros of the function's complex extension beyond its own. -/
lemma exists_isOpen_zeros_inter {g : ℍ → ℂ} (hg : MDiff g) (hg0 : g ≠ 0)
    {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ U ⊆ {z : ℂ | 0 < z.im} ∧
      {z ∈ U | (g ∘ ofComplex) z = 0} = {z ∈ K | (g ∘ ofComplex) z = 0} := by
  obtain ⟨U, hUo, hKU, hUV, hUZ⟩ := TauCeti.exists_isOpen_inter_eq_of_not_accPt
    (Z := {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0}) isOpen_upperHalfPlaneSet hK
    fun x hx => not_accPt_zeros_comp_ofComplex hg hg0 (hK hx)
  refine ⟨U, hUo, hKU, hUV, ?_⟩
  have hmassage : ∀ {W : Set ℂ}, W ⊆ {z : ℂ | 0 < z.im} →
      {z ∈ W | (g ∘ ofComplex) z = 0} =
        W ∩ {z : ℂ | 0 < z.im ∧ (g ∘ ofComplex) z = 0} := by
    intro W hW
    ext z
    exact ⟨fun hz => ⟨hz.1, hW hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
  rw [hmassage hUV, hmassage hK, hUZ]

/-- **A locally uniform limit of holomorphic functions on `ℍ` is holomorphic**: the limit is
transported to the open upper half-plane of `ℂ` by `ofComplex`. -/
lemma mdifferentiable_of_tendstoLocallyUniformly {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℍ → ℂ} {f : ℍ → ℂ} (hF : TendstoLocallyUniformly F f l)
    (hFd : ∀ᶠ i in l, MDiff (F i)) : MDiff f := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hloc : TendstoLocallyUniformlyOn (fun i ↦ ↑ₕ(F i)) (↑ₕf) l {z : ℂ | 0 < z.im} := by
    rw [← upperHalfPlaneSet, ← range_coe, ← Set.image_univ]
    apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _
      (OpenPartialHomeomorph.continuousOn_symm _)
    · simpa only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ] using hF
    · simp only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ,
        Set.mapsTo_range_iff, Set.mem_univ, forall_const]
  exact hloc.differentiableOn (hFd.mono fun i hi ↦ UpperHalfPlane.mdifferentiable_iff.mp hi)
    isOpen_upperHalfPlaneSet

/-! ### Holomorphy and smoothness of the Möbius action -/

/-- **Holomorphy is invariant under a positive-determinant Möbius action.** For any
`g : GL (Fin 2) ℝ` with `0 < det g`, the function `τ ↦ f (g • τ)` is holomorphic exactly when
`f` is: `g` acts on `ℍ` by a biholomorphism, whose inverse is the action of `g⁻¹`, again of
positive determinant. -/
lemma mdifferentiable_comp_smul_iff {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) {f : ℍ → ℂ} :
    MDiff (fun τ ↦ f (g • τ)) ↔ MDiff f := by
  have hg' : 0 < ((g⁻¹).det : ℝ) := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hg
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.comp (mdifferentiable_smul hg)⟩
  have hcomp : f = (fun τ ↦ f (g • τ)) ∘ fun τ : ℍ ↦ g⁻¹ • τ := by
    funext τ
    simp [smul_smul]
  rw [hcomp]
  exact hf.comp (mdifferentiable_smul hg')

/-- The reflection `UpperHalfPlane.J : z ↦ -conj z` is real-analytic on `ℍ` (and hence `C^n` of
every order `n : ℕ∞ω`). -/
theorem contMDiff_J_smul {n : ℕ∞ω} : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (J • · : ℍ → ℍ) := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe
  have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n UpperHalfPlane.coe := fun _ ↦ contMDiffAt_extChartAt
  have hfun : UpperHalfPlane.coe ∘ (J • · : ℍ → ℍ) = (-Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘
      UpperHalfPlane.coe := by
    funext z
    simp [coe_J_smul]
  rw [hfun]
  exact (-Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contMDiff.comp hcoe

/-- Every element of `GL(2, ℝ)` acts on `ℍ` by a real-analytic map (and hence smoothly of every
order `n : ℕ∞ω`). -/
instance instContMDiffConstSMulGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul g := by
    -- Positive-determinant matrices act holomorphically; negative-determinant ones factor via `J`.
    have hpos {h : GL (Fin 2) ℝ} (hh : 0 < h.det.val) :
        ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (h • · : ℍ → ℍ) := by
      simpa only [modelWithCornersSelf_restrictScalars] using
        ((UpperHalfPlane.contMDiff_smul (n := ω) hh).restrictScalars ℝ).of_le le_top
    rcases g.det.ne_zero.lt_or_gt with hg | hg
    · have hJg : 0 < (J * g).det.val := by simpa using hg
      have hcomp : (g • · : ℍ → ℍ) = (J • ·) ∘ ((J * g) • ·) := by
        funext z
        simp [smul_smul, ← mul_assoc, ← sq]
      rw [hcomp]
      exact contMDiff_J_smul.comp (hpos hJg)
    · exact hpos hg

/-- Every element of `PGL(2, ℝ)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulPGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

/-- Every element of `SL(2, R)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulSL2Real {R : Type*} [CommRing R] [Algebra R ℝ] {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n SL(2, R) ℍ :=
  MulAction.contMDiffConstSMul_compHom (I := 𝓘(ℝ, ℂ)) (f := Matrix.SpecialLinearGroup.mapGL ℝ)

end TauCeti.UpperHalfPlane

end
