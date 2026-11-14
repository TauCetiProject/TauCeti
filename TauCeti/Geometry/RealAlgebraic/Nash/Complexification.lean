/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Analytic.Complexification.Basic
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Analytic.Polynomial
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Derivative
import TauCeti.Order.Filter.Germ.Complex

/-!
# Realification of holomorphic algebraic germs

The real and imaginary parts of a holomorphic function satisfying a nonzero complex
polynomial relation are Nash in the doubled real coordinates. In particular a holomorphic
extension of a Nash germ has Nash real and imaginary parts, and differentiating along
complex directions preserves this property. This is the algebraic realification needed to
use holomorphic root clusters and vertical jets in real Nash geometry.

The coordinates are those of `TauCeti.complexToRealPi`: the first block gives the real
parts and the second block the imaginary parts. The polynomial relation extends from the
real locus by holomorphic uniqueness. Algebraic descent gives separate real polynomial
relations for the two components, including on the singular locus of the original relation.

## Main declarations

* `AnalyticAt.isNashAt_re_im_of_polynomial_relation`: realification of a holomorphic
  algebraic germ, at any complex point.
* `AnalyticAt.isNashAt_fderiv_re_im`, `AnalyticAt.isNashAt_iteratedDeriv_sumElim_re_im`:
  holomorphic directional and iterated vertical derivatives preserve Nashness of real and
  imaginary parts in doubled real coordinates.
* `TauCeti.IsNashAt.complexification_re_im`: Nashness of the components of any holomorphic
  extension of a real Nash germ.
* `TauCeti.IsNashAt.exists_complexification`: a conjugation-invariant holomorphic extension
  with semialgebraic domain and graph, inside any prescribed neighborhood.
* `TauCeti.IsNashAt.complexification_iteratedDeriv_sumElim_re_im`,
  `TauCeti.IsNashAt.exists_isSemialgebraicOn_complexification_iteratedDeriv_sumElim`:
  Nashness and uniform semialgebraicity of iterated vertical complex derivatives of a
  complexified Nash germ.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Section 8.1 (Nash functions).
-/

public section

open Filter Polynomial Set Topology

namespace AnalyticAt

/-- A holomorphic algebraic germ has Nash real and imaginary parts in doubled real
coordinates. No simple-root or discriminant hypothesis is imposed on its relation. -/
theorem isNashAt_re_im_of_polynomial_relation {σ : Type*} [Fintype σ]
    {F : (σ → ℂ) → ℂ} {z : σ → ℂ} (hF : AnalyticAt ℂ F z)
    (P : (MvPolynomial σ ℂ)[X]) (hP : P ≠ 0)
    (hrel : ∀ᶠ w in 𝓝 z, (P.map (MvPolynomial.eval w)).eval (F w) = 0) :
    TauCeti.IsNashAt (fun a ↦ (F ((TauCeti.complexToRealPi σ).symm a)).re)
        (TauCeti.complexToRealPi σ z) ∧
      TauCeti.IsNashAt (fun a ↦ (F ((TauCeti.complexToRealPi σ).symm a)).im)
        (TauCeti.complexToRealPi σ z) := by
  let e := TauCeti.complexToRealPi σ
  let s : MvPolynomial σ ℂ →+* MvPolynomial (σ ⊕ σ) ℂ :=
    (MvPolynomial.aeval fun i ↦
      MvPolynomial.X (.inl i) + MvPolynomial.X (.inr i) * MvPolynomial.C Complex.I).toRingHom
  let t : MvPolynomial (σ ⊕ σ) ℂ →+* MvPolynomial σ ℂ :=
    (MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun _ ↦ 0))).toRingHom
  have hts : t.comp s = RingHom.id _ := by
    ext <;> simp [s, t]
  have hleft : Function.LeftInverse t s := by
    intro p
    simpa only [RingHom.comp_apply, RingHom.id_apply] using DFunLike.congr_fun hts p
  have hs : Function.Injective s := hleft.injective
  have hmap (a : σ ⊕ σ → ℝ) :
      (P.map s).map (MvPolynomial.eval fun i ↦ (a i : ℂ)) =
        P.map (MvPolynomial.eval (e.symm a)) := by
    rw [Polynomial.map_map]
    congr 1
    ext <;> simp [s, e]
  have he : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
    simpa only [e.symm_apply_apply] using (e.symm.continuousAt (x := e z)).tendsto
  obtain ⟨hR, hI⟩ := (P.map s).exists_real_polynomial_relations
    ((Polynomial.map_ne_zero_iff hs).mpr hP) (f := fun a ↦ F (e.symm a)) (by
      filter_upwards [he.eventually hrel] with a ha
      rw [hmap]
      exact ha)
  have ha : AnalyticAt ℝ (fun a ↦ F (e.symm a)) (e z) := by
    have hF' : AnalyticAt ℝ F (e.symm (e z)) := by
      simpa only [e.symm_apply_apply] using hF.restrictScalars (𝕜 := ℝ)
    exact hF'.comp (e.symm.analyticAt _)
  exact ⟨TauCeti.isNashAt_iff.mpr ⟨(Complex.reCLM.analyticAt _).comp ha, hR⟩,
    TauCeti.isNashAt_iff.mpr ⟨(Complex.imCLM.analyticAt _).comp ha, hI⟩⟩

/-- If a holomorphic germ `F` at `z₀` has Nash real and imaginary parts in doubled real
coordinates, then so does its complex directional derivative along any `v : σ → ℂ`. -/
theorem isNashAt_fderiv_re_im {σ : Type*} [Fintype σ]
    {F : (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hF : AnalyticAt ℂ F z₀)
    (hre : TauCeti.IsNashAt (fun a ↦ (F ((TauCeti.complexToRealPi σ).symm a)).re)
      (TauCeti.complexToRealPi σ z₀))
    (him : TauCeti.IsNashAt (fun a ↦ (F ((TauCeti.complexToRealPi σ).symm a)).im)
      (TauCeti.complexToRealPi σ z₀))
    (v : σ → ℂ) :
    TauCeti.IsNashAt (fun a ↦ (fderiv ℂ F ((TauCeti.complexToRealPi σ).symm a) v).re)
        (TauCeti.complexToRealPi σ z₀) ∧
      TauCeti.IsNashAt (fun a ↦ (fderiv ℂ F ((TauCeti.complexToRealPi σ).symm a) v).im)
        (TauCeti.complexToRealPi σ z₀) := by
  let e := TauCeti.complexToRealPi σ
  have he : Tendsto e.symm (𝓝 (e z₀)) (𝓝 z₀) := by
    simpa only [e.symm_apply_apply] using (e.symm.continuousAt (x := e z₀)).tendsto
  refine ⟨(hre.fderiv_apply (e v)).congr ?_, (him.fderiv_apply (e v)).congr ?_⟩
  · filter_upwards [he.eventually hF.eventually_analyticAt] with a ha
    have hd : HasFDerivAt (fun b ↦ (F (e.symm b)).re)
        (Complex.reCLM.comp (((fderiv ℂ F (e.symm a)).restrictScalars ℝ).comp
          e.symm.toContinuousLinearMap)) a :=
      Complex.reCLM.hasFDerivAt.comp a
        ((ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a e.symm.hasFDerivAt)
    rw [hd.fderiv]
    simp [e]
  · filter_upwards [he.eventually hF.eventually_analyticAt] with a ha
    have hd : HasFDerivAt (fun b ↦ (F (e.symm b)).im)
        (Complex.imCLM.comp (((fderiv ℂ F (e.symm a)).restrictScalars ℝ).comp
          e.symm.toContinuousLinearMap)) a :=
      Complex.imCLM.hasFDerivAt.comp a
        ((ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a e.symm.hasFDerivAt)
    rw [hd.fderiv]
    simp [e]

/-- If a holomorphic germ `F` on `σ ⊕ Unit → ℂ` at `z₀` has Nash real and imaginary parts in
doubled real coordinates, then so does every iterated complex derivative along the `Unit`
coordinate. -/
theorem isNashAt_iteratedDeriv_sumElim_re_im {σ : Type*} [Fintype σ]
    {F : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ ⊕ Unit → ℂ} (hF : AnalyticAt ℂ F z₀)
    (hre : TauCeti.IsNashAt (fun a ↦ (F ((TauCeti.complexToRealPi (σ ⊕ Unit)).symm a)).re)
      (TauCeti.complexToRealPi (σ ⊕ Unit) z₀))
    (him : TauCeti.IsNashAt (fun a ↦ (F ((TauCeti.complexToRealPi (σ ⊕ Unit)).symm a)).im)
      (TauCeti.complexToRealPi (σ ⊕ Unit) z₀))
    (k : ℕ) :
    TauCeti.IsNashAt
        (fun a ↦ (iteratedDeriv k
          (fun ζ ↦ F (Sum.elim (((TauCeti.complexToRealPi (σ ⊕ Unit)).symm a) ∘ Sum.inl)
            (fun _ ↦ ζ)))
          (((TauCeti.complexToRealPi (σ ⊕ Unit)).symm a) (.inr ()))).re)
        (TauCeti.complexToRealPi (σ ⊕ Unit) z₀) ∧
      TauCeti.IsNashAt
        (fun a ↦ (iteratedDeriv k
          (fun ζ ↦ F (Sum.elim (((TauCeti.complexToRealPi (σ ⊕ Unit)).symm a) ∘ Sum.inl)
            (fun _ ↦ ζ)))
          (((TauCeti.complexToRealPi (σ ⊕ Unit)).symm a) (.inr ()))).im)
        (TauCeti.complexToRealPi (σ ⊕ Unit) z₀) := by
  induction k generalizing F with
  | zero =>
    have hp (p : σ ⊕ Unit → ℂ) : Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (.inr ())) = p := by
      ext (s | ⟨⟩) <;> rfl
    exact ⟨hre.congr <| .of_forall fun a ↦ by simp only [iteratedDeriv_zero, hp],
      him.congr <| .of_forall fun a ↦ by simp only [iteratedDeriv_zero, hp]⟩
  | succ k ih =>
    let e := TauCeti.complexToRealPi (σ ⊕ Unit)
    let v : σ ⊕ Unit → ℂ := Sum.elim 0 (fun _ ↦ 1)
    let F' : (σ ⊕ Unit → ℂ) → ℂ := fun p ↦ fderiv ℂ F p v
    have hF'a : AnalyticAt ℂ F' z₀ :=
      ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hF.fderiv
    obtain ⟨hre', him'⟩ := hF.isNashAt_fderiv_re_im hre him v
    obtain ⟨ih_re, ih_im⟩ := ih hF'a hre' him'
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_analyticAt ℂ F) z₀ hF
    have he : Tendsto e.symm (𝓝 (e z₀)) (𝓝 z₀) := by
      simpa only [e.symm_apply_apply] using (e.symm.continuousAt (x := e z₀)).tendsto
    have hcongr : ∀ᶠ a in 𝓝 (e z₀),
        iteratedDeriv (k + 1)
          (fun ζ ↦ F (Sum.elim ((e.symm a) ∘ Sum.inl) (fun _ ↦ ζ))) ((e.symm a) (.inr ())) =
        iteratedDeriv k
          (fun ζ ↦ F' (Sum.elim ((e.symm a) ∘ Sum.inl) (fun _ ↦ ζ))) ((e.symm a) (.inr ())) := by
      filter_upwards [he.eventually (Metric.ball_mem_nhds z₀ (half_pos hr))] with a ha
      let p := e.symm a
      have hp_lt : dist p z₀ < r := (Metric.mem_ball.1 ha).trans (half_lt_self hr)
      have hcont : Continuous fun ζ : ℂ ↦ Sum.elim (p ∘ Sum.inl) (fun _ : Unit ↦ ζ) :=
        continuous_pi fun i ↦ by
          cases i with
          | inl _ => exact continuous_const
          | inr _ => exact continuous_id
      have hp_eq : Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (.inr ())) = p := by ext (s | ⟨⟩) <;> rfl
      have hderiv_eq : (fun ζ ↦ F' (Sum.elim (p ∘ Sum.inl) (fun _ ↦ ζ))) =ᶠ[𝓝 (p (.inr ()))]
          deriv (fun ζ ↦ F (Sum.elim (p ∘ Sum.inl) (fun _ ↦ ζ))) := by
        filter_upwards [(hcont.tendsto (p (.inr ()))).eventually
          (hp_eq ▸ Metric.isOpen_ball.mem_nhds (Metric.mem_ball.2 hp_lt))] with ζ hζ
        have hline : HasDerivAt (fun w : ℂ ↦ Sum.elim (p ∘ Sum.inl) (fun _ : Unit ↦ w)) v ζ :=
          hasDerivAt_pi.2 fun i ↦ by
            cases i with
            | inl s => simpa [v] using hasDerivAt_const ζ (p (.inl s))
            | inr _ => simpa [v] using hasDerivAt_id' ζ
        exact (((hball hζ).differentiableAt.hasFDerivAt.comp_hasDerivAt ζ hline).deriv).symm
      rw [iteratedDeriv_succ']
      exact (hderiv_eq.iteratedDeriv_eq k).symm
    exact ⟨ih_re.congr (hcongr.mono fun _ h ↦ congrArg Complex.re h.symm),
      ih_im.congr (hcongr.mono fun _ h ↦ congrArg Complex.im h.symm)⟩

end AnalyticAt

namespace TauCeti

/-- Every holomorphic extension of a Nash germ has Nash real and imaginary parts in the
real coordinates of its complex domain. Agreement with the original function is needed
only as a germ on the real locus. -/
theorem IsNashAt.complexification_re_im {σ : Type*} [Fintype σ]
    {f : (σ → ℝ) → ℝ} {x : σ → ℝ} (hf : IsNashAt f x)
    {F : (σ → ℂ) → ℂ} (hF : AnalyticAt ℂ F (fun i ↦ (x i : ℂ)))
    (hFr : ∀ᶠ y in 𝓝 x, F (fun i ↦ (y i : ℂ)) = f y) :
    IsNashAt (fun a ↦ (F ((complexToRealPi σ).symm a)).re)
        (complexToRealPi σ (fun i ↦ (x i : ℂ))) ∧
      IsNashAt (fun a ↦ (F ((complexToRealPi σ).symm a)).im)
        (complexToRealPi σ (fun i ↦ (x i : ℂ))) := by
  obtain ⟨_, P, hP, hrel⟩ := isNashAt_iff.mp hf
  let j := MvPolynomial.map (algebraMap ℝ ℂ) (σ := σ)
  let Q := P.map j
  have hQ : Q ≠ 0 := (Polynomial.map_ne_zero_iff
    (MvPolynomial.map_injective _ Complex.ofReal_injective)).mpr hP
  have heval (y : σ → ℝ) :
      Q.map (MvPolynomial.eval fun i ↦ (y i : ℂ)) =
        (P.map (MvPolynomial.eval y)).map (algebraMap ℝ ℂ) := by
    simp only [Q, Polynomial.map_map]
    congr 1
    apply RingHom.ext
    intro p
    exact (MvPolynomial.map_eval (algebraMap ℝ ℂ) y p).symm
  have hQa : AnalyticAt ℂ
      (fun z ↦ (Q.map (MvPolynomial.eval z)).eval (F z)) (fun i ↦ (x i : ℂ)) :=
    (AnalyticOnNhd.eval_map_eval (s := {z | AnalyticAt ℂ F z}) (fun _ hz ↦ hz) Q) _ hF
  apply hF.isNashAt_re_im_of_polynomial_relation Q hQ
  apply hQa.eventually_eq_zero_of_eventually_real
  filter_upwards [hFr, hrel] with y hy hyP
  rw [hy, heval]
  simpa only [hyP, map_zero, Complex.coe_algebraMap] using
    (Polynomial.eval_map_apply (f := algebraMap ℝ ℂ) (p := P.map (MvPolynomial.eval y)) (f y))

/-- A Nash germ has a holomorphic extension on an arbitrarily small conjugation-invariant
open neighborhood, with semialgebraic domain and graph in doubled real coordinates. The
extension agrees with the original function at all real points of that neighborhood. -/
theorem IsNashAt.exists_complexification {σ : Type*} [Fintype σ]
    {f : (σ → ℝ) → ℝ} {x : σ → ℝ} (hf : IsNashAt f x)
    {W : Set (σ → ℂ)} (hW : W ∈ 𝓝 (fun i ↦ (x i : ℂ))) :
    ∃ V : Set (σ → ℂ), IsOpen V ∧ (fun i ↦ (x i : ℂ)) ∈ V ∧ V ⊆ W ∧
      (∀ z, star z ∈ V ↔ z ∈ V) ∧
      IsSemialgebraic ((complexToRealPi σ).symm ⁻¹' V) ∧
      ∃ F : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ F V ∧
        (∀ y : σ → ℝ, (fun i ↦ (y i : ℂ)) ∈ V → F (fun i ↦ (y i : ℂ)) = f y) ∧
        (∀ z, F (star z) = star (F z)) ∧
        IsSemialgebraicOn
          (fun a ↦ complexToRealPi Unit (fun _ ↦ F ((complexToRealPi σ).symm a)))
          ((complexToRealPi σ).symm ⁻¹' V) := by
  obtain ⟨s, hs, F, hF, hFr, hFstar⟩ := hf.analyticAt.exists_complexification
  let e := complexToRealPi σ
  let z : σ → ℂ := fun i ↦ (x i : ℂ)
  have hFa : AnalyticAt ℂ F z := hF z (Metric.mem_ball_self hs)
  have hN := hf.complexification_re_im hFa
    (eventually_of_mem (Metric.ball_mem_nhds x hs) hFr)
  have hcoords : ∀ i : Unit ⊕ Unit, IsNashAt
      (fun a ↦ complexToRealPi Unit (fun _ ↦ F (e.symm a)) i) (e z) := by
    intro i
    cases i with
    | inl i => simpa only [complexToRealPi_apply, Sum.elim_inl, e, z] using hN.1
    | inr i => simpa only [complexToRealPi_apply, Sum.elim_inr, e, z] using hN.2
  obtain ⟨_, U, hUo, hzU, hG⟩ :=
    forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mp hcoords
  have he : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
    simpa only [e.symm_apply_apply] using (e.symm.continuousAt (x := e z)).tendsto
  -- Shrink one common graph neighborhood inside both prescribed analytic domains.
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hUo.mem_nhds hzU) (he.eventually (inter_mem hW (Metric.ball_mem_nhds z hs))))
  let V := e ⁻¹' Metric.ball (e z) r
  have hVB : V ⊆ W ∩ Metric.ball z s := by
    intro w hw
    have hw' : e.symm (e w) ∈ W ∩ Metric.ball z s := (hball hw).2
    simpa only [e.symm_apply_apply] using hw'
  have heV : e.symm ⁻¹' V = Metric.ball (e z) r := by
    ext a
    simp only [V, mem_preimage, e.apply_symm_apply]
  refine ⟨V, Metric.isOpen_ball.preimage e.continuous, Metric.mem_ball_self hr,
    fun w hw ↦ (hVB hw).1, ?_, ?_, F, hF.mono (fun w hw ↦ (hVB hw).2), ?_, hFstar, ?_⟩
  · -- The center has zero imaginary block, so conjugation preserves this real box.
    intro w
    simp only [V, mem_preimage, Metric.mem_ball, dist_pi_lt_iff hr]
    constructor <;> intro h i <;> cases i with
    | inl i => simpa [e, z] using h (.inl i)
    | inr i => simpa [e, z, Real.dist_eq] using h (.inr i)
  · rw [heV]
    exact isSemialgebraic_ball _ _
  · intro y hy
    apply hFr y
    have hyB := (hVB hy).2
    rw [Metric.mem_ball, dist_pi_lt_iff hs] at hyB ⊢
    intro i
    simpa only [z, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using hyB i
  · rw [heV]
    exact hG.mono (isSemialgebraic_ball _ _) fun a ha ↦ (hball ha).1

/-- For a holomorphic extension `F` of a Nash germ `f` at `Sum.elim x₀ (fun _ ↦ t₀)`, the real and
imaginary parts of `(x, w) ↦ iteratedDeriv k (fun ζ ↦ F (x, ζ)) w` at real `x` and complex `w` are
Nash germs at `(x₀, t₀, 0)`. -/
theorem IsNashAt.complexification_iteratedDeriv_sumElim_re_im {σ : Type*} [Fintype σ]
    {f : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    {F : (σ ⊕ Unit → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F (fun j ↦ ((Sum.elim x₀ (fun _ ↦ t₀) : σ ⊕ Unit → ℝ) j : ℂ)))
    (hFr : ∀ᶠ y in 𝓝 (Sum.elim x₀ (fun _ ↦ t₀)), F (fun j ↦ (y j : ℂ)) = f y) (k : ℕ) :
    let q₀ : σ ⊕ (Unit ⊕ Unit) → ℝ := Sum.elim x₀ (Sum.elim (fun _ ↦ t₀) (fun _ ↦ 0))
    IsNashAt (fun q : σ ⊕ (Unit ⊕ Unit) → ℝ ↦
        (iteratedDeriv k
          (fun ζ ↦ F (Sum.elim (fun s ↦ (q (.inl s) : ℂ)) (fun _ ↦ ζ)))
          ((q (.inr (.inl ())) : ℂ) + q (.inr (.inr ())) * Complex.I)).re) q₀ ∧
      IsNashAt (fun q : σ ⊕ (Unit ⊕ Unit) → ℝ ↦
        (iteratedDeriv k
          (fun ζ ↦ F (Sum.elim (fun s ↦ (q (.inl s) : ℂ)) (fun _ ↦ ζ)))
          ((q (.inr (.inl ())) : ℂ) + q (.inr (.inr ())) * Complex.I)).im) q₀ := by
  intro q₀
  obtain ⟨hre, him⟩ := hf.complexification_re_im hF hFr
  obtain ⟨hk_re, hk_im⟩ := hF.isNashAt_iteratedDeriv_sumElim_re_im hre him k
  let ι : (σ ⊕ (Unit ⊕ Unit) → ℝ) → ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ) := fun q ↦
    Sum.elim (Sum.elim (fun s ↦ q (.inl s)) (fun _ ↦ q (.inr (.inl ()))))
      (Sum.elim (fun _ ↦ 0) (fun _ ↦ q (.inr (.inr ()))))
  have hι_nash : ∀ j, IsNashAt (fun q ↦ ι q j) q₀ := by
    rintro ((s | ⟨⟩) | (_ | ⟨⟩))
    · exact isNashAt_apply (Sum.inl s)
    · exact isNashAt_apply (Sum.inr (Sum.inl ()))
    · exact isNashAt_const 0
    · exact isNashAt_apply (Sum.inr (Sum.inr ()))
  have hι₀ : ι q₀ = complexToRealPi (σ ⊕ Unit)
      (fun j ↦ ((Sum.elim x₀ (fun _ ↦ t₀) : σ ⊕ Unit → ℝ) j : ℂ)) := by
    ext ((s | ⟨⟩) | (s | ⟨⟩)) <;> simp [ι, q₀]
  have hsymm (q : σ ⊕ (Unit ⊕ Unit) → ℝ) :
      (complexToRealPi (σ ⊕ Unit)).symm (ι q) =
        Sum.elim (fun s ↦ (q (.inl s) : ℂ))
          (fun _ ↦ (q (.inr (.inl ())) : ℂ) + q (.inr (.inr ())) * Complex.I) := by
    ext (s | ⟨⟩) <;> simp [ι]
  rw [← hι₀] at hk_re hk_im
  refine ⟨(hk_re.comp hι_nash).congr ?_, (hk_im.comp hι_nash).congr ?_⟩ <;>
    exact .of_forall fun q ↦ by simp [Function.comp_apply, hsymm, ι]

/-- For a Nash germ `f` on `σ ⊕ Unit → ℝ` at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, a holomorphic
extension `F` agreeing with `f` near `p₀`, a bound `N`, and any complex neighborhood `W` of
`fun j ↦ (p₀ j : ℂ)`, there exist a radius `R > 0` and a domain `U_D` such that on the polydisc
`Metric.ball x₀ R ×ˢ Metric.ball (t₀ : ℂ) R`, points lie in `W`, their real coordinate encodings
lie in `U_D`, and all vertical derivatives `∂_w^r F` (`r < N`) have semialgebraic real and
imaginary parts on `U_D`. -/
theorem IsNashAt.exists_isSemialgebraicOn_complexification_iteratedDeriv_sumElim
    {σ : Type*} [Fintype σ] {f : (σ ⊕ Unit → ℝ) → ℝ} {x₀ : σ → ℝ} {t₀ : ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀))) {F : (σ ⊕ Unit → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F (fun j ↦ ((Sum.elim x₀ (fun _ ↦ t₀) : σ ⊕ Unit → ℝ) j : ℂ)))
    (hFr : ∀ᶠ y in 𝓝 (Sum.elim x₀ (fun _ ↦ t₀)), F (fun j ↦ (y j : ℂ)) = f y)
    (N : ℕ) {W : Set (σ ⊕ Unit → ℂ)}
    (hW : W ∈ 𝓝 (fun j ↦ ((Sum.elim x₀ (fun _ ↦ t₀) : σ ⊕ Unit → ℝ) j : ℂ))) :
    ∃ (U_D : Set (σ ⊕ (Unit ⊕ Unit) → ℝ)) (R : ℝ), 0 < R ∧
      (∀ x ∈ Metric.ball x₀ R, ∀ w ∈ Metric.ball (t₀ : ℂ) R,
        Sum.elim (fun s ↦ (x s : ℂ)) (fun _ : Unit ↦ w) ∈ W) ∧
      (∀ x ∈ Metric.ball x₀ R, ∀ y : Unit ⊕ Unit → ℝ,
        ((y (.inl ()) : ℂ) + y (.inr ()) * Complex.I) ∈ Metric.ball (t₀ : ℂ) R →
        Sum.elim x y ∈ U_D) ∧
      ∀ r : Fin N,
        IsSemialgebraicOn (fun (q : σ ⊕ (Unit ⊕ Unit) → ℝ) (_ : Unit) ↦
          (iteratedDeriv (r : ℕ)
            (fun ζ ↦ F (Sum.elim (fun s ↦ (q (.inl s) : ℂ)) (fun _ ↦ ζ)))
            ((q (.inr (.inl ())) : ℂ) + q (.inr (.inr ())) * Complex.I)).re) U_D ∧
        IsSemialgebraicOn (fun (q : σ ⊕ (Unit ⊕ Unit) → ℝ) (_ : Unit) ↦
          (iteratedDeriv (r : ℕ)
            (fun ζ ↦ F (Sum.elim (fun s ↦ (q (.inl s) : ℂ)) (fun _ ↦ ζ)))
            ((q (.inr (.inl ())) : ℂ) + q (.inr (.inr ())) * Complex.I)).im) U_D := by
  let q₀ : σ ⊕ (Unit ⊕ Unit) → ℝ := Sum.elim x₀ (Sum.elim (fun _ ↦ t₀) (fun _ ↦ 0))
  let D_re (r : Fin N) (q : σ ⊕ (Unit ⊕ Unit) → ℝ) : ℝ :=
    (iteratedDeriv (r : ℕ) (fun ζ ↦ F (Sum.elim (fun s ↦ (q (.inl s) : ℂ)) (fun _ ↦ ζ)))
      ((q (.inr (.inl ())) : ℂ) + q (.inr (.inr ())) * Complex.I)).re
  let D_im (r : Fin N) (q : σ ⊕ (Unit ⊕ Unit) → ℝ) : ℝ :=
    (iteratedDeriv (r : ℕ) (fun ζ ↦ F (Sum.elim (fun s ↦ (q (.inl s) : ℂ)) (fun _ ↦ ζ)))
      ((q (.inr (.inl ())) : ℂ) + q (.inr (.inr ())) * Complex.I)).im
  have hDnash : ∀ s : Fin N ⊕ Fin N, IsNashAt (Sum.elim D_re D_im s) q₀ := by
    rintro (r | r)
    · exact (hf.complexification_iteratedDeriv_sumElim_re_im hF hFr r).1
    · exact (hf.complexification_iteratedDeriv_sumElim_re_im hF hFr r).2
  obtain ⟨U_D, hUD_open, hq₀_UD, -, hUD_semi⟩ :=
    exists_isSemialgebraicOn_of_forall_isNashAt hDnash
  obtain ⟨R₂, hR₂, hballD⟩ := Metric.mem_nhds_iff.1 (hUD_open.mem_nhds hq₀_UD)
  obtain ⟨R₁, hR₁, hballW⟩ := Metric.mem_nhds_iff.1 hW
  let R := min R₁ (R₂ / 2)
  have hR : 0 < R := lt_min hR₁ (half_pos hR₂)
  refine ⟨U_D, R, hR, fun x hx w hw ↦ hballW ?_, fun x hx y hy ↦ hballD ?_,
    fun r ↦ ⟨hUD_semi (.inl r), hUD_semi (.inr r)⟩⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hR₁]
    rintro (s | ⟨⟩)
    · simpa [dist_eq_norm, ← Complex.ofReal_sub] using
        ((dist_pi_lt_iff hR).1 (Metric.mem_ball.1 hx) s).trans_le (min_le_left _ _)
    · exact (Metric.mem_ball.1 hw).trans_le (min_le_left _ _)
  · have hlt : R < R₂ := (min_le_right R₁ (R₂ / 2)).trans_lt (half_lt_self hR₂)
    rw [Metric.mem_ball, dist_pi_lt_iff hR₂]
    rintro (s | (⟨⟩ | ⟨⟩))
    · exact ((dist_pi_lt_iff hR).1 (Metric.mem_ball.1 hx) s).trans hlt
    · have hre : |y (.inl ()) - t₀| ≤
          ‖((y (.inl ()) : ℂ) + y (.inr ()) * Complex.I) - (t₀ : ℂ)‖ := by
        simpa using
          Complex.abs_re_le_norm (((y (.inl ()) : ℂ) + y (.inr ()) * Complex.I) - (t₀ : ℂ))
      simpa [q₀, Real.dist_eq] using hre.trans_lt ((mem_ball_iff_norm.1 hy).trans hlt)
    · have him : |y (.inr ())| ≤
          ‖((y (.inl ()) : ℂ) + y (.inr ()) * Complex.I) - (t₀ : ℂ)‖ := by
        simpa using
          Complex.abs_im_le_norm (((y (.inl ()) : ℂ) + y (.inr ()) * Complex.I) - (t₀ : ℂ))
      simpa [q₀, Real.dist_eq] using him.trans_lt ((mem_ball_iff_norm.1 hy).trans hlt)

end TauCeti
