/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import TauCeti.Analysis.Analytic.Complexification.Basic
public import TauCeti.Analysis.Complex.Euclidean.Space
import TauCeti.Analysis.Analytic.Polynomial
import TauCeti.Order.Filter.Germ.Complex

/-!
# Realification of holomorphic algebraic germs

The real and imaginary parts of a holomorphic function satisfying a nonzero complex
polynomial relation are Nash in the doubled real coordinates. In particular a holomorphic
extension of a Nash germ has Nash real and imaginary parts. This is the algebraic
realification needed to use holomorphic root clusters in real Nash geometry.

The coordinates are those of `TauCeti.complexToRealPi`: the first block gives the real
parts and the second block the imaginary parts. The polynomial relation extends from the
real locus by holomorphic uniqueness. Algebraic descent gives separate real polynomial
relations for the two components, including on the singular locus of the original relation.

## Main declarations

* `AnalyticAt.isNashAt_re_im_of_polynomial_relation`: realification of a holomorphic
  algebraic germ, at any complex point.
* `TauCeti.IsNashAt.complexification_re_im`: Nashness of the components of any holomorphic
  extension of a real Nash germ.
* `TauCeti.IsNashAt.exists_complexification`: a conjugation-invariant holomorphic extension
  with semialgebraic domain and graph, inside any prescribed neighborhood.

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

end TauCeti
