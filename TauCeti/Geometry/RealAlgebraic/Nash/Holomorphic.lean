/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Complexification
import TauCeti.Geometry.RealAlgebraic.Nash.Derivative

/-!
# Holomorphic germs with Nash real and imaginary parts

A complex-valued function `F : (τ → ℂ) → ℂ` on a finite-dimensional complex coordinate space is
*holomorphic-Nash* at `z₀` (`TauCeti.IsHolomorphicNashAt`) when it is complex analytic at `z₀` and
its real and imaginary parts in `TauCeti.complexToRealPi` coordinates are real Nash germs at
`TauCeti.complexToRealPi τ z₀`.

Every holomorphic algebraic germ, and in particular every holomorphic extension of a real Nash germ,
is holomorphic-Nash (`AnalyticAt.isHolomorphicNashAt_of_polynomial_relation`,
`TauCeti.IsNashAt.exists_isHolomorphicNashAt`). Conversely, a holomorphic-Nash germ taking real
values along the real locus restricts to a real Nash germ
(`TauCeti.IsHolomorphicNashAt.isNashAt_of_eventually_real`). Together with the local semialgebraic
graph criteria and closure under ring operations, composition, exact analytic division, and
differentiation, this provides the complex-analytic workspace used in Nash geometry (for instance,
for the Nash Weierstrass preparation and division theorems).

## Main declarations

* `TauCeti.IsHolomorphicNashAt`: complex analytic germs with Nash real and imaginary parts in
  `TauCeti.complexToRealPi` coordinates.
* `TauCeti.IsHolomorphicNashAt.add`, `TauCeti.IsHolomorphicNashAt.mul`,
  `TauCeti.IsHolomorphicNashAt.comp`, `TauCeti.IsHolomorphicNashAt.inv`,
  `TauCeti.IsHolomorphicNashAt.of_mul_eventuallyEq`: closure under ring operations, composition,
  inverses, and exact analytic division.
* `TauCeti.isHolomorphicNashAt_iff_exists_isSemialgebraicOn`,
  `TauCeti.forall_isHolomorphicNashAt_apply_iff_exists_isSemialgebraicOn`: local semialgebraic graph
  characterizations in doubled real coordinates.
* `TauCeti.IsNashAt.exists_isHolomorphicNashAt`,
  `TauCeti.IsHolomorphicNashAt.isNashAt_of_eventually_real`: passage between real Nash germs and
  holomorphic-Nash extensions.
* `TauCeti.IsHolomorphicNashAt.fderiv_apply`,
  `TauCeti.IsHolomorphicNashAt.iteratedDeriv_vertical`: closure under complex directional
  differentiation and iterated vertical slice derivatives.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
-/

public section

open Filter Metric Polynomial Topology

namespace TauCeti

variable {τ : Type*} [Fintype τ] {F G : (τ → ℂ) → ℂ} {z₀ : τ → ℂ}

/-- A complex-valued function `F` on `τ → ℂ` is *holomorphic-Nash* at `z₀` when it is complex
analytic at `z₀` and its real and imaginary parts in `TauCeti.complexToRealPi` coordinates are real
Nash germs at `TauCeti.complexToRealPi τ z₀`. -/
structure IsHolomorphicNashAt (F : (τ → ℂ) → ℂ) (z₀ : τ → ℂ) : Prop where
  /-- A holomorphic-Nash germ is complex analytic at `z₀`. -/
  analyticAt : AnalyticAt ℂ F z₀
  /-- The real part of `F` in `TauCeti.complexToRealPi` coordinates is a real Nash germ. -/
  re : IsNashAt (fun a ↦ (F ((complexToRealPi τ).symm a)).re) (complexToRealPi τ z₀)
  /-- The imaginary part of `F` in `TauCeti.complexToRealPi` coordinates is a real Nash germ. -/
  im : IsNashAt (fun a ↦ (F ((complexToRealPi τ).symm a)).im) (complexToRealPi τ z₀)

/-- Unfolding `TauCeti.IsHolomorphicNashAt`. -/
theorem isHolomorphicNashAt_iff :
    IsHolomorphicNashAt F z₀ ↔
      AnalyticAt ℂ F z₀ ∧
        IsNashAt (fun a ↦ (F ((complexToRealPi τ).symm a)).re) (complexToRealPi τ z₀) ∧
        IsNashAt (fun a ↦ (F ((complexToRealPi τ).symm a)).im) (complexToRealPi τ z₀) :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Being holomorphic-Nash at `z₀` depends only on the germ at `z₀`. -/
theorem IsHolomorphicNashAt.congr (hF : IsHolomorphicNashAt F z₀) (h : F =ᶠ[𝓝 z₀] G) :
    IsHolomorphicNashAt G z₀ := by
  let e := complexToRealPi τ
  have he : Tendsto e.symm (𝓝 (e z₀)) (𝓝 z₀) := by
    simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e z₀)
  exact ⟨hF.analyticAt.congr h,
    hF.re.congr ((he.eventually h).mono fun _ ha ↦ congrArg Complex.re ha),
    hF.im.congr ((he.eventually h).mono fun _ ha ↦ congrArg Complex.im ha)⟩

/-- Functions with the same germ at `z₀` are holomorphic-Nash at `z₀` together. -/
theorem _root_.Filter.EventuallyEq.isHolomorphicNashAt_iff (h : F =ᶠ[𝓝 z₀] G) :
    IsHolomorphicNashAt F z₀ ↔ IsHolomorphicNashAt G z₀ :=
  ⟨fun hF ↦ hF.congr h, fun hG ↦ hG.congr h.symm⟩

/-- A holomorphic-Nash germ at `z₀` is holomorphic-Nash at every nearby point. -/
theorem IsHolomorphicNashAt.eventually_isHolomorphicNashAt (hF : IsHolomorphicNashAt F z₀) :
    ∀ᶠ z in 𝓝 z₀, IsHolomorphicNashAt F z := by
  let e := complexToRealPi τ
  have he : Tendsto e (𝓝 z₀) (𝓝 (e z₀)) := e.continuous.tendsto z₀
  filter_upwards [hF.analyticAt.eventually_analyticAt,
    he.eventually hF.re.eventually_isNashAt,
    he.eventually hF.im.eventually_isNashAt] with z hz hre him
  exact ⟨hz, hre, him⟩

/-! ### Constants, coordinates, ring operations, and polynomials -/

/-- Constant functions are holomorphic-Nash germs. -/
theorem isHolomorphicNashAt_const (c : ℂ) :
    IsHolomorphicNashAt (fun _ : τ → ℂ ↦ c) z₀ :=
  ⟨analyticAt_const, isNashAt_const c.re, isNashAt_const c.im⟩

/-- Coordinate functions are holomorphic-Nash germs. -/
theorem isHolomorphicNashAt_apply (i : τ) :
    IsHolomorphicNashAt (fun z : τ → ℂ ↦ z i) z₀ :=
  ⟨(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ ↦ ℂ) i).analyticAt z₀,
    by simpa using isNashAt_apply (x := complexToRealPi τ z₀) (Sum.inl i),
    by simpa using isNashAt_apply (x := complexToRealPi τ z₀) (Sum.inr i)⟩

/-- The sum of two holomorphic-Nash germs is holomorphic-Nash. -/
@[to_fun]
theorem IsHolomorphicNashAt.add (hF : IsHolomorphicNashAt F z₀) (hG : IsHolomorphicNashAt G z₀) :
    IsHolomorphicNashAt (F + G) z₀ :=
  ⟨hF.analyticAt.add hG.analyticAt,
    (hF.re.add hG.re).congr (.of_forall fun _ ↦ rfl),
    (hF.im.add hG.im).congr (.of_forall fun _ ↦ rfl)⟩

/-- The negation of a holomorphic-Nash germ is holomorphic-Nash. -/
@[to_fun]
theorem IsHolomorphicNashAt.neg (hF : IsHolomorphicNashAt F z₀) :
    IsHolomorphicNashAt (-F) z₀ :=
  ⟨hF.analyticAt.neg,
    hF.re.neg.congr (.of_forall fun _ ↦ rfl),
    hF.im.neg.congr (.of_forall fun _ ↦ rfl)⟩

/-- The difference of two holomorphic-Nash germs is holomorphic-Nash. -/
@[to_fun]
theorem IsHolomorphicNashAt.sub (hF : IsHolomorphicNashAt F z₀) (hG : IsHolomorphicNashAt G z₀) :
    IsHolomorphicNashAt (F - G) z₀ := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

/-- The product of two holomorphic-Nash germs is holomorphic-Nash. -/
@[to_fun]
theorem IsHolomorphicNashAt.mul (hF : IsHolomorphicNashAt F z₀) (hG : IsHolomorphicNashAt G z₀) :
    IsHolomorphicNashAt (F * G) z₀ :=
  ⟨hF.analyticAt.mul hG.analyticAt,
    ((hF.re.mul hG.re).sub (hF.im.mul hG.im)).congr (.of_forall fun _ ↦ (Complex.mul_re _ _).symm),
    ((hF.re.mul hG.im).add (hF.im.mul hG.re)).congr (.of_forall fun _ ↦ (Complex.mul_im _ _).symm)⟩

/-- Powers of a holomorphic-Nash germ are holomorphic-Nash. -/
@[to_fun]
theorem IsHolomorphicNashAt.pow (hF : IsHolomorphicNashAt F z₀) (n : ℕ) :
    IsHolomorphicNashAt (F ^ n) z₀ := by
  induction n with
  | zero => rw [pow_zero]; exact isHolomorphicNashAt_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hF

/-- Finite sums of holomorphic-Nash germs are holomorphic-Nash. -/
@[to_fun]
theorem _root_.Finset.isHolomorphicNashAt_sum {ι : Type*} {F : ι → (τ → ℂ) → ℂ} (N : Finset ι)
    (h : ∀ i ∈ N, IsHolomorphicNashAt (F i) z₀) :
    IsHolomorphicNashAt (∑ i ∈ N, F i) z₀ :=
  Finset.sum_induction _ (IsHolomorphicNashAt · z₀) (fun _ _ ↦ .add)
    (isHolomorphicNashAt_const 0) h

/-- Finite products of holomorphic-Nash germs are holomorphic-Nash. -/
@[to_fun]
theorem _root_.Finset.isHolomorphicNashAt_prod {ι : Type*} {F : ι → (τ → ℂ) → ℂ} (N : Finset ι)
    (h : ∀ i ∈ N, IsHolomorphicNashAt (F i) z₀) :
    IsHolomorphicNashAt (∏ i ∈ N, F i) z₀ :=
  Finset.prod_induction _ (IsHolomorphicNashAt · z₀) (fun _ _ ↦ .mul)
    (isHolomorphicNashAt_const 1) h

/-- Complex multivariate polynomial functions are holomorphic-Nash germs at every point. -/
theorem _root_.MvPolynomial.isHolomorphicNashAt_eval (p : MvPolynomial τ ℂ) :
    IsHolomorphicNashAt (fun z ↦ MvPolynomial.eval z p) z₀ := by
  apply p.induction_on (fun c ↦ ?_) (fun p q hp hq ↦ ?_) fun p i hp ↦ ?_
  · simpa only [MvPolynomial.eval_C] using isHolomorphicNashAt_const c
  · simpa only [map_add] using hp.fun_add hq
  · simpa only [map_mul, MvPolynomial.eval_X] using hp.fun_mul (isHolomorphicNashAt_apply i)

/-! ### Composition, exact division, and inverses -/

/-- Composing a holomorphic-Nash germ with a holomorphic map whose coordinates are holomorphic-Nash
produces a holomorphic-Nash germ. -/
theorem IsHolomorphicNashAt.comp {σ : Type*} [Fintype σ]
    {F : (τ → ℂ) → ℂ} {Φ : (σ → ℂ) → (τ → ℂ)} {z₀ : σ → ℂ}
    (hF : IsHolomorphicNashAt F (Φ z₀)) (hΦ : ∀ j, IsHolomorphicNashAt (fun z ↦ Φ z j) z₀) :
    IsHolomorphicNashAt (F ∘ Φ) z₀ := by
  let eσ := complexToRealPi σ
  let eτ := complexToRealPi τ
  have hΦ_an : AnalyticAt ℂ Φ z₀ := AnalyticAt.pi fun j ↦ (hΦ j).analyticAt
  have hcoords : ∀ k : τ ⊕ τ, IsNashAt (fun a ↦ eτ (Φ (eσ.symm a)) k) (eσ z₀) := by
    rintro (j | j)
    · simpa [eσ, eτ] using (hΦ j).re
    · simpa [eσ, eτ] using (hΦ j).im
  have heq (a : σ ⊕ σ → ℝ) : eτ.symm (eτ (Φ (eσ.symm a))) = Φ (eσ.symm a) :=
    eτ.symm_apply_apply _
  have hre0 : IsNashAt (fun b ↦ (F (eτ.symm b)).re) (eτ (Φ (eσ.symm (eσ z₀)))) := by
    simpa only [eσ.symm_apply_apply] using hF.re
  have him0 : IsNashAt (fun b ↦ (F (eτ.symm b)).im) (eτ (Φ (eσ.symm (eσ z₀)))) := by
    simpa only [eσ.symm_apply_apply] using hF.im
  have hre := hre0.comp hcoords
  have him := him0.comp hcoords
  exact ⟨hF.analyticAt.comp hΦ_an,
    hre.congr (.of_forall fun a ↦ congrArg (fun w ↦ (F w).re) (heq a)),
    him.congr (.of_forall fun a ↦ congrArg (fun w ↦ (F w).im) (heq a))⟩

/-- **Exact analytic division of holomorphic-Nash germs.** If `P` and `H` are holomorphic-Nash at
`z₀`, `Q` is complex analytic at `z₀`, `P` does not vanish as a germ at `z₀`, and
`P * Q =ᶠ[𝓝 z₀] H`, then `Q` is holomorphic-Nash at `z₀`: multiplying by `star P` reduces to real
exact division by `|P|²`. -/
theorem IsHolomorphicNashAt.of_mul_eventuallyEq {P Q H : (τ → ℂ) → ℂ}
    (hP : IsHolomorphicNashAt P z₀) (hH : IsHolomorphicNashAt H z₀)
    (hQ : AnalyticAt ℂ Q z₀) (hP0 : ¬ P =ᶠ[𝓝 z₀] (0 : (τ → ℂ) → ℂ))
    (hmul : P * Q =ᶠ[𝓝 z₀] H) :
    IsHolomorphicNashAt Q z₀ := by
  let e := complexToRealPi τ
  let nP : (τ ⊕ τ → ℝ) → ℝ := fun a ↦ (P (e.symm a)).re ^ 2 + (P (e.symm a)).im ^ 2
  have hnP : IsNashAt nP (e z₀) := (hP.re.pow 2).add (hP.im.pow 2)
  have hnP0 : ¬ nP =ᶠ[𝓝 (e z₀)] (0 : (τ ⊕ τ → ℝ) → ℝ) := fun h0 ↦
    hP0 <| (e.continuous.tendsto z₀).eventually h0 |>.mono fun z hz ↦
      Complex.normSq_eq_zero.1
        (by simpa [nP, e.symm_apply_apply, Complex.normSq_apply, sq] using hz)
  have hQ_real : AnalyticAt ℝ (fun a ↦ Q (e.symm a)) (e z₀) :=
    (hQ.restrictScalars (𝕜 := ℝ)).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply z₀)
  have he : Tendsto e.symm (𝓝 (e z₀)) (𝓝 z₀) := by
    simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e z₀)
  have hmul_star : ∀ᶠ a in 𝓝 (e z₀),
      (nP a : ℂ) * Q (e.symm a) = star (P (e.symm a)) * H (e.symm a) := by
    filter_upwards [he.eventually hmul] with a ha
    have hnorm : star (P (e.symm a)) * P (e.symm a) = (nP a : ℂ) := by
      rw [Complex.ext_iff]
      simp [nP, sq]
      ring
    calc (nP a : ℂ) * Q (e.symm a)
        = star (P (e.symm a)) * (P (e.symm a) * Q (e.symm a)) := by rw [← mul_assoc, hnorm]
      _ = star (P (e.symm a)) * H (e.symm a) := by rw [← Pi.mul_apply, ha]
  refine ⟨hQ, ?_, ?_⟩
  · refine hnP.of_mul_eventuallyEq ((hP.re.mul hH.re).add (hP.im.mul hH.im))
      ((Complex.reCLM.analyticAt _).comp hQ_real) hnP0 ?_
    exact hmul_star.mono fun a ha ↦ by simpa [Complex.mul_re] using congrArg Complex.re ha
  · refine hnP.of_mul_eventuallyEq ((hP.re.mul hH.im).sub (hP.im.mul hH.re))
      ((Complex.imCLM.analyticAt _).comp hQ_real) hnP0 ?_
    exact hmul_star.mono fun a ha ↦ by
      simpa [Complex.mul_im, sub_eq_add_neg] using congrArg Complex.im ha

/-- The inverse of a holomorphic-Nash germ nonvanishing at `z₀` is holomorphic-Nash at `z₀`. -/
@[to_fun]
theorem IsHolomorphicNashAt.inv (hF : IsHolomorphicNashAt F z₀) (h0 : F z₀ ≠ 0) :
    IsHolomorphicNashAt F⁻¹ z₀ := by
  have hF0 : ¬ F =ᶠ[𝓝 z₀] (0 : (τ → ℂ) → ℂ) := fun h ↦ h0 h.self_of_nhds
  refine hF.of_mul_eventuallyEq (isHolomorphicNashAt_const 1) (hF.analyticAt.inv h0) hF0 ?_
  filter_upwards [hF.analyticAt.continuousAt.eventually_ne h0] with z hz
  exact mul_inv_cancel₀ hz

/-- The quotient of holomorphic-Nash germs is holomorphic-Nash where the denominator does not
vanish. -/
@[to_fun]
theorem IsHolomorphicNashAt.div (hF : IsHolomorphicNashAt F z₀) (hG : IsHolomorphicNashAt G z₀)
    (h0 : G z₀ ≠ 0) : IsHolomorphicNashAt (F / G) z₀ := by
  simpa [div_eq_mul_inv] using hF.mul (hG.inv h0)

/-! ### Polynomial relations, real Nash germs, and semialgebraic graphs -/

/-- Every holomorphic germ satisfying a nonzero complex polynomial relation is holomorphic-Nash. -/
theorem _root_.AnalyticAt.isHolomorphicNashAt_of_polynomial_relation
    (hF : AnalyticAt ℂ F z₀) (P : (MvPolynomial τ ℂ)[X]) (hP : P ≠ 0)
    (hrel : ∀ᶠ w in 𝓝 z₀, (P.map (MvPolynomial.eval w)).eval (F w) = 0) :
    IsHolomorphicNashAt F z₀ := by
  obtain ⟨hre, him⟩ := hF.isNashAt_re_im_of_polynomial_relation P hP hrel
  exact ⟨hF, hre, him⟩

/-- Any holomorphic extension of a real Nash germ at `x₀` is holomorphic-Nash at `fun j ↦ x₀ j`. -/
theorem IsNashAt.isHolomorphicNashAt_of_eventually_real {f : (τ → ℝ) → ℝ} {x₀ : τ → ℝ}
    (hf : IsNashAt f x₀) {F : (τ → ℂ) → ℂ} (hF : AnalyticAt ℂ F (fun j ↦ (x₀ j : ℂ)))
    (hFr : ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y) :
    IsHolomorphicNashAt F (fun j ↦ (x₀ j : ℂ)) := by
  obtain ⟨hre, him⟩ := hf.complexification_re_im hF hFr
  exact ⟨hF, hre, him⟩

/-- Every real Nash germ at `x₀` admits a holomorphic-Nash extension near `fun j ↦ (x₀ j : ℂ)`
agreeing with it on a real neighbourhood of `x₀`. -/
theorem IsNashAt.exists_isHolomorphicNashAt {f : (τ → ℝ) → ℝ} {x₀ : τ → ℝ}
    (hf : IsNashAt f x₀) :
    ∃ F : (τ → ℂ) → ℂ, IsHolomorphicNashAt F (fun j ↦ (x₀ j : ℂ)) ∧
      ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y := by
  obtain ⟨r, hr, F, hF, hFf, _⟩ := hf.analyticAt.exists_complexification
  have hF_an : AnalyticAt ℂ F (fun j ↦ (x₀ j : ℂ)) := hF _ (mem_ball_self hr)
  have hFf' : ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y :=
    eventually_of_mem (ball_mem_nhds x₀ hr) hFf
  exact ⟨F, hf.isHolomorphicNashAt_of_eventually_real hF_an hFf', hFf'⟩

/-- Restricting a holomorphic-Nash germ to the real locus produces a real Nash germ whenever it
takes real values `f y` near `x₀`. -/
theorem IsHolomorphicNashAt.isNashAt_of_eventually_real
    {F : (τ → ℂ) → ℂ} {f : (τ → ℝ) → ℝ} {x₀ : τ → ℝ}
    (hF : IsHolomorphicNashAt F (fun j ↦ (x₀ j : ℂ)))
    (hf : ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y) :
    IsNashAt f x₀ := by
  let e := complexToRealPi τ
  let ι : (τ → ℝ) → (τ ⊕ τ → ℝ) := fun y ↦ Sum.elim y 0
  have hι_eq (y : τ → ℝ) : e.symm (ι y) = fun j ↦ (y j : ℂ) := by
    ext j; simp [e, ι]
  have hι_z₀ : ι x₀ = e (fun j ↦ (x₀ j : ℂ)) := by
    ext (_ | _) <;> simp [e, ι]
  have hι_nash : ∀ k : τ ⊕ τ, IsNashAt (fun y ↦ ι y k) x₀ := by
    rintro (j | _)
    · exact isNashAt_apply j
    · exact isNashAt_const 0
  refine ((hι_z₀ ▸ hF.re).comp hι_nash).congr ?_
  filter_upwards [hf] with y hy
  simp [Function.comp_apply, e, hι_eq, hy]

/-- **Local semialgebraic graph criterion for holomorphic-Nash germs.** A complex function is
holomorphic-Nash at `z₀` exactly when it is complex analytic at `z₀` and its realification is
semialgebraic on some open neighbourhood of `TauCeti.complexToRealPi τ z₀`. -/
theorem isHolomorphicNashAt_iff_exists_isSemialgebraicOn :
    IsHolomorphicNashAt F z₀ ↔
      AnalyticAt ℂ F z₀ ∧ ∃ U : Set (τ ⊕ τ → ℝ), IsOpen U ∧ complexToRealPi τ z₀ ∈ U ∧
        IsSemialgebraicOn
          (fun a ↦ complexToRealPi Unit (fun _ ↦ F ((complexToRealPi τ).symm a))) U := by
  let e := complexToRealPi τ
  constructor
  · intro hF
    have hcoords : ∀ b : Unit ⊕ Unit,
        IsNashAt (fun a ↦ complexToRealPi Unit (fun _ ↦ F (e.symm a)) b) (e z₀) := by
      rintro (_ | _)
      · simpa [e] using hF.re
      · simpa [e] using hF.im
    obtain ⟨_, U, hUo, hzU, hG⟩ := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mp hcoords
    exact ⟨hF.analyticAt, U, hUo, hzU, hG⟩
  · rintro ⟨hFa, U, hUo, hzU, hG⟩
    have ha : AnalyticAt ℝ (fun a ↦ complexToRealPi Unit (fun _ ↦ F (e.symm a))) (e z₀) :=
      ((complexToRealPi Unit).analyticAt _).comp <| AnalyticAt.pi fun _ ↦
        (hFa.restrictScalars (𝕜 := ℝ)).comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply z₀)
    have hcoords := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mpr ⟨ha, U, hUo, hzU, hG⟩
    exact ⟨hFa, by simpa [e] using hcoords (.inl ()), by simpa [e] using hcoords (.inr ())⟩

/-- Finitely many holomorphic-Nash germs at `z₀` have semialgebraic realifications on one common
open semialgebraic neighbourhood of `TauCeti.complexToRealPi τ z₀`. -/
theorem exists_isSemialgebraicOn_of_forall_isHolomorphicNashAt {ι : Type*} [Finite ι]
    {H : ι → (τ → ℂ) → ℂ} (hH : ∀ k, IsHolomorphicNashAt (H k) z₀) :
    ∃ U : Set (τ ⊕ τ → ℝ), IsOpen U ∧ complexToRealPi τ z₀ ∈ U ∧ IsSemialgebraic U ∧
      ∀ k, IsSemialgebraicOn
        (fun a ↦ complexToRealPi Unit (fun _ ↦ H k ((complexToRealPi τ).symm a))) U := by
  let e := complexToRealPi τ
  have hcoords : ∀ p : ι × (Unit ⊕ Unit),
      IsNashAt (fun a ↦ complexToRealPi Unit (fun _ ↦ H p.1 (e.symm a)) p.2) (e z₀) := by
    rintro ⟨k, _ | _⟩
    · simpa [e] using (hH k).re
    · simpa [e] using (hH k).im
  obtain ⟨U, hUo, hzU, hU, hG⟩ := exists_isSemialgebraicOn_of_forall_isNashAt hcoords
  exact ⟨U, hUo, hzU, hU, fun k ↦ isSemialgebraicOn_pi_iff.mpr ⟨hU, fun b ↦ hG (k, b)⟩⟩

/-- **Local semialgebraic graph criterion for holomorphic-Nash maps.** The coordinates of a map
between finite-dimensional complex coordinate spaces are holomorphic-Nash at `z₀` exactly when the
map is complex analytic at `z₀` and its realification is semialgebraic on some open neighbourhood
of `TauCeti.complexToRealPi τ z₀`. -/
theorem forall_isHolomorphicNashAt_apply_iff_exists_isSemialgebraicOn {σ : Type*} [Fintype σ]
    {Φ : (τ → ℂ) → (σ → ℂ)} :
    (∀ i, IsHolomorphicNashAt (fun z ↦ Φ z i) z₀) ↔
      AnalyticAt ℂ Φ z₀ ∧ ∃ U : Set (τ ⊕ τ → ℝ), IsOpen U ∧ complexToRealPi τ z₀ ∈ U ∧
        IsSemialgebraicOn
          (fun a ↦ complexToRealPi σ (Φ ((complexToRealPi τ).symm a))) U := by
  let eτ := complexToRealPi τ
  let eσ := complexToRealPi σ
  constructor
  · intro hΦ
    have hcoords : ∀ k : σ ⊕ σ, IsNashAt (fun a ↦ eσ (Φ (eτ.symm a)) k) (eτ z₀) := by
      rintro (i | i)
      · simpa [eτ, eσ] using (hΦ i).re
      · simpa [eτ, eσ] using (hΦ i).im
    obtain ⟨_, U, hUo, hzU, hG⟩ := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mp hcoords
    exact ⟨AnalyticAt.pi fun i ↦ (hΦ i).analyticAt, U, hUo, hzU, hG⟩
  · rintro ⟨hΦa, U, hUo, hzU, hG⟩ i
    have ha : AnalyticAt ℝ (fun a ↦ eσ (Φ (eτ.symm a))) (eτ z₀) :=
      (eσ.analyticAt _).comp <|
        (hΦa.restrictScalars (𝕜 := ℝ)).comp_of_eq (eτ.symm.analyticAt _) (eτ.symm_apply_apply z₀)
    have hcoords := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mpr ⟨ha, U, hUo, hzU, hG⟩
    exact ⟨analyticAt_pi_iff.mp hΦa i,
      by simpa [eτ, eσ] using hcoords (.inl i),
      by simpa [eτ, eσ] using hcoords (.inr i)⟩

/-! ### Differentiation -/

/-- Complex directional differentiation in any fixed direction `v` preserves
`TauCeti.IsHolomorphicNashAt`. -/
theorem IsHolomorphicNashAt.fderiv_apply (hF : IsHolomorphicNashAt F z₀) (v : τ → ℂ) :
    IsHolomorphicNashAt (fun z ↦ fderiv ℂ F z v) z₀ := by
  let e := complexToRealPi τ
  have hF'_an : AnalyticAt ℂ (fun z ↦ fderiv ℂ F z v) z₀ :=
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hF.analyticAt.fderiv
  have he : Tendsto e.symm (𝓝 (e z₀)) (𝓝 z₀) := by
    simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e z₀)
  have hfderiv_eq : ∀ᶠ a in 𝓝 (e z₀),
      fderiv ℝ (fun b ↦ (F (e.symm b)).re) a (e v) = (fderiv ℂ F (e.symm a) v).re ∧
        fderiv ℝ (fun b ↦ (F (e.symm b)).im) a (e v) = (fderiv ℂ F (e.symm a) v).im := by
    filter_upwards [he.eventually hF.analyticAt.eventually_analyticAt] with a ha
    have hF_diff : HasFDerivAt (fun b ↦ F (e.symm b))
        (((fderiv ℂ F (e.symm a)).restrictScalars ℝ).comp (e.symm : _ →L[ℝ] _)) a :=
      (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a e.symm.hasFDerivAt
    have hre := (Complex.reCLM.hasFDerivAt.comp a hF_diff).fderiv
    have him := (Complex.imCLM.hasFDerivAt.comp a hF_diff).fderiv
    exact ⟨by simpa [Function.comp_def, e.symm_apply_apply] using congrArg (fun L ↦ L (e v)) hre,
      by simpa [Function.comp_def, e.symm_apply_apply] using congrArg (fun L ↦ L (e v)) him⟩
  exact ⟨hF'_an,
    (hF.re.fderiv_apply (e v)).congr (hfderiv_eq.mono fun _ h ↦ h.1),
    (hF.im.fderiv_apply (e v)).congr (hfderiv_eq.mono fun _ h ↦ h.2)⟩

private theorem sumElim_comp_inl_inr {σ α : Type*} (z : σ ⊕ Unit → α) :
    Sum.elim (z ∘ Sum.inl) (fun _ : Unit ↦ z (.inr ())) = z := by
  ext (_ | ⟨⟩) <;> rfl

/-- Every iterated vertical slice derivative of a holomorphic-Nash germ on `σ ⊕ Unit → ℂ` is
holomorphic-Nash. -/
theorem IsHolomorphicNashAt.iteratedDeriv_vertical {σ : Type*} [Fintype σ]
    {F : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ ⊕ Unit → ℂ} (hF : IsHolomorphicNashAt F z₀) :
    ∀ n : ℕ, IsHolomorphicNashAt
      (fun z ↦ iteratedDeriv n (fun w ↦ F (Sum.elim (z ∘ Sum.inl) (fun _ ↦ w))) (z (.inr ()))) z₀
  | 0 => hF.congr (.of_forall fun z ↦ by simp [sumElim_comp_inl_inr])
  | n + 1 => by
    let F' : (σ ⊕ Unit → ℂ) → ℂ := fun z ↦ fderiv ℂ F z (Sum.elim 0 1)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_analyticAt ℂ F) z₀ hF.analyticAt
    refine ((hF.fderiv_apply (Sum.elim 0 1)).iteratedDeriv_vertical n).congr ?_
    filter_upwards [ball_mem_nhds z₀ (half_pos hr)] with z hz
    have hz_lt : dist z z₀ < r := (mem_ball.1 hz).trans (half_lt_self hr)
    have hcont : Continuous fun w : ℂ ↦ Sum.elim (z ∘ Sum.inl) (fun _ : Unit ↦ w) :=
      continuous_pi (Sum.rec (fun _ ↦ continuous_const) (fun _ ↦ continuous_id))
    have hw_open : {w : ℂ | Sum.elim (z ∘ Sum.inl) (fun _ ↦ w) ∈ ball z₀ r} ∈ 𝓝 (z (.inr ())) :=
      (hcont.tendsto (z (.inr ()))).eventually
        (isOpen_ball.mem_nhds ((sumElim_comp_inl_inr z).symm ▸ mem_ball.2 hz_lt))
    have hderiv_eq : (fun w ↦ F' (Sum.elim (z ∘ Sum.inl) (fun _ ↦ w))) =ᶠ[𝓝 (z (.inr ()))]
        deriv (fun w ↦ F (Sum.elim (z ∘ Sum.inl) (fun _ ↦ w))) := by
      filter_upwards [hw_open] with w hw
      have hγ : HasDerivAt (fun w' : ℂ ↦ Sum.elim (z ∘ Sum.inl) (fun _ : Unit ↦ w'))
          (Sum.elim 0 1) w :=
        hasDerivAt_pi.2 fun k ↦ by
          rcases k with s | ⟨⟩
          · exact hasDerivAt_const w (z (Sum.inl s))
          · exact hasDerivAt_id w
      exact (((hball hw).differentiableAt.hasFDerivAt.comp_hasDerivAt w hγ).deriv).symm
    rw [iteratedDeriv_succ']
    exact hderiv_eq.iteratedDeriv_eq n

end TauCeti
