/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Geometry.RealAlgebraic.Nash.Comp
import TauCeti.Geometry.RealAlgebraic.Nash.Complexification
import TauCeti.Geometry.RealAlgebraic.Nash.Derivative
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex

/-!
# The Nash Weierstrass preparation and division theorems

Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite,
and suppose that the vertical slice `t ↦ f (Sum.elim x₀ (fun _ ↦ t))` vanishes to finite order `d`
at `t₀`. By the real analytic Weierstrass preparation theorem
(`AnalyticAt.exists_weierstrassPreparation_real`), near `p₀` one can write
`f p = P_{p ∘ Sum.inl} (p (.inr ()) - t₀) * u p`, where `P_x` is the monic polynomial
`TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)` of degree `d` with real analytic lower
coefficients `c i` vanishing at `x₀`, and `u` is real analytic and nonvanishing at `p₀`. This file
proves that the coefficients `c i` and the unit `u` are Nash germs, and proves the corresponding
Nash Weierstrass division theorems.

## Mathematical overview

A single polynomial relation `Q(x, t, f(x, t)) = 0` for `f` does not directly cut out the
Weierstrass polynomial `P_x`: conjugate algebraic branches of `Q` may also vanish at `(x₀, t₀)`,
contributing extraneous factors to `Q(x, t, 0)` that are invisible to the analytic germ `f`.
Separating the roots belonging to the chosen analytic branch requires working in the complex domain
and isolating the local root cluster on a disk:

1. **Holomorphic-Nash extension.** Complexifying `f`, `c i`, and `u` gives a complex Weierstrass
   factorization `F (z, w) = P_z (w - w₀) * U (z, w)` near `(z₀, w₀)` in which `F` has Nash real
   and imaginary parts in `TauCeti.complexToRealPi` coordinates
   (`TauCeti.IsNashAt.complexification_re_im`), as do all iterated vertical derivatives of `F`
   (`TauCeti.IsNashAt.fderiv_apply`).
2. **Root-cluster isolation and first-order characterization.** After translating `w₀` to `0`,
   choose a disk `ball 0 R ⊆ ℂ` on which `U (z, ·)` is nonvanishing and shrink the base
   neighbourhood `B_X` so that `‖c i z‖ ≤ (R / 4) ^ (d - i)`. By Fujiwara's root bound
   (`Polynomial.IsRoot.norm_le_two_mul`), every complex root of `P_z` lies in `ball 0 R`. Because
   `ℂ` is algebraically closed, a monic degree-`d` polynomial `monicOfCoeff a` coincides with
   `P_z` if and only if all of its roots lie in `ball 0 R` and, at every `w ∈ ball 0 R`, its Hasse
   derivatives below each order `k ≤ d` vanish simultaneously with the vertical derivatives of
   `F (z, ·)`.
3. **Elimination and exact division.** Universal quantifier elimination over the real and imaginary
   parts of `w` (`TauCeti.IsSemialgebraic.setOf_forall_sumElim`) makes the graph of `z ↦ c · z`
   semialgebraic on `B_X`, so the local Nash graph criterion upgrades each `c i` to Nash. Exact
   analytic division of Nash germs (`TauCeti.IsNashAt.of_mul_eventuallyEq`) then upgrades `U`.
   Weierstrass division is proved analogously: matching Taylor jets at every root of `P_z` inside
   `ball 0 R` characterizes the degree-`< d` remainder uniquely over `ℂ`.

## Main results

* `TauCeti.IsNashAt.of_weierstrassPreparation`, `TauCeti.IsNashAt.exists_weierstrassPreparation`:
  **Nash Weierstrass preparation.**
* `TauCeti.IsNashAt.of_weierstrassDivision_monicOfCoeff`,
  `TauCeti.IsNashAt.exists_weierstrassDivision_monicOfCoeff`,
  `TauCeti.IsNashAt.of_weierstrassDivision`,
  `TauCeti.IsNashAt.exists_weierstrassDivision`: **Nash Weierstrass division** by a Nash
  Weierstrass polynomial, and by any Nash germ whose vertical slice has finite order.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions) and Proposition 8.1.8.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser,
  2002, Section 6.1.
* S. Łojasiewicz, *Introduction to Complex Analytic Geometry*, Birkhäuser, 1991.
-/

public section

open Filter Metric Polynomial Topology

namespace TauCeti

/-! ### Polynomial characterization on a root-isolating set -/

section PolynomialCharacterization

/-- Over an algebraically closed field, two monic polynomials `monicOfCoeff a` and `monicOfCoeff c`
of degree `d` whose roots all lie in `s` agree whenever, at every `w ∈ s` and for every
`k ≤ d`, their Hasse derivatives of order `< k` vanish together. -/
private theorem eq_of_monicOfCoeff_forall_hasseDeriv_iff {K : Type*} [Field K] [IsAlgClosed K]
    {d : ℕ} {a c : Fin d → K} {s : Set K}
    (ha : ∀ w, (Polynomial.monicOfCoeff a).IsRoot w → w ∈ s)
    (hc : ∀ w, (Polynomial.monicOfCoeff c).IsRoot w → w ∈ s)
    (hderiv : ∀ w ∈ s, ∀ k : Fin (d + 1),
      (∀ j : Fin (k : ℕ), (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff a)).eval w = 0) ↔
        (∀ j : Fin (k : ℕ), (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff c)).eval w = 0)) :
    a = c := by
  let P := Polynomial.monicOfCoeff a
  let Q := Polynomial.monicOfCoeff c
  have hPm : P.Monic := Polynomial.monic_monicOfCoeff a
  have hQm : Q.Monic := Polynomial.monic_monicOfCoeff c
  have hle_iff (p : K[X]) (hp : p ≠ 0) (w : K) (n : ℕ) :
      n ≤ p.rootMultiplicity w ↔ ∀ j : Fin n, (hasseDeriv (j : ℕ) p).eval w = 0 := by
    rw [Polynomial.le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hp]
    exact ⟨fun h j ↦ h j j.2, fun h j hj ↦ h ⟨j, hj⟩⟩
  have hroots : P.roots = Q.roots := by
    classical
    ext w
    rw [Polynomial.count_roots, Polynomial.count_roots]
    by_cases hw : w ∈ s
    · have hmP : P.rootMultiplicity w ≤ d := by
        rw [← Polynomial.count_roots, ← Polynomial.natDegree_monicOfCoeff a]
        exact (Multiset.count_le_card w _).trans P.card_roots'
      have hmQ : Q.rootMultiplicity w ≤ d := by
        rw [← Polynomial.count_roots, ← Polynomial.natDegree_monicOfCoeff c]
        exact (Multiset.count_le_card w _).trans Q.card_roots'
      refine le_antisymm ?_ ?_
      · exact (hle_iff Q hQm.ne_zero w _).2
          ((hderiv w hw ⟨_, Nat.lt_succ_of_le hmP⟩).1 ((hle_iff P hPm.ne_zero w _).1 le_rfl))
      · exact (hle_iff P hPm.ne_zero w _).2
          ((hderiv w hw ⟨_, Nat.lt_succ_of_le hmQ⟩).2 ((hle_iff Q hQm.ne_zero w _).1 le_rfl))
    · rw [Polynomial.rootMultiplicity_eq_zero (mt (ha w) hw),
        Polynomial.rootMultiplicity_eq_zero (mt (hc w) hw)]
  have hPQ : P = Q := by
    rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hPm,
      (IsAlgClosed.splits Q).eq_prod_roots_of_monic hQm, hroots]
  exact (Polynomial.monicOfCoeff_inj a c).1 hPQ

/-- Over an algebraically closed field, if every root of `P = monicOfCoeff c` lies in `s`, then two
degree-`< d` polynomials `∑ i, monomial i (b i)` and `∑ i, monomial i (r i)` agree whenever their
Hasse derivatives agree up to the multiplicity of `P` at every point of `s`. -/
private theorem eq_of_sum_monomial_forall_hasseDeriv_eq {K : Type*} [Field K] [IsAlgClosed K]
    {d : ℕ} {c b r : Fin d → K} {s : Set K}
    (hc : ∀ w, (Polynomial.monicOfCoeff c).IsRoot w → w ∈ s)
    (hderiv : ∀ w ∈ s, ∀ k : Fin (d + 1),
      (∀ j : Fin (k : ℕ), (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff c)).eval w = 0) →
        ∀ j : Fin (k : ℕ),
          (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ) (b i))).eval w =
            (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ) (r i))).eval w) :
    b = r := by
  let P := Polynomial.monicOfCoeff c
  let B := ∑ i : Fin d, monomial (i : ℕ) (b i)
  let R := ∑ i : Fin d, monomial (i : ℕ) (r i)
  have hPm : P.Monic := Polynomial.monic_monicOfCoeff c
  have hBR : B - R = 0 := by
    by_contra hne
    have hle : P.roots ≤ (B - R).roots := by
      classical
      rw [Multiset.le_iff_count]
      intro w
      rw [Polynomial.count_roots, Polynomial.count_roots]
      by_cases hw : P.IsRoot w
      · have hm : P.rootMultiplicity w ≤ d := by
          rw [← Polynomial.count_roots, ← Polynomial.natDegree_monicOfCoeff c]
          exact (Multiset.count_le_card w _).trans P.card_roots'
        have hP0 : ∀ j : Fin (P.rootMultiplicity w), (hasseDeriv (j : ℕ) P).eval w = 0 :=
          fun j ↦ (Polynomial.le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hPm.ne_zero).1
            le_rfl j j.2
        have hBR0 := hderiv w (hc w hw) ⟨_, Nat.lt_succ_of_le hm⟩ hP0
        rw [Polynomial.le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hne]
        intro j hj
        rw [map_sub, eval_sub, sub_eq_zero]
        exact hBR0 ⟨j, hj⟩
      · simp [Polynomial.rootMultiplicity_eq_zero hw]
    have hdvd : P ∣ B - R := (IsAlgClosed.splits P).dvd_of_roots_le_roots hPm.ne_zero hle
    have hdeg_ge : d ≤ (B - R).natDegree := by
      simpa only [P, Polynomial.natDegree_monicOfCoeff] using
        Polynomial.natDegree_le_of_dvd hdvd hne
    have hsub_eq : B - R = ∑ i : Fin d, monomial (i : ℕ) (b i - r i) := by
      simp [B, R, ← Finset.sum_sub_distrib, monomial_sub]
    have hdeg_lt : (B - R).degree < (d : WithBot ℕ) := by
      rw [hsub_eq]
      simpa only [C_mul_X_pow_eq_monomial] using Polynomial.degree_sum_fin_lt (fun i ↦ b i - r i)
    rw [Polynomial.degree_eq_natDegree hne, Nat.cast_lt] at hdeg_lt
    omega
  have heq : B = R := sub_eq_zero.1 hBR
  funext i
  simpa [B, R, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply,
    Fin.val_eq_val] using congrArg (fun p : K[X] ↦ p.coeff (i : ℕ)) heq

/-- If `‖a i‖ ≤ (R / 4) ^ (d - i)` for every `i : Fin d` and `0 < R`, then every root of
`monicOfCoeff a` lies in `ball 0 R`. -/
private theorem mem_ball_of_isRoot_monicOfCoeff {K : Type*} [NormedField K] {d : ℕ}
    {a : Fin d → K} {R : ℝ} (hR : 0 < R)
    (ha : ∀ i : Fin d, ‖a i‖ ≤ (R / 4) ^ (d - (i : ℕ))) {w : K}
    (hw : (Polynomial.monicOfCoeff a).IsRoot w) : w ∈ ball (0 : K) R := by
  have hle : ‖w‖ ≤ 2 * (R / 4) := by
    refine hw.norm_le_two_mul (Polynomial.monic_monicOfCoeff a) fun m hm ↦ ?_
    rw [Polynomial.natDegree_monicOfCoeff] at hm ⊢
    have hm' : m = (⟨m, hm⟩ : Fin d) := rfl
    rw [hm', Polynomial.coeff_monicOfCoeff]
    exact ha ⟨m, hm⟩
  rw [mem_ball_zero_iff]
  linarith

end PolynomialCharacterization

/-! ### Holomorphic functions with Nash real and imaginary parts -/

section HolomorphicNash

private theorem continuous_sumElim_const {σ : Type*} (z : σ → ℂ) :
    Continuous fun w : ℂ ↦ Sum.elim z (fun _ : Unit ↦ w) :=
  continuous_pi (Sum.rec (fun _ ↦ continuous_const) (fun _ ↦ continuous_id))

private theorem analyticAt_sumElim_const {σ : Type*} [Fintype σ] (z : σ → ℂ) (w₀ : ℂ) :
    AnalyticAt ℂ (fun w : ℂ ↦ Sum.elim z (fun _ : Unit ↦ w)) w₀ :=
  AnalyticAt.pi (Sum.rec (fun _ ↦ analyticAt_const) (fun _ ↦ analyticAt_id))

/-- A complex-valued function `F` on `τ → ℂ` is *holomorphic-Nash* at `z₀` when it is complex
analytic at `z₀` and its real and imaginary parts in `complexToRealPi τ` coordinates are real Nash
germs at `complexToRealPi τ z₀`. -/
private structure IsHolomorphicNashAt {τ : Type*} [Fintype τ]
    (F : (τ → ℂ) → ℂ) (z₀ : τ → ℂ) : Prop where
  analyticAt : AnalyticAt ℂ F z₀
  re : IsNashAt (fun a ↦ (F ((complexToRealPi τ).symm a)).re) (complexToRealPi τ z₀)
  im : IsNashAt (fun a ↦ (F ((complexToRealPi τ).symm a)).im) (complexToRealPi τ z₀)

private theorem IsHolomorphicNashAt.congr {τ : Type*} [Fintype τ]
    {F G : (τ → ℂ) → ℂ} {z₀ : τ → ℂ} (hF : IsHolomorphicNashAt F z₀) (h : F =ᶠ[𝓝 z₀] G) :
    IsHolomorphicNashAt G z₀ := by
  let e := complexToRealPi τ
  have he : Tendsto e.symm (𝓝 (e z₀)) (𝓝 z₀) := by
    simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e z₀)
  exact ⟨hF.analyticAt.congr h,
    hF.re.congr ((he.eventually h).mono fun a ha ↦ congrArg Complex.re ha),
    hF.im.congr ((he.eventually h).mono fun a ha ↦ congrArg Complex.im ha)⟩

private theorem isHolomorphicNashAt_const {τ : Type*} [Fintype τ] (c : ℂ) (z₀ : τ → ℂ) :
    IsHolomorphicNashAt (fun _ : τ → ℂ ↦ c) z₀ :=
  ⟨analyticAt_const, isNashAt_const c.re, isNashAt_const c.im⟩

private theorem isHolomorphicNashAt_apply {τ : Type*} [Fintype τ] (i : τ) (z₀ : τ → ℂ) :
    IsHolomorphicNashAt (fun z : τ → ℂ ↦ z i) z₀ :=
  ⟨(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ ↦ ℂ) i).analyticAt z₀,
    by simpa using isNashAt_apply (x := complexToRealPi τ z₀) (Sum.inl i),
    by simpa using isNashAt_apply (x := complexToRealPi τ z₀) (Sum.inr i)⟩

private theorem IsHolomorphicNashAt.add {τ : Type*} [Fintype τ]
    {F G : (τ → ℂ) → ℂ} {z₀ : τ → ℂ}
    (hF : IsHolomorphicNashAt F z₀) (hG : IsHolomorphicNashAt G z₀) :
    IsHolomorphicNashAt (fun z ↦ F z + G z) z₀ :=
  ⟨hF.analyticAt.fun_add hG.analyticAt,
    (hF.re.add hG.re).congr (.of_forall fun _ ↦ rfl),
    (hF.im.add hG.im).congr (.of_forall fun _ ↦ rfl)⟩

private theorem IsHolomorphicNashAt.sub {τ : Type*} [Fintype τ]
    {F G : (τ → ℂ) → ℂ} {z₀ : τ → ℂ}
    (hF : IsHolomorphicNashAt F z₀) (hG : IsHolomorphicNashAt G z₀) :
    IsHolomorphicNashAt (fun z ↦ F z - G z) z₀ :=
  ⟨hF.analyticAt.fun_sub hG.analyticAt,
    (hF.re.sub hG.re).congr (.of_forall fun _ ↦ rfl),
    (hF.im.sub hG.im).congr (.of_forall fun _ ↦ rfl)⟩

private theorem IsHolomorphicNashAt.mul {τ : Type*} [Fintype τ]
    {F G : (τ → ℂ) → ℂ} {z₀ : τ → ℂ}
    (hF : IsHolomorphicNashAt F z₀) (hG : IsHolomorphicNashAt G z₀) :
    IsHolomorphicNashAt (fun z ↦ F z * G z) z₀ :=
  ⟨hF.analyticAt.fun_mul hG.analyticAt,
    ((hF.re.mul hG.re).sub (hF.im.mul hG.im)).congr (.of_forall fun _ ↦ (Complex.mul_re _ _).symm),
    ((hF.re.mul hG.im).add (hF.im.mul hG.re)).congr (.of_forall fun _ ↦ (Complex.mul_im _ _).symm)⟩

private theorem IsHolomorphicNashAt.pow {τ : Type*} [Fintype τ]
    {F : (τ → ℂ) → ℂ} {z₀ : τ → ℂ} (hF : IsHolomorphicNashAt F z₀) (n : ℕ) :
    IsHolomorphicNashAt (fun z ↦ F z ^ n) z₀ := by
  induction n with
  | zero => simpa only [pow_zero] using isHolomorphicNashAt_const 1 z₀
  | succ n ih => simpa only [pow_succ] using ih.mul hF

private theorem IsHolomorphicNashAt.sum {ι τ : Type*} [Fintype τ]
    {F : ι → (τ → ℂ) → ℂ} {z₀ : τ → ℂ} (s : Finset ι)
    (h : ∀ i ∈ s, IsHolomorphicNashAt (F i) z₀) :
    IsHolomorphicNashAt (fun z ↦ ∑ i ∈ s, F i z) z₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHolomorphicNashAt_const 0 z₀
  | insert a s ha ih =>
    have hhead := h a (Finset.mem_insert_self a s)
    have htail := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    exact (hhead.add htail).congr (.of_forall fun z ↦ by simp [Finset.sum_insert ha])

/-- Composing a holomorphic-Nash germ with a holomorphic map whose coordinates are holomorphic-Nash
produces a holomorphic-Nash germ. -/
private theorem IsHolomorphicNashAt.comp {σ τ : Type*} [Fintype σ] [Fintype τ]
    {F : (τ → ℂ) → ℂ} {Φ : (σ → ℂ) → (τ → ℂ)} {z₀ : σ → ℂ}
    (hF : IsHolomorphicNashAt F (Φ z₀)) (hΦ : ∀ j, IsHolomorphicNashAt (fun z ↦ Φ z j) z₀) :
    IsHolomorphicNashAt (F ∘ Φ) z₀ := by
  let eσ := complexToRealPi σ
  let eτ := complexToRealPi τ
  have hΦ_an : AnalyticAt ℂ Φ z₀ := AnalyticAt.pi fun j ↦ (hΦ j).analyticAt
  have hcoords : ∀ k : τ ⊕ τ, IsNashAt (fun a ↦ eτ (Φ (eσ.symm a)) k) (eσ z₀) := by
    intro k
    cases k with
    | inl j => simpa [eσ, eτ] using (hΦ j).re
    | inr j => simpa [eσ, eτ] using (hΦ j).im
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

/-- Exact holomorphic division preserves `IsHolomorphicNashAt`: multiplying `P * Q = H` by `star P`
reduces to real exact division by `|P|²`. -/
private theorem IsHolomorphicNashAt.of_mul_eventuallyEq {τ : Type*} [Fintype τ]
    {P Q H : (τ → ℂ) → ℂ} {z₀ : τ → ℂ}
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

/-- Restricting a holomorphic-Nash germ to the real locus produces a real Nash germ whenever it
takes real values `f y` near `x₀`. -/
private theorem IsHolomorphicNashAt.isNashAt_of_eventually_real {τ : Type*} [Fintype τ]
    {F : (τ → ℂ) → ℂ} {f : (τ → ℝ) → ℝ} {x₀ : τ → ℝ}
    (hF : IsHolomorphicNashAt F (fun j ↦ (x₀ j : ℂ)))
    (hf : ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y) :
    IsNashAt f x₀ := by
  let e := complexToRealPi τ
  let ι : (τ → ℝ) → (τ ⊕ τ → ℝ) := fun y ↦ Sum.elim y 0
  have hι_eq (y : τ → ℝ) : e.symm (ι y) = fun j ↦ (y j : ℂ) := by
    ext j; simp [e, ι]
  have hι_z₀ : ι x₀ = e (fun j ↦ (x₀ j : ℂ)) := by
    ext k; cases k <;> simp [e, ι]
  have hι_nash : ∀ k : τ ⊕ τ, IsNashAt (fun y ↦ ι y k) x₀ := by
    rintro (j | _)
    · exact isNashAt_apply j
    · exact isNashAt_const 0
  refine ((hι_z₀ ▸ hF.re).comp hι_nash).congr ?_
  filter_upwards [hf] with y hy
  simp [Function.comp_apply, e, hι_eq, hy]

/-- Directional differentiation in the vertical coordinate `Sum.inr ()` preserves
`IsHolomorphicNashAt`. -/
private theorem IsHolomorphicNashAt.fderiv_vertical {σ : Type*} [Fintype σ]
    {F : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ ⊕ Unit → ℂ} (hF : IsHolomorphicNashAt F z₀) :
    IsHolomorphicNashAt (fun z ↦ fderiv ℂ F z (Sum.elim 0 1)) z₀ := by
  let v : σ ⊕ Unit → ℂ := Sum.elim 0 1
  let e := complexToRealPi (σ ⊕ Unit)
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

/-- Every iterated vertical slice derivative of a holomorphic-Nash germ is holomorphic-Nash. -/
private theorem IsHolomorphicNashAt.iteratedDeriv_vertical {σ : Type*} [Fintype σ]
    {F : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ ⊕ Unit → ℂ} (hF : IsHolomorphicNashAt F z₀) :
    ∀ n : ℕ, IsHolomorphicNashAt
      (fun z ↦ iteratedDeriv n (fun w ↦ F (Sum.elim (z ∘ Sum.inl) (fun _ ↦ w))) (z (.inr ()))) z₀
  | 0 => hF.congr (.of_forall fun z ↦ by
      have hz : Sum.elim (z ∘ Sum.inl) (fun _ ↦ z (.inr ())) = z := by
        ext k; rcases k with s | ⟨⟩ <;> rfl
      simp [hz])
  | n + 1 => by
    let F' : (σ ⊕ Unit → ℂ) → ℂ := fun z ↦ fderiv ℂ F z (Sum.elim 0 1)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_analyticAt ℂ F) z₀ hF.analyticAt
    refine (hF.fderiv_vertical.iteratedDeriv_vertical n).congr ?_
    filter_upwards [ball_mem_nhds z₀ (half_pos hr)] with z hz
    have hz_lt : dist z z₀ < r := (mem_ball.1 hz).trans (half_lt_self hr)
    have hz_eq : Sum.elim (z ∘ Sum.inl) (fun _ : Unit ↦ z (.inr ())) = z := by
      ext k; rcases k with s | ⟨⟩ <;> rfl
    have hw_open : {w : ℂ | Sum.elim (z ∘ Sum.inl) (fun _ ↦ w) ∈ ball z₀ r} ∈ 𝓝 (z (.inr ())) :=
      ((continuous_sumElim_const (z ∘ Sum.inl)).tendsto (z (.inr ()))).eventually
        (isOpen_ball.mem_nhds (hz_eq.symm ▸ mem_ball.2 hz_lt))
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

end HolomorphicNash

/-! ### Semialgebraicity of complex polynomial Hasse derivatives -/

section SemialgebraicComplexPoly

/-- Real coordinates `(x_ℝ, a_ℝ, w_ℝ)` for base `σ → ℂ`, coefficients `Fin d → ℂ`, and fiber `ℂ`. -/
private abbrev ElimCoord (σ : Type*) (d : ℕ) : Type _ :=
  ((σ ⊕ σ) ⊕ (Fin d ⊕ Fin d)) ⊕ (Unit ⊕ Unit) → ℝ

/-- Evaluating a complex multivariate polynomial defines a semialgebraic map in `complexToRealPi`
coordinates. -/
private theorem isSemialgebraicMap_complexToRealPi_eval {κ : Type*} [Fintype κ]
    (P : MvPolynomial κ ℂ) :
    IsSemialgebraicMap (fun u : κ ⊕ κ → ℝ ↦
      complexToRealPi Unit (fun _ ↦ MvPolynomial.eval ((complexToRealPi κ).symm u) P)) := by
  rw [← isSemialgebraicOn_univ]
  have hpre : (complexToRealPi κ).symm ⁻¹' (Set.univ : Set (κ → ℂ)) = Set.univ := rfl
  rw [← hpre]
  refine isSemialgebraicOn_complexToRealPi_of_forall_eq_iff
    (g := fun z _ ↦ MvPolynomial.eval z P) (s := Set.univ) (ι := Unit)
    isSemialgebraic_univ
    (fun _ ↦ MvPolynomial.rename (Sum.inl ∘ Sum.inl) P - MvPolynomial.X (Sum.inl (Sum.inr ())))
    fun z _ y ↦ ?_
  simp [funext_iff, Unique.forall_iff, sub_eq_zero, MvPolynomial.eval_rename, Function.comp_def]

private theorem monicOfCoeff_eq_X_pow_add_sum {d : ℕ} (a : Fin d → ℂ) :
    Polynomial.monicOfCoeff a =
      _root_.Polynomial.X ^ d + ∑ i : Fin d, monomial (i : ℕ) (a i) := by
  let q : ℂ[X] := _root_.Polynomial.X ^ d + ∑ i : Fin d, monomial (i : ℕ) (a i)
  have hdeg_lt : (∑ i : Fin d, monomial (i : ℕ) (a i)).degree < (d : WithBot ℕ) := by
    simpa only [C_mul_X_pow_eq_monomial] using Polynomial.degree_sum_fin_lt a
  have hq_monic : q.Monic := monic_X_pow_add hdeg_lt
  have hq_deg : q.natDegree = d := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hq_coeff : (fun i : Fin d ↦ q.coeff (i : ℕ)) = a := by
    ext i
    simp [q, coeff_X_pow, i.2.ne, coeff_monomial, Finsupp.single_apply, Fin.val_eq_val]
  conv_lhs => rw [← hq_coeff]
  exact Polynomial.monicOfCoeff_coeff hq_monic hq_deg

/-- The complex multivariate polynomial representing the `j`-th Hasse derivative of
`monicOfCoeff a` evaluated at `w`, in coordinates `Sum.elim a (fun _ : Unit ↦ w)`. -/
private noncomputable def hasseDerivMonicMvPoly (d j : ℕ) : MvPolynomial (Fin d ⊕ Unit) ℂ :=
  MvPolynomial.C (d.choose j : ℂ) * MvPolynomial.X (Sum.inr ()) ^ (d - j) +
    ∑ i : Fin d, MvPolynomial.C ((i : ℕ).choose j : ℂ) *
      MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr ()) ^ ((i : ℕ) - j)

private theorem eval_hasseDerivMonicMvPoly {d : ℕ} (j : ℕ) (a : Fin d → ℂ) (w : ℂ) :
    MvPolynomial.eval (Sum.elim a (fun _ : Unit ↦ w)) (hasseDerivMonicMvPoly d j) =
      (hasseDeriv j (Polynomial.monicOfCoeff a)).eval w := by
  have hXd : (_root_.Polynomial.X ^ d : ℂ[X]) = monomial d 1 := by
    rw [← C_mul_X_pow_eq_monomial, C_1, one_mul]
  rw [monicOfCoeff_eq_X_pow_add_sum, hXd, map_add, map_sum, eval_add, eval_finsetSum]
  simp only [hasseDeriv_monomial, mul_one, eval_monomial, hasseDerivMonicMvPoly, map_add, map_mul,
    map_pow, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]

/-- The complex multivariate polynomial representing `j !` times the `j`-th Hasse derivative of
`∑ i : Fin d, monomial i (b i)` evaluated at `w`. -/
private noncomputable def factorialHasseDerivSumMvPoly (d j : ℕ) : MvPolynomial (Fin d ⊕ Unit) ℂ :=
  MvPolynomial.C (Nat.factorial j : ℂ) *
    ∑ i : Fin d, MvPolynomial.C ((i : ℕ).choose j : ℂ) *
      MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr ()) ^ ((i : ℕ) - j)

private theorem eval_factorialHasseDerivSumMvPoly {d : ℕ} (j : ℕ) (b : Fin d → ℂ) (w : ℂ) :
    MvPolynomial.eval (Sum.elim b (fun _ : Unit ↦ w)) (factorialHasseDerivSumMvPoly d j) =
      (Nat.factorial j : ℂ) *
        (hasseDeriv j (∑ i : Fin d, monomial (i : ℕ) (b i))).eval w := by
  rw [map_sum, eval_finsetSum, factorialHasseDerivSumMvPoly]
  simp only [hasseDeriv_monomial, eval_monomial, map_mul, map_pow, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]

/-- The open disk `ball (0 : ℂ) R` read in `Unit ⊕ Unit → ℝ` coordinates via
`complexToRealPi Unit`. -/
private def realDiskSet (R : ℝ) : Set (Unit ⊕ Unit → ℝ) :=
  {w_ℝ | w_ℝ (Sum.inl ()) ^ 2 + w_ℝ (Sum.inr ()) ^ 2 < R ^ 2}

private theorem isSemialgebraic_realDiskSet (R : ℝ) : IsSemialgebraic (realDiskSet R) := by
  let p : MvPolynomial (Unit ⊕ Unit) ℝ :=
    MvPolynomial.X (Sum.inl ()) ^ 2 + MvPolynomial.X (Sum.inr ()) ^ 2
  convert isSemialgebraic_eval_lt p (MvPolynomial.C (R ^ 2)) using 1
  ext w_ℝ
  simp [realDiskSet, p]

private theorem mem_realDiskSet_iff {R : ℝ} (hR : 0 < R) (w_ℝ : Unit ⊕ Unit → ℝ) :
    w_ℝ ∈ realDiskSet R ↔ (complexToRealPi Unit).symm w_ℝ () ∈ ball (0 : ℂ) R := by
  set w : ℂ := (complexToRealPi Unit).symm w_ℝ ()
  have hsq : w_ℝ (Sum.inl ()) ^ 2 + w_ℝ (Sum.inr ()) ^ 2 = ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [w, sq]
  rw [realDiskSet, Set.mem_ofPred, hsq, mem_ball_zero_iff, sq_lt_sq₀ (norm_nonneg w) hR.le]

/-- Regroup `ElimCoord σ d` onto the base-and-vertical real coordinates
`(σ ⊕ Unit) ⊕ (σ ⊕ Unit)`. -/
private def projXW (σ : Type*) (d : ℕ) :
    (σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ((σ ⊕ σ) ⊕ (Fin d ⊕ Fin d)) ⊕ (Unit ⊕ Unit)
  | .inl (.inl s) => .inl (.inl (.inl s))
  | .inl (.inr ()) => .inr (.inl ())
  | .inr (.inl s) => .inl (.inl (.inr s))
  | .inr (.inr ()) => .inr (.inr ())

/-- Regroup `ElimCoord σ d` onto the coefficient-and-vertical real coordinates
`(Fin d ⊕ Unit) ⊕ (Fin d ⊕ Unit)`. -/
private def projAW (σ : Type*) (d : ℕ) :
    (Fin d ⊕ Unit) ⊕ (Fin d ⊕ Unit) → ((σ ⊕ σ) ⊕ (Fin d ⊕ Fin d)) ⊕ (Unit ⊕ Unit)
  | .inl (.inl i) => .inl (.inr (.inl i))
  | .inl (.inr ()) => .inr (.inl ())
  | .inr (.inl i) => .inl (.inr (.inr i))
  | .inr (.inr ()) => .inr (.inr ())

private theorem symm_comp_projXW {σ : Type*} [Fintype σ] {d : ℕ} (u : ElimCoord σ d) :
    (complexToRealPi (σ ⊕ Unit)).symm (u ∘ projXW σ d) =
      Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
        (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()) := by
  ext k; rcases k with s | ⟨⟩ <;> simp [projXW]

private theorem symm_comp_projAW {σ : Type*} {d : ℕ} (u : ElimCoord σ d) :
    (complexToRealPi (Fin d ⊕ Unit)).symm (u ∘ projAW σ d) =
      Sum.elim ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr))
        (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()) := by
  ext k; rcases k with i | ⟨⟩ <;> simp [projAW]

/-- Cylinder inside `ElimCoord σ d` over `B_X : Set (σ ⊕ σ → ℝ)` and `realDiskSet R`. -/
private abbrev elimCylSet (σ : Type*) (d : ℕ) (B_X : Set (σ ⊕ σ → ℝ)) (R : ℝ) :
    Set (ElimCoord σ d) :=
  ((fun u ↦ u ∘ (Sum.inl ∘ Sum.inl)) ⁻¹' B_X) ∩ ((fun u ↦ u ∘ Sum.inr) ⁻¹' realDiskSet R)

private theorem isSemialgebraic_elimCylSet {σ : Type*} {d : ℕ} {B_X : Set (σ ⊕ σ → ℝ)}
    (hBX : IsSemialgebraic B_X) (R : ℝ) :
    IsSemialgebraic (elimCylSet σ d B_X R) :=
  (hBX.preimage_comp (Sum.inl ∘ Sum.inl)).inter
    ((isSemialgebraic_realDiskSet R).preimage_comp Sum.inr)

private theorem mem_elimCylSet_iff {σ : Type*} {d : ℕ} {B_X : Set (σ ⊕ σ → ℝ)} {R : ℝ}
    (u : ElimCoord σ d) :
    ((u ∘ Sum.inl) ∘ Sum.inl ∈ B_X ∧ u ∘ Sum.inr ∈ realDiskSet R) ↔
      u ∈ elimCylSet σ d B_X R := by
  simp [elimCylSet, Function.comp_def]

/-- Pulling an `IsSemialgebraicOn` map from `W` back to `elimCylSet σ d B_X R`. -/
private theorem isSemialgebraicOn_comp_projXW {σ : Type*} [Fintype σ] {d : ℕ}
    {H : (σ ⊕ Unit → ℂ) → ℂ} {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    {B_X : Set (σ ⊕ σ → ℝ)} {R : ℝ}
    (hBX : IsSemialgebraic B_X)
    (hHW : IsSemialgebraicOn
      (fun q ↦ complexToRealPi Unit (fun _ ↦ H ((complexToRealPi (σ ⊕ Unit)).symm q))) W)
    (hsub : ∀ u : ElimCoord σ d,
      (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X → u ∘ Sum.inr ∈ realDiskSet R → u ∘ projXW σ d ∈ W) :
    IsSemialgebraicOn
      (fun u : ElimCoord σ d ↦ complexToRealPi Unit
        (fun _ ↦ H (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
          (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()))))
      (elimCylSet σ d B_X R) := by
  have hdom : IsSemialgebraic (elimCylSet σ d B_X R) := isSemialgebraic_elimCylSet hBX R
  have hproj : IsSemialgebraicOn (fun u ↦ u ∘ projXW σ d) (elimCylSet σ d B_X R) := by
    simpa [Function.comp_def] using
      isSemialgebraicOn_eval (fun t ↦ (MvPolynomial.X (projXW σ d t) : MvPolynomial _ ℝ)) hdom
  convert hHW.comp hproj (fun u hu ↦ hsub u hu.1 hu.2) using 1
  funext u
  simp only [Function.comp_apply, symm_comp_projXW]

/-- Pulling a complex polynomial on `Fin d ⊕ Unit → ℂ` back to any semialgebraic subset of
`ElimCoord σ d`. -/
private theorem isSemialgebraicOn_eval_comp_projAW {σ : Type*} {d : ℕ}
    (P : MvPolynomial (Fin d ⊕ Unit) ℂ) {S : Set (ElimCoord σ d)} (hS : IsSemialgebraic S) :
    IsSemialgebraicOn
      (fun u : ElimCoord σ d ↦ complexToRealPi Unit
        (fun _ ↦ MvPolynomial.eval
          (Sum.elim ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr))
            (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) P)) S := by
  have hproj : IsSemialgebraicMap (fun u : ElimCoord σ d ↦ u ∘ projAW σ d) := by
    simpa [Function.comp_def] using
      isSemialgebraicMap_eval (fun t ↦ (MvPolynomial.X (projAW σ d t) : MvPolynomial _ ℝ))
  convert ((isSemialgebraicMap_complexToRealPi_eval P).comp hproj).isSemialgebraicOn hS using 1
  funext u
  simp only [Function.comp_apply, symm_comp_projAW]

end SemialgebraicComplexPoly

/-! ### Complex Weierstrass upgrading (`w₀ = 0` and general `w₀`) -/

section ComplexWeierstrassUpgrade

/-- A monic Weierstrass polynomial whose lower coefficients vanish at `z₀` does not vanish as a
germ at `Sum.elim z₀ 0`. -/
private theorem not_eventuallyEq_zero_eval_monicOfCoeff {σ : Type*} {d : ℕ}
    {c : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hc0 : ∀ i, c i z₀ = 0) :
    ¬ (fun p : σ ⊕ Unit → ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ())))
      =ᶠ[𝓝 (Sum.elim z₀ 0)] (0 : (σ ⊕ Unit → ℂ) → ℂ) := by
  intro h0
  have hT : Tendsto (fun w : ℂ ↦ Sum.elim z₀ (fun _ : Unit ↦ w)) (𝓝 0) (𝓝 (Sum.elim z₀ 0)) :=
    (continuous_sumElim_const z₀).tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ((hT.eventually h0).mono fun _ hw ↦ hw)
  have hmem : ((ε / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have heval : (Polynomial.monicOfCoeff (fun i ↦ c i z₀)).eval ((ε / 2 : ℝ) : ℂ) = 0 := hball hmem
  rw [Polynomial.eval_monicOfCoeff] at heval
  simp only [hc0, zero_mul, Finset.sum_const_zero, add_zero] at heval
  exact pow_ne_zero d (Complex.ofReal_ne_zero.2 (by positivity)) heval

/-- Constructing a common isolating cylinder `(B_X, R)` around `(z₀, 0)` on which a finite family
of holomorphic-Nash functions `H : ι → (σ ⊕ Unit → ℂ) → ℂ` have semialgebraic realifications and
the Weierstrass polynomial coefficients satisfy Fujiwara's bound `‖c i x‖ ≤ (R / 4) ^ (d - i)`. -/
private theorem exists_isolating_cylinder {σ ι : Type*} [Fintype σ] [Finite ι] {d : ℕ}
    {z₀ : σ → ℂ} {c : Fin d → (σ → ℂ) → ℂ}
    (hc : ∀ i, AnalyticAt ℂ (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    {H : ι → (σ ⊕ Unit → ℂ) → ℂ} (hH : ∀ k, IsHolomorphicNashAt (H k) (Sum.elim z₀ 0))
    {P : (σ ⊕ Unit → ℂ) → Prop} (hP : ∀ᶠ p in 𝓝 (Sum.elim z₀ 0), P p) :
    ∃ (R : ℝ) (B_X : Set (σ ⊕ σ → ℝ)),
      0 < R ∧ IsOpen B_X ∧ complexToRealPi σ z₀ ∈ B_X ∧ IsSemialgebraic B_X ∧
      (∀ x_ℝ ∈ B_X, ∀ i : Fin d,
        ‖c i ((complexToRealPi σ).symm x_ℝ)‖ ≤ (R / 4) ^ (d - (i : ℕ))) ∧
      (∀ x_ℝ ∈ B_X, ∀ w ∈ ball (0 : ℂ) R,
        P (Sum.elim ((complexToRealPi σ).symm x_ℝ) (fun _ ↦ w))) ∧
      ∃ W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ),
        (∀ k, IsSemialgebraicOn
          (fun q ↦ complexToRealPi Unit
            (fun _ ↦ H k ((complexToRealPi (σ ⊕ Unit)).symm q))) W) ∧
        (∀ u : ElimCoord σ d,
          (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X → u ∘ Sum.inr ∈ realDiskSet R → u ∘ projXW σ d ∈ W) := by
  let eσ := complexToRealPi σ
  let e := complexToRealPi (σ ⊕ Unit)
  have hcoords : ∀ p : ι × (Unit ⊕ Unit),
      IsNashAt (fun q ↦ complexToRealPi Unit (fun _ ↦ H p.1 (e.symm q)) p.2)
        (e (Sum.elim z₀ 0)) := by
    rintro ⟨k, b⟩
    cases b with
    | inl _ => simpa [e] using (hH k).re
    | inr _ => simpa [e] using (hH k).im
  obtain ⟨W, hWo, hzW, hW_semi, hHW_coord⟩ := exists_isSemialgebraicOn_of_forall_isNashAt hcoords
  have hHW (k : ι) : IsSemialgebraicOn
      (fun q ↦ complexToRealPi Unit (fun _ ↦ H k (e.symm q))) W :=
    isSemialgebraicOn_pi_iff.2 ⟨hW_semi, fun b ↦ hHW_coord (k, b)⟩
  obtain ⟨R, hR, hR_ball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (e.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)) hP)
  have hc_bound : ∀ᶠ x in 𝓝 z₀, ∀ i : Fin d, ‖c i x‖ ≤ (R / 4) ^ (d - (i : ℕ)) := by
    refine eventually_all.2 fun i ↦ ?_
    have hrad : 0 < (R / 4) ^ (d - (i : ℕ)) := by positivity
    have hlt := (hc i).continuousAt.tendsto (ball_mem_nhds (c i z₀) hrad)
    exact eventually_of_mem hlt fun x hx ↦ by simpa [hc0 i] using (mem_ball.1 hx).le
  have heσ : Tendsto eσ.symm (𝓝 (eσ z₀)) (𝓝 z₀) := by
    simpa only [eσ.symm_apply_apply] using eσ.symm.continuous.tendsto (eσ z₀)
  obtain ⟨δ, hδ, hδ_ball⟩ := Metric.mem_nhds_iff.1
    (heσ.eventually (inter_mem (ball_mem_nhds z₀ hR) hc_bound))
  refine ⟨R, ball (eσ z₀) δ, hR, isOpen_ball, mem_ball_self hδ,
    isSemialgebraic_ball (eσ z₀) δ, fun x_ℝ hx ↦ (hδ_ball hx).2, ?_, W, hHW, ?_⟩
  · intro x_ℝ hx w hw
    refine (hR_ball ?_).2
    rw [mem_ball, dist_pi_lt_iff hR]
    rintro (s | ⟨⟩)
    · exact (dist_pi_lt_iff hR).1 (mem_ball.1 (hδ_ball hx).1) s
    · exact mem_ball.1 hw
  · intro u hx hw
    have hp_mem : Sum.elim (eσ.symm ((u ∘ Sum.inl) ∘ Sum.inl))
        (fun _ : Unit ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ()) ∈
          ball (Sum.elim z₀ 0) R := by
      rw [mem_ball, dist_pi_lt_iff hR]
      rintro (s | ⟨⟩)
      · exact (dist_pi_lt_iff hR).1 (mem_ball.1 (hδ_ball hx).1) s
      · exact mem_ball.1 ((mem_realDiskSet_iff hR _).1 hw)
    have he_eq : e (Sum.elim (eσ.symm ((u ∘ Sum.inl) ∘ Sum.inl))
        (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = u ∘ projXW σ d := by
      rw [← symm_comp_projXW, e.apply_symm_apply]
    exact he_eq ▸ (hR_ball hp_mem).1

/-- Upgrading a holomorphic tuple `a : Fin d → (σ → ℂ) → ℂ` whose realified map is semialgebraic on
an open neighbourhood of `complexToRealPi σ z₀` to `IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_isSemialgebraicOn {σ : Type*} [Fintype σ] {d : ℕ}
    {a : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} {B_X : Set (σ ⊕ σ → ℝ)}
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hBX_open : IsOpen B_X) (hzBX : complexToRealPi σ z₀ ∈ B_X)
    (hsemi : IsSemialgebraicOn
      (fun x_ℝ ↦ complexToRealPi (Fin d) (fun i ↦ a i ((complexToRealPi σ).symm x_ℝ))) B_X) :
    ∀ i, IsHolomorphicNashAt (a i) z₀ := by
  let eσ := complexToRealPi σ
  let ed := complexToRealPi (Fin d)
  have ha_real : AnalyticAt ℝ (fun x_ℝ ↦ ed (fun i ↦ a i (eσ.symm x_ℝ))) (eσ z₀) :=
    (ed.analyticAt _).comp <| AnalyticAt.pi fun i ↦
      ((ha i).restrictScalars (𝕜 := ℝ)).comp_of_eq (eσ.symm.analyticAt _) (eσ.symm_apply_apply z₀)
  have hcoords := forall_isNashAt_apply_iff_exists_isSemialgebraicOn.2
    ⟨ha_real, B_X, hBX_open, hzBX, hsemi⟩
  exact fun i ↦
    ⟨ha i, by simpa [ed] using hcoords (Sum.inl i), by simpa [ed] using hcoords (Sum.inr i)⟩

/-- Evaluating the `j`-th Hasse derivative of `monicOfCoeff` at holomorphic-Nash coefficient germs
gives a holomorphic-Nash germ on `σ ⊕ Unit → ℂ`. -/
private theorem isHolomorphicNashAt_eval_hasseDeriv_monicOfCoeff {σ : Type*} [Fintype σ] {d : ℕ}
    {c : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hc : ∀ i, IsHolomorphicNashAt (c i) z₀) (j : ℕ) :
    IsHolomorphicNashAt
      (fun p : σ ⊕ Unit → ℂ ↦
        (hasseDeriv j (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl)))).eval (p (.inr ())))
      (Sum.elim z₀ 0) := by
  have hw_nash : IsHolomorphicNashAt (fun p : σ ⊕ Unit → ℂ ↦ p (.inr ())) (Sum.elim z₀ 0) :=
    isHolomorphicNashAt_apply (Sum.inr ()) _
  have hc_pull (i : Fin d) :
      IsHolomorphicNashAt (fun p : σ ⊕ Unit → ℂ ↦ c i (p ∘ Sum.inl)) (Sum.elim z₀ 0) :=
    (hc i).comp fun s ↦ isHolomorphicNashAt_apply (Sum.inl s) _
  have hlead := (isHolomorphicNashAt_const (d.choose j : ℂ) _).mul (hw_nash.pow (d - j))
  have hsum := IsHolomorphicNashAt.sum Finset.univ fun (i : Fin d) _ ↦
    ((isHolomorphicNashAt_const ((i : ℕ).choose j : ℂ) _).mul (hc_pull i)).mul
      (hw_nash.pow ((i : ℕ) - j))
  refine (hlead.add hsum).congr (.of_forall fun p ↦ ?_)
  simpa [hasseDerivMonicMvPoly] using
    eval_hasseDerivMonicMvPoly j (fun i ↦ c i (p ∘ Sum.inl)) (p (.inr ()))

/-- Evaluating `monicOfCoeff` at holomorphic-Nash coefficient germs gives a holomorphic-Nash germ
on `σ ⊕ Unit → ℂ`. -/
private theorem isHolomorphicNashAt_eval_monicOfCoeff {σ : Type*} [Fintype σ] {d : ℕ}
    {c : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hc : ∀ i, IsHolomorphicNashAt (c i) z₀) :
    IsHolomorphicNashAt
      (fun p : σ ⊕ Unit → ℂ ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ())))
      (Sum.elim z₀ 0) := by
  simpa only [hasseDeriv_zero, LinearMap.id_apply] using
    isHolomorphicNashAt_eval_hasseDeriv_monicOfCoeff hc 0

/-- Evaluating a polynomial remainder `∑ i : Fin d, r i (p ∘ Sum.inl) * p (.inr ()) ^ i` at
holomorphic-Nash coefficient germs gives a holomorphic-Nash germ on `σ ⊕ Unit → ℂ`. -/
private theorem isHolomorphicNashAt_sum_mul_pow {σ : Type*} [Fintype σ] {d : ℕ}
    {r : Fin d → (σ → ℂ) → ℂ} {z₀ : σ → ℂ} (hr : ∀ i, IsHolomorphicNashAt (r i) z₀) :
    IsHolomorphicNashAt
      (fun p : σ ⊕ Unit → ℂ ↦ ∑ i : Fin d, r i (p ∘ Sum.inl) * p (.inr ()) ^ (i : ℕ))
      (Sum.elim z₀ 0) :=
  .sum Finset.univ fun i _ ↦
    ((hr i).comp fun s ↦ isHolomorphicNashAt_apply (Sum.inl s) _).mul
      ((isHolomorphicNashAt_apply (Sum.inr ()) _).pow (i : ℕ))

/-- Along a vertical slice where `F (x, w) = P.eval w * u (x, w)` and `u (x, w₀) ≠ 0`, the Hasse
derivatives of `P = monicOfCoeff c` below `k` vanish at `w₀` iff the iterated derivatives of `F`
below `k` vanish at `w₀`. -/
private theorem hasseDeriv_iff_iteratedDeriv_of_weierstrassPreparation {σ : Type*} [Fintype σ]
    {F u : (σ ⊕ Unit → ℂ) → ℂ} {x : σ → ℂ} {d : ℕ} {c : Fin d → ℂ} {w₀ : ℂ} {R : ℝ}
    (hw₀ : w₀ ∈ ball (0 : ℂ) R)
    (hF_an : AnalyticAt ℂ F (Sum.elim x (fun _ ↦ w₀)))
    (hu_an : AnalyticAt ℂ u (Sum.elim x (fun _ ↦ w₀)))
    (hu0 : u (Sum.elim x (fun _ ↦ w₀)) ≠ 0)
    (hfac : ∀ w ∈ ball (0 : ℂ) R,
      F (Sum.elim x (fun _ ↦ w)) = (Polynomial.monicOfCoeff c).eval w * u (Sum.elim x (fun _ ↦ w)))
    (k : Fin (d + 1)) :
    (∀ j : Fin (k : ℕ), (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff c)).eval w₀ = 0) ↔
      (∀ j : Fin (k : ℕ),
        iteratedDeriv (j : ℕ) (fun w ↦ F (Sum.elim x (fun _ ↦ w))) w₀ = 0) := by
  let P := Polynomial.monicOfCoeff c
  have hf_w : AnalyticAt ℂ (fun w ↦ F (Sum.elim x (fun _ ↦ w))) w₀ :=
    hF_an.comp_of_eq (analyticAt_sumElim_const x w₀) rfl
  have hu_w : AnalyticAt ℂ (fun w ↦ u (Sum.elim x (fun _ ↦ w))) w₀ :=
    hu_an.comp_of_eq (analyticAt_sumElim_const x w₀) rfl
  have hP_w : AnalyticAt ℂ (fun w ↦ P.eval w) w₀ :=
    (AnalyticOnNhd.eval_polynomial P) w₀ (Set.mem_univ w₀)
  have hfac_w : (fun w ↦ F (Sum.elim x (fun _ ↦ w))) =ᶠ[𝓝 w₀]
      (fun w ↦ P.eval w) * (fun w ↦ u (Sum.elim x (fun _ ↦ w))) :=
    eventually_of_mem (isOpen_ball.mem_nhds hw₀) hfac
  have hord : analyticOrderAt (fun w ↦ F (Sum.elim x (fun _ ↦ w))) w₀ =
      (P.rootMultiplicity w₀ : ℕ∞) := by
    rw [analyticOrderAt_congr hfac_w, analyticOrderAt_mul hP_w hu_w,
      hu_w.analyticOrderAt_eq_zero.2 hu0, add_zero,
      Polynomial.analyticOrderAt_eval (Polynomial.monic_monicOfCoeff _).ne_zero w₀]
  have hiff := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf_w (n := (k : ℕ))).symm
  rw [hord, Nat.cast_le,
    Polynomial.le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero
      (Polynomial.monic_monicOfCoeff _).ne_zero] at hiff
  exact ⟨fun h j ↦ (hiff.2 fun m hm ↦ h ⟨m, hm⟩) j j.2,
    fun h j ↦ (hiff.1 fun m hm ↦ h ⟨m, hm⟩) j j.2⟩

private theorem imp_iff_mem_compl_union {α : Type*} {A B : Set α} (u : α) :
    (u ∈ A → u ∈ B) ↔ u ∈ Aᶜ ∪ B := by
  classical
  exact ⟨fun h ↦ if ha : u ∈ A then .inr (h ha) else .inl ha,
    fun h ha ↦ h.resolve_left (Classical.not_not.2 ha)⟩

private theorem imp_forall_iff_mem_compl_union {α : Type*} {n : ℕ} {U : Set α}
    {P : Fin n → Prop} {S : Fin n → Set α} {u : α} (hS : u ∈ U → ∀ k, P k ↔ u ∈ S k) :
    (u ∈ U → ∀ k, P k) ↔ u ∈ Uᶜ ∪ ⋂ k, S k := by
  classical
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iInter]
  exact ⟨fun h ↦ if hu : u ∈ U then .inr fun k ↦ (hS hu k).1 (h hu k) else .inl hu,
    fun h hu k ↦ (hS hu k).2 ((h.resolve_left (Classical.not_not.2 hu)) k)⟩

/-- Semialgebraicity of the fiberwise root-and-multiplicity relation cutting out the Weierstrass
polynomial coefficients before universal elimination of `w_ℝ`. -/
private theorem isSemialgebraic_prepElimSet {σ : Type*} [Fintype σ] {d : ℕ}
    {B_X : Set (σ ⊕ σ → ℝ)} {R : ℝ} {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    {DF : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ}
    (hBX : IsSemialgebraic B_X)
    (hDF_W : ∀ j, IsSemialgebraicOn
      (fun q ↦ complexToRealPi Unit (fun _ ↦ DF j ((complexToRealPi (σ ⊕ Unit)).symm q))) W)
    (hsub : ∀ u : ElimCoord σ d,
      (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X → u ∘ Sum.inr ∈ realDiskSet R → u ∘ projXW σ d ∈ W) :
    IsSemialgebraic
      {u : ElimCoord σ d |
        ((Polynomial.monicOfCoeff
            ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr))).eval
              ((complexToRealPi Unit).symm (u ∘ Sum.inr) ()) = 0 →
            u ∘ Sum.inr ∈ realDiskSet R) ∧
          ((u ∘ Sum.inl) ∘ Sum.inl ∈ B_X ∧ u ∘ Sum.inr ∈ realDiskSet R →
            ∀ k : Fin (d + 1),
              (∀ j : Fin (k : ℕ),
                (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff
                  ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr)))).eval
                    ((complexToRealPi Unit).symm (u ∘ Sum.inr) ()) = 0) ↔
              (∀ j : Fin (k : ℕ),
                DF ⟨j, j.2.trans k.2⟩
                  (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
                    (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = 0))} := by
  let U_cyl := elimCylSet σ d B_X R
  have hU_cyl : IsSemialgebraic U_cyl := isSemialgebraic_elimCylSet hBX R
  let Z_P (j : ℕ) : Set (ElimCoord σ d) :=
    {u | (hasseDeriv j (Polynomial.monicOfCoeff
      ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr)))).eval
        ((complexToRealPi Unit).symm (u ∘ Sum.inr) ()) = 0}
  have hZ_P (j : ℕ) : IsSemialgebraic (Z_P j) := by
    convert (isSemialgebraicOn_eval_comp_projAW (σ := σ) (hasseDerivMonicMvPoly d j)
      isSemialgebraic_univ).isSemialgebraic_inter_setOf_eq
        (isSemialgebraicOn_const 0 isSemialgebraic_univ) using 1
    ext u; simp [Z_P, eval_hasseDerivMonicMvPoly, funext_iff, Complex.ext_iff]
  let Z_F (j : Fin (d + 1)) : Set (ElimCoord σ d) :=
    U_cyl ∩ {u | DF j (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
      (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = 0}
  have hZ_F (j : Fin (d + 1)) : IsSemialgebraic (Z_F j) := by
    convert (isSemialgebraicOn_comp_projXW hBX (hDF_W j) hsub).isSemialgebraic_inter_setOf_eq
      (isSemialgebraicOn_const 0 hU_cyl) using 1
    ext u; simp [Z_F, U_cyl, funext_iff, Complex.ext_iff]
  let A_P (k : Fin (d + 1)) : Set (ElimCoord σ d) := ⋂ j : Fin (k : ℕ), Z_P (j : ℕ)
  let A_F (k : Fin (d + 1)) : Set (ElimCoord σ d) :=
    ⋂ j : Fin (k : ℕ), Z_F ⟨j, j.2.trans k.2⟩
  have hA_P (k : Fin (d + 1)) : IsSemialgebraic (A_P k) := .iInter fun j ↦ hZ_P (j : ℕ)
  have hA_F (k : Fin (d + 1)) : IsSemialgebraic (A_F k) :=
    .iInter fun j ↦ hZ_F ⟨j, j.2.trans k.2⟩
  have hC1 :
      IsSemialgebraic ((Z_P 0)ᶜ ∪ ((fun u : ElimCoord σ d ↦ u ∘ Sum.inr) ⁻¹' realDiskSet R)) :=
    (hZ_P 0).compl.union ((isSemialgebraic_realDiskSet R).preimage_comp Sum.inr)
  have hC2 : IsSemialgebraic
      (U_cylᶜ ∪ ⋂ k : Fin (d + 1), ((A_P k)ᶜ ∪ A_F k) ∩ ((A_F k)ᶜ ∪ A_P k)) :=
    hU_cyl.compl.union (.iInter fun k ↦
      ((hA_P k).compl.union (hA_F k)).inter ((hA_F k).compl.union (hA_P k)))
  convert hC1.inter hC2 using 1
  ext u
  rw [Set.mem_ofPred, Set.mem_inter_iff, mem_elimCylSet_iff]
  refine and_congr ?_ (imp_forall_iff_mem_compl_union fun hu k ↦ ?_)
  · simpa only [Z_P, Set.mem_ofPred, Set.mem_preimage, hasseDeriv_zero, LinearMap.id_apply] using
      imp_iff_mem_compl_union (A := Z_P 0) (B := (fun u ↦ u ∘ Sum.inr) ⁻¹' realDiskSet R) u
  · have hAP : (∀ j : Fin (k : ℕ), (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff
        ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr)))).eval
          ((complexToRealPi Unit).symm (u ∘ Sum.inr) ()) = 0) ↔ u ∈ A_P k := by
      simp [A_P, Z_P]
    have hAF : (∀ j : Fin (k : ℕ), DF ⟨j, j.2.trans k.2⟩
        (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
          (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = 0) ↔ u ∈ A_F k := by
      simp [A_F, Z_F, U_cyl, hu]
    rw [hAP, hAF, Set.mem_inter_iff, ← imp_iff_mem_compl_union, ← imp_iff_mem_compl_union]
    exact iff_def

/-- Upgrading a complex Weierstrass preparation at `(z₀, 0)` to `IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_weierstrassPreparation_zero {σ : Type*} [Fintype σ]
    {F u : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {d : ℕ} {c : Fin d → (σ → ℂ) → ℂ}
    (hF : IsHolomorphicNashAt F (Sum.elim z₀ 0))
    (hc : ∀ i, AnalyticAt ℂ (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    (hu : AnalyticAt ℂ u (Sum.elim z₀ 0)) (hu0 : u (Sum.elim z₀ 0) ≠ 0)
    (hfac : F =ᶠ[𝓝 (Sum.elim z₀ 0)] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ())) * u p) :
    (∀ i, IsHolomorphicNashAt (c i) z₀) ∧ IsHolomorphicNashAt u (Sum.elim z₀ 0) := by
  let eσ := complexToRealPi σ
  let ed := complexToRealPi (Fin d)
  let DF : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ := fun j p ↦
    iteratedDeriv (j : ℕ) (fun w ↦ F (Sum.elim (p ∘ Sum.inl) (fun _ ↦ w))) (p (.inr ()))
  obtain ⟨R, B_X, hR, hBX_open, hzBX, hBX_semi, hc_bound, hprop, W, hDF_W, hsub⟩ :=
    exists_isolating_cylinder (H := DF) hc hc0 (fun j ↦ hF.iteratedDeriv_vertical (j : ℕ))
      (((hF.analyticAt.eventually_analyticAt.and hu.eventually_analyticAt).and
        (hu.continuousAt.eventually_ne hu0)).and hfac)
  have horder (x_ℝ : σ ⊕ σ → ℝ) (hx : x_ℝ ∈ B_X) (w : ℂ) (hw : w ∈ ball (0 : ℂ) R)
      (k : Fin (d + 1)) :=
    hasseDeriv_iff_iteratedDeriv_of_weierstrassPreparation hw
      (hprop x_ℝ hx w hw).1.1.1 (hprop x_ℝ hx w hw).1.1.2 (hprop x_ℝ hx w hw).1.2
      (fun w' hw' ↦ by simpa only [Sum.elim_comp_inl, Sum.elim_inr] using (hprop x_ℝ hx w' hw').2) k
  have hc_semi : IsSemialgebraicOn (fun x_ℝ ↦ ed (fun i ↦ c i (eσ.symm x_ℝ))) B_X := by
    rw [isSemialgebraicOn_iff_graph]
    convert (hBX_semi.preimage_comp Sum.inl).inter
      (isSemialgebraic_prepElimSet hBX_semi hDF_W hsub).setOf_forall_sumElim using 1
    ext v
    rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    refine and_congr_right fun hvBX ↦ ?_
    rw [← ContinuousLinearEquiv.eq_symm_apply]
    refine ⟨fun hvc w_ℝ ↦ ?_, fun hall ↦ symm <| eq_of_monicOfCoeff_forall_hasseDeriv_iff
      (fun w hw ↦ ?_) (fun w hw ↦ mem_ball_of_isRoot_monicOfCoeff hR (hc_bound _ hvBX) hw)
      (fun w hw k ↦ ?_)⟩
    · have hvc' : (complexToRealPi (Fin d)).symm (v ∘ Sum.inr) =
          fun i ↦ c i (eσ.symm (v ∘ Sum.inl)) := hvc.symm
      rw [hvc']
      exact ⟨fun hw ↦ (mem_realDiskSet_iff hR w_ℝ).2
        (mem_ball_of_isRoot_monicOfCoeff hR (hc_bound _ hvBX) hw),
        fun ⟨_, hwD⟩ k ↦ horder _ hvBX _ ((mem_realDiskSet_iff hR w_ℝ).1 hwD) k⟩
    · let w_ℝ := complexToRealPi Unit (fun _ ↦ w)
      have hw_eq : (complexToRealPi Unit).symm w_ℝ () = w := by simp [w_ℝ]
      exact hw_eq ▸ (mem_realDiskSet_iff hR w_ℝ).1 ((hall w_ℝ).1 (hw_eq.symm ▸ hw))
    · let w_ℝ := complexToRealPi Unit (fun _ ↦ w)
      have hw_eq : (complexToRealPi Unit).symm w_ℝ () = w := by simp [w_ℝ]
      have hwD : w_ℝ ∈ realDiskSet R := (mem_realDiskSet_iff hR w_ℝ).2 (hw_eq.symm ▸ hw)
      have h2 := (hall w_ℝ).2 ⟨hvBX, hwD⟩ k
      rw [hw_eq] at h2
      exact h2.trans (horder _ hvBX w hw k).symm
  have hc_nash := isHolomorphicNashAt_of_isSemialgebraicOn hc hBX_open hzBX hc_semi
  exact ⟨hc_nash, (isHolomorphicNashAt_eval_monicOfCoeff hc_nash).of_mul_eventuallyEq
    hF hu (not_eventuallyEq_zero_eval_monicOfCoeff hc0) hfac.symm⟩

/-- Along a vertical slice where `G = P * q + Rem`, vanishing of Hasse derivatives of `P` below `k`
forces the iterated derivatives of `G` below `k` to match `j !` times the Hasse derivatives of
`Rem`. -/
private theorem jet_eq_of_weierstrassDivision {σ : Type*} [Fintype σ]
    {G q : (σ ⊕ Unit → ℂ) → ℂ} {x : σ → ℂ} {d : ℕ} {c r : Fin d → ℂ} {w₀ : ℂ} {R : ℝ}
    (hw₀ : w₀ ∈ ball (0 : ℂ) R)
    (hG_an : AnalyticAt ℂ G (Sum.elim x (fun _ ↦ w₀)))
    (hq_an : AnalyticAt ℂ q (Sum.elim x (fun _ ↦ w₀)))
    (hdiv : ∀ w ∈ ball (0 : ℂ) R,
      G (Sum.elim x (fun _ ↦ w)) =
        (Polynomial.monicOfCoeff c).eval w * q (Sum.elim x (fun _ ↦ w)) +
          ∑ i : Fin d, r i * w ^ (i : ℕ))
    (k : Fin (d + 1))
    (hP0 : ∀ j : Fin (k : ℕ), (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff c)).eval w₀ = 0) :
    ∀ j : Fin (k : ℕ),
      iteratedDeriv (j : ℕ) (fun w ↦ G (Sum.elim x (fun _ ↦ w))) w₀ =
        (Nat.factorial (j : ℕ) : ℂ) *
          (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ) (r i))).eval w₀ := by
  let P := Polynomial.monicOfCoeff c
  let Rem : ℂ[X] := ∑ i : Fin d, monomial (i : ℕ) (r i)
  have hg_w : AnalyticAt ℂ (fun w ↦ G (Sum.elim x (fun _ ↦ w))) w₀ :=
    hG_an.comp_of_eq (analyticAt_sumElim_const x w₀) rfl
  have hq_w : AnalyticAt ℂ (fun w ↦ q (Sum.elim x (fun _ ↦ w))) w₀ :=
    hq_an.comp_of_eq (analyticAt_sumElim_const x w₀) rfl
  have hP_w : AnalyticAt ℂ (fun w ↦ P.eval w) w₀ :=
    (AnalyticOnNhd.eval_polynomial P) w₀ (Set.mem_univ w₀)
  have hR_w : AnalyticAt ℂ (fun w ↦ Rem.eval w) w₀ :=
    (AnalyticOnNhd.eval_polynomial Rem) w₀ (Set.mem_univ w₀)
  have hsub_eq : (fun w ↦ G (Sum.elim x (fun _ ↦ w)) - Rem.eval w) =ᶠ[𝓝 w₀]
      (fun w ↦ P.eval w) * (fun w ↦ q (Sum.elim x (fun _ ↦ w))) := by
    filter_upwards [isOpen_ball.mem_nhds hw₀] with w hw
    simp only [Rem, eval_finsetSum, eval_monomial]
    exact sub_eq_of_eq_add (hdiv w hw)
  have hk_le : (k : ℕ∞) ≤
      analyticOrderAt (fun w ↦ G (Sum.elim x (fun _ ↦ w)) - Rem.eval w) w₀ := by
    rw [analyticOrderAt_congr hsub_eq, analyticOrderAt_mul hP_w hq_w,
      Polynomial.analyticOrderAt_eval (Polynomial.monic_monicOfCoeff _).ne_zero w₀]
    refine le_trans ?_ le_self_add
    rw [Nat.cast_le, Polynomial.le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero
      (Polynomial.monic_monicOfCoeff _).ne_zero]
    exact fun m hm ↦ hP0 ⟨m, hm⟩
  have hzero :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg_w.fun_sub hR_w)).1 hk_le
  intro j
  have hj := hzero (j : ℕ) j.2
  rw [iteratedDeriv_fun_sub hg_w.contDiffAt hR_w.contDiffAt, sub_eq_zero,
    Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv] at hj
  exact hj

/-- Semialgebraicity of the fiberwise Taylor-jet matching relation cutting out the Weierstrass
remainder coefficients before universal elimination of `w_ℝ`. -/
private theorem isSemialgebraic_divElimSet {σ : Type*} [Fintype σ] {d : ℕ}
    {B_X : Set (σ ⊕ σ → ℝ)} {R : ℝ} {W : Set ((σ ⊕ Unit) ⊕ (σ ⊕ Unit) → ℝ)}
    {DG HP : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ}
    (hBX : IsSemialgebraic B_X)
    (hHW : ∀ s : Fin (d + 1) ⊕ Fin (d + 1), IsSemialgebraicOn
      (fun q ↦ complexToRealPi Unit
        (fun _ ↦ Sum.elim DG HP s ((complexToRealPi (σ ⊕ Unit)).symm q))) W)
    (hsub : ∀ u : ElimCoord σ d,
      (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X → u ∘ Sum.inr ∈ realDiskSet R → u ∘ projXW σ d ∈ W) :
    IsSemialgebraic
      {u : ElimCoord σ d |
        (u ∘ Sum.inl) ∘ Sum.inl ∈ B_X ∧ u ∘ Sum.inr ∈ realDiskSet R →
          ∀ k : Fin (d + 1),
            (∀ j : Fin (k : ℕ),
              HP ⟨j, j.2.trans k.2⟩
                (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
                  (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = 0) →
            ∀ j : Fin (k : ℕ),
              DG ⟨j, j.2.trans k.2⟩
                (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
                  (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) =
                (Nat.factorial (j : ℕ) : ℂ) *
                  (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ)
                    ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr) i))).eval
                      ((complexToRealPi Unit).symm (u ∘ Sum.inr) ())} := by
  let U_cyl := elimCylSet σ d B_X R
  have hU_cyl : IsSemialgebraic U_cyl := isSemialgebraic_elimCylSet hBX R
  let Z_HP (j : Fin (d + 1)) : Set (ElimCoord σ d) :=
    U_cyl ∩ {u | HP j (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
      (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = 0}
  have hZ_HP (j : Fin (d + 1)) : IsSemialgebraic (Z_HP j) := by
    have hcomp := isSemialgebraicOn_comp_projXW hBX (hHW (Sum.inr j)) hsub
    convert hcomp.isSemialgebraic_inter_setOf_eq (isSemialgebraicOn_const 0 hU_cyl) using 1
    ext u; simp [Z_HP, U_cyl, funext_iff, Complex.ext_iff]
  let Eq_DG (j : Fin (d + 1)) : Set (ElimCoord σ d) :=
    U_cyl ∩ {u | DG j (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
      (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) =
        (Nat.factorial (j : ℕ) : ℂ) *
          (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ)
            ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr) i))).eval
              ((complexToRealPi Unit).symm (u ∘ Sum.inr) ())}
  have hEq_DG (j : Fin (d + 1)) : IsSemialgebraic (Eq_DG j) := by
    have hcomp := isSemialgebraicOn_comp_projXW hBX (hHW (Sum.inl j)) hsub
    convert hcomp.isSemialgebraic_inter_setOf_eq
      (isSemialgebraicOn_eval_comp_projAW (σ := σ)
        (factorialHasseDerivSumMvPoly d (j : ℕ)) hU_cyl) using 1
    ext u; simp [Eq_DG, U_cyl, eval_factorialHasseDerivSumMvPoly, funext_iff, Complex.ext_iff]
  let A_HP (k : Fin (d + 1)) : Set (ElimCoord σ d) :=
    ⋂ j : Fin (k : ℕ), Z_HP ⟨j, j.2.trans k.2⟩
  let B_DG (k : Fin (d + 1)) : Set (ElimCoord σ d) :=
    ⋂ j : Fin (k : ℕ), Eq_DG ⟨j, j.2.trans k.2⟩
  have hA_HP (k : Fin (d + 1)) : IsSemialgebraic (A_HP k) :=
    .iInter fun j ↦ hZ_HP ⟨j, j.2.trans k.2⟩
  have hB_DG (k : Fin (d + 1)) : IsSemialgebraic (B_DG k) :=
    .iInter fun j ↦ hEq_DG ⟨j, j.2.trans k.2⟩
  convert hU_cyl.compl.union (.iInter fun k ↦ (hA_HP k).compl.union (hB_DG k)) using 1
  ext u
  rw [Set.mem_ofPred, mem_elimCylSet_iff]
  refine imp_forall_iff_mem_compl_union fun hu k ↦ ?_
  have hAHP : (∀ j : Fin (k : ℕ), HP ⟨j, j.2.trans k.2⟩
      (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
        (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) = 0) ↔ u ∈ A_HP k := by
    simp [A_HP, Z_HP, U_cyl, hu]
  have hBDG : (∀ j : Fin (k : ℕ), DG ⟨j, j.2.trans k.2⟩
      (Sum.elim ((complexToRealPi σ).symm ((u ∘ Sum.inl) ∘ Sum.inl))
        (fun _ ↦ (complexToRealPi Unit).symm (u ∘ Sum.inr) ())) =
        (Nat.factorial (j : ℕ) : ℂ) *
          (hasseDeriv (j : ℕ) (∑ i : Fin d, monomial (i : ℕ)
            ((complexToRealPi (Fin d)).symm ((u ∘ Sum.inl) ∘ Sum.inr) i))).eval
              ((complexToRealPi Unit).symm (u ∘ Sum.inr) ())) ↔ u ∈ B_DG k := by
    simp [B_DG, Eq_DG, U_cyl, hu]
  rw [hAHP, hBDG, imp_iff_mem_compl_union]

/-- Upgrading a complex Weierstrass division at `(z₀, 0)` to `IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_weierstrassDivision_zero {σ : Type*} [Fintype σ]
    {G q : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {d : ℕ} {c r : Fin d → (σ → ℂ) → ℂ}
    (hG : IsHolomorphicNashAt G (Sum.elim z₀ 0))
    (hc : ∀ i, IsHolomorphicNashAt (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    (hq : AnalyticAt ℂ q (Sum.elim z₀ 0)) (hr : ∀ i, AnalyticAt ℂ (r i) z₀)
    (hdiv : G =ᶠ[𝓝 (Sum.elim z₀ 0)] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ())) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * p (.inr ()) ^ (i : ℕ)) :
    IsHolomorphicNashAt q (Sum.elim z₀ 0) ∧ ∀ i, IsHolomorphicNashAt (r i) z₀ := by
  let eσ := complexToRealPi σ
  let ed := complexToRealPi (Fin d)
  let DG : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ := fun j p ↦
    iteratedDeriv (j : ℕ) (fun w ↦ G (Sum.elim (p ∘ Sum.inl) (fun _ ↦ w))) (p (.inr ()))
  let HP : Fin (d + 1) → (σ ⊕ Unit → ℂ) → ℂ := fun j p ↦
    (hasseDeriv (j : ℕ) (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl)))).eval (p (.inr ()))
  obtain ⟨R, B_X, hR, hBX_open, hzBX, hBX_semi, hc_bound, hprop, W, hHW, hsub⟩ :=
    exists_isolating_cylinder (H := Sum.elim DG HP) (fun i ↦ (hc i).analyticAt) hc0
      (by
        rintro (j | j)
        · exact hG.iteratedDeriv_vertical (j : ℕ)
        · exact isHolomorphicNashAt_eval_hasseDeriv_monicOfCoeff hc (j : ℕ))
      ((hG.analyticAt.eventually_analyticAt.and hq.eventually_analyticAt).and hdiv)
  have hjet (x_ℝ : σ ⊕ σ → ℝ) (hx : x_ℝ ∈ B_X) (w : ℂ) (hw : w ∈ ball (0 : ℂ) R)
      (k : Fin (d + 1)) :=
    jet_eq_of_weierstrassDivision hw (hprop x_ℝ hx w hw).1.1 (hprop x_ℝ hx w hw).1.2
      (fun w' hw' ↦ by simpa only [Sum.elim_comp_inl, Sum.elim_inr] using (hprop x_ℝ hx w' hw').2) k
  have hr_semi : IsSemialgebraicOn (fun x_ℝ ↦ ed (fun i ↦ r i (eσ.symm x_ℝ))) B_X := by
    rw [isSemialgebraicOn_iff_graph]
    convert (hBX_semi.preimage_comp Sum.inl).inter
      (isSemialgebraic_divElimSet hBX_semi hHW hsub).setOf_forall_sumElim using 1
    ext v
    rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    refine and_congr_right fun hvBX ↦ ?_
    rw [← ContinuousLinearEquiv.eq_symm_apply]
    refine ⟨fun hvr w_ℝ ⟨_, hwD⟩ k hP0 j ↦ ?_,
      fun hall ↦ symm <| eq_of_sum_monomial_forall_hasseDeriv_eq
        (fun w hw ↦ mem_ball_of_isRoot_monicOfCoeff hR (hc_bound _ hvBX) hw)
        (fun w hw k hP0 j ↦ ?_)⟩
    · have hvr' : ∀ i, (complexToRealPi (Fin d)).symm (v ∘ Sum.inr) i =
          r i (eσ.symm (v ∘ Sum.inl)) := fun i ↦ (congrFun hvr i).symm
      simp only [hvr']
      exact hjet _ hvBX _ ((mem_realDiskSet_iff hR w_ℝ).1 hwD) k hP0 j
    · let w_ℝ := complexToRealPi Unit (fun _ ↦ w)
      have hw_eq : (complexToRealPi Unit).symm w_ℝ () = w := by simp [w_ℝ]
      have hwD : w_ℝ ∈ realDiskSet R := (mem_realDiskSet_iff hR w_ℝ).2 (hw_eq.symm ▸ hw)
      have h2 := hall w_ℝ ⟨hvBX, hwD⟩ k
      rw [hw_eq] at h2
      exact mul_left_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (j : ℕ)))
        ((h2 hP0 j).symm.trans (hjet _ hvBX w hw k hP0 j))
  have hr_nash := isHolomorphicNashAt_of_isSemialgebraicOn hr hBX_open hzBX hr_semi
  exact ⟨(isHolomorphicNashAt_eval_monicOfCoeff hc).of_mul_eventuallyEq
    (hG.sub (isHolomorphicNashAt_sum_mul_pow hr_nash)) hq
    (not_eventuallyEq_zero_eval_monicOfCoeff hc0) (hdiv.mono fun _ hp ↦ eq_sub_of_add_eq hp.symm),
    hr_nash⟩

/-- Vertical coordinate translation `p ↦ Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (.inr ()) + c₀)`. -/
private def verticalShift {σ : Type*} (c₀ : ℂ) (p : σ ⊕ Unit → ℂ) : σ ⊕ Unit → ℂ :=
  Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (.inr ()) + c₀)

private theorem isHolomorphicNashAt_verticalShift {σ : Type*} [Fintype σ]
    (c₀ : ℂ) (z₀ : σ ⊕ Unit → ℂ) (k : σ ⊕ Unit) :
    IsHolomorphicNashAt (fun p ↦ verticalShift c₀ p k) z₀ := by
  rcases k with s | ⟨⟩
  · exact isHolomorphicNashAt_apply (Sum.inl s) z₀
  · exact (isHolomorphicNashAt_apply (Sum.inr ()) z₀).add (isHolomorphicNashAt_const c₀ z₀)

private theorem verticalShift_zero_right {σ : Type*} (z₀ : σ → ℂ) (w₀ : ℂ) :
    verticalShift w₀ (Sum.elim z₀ 0) = Sum.elim z₀ (fun _ ↦ w₀) := by
  ext (_ | ⟨⟩) <;> simp [verticalShift]

private theorem verticalShift_neg_self {σ : Type*} (z₀ : σ → ℂ) (w₀ : ℂ) :
    verticalShift (-w₀) (Sum.elim z₀ (fun _ ↦ w₀)) = Sum.elim z₀ 0 := by
  ext (_ | ⟨⟩) <;> simp [verticalShift]

private theorem verticalShift_neg_cancel {σ : Type*} (w₀ : ℂ) (p : σ ⊕ Unit → ℂ) :
    verticalShift w₀ (verticalShift (-w₀) p) = p := by
  ext (_ | ⟨⟩) <;> simp [verticalShift]

/-- Upgrading a complex Weierstrass preparation at `Sum.elim z₀ (fun _ ↦ w₀)` to
`IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_weierstrassPreparation {σ : Type*} [Fintype σ]
    {F u : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {w₀ : ℂ} {d : ℕ} {c : Fin d → (σ → ℂ) → ℂ}
    (hF : IsHolomorphicNashAt F (Sum.elim z₀ (fun _ ↦ w₀)))
    (hc : ∀ i, AnalyticAt ℂ (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    (hu : AnalyticAt ℂ u (Sum.elim z₀ (fun _ ↦ w₀)))
    (hu0 : u (Sum.elim z₀ (fun _ ↦ w₀)) ≠ 0)
    (hfac : F =ᶠ[𝓝 (Sum.elim z₀ (fun _ ↦ w₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - w₀) * u p) :
    (∀ i, IsHolomorphicNashAt (c i) z₀) ∧ IsHolomorphicNashAt u (Sum.elim z₀ (fun _ ↦ w₀)) := by
  have hshift0 := verticalShift_zero_right z₀ w₀
  have hshift_an : AnalyticAt ℂ (verticalShift w₀) (Sum.elim z₀ 0) :=
    AnalyticAt.pi fun k ↦ (isHolomorphicNashAt_verticalShift w₀ (Sum.elim z₀ 0) k).analyticAt
  have hF0 : IsHolomorphicNashAt (F ∘ verticalShift w₀) (Sum.elim z₀ 0) :=
    (hshift0.symm ▸ hF).comp (isHolomorphicNashAt_verticalShift w₀ _)
  have hT : Tendsto (verticalShift w₀) (𝓝 (Sum.elim z₀ 0)) (𝓝 (Sum.elim z₀ (fun _ ↦ w₀))) :=
    hshift0 ▸ hshift_an.continuousAt.tendsto
  obtain ⟨hc_nash, hu0_nash⟩ := isHolomorphicNashAt_of_weierstrassPreparation_zero hF0 hc hc0
    (hu.comp_of_eq hshift_an hshift0) (by simpa only [Function.comp_apply, hshift0] using hu0)
    ((hT.eventually hfac).mono fun p hp ↦ by simpa [verticalShift, Function.comp_def] using hp)
  have hu_nash := ((verticalShift_neg_self z₀ w₀).symm ▸ hu0_nash).comp
    (isHolomorphicNashAt_verticalShift (-w₀) (Sum.elim z₀ (fun _ ↦ w₀)))
  exact ⟨hc_nash, hu_nash.congr (.of_forall fun _ ↦ by simp [verticalShift_neg_cancel])⟩

/-- Upgrading a complex Weierstrass division at `Sum.elim z₀ (fun _ ↦ w₀)` to
`IsHolomorphicNashAt`. -/
private theorem isHolomorphicNashAt_of_weierstrassDivision {σ : Type*} [Fintype σ]
    {G q : (σ ⊕ Unit → ℂ) → ℂ} {z₀ : σ → ℂ} {w₀ : ℂ} {d : ℕ} {c r : Fin d → (σ → ℂ) → ℂ}
    (hG : IsHolomorphicNashAt G (Sum.elim z₀ (fun _ ↦ w₀)))
    (hc : ∀ i, IsHolomorphicNashAt (c i) z₀) (hc0 : ∀ i, c i z₀ = 0)
    (hq : AnalyticAt ℂ q (Sum.elim z₀ (fun _ ↦ w₀)))
    (hr : ∀ i, AnalyticAt ℂ (r i) z₀)
    (hdiv : G =ᶠ[𝓝 (Sum.elim z₀ (fun _ ↦ w₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - w₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - w₀) ^ (i : ℕ)) :
    IsHolomorphicNashAt q (Sum.elim z₀ (fun _ ↦ w₀)) ∧ ∀ i, IsHolomorphicNashAt (r i) z₀ := by
  have hshift0 := verticalShift_zero_right z₀ w₀
  have hshift_an : AnalyticAt ℂ (verticalShift w₀) (Sum.elim z₀ 0) :=
    AnalyticAt.pi fun k ↦ (isHolomorphicNashAt_verticalShift w₀ (Sum.elim z₀ 0) k).analyticAt
  have hG0 : IsHolomorphicNashAt (G ∘ verticalShift w₀) (Sum.elim z₀ 0) :=
    (hshift0.symm ▸ hG).comp (isHolomorphicNashAt_verticalShift w₀ _)
  have hT : Tendsto (verticalShift w₀) (𝓝 (Sum.elim z₀ 0)) (𝓝 (Sum.elim z₀ (fun _ ↦ w₀))) :=
    hshift0 ▸ hshift_an.continuousAt.tendsto
  obtain ⟨hq0_nash, hr_nash⟩ := isHolomorphicNashAt_of_weierstrassDivision_zero hG0 hc hc0
    (hq.comp_of_eq hshift_an hshift0) hr
    ((hT.eventually hdiv).mono fun p hp ↦ by simpa [verticalShift, Function.comp_def] using hp)
  have hq_nash := ((verticalShift_neg_self z₀ w₀).symm ▸ hq0_nash).comp
    (isHolomorphicNashAt_verticalShift (-w₀) (Sum.elim z₀ (fun _ ↦ w₀)))
  exact ⟨hq_nash.congr (.of_forall fun _ ↦ by simp [verticalShift_neg_cancel]), hr_nash⟩

end ComplexWeierstrassUpgrade

/-! ### Real Nash Weierstrass preparation and division -/

section RealNashWeierstrass

variable {σ : Type*} [Fintype σ]

private theorem complexify_nash {τ : Type*} [Fintype τ] {f : (τ → ℝ) → ℝ} {x₀ : τ → ℝ}
    (hf : IsNashAt f x₀) :
    ∃ F : (τ → ℂ) → ℂ, IsHolomorphicNashAt F (fun j ↦ (x₀ j : ℂ)) ∧
      ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y := by
  obtain ⟨r, hr, F, hF, hFf, _⟩ := hf.analyticAt.exists_complexification
  have hF_an : AnalyticAt ℂ F (fun j ↦ (x₀ j : ℂ)) := hF _ (mem_ball_self hr)
  have hFf' : ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y :=
    eventually_of_mem (ball_mem_nhds x₀ hr) hFf
  obtain ⟨hre, him⟩ := hf.complexification_re_im hF_an hFf'
  exact ⟨F, ⟨hF_an, hre, him⟩, hFf'⟩

private theorem complexify_analytic {τ : Type*} [Fintype τ] {f : (τ → ℝ) → ℝ} {x₀ : τ → ℝ}
    (hf : AnalyticAt ℝ f x₀) :
    ∃ F : (τ → ℂ) → ℂ, AnalyticAt ℂ F (fun j ↦ (x₀ j : ℂ)) ∧
      ∀ᶠ y in 𝓝 x₀, F (fun j ↦ (y j : ℂ)) = f y := by
  obtain ⟨r, hr, F, hF, hFf, _⟩ := hf.exists_complexification
  exact ⟨F, hF _ (mem_ball_self hr), eventually_of_mem (ball_mem_nhds x₀ hr) hFf⟩

private theorem analyticAt_sum_mul_sub_pow_sumElim {d : ℕ} {B : Fin d → (σ → ℂ) → ℂ}
    {z₀ : σ → ℂ} {w₀ : ℂ} (hB : ∀ i, AnalyticAt ℂ (B i) z₀) :
    AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦
      ∑ i : Fin d, B i (p ∘ Sum.inl) * (p (.inr ()) - w₀) ^ (i : ℕ))
      (Sum.elim z₀ (fun _ ↦ w₀)) := by
  have hw : AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦ p (.inr ()) - w₀) (Sum.elim z₀ (fun _ ↦ w₀)) :=
    ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : σ ⊕ Unit ↦ ℂ) (Sum.inr ())).analyticAt _).fun_sub analyticAt_const
  have hsum : AnalyticAt ℂ
      (∑ i : Fin d, fun p : σ ⊕ Unit → ℂ ↦ B i (p ∘ Sum.inl) * (p (.inr ()) - w₀) ^ (i : ℕ))
      (Sum.elim z₀ (fun _ ↦ w₀)) :=
    Finset.sum_induction _ (fun g ↦ AnalyticAt ℂ g (Sum.elim z₀ (fun _ ↦ w₀)))
      (fun _ _ ↦ .add) analyticAt_const fun i _ ↦
        ((hB i).comp_of_eq (AnalyticAt.pi fun s ↦
          (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : σ ⊕ Unit ↦ ℂ) (Sum.inl s)).analyticAt _)
          rfl).fun_mul (hw.fun_pow (i : ℕ))
  exact hsum.congr (.of_forall fun _ ↦ by simp)

private theorem analyticAt_eval_monicOfCoeff_sumElim {d : ℕ} {C : Fin d → (σ → ℂ) → ℂ}
    {z₀ : σ → ℂ} {w₀ : ℂ} (hC : ∀ i, AnalyticAt ℂ (C i) z₀) :
    AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval (p (.inr ()) - w₀))
      (Sum.elim z₀ (fun _ ↦ w₀)) := by
  have hw : AnalyticAt ℂ (fun p : σ ⊕ Unit → ℂ ↦ p (.inr ()) - w₀) (Sum.elim z₀ (fun _ ↦ w₀)) :=
    ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : σ ⊕ Unit ↦ ℂ) (Sum.inr ())).analyticAt _).fun_sub analyticAt_const
  exact ((hw.fun_pow d).fun_add (analyticAt_sum_mul_sub_pow_sumElim hC)).congr
    (.of_forall fun _ ↦ (Polynomial.eval_monicOfCoeff _ _).symm)

/-- **Nash upgrading of a real Weierstrass preparation.** If `f : (σ ⊕ Unit → ℝ) → ℝ` is a Nash
germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)` and `f = P_c * u` is a real analytic Weierstrass
preparation of `f` at `p₀`, then the coefficient germs `c i` are Nash at `x₀` and the unit `u` is
Nash at `p₀`. -/
theorem IsNashAt.of_weierstrassPreparation {f u : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, AnalyticAt ℝ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hu : AnalyticAt ℝ u (Sum.elim x₀ (fun _ ↦ t₀)))
    (hu0 : u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0)
    (hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p) :
    (∀ i, IsNashAt (c i) x₀) ∧ IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) := by
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let z₀ : σ → ℂ := fun s ↦ (x₀ s : ℂ)
  have hp₀_eq : (fun k ↦ (p₀ k : ℂ)) = Sum.elim z₀ (fun _ ↦ (t₀ : ℂ)) := by ext (_ | ⟨⟩) <;> rfl
  obtain ⟨F, hF, hFf⟩ := complexify_nash hf
  obtain ⟨U, hU, hUu⟩ := complexify_analytic hu
  choose C hC hCc using fun i ↦ complexify_analytic (hc i)
  have hC0 (i : Fin d) : C i z₀ = 0 := by
    rw [(hCc i).self_of_nhds, hc0 i, Complex.ofReal_zero]
  have hU0 : U (Sum.elim z₀ (fun _ ↦ (t₀ : ℂ))) ≠ 0 := by
    rw [← hp₀_eq, hUu.self_of_nhds]; exact_mod_cast hu0
  have hinl : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) (𝓝 p₀) (𝓝 x₀) :=
    (continuous_pi fun s ↦ continuous_apply (Sum.inl s)).tendsto p₀
  have hC_ev : ∀ᶠ x in 𝓝 x₀, ∀ i, C i (fun s ↦ (x s : ℂ)) = c i x := eventually_all.2 hCc
  have hfac_C : F =ᶠ[𝓝 (Sum.elim z₀ (fun _ ↦ (t₀ : ℂ)))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval
        (p (.inr ()) - (t₀ : ℂ)) * U p := by
    rw [← hp₀_eq]
    refine hF.analyticAt.eventuallyEq_of_eventually_real
      (hp₀_eq ▸ ((analyticAt_eval_monicOfCoeff_sumElim hC).fun_mul (hp₀_eq ▸ hU))) ?_
    filter_upwards [hFf, hfac, hUu, hinl.eventually hC_ev] with p hFp hp hUp hCp
    have hinl_eq : ((fun k ↦ (p k : ℂ)) ∘ Sum.inl) = fun s ↦ (p (Sum.inl s) : ℂ) := rfl
    have hCp' (i : Fin d) : C i (fun s ↦ (p (Sum.inl s) : ℂ)) = c i (p ∘ Sum.inl) := hCp i
    rw [hFp]
    simp only [Polynomial.eval_monicOfCoeff] at hp ⊢
    simp only [hinl_eq, hCp', hUp]
    exact_mod_cast hp
  obtain ⟨hC_nash, hU_nash⟩ :=
    isHolomorphicNashAt_of_weierstrassPreparation (hp₀_eq ▸ hF) hC hC0 (hp₀_eq ▸ hU) hU0 hfac_C
  exact ⟨fun i ↦ (hC_nash i).isNashAt_of_eventually_real (hCc i),
    (hp₀_eq.symm ▸ hU_nash).isNashAt_of_eventually_real hUu⟩

private noncomputable def finJoin (q : (Fin (Fintype.card σ) → ℝ) × ℝ) : σ ⊕ Unit → ℝ :=
  Sum.elim (q.1 ∘ Fintype.equivFin σ) (fun _ ↦ q.2)

private noncomputable def finSplit (p : σ ⊕ Unit → ℝ) : (Fin (Fintype.card σ) → ℝ) × ℝ :=
  ((p ∘ Sum.inl) ∘ (Fintype.equivFin σ).symm, p (.inr ()))

private theorem analyticAt_finJoin (y₀ : Fin (Fintype.card σ) → ℝ) (t₀ : ℝ) :
    AnalyticAt ℝ (finJoin (σ := σ)) (y₀, t₀) :=
  AnalyticAt.pi fun k ↦ by
    rcases k with s | ⟨⟩
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ)
        (Fintype.equivFin σ s)).analyticAt _).comp_of_eq analyticAt_fst rfl
    · exact analyticAt_snd

private theorem analyticAt_finSplit (p₀ : σ ⊕ Unit → ℝ) :
    AnalyticAt ℝ (finSplit (σ := σ)) p₀ :=
  (AnalyticAt.pi fun j ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ)
      (Sum.inl ((Fintype.equivFin σ).symm j))).analyticAt _).prod
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ⊕ Unit ↦ ℝ) (Sum.inr ())).analyticAt _)

private theorem finJoin_finSplit (p : σ ⊕ Unit → ℝ) : finJoin (finSplit p) = p := by
  ext k; rcases k with s | ⟨⟩ <;> simp [finJoin, finSplit]

/-- **Nash Weierstrass preparation theorem.** Let `f : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` has finite order of vanishing `d` at `t₀`. Then there exist Nash
coefficient germs `c : Fin d → (σ → ℝ) → ℝ` vanishing at `x₀` and a Nash germ `u` nonvanishing at
`p₀` such that near `p₀`,
`f p = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval`
`  (p (.inr ()) - t₀) * u p`. -/
theorem IsNashAt.exists_weierstrassPreparation {f : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (c : Fin d → (σ → ℝ) → ℝ) (u : (σ ⊕ Unit → ℝ) → ℝ),
      (∀ i, IsNashAt (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      IsNashAt u (Sum.elim x₀ (fun _ ↦ t₀)) ∧ u (Sum.elim x₀ (fun _ ↦ t₀)) ≠ 0 ∧
      f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hjoin_x₀ (t : ℝ) : finJoin (x₀ ∘ e.symm, t) = Sum.elim x₀ (fun _ ↦ t) := by
    ext k; rcases k with s | ⟨⟩ <;> simp [finJoin, e]
  have hf_prod : AnalyticAt ℝ (f ∘ finJoin) (x₀ ∘ e.symm, t₀) :=
    hf.analyticAt.comp_of_eq (analyticAt_finJoin (x₀ ∘ e.symm) t₀) (hjoin_x₀ t₀)
  have hd_prod : analyticOrderAt (fun t ↦ (f ∘ finJoin) (x₀ ∘ e.symm, t)) t₀ = d := by
    simpa only [Function.comp_apply, hjoin_x₀] using hd
  obtain ⟨c', u', hc', hc'0, hu', hu'0, hfac'⟩ := hf_prod.exists_weierstrassPreparation_real hd_prod
  let c : Fin d → (σ → ℝ) → ℝ := fun i x ↦ c' i (x ∘ e.symm)
  let u : (σ ⊕ Unit → ℝ) → ℝ := u' ∘ finSplit
  have hc_an (i : Fin d) : AnalyticAt ℝ (c i) x₀ :=
    (hc' i).comp_of_eq (AnalyticAt.pi fun j ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) (e.symm j)).analyticAt x₀) rfl
  have hsplit_an := analyticAt_finSplit (Sum.elim x₀ (fun _ ↦ t₀))
  have hfac : f =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * u p := by
    filter_upwards [hsplit_an.continuousAt.tendsto.eventually hfac'] with p hp
    rw [Function.comp_apply, finJoin_finSplit] at hp
    simpa only [Function.comp_apply, c, u, finSplit, e] using hp
  obtain ⟨hc_nash, hu_nash⟩ :=
    hf.of_weierstrassPreparation hc_an (fun i ↦ hc'0 i) (hu'.comp_of_eq hsplit_an rfl) hu'0 hfac
  exact ⟨c, u, hc_nash, fun i ↦ hc'0 i, hu_nash, hu'0, hfac⟩

/-- **Nash upgrading of a real Weierstrass division by a Weierstrass polynomial.** If
`g : (σ ⊕ Unit → ℝ) → ℝ` is a Nash germ at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, `c : Fin d → (σ → ℝ) →
ℝ` are Nash germs vanishing at `x₀`, and `g = P_c * q + ∑ i, r i * (t - t₀) ^ i` is a real analytic
Weierstrass division at `p₀`, then `q` is Nash at `p₀` and every `r i` is Nash at `x₀`. -/
theorem IsNashAt.of_weierstrassDivision_monicOfCoeff {g q : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {c r : Fin d → (σ → ℝ) → ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀)))
    (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) :
    IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ ∀ i, IsNashAt (r i) x₀ := by
  let p₀ : σ ⊕ Unit → ℝ := Sum.elim x₀ (fun _ ↦ t₀)
  let z₀ : σ → ℂ := fun s ↦ (x₀ s : ℂ)
  have hp₀_eq : (fun k ↦ (p₀ k : ℂ)) = Sum.elim z₀ (fun _ ↦ (t₀ : ℂ)) := by ext (_ | ⟨⟩) <;> rfl
  obtain ⟨G, hG, hGg⟩ := complexify_nash hg
  choose C hC hCc using fun i ↦ complexify_nash (hc i)
  obtain ⟨Q, hQ, hQq⟩ := complexify_analytic hq
  choose R hR hRr using fun i ↦ complexify_analytic (hr i)
  have hC0 (i : Fin d) : C i z₀ = 0 := by
    rw [(hCc i).self_of_nhds, hc0 i, Complex.ofReal_zero]
  have hinl : Tendsto (fun p : σ ⊕ Unit → ℝ ↦ p ∘ Sum.inl) (𝓝 p₀) (𝓝 x₀) :=
    (continuous_pi fun s ↦ continuous_apply (Sum.inl s)).tendsto p₀
  have hC_ev : ∀ᶠ x in 𝓝 x₀, ∀ i, C i (fun s ↦ (x s : ℂ)) = c i x := eventually_all.2 hCc
  have hR_ev : ∀ᶠ x in 𝓝 x₀, ∀ i, R i (fun s ↦ (x s : ℂ)) = r i x := eventually_all.2 hRr
  have hdiv_C : G =ᶠ[𝓝 (Sum.elim z₀ (fun _ ↦ (t₀ : ℂ)))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ C i (p ∘ Sum.inl))).eval (p (.inr ()) - (t₀ : ℂ)) * Q p +
        ∑ i : Fin d, R i (p ∘ Sum.inl) * (p (.inr ()) - (t₀ : ℂ)) ^ (i : ℕ) := by
    rw [← hp₀_eq]
    refine hG.analyticAt.eventuallyEq_of_eventually_real
      (hp₀_eq ▸ (((analyticAt_eval_monicOfCoeff_sumElim fun i ↦ (hC i).analyticAt).fun_mul
        (hp₀_eq ▸ hQ)).fun_add (analyticAt_sum_mul_sub_pow_sumElim hR))) ?_
    filter_upwards [hGg, hdiv, hQq, hinl.eventually hC_ev, hinl.eventually hR_ev]
      with p hGp hp hQp hCp hRp
    have hinl_eq : ((fun k ↦ (p k : ℂ)) ∘ Sum.inl) = fun s ↦ (p (Sum.inl s) : ℂ) := rfl
    have hCp' (i : Fin d) : C i (fun s ↦ (p (Sum.inl s) : ℂ)) = c i (p ∘ Sum.inl) := hCp i
    have hRp' (i : Fin d) : R i (fun s ↦ (p (Sum.inl s) : ℂ)) = r i (p ∘ Sum.inl) := hRp i
    rw [hGp]
    simp only [Polynomial.eval_monicOfCoeff] at hp ⊢
    simp only [hinl_eq, hCp', hQp, hRp']
    exact_mod_cast hp
  obtain ⟨hQ_nash, hR_nash⟩ :=
    isHolomorphicNashAt_of_weierstrassDivision (hp₀_eq ▸ hG) hC hC0 (hp₀_eq ▸ hQ) hR hdiv_C
  exact ⟨(hp₀_eq.symm ▸ hQ_nash).isNashAt_of_eventually_real hQq,
    fun i ↦ (hR_nash i).isNashAt_of_eventually_real (hRr i)⟩

/-- **Nash Weierstrass division by a Weierstrass polynomial.** Let `c : Fin d → (σ → ℝ) → ℝ` be Nash
germs at `x₀` with `c i x₀ = 0`, with `σ` finite, and let `g : (σ ⊕ Unit → ℝ) → ℝ` be a Nash germ
at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`. Then there exist a Nash germ `q` at `p₀` and Nash germs
`r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval`
`  (p (.inr ()) - t₀) * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision_monicOfCoeff {g : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hc : ∀ i, IsNashAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
          ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hjoin_x₀ : finJoin (x₀ ∘ e.symm, t₀) = Sum.elim x₀ (fun _ ↦ t₀) := by
    ext k; rcases k with s | ⟨⟩ <;> simp [finJoin, e]
  have hg_prod : AnalyticAt ℝ (g ∘ finJoin) (x₀ ∘ e.symm, t₀) :=
    hg.analyticAt.comp_of_eq (analyticAt_finJoin (x₀ ∘ e.symm) t₀) hjoin_x₀
  have hc_fin (i : Fin d) : AnalyticAt ℝ (fun y ↦ c i (y ∘ e)) (x₀ ∘ e.symm) :=
    (hc i).analyticAt.comp_of_eq (AnalyticAt.pi fun s ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) (e s)).analyticAt _) (by ext; simp)
  have hc0_fin (i : Fin d) : c i ((x₀ ∘ e.symm) ∘ e) = 0 := by
    have hx : (x₀ ∘ e.symm) ∘ e = x₀ := by ext; simp
    rw [hx]; exact hc0 i
  obtain ⟨q', r', hq', hr', hdiv'⟩ :=
    hg_prod.exists_weierstrassDivision_monicOfCoeff_real hc_fin hc0_fin
  let q : (σ ⊕ Unit → ℝ) → ℝ := q' ∘ finSplit
  let r : Fin d → (σ → ℝ) → ℝ := fun i x ↦ r' i (x ∘ e.symm)
  have hsplit_an := analyticAt_finSplit (Sum.elim x₀ (fun _ ↦ t₀))
  have hr_an (i : Fin d) : AnalyticAt ℝ (r i) x₀ :=
    (hr' i).comp_of_eq (AnalyticAt.pi fun j ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) (e.symm j)).analyticAt x₀) rfl
  have hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      (Polynomial.monicOfCoeff (fun i ↦ c i (p ∘ Sum.inl))).eval (p (.inr ()) - t₀) * q p +
        ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
    filter_upwards [hsplit_an.continuousAt.tendsto.eventually hdiv'] with p hp
    have hinl : ((p ∘ Sum.inl) ∘ e.symm) ∘ e = p ∘ Sum.inl := by ext; simp
    rw [Function.comp_apply, finJoin_finSplit] at hp
    simpa only [Function.comp_apply, hinl, q, r, finSplit, e] using hp
  obtain ⟨hq_nash, hr_nash⟩ :=
    hg.of_weierstrassDivision_monicOfCoeff hc hc0 (hq'.comp_of_eq hsplit_an rfl) hr_an hdiv
  exact ⟨q, r, hq_nash, hr_nash, hdiv⟩

/-- **Nash upgrading of a general real Weierstrass division.** Let `f, g : (σ ⊕ Unit → ℝ) → ℝ` be
Nash germs at `p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with vertical slice of `f` of finite order `d` at
`t₀`. If `g = f * q + ∑ i : Fin d, r i * (t - t₀) ^ i` is a real analytic Weierstrass division at
`p₀`, then `q` is Nash at `p₀` and every `r i` is Nash at `x₀`. -/
theorem IsNashAt.of_weierstrassDivision {f g q : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ} {r : Fin d → (σ → ℝ) → ℝ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d)
    (hq : AnalyticAt ℝ q (Sum.elim x₀ (fun _ ↦ t₀)))
    (hr : ∀ i, AnalyticAt ℝ (r i) x₀)
    (hdiv : g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
      f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)) :
    IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ ∀ i, IsNashAt (r i) x₀ := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨huq, hr_nash⟩ := hg.of_weierstrassDivision_monicOfCoeff hc hc0 (hu.analyticAt.mul hq) hr
    (by filter_upwards [hdiv, hprep] with p hp hfp; rw [hp, hfp, mul_assoc, Pi.mul_apply])
  exact ⟨(huq.div hu hu0).congr ((hu.analyticAt.continuousAt.eventually_ne hu0).mono fun p hup ↦ by
    simp [mul_div_cancel_left₀ _ hup]), hr_nash⟩

/-- **Nash Weierstrass division theorem.** Let `f, g : (σ ⊕ Unit → ℝ) → ℝ` be Nash germs at
`p₀ = Sum.elim x₀ (fun _ ↦ t₀)`, with `σ` finite, and suppose the vertical slice
`t ↦ f (Sum.elim x₀ (fun _ ↦ t))` has finite order of vanishing `d` at `t₀`. Then there exist a Nash
germ `q` at `p₀` and Nash germs `r : Fin d → (σ → ℝ) → ℝ` at `x₀` such that near `p₀`,
`g p = f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ)`. -/
theorem IsNashAt.exists_weierstrassDivision {f g : (σ ⊕ Unit → ℝ) → ℝ}
    {x₀ : σ → ℝ} {t₀ : ℝ} {d : ℕ}
    (hg : IsNashAt g (Sum.elim x₀ (fun _ ↦ t₀)))
    (hf : IsNashAt f (Sum.elim x₀ (fun _ ↦ t₀)))
    (hd : analyticOrderAt (fun t ↦ f (Sum.elim x₀ (fun _ ↦ t))) t₀ = d) :
    ∃ (q : (σ ⊕ Unit → ℝ) → ℝ) (r : Fin d → (σ → ℝ) → ℝ),
      IsNashAt q (Sum.elim x₀ (fun _ ↦ t₀)) ∧ (∀ i, IsNashAt (r i) x₀) ∧
      g =ᶠ[𝓝 (Sum.elim x₀ (fun _ ↦ t₀))] fun p ↦
        f p * q p + ∑ i : Fin d, r i (p ∘ Sum.inl) * (p (.inr ()) - t₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff hc hc0
  refine ⟨q₀ / u, r, hq₀.div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.analyticAt.continuousAt.eventually_ne hu0] with p hp hgp hup
  simp only [Pi.div_apply, hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end RealNashWeierstrass

end TauCeti
