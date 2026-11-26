/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Analysis.Complex.Conformal.Hurwitz
public import TauCeti.Analysis.MvPolynomial.Hyperbolic

/-!
# Hyperbolicity in every direction of the Gårding cone

Let `p` be a real polynomial, hyperbolic of degree `m` in the direction `a`
(`MvPolynomial.IsHyperbolic`). This file proves the part of Gårding's theorem that concerns the
directions of hyperbolicity: for every `b` in the Gårding cone `Γ(p, a)`, the polynomial `p` is
hyperbolic of degree `m` in the direction `b` (`MvPolynomial.IsHyperbolic.of_mem_gardingCone`),
and `Γ(p, b) = Γ(p, a)` (`MvPolynomial.IsHyperbolic.gardingCone_eq_of_mem`). Consequently the
Gårding cone is convex (`MvPolynomial.IsHyperbolic.convex_gardingCone`): for `x, y ∈ Γ(p, a)` the
cone `Γ(p, x) = Γ(p, a)` is star-convex with respect to `x`. None of these needs `m ≥ 1`.

The proof works with the complexification of `p`. Hyperbolicity in `a` says that `p` has no zero
at `y + t • a` for real `y` and non-real `t`
(`MvPolynomial.IsHyperbolic.eval_map_ofReal_add_smul_ne_zero`). For real `x`, consider the
polynomials `z ↦ p(λ • x + i • a + z • b)`, `λ ∈ ℝ`. They have no zero on the real axis, by the
previous remark, and at `λ = 0` none in the closed upper half-plane, since `b ∈ Γ(p, a)`. The set of
`λ` for which there is no zero in the closed upper half-plane is open, by compactness after
inverting large `z` through homogeneity, and closed, by Hurwitz's theorem
(`TauCeti.hurwitz_forall_ne`). So it is all of `ℝ`; scaling and a second application of Hurwitz's
theorem, as the coefficient of `i • a` tends to `0`, show that `z ↦ p(x + z • b)` has no zero in the
open upper half-plane, hence, by conjugation, only real roots. For the cones, `Γ(p, a)` is
connected and meets the open cone `Γ(p, b)`, and Hurwitz's theorem shows that a limit point of
`Γ(p, b)` inside `Γ(p, a)` lies in `Γ(p, b)`.

## Main results

* `MvPolynomial.IsHyperbolic.eval_map_ofReal_add_smul_ne_zero`: a hyperbolic polynomial has no
  complex zero off the real axis on a line in its direction.
* `MvPolynomial.IsHyperbolic.of_mem_gardingCone`: `p` is hyperbolic in every direction of
  `Γ(p, a)`.
* `MvPolynomial.IsHyperbolic.gardingCone_eq_of_mem`: `Γ(p, b) = Γ(p, a)` for `b ∈ Γ(p, a)`.
* `MvPolynomial.IsHyperbolic.convex_gardingCone`: the Gårding cone is convex.

## References

* L. Gårding, *An inequality for hyperbolic polynomials*, J. Math. Mech. 8 (1959), 957–965.
* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2, Theorem 2.2.
-/

public section

open Complex Filter Set Topology

namespace MvPolynomial

variable {σ : Type*} {p : MvPolynomial σ ℝ} {m : ℕ} {a b : σ → ℝ}

/-- Evaluating the complexification of a real polynomial at a real point gives the real value. -/
private theorem eval_map_ofReal (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    eval (fun j ↦ (x j : ℂ)) (p.map ofRealHom) = (eval x p : ℂ) := by
  rw [eval_map, ← coe_eval₂Hom, eval, coe_eval₂Hom]
  exact (eval₂_comp_left ofRealHom (RingHom.id ℝ) x p).symm

/-- The complexified restriction of a real polynomial to the line through `y` in the direction
`v`, evaluated at `t : ℂ`, is the complexified polynomial at `y + t • v`. -/
private theorem eval_map_aeval_C_add_C_mul_X (p : MvPolynomial σ ℝ) (y v : σ → ℝ) (t : ℂ) :
    ((aeval (fun i ↦ Polynomial.C (y i) + Polynomial.C (v i) * Polynomial.X) p).map
      ofRealHom).eval t = eval ((fun j ↦ (y j : ℂ)) + t • fun j ↦ (v j : ℂ)) (p.map ofRealHom) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Polynomial.map_mul, Polynomial.eval_mul, hp, map_X, eval_X,
      Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, ofRealHom_eq_coe]
    ring

/-- The complexification of a real polynomial commutes with complex conjugation. -/
private theorem eval_map_ofReal_conj (p : MvPolynomial σ ℝ) (v : σ → ℂ) :
    eval (fun j ↦ (starRingEnd ℂ) (v j)) (p.map ofRealHom) =
      (starRingEnd ℂ) (eval v (p.map ofRealHom)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  ext r
  simp

/-- **No complex roots off the real axis.** If `p` is hyperbolic in the direction `a`, then for a
real point `y` and a non-real `t`, the complexification of `p` does not vanish at `y + t • a`. -/
theorem IsHyperbolic.eval_map_ofReal_add_smul_ne_zero (hp : IsHyperbolic p m a) (y : σ → ℝ)
    {t : ℂ} (ht : t.im ≠ 0) :
    eval ((fun j ↦ (y j : ℂ)) + t • fun j ↦ (a j : ℂ)) (p.map ofRealHom) ≠ 0 := by
  intro h
  have hq0 : aeval (fun i ↦ Polynomial.C (y i) + Polynomial.C (a i) * Polynomial.X) p ≠ 0 :=
    fun h0 ↦ hp.eval_pos.ne' <| by
      rw [← coeff_aeval_C_add_C_mul_X_of_isHomogeneous hp.isHomogeneous y a, h0,
        Polynomial.coeff_zero]
  obtain ⟨r, hr⟩ := (hp.splits y).mem_range_of_isRoot hq0 (i := ofRealHom) (x := t) <| by
    rw [Polynomial.IsRoot.def, eval_map_aeval_C_add_C_mul_X, h]
  exact ht (by rw [← hr]; simp)


/-- A continuous two-variable family `F λ z` converges locally uniformly on every open set as the
parameter `λ` tends to `λ₀`, along any set of parameters. -/
private theorem tendstoLocallyUniformlyOn_of_continuous_uncurry {α : Type*} [TopologicalSpace α]
    {F : α → ℂ → ℂ} (hF : Continuous (Function.uncurry F)) (l₀ : α) (s : Set α) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) :
    TendstoLocallyUniformlyOn F (F l₀) (𝓝[s] l₀) Ω := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ]
  intro K _ hK u hu
  obtain ⟨v, hv, hvu⟩ := hK.mem_uniformity_of_prod (s := univ) hF.continuousOn (mem_univ l₀)
    (symm_le_uniformity hu)
  rw [nhdsWithin_univ] at hv
  exact Filter.mem_of_superset (nhdsWithin_le_nhds hv) fun l hl x hx ↦ hvu l hl x hx

/-- The open upper half-plane is open and preconnected. -/
private theorem isOpen_and_isPreconnected_upperHalfPlane :
    IsOpen {z : ℂ | 0 < z.im} ∧ IsPreconnected {z : ℂ | 0 < z.im} :=
  ⟨isOpen_lt continuous_const continuous_im,
    (convex_halfSpace_gt (f := im) ⟨fun _ _ ↦ add_im _ _, fun _ _ ↦ by simp⟩ 0).isPreconnected⟩

/-- A nonzero complex polynomial does not vanish identically on the open upper half-plane. -/
private theorem exists_im_pos_eval_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    ¬ ∀ z ∈ {z : ℂ | 0 < z.im}, q.eval z = 0 := fun h ↦ hq <| by
  refine Polynomial.eq_zero_of_infinite_isRoot q (Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ ((n : ℂ) + 1) * I) (fun n k hnk ↦ ?_) fun n ↦ h _ ?_)
  · simpa using hnk
  · simp only [mem_ofPred_eq, mul_im, I_re, mul_zero, I_im, mul_one, add_re, natCast_re, one_re]
    positivity

/-- For continuous families `f l z = z ^ m * g l z⁻¹` (`z ≠ 0`) with `g l 0 ≠ 0`, the set of
parameters `l` for which `f l` has no zero in the closed upper half-plane is open: the closed
half-disc of radius `1` and, through `z ↦ z⁻¹`, the closed lower half-disc are compact. -/
private theorem isOpen_setOf_forall_im_nonneg_ne_zero {m : ℕ} {f g : ℝ → ℂ → ℂ}
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g))
    (hfg : ∀ l {z : ℂ}, z ≠ 0 → f l z = z ^ m * g l z⁻¹) (hg0 : ∀ l, g l 0 ≠ 0) :
    IsOpen {l | ∀ z : ℂ, 0 ≤ z.im → f l z ≠ 0} := by
  refine isOpen_iff_eventually.2 fun l₀ hl₀ ↦ ?_
  have hK₁ : IsCompact ({z : ℂ | 0 ≤ z.im} ∩ Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).inter_left (isClosed_le continuous_const continuous_im)
  have hK₂ : IsCompact ({u : ℂ | u.im ≤ 0} ∩ Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).inter_left (isClosed_le continuous_im continuous_const)
  have e₁ := hK₁.eventually_forall_of_forall_eventually (P := fun l z ↦ f l z ≠ 0)
    fun z hz ↦ hf.continuousAt.eventually_ne (x := (l₀, z)) (hl₀ z hz.1)
  have e₂ := hK₂.eventually_forall_of_forall_eventually (P := fun l u ↦ g l u ≠ 0)
    fun u hu ↦ by
    refine hg.continuousAt.eventually_ne (x := (l₀, u)) ?_
    rcases eq_or_ne u 0 with rfl | hu0
    · exact hg0 l₀
    · intro hgu
      refine hl₀ u⁻¹ ?_ (by
        rw [hfg l₀ (inv_ne_zero hu0), inv_inv]
        exact mul_eq_zero_of_right _ hgu)
      rw [inv_im, neg_div, le_neg, neg_zero]
      exact div_nonpos_of_nonpos_of_nonneg hu.1 (normSq_nonneg u)
  filter_upwards [e₁, e₂] with l h₁ h₂ z hz
  by_cases hz1 : ‖z‖ ≤ 1
  · exact h₁ z ⟨hz, mem_closedBall_zero_iff.2 hz1⟩
  · have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
    rw [hfg l hz0]
    refine mul_ne_zero (pow_ne_zero _ hz0) (h₂ z⁻¹ ⟨?_, ?_⟩)
    · rw [mem_ofPred_eq, inv_im, neg_div, neg_nonpos]
      exact div_nonneg hz (normSq_nonneg z)
    · rw [mem_closedBall_zero_iff, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 hz1).le

/-- For a continuous family `f l` of functions holomorphic on the open upper half-plane, none of
them identically zero there and none with a zero on the real axis, the set of parameters `l` for
which `f l` has no zero in the closed upper half-plane is closed, by Hurwitz's theorem. -/
private theorem isClosed_setOf_forall_im_nonneg_ne_zero {f : ℝ → ℂ → ℂ}
    (hf : Continuous (Function.uncurry f)) (hreal : ∀ l {z : ℂ}, z.im = 0 → f l z ≠ 0)
    (hdiff : ∀ l, DifferentiableOn ℂ (f l) {z : ℂ | 0 < z.im})
    (hnc : ∀ l, ¬ ∀ z ∈ {z : ℂ | 0 < z.im}, f l z = 0) :
    IsClosed {l | ∀ z : ℂ, 0 ≤ z.im → f l z ≠ 0} := by
  set S := {l | ∀ z : ℂ, 0 ≤ z.im → f l z ≠ 0}
  refine closure_subset_iff_isClosed.1 fun l hl z hz ↦ ?_
  rcases hz.eq_or_lt with hz0 | hzpos
  · exact hreal l hz0.symm
  have := mem_closure_iff_nhdsWithin_neBot.1 hl
  exact TauCeti.hurwitz_forall_ne isOpen_and_isPreconnected_upperHalfPlane.1
    isOpen_and_isPreconnected_upperHalfPlane.2 (Eventually.of_forall hdiff)
    (tendstoLocallyUniformlyOn_of_continuous_uncurry hf l S
      isOpen_and_isPreconnected_upperHalfPlane.1)
    ((eventually_mem_nhdsWithin (s := S) (a := l)).mono fun l' (hl' : l' ∈ S) z hz ↦
      hl' z (le_of_lt hz)).frequently
    (hnc l) z hzpos

/-- **Zeros persist (Hurwitz).** For a continuous family `G w` of polynomial functions, none of
them zero, a zero `z₀` of `G y` with `y` in the closure of `s` is approached by zeros: every
ball about `z₀` contains a zero of `G w` for some `w ∈ s`. -/
private theorem exists_mem_ball_eq_zero_of_mem_closure {α : Type*} [TopologicalSpace α]
    {G : α → ℂ → ℂ} (hG : Continuous (Function.uncurry G))
    (hpoly : ∀ w, ∃ q : Polynomial ℂ, q ≠ 0 ∧ G w = fun z ↦ q.eval z) {s : Set α} {y : α}
    (hy : y ∈ closure s) {z₀ : ℂ} (hz₀ : G y z₀ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ s, ∃ z ∈ Metric.ball z₀ ε, G w z = 0 := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hy
  have hev := TauCeti.hurwitz_eventually_exists_eq_zero (Ω := univ) isOpen_univ
    isPreconnected_univ (F := G) (g := G y) (l := 𝓝[s] y)
    (Eventually.of_forall fun w ↦ by
      obtain ⟨q, -, hq⟩ := hpoly w
      rw [hq]
      exact Polynomial.differentiable _ |>.differentiableOn)
    (tendstoLocallyUniformlyOn_of_continuous_uncurry hG y _ isOpen_univ) (mem_univ z₀) hz₀
    (fun h ↦ by
      obtain ⟨q, hq0, hq⟩ := hpoly y
      rw [hq] at h
      exact exists_im_pos_eval_ne_zero hq0 fun z _ ↦ h z (mem_univ z)) hε
  obtain ⟨w, ⟨z, ⟨-, hz⟩, hGz⟩, hw⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨w, hw, z, hz, hGz⟩

variable (hp : IsHyperbolic p m a) (hb : b ∈ gardingCone p a)
include hp hb

/-- The restriction of the complexified polynomial to a line in a direction `b` of the Gårding
cone is a nonzero polynomial, with coefficient `p(b)` in degree `m`. -/
private theorem aeval_map_ne_zero (w : σ → ℂ) :
    aeval (fun i ↦ Polynomial.C (w i) + Polynomial.C (b i : ℂ) * Polynomial.X)
      (p.map ofRealHom) ≠ 0 := by
  intro h0
  have h := coeff_aeval_C_add_C_mul_X_of_isHomogeneous (hp.isHomogeneous.map ofRealHom) w
    (fun j ↦ (b j : ℂ))
  rw [h0, Polynomial.coeff_zero, eval_map_ofReal] at h
  exact (eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hb).ne' (by exact_mod_cast h.symm)

/-- On the line through `i • a` in a direction `b` of the Gårding cone, the complexified
polynomial has no zero in the closed upper half-plane. -/
private theorem eval_map_I_smul_add_smul_ne_zero {z : ℂ} (hz : 0 ≤ z.im) :
    eval (I • (fun j ↦ (a j : ℂ)) + z • fun j ↦ (b j : ℂ)) (p.map ofRealHom) ≠ 0 := by
  have hP := hp.isHomogeneous.map ofRealHom
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [zero_smul, add_zero, hP.eval_smul, eval_map_ofReal]
    exact mul_ne_zero (pow_ne_zero _ I_ne_zero) (ofReal_ne_zero.2 hp.eval_pos.ne')
  have heq : I • (fun j ↦ (a j : ℂ)) + z • (fun j ↦ (b j : ℂ)) =
      z • ((fun j ↦ (b j : ℂ)) + (I / z) • fun j ↦ (a j : ℂ)) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hz0, add_comm]
  rw [heq, hP.eval_smul]
  refine mul_ne_zero (pow_ne_zero _ hz0) ?_
  by_cases ht : (I / z).im = 0
  · have hre : 0 ≤ (I / z).re := by
      rw [div_re, I_re, I_im, zero_mul, one_mul, zero_div, zero_add]
      exact div_nonneg hz (normSq_nonneg z)
    have hpt : (fun j ↦ (b j : ℂ)) + (I / z) • (fun j ↦ (a j : ℂ)) =
        fun j ↦ ((b + (I / z).re • a) j : ℂ) := by
      funext j
      simp [Complex.ext_iff, ht]
    rw [hpt, eval_map_ofReal]
    exact_mod_cast (mem_gardingCone.1 hb) _ hre
  · exact hp.eval_map_ofReal_add_smul_ne_zero b ht

/-- **The deformation step.** For every real `x`, the complexified polynomial has no zero at
`x + i • a + z • b` with `z` in the closed upper half-plane. The family
`λ ↦ (z ↦ p(λ • x + i • a + z • b))` has no zero on the real axis for any `λ` (the real point
`λ • x + z • b` plus `i • a` is not a zero, by hyperbolicity in `a`), none in the closed upper
half-plane at `λ = 0`, and the set of `λ` with no zero there is open (by compactness, after
inverting large `z` through homogeneity) and closed (by Hurwitz's theorem). -/
private theorem eval_map_add_I_smul_add_smul_ne_zero (x : σ → ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    eval ((fun j ↦ (x j : ℂ)) + I • (fun j ↦ (a j : ℂ)) + z • fun j ↦ (b j : ℂ))
      (p.map ofRealHom) ≠ 0 := by
  have hP := hp.isHomogeneous.map ofRealHom
  set X : σ → ℂ := fun j ↦ (x j : ℂ)
  set A : σ → ℂ := fun j ↦ (a j : ℂ)
  set B : σ → ℂ := fun j ↦ (b j : ℂ)
  set P := p.map ofRealHom
  let f : ℝ → ℂ → ℂ := fun l z ↦ eval ((l : ℂ) • X + I • A + z • B) P
  let g : ℝ → ℂ → ℂ := fun l u ↦ eval (u • ((l : ℂ) • X + I • A) + B) P
  have hf : Continuous (Function.uncurry f) :=
    (continuous_eval P).comp (by fun_prop)
  have hg : Continuous (Function.uncurry g) :=
    (continuous_eval P).comp (by fun_prop)
  have hfg (l : ℝ) {z : ℂ} (hz0 : z ≠ 0) : f l z = z ^ m * g l z⁻¹ := by
    simp only [f, g]
    rw [← hP.eval_smul, smul_add, smul_smul, mul_inv_cancel₀ hz0, one_smul]
  have hreal (l : ℝ) {z : ℂ} (hz : z.im = 0) : f l z ≠ 0 := by
    have hpt : (l : ℂ) • X + I • A + z • B = (fun j ↦ ((l • x + z.re • b) j : ℂ)) + I • A := by
      funext j
      simp [X, A, B, Complex.ext_iff, hz]
    simp only [f]
    rw [hpt]
    exact hp.eval_map_ofReal_add_smul_ne_zero _ (by simp)
  have hpoly (l : ℝ) : f l = fun z ↦ (aeval (fun i ↦ Polynomial.C (((l : ℂ) • X + I • A) i) +
      Polynomial.C (b i : ℂ) * Polynomial.X) P).eval z := by
    funext z
    simp only [f, eval_aeval_C_add_C_mul_X]
    rfl
  have hdiff (l : ℝ) : DifferentiableOn ℂ (f l) {z : ℂ | 0 < z.im} := by
    rw [hpoly l]
    exact Polynomial.differentiable _ |>.differentiableOn
  have hnc (l : ℝ) : ¬ ∀ z ∈ {z : ℂ | 0 < z.im}, f l z = 0 := by
    rw [hpoly l]
    exact exists_im_pos_eval_ne_zero (aeval_map_ne_zero hp hb _)
  let S : Set ℝ := {l | ∀ z : ℂ, 0 ≤ z.im → f l z ≠ 0}
  have h0 : (0 : ℝ) ∈ S := fun z hz ↦ by
    simp only [f, ofReal_zero, zero_smul, zero_add]
    exact eval_map_I_smul_add_smul_ne_zero hp hb hz
  have hopen : IsOpen S := isOpen_setOf_forall_im_nonneg_ne_zero hf hg hfg fun l ↦ by
    change eval ((0 : ℂ) • ((l : ℂ) • X + I • A) + B) P ≠ 0
    rw [zero_smul, zero_add, eval_map_ofReal, ne_eq, ofReal_eq_zero]
    exact (eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hb).ne'
  have hclosed : IsClosed S := isClosed_setOf_forall_im_nonneg_ne_zero hf hreal hdiff hnc
  have hS : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0⟩
  have h1 : (1 : ℝ) ∈ S := hS ▸ mem_univ _
  simpa [f] using h1 z hz

/-- For every real `x`, the complexification of `p` has no zero at `x + z • b` with `z` in the
open upper half-plane. Scaling the deformation step gives no zero at `x + (α * i) • a + z • b`
for every `α > 0`, and Hurwitz's theorem passes to the limit `α → 0`. -/
private theorem eval_map_ofReal_add_smul_ne_zero_of_im_pos (x : σ → ℝ) {z : ℂ} (hz : 0 < z.im) :
    eval ((fun j ↦ (x j : ℂ)) + z • fun j ↦ (b j : ℂ)) (p.map ofRealHom) ≠ 0 := by
  have hP := hp.isHomogeneous.map ofRealHom
  set X : σ → ℂ := fun j ↦ (x j : ℂ)
  set A : σ → ℂ := fun j ↦ (a j : ℂ)
  set B : σ → ℂ := fun j ↦ (b j : ℂ)
  set P := p.map ofRealHom
  let F : ℝ → ℂ → ℂ := fun α z ↦ eval (X + ((α : ℂ) * I) • A + z • B) P
  have hF : Continuous (Function.uncurry F) := (continuous_eval P).comp (by fun_prop)
  have hpos (α : ℝ) (hα : 0 < α) : ∀ z ∈ {z : ℂ | 0 < z.im}, F α z ≠ 0 := fun z hz ↦ by
    have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.2 hα.ne'
    have hpt : X + ((α : ℂ) * I) • A + z • B = (α : ℂ) •
        ((fun j ↦ ((α⁻¹ • x) j : ℂ)) + I • A + (z / α) • B) := by
      funext j
      simp only [X, A, B, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_mul, ofReal_inv]
      field_simp
    simp only [F]
    rw [hpt, hP.eval_smul]
    refine mul_ne_zero (pow_ne_zero _ hα') ?_
    refine eval_map_add_I_smul_add_smul_ne_zero hp hb _ ?_
    rw [div_ofReal_im]
    exact (div_pos hz hα).le
  have hpoly (α : ℝ) : F α = fun z ↦ (aeval (fun i ↦ Polynomial.C ((X + ((α : ℂ) * I) • A) i) +
      Polynomial.C (b i : ℂ) * Polynomial.X) P).eval z := by
    funext z
    simp only [F, eval_aeval_C_add_C_mul_X]
    rfl
  have h := TauCeti.hurwitz_forall_ne isOpen_and_isPreconnected_upperHalfPlane.1
    isOpen_and_isPreconnected_upperHalfPlane.2 (F := F) (g := F 0) (l := 𝓝[>] (0 : ℝ))
    (Eventually.of_forall fun α ↦ by
      rw [hpoly α]
      exact Polynomial.differentiable _ |>.differentiableOn)
    (tendstoLocallyUniformlyOn_of_continuous_uncurry hF 0 _
      isOpen_and_isPreconnected_upperHalfPlane.1)
    (v := 0)
    ((eventually_mem_nhdsWithin (s := Ioi 0) (a := 0)).mono fun α hα ↦ hpos α hα).frequently
    (by rw [hpoly 0]; exact exists_im_pos_eval_ne_zero (aeval_map_ne_zero hp hb _)) z hz
  simpa [F] using h

/-- **Hyperbolicity in every direction of the Gårding cone.** If `p` is hyperbolic of degree `m`
in the direction `a` and `b` lies in the Gårding cone `Γ(p, a)`, then `p` is hyperbolic of degree
`m` in the direction `b`. -/
theorem IsHyperbolic.of_mem_gardingCone : IsHyperbolic p m b where
  isHomogeneous := hp.isHomogeneous
  eval_pos := eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hb
  splits x := by
    refine Polynomial.Splits.of_splits_map ofRealHom (IsAlgClosed.splits _) fun t ht ↦ ?_
    by_cases him : t.im = 0
    · exact ⟨t.re, by simp [Complex.ext_iff, him]⟩
    have hroot := (Polynomial.mem_roots'.1 ht).2
    rw [Polynomial.IsRoot.def, eval_map_aeval_C_add_C_mul_X] at hroot
    exfalso
    rcases lt_or_gt_of_ne him with hneg | hpos
    · refine eval_map_ofReal_add_smul_ne_zero_of_im_pos hp hb x (z := (starRingEnd ℂ) t)
        (by simpa using hneg) ?_
      have := congrArg (starRingEnd ℂ) hroot
      rw [map_zero, ← eval_map_ofReal_conj] at this
      convert this using 3
      funext j
      simp
    · exact eval_map_ofReal_add_smul_ne_zero_of_im_pos hp hb x hpos hroot

/-- If `p` is hyperbolic in the direction `a` and `b ∈ Γ(p, a)`, then `Γ(p, a) ⊆ Γ(p, b)`. The
cone `Γ(p, a)` is connected and meets the open cone `Γ(p, b)` at `b`. A limit `y ∈ Γ(p, a)` of
points of `Γ(p, b)` lies in `Γ(p, b)`: otherwise `p(y + t₀ • b) = 0` for some `t₀ > 0`, and by
Hurwitz's theorem nearby points `w` have a root of `z ↦ p(w + z • b)` near `t₀`, which is real by
hyperbolicity in `b`, hence positive, so `w ∉ Γ(p, b)`. -/
private theorem gardingCone_subset_of_mem : gardingCone p a ⊆ gardingCone p b := by
  have hpb := hp.of_mem_gardingCone hb
  have hpa0 := hp.eval_pos.ne'
  have hpb0 := hpb.eval_pos.ne'
  refine ((starConvex_gardingCone hp.isHomogeneous hpa0).isPathConnected
    (self_mem_gardingCone hp.isHomogeneous hpa0)).isConnected.isPreconnected
    |>.subset_of_closure_inter_subset (isOpen_gardingCone hp.isHomogeneous hpb0)
    ⟨b, hb, self_mem_gardingCone hp.isHomogeneous hpb0⟩ ?_
  rintro y ⟨hyc, hya⟩
  by_contra hyb
  obtain ⟨t₀, ht₀, hroot⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ eval (y + t₀ • b) p = 0 := by
    simpa [mem_gardingCone] using hyb
  have ht₀pos : 0 < t₀ := lt_of_le_of_ne ht₀ fun h ↦
    (eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hya).ne' (by simpa [← h] using hroot)
  let G : (σ → ℝ) → ℂ → ℂ := fun w z ↦
    eval ((fun j ↦ (w j : ℂ)) + z • fun j ↦ (b j : ℂ)) (p.map ofRealHom)
  have hG : Continuous (Function.uncurry G) := (continuous_eval _).comp (by fun_prop)
  have hpoly (w : σ → ℝ) : G w = fun z ↦ (aeval (fun i ↦ Polynomial.C (w i : ℂ) +
      Polynomial.C (b i : ℂ) * Polynomial.X) (p.map ofRealHom)).eval z := by
    funext z
    simp only [G, eval_aeval_C_add_C_mul_X]
  obtain ⟨w, hw, z, hz, hGz⟩ := exists_mem_ball_eq_zero_of_mem_closure hG
    (fun w ↦ ⟨_, aeval_map_ne_zero hp hb _, hpoly w⟩) hyc (z₀ := t₀) (by
      have hpt : (fun j ↦ (y j : ℂ)) + (t₀ : ℂ) • (fun j ↦ (b j : ℂ)) =
          fun j ↦ ((y + t₀ • b) j : ℂ) := by
        funext j
        simp
      simp only [G]
      rw [hpt, eval_map_ofReal, hroot, ofReal_zero]) (half_pos ht₀pos)
  have him : z.im = 0 := by
    by_contra h
    exact hpb.eval_map_ofReal_add_smul_ne_zero w h hGz
  have hzre : 0 < z.re := by
    have h := Complex.abs_re_le_norm (z - t₀)
    rw [sub_re, ofReal_re, ← dist_eq_norm] at h
    have := (abs_le.1 (h.trans (Metric.mem_ball.1 hz).le)).1
    linarith
  refine (mem_gardingCone.1 hw) z.re hzre.le ?_
  have hpt : (fun j ↦ (w j : ℂ)) + z • (fun j ↦ (b j : ℂ)) = fun j ↦ ((w + z.re • b) j : ℂ) := by
    funext j
    simp [Complex.ext_iff, him]
  simp only [G] at hGz
  rw [hpt, eval_map_ofReal] at hGz
  exact_mod_cast hGz

/-- **Independence of the direction (Gårding).** If `p` is hyperbolic in the direction `a` and
`b ∈ Γ(p, a)`, then `Γ(p, b) = Γ(p, a)`. -/
theorem IsHyperbolic.gardingCone_eq_of_mem : gardingCone p b = gardingCone p a :=
  (gardingCone_subset_of_mem (hp.of_mem_gardingCone hb)
    (gardingCone_subset_of_mem hp hb (self_mem_gardingCone hp.isHomogeneous hp.eval_pos.ne'))
    ).antisymm (gardingCone_subset_of_mem hp hb)

omit hb in
/-- **Convexity of the Gårding cone (Gårding).** The Gårding cone of a hyperbolic polynomial is
convex: for `x, y ∈ Γ(p, a)`, the cone `Γ(p, x) = Γ(p, a)` is star-convex with respect to `x`. -/
theorem IsHyperbolic.convex_gardingCone : Convex ℝ (gardingCone p a) := fun x hx ↦ by
  rw [← hp.gardingCone_eq_of_mem hx]
  exact starConvex_gardingCone hp.isHomogeneous (hp.of_mem_gardingCone hx).eval_pos.ne'

end MvPolynomial
