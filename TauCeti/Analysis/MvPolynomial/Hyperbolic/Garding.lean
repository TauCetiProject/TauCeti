/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Geometry.Convex.Cone.Basic
public import TauCeti.Analysis.MvPolynomial.Hyperbolic
import TauCeti.Analysis.Convex.Cone.Orthant
import TauCeti.Analysis.Polynomial.RootLocation

/-!
# Gårding's theorem: hyperbolicity in the directions of the cone

Let `p` be a real polynomial, hyperbolic of degree `m` in the direction `a`
(`MvPolynomial.IsHyperbolic`), with Gårding cone `Γ = Γ(p, a)` (`MvPolynomial.gardingCone`).
Gårding's theorem says that `p` is then hyperbolic in every direction `b ∈ Γ`, with the same cone
`Γ(p, b) = Γ`. Consequently `Γ` is convex: for `y ∈ Γ` it is the cone `Γ(p, y)`, which is
star-convex with respect to `y`. With the derivative rule of `MvPolynomial.IsHyperbolic` it also
gives that the directional derivative `D_b p = ∑ᵢ bᵢ ∂p/∂Xᵢ` is positive on `Γ` for every `b ∈ Γ`
when `m ≥ 1`. The concavity of `p^{1/m}` on `Γ`, the remaining part of Gårding's theorem, is in
`TauCeti.Analysis.MvPolynomial.Hyperbolic.Concave` (`MvPolynomial.IsHyperbolic.concaveOn_rpow`).

The model case is that of the elementary symmetric polynomials `σ_k`, hyperbolic in the direction
`e = (1, …, 1)` with Gårding cones the cones `Γ_k` (`MvPolynomial.gardingCone_esymm`): for them
these results say that `Γ_k` is a convex cone and that `D_b σ_k > 0` on `Γ_k` for `b ∈ Γ_k`, as
fully nonlinear elliptic equations such as the complex Hessian equations require.

## Main results

* `MvPolynomial.IsHyperbolic.eval_map_ofReal_add_smul_ne_zero`: a hyperbolic polynomial has no
  complex zero off the real axis on a line in its direction.
* `MvPolynomial.IsHyperbolic.of_mem_gardingCone`: `p` is hyperbolic in every direction `b ∈ Γ`.
* `MvPolynomial.IsHyperbolic.mem_gardingCone_of_mem_closure`: a point of the closure of `Γ` where
  `p` does not vanish lies in `Γ`.
* `MvPolynomial.IsHyperbolic.gardingCone_eq_of_mem`: `Γ(p, b) = Γ(p, a)` for `b ∈ Γ(p, a)`.
* `MvPolynomial.IsHyperbolic.convex_gardingCone`, `MvPolynomial.IsHyperbolic.add_mem_gardingCone`:
  `Γ` is a convex cone.
* `MvPolynomial.IsHyperbolic.gardingConvexCone`: `Γ` as a `ConvexCone`.
* `MvPolynomial.IsHyperbolic.setOf_forall_pos_subset_iff`: `Γ` contains the positive orthant if
  and only if every coordinate vector `eᵢ` lies in its closure.
* `MvPolynomial.IsHyperbolic.eval_sum_smul_pderiv_pos`: `D_b p > 0` on `Γ` for `b ∈ Γ`, `m ≥ 1`.

## Implementation notes

Fix `b ∈ Γ`, a real point `x` and `α > 0`, and consider the complex polynomials
`ψ_s(τ) = p(s • x + α i • a + τ • b)` for `s ∈ [0, 1]`, all of degree `m` with leading coefficient
`p(b) > 0`. None has a real root, since `t ↦ p(y + t • a)` has only real roots for real `y`. For
`s = 0` all roots lie in the open lower half-plane, because the roots of `t ↦ p(b + t • a)` are
negative. A continuity argument on `[0, 1]` keeps them there up to `s = 1`. On one side, the roots
of the `ψ_s` with `s ∈ [0, 1]` are uniformly bounded, by homogeneity, so the set of `s` for which
`ψ_s` has a root in the closed upper half-plane is closed. On the other side, if every root of
`ψ_s` lies in the lower half-plane then `|ψ_s(τ)| ≥ p(b) (Im τ)^m` for `Im τ ≥ 0`, a closed
condition in `s`. Letting `α → 0` in this inequality for `s = 1` shows that `τ ↦ p(x + τ • b)` has
no root in the open upper half-plane, and by conjugation none in the lower one.

The equality of the cones follows because `Γ(p, a)` is closed in the open set `{p ≠ 0}`: the
restriction `t ↦ p(y + t • a)` for `y ∈ Γ` has only negative roots, so `|p(y + t • a)| ≥ p(a) t^m`
for `t ≥ 0`, and this inequality passes to the closure. The star-convex, hence connected, cone
`Γ(p, b)` meets `Γ(p, a)` at `b`, so it lies in `Γ(p, a)`, and symmetrically.

## References

* L. Gårding, *An inequality for hyperbolic polynomials*, J. Math. Mech. 8 (1959), 957–965.
* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), Theorem 2.2.
-/

public section

open Complex ComplexConjugate Set Topology

/-- **Zeros do not cross the real axis.** Let `F (s, τ)` be continuous in `s ∈ ℝ` and `τ ∈ ℂ`,
with no zero `τ` on the real axis for `s ∈ [0, 1]`, and with the zeros for `s ∈ [0, 1]` uniformly
bounded. Suppose that whenever `F (s, ·)` has no zero in the closed upper half-plane, it satisfies
`|F (s, τ)| ≥ c (Im τ)^m` there, for a fixed `c > 0`. If `F (0, ·)` has no zero in the closed
upper half-plane, neither has `F (1, ·)`. -/
private theorem ne_zero_of_forall_ne_zero_of_isPreconnected {F : ℝ × ℂ → ℂ} (hF : Continuous F)
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hreal : ∀ s ∈ Icc (0 : ℝ) 1, ∀ τ : ℂ, τ.im = 0 → F (s, τ) ≠ 0)
    {R : ℝ} (hR : ∀ s ∈ Icc (0 : ℝ) 1, ∀ τ : ℂ, R < ‖τ‖ → F (s, τ) ≠ 0)
    (hlow : ∀ s : ℝ, (∀ τ : ℂ, 0 ≤ τ.im → F (s, τ) ≠ 0) →
      ∀ τ : ℂ, 0 ≤ τ.im → c * τ.im ^ m ≤ ‖F (s, τ)‖)
    (h0 : ∀ τ : ℂ, 0 ≤ τ.im → F (0, τ) ≠ 0) {τ : ℂ} (hτ : 0 ≤ τ.im) : F (1, τ) ≠ 0 := by
  -- `T` is the closed set of `s` with the lower bound, and `T'` the closed set of `s ∈ [0, 1]`
  -- for which `F (s, ·)` has a zero in the closed upper half-plane.
  let T : Set ℝ := {s | ∀ τ : ℂ, 0 ≤ τ.im → c * τ.im ^ m ≤ ‖F (s, τ)‖}
  have hT : IsClosed T := by
    simp only [T, ofPred_forall]
    exact isClosed_iInter fun τ ↦ isClosed_iInter fun _ ↦
      isClosed_le continuous_const (hF.comp (Continuous.prodMk_left τ)).norm
  let K : Set ℂ := Metric.closedBall 0 R ∩ {τ | 0 ≤ τ.im}
  have hK : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_im)
  let T' : Set ℝ := Prod.fst '' (Icc 0 1 ×ˢ K ∩ F ⁻¹' {0})
  have hT' : IsClosed T' := (((isCompact_Icc.prod hK).inter_right
    (isClosed_singleton.preimage hF)).image continuous_fst).isClosed
  have hmem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {τ : ℂ} (hτ : 0 ≤ τ.im) (h : F (s, τ) = 0) :
      s ∈ T' :=
    ⟨(s, τ), ⟨⟨hs, mem_closedBall_zero_iff.2 (not_lt.1 fun h' ↦ hR s hs τ h' h), hτ⟩, h⟩, rfl⟩
  have hcover : Icc (0 : ℝ) 1 ⊆ T ∪ T' := fun s hs ↦ by
    by_cases h : ∀ τ : ℂ, 0 ≤ τ.im → F (s, τ) ≠ 0
    · exact Or.inl (hlow s h)
    · push Not at h
      obtain ⟨τ, hτ, hFτ⟩ := h
      exact Or.inr (hmem hs hτ hFτ)
  -- By connectedness of `[0, 1]`, `0 ∈ T` and `1 ∈ T'` would give a point of `T ∩ T'`.
  intro h1
  obtain ⟨s, -, hsT, ⟨⟨s', τ'⟩, ⟨⟨hs', -, hτ'⟩, hFτ⟩, rfl⟩⟩ :=
    isPreconnected_closed_iff.1 isPreconnected_Icc T T' hT hT' hcover
      ⟨0, left_mem_Icc.2 zero_le_one, hlow 0 h0⟩
      ⟨1, right_mem_Icc.2 zero_le_one, hmem (right_mem_Icc.2 zero_le_one) hτ h1⟩
  rw [mem_ofPred_eq] at hτ'
  rw [mem_preimage, mem_singleton_iff] at hFτ
  have hs := hsT τ' hτ'
  rw [hFτ, norm_zero] at hs
  rcases hτ'.eq_or_lt with h | h
  · exact hreal s' hs' τ' h.symm hFτ
  · exact (mul_pos hc (pow_pos h m)).not_ge hs

namespace MvPolynomial

variable {σ : Type*} {p : MvPolynomial σ ℝ} {m : ℕ} {a b x : σ → ℝ}

/-- For `p` hyperbolic in the direction `a` and a real point `y`, the complexified `p` vanishes at
`y + l • a` only for real `l`. -/
private theorem IsHyperbolic.im_eq_zero_of_eval_eq_zero (hp : IsHyperbolic p m a) (y : σ → ℝ)
    {l : ℂ} (hl : eval (ofReal ∘ y + l • ofReal ∘ a) (map ofRealHom p) = 0) : l.im = 0 := by
  obtain ⟨r, rfl⟩ := (hp.splits y).mem_range_of_isRoot
    (aeval_C_add_C_mul_X_ne_zero_of_isHomogeneous hp.isHomogeneous y hp.eval_pos.ne')
    (i := ofRealHom)
    (by rwa [Polynomial.IsRoot.def, eval_map_aeval_C_add_C_mul_X ofRealHom])
  simp

/-- **No complex roots off the real axis.** If `p` is hyperbolic in the direction `a`, then for a
real point `y` and a non-real `t`, the complexification of `p` does not vanish at `y + t • a`. -/
theorem IsHyperbolic.eval_map_ofReal_add_smul_ne_zero (hp : IsHyperbolic p m a) (y : σ → ℝ)
    {t : ℂ} (ht : t.im ≠ 0) :
    eval ((fun j ↦ (y j : ℂ)) + t • fun j ↦ (a j : ℂ)) (p.map ofRealHom) ≠ 0 :=
  fun h ↦ ht (hp.im_eq_zero_of_eval_eq_zero y h)

/-- The point `y + r • v` of the complexification, for real `y`, `v` and `r`, is real. -/
private theorem ofReal_comp_add_ofReal_smul (y v : σ → ℝ) (r : ℝ) :
    ofReal ∘ y + (r : ℂ) • ofReal ∘ v = ofReal ∘ (y + r • v) := by
  ext i
  simp

/-- If the complexification of a homogeneous `p` with `p(b) ≠ 0` has no zero on the closed upper
half-line `{w + τ • b | Im τ ≥ 0}`, then `|p(w + τ • b)| ≥ |p(b)| (Im τ)^m` there: the roots of
`τ ↦ p(w + τ • b)` lie in the lower half-plane, at distance at least `Im τ` from `τ`. -/
private theorem norm_mul_im_pow_le_norm_eval (hp : p.IsHomogeneous m) (hb : eval b p ≠ 0)
    (w : σ → ℂ) (h : ∀ τ : ℂ, 0 ≤ τ.im → eval (w + τ • ofReal ∘ b) (map ofRealHom p) ≠ 0)
    {τ : ℂ} (hτ : 0 ≤ τ.im) :
    ‖(eval b p : ℂ)‖ * τ.im ^ m ≤ ‖eval (w + τ • ofReal ∘ b) (map ofRealHom p)‖ := by
  have hP := hp.map ofRealHom
  have hPb : eval (ofReal ∘ b) (map ofRealHom p) ≠ 0 :=
    (map_eval ofRealHom b p).symm.trans_ne (by simpa using hb)
  have hψ (z : ℂ) := eval_aeval_C_add_C_mul_X (map ofRealHom p) w (ofReal ∘ b) z
  have hdeg := natDegree_aeval_C_add_C_mul_X_of_isHomogeneous hP w hPb
  have hlc := leadingCoeff_aeval_C_add_C_mul_X_of_isHomogeneous hP w hPb
  replace hlc := hlc.trans (map_eval ofRealHom b p).symm
  rw [← hψ, ← ofRealHom_eq_coe (eval b p), ← hlc, ← hdeg]
  refine (IsAlgClosed.splits _).norm_leadingCoeff_mul_pow_le_norm_eval hτ fun r hr ↦ ?_
  have hr : r.im < 0 := by
    refine not_le.1 fun hr' ↦ h r hr' ?_
    rw [← hψ]
    exact (Polynomial.mem_roots (aeval_C_add_C_mul_X_ne_zero_of_isHomogeneous hP w hPb)).1 hr
  calc τ.im ≤ (τ - r).im := by rw [sub_im]; linarith
    _ ≤ ‖τ - r‖ := (le_abs_self _).trans (abs_im_le_norm _)

/-- For `p` hyperbolic in the direction `a`, `b ∈ Γ(p, a)` and `α > 0`, the complexified `p` does
not vanish at `α i • a + τ • b` when `Im τ ≥ 0`, since the roots of `t ↦ p(b + t • a)` are real
and negative. -/
private theorem IsHyperbolic.eval_I_smul_add_smul_ne_zero (hp : IsHyperbolic p m a)
    (hb : b ∈ gardingCone p a) {α : ℝ} (hα : 0 < α) {τ : ℂ} (hτ : 0 ≤ τ.im) :
    eval ((α * I) • ofReal ∘ a + τ • ofReal ∘ b) (map ofRealHom p) ≠ 0 := by
  have hP := hp.isHomogeneous.map ofRealHom
  rcases eq_or_ne τ 0 with rfl | hτ0
  · rw [zero_smul, add_zero, hP.eval_smul]
    exact mul_ne_zero (pow_ne_zero _ (by simp [hα.ne']))
      ((map_eval ofRealHom a p).symm.trans_ne (by simpa using hp.eval_pos.ne'))
  have hpt : (α * I) • ofReal ∘ a + τ • ofReal ∘ b =
      τ • (ofReal ∘ b + (α * I / τ) • ofReal ∘ a) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hτ0, add_comm]
  rw [hpt, hP.eval_smul]
  refine mul_ne_zero (pow_ne_zero _ hτ0) fun h ↦ ?_
  -- `l = α i / τ` is a root of `t ↦ p(b + t • a)`, hence real and negative.
  have hl : α * I / τ = ((α * I / τ).re : ℂ) :=
    Complex.ext rfl (by simpa using hp.im_eq_zero_of_eval_eq_zero b h)
  rw [hl, ofReal_comp_add_ofReal_smul] at h
  replace h := (map_eq_zero ofRealHom).1 ((map_eval ofRealHom _ p).trans h)
  have hre : (α * I / τ).re < 0 := not_le.1 fun hre ↦ mem_gardingCone.1 hb _ hre h
  have : α = (α * I / τ).re * τ.im := by
    simpa using congrArg Complex.im (show α * I = (α * I / τ).re * τ by
      rw [← hl, div_mul_cancel₀ _ hτ0])
  nlinarith

/-- By homogeneity, for `p(b) ≠ 0` the zeros `τ` of `p(s • x + α i • a + τ • b)` are bounded
uniformly in `s ∈ [0, 1]`. -/
private theorem exists_forall_eval_add_smul_ne_zero (hp : p.IsHomogeneous m)
    (hb : eval b p ≠ 0) (x a : σ → ℝ) (α : ℝ) :
    ∃ R : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ τ : ℂ, R < ‖τ‖ →
      eval ((s • ofReal ∘ x + (α * I) • ofReal ∘ a) + τ • ofReal ∘ b) (map ofRealHom p) ≠ 0 := by
  have hP := hp.map ofRealHom
  have hG : Continuous fun z : ℂ × ℝ ↦
      eval (ofReal ∘ b + z.1 • (z.2 • ofReal ∘ x + (α * I) • ofReal ∘ a)) (map ofRealHom p) :=
    (continuous_eval _).comp (by fun_prop)
  have hb0 (s : ℝ) : eval (ofReal ∘ b + (0 : ℂ) • (s • ofReal ∘ x + (α * I) • ofReal ∘ a))
      (map ofRealHom p) ≠ 0 := by
    rw [zero_smul, add_zero]
    exact (map_eval ofRealHom b p).symm.trans_ne (by simpa using hb)
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ s ∈ Icc (0 : ℝ) 1,
      eval (ofReal ∘ b + u • (s • ofReal ∘ x + (α * I) • ofReal ∘ a)) (map ofRealHom p) ≠ 0 :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun s _ ↦
      (hG.continuousAt (x := ((0 : ℂ), s))).eventually_ne (hb0 s)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε⁻¹, fun s hs τ hτ ↦ ?_⟩
  have hτ0 : τ ≠ 0 := norm_pos_iff.1 ((inv_pos.2 hε).trans hτ)
  have hpt : (s • ofReal ∘ x + (α * I) • ofReal ∘ a) + τ • ofReal ∘ b =
      τ • (ofReal ∘ b + τ⁻¹ • (s • ofReal ∘ x + (α * I) • ofReal ∘ a)) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hτ0, one_smul, add_comm]
  rw [hpt, hP.eval_smul]
  refine mul_ne_zero (pow_ne_zero _ hτ0) (hball ?_ s hs)
  rw [dist_zero_right, norm_inv]
  exact inv_lt_of_inv_lt₀ hε hτ

/-- **The key step of Gårding's theorem.** For `p` hyperbolic in the direction `a`, `b ∈ Γ(p, a)`,
a real point `x` and `α > 0`, the complexified `p` does not vanish at `x + α i • a + τ • b` when
`Im τ ≥ 0`. The family `s ↦ p(s • x + α i • a + τ • b)`, `s ∈ [0, 1]`, has no real zero, and its
zeros for `s = 0` lie in the open lower half-plane. -/
private theorem IsHyperbolic.eval_add_smul_ne_zero_of_mem_gardingCone (hp : IsHyperbolic p m a)
    (hb : b ∈ gardingCone p a) (x : σ → ℝ) {α : ℝ} (hα : 0 < α) {τ : ℂ} (hτ : 0 ≤ τ.im) :
    eval ((ofReal ∘ x + (α * I) • ofReal ∘ a) + τ • ofReal ∘ b) (map ofRealHom p) ≠ 0 := by
  have hpb : 0 < eval b p := eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hb
  obtain ⟨R, hR⟩ := exists_forall_eval_add_smul_ne_zero hp.isHomogeneous hpb.ne' x a α
  -- A real zero `τ` would make `α i` a nonreal root of `t ↦ p(s • x + τ • b + t • a)`.
  have hreal (s : ℝ) (τ : ℂ) (hτ : τ.im = 0) :
      eval ((s • ofReal ∘ x + (α * I) • ofReal ∘ a) + τ • ofReal ∘ b) (map ofRealHom p) ≠ 0 := by
    have hpt : (s • ofReal ∘ x + (α * I) • ofReal ∘ a) + τ • ofReal ∘ b =
        ofReal ∘ (s • x + τ.re • b) + (α * I) • ofReal ∘ a := by
      ext i
      apply Complex.ext <;> simp [hτ]
    intro h
    have := hp.im_eq_zero_of_eval_eq_zero (s • x + τ.re • b) (hpt ▸ h)
    simp [hα.ne'] at this
  have hF : Continuous fun z : ℝ × ℂ ↦
      eval ((z.1 • ofReal ∘ x + (α * I) • ofReal ∘ a) + z.2 • ofReal ∘ b) (map ofRealHom p) :=
    (continuous_eval _).comp (by fun_prop)
  have h0 (τ : ℂ) (hτ : 0 ≤ τ.im) :
      eval (((0 : ℝ) • ofReal ∘ x + (α * I) • ofReal ∘ a) + τ • ofReal ∘ b) (map ofRealHom p) ≠
        0 := by
    rw [zero_smul, zero_add]
    exact hp.eval_I_smul_add_smul_ne_zero hb hα hτ
  have hc : 0 < ‖(eval b p : ℂ)‖ := norm_pos_iff.2 (by exact_mod_cast hpb.ne')
  have h := ne_zero_of_forall_ne_zero_of_isPreconnected (m := m) hF hc (fun s _ ↦ hreal s) hR
    ?_ h0 hτ
  · rwa [one_smul] at h
  · intro s h τ hτ
    exact norm_mul_im_pow_le_norm_eval hp.isHomogeneous hpb.ne'
      (s • ofReal ∘ x + (α * I) • ofReal ∘ a) h hτ

namespace IsHyperbolic

/-- **Gårding's theorem, hyperbolicity.** A polynomial hyperbolic in the direction `a` is
hyperbolic, of the same degree, in every direction `b` of its Gårding cone `Γ(p, a)`. -/
theorem of_mem_gardingCone (hp : IsHyperbolic p m a) (hb : b ∈ gardingCone p a) :
    IsHyperbolic p m b where
  isHomogeneous := hp.isHomogeneous
  eval_pos := eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hb
  splits x := by
    have hpb : 0 < eval b p := eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hb
    have hq := aeval_C_add_C_mul_X_ne_zero_of_isHomogeneous hp.isHomogeneous x hpb.ne'
    have hev (z : ℂ) : Polynomial.eval z (Polynomial.map ofRealHom
        (aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (b i) * Polynomial.X) p)) =
        eval (ofReal ∘ x + z • ofReal ∘ b) (map ofRealHom p) :=
      eval_map_aeval_C_add_C_mul_X ofRealHom p x b z
    -- The restriction has no complex root in the open upper half-plane: let `α → 0` in the
    -- lower bound of `|p(x + α i • a + z • b)|`.
    have hup (z : ℂ) (hz : 0 < z.im) :
        eval (ofReal ∘ x + z • ofReal ∘ b) (map ofRealHom p) ≠ 0 := by
      have hclosed : IsClosed {α : ℝ | ‖(eval b p : ℂ)‖ * z.im ^ m ≤
          ‖eval ((ofReal ∘ x + (α * I) • ofReal ∘ a) + z • ofReal ∘ b) (map ofRealHom p)‖} :=
        isClosed_le continuous_const ((continuous_eval _).comp (by fun_prop)).norm
      have h0 := (hclosed.closure_subset_iff (s := Ioi 0)).2
        (fun α (hα : 0 < α) ↦ norm_mul_im_pow_le_norm_eval hp.isHomogeneous hpb.ne' _
          (fun τ hτ ↦ hp.eval_add_smul_ne_zero_of_mem_gardingCone hb x hα hτ) hz.le)
        (show (0 : ℝ) ∈ closure (Ioi 0) by simp)
      simp only [mem_ofPred_eq, ofReal_zero, zero_mul, zero_smul, add_zero] at h0
      intro h
      rw [h, norm_zero] at h0
      exact (mul_pos (norm_pos_iff.2 (by exact_mod_cast hpb.ne')) (pow_pos hz m)).not_ge h0
    refine Polynomial.Splits.of_splits_map ofRealHom (IsAlgClosed.splits _) fun z hz ↦ ?_
    have hz0 := (Polynomial.mem_roots (Polynomial.map_ne_zero hq)).1 hz
    rw [Polynomial.IsRoot.def] at hz0
    have him : z.im = 0 := by
      rcases lt_trichotomy z.im 0 with h | h | h
      · refine (hup (conj z) (by simpa using h) ?_).elim
        -- The complex roots of a real polynomial are closed under conjugation.
        rw [← hev]
        exact (Polynomial.eval_map _ _).trans <| (Polynomial.aeval_conj _ z).trans <|
          (congrArg conj ((Polynomial.eval_map _ _).symm.trans hz0)).trans (map_zero _)
      · exact h
      · exact (hup z h (by rwa [← hev])).elim
    exact ⟨z.re, Complex.ext (by simp) (by simp [him])⟩

/-- A point of the closure of the Gårding cone `Γ(p, a)` of a hyperbolic polynomial at which `p`
does not vanish lies in `Γ(p, a)`. -/
theorem mem_gardingCone_of_mem_closure (hp : IsHyperbolic p m a)
    (hx : x ∈ closure (gardingCone p a)) (hx0 : eval x p ≠ 0) : x ∈ gardingCone p a := by
  refine mem_gardingCone.2 fun t ht ↦ ?_
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hx0
  -- For `y ∈ Γ(p, a)` the roots of `s ↦ p(y + s • a)` are negative, so `|p(y + t • a)| ≥ p(a) t^m`.
  have hlow : gardingCone p a ⊆ {y | ‖eval a p‖ * t ^ m ≤ ‖eval (y + t • a) p‖} := by
    intro y hy
    have hdeg := natDegree_aeval_C_add_C_mul_X_of_isHomogeneous hp.isHomogeneous y hp.eval_pos.ne'
    have hroots := (mem_gardingCone_iff_forall_mem_roots hp.isHomogeneous hp.eval_pos.ne').1 hy
    rw [mem_ofPred_eq, ← eval_aeval_C_add_C_mul_X,
      ← leadingCoeff_aeval_C_add_C_mul_X_of_isHomogeneous hp.isHomogeneous y hp.eval_pos.ne',
      ← hdeg]
    refine (hp.splits y).norm_leadingCoeff_mul_pow_le_norm_eval ht.le fun r hr ↦ ?_
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hroots r hr])]
    linarith [hroots r hr]
  have hx' := closure_minimal hlow
    (isClosed_le continuous_const ((continuous_eval p).comp (by fun_prop)).norm) hx
  intro h
  rw [mem_ofPred_eq, h, norm_zero] at hx'
  exact (mul_pos (norm_pos_iff.2 hp.eval_pos.ne') (pow_pos ht m)).not_ge hx'

/-- For a polynomial hyperbolic in two directions `a` and `c` whose Gårding cones meet, the cone
`Γ(p, c)` lies in `Γ(p, a)`: it is connected, and `Γ(p, a)` is open and closed in `{p ≠ 0}`. -/
private theorem gardingCone_subset (ha : IsHyperbolic p m a) {c y : σ → ℝ}
    (hc : IsHyperbolic p m c) (hya : y ∈ gardingCone p a) (hyc : y ∈ gardingCone p c) :
    gardingCone p c ⊆ gardingCone p a :=
  ((starConvex_gardingCone hc.isHomogeneous hc.eval_pos.ne').isPathConnected
    (self_mem_gardingCone hc.isHomogeneous hc.eval_pos.ne')).isConnected.isPreconnected
    |>.subset_of_closure_inter_subset (isOpen_gardingCone ha.isHomogeneous ha.eval_pos.ne')
      ⟨y, hyc, hya⟩ fun z ⟨hz, hzc⟩ ↦
        ha.mem_gardingCone_of_mem_closure hz (by simpa using mem_gardingCone.1 hzc 0 le_rfl)

/-- **Gårding's theorem, independence of the direction.** For `p` hyperbolic in the direction
`a` and `b ∈ Γ(p, a)`, the Gårding cones in the directions `a` and `b` coincide. -/
theorem gardingCone_eq_of_mem (hp : IsHyperbolic p m a) (hb : b ∈ gardingCone p a) :
    gardingCone p b = gardingCone p a := by
  have hb' := hp.of_mem_gardingCone hb
  have hbb := self_mem_gardingCone hb'.isHomogeneous hb'.eval_pos.ne'
  exact (hp.gardingCone_subset hb' hb hbb).antisymm (hb'.gardingCone_subset hp hbb hb)

/-- **Gårding's theorem, convexity.** The Gårding cone of a hyperbolic polynomial is convex. -/
theorem convex_gardingCone (hp : IsHyperbolic p m a) : Convex ℝ (gardingCone p a) := fun y hy ↦ by
  have hy' := hp.of_mem_gardingCone hy
  rw [← hp.gardingCone_eq_of_mem hy]
  exact starConvex_gardingCone hy'.isHomogeneous hy'.eval_pos.ne'

/-- The Gårding cone of a hyperbolic polynomial is closed under addition. -/
theorem add_mem_gardingCone (hp : IsHyperbolic p m a) {y : σ → ℝ} (hx : x ∈ gardingCone p a)
    (hy : y ∈ gardingCone p a) : x + y ∈ gardingCone p a := by
  have h := smul_mem_gardingCone hp.isHomogeneous
    (hp.convex_gardingCone hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)) two_pos
  rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    one_smul] at h

/-- The Gårding cone `Γ(p, a)` of a hyperbolic polynomial, as a convex cone. -/
def gardingConvexCone (hp : IsHyperbolic p m a) : ConvexCone ℝ (σ → ℝ) where
  carrier := gardingCone p a
  smul_mem' _ hc _ hx := smul_mem_gardingCone hp.isHomogeneous hx hc
  add_mem' _ hx _ hy := hp.add_mem_gardingCone hx hy

/-- The underlying set of `IsHyperbolic.gardingConvexCone` is the Gårding cone. -/
@[simp]
theorem coe_gardingConvexCone (hp : IsHyperbolic p m a) :
    (hp.gardingConvexCone : Set (σ → ℝ)) = gardingCone p a :=
  (rfl)

/-- Membership in `IsHyperbolic.gardingConvexCone` is membership in the Gårding cone. -/
@[simp]
theorem mem_gardingConvexCone (hp : IsHyperbolic p m a) {x : σ → ℝ} :
    x ∈ hp.gardingConvexCone ↔ x ∈ gardingCone p a :=
  .rfl

/-- **The positive orthant and the Gårding cone.** For `p` hyperbolic in the direction `a`, the
Gårding cone `Γ(p, a)` contains the positive orthant `Γ_n` if and only if every coordinate
vector `eᵢ` lies in its closure. -/
theorem setOf_forall_pos_subset_iff [Finite σ] [DecidableEq σ] (hp : IsHyperbolic p m a) :
    {x : σ → ℝ | ∀ i, 0 < x i} ⊆ gardingCone p a ↔
      ∀ i, (Pi.single i 1 : σ → ℝ) ∈ closure (gardingCone p a) :=
  hp.coe_gardingConvexCone ▸ ConvexCone.setOf_forall_pos_subset_iff
    (hp.coe_gardingConvexCone ▸ isOpen_gardingCone hp.isHomogeneous hp.eval_pos.ne')
    (hp.coe_gardingConvexCone ▸ ⟨a, self_mem_gardingCone hp.isHomogeneous hp.eval_pos.ne'⟩)

/-- **Gårding's theorem, positivity of the derivatives.** For `p` hyperbolic of degree `m ≥ 1` in
the direction `a` and `b ∈ Γ(p, a)`, the directional derivative `D_b p = ∑ᵢ bᵢ ∂p/∂Xᵢ` is positive
on `Γ(p, a)`. -/
theorem eval_sum_smul_pderiv_pos [Fintype σ] (hp : IsHyperbolic p m a) (hm : 1 ≤ m)
    (hb : b ∈ gardingCone p a) (hx : x ∈ gardingCone p a) :
    0 < eval x (∑ i, b i • pderiv i p) := by
  have hb' := hp.of_mem_gardingCone hb
  have hd := hb'.sum_smul_pderiv hm
  rw [← hp.gardingCone_eq_of_mem hb] at hx
  exact eval_pos_of_mem_gardingCone hd.isHomogeneous hd.eval_pos
    (hb'.gardingCone_subset_sum_smul_pderiv hm hx)

end IsHyperbolic

end MvPolynomial
