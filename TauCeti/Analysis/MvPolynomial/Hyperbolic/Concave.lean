/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Order.Polynomial
import TauCeti.Analysis.Convex.Strong
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.MvPolynomial.Jacobian

/-!
# Gårding's theorem: concavity of `p^{1/m}` on the Gårding cone

Let `p` be a real polynomial, hyperbolic of degree `m ≥ 1` in the direction `a`
(`MvPolynomial.IsHyperbolic`), with Gårding cone `Γ = Γ(p, a)`. Then `p^{1/m}` is superadditive
on `Γ` (`MvPolynomial.IsHyperbolic.eval_rpow_add_le`):

`p(x)^{1/m} + p(y)^{1/m} ≤ p(x + y)^{1/m}` for `x, y ∈ Γ`,

and, being positively homogeneous of degree one (`MvPolynomial.IsHomogeneous.eval_smul_rpow`), it
is concave on the convex cone `Γ` (`MvPolynomial.IsHyperbolic.concaveOn_rpow`). This is the
concavity part of Gårding's theorem.

As a consequence, if `b` lies in the closure of `Γ` but `-b` does not, then the directional
derivative `D_b p = ∑ᵢ bᵢ ∂p/∂Xᵢ` is positive on `Γ`
(`MvPolynomial.IsHyperbolic.eval_sum_smul_pderiv_pos_of_mem_closure`).

Its tangent form is **Gårding's inequality**
(`MvPolynomial.IsHyperbolic.mul_rpow_mul_rpow_le_eval_sum_smul_pderiv`): for `x` and `y` in the
closure of `Γ`,

`m p(y)^{1/m} p(x)^{1 - 1/m} ≤ D_y p(x) = ∑ᵢ yᵢ ∂p/∂Xᵢ (x)`.

## Implementation notes

By Gårding's theorem on the directions (`MvPolynomial.IsHyperbolic.of_mem_gardingCone`), `p` is
hyperbolic in the direction `y`, with the same cone. So `t ↦ p(x + t • y)` splits with leading
coefficient `p(y)` and `m` roots `rᵢ`, all negative since `x ∈ Γ(p, y)`:
`p(x + t • y) = p(y) ∏ᵢ (t - rᵢ)`. At `t = 0` and `t = 1` this gives `p(x) = p(y) ∏ᵢ (-rᵢ)` and
`p(x + y) = p(y) ∏ᵢ (1 - rᵢ)`, and the inequality is the superadditivity of the geometric mean
(`Real.multiset_prod_map_rpow_inv_card_add_le`) for the families `-rᵢ` and `1`.

For the derivative, fix `x ∈ Γ` and let `q(t) = p(x + t • b)`. The ray `x + t • b`, `t ≥ 0`, lies
in `Γ`, since `Γ + closure Γ ⊆ Γ` (`MvPolynomial.IsHyperbolic.add_mem_gardingCone_of_mem_closure`),
so `t ↦ q(t)^{1/m}` is concave on `[0, ∞)`. If `q'(0) ≤ 0`, concavity gives `0 < q(t) ≤ q(0)`
for `t ≥ 0`, and a polynomial bounded on a half-line is constant
(`Polynomial.isBoundedUnder_abs_atTop_iff`). Then the whole line `x + ℝ • b` avoids the zeros of
`p`; it meets `Γ` at `x` and `Γ` is closed in `{p ≠ 0}`
(`MvPolynomial.IsHyperbolic.mem_gardingCone_of_mem_closure`), so the line lies in `Γ`. Hence
`s • x - b = s • (x - s⁻¹ • b) ∈ Γ` for every `s > 0`, and letting `s → 0` puts `-b` in the
closure of `Γ`.

For Gårding's inequality with `x` and `y` in `Γ`, the function `p^{1/m}` is concave on `Γ` and
positively homogeneous of degree one, so it lies below its tangent hyperplane through the origin
at `x` (`ConcaveOn.le_apply_of_hasFDerivAt_of_homogeneous`):
`p(y)^{1/m} ≤ (1/m) p(x)^{1/m - 1} D_y p(x)`. Both sides of Gårding's inequality are continuous
in `(x, y)`, which extends it to the closure of `Γ`.

## References

* L. Gårding, *An inequality for hyperbolic polynomials*, J. Math. Mech. 8 (1959), 957–965.
* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

open Set Filter Topology

variable {σ : Type*} {p : MvPolynomial σ ℝ} {m : ℕ} {a : σ → ℝ}

namespace MvPolynomial.IsHomogeneous

/-- For a homogeneous polynomial of degree `m ≥ 1` and `p(x) ≥ 0`, `p^{1/m}` is positively
homogeneous of degree one: `p(θ • x)^{1/m} = θ p(x)^{1/m}` for `θ ≥ 0`. -/
theorem eval_smul_rpow (hp : p.IsHomogeneous m) (hm : 1 ≤ m) {x : σ → ℝ}
    (hx : 0 ≤ eval x p) {θ : ℝ} (hθ : 0 ≤ θ) :
    eval (θ • x) p ^ (m : ℝ)⁻¹ = θ * eval x p ^ (m : ℝ)⁻¹ := by
  rw [hp.eval_smul, Real.mul_rpow (pow_nonneg hθ m) hx,
    Real.pow_rpow_inv_natCast hθ (by omega)]

end MvPolynomial.IsHomogeneous

namespace MvPolynomial.IsHyperbolic

/-- **Gårding's theorem, superadditivity.** For `p` hyperbolic of degree `m ≥ 1` in the direction
`a`, `p(x)^{1/m} + p(y)^{1/m} ≤ p(x + y)^{1/m}` for `x` and `y` in the Gårding cone `Γ(p, a)`. -/
theorem eval_rpow_add_le (hp : IsHyperbolic p m a) (hm : 1 ≤ m) {x y : σ → ℝ}
    (hx : x ∈ gardingCone p a) (hy : y ∈ gardingCone p a) :
    eval x p ^ (m : ℝ)⁻¹ + eval y p ^ (m : ℝ)⁻¹ ≤ eval (x + y) p ^ (m : ℝ)⁻¹ := by
  -- `p` is hyperbolic in the direction `y`, and `x` lies in its cone in that direction.
  have hy' := hp.of_mem_gardingCone hy
  have hx' : x ∈ gardingCone p y := (hp.gardingCone_eq_of_mem hy).symm ▸ hx
  set Q := aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X) p
  have hcard : Multiset.card Q.roots = m := hy'.card_roots x
  have hlc : Q.leadingCoeff = eval y p :=
    leadingCoeff_aeval_C_add_C_mul_X_of_isHomogeneous hy'.isHomogeneous x hy'.eval_pos.ne'
  have hroots := (mem_gardingCone_iff_forall_mem_roots hy'.isHomogeneous hy'.eval_pos.ne').1 hx'
  -- The values at `t = 0` and `t = 1` of `p(x + t • y) = p(y) ∏ᵢ (t - rᵢ)`.
  have h0 : eval x p = eval y p * (Q.roots.map fun r ↦ -r).prod := by
    have := (hy'.splits x).eval_eq_prod_roots 0
    rw [eval_aeval_C_add_C_mul_X, zero_smul, add_zero, hlc] at this
    simpa using this
  have h1 : eval (x + y) p = eval y p * (Q.roots.map fun r ↦ 1 - r).prod := by
    have := (hy'.splits x).eval_eq_prod_roots 1
    rwa [eval_aeval_C_add_C_mul_X, one_smul, hlc] at this
  have hpy := hy'.eval_pos.le
  have hA : 0 ≤ (Q.roots.map fun r ↦ -r).prod :=
    Multiset.prod_nonneg fun r hr ↦ by
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hr
      exact neg_nonneg.2 (hroots s hs).le
  have hB : 0 ≤ (Q.roots.map fun r ↦ 1 - r).prod :=
    Multiset.prod_nonneg fun r hr ↦ by
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hr
      linarith [hroots s hs]
  -- The superadditivity of the geometric mean for the families `-rᵢ` and `1`.
  have key := Real.multiset_prod_map_rpow_inv_card_add_le (s := Q.roots) (a := fun r ↦ -r)
    (b := fun _ ↦ 1) (fun h ↦ by simp [h] at hcard; omega)
    (fun r hr ↦ neg_nonneg.2 (hroots r hr).le) fun _ _ ↦ zero_le_one
  simp only [hcard, Multiset.map_const', Multiset.prod_replicate, one_pow, Real.one_rpow,
    neg_add_eq_sub] at key
  rw [h0, h1, Real.mul_rpow hpy hA, Real.mul_rpow hpy hB]
  nlinarith [Real.rpow_nonneg hpy (m : ℝ)⁻¹]

/-- **Gårding's theorem, concavity.** For `p` hyperbolic of degree `m` in the direction `a`,
`p^{1/m}` is concave on the Gårding cone `Γ(p, a)`. For `m = 0` the exponent `1/m` is the junk
value `0`, and the function is the constant `1`. -/
theorem concaveOn_rpow (hp : IsHyperbolic p m a) :
    ConcaveOn ℝ (gardingCone p a) fun x ↦ eval x p ^ (m : ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using concaveOn_const (1 : ℝ) hp.convex_gardingCone
  refine ⟨hp.convex_gardingCone, fun x hx y hy θ η hθ hη hθη ↦ ?_⟩
  have hpos {z : σ → ℝ} (hz : z ∈ gardingCone p a) : 0 ≤ eval z p :=
    (eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hz).le
  simp only [smul_eq_mul]
  rcases hθ.eq_or_lt with rfl | hθ'
  · simp [show η = 1 by linarith]
  rcases hη.eq_or_lt with rfl | hη'
  · simp [show θ = 1 by linarith]
  rw [← hp.isHomogeneous.eval_smul_rpow hm (hpos hx) hθ,
    ← hp.isHomogeneous.eval_smul_rpow hm (hpos hy) hη]
  exact hp.eval_rpow_add_le hm (smul_mem_gardingCone hp.isHomogeneous hx hθ')
    (smul_mem_gardingCone hp.isHomogeneous hy hη')

/-- A real polynomial `q`, positive on `[0, ∞)`, with `q^{1/m}` concave there for some `m ≥ 1` and
`q'(0) ≤ 0`, satisfies `q(t) ≤ q(0)` for `t ≥ 0`. -/
private theorem eval_le_eval_zero_of_concaveOn_rpow {q : Polynomial ℝ} (hm : 1 ≤ m)
    (hpos : ∀ t, 0 ≤ t → 0 < q.eval t)
    (hconc : ConcaveOn ℝ (Ici 0) fun t ↦ q.eval t ^ (m : ℝ)⁻¹) (hle : q.derivative.eval 0 ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) : q.eval t ≤ q.eval 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · exact le_rfl
  have hderiv := (q.hasDerivAt 0).rpow_const (p := (m : ℝ)⁻¹) (Or.inl (hpos 0 le_rfl).ne')
  have hs := hconc.slope_le_of_hasDerivAt (mem_Ici.2 le_rfl) (mem_Ici.2 ht.le) ht hderiv
  rw [slope_def_field, sub_zero] at hs
  have hd : q.derivative.eval 0 * (m : ℝ)⁻¹ * q.eval 0 ^ ((m : ℝ)⁻¹ - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hle (by positivity))
      (Real.rpow_nonneg (hpos 0 le_rfl).le _)
  have : q.eval t ^ (m : ℝ)⁻¹ ≤ q.eval 0 ^ (m : ℝ)⁻¹ := by
    have := (div_le_iff₀ ht).1 (hs.trans hd)
    linarith
  have hm' : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hm)
  exact (Real.rpow_le_rpow_iff (hpos t ht.le).le (hpos 0 le_rfl).le hm').1 this

/-- **Positivity of the directional derivatives in the closure of the cone.** Let `p` be
hyperbolic of degree `m ≥ 1` in the direction `a`, and let `b` lie in the closure of the Gårding
cone `Γ(p, a)` with `-b` not in it. Then the directional derivative `D_b p = ∑ᵢ bᵢ ∂p/∂Xᵢ` is
positive on `Γ(p, a)`. -/
theorem eval_sum_smul_pderiv_pos_of_mem_closure [Fintype σ] (hp : IsHyperbolic p m a)
    (hm : 1 ≤ m) {b : σ → ℝ} (hb : b ∈ closure (gardingCone p a))
    (hb' : -b ∉ closure (gardingCone p a)) {x : σ → ℝ} (hx : x ∈ gardingCone p a) :
    0 < eval x (∑ i, b i • pderiv i p) := by
  -- The ray `x + t • b`, `t ≥ 0`, lies in the cone, since `Γ + closure Γ ⊆ Γ`.
  have hray (t : ℝ) (ht : 0 ≤ t) : x + t • b ∈ gardingCone p a := by
    rcases ht.eq_or_lt with rfl | ht
    · simpa using hx
    convert smul_mem_gardingCone hp.isHomogeneous (hp.add_mem_gardingCone_of_mem_closure
      (smul_mem_gardingCone hp.isHomogeneous hx (inv_pos.2 ht)) hb) ht using 1
    match_scalars <;> field_simp
  -- The restriction `q(t) = p(x + t • b)` is positive on `[0, ∞)`, with `q'(0) = D_b p (x)`.
  set q := aeval (fun j ↦ Polynomial.C (x j) + Polynomial.C (b j) * Polynomial.X) p
  have hq (t : ℝ) : q.eval t = eval (x + t • b) p := eval_aeval_C_add_C_mul_X p x b t
  have hq' : q.derivative.eval 0 = eval x (∑ i, b i • pderiv i p) := by
    rw [derivative_aeval_C_add_C_mul_X, eval_aeval_C_add_C_mul_X, zero_smul, add_zero]
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < q.eval t :=
    hq t ▸ eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos (hray t ht)
  by_contra! hle
  -- `q^{1/m}` is concave on `[0, ∞)`, so `q` is bounded there, hence constant.
  have hconc : ConcaveOn ℝ (Ici 0) fun t ↦ q.eval t ^ (m : ℝ)⁻¹ := by
    refine ((hp.concaveOn_rpow.comp_affineMap (AffineMap.lineMap x (x + b))).subset
      (fun t ht ↦ ?_) (convex_Ici 0)).congr fun t _ ↦ ?_
    · simpa [AffineMap.lineMap_apply_module', add_comm] using hray t ht
    · simp [AffineMap.lineMap_apply_module', hq, add_comm]
  have hdeg : q.degree ≤ 0 := Polynomial.isBoundedUnder_abs_atTop_iff.1
    ⟨q.eval 0, eventually_map.2 <| (eventually_ge_atTop 0).mono fun t ht ↦ by
      rw [abs_of_pos (hpos t ht)]
      exact eval_le_eval_zero_of_concaveOn_rpow hm hpos hconc (hq' ▸ hle) ht⟩
  have hne (t : ℝ) : eval (x + t • b) p ≠ 0 := by
    rw [← hq, Polynomial.eq_C_of_degree_le_zero hdeg, Polynomial.eval_C]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using (hpos 0 le_rfl).ne'
  -- So the whole line `x + ℝ • b` lies in the cone.
  have hcont : Continuous fun t : ℝ ↦ x + t • b := by fun_prop
  have hclopen : IsClopen {t : ℝ | x + t • b ∈ gardingCone p a} :=
    ⟨isClosed_of_closure_subset fun t ht ↦ hp.mem_gardingCone_of_mem_closure
      (map_mem_closure (f := fun t : ℝ ↦ x + t • b) (t := gardingCone p a) hcont ht
        fun _ hs ↦ hs) (hne t),
      (isOpen_gardingCone hp.isHomogeneous hp.eval_pos.ne').preimage hcont⟩
  have hline (t : ℝ) : x + t • b ∈ gardingCone p a :=
    eq_univ_iff_forall.1 (hclopen.eq_univ ⟨0, by simpa using hx⟩) t
  -- Then `s • x - b ∈ Γ` for `s > 0`, and `s • x - b → -b` as `s → 0`, so `-b ∈ closure Γ`.
  refine hb' (mem_closure_of_tendsto (f := fun s : ℝ ↦ s • x - b) (b := 𝓝[>] 0) ?_ ?_)
  · simpa using ((Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds :
      Tendsto (fun s : ℝ ↦ s • x - b) (𝓝[>] 0) (𝓝 ((0 : ℝ) • x - b)))
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    convert smul_mem_gardingCone hp.isHomogeneous (hline (-s⁻¹)) hs using 1
    match_scalars <;> field_simp

/-- **Gårding's inequality**, for `x` and `y` in the cone. -/
private theorem mul_rpow_mul_rpow_le_eval_sum_smul_pderiv_of_mem [Fintype σ]
    (hp : IsHyperbolic p m a) (hm : 1 ≤ m) {x y : σ → ℝ} (hx : x ∈ gardingCone p a)
    (hy : y ∈ gardingCone p a) :
    m * eval y p ^ (m : ℝ)⁻¹ * eval x p ^ (1 - (m : ℝ)⁻¹) ≤ eval x (∑ i, y i • pderiv i p) := by
  have hP : 0 < eval x p := eval_pos_of_mem_gardingCone hp.isHomogeneous hp.eval_pos hx
  -- The tangent inequality for the concave, positively one-homogeneous function `p^{1/m}`.
  have h := hp.concaveOn_rpow.le_apply_of_hasFDerivAt_of_homogeneous hx hy
    ((p.hasFDerivAt_eval x).rpow_const (Or.inl hP.ne'))
    (Filter.eventually_of_mem (lt_mem_nhds zero_lt_one) fun t ht ↦
      hp.isHomogeneous.eval_smul_rpow hm hP.le (le_of_lt ht))
  simp only [smul_apply, sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    mul_comm (eval x (pderiv _ p))] at h
  rw [map_sum]
  simp only [smul_eval]
  -- Multiply by `m p(x)^{1 - 1/m}`.
  set D := ∑ i, y i * eval x (pderiv i p)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hQ : 0 < eval x p ^ (m : ℝ)⁻¹ := Real.rpow_pos_of_pos hP _
  rw [Real.rpow_sub_one hP.ne'] at h
  rw [Real.rpow_sub hP, Real.rpow_one]
  calc m * eval y p ^ (m : ℝ)⁻¹ * (eval x p / eval x p ^ (m : ℝ)⁻¹)
      ≤ m * ((m : ℝ)⁻¹ * (eval x p ^ (m : ℝ)⁻¹ / eval x p) * D) *
          (eval x p / eval x p ^ (m : ℝ)⁻¹) := by gcongr
    _ = D := by field_simp

/-- **Gårding's inequality.** For `p` hyperbolic of degree `m` in the direction `a` and `x`, `y`
in the closure of the Gårding cone `Γ(p, a)`,
`m p(y)^{1/m} p(x)^{1 - 1/m} ≤ D_y p(x) = ∑ᵢ yᵢ ∂p/∂Xᵢ (x)`. This is the tangent inequality of
the concave function `p^{1/m}`, positively homogeneous of degree one, at `x`. In degree `m = 0`
both sides vanish. -/
theorem mul_rpow_mul_rpow_le_eval_sum_smul_pderiv [Fintype σ] (hp : IsHyperbolic p m a)
    {x y : σ → ℝ} (hx : x ∈ closure (gardingCone p a)) (hy : y ∈ closure (gardingCone p a)) :
    m * eval y p ^ (m : ℝ)⁻¹ * eval x p ^ (1 - (m : ℝ)⁻¹) ≤ eval x (∑ i, y i • pderiv i p) := by
  -- In degree `0`, `p` is a constant and both sides vanish.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.1
      (hp.isHomogeneous.totalDegree hp.ne_zero)⟩
    simp
  have hm' : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hm)
  have hm'' : (0 : ℝ) ≤ 1 - (m : ℝ)⁻¹ :=
    sub_nonneg.2 (inv_le_one_of_one_le₀ (by exact_mod_cast hm))
  -- Both sides are continuous in `(x, y)`; the left side through `t ↦ t^{1/m}` and
  -- `t ↦ t^{1 - 1/m}`, whose exponents are nonnegative.
  have hclosed : IsClosed {z : (σ → ℝ) × (σ → ℝ) | m * eval z.2 p ^ (m : ℝ)⁻¹ *
      eval z.1 p ^ (1 - (m : ℝ)⁻¹) ≤ eval z.1 (∑ i, z.2 i • pderiv i p)} := by
    refine isClosed_le ?_ ?_
    · exact (continuous_const.mul (((continuous_eval p).comp continuous_snd).rpow_const
        fun _ ↦ Or.inr hm'.le)).mul (((continuous_eval p).comp continuous_fst).rpow_const
          fun _ ↦ Or.inr hm'')
    · have (i : σ) : Continuous fun z : (σ → ℝ) × (σ → ℝ) ↦ eval z.1 (pderiv i p) :=
        (continuous_eval _).comp continuous_fst
      simp only [map_sum, smul_eval]
      fun_prop
  have hxy : (x, y) ∈ closure (gardingCone p a ×ˢ gardingCone p a) := by
    rw [closure_prod_eq]
    exact Set.mk_mem_prod hx hy
  have h := closure_minimal (fun z (hz : z ∈ gardingCone p a ×ˢ gardingCone p a) ↦
    hp.mul_rpow_mul_rpow_le_eval_sum_smul_pderiv_of_mem hm hz.1 hz.2) hclosed hxy
  simpa only [Set.mem_ofPred_eq] using h

end MvPolynomial.IsHyperbolic
