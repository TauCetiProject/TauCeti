/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Star
public import Mathlib.FieldTheory.IsRealClosed.Real
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Order.IntermediateValue
public import TauCeti.FieldTheory.RealClosure.AbstractRolle
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.LineRestriction
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous

/-!
# Hyperbolic polynomials and their Gårding cones

A real polynomial `p` in the variables `σ` is *hyperbolic of degree `m` in the direction `a`*
(`MvPolynomial.IsHyperbolic`) if it is homogeneous of degree `m`, `p(a) > 0`, and for every `x`
the one-variable polynomial `t ↦ p(x + t • a)` has only real roots. Its *Gårding cone*
(`MvPolynomial.gardingCone`) is

`Γ(p, a) = {x | p(x + t • a) ≠ 0 for all t ≥ 0}`.

The model example is the product `σ_n = X₁ ⋯ X_n` of the variables, hyperbolic in the direction
`e = (1, …, 1)`, whose Gårding cone is the open positive orthant. Gårding's theory of hyperbolic
polynomials shows that `Γ(p, a)` is a convex cone on which `p^{1/m}` is concave; applied to the
elementary symmetric polynomials `σ_k`, this gives the cones `Γ_k` and the concave operators
`σ_k^{1/k}` of fully nonlinear elliptic equations such as the complex Hessian equations.

This file develops the elementary part of the theory. For a homogeneous `p` with `p(a) ≠ 0`, the
point `x` lies in `Γ(p, a)` exactly when `p` does not vanish on the closed segment from `a` to `x`
(`MvPolynomial.mem_gardingCone_iff_forall_mem_segment`), since the points `x + t • a`, `t ≥ 0`,
are positive multiples of the points of that segment other than `a`. Consequently `Γ(p, a)` is an
open set, star-convex with respect to `a`, invariant under positive dilations and under adding
nonnegative multiples of `a`, and `p > 0` on it when `p(a) > 0`. It is invariant under every
permutation of the variables fixing both `p` and `a`, for instance under all permutations when `p`
is symmetric and `a = e`. For a hyperbolic `p`, the line
restriction has exactly `m` real roots, and `x ∈ Γ(p, a)` exactly when all of them are negative.
Finally, if `p` is hyperbolic of degree `m ≥ 1` in the direction `a`, then so is its directional
derivative `D_a p = ∑ᵢ aᵢ ∂p/∂Xᵢ`, of degree `m - 1`, and `Γ(p, a) ⊆ Γ(D_a p, a)`: the line
restriction of `D_a p` is the derivative of that of `p`, whose roots are real by Rolle's theorem,
and at a point `t ≥ 0` beyond all the (negative) roots `rⱼ` of `q(t) = p(x + t • a)` the
logarithmic derivative `q'(t) / q(t) = ∑ⱼ 1 / (t - rⱼ)` is positive.

## Main definitions

* `MvPolynomial.IsHyperbolic p m a`: `p` is hyperbolic of degree `m` in the direction `a`.
* `MvPolynomial.gardingCone p a`: the Gårding cone `Γ(p, a)`.

## Main results

* `MvPolynomial.isOpen_gardingCone`, `MvPolynomial.starConvex_gardingCone`,
  `MvPolynomial.smul_mem_gardingCone`: `Γ(p, a)` is an open cone, star-convex with respect to `a`.
* `MvPolynomial.comp_mem_gardingCone`: `Γ(p, a)` is invariant under the permutations of the
  variables that fix both `p` and `a`.
* `MvPolynomial.eval_pos_of_mem_gardingCone`: `p > 0` on `Γ(p, a)`.
* `MvPolynomial.mem_gardingCone_iff_forall_mem_roots`: `x ∈ Γ(p, a)` exactly when the roots of
  `t ↦ p(x + t • a)` are negative.
* `MvPolynomial.IsHyperbolic.card_roots`: a hyperbolic polynomial of degree `m` has `m` real roots
  on each line in its direction.
* `MvPolynomial.IsHyperbolic.sum_smul_pderiv`,
  `MvPolynomial.IsHyperbolic.gardingCone_subset_sum_smul_pderiv`: the directional derivative
  `D_a p` is hyperbolic in the direction `a`, with a larger Gårding cone.
* `MvPolynomial.isHyperbolic_esymm_card`, `MvPolynomial.gardingCone_esymm_card`: `σ_n` is
  hyperbolic in the direction `e`, with the open positive orthant as Gårding cone.

## References

* L. Gårding, *An inequality for hyperbolic polynomials*, J. Math. Mech. 8 (1959), 957–965.
* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

namespace MvPolynomial

variable {σ : Type*}

/-- A real polynomial `p` is *hyperbolic of degree `m` in the direction `a`* if it is homogeneous
of degree `m`, `p(a) > 0`, and for every `x` its restriction `t ↦ p(x + t • a)` to the line
through `x` in the direction `a` has only real roots. -/
structure IsHyperbolic (p : MvPolynomial σ ℝ) (m : ℕ) (a : σ → ℝ) : Prop where
  /-- A hyperbolic polynomial is homogeneous. -/
  isHomogeneous : p.IsHomogeneous m
  /-- A hyperbolic polynomial is positive at its direction. -/
  eval_pos : 0 < eval a p
  /-- Every restriction of a hyperbolic polynomial to a line in its direction splits over `ℝ`. -/
  splits (x : σ → ℝ) :
    (aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (a i) * Polynomial.X) p).Splits

/-- The *Gårding cone* `Γ(p, a)` of a real polynomial `p` in the direction `a`: the points `x`
such that `p(x + t • a) ≠ 0` for every `t ≥ 0`. -/
def gardingCone (p : MvPolynomial σ ℝ) (a : σ → ℝ) : Set (σ → ℝ) :=
  {x | ∀ t : ℝ, 0 ≤ t → eval (x + t • a) p ≠ 0}

variable {p : MvPolynomial σ ℝ} {m : ℕ} {a x : σ → ℝ}

/-- Membership in the Gårding cone `Γ(p, a)`. -/
@[simp]
theorem mem_gardingCone : x ∈ gardingCone p a ↔ ∀ t : ℝ, 0 ≤ t → eval (x + t • a) p ≠ 0 :=
  Iff.rfl

/-- The Gårding cone is invariant under moving in the direction `a`. -/
theorem add_smul_mem_gardingCone (hx : x ∈ gardingCone p a) {s : ℝ} (hs : 0 ≤ s) :
    x + s • a ∈ gardingCone p a := fun t ht ↦ by
  rw [add_assoc, ← add_smul]
  exact hx _ (add_nonneg hs ht)

/-- The Gårding cone of a homogeneous polynomial is invariant under positive dilations. -/
theorem smul_mem_gardingCone (hp : p.IsHomogeneous m) (hx : x ∈ gardingCone p a) {s : ℝ}
    (hs : 0 < s) : s • x ∈ gardingCone p a := fun t ht ↦ by
  have : s • x + t • a = s • (x + (t / s) • a) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hs.ne']
  rw [this, hp.eval_smul_ne_zero_iff hs.ne']
  exact hx _ (div_nonneg ht hs.le)

/-- The Gårding cone of a polynomial invariant under a permutation `e` of the variables, in a
direction fixed by `e`, is invariant under `e`. -/
theorem comp_mem_gardingCone {e : Equiv.Perm σ} (hp : rename e p = p) (ha : a ∘ e = a)
    (hx : x ∈ gardingCone p a) : x ∘ e ∈ gardingCone p a := fun t ht ↦ by
  have : x ∘ e + t • a = (x + t • a) ∘ e := by
    ext i
    simp [← congrFun ha i]
  rw [this, ← eval_rename, hp]
  exact hx t ht

/-- The direction `a` lies in the Gårding cone `Γ(p, a)` of a homogeneous polynomial with
`p(a) ≠ 0`. -/
theorem self_mem_gardingCone (hp : p.IsHomogeneous m) (ha : eval a p ≠ 0) :
    a ∈ gardingCone p a := fun t ht ↦ by
  rw [show a + t • a = (1 + t) • a by rw [add_smul, one_smul],
    hp.eval_smul_ne_zero_iff (by positivity)]
  exact ha

/-- Scaling the polynomial by a nonzero constant does not change its Gårding cone. -/
@[simp]
theorem gardingCone_smul_left {c : ℝ} (hc : c ≠ 0) : gardingCone (c • p) a = gardingCone p a := by
  ext x
  simp [mem_gardingCone, smul_eval, hc]

/-- Scaling the direction by a positive constant does not change the Gårding cone. -/
theorem gardingCone_smul_right {s : ℝ} (hs : 0 < s) : gardingCone p (s • a) = gardingCone p a := by
  ext x
  refine ⟨fun hx t ht ↦ ?_, fun hx t ht ↦ ?_⟩
  · have := hx (t / s) (div_nonneg ht hs.le)
    rwa [smul_smul, div_mul_cancel₀ _ hs.ne'] at this
  · rw [smul_smul]
    exact hx _ (mul_nonneg ht hs.le)

/-- For a homogeneous polynomial with `p(a) ≠ 0`, a point `x` lies in the Gårding cone `Γ(p, a)`
if and only if `p` does not vanish on the closed segment from `a` to `x`. -/
theorem mem_gardingCone_iff_forall_mem_segment (hp : p.IsHomogeneous m) (ha : eval a p ≠ 0) :
    x ∈ gardingCone p a ↔ ∀ y ∈ segment ℝ a x, eval y p ≠ 0 := by
  refine ⟨?_, fun h t ht ↦ ?_⟩
  · rintro hx _ ⟨u, v, hu, hv, huv, rfl⟩
    obtain rfl | hv := hv.eq_or_lt
    · simpa [show u = 1 by linarith] using ha
    have : u • a + v • x = v • (x + (u / v) • a) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ hv.ne', add_comm]
    rw [this, hp.eval_smul_ne_zero_iff hv.ne']
    exact hx _ (div_nonneg hu hv.le)
  · have h1 : 0 < 1 + t := by linarith
    have hmem : (t / (1 + t)) • a + (1 / (1 + t)) • x ∈ segment ℝ a x :=
      ⟨_, _, div_nonneg ht h1.le, div_nonneg zero_le_one h1.le,
        by rw [← add_div, add_comm, div_self h1.ne'], rfl⟩
    have : x + t • a = (1 + t) • ((t / (1 + t)) • a + (1 / (1 + t)) • x) := by
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h1.ne', mul_div_cancel₀ _ h1.ne',
        one_smul, add_comm]
    rw [this, hp.eval_smul_ne_zero_iff h1.ne']
    exact h _ hmem

/-- The same criterion, with the segment parametrized by `θ ∈ [0, 1]`. -/
private theorem mem_gardingCone_iff_forall_mem_Icc (hp : p.IsHomogeneous m) (ha : eval a p ≠ 0) :
    x ∈ gardingCone p a ↔ ∀ θ ∈ Set.Icc (0 : ℝ) 1, eval ((1 - θ) • a + θ • x) p ≠ 0 := by
  rw [mem_gardingCone_iff_forall_mem_segment hp ha, segment_eq_image, Set.forall_mem_image]

/-- The Gårding cone `Γ(p, a)` of a homogeneous polynomial with `p(a) ≠ 0` is star-convex with
respect to `a`. -/
theorem starConvex_gardingCone (hp : p.IsHomogeneous m) (ha : eval a p ≠ 0) :
    StarConvex ℝ a (gardingCone p a) := by
  refine starConvex_iff_segment_subset.2 fun x hx y hy ↦ ?_
  rw [mem_gardingCone_iff_forall_mem_segment hp ha] at hx ⊢
  exact fun z hz ↦ hx z ((convex_segment a x).segment_subset (left_mem_segment ℝ a x) hy hz)

/-- The Gårding cone `Γ(p, a)` of a homogeneous polynomial with `p(a) ≠ 0` is open. -/
theorem isOpen_gardingCone (hp : p.IsHomogeneous m) (ha : eval a p ≠ 0) :
    IsOpen (gardingCone p a) := by
  refine isOpen_iff_mem_nhds.2 fun x₀ hx₀ ↦ ?_
  have hF : Continuous fun z : (σ → ℝ) × ℝ ↦ eval ((1 - z.2) • a + z.2 • z.1) p :=
    (continuous_eval p).comp (by fun_prop)
  have := isCompact_Icc.eventually_forall_of_forall_eventually
    (P := fun x θ ↦ eval ((1 - θ) • a + θ • x) p ≠ 0) fun θ hθ ↦
      hF.continuousAt.eventually_ne ((mem_gardingCone_iff_forall_mem_Icc hp ha).1 hx₀ θ hθ)
  filter_upwards [this] with x hx using (mem_gardingCone_iff_forall_mem_Icc hp ha).2 hx

/-- A homogeneous polynomial with `p(a) > 0` is positive on its Gårding cone `Γ(p, a)`. -/
theorem eval_pos_of_mem_gardingCone (hp : p.IsHomogeneous m) (ha : 0 < eval a p)
    (hx : x ∈ gardingCone p a) : 0 < eval x p := by
  rw [mem_gardingCone_iff_forall_mem_Icc hp ha.ne'] at hx
  by_contra! hneg
  have hf : Continuous fun θ : ℝ ↦ eval ((1 - θ) • a + θ • x) p :=
    (continuous_eval p).comp (by fun_prop)
  obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc' zero_le_one hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc _ _ by simp [hneg, ha.le])
  exact hx θ hθ hθ0

/-- For a homogeneous polynomial of degree `m` with `p(a) ≠ 0`, a point `x` lies in the Gårding
cone `Γ(p, a)` if and only if every real root of `t ↦ p(x + t • a)` is negative. -/
theorem mem_gardingCone_iff_forall_mem_roots (hp : p.IsHomogeneous m) (ha : eval a p ≠ 0) :
    x ∈ gardingCone p a ↔ ∀ t ∈
      (aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (a i) * Polynomial.X) p).roots, t < 0 := by
  have hne : aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (a i) * Polynomial.X) p ≠ 0 :=
    fun h ↦ ha <| by
      rw [← coeff_aeval_C_add_C_mul_X_of_isHomogeneous hp x a, h, Polynomial.coeff_zero]
  simp only [mem_gardingCone, Polynomial.mem_roots hne, Polynomial.IsRoot.def,
    eval_aeval_C_add_C_mul_X]
  exact ⟨fun h t ht ↦ not_le.1 fun ht' ↦ h t ht' ht, fun h t ht h0 ↦ (h t h0).not_ge ht⟩

namespace IsHyperbolic

/-- The restriction of a hyperbolic polynomial of degree `m` to a line in its direction has
exactly `m` real roots, counted with multiplicity. -/
theorem card_roots (hp : IsHyperbolic p m a) (x : σ → ℝ) :
    Multiset.card
      (aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (a i) * Polynomial.X) p).roots = m := by
  rw [← (hp.splits x).natDegree_eq_card_roots,
    natDegree_aeval_C_add_C_mul_X_of_isHomogeneous hp.isHomogeneous x hp.eval_pos.ne']

/-- Hyperbolicity is preserved by multiplying the polynomial by a positive constant. -/
theorem smul_left (hp : IsHyperbolic p m a) {c : ℝ} (hc : 0 < c) : IsHyperbolic (c • p) m a where
  isHomogeneous := by simpa [smul_eq_C_mul] using hp.isHomogeneous.C_mul c
  eval_pos := by simpa [smul_eval] using mul_pos hc hp.eval_pos
  splits x := by simpa [Polynomial.smul_eq_C_mul] using (hp.splits x).C_mul c

/-- Hyperbolicity is preserved by multiplying the direction by a positive constant. -/
theorem smul_right (hp : IsHyperbolic p m a) {s : ℝ} (hs : 0 < s) : IsHyperbolic p m (s • a) where
  isHomogeneous := hp.isHomogeneous
  eval_pos := by
    rw [hp.isHomogeneous.eval_smul]
    exact mul_pos (pow_pos hs m) hp.eval_pos
  splits x := by
    have : aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C ((s • a) i) * Polynomial.X) p =
        (aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (a i) * Polynomial.X) p).comp
          (Polynomial.C s * Polynomial.X) :=
      Polynomial.funext fun t ↦ by
        rw [Polynomial.eval_comp, eval_aeval_C_add_C_mul_X, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X, eval_aeval_C_add_C_mul_X, smul_smul, mul_comm t s]
    rw [this]
    refine (hp.splits x).comp_of_natDegree_le_one_of_invertible
      (Polynomial.natDegree_C_mul_X s hs.ne').le ?_
    exact invertibleOfNonzero (by rw [Polynomial.leadingCoeff_C_mul_X]; exact hs.ne')

/-- If `p` is hyperbolic of degree `m ≥ 1` in the direction `a`, then so is its derivative
`D_a p = ∑ᵢ aᵢ ∂p/∂Xᵢ` in the direction `a`, with degree `m - 1`. -/
theorem sum_smul_pderiv [Fintype σ] (hp : IsHyperbolic p m a) (hm : 1 ≤ m) :
    IsHyperbolic (∑ i, a i • pderiv i p) (m - 1) a where
  isHomogeneous :=
    IsHomogeneous.sum _ _ _ fun i _ ↦ by
      simpa [smul_eq_C_mul] using hp.isHomogeneous.pderiv.C_mul (a i)
  eval_pos := by
    have := congrArg (eval a) hp.isHomogeneous.sum_X_mul_pderiv
    simp only [map_sum, eval_mul, eval_X, nsmul_eq_mul, map_natCast] at this
    simp only [map_sum, smul_eval, this]
    exact mul_pos (Nat.cast_pos.2 (zero_lt_one.trans_le hm) : (0 : ℝ) < m) hp.eval_pos
  splits x := by
    -- The derivative of a real polynomial with only real roots has only real roots, by Rolle.
    rw [← derivative_aeval_C_add_C_mul_X]
    exact TauCeti.RealClosure.polynomialRolle_of_isRealClosed.splits_derivative (hp.splits x)

/-- The Gårding cone of a hyperbolic polynomial of degree `m ≥ 1` in the direction `a` lies in the
Gårding cone of its derivative `D_a p = ∑ᵢ aᵢ ∂p/∂Xᵢ` in the same direction. -/
theorem gardingCone_subset_sum_smul_pderiv [Fintype σ] (hp : IsHyperbolic p m a) (hm : 1 ≤ m) :
    gardingCone p a ⊆ gardingCone (∑ i, a i • pderiv i p) a := by
  intro x hx t ht
  set q := aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (a i) * Polynomial.X) p
  have hroots := (mem_gardingCone_iff_forall_mem_roots hp.isHomogeneous hp.eval_pos.ne').1 hx
  have hqt : q.eval t ≠ 0 := by simpa [q] using hx t ht
  -- `q'(t) / q(t) = ∑ᵣ 1 / (t - r)` over the roots `r < 0 ≤ t` of `q`, of which there are `m ≥ 1`.
  have hsum : 0 < (q.roots.map fun r ↦ 1 / (t - r)).sum := by
    have hpos : ∀ r ∈ q.roots, 0 < 1 / (t - r) := fun r hr ↦
      one_div_pos.2 (by linarith [hroots r hr])
    obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < Multiset.card q.roots by
      rw [hp.card_roots x]; omega)
    refine (hpos r hr).trans_le (Multiset.single_le_sum (fun y hy ↦ ?_) _
      (Multiset.mem_map_of_mem _ hr))
    obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.1 hy
    exact (hpos r' hr').le
  rw [← eval_aeval_C_add_C_mul_X, ← derivative_aeval_C_add_C_mul_X,
    (hp.splits x).eval_derivative_eq_eval_mul_sum hqt]
  exact mul_ne_zero hqt hsum.ne'

end IsHyperbolic

section Esymm

variable [Fintype σ]

/-- The elementary symmetric polynomial `σ_n = X₁ ⋯ X_n` in all `n` variables is hyperbolic of
degree `n` in the direction `e = (1, …, 1)`: `σ_n(x + t • e) = ∏ᵢ (xᵢ + t)`. -/
theorem isHyperbolic_esymm_card :
    IsHyperbolic (esymm σ ℝ (Fintype.card σ)) (Fintype.card σ) 1 where
  isHomogeneous := isHomogeneous_esymm _
  eval_pos := by simp [esymm_card]
  splits x := by
    rw [esymm_card, map_prod]
    exact Polynomial.Splits.prod fun i _ ↦ Polynomial.Splits.of_natDegree_le_one <| by
      simp [add_comm]

/-- The Gårding cone of `σ_n = X₁ ⋯ X_n` in the direction `e = (1, …, 1)` is the open positive
orthant. -/
theorem gardingCone_esymm_card :
    gardingCone (esymm σ ℝ (Fintype.card σ)) 1 = {x | ∀ i, 0 < x i} := by
  ext x
  simp only [mem_gardingCone, esymm_card, map_prod, eval_X, Pi.add_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one, Set.mem_ofPred_eq]
  refine ⟨fun h i ↦ ?_, fun h t ht ↦ Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_⟩
  · by_contra! hi
    exact h (-x i) (by linarith) (Finset.prod_eq_zero (Finset.mem_univ i) (by ring))
  · linarith [h i]

end Esymm

end MvPolynomial
