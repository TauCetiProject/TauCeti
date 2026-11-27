/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Garding
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Order.Polynomial
import TauCeti.Algebra.BigOperators.Perm
import TauCeti.Analysis.MvPolynomial.Hyperbolic.Concave

/-!
# Gårding cones in the direction `e = (1, …, 1)`

Let `p` be a real polynomial, hyperbolic of degree `m` in the direction `e = (1, …, 1)`, with
Gårding cone `Γ = Γ(p, e)`.

If `p` is symmetric and `m ≥ 1`, then `Γ` lies in the half-space `σ_1 > 0`
(`MvPolynomial.IsHyperbolic.sum_pos_of_mem_gardingCone`). The proof averages over permutations:
for `x ∈ Γ`, the sum `∑_π x ∘ π` over all permutations `π` lies in the convex cone `Γ`, and all
its coordinates are equal, to a multiple of `σ_1(x)` by a positive constant. If `σ_1(x) ≤ 0`, it
is `-s • e` with `s ≥ 0`, which is not in `Γ` since `p(-s • e + s • e) = p(0) = 0`
(`MvPolynomial.smul_notMem_gardingCone`).

If moreover `b` lies in the closure of the cone and `σ_1(b) > 0`, then the directional
derivative `D_b p = ∑ᵢ bᵢ ∂p/∂Xᵢ` is positive on `Γ`
(`MvPolynomial.IsHyperbolic.eval_sum_smul_pderiv_pos_of_mem_closure`). In particular, if the
coordinate vector `eᵢ` lies in the closure of the cone, then `∂p/∂Xᵢ > 0` on `Γ`
(`MvPolynomial.IsHyperbolic.eval_pderiv_pos_of_single_mem_closure`). By
`MvPolynomial.IsHyperbolic.setOf_forall_pos_subset_iff`, this condition for every `i` says that
`Γ` contains the positive orthant `Γ_n`. Symmetry alone does not give it: for
`p = 2xy - 0.9(x² + y²)` on `ℝ²`, hyperbolic in `e`, the cone is a sector around the diagonal
that contains `(1, 0.7)`, where `∂p/∂x = -0.4`.

## Main results

* `MvPolynomial.IsHyperbolic.sum_pos_of_mem_gardingCone`: for symmetric `p` of degree `m ≥ 1`,
  `σ_1 > 0` on `Γ(p, e)`.
* `MvPolynomial.IsHyperbolic.eval_sum_smul_pderiv_pos_of_mem_closure`: for symmetric `p` of
  degree `m ≥ 1`, `b ∈ closure Γ(p, e)` and `σ_1(b) > 0`, `D_b p > 0` on `Γ(p, e)`.
* `MvPolynomial.IsHyperbolic.eval_pderiv_pos_of_single_mem_closure`: for symmetric `p` of degree
  `m ≥ 1` and `eᵢ ∈ closure Γ(p, e)`, `∂p/∂Xᵢ > 0` on `Γ(p, e)`.

## Implementation notes

For the derivative, fix `x ∈ Γ` and let `q(t) = p(x + t • b)`. The ray `x + t • b`, `t ≥ 0`, lies
in `Γ`, since `Γ + closure Γ ⊆ Γ` (`MvPolynomial.IsHyperbolic.add_mem_gardingCone_of_mem_closure`),
so `t ↦ q(t)^{1/m}` is concave on `[0, ∞)` by Gårding's theorem
(`MvPolynomial.IsHyperbolic.concaveOn_rpow`). If `q'(0) ≤ 0`, concavity gives `0 < q(t) ≤ q(0)`
for `t ≥ 0`, and a polynomial bounded on a half-line is constant
(`Polynomial.isBoundedUnder_abs_atTop_iff`). Then the whole line `x + ℝ • b` avoids the zeros of
`p`; it meets `Γ` at `x` and `Γ` is closed in `{p ≠ 0}`
(`MvPolynomial.IsHyperbolic.mem_gardingCone_of_mem_closure`), so the line lies in `Γ`. This
contradicts `σ_1 > 0` on `Γ`, since `σ_1(x + t • b) = σ_1(x) + t σ_1(b)` with `σ_1(b) > 0`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in
  *Global theory of minimal surfaces*, Clay Math. Proc. 2 (2005), §2.
-/

public section

open Set

namespace MvPolynomial.IsHyperbolic

variable {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℝ} {m : ℕ}

/-- **A symmetric Gårding cone lies in the half-space `σ_1 > 0`.** For a symmetric polynomial `p`
of degree `m ≥ 1`, hyperbolic in the direction `e = (1, …, 1)`, every point of the Gårding cone
`Γ(p, e)` has positive coordinate sum. -/
theorem sum_pos_of_mem_gardingCone (hp : IsHyperbolic p m 1) (hm : 1 ≤ m) (hsymm : p.IsSymmetric)
    {x : σ → ℝ} (hx : x ∈ gardingCone p 1) : 0 < ∑ i, x i := by
  classical
  -- The sum over all permutations lies in the cone.
  set y : σ → ℝ := ∑ π : Equiv.Perm σ, x ∘ π
  have hy : y ∈ gardingCone p 1 :=
    Finset.sum_induction_nonempty _ (· ∈ gardingCone p 1)
      (fun _ _ ha hb ↦ hp.add_mem_gardingCone ha hb) Finset.univ_nonempty
      fun π _ ↦ comp_mem_gardingCone (hsymm π) rfl hx
  have hyi (i : σ) : y i = ∑ π : Equiv.Perm σ, x (π i) := by simp [y, Finset.sum_apply]
  by_contra! hneg
  -- A polynomial of positive degree vanishes at `0`, so the cone contains no `s • e` with `s ≤ 0`.
  -- Hence `σ` is nonempty: otherwise `y = 0 • e`.
  obtain ⟨i₀⟩ : Nonempty σ := by
    by_contra hσ
    rw [not_nonempty_iff] at hσ
    exact smul_notMem_gardingCone hp.isHomogeneous (by omega) le_rfl
      (Subsingleton.elim y ((0 : ℝ) • 1) ▸ hy)
  -- All coordinates of `y` equal `y i₀`, which has the sign of `σ_1(x)`.
  have hyc : y = y i₀ • (1 : σ → ℝ) := by
    ext i
    simp [hyi, Equiv.Perm.sum_apply_eq_sum_apply x i i₀]
  have hsum : (Fintype.card σ : ℝ) * y i₀ = Fintype.card (Equiv.Perm σ) * ∑ i, x i := by
    rw [← nsmul_eq_mul (Fintype.card (Equiv.Perm σ)), ← Equiv.Perm.sum_sum_apply, hyi]
    simp_rw [Equiv.Perm.sum_apply_eq_sum_apply x _ i₀]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hy₀ : y i₀ ≤ 0 := by
    have hcard : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i₀⟩
    nlinarith [show (0 : ℝ) < Fintype.card (Equiv.Perm σ) by exact_mod_cast Fintype.card_pos]
  exact smul_notMem_gardingCone hp.isHomogeneous (by omega) hy₀ (hyc ▸ hy)

/-- A real polynomial `q`, positive on `[0, ∞)`, with `q^{1/m}` concave there for some `m ≥ 1` and
`q'(0) ≤ 0`, satisfies `q(t) ≤ q(0)` for `t ≥ 0`. -/
private theorem eval_le_eval_zero_of_concaveOn_rpow {q : Polynomial ℝ} {m : ℕ} (hm : 1 ≤ m)
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

/-- **Positivity of the directional derivatives on a symmetric Gårding cone.** Let `p` be a
symmetric polynomial, hyperbolic of degree `m ≥ 1` in the direction `e = (1, …, 1)`, and let `b`
lie in the closure of the Gårding cone `Γ(p, e)` with `σ_1(b) > 0`. Then the directional
derivative `D_b p = ∑ᵢ bᵢ ∂p/∂Xᵢ` is positive on `Γ(p, e)`. -/
theorem eval_sum_smul_pderiv_pos_of_mem_closure (hp : IsHyperbolic p m 1) (hm : 1 ≤ m)
    (hsymm : p.IsSymmetric) {b : σ → ℝ} (hb : b ∈ closure (gardingCone p 1))
    (hb0 : 0 < ∑ j, b j) {x : σ → ℝ} (hx : x ∈ gardingCone p 1) :
    0 < eval x (∑ i, b i • pderiv i p) := by
  -- The ray `x + t • b`, `t ≥ 0`, lies in the cone, since `Γ + closure Γ ⊆ Γ`.
  have hray (t : ℝ) (ht : 0 ≤ t) : x + t • b ∈ gardingCone p 1 := by
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
  -- `q^{1/m}` is concave on `[0, ∞)` by Gårding's theorem, so `q` is bounded there, hence constant.
  have hconc : ConcaveOn ℝ (Ici 0) fun t ↦ q.eval t ^ (m : ℝ)⁻¹ := by
    refine ((hp.concaveOn_rpow.comp_affineMap (AffineMap.lineMap x (x + b))).subset
      (fun t ht ↦ ?_) (convex_Ici 0)).congr fun t _ ↦ ?_
    · simpa [AffineMap.lineMap_apply_module', add_comm] using hray t ht
    · simp [AffineMap.lineMap_apply_module', hq, add_comm]
  have hdeg : q.degree ≤ 0 := Polynomial.isBoundedUnder_abs_atTop_iff.1
    ⟨q.eval 0, Filter.eventually_map.2 <| (Filter.eventually_ge_atTop 0).mono fun t ht ↦ by
      rw [abs_of_pos (hpos t ht)]
      exact eval_le_eval_zero_of_concaveOn_rpow hm hpos hconc (hq' ▸ hle) ht⟩
  have hne (t : ℝ) : eval (x + t • b) p ≠ 0 := by
    rw [← hq, Polynomial.eq_C_of_degree_le_zero hdeg, Polynomial.eval_C]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using (hpos 0 le_rfl).ne'
  -- So the whole line `x + ℝ • b` lies in the cone, which contradicts `σ_1 > 0` on the cone.
  have hcont : Continuous fun t : ℝ ↦ x + t • b := by fun_prop
  have hclopen : IsClopen {t : ℝ | x + t • b ∈ gardingCone p 1} :=
    ⟨isClosed_of_closure_subset fun t ht ↦ hp.mem_gardingCone_of_mem_closure
      (map_mem_closure (f := fun t : ℝ ↦ x + t • b) (t := gardingCone p 1) hcont ht
        fun _ hs ↦ hs) (hne t),
      (isOpen_gardingCone hp.isHomogeneous hp.eval_pos.ne').preimage hcont⟩
  have hline := hclopen.eq_univ ⟨0, by simpa using hx⟩ ▸ mem_univ (-(∑ j, x j + 1) / ∑ j, b j)
  have hsum := hp.sum_pos_of_mem_gardingCone hm hsymm hline
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, div_mul_cancel₀ _ hb0.ne'] at hsum
  linarith

omit [Fintype σ] in
/-- **Positivity of the partial derivatives on a symmetric Gårding cone.** Let `p` be a symmetric
polynomial, hyperbolic of degree `m ≥ 1` in the direction `e = (1, …, 1)`, such that the
coordinate vector `eᵢ` lies in the closure of the Gårding cone `Γ(p, e)`. Then `∂p/∂Xᵢ > 0` on
`Γ(p, e)`. -/
theorem eval_pderiv_pos_of_single_mem_closure [Finite σ] [DecidableEq σ] (hp : IsHyperbolic p m 1)
    (hm : 1 ≤ m) (hsymm : p.IsSymmetric) {i : σ}
    (hi : (Pi.single i 1 : σ → ℝ) ∈ closure (gardingCone p 1)) {x : σ → ℝ}
    (hx : x ∈ gardingCone p 1) : 0 < eval x (pderiv i p) := by
  have := Fintype.ofFinite σ
  simpa [Pi.single_apply] using hp.eval_sum_smul_pderiv_pos_of_mem_closure hm hsymm hi (by simp) hx

end MvPolynomial.IsHyperbolic
