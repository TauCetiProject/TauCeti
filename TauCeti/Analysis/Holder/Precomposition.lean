/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Topology.MetricSpace.Holder

/-!
# Precomposition by `C^{k+1,α}` maps in bounded Hölder spaces

Let `φ : E → E'` be differentiable, with derivative `Dφ` a bounded `C^{k,α}` map,
`Dφ ∈ C_b^{k,α}(E, E →L[ℝ] E')`, and `0 ≤ α ≤ 1`. The map `φ` itself need not be bounded: for
instance a boundary-flattening map `(x', xₙ) ↦ (x', xₙ - γ(x'))` with `γ ∈ C_b^{k+1,α}` qualifies.
This file proves the chain rule in bounded Hölder spaces: precomposition `g ↦ g ∘ φ` maps
`C_b^{k+1,α}(E', F)` into `C_b^{k+1,α}(E, F)` with

`‖g ∘ φ‖ ≤ ((k + 2)! + 3 (k + 2) N) max(1, ‖Dφ‖)^(k + 2) ‖g‖`,

where `N` is the number of ordered partitions of a set of `k + 1` elements
(`Fintype.card (OrderedFinpartition (k + 1))`, a Bell number) and `‖Dφ‖` is the `C^{k,α}` norm
of the derivative. The constant depends only on `k` and `‖Dφ‖`. This is the change-of-variables
rule needed to transport Hölder norms through boundary charts, and, with `φ x = (x, u x)` for
`u ∈ C_b^{k+1,α}`, to control coefficients `A(x, u(x))` in terms of `u`. At order zero,
precomposition of `C^{0,α}` maps by a Lipschitz map is `TauCeti.HolderSpace.compLipschitzL`.

## The argument

The supremum norms of the derivatives of `g ∘ φ` through order `k + 1` are bounded by Mathlib's
`norm_iteratedFDeriv_comp_le`. For the Hölder seminorm of the top derivative, the Faà di Bruno
formula (`iteratedFDeriv_comp`) writes `D^{k+1}(g ∘ φ)(x)` as a sum over the ordered partitions
`c` of `{0, …, k}` of the multilinear compositions of `D^{ℓ} g(φ x)`, `ℓ` the number of parts, with
the derivatives `D^{s}φ(x)` along the parts, `1 ≤ s ≤ k + 1`. Each factor is bounded and
`α`-Hölder: `D^{s}φ = D^{s-1}(Dφ)` is controlled by `‖Dφ‖`, every derivative of `g` through
order `k + 1` is `α`-Hölder (`CkHolderSpace.holderWith_iteratedFDeriv_of_le`, this is where
`α ≤ 1` enters), and `φ` is `‖Dφ‖`-Lipschitz. The difference of two such compositions is
estimated term by term by
`OrderedFinpartition.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le`.
This estimate is a quantitative, uniform version of Mathlib's
`FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO`, which follows the same steps to give
the pointwise asymptotic bound used in `ContDiffPointwiseHolderAt.comp_of_differentiableAt`.

## Main declarations

* `TauCeti.CkHolderSpace.compOfFDerivL`: precomposition by `φ` as a bounded linear operator
  `C_b^{k+1,α}(E', F) →L[ℝ] C_b^{k+1,α}(E, F)`.
* `TauCeti.CkHolderSpace.compOfFDerivL_apply`: its values are `g (φ x)`.
* `TauCeti.CkHolderSpace.norm_compOfFDerivL_le`: the operator norm bound.
* `TauCeti.CkHolderSpace.compOfFDerivCLE`: precomposition by a bijection `φ` such that `φ` and
  `φ⁻¹` both have derivatives in `C_b^{k,α}`, as an isomorphism of bounded Hölder spaces.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (Hölder norms under the boundary-flattening maps of `C^{k,α}` domains).
-/

public section
noncomputable section

namespace TauCeti.CkHolderSpace

open scoped NNReal

variable {k : ℕ} {α : ℝ≥0} {E E' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → E'} {ψ : CkHolderSpace k α E (E →L[ℝ] E')}

/-! ### Bounds on the derivatives of `φ` -/

/-- A map whose derivative is a bounded `C^{k,α}` map is `C^{k+1}`. -/
private theorem contDiff_of_fderiv_eq (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ) :
    ContDiff ℝ (k + 1 : ℕ) φ := by
  have h : ContDiff ℝ ((k : WithTop ℕ∞) + 1) φ :=
    contDiff_succ_iff_fderiv.2 ⟨hφ, fun h ↦ absurd h (by simp), hψ ▸ ψ.contDiff⟩
  exact_mod_cast h

/-- The derivatives of orders `1, …, k + 1` of `φ` are bounded by the norm of `Dφ`. -/
private theorem norm_iteratedFDeriv_le_of_fderiv_eq (hψ : fderiv ℝ φ = ψ) {s : ℕ} (hs₁ : 1 ≤ s)
    (hs : s ≤ k + 1) (x : E) : ‖_root_.iteratedFDeriv ℝ s φ x‖ ≤ ‖ψ‖ := by
  obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv, hψ]
  exact ψ.norm_iteratedFDeriv_apply_le (by omega) x

/-- The derivatives of orders `1, …, k + 1` of `φ` are `α`-Hölder with constant `3 ‖Dφ‖`. -/
private theorem dist_iteratedFDeriv_le_of_fderiv_eq (hα : α ≤ 1) (hψ : fderiv ℝ φ = ψ)
    {s : ℕ} (hs₁ : 1 ≤ s) (hs : s ≤ k + 1) (x y : E) :
    dist (_root_.iteratedFDeriv ℝ s φ x) (_root_.iteratedFDeriv ℝ s φ y) ≤
      3 * ‖ψ‖ * dist x y ^ (α : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.dist_map,
    hψ]
  have h := (ψ.holderWith_iteratedFDeriv_of_le hα (j := j) (by omega)).dist_le x y
  push_cast at h
  exact h

/-- The map `φ` is `‖Dφ‖`-Lipschitz. -/
private theorem lipschitzWith_of_fderiv_eq (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ) :
    LipschitzWith ‖ψ‖₊ φ :=
  lipschitzWith_of_nnNorm_fderiv_le hφ fun x ↦ by
    rw [hψ]
    exact_mod_cast ψ.norm_apply_le x

/-! ### The Hölder estimate for the top derivative -/

/-- One term of the Faà di Bruno formula for `D^{k+1}(g ∘ φ)`, at the ordered partition `c`: the
composition of `D^{ℓ} g (φ x)` with the derivatives of `φ` at `x` along the parts of `c`. -/
private abbrev faaDiBrunoTerm (g : E' → F) (φ : E → E') (c : OrderedFinpartition (k + 1))
    (x : E) : E [×k + 1]→L[ℝ] F :=
  c.compAlongOrderedFinpartition (_root_.iteratedFDeriv ℝ c.length g (φ x))
    fun i ↦ _root_.iteratedFDeriv ℝ (c.partSize i) φ x

/-- The derivatives of `g` through order `k + 1`, evaluated along `φ`, are `α`-Hölder with
constant `3 ‖g‖ max(1, ‖Dφ‖)`. -/
private theorem dist_iteratedFDeriv_apply_le_of_fderiv_eq (hα : α ≤ 1) (hφ : Differentiable ℝ φ)
    (hψ : fderiv ℝ φ = ψ) (g : CkHolderSpace (k + 1) α E' F) {ℓ : ℕ} (hℓ : ℓ ≤ k + 1)
    (x y : E) :
    dist (_root_.iteratedFDeriv ℝ ℓ g (φ x)) (_root_.iteratedFDeriv ℝ ℓ g (φ y)) ≤
      3 * ‖g‖ * max 1 ‖ψ‖ * dist x y ^ (α : ℝ) := by
  have ha : 0 ≤ ‖ψ‖ := norm_nonneg _
  have hA : 1 ≤ max 1 ‖ψ‖ := le_max_left _ _
  have haα : ‖ψ‖ ^ (α : ℝ) ≤ max 1 ‖ψ‖ :=
    calc ‖ψ‖ ^ (α : ℝ) ≤ max 1 ‖ψ‖ ^ (α : ℝ) :=
          Real.rpow_le_rpow ha (le_max_right _ _) α.coe_nonneg
      _ ≤ max 1 ‖ψ‖ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by exact_mod_cast hα)
      _ = max 1 ‖ψ‖ := Real.rpow_one _
  have h := ((g.holderWith_iteratedFDeriv_of_le hα hℓ).comp
    (lipschitzWith_of_fderiv_eq hφ hψ).holderWith).dist_le x y
  rw [mul_one] at h
  push_cast at h
  calc dist (_root_.iteratedFDeriv ℝ ℓ g (φ x)) (_root_.iteratedFDeriv ℝ ℓ g (φ y))
      ≤ 3 * ‖g‖ * ‖ψ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ) := h
    _ ≤ 3 * ‖g‖ * max 1 ‖ψ‖ * dist x y ^ (α : ℝ) := by gcongr

/-- The power bookkeeping of one Faà di Bruno term: for `0 ≤ a ≤ A`, `1 ≤ A` and `ℓ ≤ n`,
`ℓ a^(ℓ - 1) a + a^ℓ A ≤ (n + 1) A^(n + 1)`. -/
private theorem natCast_mul_pow_mul_add_pow_mul_le {a A : ℝ} {ℓ n : ℕ} (ha : 0 ≤ a)
    (haA : a ≤ A) (hA : 1 ≤ A) (hℓ : ℓ ≤ n) :
    ℓ * a ^ (ℓ - 1) * a + a ^ ℓ * A ≤ (n + 1) * A ^ (n + 1) := by
  have hpow : a ^ ℓ ≤ A ^ (n + 1) :=
    (pow_le_pow_left₀ ha haA ℓ).trans (pow_le_pow_right₀ hA (by omega))
  have h₁ : (ℓ : ℝ) * a ^ (ℓ - 1) * a ≤ n * A ^ (n + 1) := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_mul, zero_mul]
      positivity
    · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hpos]
      exact mul_le_mul (by exact_mod_cast hℓ) hpow (by positivity) (by positivity)
  have h₂ : a ^ ℓ * A ≤ A ^ (n + 1) :=
    calc a ^ ℓ * A ≤ A ^ ℓ * A :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha haA ℓ) (by positivity)
      _ = A ^ (ℓ + 1) := (pow_succ A ℓ).symm
      _ ≤ A ^ (n + 1) := pow_le_pow_right₀ hA (by omega)
  linarith

/-- Each term of the Faà di Bruno formula for `D^{k+1}(g ∘ φ)` is `α`-Hölder with constant
`3 (k + 2) ‖g‖ max(1, ‖Dφ‖)^(k + 2)`. -/
private theorem dist_faaDiBrunoTerm_le (hα : α ≤ 1) (hφ : Differentiable ℝ φ)
    (hψ : fderiv ℝ φ = ψ) (g : CkHolderSpace (k + 1) α E' F) (c : OrderedFinpartition (k + 1))
    (x y : E) :
    dist (faaDiBrunoTerm g φ c x) (faaDiBrunoTerm g φ c y) ≤
      3 * (k + 2) * ‖g‖ * max 1 ‖ψ‖ ^ (k + 2) * dist x y ^ (α : ℝ) := by
  set a := ‖ψ‖
  set d := dist x y ^ (α : ℝ)
  have ha : 0 ≤ a := norm_nonneg _
  -- The derivatives of `φ` along the parts of `c`, as a point of the product space, and their
  -- variation between `x` and `y`.
  have hP (z : E) : ‖fun i ↦ _root_.iteratedFDeriv ℝ (c.partSize i) φ z‖ ≤ a :=
    (pi_norm_le_iff_of_nonneg ha).2 fun i ↦
      norm_iteratedFDeriv_le_of_fderiv_eq hψ (c.partSize_pos i) (c.partSize_le i) z
  have hPdiff : ‖(fun i ↦ _root_.iteratedFDeriv ℝ (c.partSize i) φ x) -
      fun i ↦ _root_.iteratedFDeriv ℝ (c.partSize i) φ y‖ ≤ 3 * a * d :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ by
      rw [Pi.sub_apply, ← dist_eq_norm]
      exact dist_iteratedFDeriv_le_of_fderiv_eq hα hψ (c.partSize_pos i) (c.partSize_le i) x y
  have hprod : ∏ i, ‖_root_.iteratedFDeriv ℝ (c.partSize i) φ y‖ ≤ a ^ c.length :=
    calc ∏ i, ‖_root_.iteratedFDeriv ℝ (c.partSize i) φ y‖ ≤ ∏ _i : Fin c.length, a :=
          Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) fun i _ ↦
            norm_iteratedFDeriv_le_of_fderiv_eq hψ (c.partSize_pos i) (c.partSize_le i) y
      _ = a ^ c.length := by simp
  have hgdiff := dist_iteratedFDeriv_apply_le_of_fderiv_eq hα hφ hψ g c.length_le x y
  rw [dist_eq_norm] at hgdiff ⊢
  -- Vary the derivatives of `φ` first, then the derivative of `g`.
  refine (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le _ _ _ _).trans ?_
  calc _ ≤ ‖g‖ * c.length * a ^ (c.length - 1) * (3 * a * d) +
        3 * ‖g‖ * max 1 a * d * a ^ c.length := by
        gcongr
        · exact g.norm_iteratedFDeriv_apply_le c.length_le _
        · exact max_le (hP x) (hP y)
    _ = 3 * ‖g‖ * d * (c.length * a ^ (c.length - 1) * a + a ^ c.length * max 1 a) := by ring
    _ ≤ 3 * ‖g‖ * d * ((k + 1 + 1) * max 1 a ^ (k + 1 + 1)) := by
        gcongr
        exact_mod_cast natCast_mul_pow_mul_add_pow_mul_le ha (le_max_right _ _) (le_max_left _ _)
          c.length_le
    _ = 3 * (k + 2) * ‖g‖ * max 1 a ^ (k + 2) * d := by ring

/-- The top derivative `D^{k+1}(g ∘ φ)` is `α`-Hölder with constant
`3 (k + 2) N ‖g‖ max(1, ‖Dφ‖)^(k + 2)`, `N` the number of ordered partitions of `k + 1`. -/
private theorem holderWith_iteratedFDeriv_comp (hα : α ≤ 1) (hφ : Differentiable ℝ φ)
    (hψ : fderiv ℝ φ = ψ) (g : CkHolderSpace (k + 1) α E' F) :
    HolderWith (3 * (k + 2) * Fintype.card (OrderedFinpartition (k + 1)) * ‖g‖₊ *
        max 1 ‖ψ‖₊ ^ (k + 2)) α (_root_.iteratedFDeriv ℝ (k + 1) (g ∘ φ)) := by
  have hφ' := contDiff_of_fderiv_eq hφ hψ
  have heq (z : E) : _root_.iteratedFDeriv ℝ (k + 1) (g ∘ φ) z =
      ∑ c : OrderedFinpartition (k + 1), faaDiBrunoTerm g φ c z := by
    rw [iteratedFDeriv_comp g.contDiff.contDiffAt hφ'.contDiffAt le_rfl]
    simp only [FormalMultilinearSeries.taylorComp,
      FormalMultilinearSeries.compAlongOrderedFinpartition, ftaylorSeries]
  refine holderOnWith_univ.1 <| HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [heq, heq, dist_eq_norm, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ c, ‖faaDiBrunoTerm g φ c x - faaDiBrunoTerm g φ c y‖
      ≤ ∑ _c : OrderedFinpartition (k + 1),
          3 * (k + 2) * ‖g‖ * max 1 ‖ψ‖ ^ (k + 2) * dist x y ^ (α : ℝ) :=
        Finset.sum_le_sum fun c _ ↦ by
          rw [← dist_eq_norm]
          exact dist_faaDiBrunoTerm_le hα hφ hψ g c x y
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

/-! ### The precomposition operator -/

/-- The derivatives of `g ∘ φ` through order `k + 1` are bounded by
`(k + 1)! ‖g‖ max(1, ‖Dφ‖)^(k + 2)`. -/
private theorem norm_iteratedFDeriv_comp_le_of_fderiv_eq (hφ : Differentiable ℝ φ)
    (hψ : fderiv ℝ φ = ψ) (g : CkHolderSpace (k + 1) α E' F) {i : ℕ} (hi : i ≤ k + 1) (x : E) :
    ‖_root_.iteratedFDeriv ℝ i (g ∘ φ) x‖ ≤ (k + 1).factorial * ‖g‖ * max 1 ‖ψ‖ ^ (k + 2) := by
  have hA : 1 ≤ max 1 ‖ψ‖ := le_max_left _ _
  refine (norm_iteratedFDeriv_comp_le (D := max 1 ‖ψ‖) g.contDiff (contDiff_of_fderiv_eq hφ hψ)
    (by exact_mod_cast hi) x (fun j hj ↦ g.norm_iteratedFDeriv_apply_le (hj.trans hi) _)
    fun j hj₁ hj ↦ ?_).trans ?_
  · exact (norm_iteratedFDeriv_le_of_fderiv_eq hψ hj₁ (hj.trans hi) x).trans
      ((le_max_right _ _).trans (le_self_pow₀ hA (by omega)))
  · have hfac : (i.factorial : ℝ) ≤ (k + 1).factorial := by exact_mod_cast Nat.factorial_le hi
    have hpow : max 1 ‖ψ‖ ^ i ≤ max 1 ‖ψ‖ ^ (k + 2) := pow_le_pow_right₀ hA (by omega)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hfac (norm_nonneg g)) hpow (by positivity)
      (by positivity)

/-- Precomposition of a bounded `C^{k+1,α}` map by `φ`. -/
private def comp (hα : α ≤ 1) (φ : E → E') (ψ : CkHolderSpace k α E (E →L[ℝ] E'))
    (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ) (g : CkHolderSpace (k + 1) α E' F) :
    CkHolderSpace (k + 1) α E F :=
  ofContDiff (g ∘ φ) (g.contDiff.comp (contDiff_of_fderiv_eq hφ hψ))
    (fun _ hi ↦ ⟨_, norm_iteratedFDeriv_comp_le_of_fderiv_eq hφ hψ g hi⟩)
    (holderWith_iteratedFDeriv_comp hα hφ hψ g).memHolder

private theorem coe_comp (hα : α ≤ 1) (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ)
    (g : CkHolderSpace (k + 1) α E' F) : ⇑(comp hα φ ψ hφ hψ g) = g ∘ φ :=
  coe_ofContDiff ..

/-- The norm bound for precomposition by `φ`. -/
private theorem norm_comp_le (hα : α ≤ 1) (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ)
    (g : CkHolderSpace (k + 1) α E' F) :
    ‖comp hα φ ψ hφ hψ g‖ ≤
      ((k + 2).factorial + 3 * (k + 2) * Fintype.card (OrderedFinpartition (k + 1))) *
        max 1 ‖ψ‖ ^ (k + 2) * ‖g‖ := by
  have h := norm_le_of_norm_iteratedFDeriv_le_of_holderWith (f := comp hα φ ψ hφ hψ g)
    (fun i hi x ↦ by
      rw [coe_comp]
      exact norm_iteratedFDeriv_comp_le_of_fderiv_eq hφ hψ g hi x)
    (by rw [coe_comp]; exact holderWith_iteratedFDeriv_comp hα hφ hψ g)
  refine h.trans (le_of_eq ?_)
  rw [Nat.factorial_succ (k + 1)]
  push_cast
  ring

/-- **Precomposition by a `C^{k+1,α}` map.** Let `0 ≤ α ≤ 1` and let `φ : E → E'` be
differentiable with derivative `Dφ = ψ` a bounded `C^{k,α}` map. Then `g ↦ g ∘ φ` is a bounded
linear operator from `C_b^{k+1,α}(E', F)` to `C_b^{k+1,α}(E, F)`; its norm is bounded in
`norm_compOfFDerivL_le`. The map `φ` need not be bounded. -/
def compOfFDerivL (hα : α ≤ 1) (φ : E → E') (ψ : CkHolderSpace k α E (E →L[ℝ] E'))
    (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ) :
    CkHolderSpace (k + 1) α E' F →L[ℝ] CkHolderSpace (k + 1) α E F :=
  LinearMap.mkContinuous
    { toFun := comp hα φ ψ hφ hψ
      map_add' g h := ext fun x ↦ by simp [coe_comp, coe_add]
      map_smul' c g := ext fun x ↦ by simp [coe_comp, coe_smul] }
    _ (norm_comp_le hα hφ hψ)

/-- The values of the precomposition `compOfFDerivL … g` are `g (φ x)`. -/
@[simp]
theorem compOfFDerivL_apply (hα : α ≤ 1) (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ)
    (g : CkHolderSpace (k + 1) α E' F) (x : E) : compOfFDerivL hα φ ψ hφ hψ g x = g (φ x) :=
  congrFun (coe_comp hα hφ hψ g) x

@[simp]
theorem coe_compOfFDerivL (hα : α ≤ 1) (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ)
    (g : CkHolderSpace (k + 1) α E' F) : ⇑(compOfFDerivL hα φ ψ hφ hψ g) = g ∘ φ :=
  funext (compOfFDerivL_apply hα hφ hψ g)

/-- **The chain rule bound in bounded Hölder spaces.** Precomposition by `φ` multiplies the
`C^{k+1,α}` norm by at most `((k + 2)! + 3 (k + 2) N) max(1, ‖Dφ‖)^(k + 2)`, where `N` is the
number of ordered partitions of a set of `k + 1` elements and `‖Dφ‖` is the `C^{k,α}` norm of the
derivative `Dφ = ψ`. -/
theorem norm_compOfFDerivL_le (hα : α ≤ 1) (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ) :
    ‖compOfFDerivL (F := F) hα φ ψ hφ hψ‖ ≤
      ((k + 2).factorial + 3 * (k + 2) * Fintype.card (OrderedFinpartition (k + 1))) *
        max 1 ‖ψ‖ ^ (k + 2) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_comp_le hα hφ hψ)

/-- **Change of variables by a `C^{k+1,α}` diffeomorphism.** Let `0 ≤ α ≤ 1` and let `φ : E ≃ E'`
be a bijection such that `φ` and `φ.symm` are differentiable with derivatives `ψ` and `ψ'` that
are bounded `C^{k,α}` maps. Then precomposition by `φ` is an isomorphism
`C_b^{k+1,α}(E', F) ≃L[ℝ] C_b^{k+1,α}(E, F)`, with inverse precomposition by `φ.symm`. -/
def compOfFDerivCLE (hα : α ≤ 1) (φ : E ≃ E') (ψ : CkHolderSpace k α E (E →L[ℝ] E'))
    (ψ' : CkHolderSpace k α E' (E' →L[ℝ] E)) (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ)
    (hφ' : Differentiable ℝ φ.symm) (hψ' : fderiv ℝ φ.symm = ψ') :
    CkHolderSpace (k + 1) α E' F ≃L[ℝ] CkHolderSpace (k + 1) α E F :=
  { compOfFDerivL hα φ ψ hφ hψ with
    invFun := compOfFDerivL hα φ.symm ψ' hφ' hψ'
    left_inv g := ext fun x ↦ by simp
    right_inv g := ext fun x ↦ by simp
    continuous_toFun := (compOfFDerivL hα φ ψ hφ hψ).continuous
    continuous_invFun := (compOfFDerivL hα φ.symm ψ' hφ' hψ').continuous }

@[simp]
theorem compOfFDerivCLE_apply (hα : α ≤ 1) (φ : E ≃ E') (ψ : CkHolderSpace k α E (E →L[ℝ] E'))
    (ψ' : CkHolderSpace k α E' (E' →L[ℝ] E)) (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ)
    (hφ' : Differentiable ℝ φ.symm) (hψ' : fderiv ℝ φ.symm = ψ')
    (g : CkHolderSpace (k + 1) α E' F) :
    compOfFDerivCLE hα φ ψ ψ' hφ hψ hφ' hψ' g = compOfFDerivL hα φ ψ hφ hψ g :=
  (rfl)

@[simp]
theorem compOfFDerivCLE_symm_apply (hα : α ≤ 1) (φ : E ≃ E') (ψ : CkHolderSpace k α E (E →L[ℝ] E'))
    (ψ' : CkHolderSpace k α E' (E' →L[ℝ] E)) (hφ : Differentiable ℝ φ) (hψ : fderiv ℝ φ = ψ)
    (hφ' : Differentiable ℝ φ.symm) (hψ' : fderiv ℝ φ.symm = ψ')
    (g : CkHolderSpace (k + 1) α E F) :
    (compOfFDerivCLE hα φ ψ ψ' hφ hψ hφ' hψ').symm g = compOfFDerivL hα φ.symm ψ' hφ' hψ' g :=
  (rfl)

end TauCeti.CkHolderSpace
