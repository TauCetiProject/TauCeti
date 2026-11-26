/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HalfSpace.Basic
import TauCeti.Analysis.Calculus.ContDiff.BoundedDerivatives
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.OrthogonalSpanSingleton
import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.Sobolev.WeakDeriv.NormalTangential
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Analysis.Sobolev.Wkp.BoundedMultiplication

/-!
# `H^{m+2}` regularity up to the boundary of a half-space

Let `Ω = {x | c < ⟪x, ν⟫}` be an open half-space in `ℝⁿ`, or more generally a convex open set
mapped into itself by every translation orthogonal to `ν`, such as a slab. Let `m ≥ 0`, let `a`
be uniformly elliptic and bounded on `Ω`, Lipschitz there as a bilinear form, with entries of
class `C^{m+1}` on `Ω` whose derivatives of order `2` to `m + 1` are bounded on `Ω`, and let
`u ∈ H¹₀(Ω)` be the weak solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω`, `u = 0` on `∂Ω`, with `F ∈ H^m(Ω)`.

This file proves that `u ∈ H^{m+2}(Ω)`, globally on `Ω` and not only on compactly contained
subsets (`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_halfSpace_of_contDiffOn`). Each
derivative of the data and of the coefficients buys one more derivative of the solution up to the
boundary. This is the flat model of higher regularity up to the boundary: flattening the boundary
of a domain of class `C^{m+2}` turns the equation in each chart into one of this form. The case
`m = 0` is `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace`; the case `m = 1`,
for coefficients whose first derivatives are Lipschitz, is
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_halfSpace`.

## The argument

The proof is by induction on `m`, the case `m = 0` being `H²` regularity up to the boundary
(Evans, §6.3.2, Theorem 4). Suppose `F ∈ H^{m+1}(Ω)`, so that `u ∈ H^{m+2}(Ω)` by induction.

* **Tangential directions.** For `τ` orthogonal to `ν`, the derivative `∂_τ u` lies in `H¹₀(Ω)`
  (`TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_of_mapsTo`) and solves the
  differentiated equation `-∂ᵢ(aⁱʲ ∂ⱼ(∂_τ u)) = ∂_τ F + ∑ᵢⱼ (∂ᵢ∂_τaⁱʲ ∂ⱼu + ∂_τaⁱʲ ∂ᵢ∂ⱼu)`, whose
  right-hand side lies in `H^m(Ω)`: multiplication by the derivatives of the coefficients, which
  are bounded on `Ω` with their derivatives, preserves `H^m(Ω)`
  (`TauCeti.PDE.exists_hasWeakLineDerivOn_and_energyFormH1_eq_setIntegral_of_bddDerivOn`). The
  induction hypothesis puts `∂_τ u` in `H^{m+2}(Ω)`.
* **The normal direction.** With `e = ν / ‖ν‖`, every second derivative `∂_w ∂_y u` is
  `⟪e, y⟫ ⟪e, w⟫ ∂_e ∂_e u` plus derivatives of the `∂_τ u` with `τ` tangential
  (`TauCeti.Wkp.ae_inner_gradient_firstOrder_lineDerivL_eq`), which lie in `H^{m+1}(Ω)`. The
  equation, holding almost everywhere since `u ∈ H²(Ω)`, therefore gives
  `ρ ∂_e ∂_e u ∈ H^{m+1}(Ω)` for `ρ = ⟪e, a e⟫ ≥ λ`, and dividing by `ρ`
  (`TauCeti.Wkp.exists_value_eq_of_value_ae_eq_mul`) puts `∂_e ∂_e u` in `H^{m+1}(Ω)`.
* **Assembly.** The derivatives of `∂_e u` along `e` and along the tangential directions lie in
  `H^{m+1}(Ω)`, so `∂_e u ∈ H^{m+2}(Ω)`; together with the tangential derivatives this puts every
  first derivative of `u` in `H^{m+2}(Ω)`, that is, `u ∈ H^{m+3}(Ω)`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_mapsTo_of_contDiffOn`: `H^{m+2}`
  regularity up to the boundary on a convex open set invariant under the translations orthogonal
  to `ν`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_halfSpace_of_contDiffOn`: the
  half-space case.
* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_mapsTo` and its half-space case
  `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_halfSpace`: `H³` regularity, the case
  `m = 1`, for coefficients whose first derivatives are Lipschitz.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorem 5.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.13.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions InnerProductSpace Matrix NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c : ℝ} {K : ℝ≥0} {ν : EuclideanSpace ℝ ι}

/-- **Tangential derivatives gain the regularity of the data.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_of_mapsTo`, suppose that the entries of
`a` are of class `C^{m+2}` on `Ω` with bounded derivatives, that the Dirichlet problem with
forcing in `W^{m,2}(Ω)` has its solutions in `W^{m+2,2}(Ω)`, that `F ∈ W^{m+1,2}(Ω)`, and that the
solution `u` is the value of `U ∈ W^{m+2,2}(Ω)`. Then along every `τ` orthogonal to `ν` the
derivative `∂_τ u` lies in `W^{m+2,2}(Ω)`. -/
private theorem exists_hasWeakLineDerivOn_tangential (hν : ν ≠ 0)
    (hΩc : Convex ℝ (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) {m : ℕ}
    (hbd : ∀ i j, BddDerivOn ℝ (m + 2) (fun x => a x i j) (Omega : Set (EuclideanSpace ℝ ι)))
    (ih : ∀ (G : Wkp mu Omega 2 m) (t : W1p0 mu Omega 2),
      IsWeakSolutionDirichlet a 0 0 (Wkp.value m G) t →
        ∃ W : Wkp mu Omega 2 (m + 2), Wkp.value (m + 2) W = W1p.value (t : W1p mu Omega 2))
    {F : Wkp mu Omega 2 (m + 1)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value (m + 1) F) u)
    {U : Wkp mu Omega 2 (m + 2)} (hU : Wkp.value (m + 2) U = W1p.value (u : W1p mu Omega 2))
    {τ : EuclideanSpace ℝ ι} (hτ : ⟪τ, ν⟫_ℝ = 0) :
    ∃ T : Wkp mu Omega 2 (m + 2),
      HasWeakLineDerivOn mu Omega (Wkp.value (m + 2) U) (Wkp.value (m + 2) T) τ := by
  -- `∂_τ u ∈ H¹₀(Ω)`, and it solves the differentiated equation with forcing `G ∈ W^{m,2}(Ω)`.
  obtain ⟨t, ht⟩ := ha.exists_hasWeakLineDerivOn_of_mapsTo hν hΩc hΩ hK hu hτ
  obtain ⟨d, G, hd, hG⟩ := exists_hasWeakLineDerivOn_and_energyFormH1_eq_setIntegral_of_bddDerivOn
    m hbd ⟨U, hU⟩ ((isWeakSolutionDirichlet_iff _ _).1 hu) τ
  obtain rfl : d = (t : W1p mu Omega 2) := W1p.ext_value (Lp.ext (hd.ae_eq ht))
  -- The induction hypothesis puts `∂_τ u` in `W^{m+2,2}(Ω)`.
  obtain ⟨T, hT⟩ := ih G t ((isWeakSolutionDirichlet_iff _ _).2 hG)
  exact ⟨T, by rw [hU, hT]; exact ht⟩

/-- For a unit vector `e`, the coefficient `ρ = ∑ᵢⱼ eᵢ eⱼ aⁱʲ = ⟪e, a e⟫` of the purely normal
second derivative has bounded derivatives along with the entries of `a`, and `λ ≤ ρ` on `Ω`. -/
private theorem bddDerivOn_sum_inner_smul_and_le {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {m : ℕ}
    (hbd : ∀ i j, BddDerivOn ℝ m (fun x => a x i j) (Omega : Set (EuclideanSpace ℝ ι))) :
    BddDerivOn ℝ m (fun x => ∑ i, ∑ j, (⟪e, EuclideanSpace.basisFun ι ℝ i⟫_ℝ *
        ⟪e, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) • a x i j) (Omega : Set (EuclideanSpace ℝ ι)) ∧
      ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
        lam ≤ ∑ i, ∑ j, (⟪e, EuclideanSpace.basisFun ι ℝ i⟫_ℝ *
          ⟪e, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) • a x i j := by
  refine ⟨BddDerivOn.sum Omega.isOpen fun i _ => BddDerivOn.sum Omega.isOpen fun j _ =>
    (hbd i j).const_smul Omega.isOpen _, fun x hx => ?_⟩
  -- `ρ(x) = ⟪e, a(x) e⟫ ≥ λ ‖e‖² = λ`.
  have hrho : ∑ i, ∑ j, (⟪e, EuclideanSpace.basisFun ι ℝ i⟫_ℝ *
      ⟪e, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) • a x i j = matrixBilinearForm (a x) e e := by
    rw [matrixBilinearForm_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [EuclideanSpace.inner_basisFun_real, EuclideanSpace.inner_basisFun_real, smul_eq_mul]
  rw [hrho, matrixBilinearForm_self]
  simpa only [he, one_pow, mul_one] using ha.lower_bound hx e

/-- **The purely normal second derivative from the equation.** Let `e` be a unit vector, let `a`
be uniformly elliptic on `Ω` with entries of class `C^{m+2}` with bounded derivatives, and let
`u ∈ H¹₀(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = F` with `F ∈ W^{m+1,2}(Ω)`. Suppose that `u` is the value of
`U ∈ W^{m+2,2}(Ω)` whose derivatives `T τ` along the directions `τ` orthogonal to `e` lie in
`W^{m+2,2}(Ω)`. Then `∂_e ∂_e u` lies in `W^{m+1,2}(Ω)`: in the equation, solved for
`⟪e, a e⟫ ∂_e ∂_e u`, every other term lies in `W^{m+1,2}(Ω)`, and `⟪e, a e⟫ ≥ λ`. -/
private theorem exists_hasWeakLineDerivOn_normal {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {m : ℕ}
    (hbd : ∀ i j, BddDerivOn ℝ (m + 2) (fun x => a x i j) (Omega : Set (EuclideanSpace ℝ ι)))
    {F : Wkp mu Omega 2 (m + 1)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value (m + 1) F) u)
    {U : Wkp mu Omega 2 (m + 2)} (hU : Wkp.value (m + 2) U = W1p.value (u : W1p mu Omega 2))
    {T : EuclideanSpace ℝ ι → Wkp mu Omega 2 (m + 2)}
    (hT : ∀ τ, ⟪τ, e⟫_ℝ = 0 →
      HasWeakLineDerivOn mu Omega (Wkp.value (m + 2) U) (Wkp.value (m + 2) (T τ)) τ) :
    ∃ N : Wkp mu Omega 2 (m + 1), HasWeakLineDerivOn mu Omega
      (Wkp.value (m + 1) (Wkp.lineDerivL e (m + 1) U)) (Wkp.value (m + 1) N) e := by
  set b := EuclideanSpace.basisFun ι ℝ with hb
  set P := (ℝ ∙ e)ᗮ.starProjection
  set Dee := Wkp.lineDerivL e m (Wkp.lineDerivL e (m + 1) U)
  set D : ι → Wkp mu Omega 2 (m + 1) := fun j => Wkp.lineDerivL (b j) (m + 1) U
  have hD : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value (u : W1p mu Omega 2))
      (W1p.value (Wkp.firstOrder m (D j))) (b j) := fun j => by
    rw [Wkp.value_firstOrder, ← hU]; exact Wkp.hasWeakLineDerivOn_lineDerivL _ _ _
  -- The equation holds almost everywhere, since `u ∈ H²(Ω)`.
  have heq := ae_sum_sum_eq_neg_of_hasWeakLineDerivOn
    (fun i j => (hbd i j).contDiffOn.of_le (by norm_cast; omega))
    (Wkp.locallyIntegrableOn_value (m + 1) F) hu.energyFormH1_ofTestFunctionₗ hD
  rw [← hb] at heq
  -- The first derivatives; the second derivatives split along `e` and the hyperplane, by
  -- `TauCeti.Wkp.ae_inner_gradient_firstOrder_lineDerivL_eq`, into `∂_e ∂_e u` and the terms `R`.
  have hg₁ : ∀ᵐ x ∂mu.restrict Omega, ∀ j, ⟪W1p.gradient (u : W1p mu Omega 2) x, b j⟫_ℝ =
      Wkp.value (m + 1) (D j) x := Filter.eventually_all.2 fun j => by
    filter_upwards [((W1p.hasWeakFDerivOn (u : W1p mu Omega 2)).hasWeakLineDerivOn (b j)).ae_eq
      (by simpa only [Wkp.value_firstOrder] using hD j)] with x hx
    rw [← hx, innerSL_apply_apply]
  set R : ι → ι → Wkp mu Omega 2 (m + 1) := fun i j =>
    ⟪e, b j⟫_ℝ • Wkp.lineDerivL e (m + 1) (T (P (b i))) + Wkp.lineDerivL (b i) (m + 1) (T (P (b j)))
  -- The other terms of the equation lie in `W^{m+1,2}(Ω)`.
  choose Y₁ hY₁ using fun i j => Wkp.exists_value_ae_eq_mul_of_bddDerivOn
    ((hbd i j).fderiv_apply Omega.isOpen (b i)) (D j)
  choose Y₂ hY₂ using fun i j => Wkp.exists_value_ae_eq_mul_of_bddDerivOn
    ((hbd i j).of_le (by omega)) (R i j)
  -- The coefficient `ρ = ⟪e, a e⟫` of `∂_e ∂_e u` is bounded below by `λ`.
  set rho : EuclideanSpace ℝ ι → ℝ := fun x => ∑ i, ∑ j, (⟪e, b i⟫_ℝ * ⟪e, b j⟫_ℝ) • a x i j
  obtain ⟨hrho, hrl⟩ := bddDerivOn_sum_inner_smul_and_le (m := m + 1) he ha
    fun i j => (hbd i j).of_le (by omega)
  -- By the equation, `ρ ∂_e ∂_e u = -F - ∑ᵢⱼ (∂ᵢaⁱʲ ∂ⱼu + aⁱʲ Rᵢⱼ) ∈ W^{m+1,2}(Ω)`.
  have hDee : (Wkp.value (m + 1) (-F + ∑ i, ∑ j, (-Y₁ i j + -Y₂ i j)) :
      EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] fun x => rho x * Wkp.value m Dee x := by
    filter_upwards [Wkp.ae_value_add_sum_eq (-F) Finset.univ Finset.univ (fun i j => -Y₁ i j)
        (fun i j => -Y₂ i j) (c₁ := fun i j x => -(fderiv ℝ (fun y => a y i j) x (b i) *
          Wkp.value (m + 1) (D j) x))
        (c₂ := fun i j x => -(a x i j * Wkp.value (m + 1) (R i j) x))
        (Wkp.ae_forall_value_neg_eq hY₁ _ _) (Wkp.ae_forall_value_neg_eq hY₂ _ _),
      Wkp.value_neg_ae (m + 1) F, heq, hg₁, Filter.eventually_all.2 fun i =>
        Filter.eventually_all.2 fun j =>
          Wkp.ae_inner_gradient_firstOrder_lineDerivL_eq he hT (b i) (b j)]
      with x hx hF hx₀ hx₁ hx₂
    rw [hx, hF, Pi.neg_apply, ← hx₀]
    simp only [hx₁, D, R, hx₂, rho, smul_eq_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- Dividing by `ρ ≥ λ` puts `∂_e ∂_e u` in `W^{m+1,2}(Ω)`.
  obtain ⟨N, hN⟩ :=
    Wkp.exists_value_eq_of_value_ae_eq_mul hrho ha.pos hrl (Wkp.value m Dee) _ hDee
  exact ⟨N, by rw [hN]; exact Wkp.hasWeakLineDerivOn_lineDerivL _ _ _⟩

/-- **The induction on the order.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`: if the entries of `a` are of
class `C^{m+1}` on `Ω` with bounded derivatives, then every solution `u ∈ H¹₀(Ω)` of the Dirichlet
problem with forcing in `W^{m,2}(Ω)` lies in `W^{m+2,2}(Ω)`. -/
private theorem exists_value_eq_value_of_mapsTo_of_bddDerivOn (hν : ν ≠ 0)
    (hΩc : Convex ℝ (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) :
    ∀ m : ℕ, (∀ i j, BddDerivOn ℝ (m + 1) (fun x => a x i j) (Omega : Set (EuclideanSpace ℝ ι))) →
      ∀ (F : Wkp mu Omega 2 m) (u : W1p0 mu Omega 2),
        IsWeakSolutionDirichlet a 0 0 (Wkp.value m F) u →
          ∃ W : Wkp mu Omega 2 (m + 2), Wkp.value (m + 2) W = W1p.value (u : W1p mu Omega 2)
  | 0, _, F, u, hu => by
    obtain ⟨U, hU⟩ := ha.exists_lowerOrder_eq_of_mapsTo hν hΩ hK hu
    refine ⟨U, ?_⟩
    rw [Wkp.value_succ, hU]
    exact Wkp.value_one (u : W1p mu Omega 2)
  | m + 1, hbd, F, u, hu => by
    have ih := exists_value_eq_value_of_mapsTo_of_bddDerivOn hν hΩc hΩ ha hK m
      fun i j => (hbd i j).of_le (by omega)
    obtain ⟨U, hU⟩ := ih (Wkp.lowerOrder m F) u (by rwa [← Wkp.value_succ])
    set b := EuclideanSpace.basisFun ι ℝ
    set e : EuclideanSpace ℝ ι := ‖ν‖⁻¹ • ν
    have he : ‖e‖ = 1 := norm_smul_inv_norm hν
    set P := (ℝ ∙ e)ᗮ.starProjection
    have hP : ∀ z, ⟪P z, e⟫_ℝ = 0 := inner_starProjection_orthogonal_singleton_eq_zero ℝ e
    -- The derivatives along the directions orthogonal to `e`, hence to `ν`.
    have htan : ∀ τ, ∃ T : Wkp mu Omega 2 (m + 2), ⟪τ, e⟫_ℝ = 0 →
        HasWeakLineDerivOn mu Omega (Wkp.value (m + 2) U) (Wkp.value (m + 2) T) τ := fun τ => by
      by_cases hτ : ⟪τ, e⟫_ℝ = 0
      · have hτν : ⟪τ, ν⟫_ℝ = 0 := by
          rw [real_inner_smul_right] at hτ
          exact (mul_eq_zero.1 hτ).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hν))
        obtain ⟨T, hT⟩ := exists_hasWeakLineDerivOn_tangential hν hΩc hΩ ha hK hbd
          (ih := ih) hu hU hτν
        exact ⟨T, fun _ => hT⟩
      · exact ⟨0, fun h => absurd h hτ⟩
    choose T hT using htan
    -- The purely normal second derivative, and then `∂_e u ∈ W^{m+2,2}(Ω)`.
    obtain ⟨N, hN⟩ := exists_hasWeakLineDerivOn_normal he ha hbd hu hU hT
    have hDe := Wkp.hasWeakLineDerivOn_lineDerivL e (m + 1) U
    -- Each derivative splits into its normal and tangential parts.
    obtain ⟨Ne, hNe⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b
      (Wkp.value (m + 1) (Wkp.lineDerivL e (m + 1) U)) (m + 1) fun i =>
        ⟨⟪e, b i⟫_ℝ • N + Wkp.lineDerivL e (m + 1) (T (P (b i))), by
          rw [Wkp.value_add, Wkp.value_smul]
          exact hN.smul_add_of_normal_tangential he ((hT _ (hP (b i))).comm
            (Wkp.hasWeakLineDerivOn_lineDerivL e (m + 1) (T (P (b i)))) hDe)⟩
    -- Every first derivative of `u` lies in `W^{m+2,2}(Ω)`.
    obtain ⟨W, hW⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b
      (Wkp.value (m + 2) U) (m + 2) fun i =>
        ⟨⟪e, b i⟫_ℝ • Ne + T (P (b i)), by
          rw [Wkp.value_add, Wkp.value_smul, hNe]
          exact hDe.smul_add_of_normal_tangential he (hT _ (hP (b i)))⟩
    exact ⟨W, hW.trans hU⟩

/-- **`H^{m+2}` regularity up to the boundary.** Let `ν ≠ 0` and let `Ω` be convex and mapped into
itself by every translation orthogonal to `ν`, as a half-space `{x | c < ⟪x, ν⟫}` or a slab is.
Let `a` be uniformly elliptic and bounded on `Ω`, with `x ↦ a(x)` Lipschitz on `Ω` as a bilinear
form, and with entries of class `C^{m+1}` on `Ω` whose derivatives of order `2` to `m + 1` are
bounded on `Ω` by `C`. Let `F ∈ W^{m,2}(Ω)` and let `u ∈ H¹₀(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = F`, that is, of the Dirichlet problem with zero boundary values. Then `u` is the
value of an element of `W^{m+2,2}(Ω)`: its derivatives of order `m + 2` lie in `L²(Ω)` up to the
boundary. No regularity of `∂Ω` is assumed.

For `m = 0` this is `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_of_mapsTo_of_contDiffOn (hν : ν ≠ 0)
    (hΩc : Convex ℝ (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) (m : ℕ)
    (hsmooth : ∀ i j, ContDiffOn ℝ (m + 1) (fun x => a x i j) Omega) {C : ℝ}
    (hC : ∀ i j, ∀ k, 2 ≤ k → k ≤ m + 1 → ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ‖iteratedFDeriv ℝ k (fun y => a y i j) x‖ ≤ C)
    {F : Wkp mu Omega 2 m} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value m F) u) :
    ∃ W : Wkp mu Omega 2 (m + 2), Wkp.value (m + 2) W = W1p.value (u : W1p mu Omega 2) := by
  -- The entries of `a` are bounded by `Λ` and `K`-Lipschitz on `Ω`, so their derivatives of every
  -- order at most `m + 1` are bounded on `Ω`.
  have hbd : ∀ i j, BddDerivOn ℝ (m + 1) (fun x => a x i j)
      (Omega : Set (EuclideanSpace ℝ ι)) := fun i j => by
    refine bddDerivOn_iff.2 ⟨hsmooth i j, max (max Lam K) C, fun k hk x hx => ?_⟩
    rcases k with _ | _ | k
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (ha.abs_apply_le hx i j).trans ((le_max_left _ _).trans (le_max_left _ _))
    · rw [norm_iteratedFDeriv_one]
      exact (norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hx)
        (lipschitzOnWith_apply_apply_of_matrixBilinearForm hK i j)).trans
        ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hC i j (k + 2) (by omega) hk x hx).trans (le_max_right _ _)
  exact exists_value_eq_value_of_mapsTo_of_bddDerivOn hν hΩc hΩ ha hK m hbd F u hu

/-- **`H^{m+2}` regularity up to the boundary of a half-space.** Let `Ω = {x | c < ⟪x, ν⟫}` with
`ν ≠ 0`, let `a` be uniformly elliptic and bounded on `Ω`, with `x ↦ a(x)` Lipschitz on `Ω` as a
bilinear form, and with entries of class `C^{m+1}` on `Ω` whose derivatives of order `2` to
`m + 1` are bounded on `Ω`. Let `F ∈ W^{m,2}(Ω)` and let `u ∈ H¹₀(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = F`. Then `u` is the value of an element of `W^{m+2,2}(Ω)`. This is the half-space
case of `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_mapsTo_of_contDiffOn`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_of_halfSpace_of_contDiffOn (hν : ν ≠ 0)
    (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) (m : ℕ)
    (hsmooth : ∀ i j, ContDiffOn ℝ (m + 1) (fun x => a x i j) Omega) {C : ℝ}
    (hC : ∀ i j, ∀ k, 2 ≤ k → k ≤ m + 1 → ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ‖iteratedFDeriv ℝ k (fun y => a y i j) x‖ ≤ C)
    {F : Wkp mu Omega 2 m} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (Wkp.value m F) u) :
    ∃ W : Wkp mu Omega 2 (m + 2), Wkp.value (m + 2) W = W1p.value (u : W1p mu Omega 2) :=
  ha.exists_value_eq_value_of_mapsTo_of_contDiffOn hν (TauCeti.convex_of_halfSpace hΩ)
    (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτ) hK m hsmooth hC hu

/-- **`H³` regularity up to the boundary.** Let `ν ≠ 0` and let `Ω` be convex and mapped into
itself by every translation orthogonal to `ν`, as a half-space `{x | c < ⟪x, ν⟫}` or a slab is.
Let `a` be uniformly elliptic and bounded on `Ω`, with entries of class `C²` on `Ω`, `x ↦ a(x)`
Lipschitz on `Ω` as a bilinear form and the first derivatives of its entries Lipschitz on `Ω`. Let
`F ∈ H¹(Ω)` and let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = F`, that is, of the
Dirichlet problem with zero boundary values. Then `u` is the value of an element of `W^{3,2}(Ω)`:
its third weak derivatives lie in `L²(Ω)` up to the boundary. No regularity of `∂Ω` is assumed.

This is the case `m = 1` of
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_mapsTo_of_contDiffOn`: the Lipschitz
constant `K'` of the first derivatives bounds the second derivatives. -/
theorem UniformlyEllipticOn.exists_value_eq_value_of_mapsTo (hν : ν ≠ 0)
    (hΩc : Convex ℝ (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hsmooth : ∀ i j, ContDiffOn ℝ 2 (fun x => a x i j) Omega) {K' : ℝ≥0}
    (hK' : ∀ i j, LipschitzOnWith K' (fun x => fderiv ℝ (fun y => a y i j) x) Omega)
    {F : W1p mu Omega 2} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (W1p.value F) u) :
    ∃ W : Wkp mu Omega 2 3, Wkp.value 3 W = W1p.value (u : W1p mu Omega 2) :=
  ha.exists_value_eq_value_of_mapsTo_of_contDiffOn hν hΩc hΩ hK 1 hsmooth (C := K')
    (fun i j k hk₂ hk x hx => by
      obtain rfl : k = 2 := by omega
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
      exact norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hx) (hK' i j))
    (F := F) (by convert hu using 2; exact Wkp.value_one F)

/-- **`H³` regularity up to the boundary of a half-space.** Let `Ω = {x | c < ⟪x, ν⟫}` with
`ν ≠ 0`, let `a` be uniformly elliptic and bounded on `Ω`, with entries of class `C²` on `Ω`,
`x ↦ a(x)` Lipschitz on `Ω` as a bilinear form and the first derivatives of its entries Lipschitz
on `Ω`, let `F ∈ H¹(Ω)` and let `u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = F`. Then `u`
is the value of an element of `W^{3,2}(Ω)`. This is the half-space case of
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_of_halfSpace (hν : ν ≠ 0)
    (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hsmooth : ∀ i j, ContDiffOn ℝ 2 (fun x => a x i j) Omega) {K' : ℝ≥0}
    (hK' : ∀ i j, LipschitzOnWith K' (fun x => fderiv ℝ (fun y => a y i j) x) Omega)
    {F : W1p mu Omega 2} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 (W1p.value F) u) :
    ∃ W : Wkp mu Omega 2 3, Wkp.value 3 W = W1p.value (u : W1p mu Omega 2) :=
  ha.exists_value_eq_value_of_mapsTo hν (TauCeti.convex_of_halfSpace hΩ)
    (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hΩ hτ) hK hsmooth hK' hu

end PDE

end TauCeti
