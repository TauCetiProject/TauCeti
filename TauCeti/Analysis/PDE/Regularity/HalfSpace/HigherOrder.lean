/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HalfSpace.Basic
import TauCeti.Analysis.Calculus.ContDiff.BoundedDerivatives
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.OrthogonalSpanSingleton
import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
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
of a domain of class `C^{m+2}` turns the equation in each chart into one of this form. The cases
`m = 0` and `m = 1` are `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace` and,
for smooth coefficients, `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_halfSpace`.

## The argument

The proof is by induction on `m`, the case `m = 0` being `H²` regularity up to the boundary
(Evans, §6.3.2, Theorem 4). Suppose `F ∈ H^{m+1}(Ω)`, so that `u ∈ H^{m+2}(Ω)` by induction.

* **Tangential directions.** For `τ` orthogonal to `ν`, the derivative `∂_τ u` lies in `H¹₀(Ω)`
  (`TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_of_mapsTo`) and solves the
  differentiated equation `-∂ᵢ(aⁱʲ ∂ⱼ(∂_τ u)) = ∂_τ F + ∑ᵢⱼ (∂ᵢ∂_τaⁱʲ ∂ⱼu + ∂_τaⁱʲ ∂ᵢ∂ⱼu)`, whose
  right-hand side lies in `H^m(Ω)`: multiplication by the derivatives of the coefficients, which
  are bounded on `Ω` with their derivatives, preserves `H^m(Ω)`
  (`TauCeti.Wkp.exists_value_ae_eq_mul_of_norm_iteratedFDeriv_le`). The induction hypothesis puts
  `∂_τ u` in `H^{m+2}(Ω)`.
* **The normal direction.** With `e = ν / ‖ν‖`, every second derivative `∂_w ∂_y u` is
  `⟪e, y⟫ ⟪e, w⟫ ∂_e ∂_e u` plus derivatives of the `∂_τ u` with `τ` tangential, which lie in
  `H^{m+1}(Ω)`. The equation, holding almost everywhere since `u ∈ H²(Ω)`, therefore gives
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

/-! ### Coefficients with bounded derivatives -/

section BddDerivOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k l : ℕ}
  {psi : E → ℝ}

/-- `ψ` is `Cᵏ` on `s`, and its derivatives of order at most `k` are bounded on `s`. -/
private def BddDerivOn (s : Set E) (k : ℕ) (psi : E → ℝ) : Prop :=
  ContDiffOn ℝ k psi s ∧ ∃ C : ℝ, ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i psi x‖ ≤ C

private theorem BddDerivOn.of_le (h : BddDerivOn s k psi) (hl : l ≤ k) : BddDerivOn s l psi :=
  ⟨h.1.of_le (by exact_mod_cast hl), h.2.imp fun _ hC i hi => hC i (hi.trans hl)⟩

private theorem BddDerivOn.fderiv_apply (hs : IsOpen s) (h : BddDerivOn s (k + 1) psi) (v : E) :
    BddDerivOn s k (fun y => fderiv ℝ psi y v) := by
  obtain ⟨C, hC⟩ := h.2
  exact ⟨h.1.fderiv_apply_of_isOpen hs (by norm_cast) v, ‖v‖ * C, fun i hi x hx =>
    (h.1.norm_iteratedFDeriv_fderiv_apply_le hs v hi hx).trans
      (mul_le_mul_of_nonneg_left (hC (i + 1) (by omega) x hx) (norm_nonneg v))⟩

private theorem BddDerivOn.const_mul (hs : IsOpen s) (h : BddDerivOn s k psi) (c : ℝ) :
    BddDerivOn s k (fun x => c * psi x) := by
  obtain ⟨C, hC⟩ := h.2
  refine ⟨contDiffOn_const.mul h.1, ‖c‖ * C, fun i hi x hx => ?_⟩
  have hx' : ContDiffAt ℝ i psi x :=
    (h.1.of_le (by exact_mod_cast hi)).contDiffAt (hs.mem_nhds hx)
  rw [show (fun x => c * psi x) = fun x => c • psi x from rfl,
    iteratedFDeriv_const_smul_apply' hx', norm_smul]
  exact mul_le_mul_of_nonneg_left (hC i hi x hx) (norm_nonneg c)

private theorem BddDerivOn.sum {κ : Type*} [Fintype κ] (hs : IsOpen s) {f : κ → E → ℝ}
    (h : ∀ j, BddDerivOn s k (f j)) : BddDerivOn s k (fun x => ∑ j, f j x) := by
  choose C hC using fun j => (h j).2
  refine ⟨ContDiffOn.sum fun j _ => (h j).1, ∑ j, C j, fun i hi x hx => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply fun j _ =>
    ((h j).1.of_le (by exact_mod_cast hi)).contDiffAt (hs.mem_nhds hx)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hC j i hi x hx)

end BddDerivOn

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c : ℝ} {K : ℝ≥0} {ν : EuclideanSpace ℝ ι}

omit [DecidableEq ι] in
/-- Multiplication by a coefficient with bounded derivatives preserves `W^{k,2}(Ω)`. -/
private theorem BddDerivOn.exists_value_ae_eq_mul {k : ℕ} {psi : EuclideanSpace ℝ ι → ℝ}
    (h : BddDerivOn (Omega : Set (EuclideanSpace ℝ ι)) k psi) (u : Wkp mu Omega 2 k) :
    ∃ w : Wkp mu Omega 2 k, (Wkp.value k w : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * Wkp.value k u x :=
  h.2.elim fun _ hC => Wkp.exists_value_ae_eq_mul_of_norm_iteratedFDeriv_le h.1 hC u

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- **Splitting a direction along a unit vector `e` and its orthogonal hyperplane.** A weak
derivative `n` along `e` and a weak derivative `t` along the projection `P w` of `w` onto the
hyperplane orthogonal to `e` combine into the weak derivative `⟪e, w⟫ n + t` along `w`. -/
private theorem hasWeakLineDerivOn_normal_add_tangential {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1)
    {f n t : EuclideanSpace ℝ ι → ℝ} {w : EuclideanSpace ℝ ι}
    (hn : HasWeakLineDerivOn mu Omega f n e)
    (ht : HasWeakLineDerivOn mu Omega f t ((ℝ ∙ e)ᗮ.starProjection w)) :
    HasWeakLineDerivOn mu Omega f (fun x => ⟪e, w⟫_ℝ * n x + t x) w := by
  have h := (hn.smul_direction ⟪e, w⟫_ℝ).add_direction ht
  rwa [inner_smul_add_starProjection_eq ℝ he w] at h

omit [DecidableEq ι] in
/-- **Every derivative from the normal and the tangential ones.** If, in `W^{k,2}(Ω)`, a function
`f` has a weak derivative `N` along a unit vector `e` and a weak derivative `T τ` along every `τ`
orthogonal to `e`, then along every `w` it has the weak derivative `⟪e, w⟫ N + T (P w)`, where
`P` is the orthogonal projection onto the hyperplane orthogonal to `e`. -/
private theorem hasWeakLineDerivOn_smul_add {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1) {k : ℕ}
    {f : EuclideanSpace ℝ ι → ℝ} {N : Wkp mu Omega 2 k}
    (hN : HasWeakLineDerivOn mu Omega f (Wkp.value k N) e)
    {T : EuclideanSpace ℝ ι → Wkp mu Omega 2 k}
    (hT : ∀ τ, ⟪τ, e⟫_ℝ = 0 → HasWeakLineDerivOn mu Omega f (Wkp.value k (T τ)) τ)
    (w : EuclideanSpace ℝ ι) :
    HasWeakLineDerivOn mu Omega f
      (Wkp.value k (⟪e, w⟫_ℝ • N + T ((ℝ ∙ e)ᗮ.starProjection w))) w := by
  refine (hasWeakLineDerivOn_normal_add_tangential he hN
    (hT _ (inner_starProjection_orthogonal_singleton_eq_zero ℝ e w))).congr_ae_deriv ?_
  filter_upwards [Wkp.value_add_ae k (⟪e, w⟫_ℝ • N) (T ((ℝ ∙ e)ᗮ.starProjection w)),
    Wkp.value_smul_ae k ⟪e, w⟫_ℝ N] with x h₁ h₂
  rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, smul_eq_mul]

omit [DecidableEq ι] in
/-- **Second derivatives from the normal one and the tangential ones.** Let `e` be a unit vector,
`P` the orthogonal projection onto the hyperplane orthogonal to `e`, and `U ∈ W^{k+2,2}(Ω)` with
weak derivatives `T τ ∈ W^{k+2,2}(Ω)` along every `τ` orthogonal to `e`. Then the second weak
derivative `∂_w ∂_y U` is `⟪e, y⟫ (⟪e, w⟫ ∂_e ∂_e U + ∂_e T (P w)) + ∂_w T (P y)`. -/
private theorem value_lineDerivL_lineDerivL_ae_eq {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1)
    {k : ℕ} {U : Wkp mu Omega 2 (k + 2)} {T : EuclideanSpace ℝ ι → Wkp mu Omega 2 (k + 2)}
    (hT : ∀ τ, ⟪τ, e⟫_ℝ = 0 →
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 2) U) (Wkp.value (k + 2) (T τ)) τ)
    (w y : EuclideanSpace ℝ ι) :
    (Wkp.value k (Wkp.lineDerivL w k (Wkp.lineDerivL y (k + 1) U)) :
      EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] fun x =>
        ⟪e, y⟫_ℝ * (⟪e, w⟫_ℝ *
            Wkp.value k (Wkp.lineDerivL e k (Wkp.lineDerivL e (k + 1) U)) x +
          Wkp.value (k + 1) (Wkp.lineDerivL e (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection w))) x) +
        Wkp.value (k + 1) (Wkp.lineDerivL w (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection y))) x := by
  set P := (ℝ ∙ e)ᗮ.starProjection
  have hP : ∀ z, ⟪P z, e⟫_ℝ = 0 := inner_starProjection_orthogonal_singleton_eq_zero ℝ e
  have hDe := Wkp.hasWeakLineDerivOn_lineDerivL e (k + 1) U
  -- `∂_y U = ⟪e, y⟫ ∂_e U + T (P y)`.
  have h₁ := (Wkp.hasWeakLineDerivOn_lineDerivL y (k + 1) U).ae_eq
    (hasWeakLineDerivOn_normal_add_tangential he hDe (hT _ (hP y)))
  -- `∂_w ∂_e U = ⟪e, w⟫ ∂_e ∂_e U + ∂_e T (P w)`, since `∂_{P w} ∂_e U = ∂_e ∂_{P w} U`.
  have hDew := hasWeakLineDerivOn_normal_add_tangential he
    (Wkp.hasWeakLineDerivOn_lineDerivL e k (Wkp.lineDerivL e (k + 1) U))
    ((hT _ (hP w)).comm (Wkp.hasWeakLineDerivOn_lineDerivL e (k + 1) (T (P w))) hDe)
  have h₂ := ((hDew.const_smul ⟪e, y⟫_ℝ).add
    (Wkp.hasWeakLineDerivOn_lineDerivL w (k + 1) (T (P y)))).congr_ae h₁.symm
  exact (Wkp.hasWeakLineDerivOn_lineDerivL w k (Wkp.lineDerivL y (k + 1) U)).ae_eq h₂

omit [DecidableEq ι] in
/-- **The differentiated equation with forcing in `W^{k,2}(Ω)`.** Let the entries of `a` be of
class `C^{k+2}` on `Ω` with derivatives of order at most `k + 2` bounded on `Ω`, let the energy
integrand of `a` be essentially bounded on `Ω`, let `F ∈ W^{k+1,2}(Ω)`, and let `u ∈ H^{k+2}(Ω)`
solve `-∂ᵢ(aⁱʲ ∂ⱼu) = F` against `H¹₀(Ω)`. Then along every direction `e` the derivative
`∂_e u ∈ H¹(Ω)` solves `-∂ᵢ(aⁱʲ ∂ⱼ(∂_e u)) = G` against `H¹₀(Ω)` for some `G ∈ W^{k,2}(Ω)`.
No boundary condition on `u` is used. -/
private theorem exists_hasWeakLineDerivOn_and_energyFormH1_eq_setIntegral_of_bddDerivOn
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (k : ℕ)
    (ha : ∀ i j, BddDerivOn (Omega : Set (EuclideanSpace ℝ ι)) (k + 2) (fun x => a x i j))
    {F : Wkp mu Omega 2 (k + 1)} {u : W1p mu Omega 2}
    (hw : ∃ w : Wkp mu Omega 2 (k + 2), Wkp.value (k + 2) w = W1p.value u)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value (k + 1) F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (e : EuclideanSpace ℝ ι) :
    ∃ (d : W1p mu Omega 2) (G : Wkp mu Omega 2 k),
      HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) e ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 d (v : W1p mu Omega 2) =
        ∫ x in Omega, Wkp.value k G x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  obtain ⟨w, hw⟩ := hw
  set b := EuclideanSpace.basisFun ι ℝ
  have hΩo := Omega.isOpen
  have haΩ : ∀ i j, ContDiffOn ℝ 2 (fun x => a x i j) Omega := fun i j =>
    (ha i j).1.of_le (by norm_cast; omega)
  -- The first and second weak derivatives of `u`, from `u ∈ H^{k+2}(Ω)`.
  choose D hD using fun j => Wkp.exists_hasWeakLineDerivOn_value (k + 1) w (b j)
  choose E hE using fun i j => Wkp.exists_hasWeakLineDerivOn_value k (D j) (b i)
  obtain ⟨De, hDe⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) w e
  obtain ⟨Fe, hFe⟩ := Wkp.exists_hasWeakLineDerivOn_value k F e
  rw [hw] at hD hDe
  have hD' : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value u)
      (W1p.value (Wkp.firstOrder k (D j))) (b j) := fun j => by
    rw [Wkp.value_firstOrder]; exact hD j
  -- The commutator terms `∂ᵢ∂ₑaⁱʲ ∂ⱼu` and `∂ₑaⁱʲ ∂ᵢ∂ⱼu` lie in `W^{k,2}(Ω)`.
  choose M₁ hM₁ using fun i j => BddDerivOn.exists_value_ae_eq_mul (mu := mu)
    ((((ha i j).fderiv_apply hΩo e).fderiv_apply hΩo (b i))) (Wkp.lowerOrder k (D j))
  choose M₂ hM₂ using fun i j => BddDerivOn.exists_value_ae_eq_mul (mu := mu)
    (((ha i j).fderiv_apply hΩo e).of_le (by omega)) (E i j)
  have hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value (Wkp.firstOrder k De)) e := by
    rw [Wkp.value_firstOrder]; exact hDe
  refine ⟨Wkp.firstOrder k De, Fe + ∑ i, ∑ j, (M₁ i j + M₂ i j), hd, ?_⟩
  -- The differentiated equation, tested on test functions.
  have hut := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction (b := 0) (c := 0)
    hcoeff _ u).1 hu
  refine (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction (b := 0) (c := 0)
    hcoeff _ _).2 fun φ => ?_
  rw [energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn haΩ hut hd hD' hFe φ]
  refine integral_congr_ae ?_
  -- Identify the commutator terms with the values of `M₁` and `M₂`.
  have hu₁ : ∀ᵐ x ∂mu.restrict Omega, ∀ i j, Wkp.value k (M₁ i j) x =
      fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y e) x (b i) *
        ⟪W1p.gradient u x, b j⟫_ℝ := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    filter_upwards [hM₁ i j, (hD j).ae_eq ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (b j))]
      with x h₁ h₂
    rw [h₁, ← Wkp.value_succ, h₂, innerSL_apply_apply]
  have hu₂ : ∀ᵐ x ∂mu.restrict Omega, ∀ i j, Wkp.value k (M₂ i j) x =
      fderiv ℝ (fun y => a y i j) x e *
        ⟪W1p.gradient (Wkp.firstOrder k (D j)) x, b i⟫_ℝ := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have h := (W1p.hasWeakFDerivOn (Wkp.firstOrder k (D j))).hasWeakLineDerivOn (b i)
    rw [Wkp.value_firstOrder] at h
    filter_upwards [hM₂ i j, (hE i j).ae_eq h] with x h₁ h₂
    rw [h₁, h₂, innerSL_apply_apply]
  filter_upwards [Wkp.ae_value_add_sum_eq Fe Finset.univ Finset.univ M₁ M₂
    (hu₁.mono fun x h i _ j _ ↦ h i j) (hu₂.mono fun x h i _ j _ ↦ h i j)] with x hx
  rw [hx]

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
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) {m : ℕ}
    (hbd : ∀ i j, BddDerivOn (Omega : Set (EuclideanSpace ℝ ι)) (m + 2) (fun x => a x i j))
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
    hcoeff m hbd ⟨U, hU⟩ ((isWeakSolutionDirichlet_iff _ _).1 hu) τ
  obtain rfl : d = (t : W1p mu Omega 2) := W1p.ext_value (Lp.ext (hd.ae_eq ht))
  -- The induction hypothesis puts `∂_τ u` in `W^{m+2,2}(Ω)`.
  obtain ⟨T, hT⟩ := ih G t ((isWeakSolutionDirichlet_iff _ _).2 hG)
  exact ⟨T, by rw [hU, hT]; exact ht⟩

omit [DecidableEq ι] in
/-- The quadratic form `x ↦ ⟪e, a(x) e⟫` in the coordinates of the standard basis `(bᵢ)`:
`⟪e, a(x) e⟫ = ∑ᵢⱼ ⟪e, bᵢ⟫ ⟪e, bⱼ⟫ aⁱʲ(x)`. -/
private theorem matrixBilinearForm_self_eq_sum (A : Matrix ι ι ℝ) (e : EuclideanSpace ℝ ι) :
    matrixBilinearForm A e e = ∑ i, ∑ j, ⟪e, EuclideanSpace.basisFun ι ℝ i⟫_ℝ *
      ⟪e, EuclideanSpace.basisFun ι ℝ j⟫_ℝ * A i j := by
  simp only [matrixBilinearForm_apply, EuclideanSpace.inner_basisFun_real, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
/-- **Second derivatives through the weak gradient.** Under the hypotheses of
`value_lineDerivL_lineDerivL_ae_eq`, the component along `w` of the weak gradient of the first
derivative `∂_y U ∈ H¹(Ω)` is `⟪e, w⟫ ⟪e, y⟫ ∂_e ∂_e U + ⟪e, y⟫ ∂_e T (P w) + ∂_w T (P y)`. -/
private theorem ae_inner_gradient_firstOrder_lineDerivL_eq {e : EuclideanSpace ℝ ι}
    (he : ‖e‖ = 1) {k : ℕ} {U : Wkp mu Omega 2 (k + 2)}
    {T : EuclideanSpace ℝ ι → Wkp mu Omega 2 (k + 2)}
    (hT : ∀ τ, ⟪τ, e⟫_ℝ = 0 →
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 2) U) (Wkp.value (k + 2) (T τ)) τ)
    (w y : EuclideanSpace ℝ ι) :
    ∀ᵐ x ∂mu.restrict Omega,
      ⟪W1p.gradient (Wkp.firstOrder k (Wkp.lineDerivL y (k + 1) U)) x, w⟫_ℝ =
        ⟪e, w⟫_ℝ * ⟪e, y⟫_ℝ * Wkp.value k (Wkp.lineDerivL e k (Wkp.lineDerivL e (k + 1) U)) x +
          Wkp.value (k + 1) (⟪e, y⟫_ℝ • Wkp.lineDerivL e (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection w)) +
            Wkp.lineDerivL w (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection y))) x := by
  have h :=
    (W1p.hasWeakFDerivOn (Wkp.firstOrder k (Wkp.lineDerivL y (k + 1) U))).hasWeakLineDerivOn w
  rw [Wkp.value_firstOrder] at h
  filter_upwards [h.ae_eq (Wkp.hasWeakLineDerivOn_lineDerivL w k (Wkp.lineDerivL y (k + 1) U)),
    value_lineDerivL_lineDerivL_ae_eq he hT w y,
    Wkp.value_add_ae (k + 1)
      (⟪e, y⟫_ℝ • Wkp.lineDerivL e (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection w)))
      (Wkp.lineDerivL w (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection y))),
    Wkp.value_smul_ae (k + 1) ⟪e, y⟫_ℝ
      (Wkp.lineDerivL e (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection w)))] with x h₁ h₂ h₃ h₄
  rw [← innerSL_apply_apply, h₁, h₂, h₃, Pi.add_apply, h₄, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The purely normal second derivative from the equation.** Let `e` be a unit vector, let `a`
be uniformly elliptic on `Ω` with entries of class `C^{m+2}` with bounded derivatives, and let
`u ∈ H¹₀(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = F` with `F ∈ W^{m+1,2}(Ω)`. Suppose that `u` is the value of
`U ∈ W^{m+2,2}(Ω)` whose derivatives `T τ` along the directions `τ` orthogonal to `e` lie in
`W^{m+2,2}(Ω)`. Then `∂_e ∂_e u` lies in `W^{m+1,2}(Ω)`: in the equation, solved for
`⟪e, a e⟫ ∂_e ∂_e u`, every other term lies in `W^{m+1,2}(Ω)`, and `⟪e, a e⟫ ≥ λ`. -/
private theorem exists_hasWeakLineDerivOn_normal {e : EuclideanSpace ℝ ι} (he : ‖e‖ = 1)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) {m : ℕ}
    (hbd : ∀ i j, BddDerivOn (Omega : Set (EuclideanSpace ℝ ι)) (m + 2) (fun x => a x i j))
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
    (fun i j => (hbd i j).1.of_le (by norm_cast; omega))
    (Wkp.locallyIntegrableOn_value (m + 1) F) hu.energyFormH1_ofTestFunctionₗ hD
  rw [← hb] at heq
  -- The first derivatives; the second derivatives split along `e` and the hyperplane, by
  -- `ae_inner_gradient_firstOrder_lineDerivL_eq`, into `∂_e ∂_e u` and the terms `R`.
  have hg₁ : ∀ᵐ x ∂mu.restrict Omega, ∀ j, ⟪W1p.gradient (u : W1p mu Omega 2) x, b j⟫_ℝ =
      Wkp.value (m + 1) (D j) x := Filter.eventually_all.2 fun j => by
    filter_upwards [((W1p.hasWeakFDerivOn (u : W1p mu Omega 2)).hasWeakLineDerivOn (b j)).ae_eq
      (by simpa only [Wkp.value_firstOrder] using hD j)] with x hx
    rw [← hx, innerSL_apply_apply]
  set R : ι → ι → Wkp mu Omega 2 (m + 1) := fun i j =>
    ⟪e, b j⟫_ℝ • Wkp.lineDerivL e (m + 1) (T (P (b i))) + Wkp.lineDerivL (b i) (m + 1) (T (P (b j)))
  -- The other terms of the equation lie in `W^{m+1,2}(Ω)`.
  choose Y₁ hY₁ using fun i j => BddDerivOn.exists_value_ae_eq_mul (mu := mu)
    ((hbd i j).fderiv_apply Omega.isOpen (b i)) (D j)
  choose Y₂ hY₂ using fun i j => BddDerivOn.exists_value_ae_eq_mul (mu := mu)
    ((hbd i j).of_le (by omega)) (R i j)
  -- The coefficient `ρ = ⟪e, a e⟫` of `∂_e ∂_e u` is bounded below by `λ`.
  set rho : EuclideanSpace ℝ ι → ℝ := fun x => ∑ i, ∑ j, ⟪e, b i⟫_ℝ * ⟪e, b j⟫_ℝ * a x i j
  have hrho : BddDerivOn (Omega : Set (EuclideanSpace ℝ ι)) (m + 1) rho :=
    BddDerivOn.sum Omega.isOpen fun i => BddDerivOn.sum Omega.isOpen fun j =>
      ((hbd i j).of_le (by omega)).const_mul Omega.isOpen _
  have hrl : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), lam ≤ rho x := fun x hx => by
    simpa only [he, one_pow, mul_one, ← matrixBilinearForm_self, matrixBilinearForm_self_eq_sum]
      using ha.lower_bound hx e
  obtain ⟨C, hC⟩ := hrho.2
  -- `ρ ∂_e ∂_e u = -F - ∑ᵢⱼ (∂ᵢaⁱʲ ∂ⱼu + aⁱʲ Rᵢⱼ)` lies in `W^{m+1,2}(Ω)`; divide by `ρ`.
  obtain ⟨N, hN⟩ := Wkp.exists_value_eq_of_value_ae_eq_mul hrho.1 ha.pos hC hrl (Wkp.value m Dee)
    (-F + ∑ i, ∑ j, (-Y₁ i j + -Y₂ i j)) (by
      filter_upwards [Wkp.ae_value_add_sum_eq (-F) Finset.univ Finset.univ (fun i j => -Y₁ i j)
          (fun i j => -Y₂ i j) (c₁ := fun i j x => -(fderiv ℝ (fun y => a y i j) x (b i) *
            Wkp.value (m + 1) (D j) x))
          (c₂ := fun i j x => -(a x i j * Wkp.value (m + 1) (R i j) x))
          ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => by
            filter_upwards [Wkp.value_neg_ae (m + 1) (Y₁ i j), hY₁ i j] with x h₁ h₂
            rw [h₁, Pi.neg_apply, h₂]).mono fun x h i _ j _ => h i j)
          ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => by
            filter_upwards [Wkp.value_neg_ae (m + 1) (Y₂ i j), hY₂ i j] with x h₁ h₂
            rw [h₁, Pi.neg_apply, h₂]).mono fun x h i _ j _ => h i j),
        Wkp.value_neg_ae (m + 1) F, heq, hg₁, Filter.eventually_all.2 fun i =>
          Filter.eventually_all.2 fun j =>
            ae_inner_gradient_firstOrder_lineDerivL_eq he hT (b i) (b j)]
        with x hx hF hx₀ hx₁ hx₂
      rw [hx, hF, Pi.neg_apply, ← hx₀]
      simp only [hx₁, D, R, hx₂, rho, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  exact ⟨N, by rw [hN]; exact Wkp.hasWeakLineDerivOn_lineDerivL _ _ _⟩

/-- **The induction on the order.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`, with the energy integrand of `a`
essentially bounded on `Ω`: if the entries of `a` are of class `C^{m+1}` on `Ω` with bounded
derivatives, then every solution `u ∈ H¹₀(Ω)` of the Dirichlet problem with forcing in
`W^{m,2}(Ω)` lies in `W^{m+2,2}(Ω)`. -/
private theorem exists_value_eq_value_of_mapsTo_of_bddDerivOn (hν : ν ≠ 0)
    (hΩc : Convex ℝ (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩ : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) :
    ∀ m : ℕ, (∀ i j, BddDerivOn (Omega : Set (EuclideanSpace ℝ ι)) (m + 1) (fun x => a x i j)) →
      ∀ (F : Wkp mu Omega 2 m) (u : W1p0 mu Omega 2),
        IsWeakSolutionDirichlet a 0 0 (Wkp.value m F) u →
          ∃ W : Wkp mu Omega 2 (m + 2), Wkp.value (m + 2) W = W1p.value (u : W1p mu Omega 2)
  | 0, _, F, u, hu => by
    obtain ⟨U, hU⟩ := ha.exists_lowerOrder_eq_of_mapsTo hν hΩ hK hu
    refine ⟨U, ?_⟩
    rw [Wkp.value_succ, hU]
    exact Wkp.value_one (u : W1p mu Omega 2)
  | m + 1, hbd, F, u, hu => by
    have ih := exists_value_eq_value_of_mapsTo_of_bddDerivOn hν hΩc hΩ ha hK hcoeff m
      fun i j => (hbd i j).of_le (by omega)
    obtain ⟨U, hU⟩ := ih (Wkp.lowerOrder m F) u (by rwa [← Wkp.value_succ])
    set b := EuclideanSpace.basisFun ι ℝ
    set e : EuclideanSpace ℝ ι := ‖ν‖⁻¹ • ν
    have he : ‖e‖ = 1 := norm_smul_inv_norm hν
    set P := (ℝ ∙ e)ᗮ.starProjection
    -- The derivatives along the directions orthogonal to `e`, hence to `ν`.
    have htan : ∀ τ, ∃ T : Wkp mu Omega 2 (m + 2), ⟪τ, e⟫_ℝ = 0 →
        HasWeakLineDerivOn mu Omega (Wkp.value (m + 2) U) (Wkp.value (m + 2) T) τ := fun τ => by
      by_cases hτ : ⟪τ, e⟫_ℝ = 0
      · have hτν : ⟪τ, ν⟫_ℝ = 0 := by
          rw [real_inner_smul_right] at hτ
          exact (mul_eq_zero.1 hτ).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hν))
        obtain ⟨T, hT⟩ := exists_hasWeakLineDerivOn_tangential hν hΩc hΩ ha hK hcoeff hbd
          (ih := ih) hu hU hτν
        exact ⟨T, fun _ => hT⟩
      · exact ⟨0, fun h => absurd h hτ⟩
    choose T hT using htan
    -- The purely normal second derivative, and then `∂_e u ∈ W^{m+2,2}(Ω)`.
    obtain ⟨N, hN⟩ := exists_hasWeakLineDerivOn_normal he ha hbd hu hU hT
    have hDe := Wkp.hasWeakLineDerivOn_lineDerivL e (m + 1) U
    obtain ⟨Ne, hNe⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b
      (Wkp.value (m + 1) (Wkp.lineDerivL e (m + 1) U)) (m + 1) fun i =>
        ⟨_, hasWeakLineDerivOn_smul_add he hN
          (T := fun τ => Wkp.lineDerivL e (m + 1) (T τ))
          (fun τ hτ => (hT τ hτ).comm (Wkp.hasWeakLineDerivOn_lineDerivL e (m + 1) (T τ)) hDe)
          (b i)⟩
    -- Every first derivative of `u` lies in `W^{m+2,2}(Ω)`.
    obtain ⟨W, hW⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b
      (Wkp.value (m + 2) U) (m + 2) fun i =>
        ⟨_, hasWeakLineDerivOn_smul_add he (N := Ne) (by rw [hNe]; exact hDe) hT (b i)⟩
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
  set b := EuclideanSpace.basisFun ι ℝ
  -- The entries of `a` are bounded by `Λ` and `K`-Lipschitz on `Ω`, so their derivatives of every
  -- order at most `m + 1` are bounded on `Ω`.
  have hbd : ∀ i j, BddDerivOn (Omega : Set (EuclideanSpace ℝ ι)) (m + 1)
      (fun x => a x i j) := fun i j => by
    have hentry : LipschitzOnWith K (fun x => a x i j) Omega := by
      simpa [b, matrixBilinearForm_apply, b.orthonormal.1 i, b.orthonormal.1 j] using
        lipschitzOnWith_matrixBilinearForm_apply_apply hK (b i) (b j)
    refine ⟨hsmooth i j, max (max Lam K) C, fun k hk x hx => ?_⟩
    rcases k with _ | _ | k
    · rw [norm_iteratedFDeriv_zero]
      refine le_trans ?_ ((le_max_left _ _).trans (le_max_left _ _))
      simpa [b, b.orthonormal.1 i, b.orthonormal.1 j, Real.norm_eq_abs] using
        ha.upper_bound hx (b i) (b j)
    · rw [norm_iteratedFDeriv_one]
      exact (norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hx) hentry).trans
        ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hC i j (k + 2) (by omega) hk x hx).trans (le_max_right _ _)
  -- The energy integrand of `a` is essentially bounded on `Ω`.
  have hcoeff := memLp_energyIntegrand_of_bounds (mu := mu) (Omega := Omega) (b := 0) (c := 0)
    (beta := 0) (gamma := 0) ha.upper_nonneg
    (ContinuousOn.aestronglyMeasurable (β := ι → ι → ℝ) (continuousOn_pi.2 fun i =>
      continuousOn_pi.2 fun j => (hsmooth i j).continuousOn) Omega.isOpen.measurableSet)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx => ha.upper_bound hx) (fun _ _ => by simp) (fun _ _ => by simp)
  exact exists_value_eq_value_of_mapsTo_of_bddDerivOn hν hΩc hΩ ha hK hcoeff m hbd F u hu

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

end PDE

end TauCeti
