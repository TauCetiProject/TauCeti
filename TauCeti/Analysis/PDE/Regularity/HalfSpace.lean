/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# `H²` regularity up to the boundary of a half-space

Let `Ω = {x | c < ⟪x, ν⟫}` be an open half-space in `ℝⁿ`, let `A` be a constant matrix with
`λ ‖ξ‖² ≤ ξ ⬝ᵥ A ξ` for some `λ > 0`, and let `u ∈ H¹₀(Ω)` be the weak solution of the Dirichlet
problem

`-∂ⱼ(Aⁱʲ ∂ᵢu) = f` in `Ω`, `u = 0` on `∂Ω`, with `f ∈ L²(Ω)`.

This file proves that `u ∈ H²(Ω)`: every second weak derivative of `u` exists and lies in
`L²(Ω)`, globally on `Ω` and not only on compactly contained subsets. This is the flat model of
global `H²` regularity: after the boundary of a `C²` domain is flattened, the equation in each
chart is posed on a half-space.

## The argument

The proof is the classical one (Evans, §6.3.2, Theorem 4).

* **Tangential directions.** Translations parallel to `∂Ω` map `Ω` onto itself, so the
  difference quotients of `u` in such a direction stay in `H¹₀(Ω)` and are admissible test
  functions. The difference-quotient argument then bounds `∂_τ ∇u` in `L²(Ω)` for every tangential
  `τ`
  (`UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith_of_mapsTo`).
  Since weak derivatives commute, this gives every second derivative except `∂_ν ∂_ν u`.
* **The normal direction.** Against a test function `φ`, the equation reads
  `∑ⱼ ∫ (∂_{cⱼ} φ) ∂ⱼu = ∫ f φ`, where `cⱼ` is the `j`-th column of `A`. Splitting
  `cⱼ = sⱼ ν + τⱼ` with `τⱼ` tangential and moving the tangential derivatives across shows that
  `∂_m u`, for `m = ∑ⱼ sⱼ eⱼ`, has the weak derivative `-(f + ∑ⱼ ∂_{τⱼ} ∂ⱼu)` in the direction `ν`.
  Ellipticity gives `⟪m, ν⟫ ‖ν‖² = ν ⬝ᵥ A ν > 0`, so `ν` is a combination of `m` and a
  tangential vector, and `∂_ν ∂_ν u` exists.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_halfSpace`: every first
  derivative of the solution has an `L²(Ω)` weak derivative in every direction.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace`: the solution lies in
  `W^{2,2}(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorem 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.12.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped Distributions InnerProductSpace Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ} {lam c : ℝ}
  {ν : EuclideanSpace ℝ ι}

/-- **The equation gives the normal derivative.** Let `u ∈ H¹(Ω)` satisfy `a(u, φ) = ∫_Ω f φ`
for every test function `φ`, where `a` is the energy form of the constant matrix `A`. Split the
`j`-th column `cⱼ` of `A` as `sⱼ ν + τⱼ`, with `sⱼ = ⟪cⱼ, ν⟫ / ‖ν‖²` and `τⱼ ⊥ ν`. If each
`∂ⱼu` has a weak derivative `Gⱼ` in the direction `τⱼ`, then `∂_m u`, for `m = ∑ⱼ sⱼ eⱼ`, has the
weak derivative `-(f + ∑ⱼ Gⱼ)` in the direction `ν`. -/
private theorem hasWeakLineDerivOn_inner_gradient_sum_smul_basisFun
    {f : Lp ℝ 2 (mu.restrict Omega)} {U : W1p mu Omega 2}
    (hU : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun _ => A) 0 0 U (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu)
    {G : ι → Lp ℝ 2 (mu.restrict Omega)}
    (hG : ∀ j, HasWeakLineDerivOn mu Omega
      (fun x => ⟪W1p.gradient U x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ) (G j)
      (WithLp.toLp 2 (Aᵀ j) - (⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ / ‖ν‖ ^ 2) • ν)) :
    HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x,
        ∑ j, (⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ / ‖ν‖ ^ 2) • EuclideanSpace.basisFun ι ℝ j⟫_ℝ)
      (fun x => -(f x + ∑ j, G j x)) ν := by
  set b := EuclideanSpace.basisFun ι ℝ
  set s : ι → ℝ := fun j => ⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ / ‖ν‖ ^ 2
  have hloc : ∀ z, LocallyIntegrableOn (fun x => ⟪W1p.gradient U x, z⟫_ℝ) Omega mu := fun z => by
    simpa only [innerSL_apply_apply] using
      ((W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z).locallyIntegrableOn_deriv
  have hfloc : LocallyIntegrableOn (f : EuclideanSpace ℝ ι → ℝ) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable (by norm_num))
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hloc _,
    locallyIntegrableOn_of_locallyIntegrable_restrict (((Lp.memLp f).add (memLp_finsetSum
      Finset.univ fun j _ => Lp.memLp (G j))).neg.locallyIntegrable (by norm_num)), fun φ => ?_⟩
  have hφ : Differentiable ℝ (φ : EuclideanSpace ℝ ι → ℝ) := φ.contDiff.differentiable (by simp)
  have hIν : ∀ j, Integrable (fun x => lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
      ⟪W1p.gradient U x, b j⟫_ℝ) mu :=
    fun j => integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc (b j)) φ ν
  have hIG : ∀ j, Integrable (fun x => (φ : EuclideanSpace ℝ ι → ℝ) x • G j x) mu :=
    fun j => integrable_smul_of_locallyIntegrableOn (hG j).locallyIntegrableOn_deriv φ
  -- The weak equation against `φ`, written column by column.
  have heq := hU φ
  rw [energyFormH1_ofTestFunctionₗ_eq_sum] at heq
  simp only [innerSL_apply_apply] at heq
  -- Each column splits into its normal and tangential parts.
  have hsplit : ∀ j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (WithLp.toLp 2 (Aᵀ j)) •
      ⟪W1p.gradient U x, b j⟫_ℝ ∂mu =
        s j * ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν • ⟪W1p.gradient U x, b j⟫_ℝ ∂mu -
          ∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • G j x ∂mu := by
    intro j
    have hline : ∀ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (WithLp.toLp 2 (Aᵀ j)) =
        s j * lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν +
          lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (WithLp.toLp 2 (Aᵀ j) - s j • ν) := by
      intro x
      simp only [(hφ x).lineDeriv_eq_fderiv, map_sub, map_smul, smul_eq_mul]
      ring
    rw [sub_eq_add_neg, ← (hG j).integral_lineDeriv_smul_eq_neg_integral_smul φ,
      ← integral_const_mul, ← integral_add ((hIν j).const_mul _)
        (integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc (b j)) φ _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hline x, smul_eq_mul]
    ring
  -- The left side is `∑ⱼ sⱼ ∫ (∂_ν φ) ∂ⱼu`.
  have hL : ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
      ⟪W1p.gradient U x, ∑ j, s j • b j⟫_ℝ ∂mu =
        ∑ j, s j * ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
          ⟪W1p.gradient U x, b j⟫_ℝ ∂mu := by
    have hpt : ∀ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν •
        ⟪W1p.gradient U x, ∑ j, s j • b j⟫_ℝ = ∑ j, s j *
          (lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x ν • ⟪W1p.gradient U x, b j⟫_ℝ) := fun x => by
      simp only [inner_sum, real_inner_smul_right, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ => (hIν j).const_mul _]
    simp_rw [integral_const_mul]
  -- The right side is `∫ f φ + ∑ⱼ ∫ φ Gⱼ`.
  have hR : -∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • -(f x + ∑ j, G j x) ∂mu =
      (∫ x in Omega, f x * φ x ∂mu) + ∑ j, ∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • G j x ∂mu := by
    simp only [smul_neg, integral_neg, neg_neg, smul_add, Finset.smul_sum]
    rw [integral_add (integrable_smul_of_locallyIntegrableOn hfloc φ)
      (integrable_finsetSum _ fun j _ => hIG j), integral_finsetSum _ fun j _ => hIG j,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [φ.zero_on_compl hx]]
    simp only [smul_eq_mul, mul_comm]
  rw [hL, hR, ← heq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [hsplit j]; ring

/-- The vector `m = ∑ⱼ sⱼ eⱼ` of `hasWeakLineDerivOn_inner_gradient_sum_smul_basisFun` satisfies
`⟪m, ν⟫ ‖ν‖² = ν ⬝ᵥ A ν`. -/
private theorem inner_sum_smul_basisFun_mul_norm_sq (hν : ν ≠ 0) :
    ⟪∑ j, (⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ / ‖ν‖ ^ 2) • EuclideanSpace.basisFun ι ℝ j, ν⟫_ℝ *
      ‖ν‖ ^ 2 = ν.ofLp ⬝ᵥ A *ᵥ ν.ofLp := by
  have hN : ‖ν‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hν)
  have hcol : ∀ j, ⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ = ∑ i, A i j * ν.ofLp i := fun j => by
    simp [PiLp.inner_apply, mul_comm]
  have hs : ∀ j, ⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ / ‖ν‖ ^ 2 * ν.ofLp j * ‖ν‖ ^ 2 =
      (∑ i, A i j * ν.ofLp i) * ν.ofLp j := fun j => by
    rw [hcol]
    field_simp
  simp only [sum_inner, real_inner_smul_left, EuclideanSpace.basisFun_inner, Finset.sum_mul, hs]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Second derivatives up to the boundary of a half-space.** Let `Ω = {x | c < ⟪x, ν⟫}` with
`ν ≠ 0`, let `A` be a constant matrix with `λ ‖ξ‖² ≤ ξ ⬝ᵥ A ξ` for some `λ > 0`, and let
`u ∈ H¹₀(Ω)` be a weak solution of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f` with `f ∈ L²(Ω)`. Then for all `y` and `w`
the derivative `∂_y u = ⟪∇u, y⟫` has a weak derivative in the direction `w` that lies in
`L²(Ω)`. -/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_gradient_of_halfSpace (hν : ν ≠ 0)
    (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ) (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (A *ᵥ ξ))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u) (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ) G w := by
  classical
  set U : W1p mu Omega 2 := (u : W1p mu Omega 2)
  set b := EuclideanSpace.basisFun ι ℝ
  have hN : 0 < ‖ν‖ ^ 2 := pow_pos (norm_pos_iff.2 hν) 2
  -- `D y w`: the derivative `∂_y u` has a weak derivative in the direction `w` in `L²(Ω)`.
  let D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → Prop := fun y w =>
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G w
  -- `D` is linear in each argument.
  have hadd_dir : ∀ {y w₁ w₂}, D y w₁ → D y w₂ → D y (w₁ + w₂) := by
    rintro y w₁ w₂ ⟨G₁, h₁⟩ ⟨G₂, h₂⟩
    exact ⟨G₁ + G₂, (h₁.add_direction h₂).congr_ae_deriv (Lp.coeFn_add G₁ G₂).symm⟩
  have hsmul_dir : ∀ {y w} (r : ℝ), D y w → D y (r • w) := by
    rintro y w r ⟨G, h⟩
    exact ⟨r • G, (h.smul_direction r).congr_ae_deriv (Lp.coeFn_smul r G).symm⟩
  have hadd : ∀ {y₁ y₂ w}, D y₁ w → D y₂ w → D (y₁ + y₂) w := by
    rintro y₁ y₂ w ⟨G₁, h₁⟩ ⟨G₂, h₂⟩
    refine ⟨G₁ + G₂, ((h₁.add h₂).congr_ae (Filter.Eventually.of_forall fun x => ?_))
      |>.congr_ae_deriv (Lp.coeFn_add G₁ G₂).symm⟩
    simp [inner_add_right]
  have hsmul : ∀ {y w} (r : ℝ), D y w → D (r • y) w := by
    rintro y w r ⟨G, h⟩
    refine ⟨r • G, ((h.const_smul r).congr_ae (Filter.Eventually.of_forall fun x => ?_))
      |>.congr_ae_deriv (Lp.coeFn_smul r G).symm⟩
    simp [real_inner_smul_right]
  -- The first derivatives of `u`, and the symmetry of `D` that comes from commuting them.
  have hfd : ∀ z, HasWeakLineDerivOn mu Omega (W1p.value U)
      (fun x => ⟪W1p.gradient U x, z⟫_ℝ) z := fun z => by
    simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z
  have hsymm : ∀ {y w}, D y w → D w y := by
    rintro y w ⟨G, hG⟩
    exact ⟨G, (hfd y).comm hG (hfd w)⟩
  -- Tangential directions: the difference-quotient estimate.
  have hP : ∀ z, ⟪z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν, ν⟫_ℝ = 0 := fun z => by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ hN.ne', sub_self]
  have htan : ∀ y {τ}, ⟪τ, ν⟫_ℝ = 0 → D y τ := by
    intro y τ hτ
    have hw : ∀ t : ℝ, MapsTo (· + t • τ) Omega Omega := fun t x hx => by
      have hx' := (hΩ x).1 hx
      exact (hΩ _).2 (by simpa [inner_add_left, real_inner_smul_left, hτ] using hx')
    obtain ⟨G, -, hG⟩ := (uniformlyEllipticOn_const (Omega : Set (EuclideanSpace ℝ ι)) hlam hA)
      |>.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith_of_mapsTo (K := 0) hw
        (Bornology.isBounded_singleton.subset Set.range_const_subset) (LipschitzWith.const _) hu y
    exact ⟨G, hG⟩
  -- The normal direction, from the equation.
  let s : ι → ℝ := fun j => ⟪WithLp.toLp 2 (Aᵀ j), ν⟫_ℝ / ‖ν‖ ^ 2
  set m : EuclideanSpace ℝ ι := ∑ j, s j • b j
  choose G hG using fun j => htan (b j) (hP (WithLp.toLp 2 (Aᵀ j)))
  have hm : D m ν := by
    have hFm : MemLp (fun x => -(f x + ∑ j, G j x)) 2 (mu.restrict Omega) :=
      ((Lp.memLp f).add (memLp_finsetSum Finset.univ fun j _ => Lp.memLp (G j))).neg
    exact ⟨hFm.toLp _, (hasWeakLineDerivOn_inner_gradient_sum_smul_basisFun
      ((forall_energyFormH1_eq_setIntegral_iff_forall_testFunction (b := 0) (c := 0)
        (memLp_top_const (energyIntegrand A 0 0)) f U).1 ((isWeakSolutionDirichlet_iff f u).1 hu))
      hG).congr_ae_deriv hFm.coeFn_toLp.symm⟩
  -- Ellipticity makes `m` transversal to the boundary: `⟪m, ν⟫ ‖ν‖² = ν ⬝ᵥ A ν ≥ λ ‖ν‖²`.
  have hmpos : 0 < ⟪m, ν⟫_ℝ := by
    have h := hA ν
    rw [← inner_sum_smul_basisFun_mul_norm_sq hν] at h
    exact hlam.trans_le (le_of_mul_le_mul_right h hN)
  -- Hence `ν` is a combination of `m` and a tangential vector, and `∂_ν ∂_ν u` exists.
  have hνν : D ν ν := by
    have h := hsmul (‖ν‖ ^ 2 / ⟪m, ν⟫_ℝ) (hadd hm (hsmul (-1) (hsymm (htan ν (hP m)))))
    have hvec : (‖ν‖ ^ 2 / ⟪m, ν⟫_ℝ) • (m + (-1 : ℝ) • (m - (⟪m, ν⟫_ℝ / ‖ν‖ ^ 2) • ν)) = ν := by
      rw [show m + (-1 : ℝ) • (m - (⟪m, ν⟫_ℝ / ‖ν‖ ^ 2) • ν) = (⟪m, ν⟫_ℝ / ‖ν‖ ^ 2) • ν by module,
        smul_smul, div_mul_div_cancel₀ hmpos.ne', div_self hN.ne', one_smul]
    rwa [hvec] at h
  -- Every first derivative has a normal derivative, and then a derivative in every direction.
  have hyν : ∀ y, D y ν := fun y => by
    have h := hadd (hsmul (⟪y, ν⟫_ℝ / ‖ν‖ ^ 2) hνν) (hsymm (htan ν (hP y)))
    rwa [add_sub_cancel] at h
  have h : D y w := by
    have h := hadd_dir (hsmul_dir (⟪w, ν⟫_ℝ / ‖ν‖ ^ 2) (hyν y)) (htan y (hP w))
    rwa [add_sub_cancel] at h
  exact h

/-- **`H²` regularity up to the boundary of a half-space.** Let `Ω = {x | c < ⟪x, ν⟫}` with
`ν ≠ 0`, let `A` be a constant matrix with `λ ‖ξ‖² ≤ ξ ⬝ᵥ A ξ` for some `λ > 0`, and let
`u ∈ H¹₀(Ω)` be a weak solution of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f` with `f ∈ L²(Ω)`, that is, of the Dirichlet
problem with zero boundary values. Then `u` is the first-order part of an element of
`W^{2,2}(Ω)`: its second weak derivatives lie in `L²(Ω)` up to the boundary. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_of_halfSpace (hν : ν ≠ 0)
    (hΩ : ∀ x, x ∈ Omega ↔ c < ⟪x, ν⟫_ℝ) (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (A *ᵥ ξ))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u) :
    ∃ U : Wkp mu Omega 2 2, Wkp.lowerOrder 1 U = (u : W1p mu Omega 2) :=
  W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun _ _ => exists_hasWeakLineDerivOn_gradient_of_halfSpace hν hΩ hlam hA hu _ _

end PDE

end TauCeti
