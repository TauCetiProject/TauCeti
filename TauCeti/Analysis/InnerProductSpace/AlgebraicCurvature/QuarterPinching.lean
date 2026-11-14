/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Isotropic
public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.LinearAlgebra.Multilinear.SectionalPolarization

/-!
# Berger's mixed-component estimate, strict quarter pinching, and Fubini–Study sharpness

Sectional curvature bounds on an algebraic curvature tensor `r : FourTensor V` control its mixed
orthonormal-frame component `r(f₀, f₁, f₂, f₃)` via Berger's polarization inequality: rewriting
`24 r(f₀, f₁, f₂, f₃)` through `LinearMap.twentyFour_mul_apply_eq_of_cyclic_eq_zero` as a signed
combination of eight sectional numerators on orthonormal pairs `(fᵢ ± fⱼ) / √2` yields
`|r(f₀, f₁, f₂, f₃)| ≤ (2 / 3) (b - a)` whenever sectional curvatures in `span(f)` lie in `[a, b]`.
Substituting this bound into `pic2Expression r f l m` gives
`min a ((4 a - b) / 3) * (1 + l²) * (1 + m²) ≤ pic2Expression r f l m`, so weak quarter pinching
(`0 ≤ a`, `b ≤ 4 a`) implies `IsPIC2FourFrame r`, while strict quarter pinching (`0 < a`,
`b < 4 a`) gives strict positivity of `pic2Expression` and places `r` in the interior of the PIC2
cone inside `algebraicCurvatureSubmodule V`.

Both Berger's constant `2 / 3` and the strict inequality `b < 4 a` are sharp: for an orthogonal
almost complex structure `J`, the Fubini–Study four-tensor `fubiniStudy J` has sectional curvatures
in `[1, 4]`, satisfies `fubiniStudy J ![X, J X, Y, J Y] = 2` on every unitary orthonormal
four-frame, lies in `IsPIC2FourFrame`, and vanishes on `pic2Expression` at `l = m = 1`, so it lies
on the boundary rather than the interior of the PIC2 cone.

## Main definitions

* `TauCeti.FourTensor.sectionalMin`, `TauCeti.FourTensor.sectionalMax`: extremal sectional
  curvatures over orthonormal two-frames.
* `TauCeti.FourTensor.fubiniStudy`: algebraic curvature tensor of constant holomorphic sectional
  curvature `4` attached to an almost complex structure `J`.

## Main statements

* `TauCeti.FourTensor.lipschitzWith_sectionalMin`, `TauCeti.FourTensor.lipschitzWith_sectionalMax`,
  `TauCeti.FourTensor.exists_orthonormal_eq_sectionalMin`,
  `TauCeti.FourTensor.exists_orthonormal_eq_sectionalMax`,
  `TauCeti.FourTensor.IsPIC2FourFrame.apply_self_nonneg`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.abs_apply_orthonormal_le`: Berger's `2 / 3` estimate.
* `TauCeti.FourTensor.strict_quarterPinching_isPIC2` and
  `TauCeti.FourTensor.mem_interior_isPIC2FourFrame_of_quarterPinched`.
* `TauCeti.FourTensor.fubiniStudy_apply_unitary`, `TauCeti.FourTensor.isPIC2FourFrame_fubiniStudy`,
  `TauCeti.FourTensor.not_mem_interior_isPIC2FourFrame_fubiniStudy`, and
  `TauCeti.FourTensor.exists_isPIC2FourFrame_not_mem_interior_fin_four`.

## References

* M. Berger, *Sur quelques variétés riemanniennes suffisamment pincées*, Bull. Soc. Math. France
  88 (1960), 57–71.
* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Interscience (1969),
  Chapter IX, Proposition 7.1.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Sections 1.G and 2.F.
-/

public section

open Set
open scoped InnerProductSpace NNReal Pointwise

noncomputable section

namespace TauCeti.FourTensor

/-! ### Extremal sectional curvatures on `FourTensor V` -/

section InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Minimum of `r ![u, v, u, v]` over all orthonormal two-frames `(u, v)` in `V` (equal to `0` when
`dim V < 2`). -/
def sectionalMin (r : FourTensor V) : ℝ :=
  sInf ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u})

/-- Maximum of `r ![u, v, u, v]` over all orthonormal two-frames `(u, v)` in `V` (equal to `0` when
`dim V < 2`). -/
def sectionalMax (r : FourTensor V) : ℝ :=
  sSup ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u})

/-- Defining formula for `sectionalMin`. -/
theorem sectionalMin_def (r : FourTensor V) : sectionalMin r =
    sInf ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u}) :=
  (rfl)

/-- Defining formula for `sectionalMax`. -/
theorem sectionalMax_def (r : FourTensor V) : sectionalMax r =
    sSup ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u}) :=
  (rfl)

/-- Negation duality between `sectionalMin` and `sectionalMax`. -/
@[simp]
theorem sectionalMin_neg (r : FourTensor V) : sectionalMin (-r) = -sectionalMax r := by
  rw [sectionalMin_def, sectionalMax_def, ← Real.sInf_neg]
  congr 1; ext y; simp [neg_eq_iff_eq_neg]

/-- `sectionalMax` of `-r` is `-sectionalMin r`. -/
@[simp]
theorem sectionalMax_neg (r : FourTensor V) : sectionalMax (-r) = -sectionalMin r := by
  simpa using (neg_inj.2 (sectionalMin_neg (-r))).symm

private theorem abs_apply_orthonormal_two_le_norm (r : FourTensor V) {u : Fin 2 → V}
    (hu : Orthonormal ℝ u) : |r ![u 0, u 1, u 0, u 1]| ≤ ‖r‖ := by
  have h := r.le_opNorm ![u 0, u 1, u 0, u 1]
  rw [Real.norm_eq_abs, Fin.prod_univ_four] at h
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    hu.1 0, hu.1 1, mul_one] using h

private theorem bddBelow_sectionalImage (r : FourTensor V) :
    BddBelow ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) ''
      {u : Fin 2 → V | Orthonormal ℝ u}) :=
  ⟨-‖r‖, by rintro _ ⟨u, hu, rfl⟩; exact neg_le_of_abs_le (abs_apply_orthonormal_two_le_norm r hu)⟩

private theorem bddAbove_sectionalImage (r : FourTensor V) :
    BddAbove ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) ''
      {u : Fin 2 → V | Orthonormal ℝ u}) :=
  ⟨‖r‖, fun _ ⟨_, hu, h⟩ ↦ h ▸ (le_abs_self _).trans (abs_apply_orthonormal_two_le_norm r hu)⟩

/-- `sectionalMin r` is a lower bound on `r ![u, v, u, v]` for every orthonormal pair `(u, v)`. -/
theorem sectionalMin_le_of_orthonormal (r : FourTensor V) {u v : V} (huv : Orthonormal ℝ ![u, v]) :
    sectionalMin r ≤ r ![u, v, u, v] :=
  csInf_le (bddBelow_sectionalImage r) ⟨![u, v], huv, rfl⟩

/-- `sectionalMax r` is an upper bound on `r ![u, v, u, v]` for every orthonormal pair `(u, v)`. -/
theorem le_sectionalMax_of_orthonormal (r : FourTensor V) {u v : V} (huv : Orthonormal ℝ ![u, v]) :
    r ![u, v, u, v] ≤ sectionalMax r :=
  le_csSup (bddAbove_sectionalImage r) ⟨![u, v], huv, rfl⟩

/-- `sectionalMin` is `1`-Lipschitz on `FourTensor V`. -/
theorem lipschitzWith_sectionalMin : LipschitzWith 1 (sectionalMin (V := V)) := by
  refine LipschitzWith.of_dist_le_mul fun r q ↦ ?_
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
  set S := {u : Fin 2 → V | Orthonormal ℝ u}
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [sectionalMin_def, S, hS]
  · have hle (r₁ r₂ : FourTensor V) : sectionalMin r₁ - ‖r₁ - r₂‖ ≤ sectionalMin r₂ := by
      refine le_csInf (hS.image _) ?_
      rintro _ ⟨u, hu, rfl⟩; dsimp only
      have hdiff : r₁ ![u 0, u 1, u 0, u 1] - r₂ ![u 0, u 1, u 0, u 1] ≤ ‖r₁ - r₂‖ := by
        simpa only [sub_apply] using (le_abs_self _).trans
          (abs_apply_orthonormal_two_le_norm (r₁ - r₂) hu)
      have hmin : sectionalMin r₁ ≤ r₁ ![u 0, u 1, u 0, u 1] :=
        csInf_le (bddBelow_sectionalImage r₁) ⟨u, hu, rfl⟩
      linarith
    rw [abs_sub_le_iff]; refine ⟨by linarith [hle r q], ?_⟩
    have := hle q r; rw [norm_sub_rev] at this; linarith

/-- `sectionalMax` is `1`-Lipschitz on `FourTensor V`. -/
theorem lipschitzWith_sectionalMax : LipschitzWith 1 (sectionalMax (V := V)) := by
  refine LipschitzWith.of_dist_le_mul fun r q ↦ ?_
  simpa only [sectionalMin_neg, dist_neg_neg, NNReal.coe_one, one_mul] using
    lipschitzWith_sectionalMin.dist_le_mul (-r) (-q)

/-- `sectionalMin` is continuous on `FourTensor V`. -/
theorem continuous_sectionalMin : Continuous (sectionalMin (V := V)) :=
  lipschitzWith_sectionalMin.continuous

/-- `sectionalMax` is continuous on `FourTensor V`. -/
theorem continuous_sectionalMax : Continuous (sectionalMax (V := V)) :=
  lipschitzWith_sectionalMax.continuous

/-- `sectionalMin` is invariant under pullback by linear isometric equivalences. -/
@[simp]
theorem sectionalMin_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    sectionalMin (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) = sectionalMin r := by
  rw [sectionalMin_def, sectionalMin_def]; congr 1; ext y; constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨e ∘ u, e.toLinearIsometry.orthonormal_comp_iff.2 hu,
      (compContinuousLinearMap_apply_vec r (e : W →L[ℝ] V) (u 0) (u 1) (u 0) (u 1)).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨e.symm ∘ u, e.symm.toLinearIsometry.orthonormal_comp_iff.2 hu, ?_⟩
    dsimp only; rw [compContinuousLinearMap_apply_vec]; simp

/-- `sectionalMax` is invariant under pullback by linear isometric equivalences. -/
@[simp]
theorem sectionalMax_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    sectionalMax (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) = sectionalMax r := by
  have h := sectionalMin_compContinuousLinearMap_linearIsometryEquiv e (-r)
  have hneg : (-r).compContinuousLinearMap (fun _ ↦ (e : W →L[ℝ] V)) =
      -(r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) := by ext m; rfl
  rwa [hneg, sectionalMin_neg, sectionalMin_neg, neg_inj] at h

/-- Every linearly independent pair `(u, v)` can be Gram–Schmidt normalized into an orthonormal pair
`(e₀, e₁)` within `span {u, v}` such that
`r ![u, v, u, v] = det(Gram(u, v)) * r ![e₀, e₁, e₀, e₁]`. -/
theorem IsAlgebraicCurvature.exists_orthonormal_apply_self_eq_det_gram_mul
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) {u v : V} (huv : LinearIndependent ℝ ![u, v]) :
    ∃ e₀ e₁ : V, Orthonormal ℝ ![e₀, e₁] ∧
      e₀ ∈ Submodule.span ℝ {u, v} ∧ e₁ ∈ Submodule.span ℝ {u, v} ∧
      r ![u, v, u, v] = (Matrix.gram ℝ ![u, v]).det * r ![e₀, e₁, e₀, e₁] := by
  have hu0 : u ≠ 0 := huv.ne_zero 0
  have hnorm_u : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set e₀ : V := ‖u‖⁻¹ • u
  have he₀_norm : ‖e₀‖ = 1 := by simp [e₀, norm_smul, hnorm_u.ne']
  set w : V := v - ⟪e₀, v⟫_ℝ • e₀
  have he₀w : ⟪e₀, w⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he₀_norm]; ring
  have hw0 : w ≠ 0 := fun hw ↦ (LinearIndependent.pair_iff' hu0).1 huv (⟪e₀, v⟫_ℝ * ‖u‖⁻¹)
    (by rw [mul_smul, ← sub_eq_zero.1 hw])
  have hnorm_w : 0 < ‖w‖ := norm_pos_iff.2 hw0
  set e₁ : V := ‖w‖⁻¹ • w
  have he₁_norm : ‖e₁‖ = 1 := by simp [e₁, norm_smul, hnorm_w.ne']
  have he₀e₁ : ⟪e₀, e₁⟫_ℝ = 0 := by simp [e₁, real_inner_smul_right, he₀w]
  have horth : Orthonormal ℝ ![e₀, e₁] :=
    ⟨fun i ↦ by fin_cases i <;> simp [he₀_norm, he₁_norm], fun {i j} hij ↦ by
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij | exact he₀e₁ | simpa [real_inner_comm] using he₀e₁⟩
  have hu_eq : u = ‖u‖ • e₀ := by simp [e₀, smul_smul, hnorm_u.ne']
  have hv_eq : v = ⟪e₀, v⟫_ℝ • e₀ + ‖w‖ • e₁ := by simp [e₁, smul_smul, hnorm_w.ne', w]
  have hr_self1 (a c d : V) : r ![a, a, c, d] = 0 := by linarith [hr.antisymm_first a a c d]
  have hr_self2 (a b c : V) : r ![a, b, c, c] = 0 := by linarith [hr.antisymm_last a b c c]
  have he₀_inner : ⟪e₀, e₀⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he₀_norm, one_pow]
  have he₁_inner : ⟪e₁, e₁⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he₁_norm, one_pow]
  have hgram : (Matrix.gram ℝ ![u, v]).det = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_lhs => rw [hu_eq, hv_eq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      he₀_inner, he₁_inner, he₀e₁, show ⟪e₁, e₀⟫_ℝ = 0 by rw [real_inner_comm]; exact he₀e₁]; ring
  have hr_eq : r ![u, v, u, v] = ‖u‖ ^ 2 * ‖w‖ ^ 2 * r ![e₀, e₁, e₀, e₁] := by
    conv_lhs => rw [hu_eq, hv_eq]
    simp only [r.apply_add_second, r.apply_add_fourth, r.apply_smul_first, r.apply_smul_second,
      r.apply_smul_third, r.apply_smul_fourth, hr_self1, hr_self2]; ring
  have he₀_mem : e₀ ∈ Submodule.span ℝ {u, v} :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact ⟨e₀, e₁, horth, he₀_mem, Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.subset_span (by simp)) (Submodule.smul_mem _ _ he₀_mem)), by rw [hgram, hr_eq]⟩

/-- For an algebraic curvature tensor `r`, `sectionalMin r` and `sectionalMax r` bound every
sectional numerator `r ![u, v, u, v]` against `det(Gram(u, v))`, including dependent pairs. -/
theorem IsAlgebraicCurvature.sectionalMin_mul_det_gram_le_and_le_sectionalMax
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (u v : V) :
    sectionalMin r * (Matrix.gram ℝ ![u, v]).det ≤ r ![u, v, u, v] ∧
      r ![u, v, u, v] ≤ sectionalMax r * (Matrix.gram ℝ ![u, v]).det := by
  by_cases huv : LinearIndependent ℝ ![u, v]
  · obtain ⟨e₀, e₁, horth, -, -, heq⟩ := hr.exists_orthonormal_apply_self_eq_det_gram_mul huv
    have hdet : 0 < (Matrix.gram ℝ ![u, v]).det :=
      (Matrix.posDef_gram_of_linearIndependent huv).det_pos
    rw [heq, mul_comm (Matrix.gram ℝ ![u, v]).det]
    exact ⟨mul_le_mul_of_nonneg_right (sectionalMin_le_of_orthonormal r horth) hdet.le,
      mul_le_mul_of_nonneg_right (le_sectionalMax_of_orthonormal r horth) hdet.le⟩
  · have hdet : (Matrix.gram ℝ ![u, v]).det = 0 :=
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv)
    have hr0 : r ![u, v, u, v] = 0 := by
      have := LinearMap.apply_apply_apply_apply_eq_zero_of_not_linearIndependent
        (T := r.toLinearMap₄) two_ne_zero
        (fun a b c d ↦ by simpa only [toLinearMap₄_apply] using hr.antisymm_first a b c d) huv
      simp only [toLinearMap₄_apply] at this; linarith [hr.antisymm_last u v u v]
    simp [hdet, hr0]

/-! ### Berger's mixed-component estimate and strict quarter pinching -/

private theorem orthonormal_inv_sqrt_two_add {x₁ x₂ y₁ y₂ : V}
    (hx₁ : ‖x₁‖ = 1) (hx₂ : ‖x₂‖ = 1) (hy₁ : ‖y₁‖ = 1) (hy₂ : ‖y₂‖ = 1)
    (hx : ⟪x₁, x₂⟫_ℝ = 0) (hy : ⟪y₁, y₂⟫_ℝ = 0)
    (h₁₁ : ⟪x₁, y₁⟫_ℝ = 0) (h₁₂ : ⟪x₁, y₂⟫_ℝ = 0)
    (h₂₁ : ⟪x₂, y₁⟫_ℝ = 0) (h₂₂ : ⟪x₂, y₂⟫_ℝ = 0) :
    Orthonormal ℝ ![(√2)⁻¹ • (x₁ + x₂), (√2)⁻¹ • (y₁ + y₂)] := by
  have hnorm {a b : V} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫_ℝ = 0) :
      ‖(√2)⁻¹ • (a + b)‖ = 1 := by
    have hsq : ‖a + b‖ ^ 2 = 2 := by rw [norm_add_sq_real, ha, hb, hab]; ring
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg 2)),
      ← Real.sqrt_sq (norm_nonneg (a + b)), hsq, inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 two_pos)]
  have hinner : ⟪(√2)⁻¹ • (x₁ + x₂), (√2)⁻¹ • (y₁ + y₂)⟫_ℝ = 0 := by
    simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      h₁₁, h₁₂, h₂₁, h₂₂]
  refine ⟨fun i ↦ by fin_cases i; exacts [hnorm hx₁ hx₂ hx, hnorm hy₁ hy₂ hy], fun {i j} hij ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij | exact hinner | simpa [real_inner_comm] using hinner

/-- **Berger's mixed-component estimate (localized to `span(f)`).** For an algebraic curvature
tensor `r` and an orthonormal four-frame `f`, if `a ≤ r ![u, v, u, v] ≤ b` on every orthonormal pair
`(u, v)` in `span(range f)`, then `|r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a)`. -/
theorem IsAlgebraicCurvature.abs_apply_orthonormal_le_of_span {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {f : Fin 4 → V} (hf : Orthonormal ℝ f) {a b : ℝ}
    (hsec : ∀ u v : V, u ∈ Submodule.span ℝ (range f) → v ∈ Submodule.span ℝ (range f) →
      Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b) :
    |r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a) := by
  have hpol := LinearMap.twentyFour_mul_apply_eq_of_cyclic_eq_zero (T := r.toLinearMap₄)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.antisymm_first u v z w)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.antisymm_last u v z w)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.cyclic_eq_zero u v z w)
    (f 0) (f 1) (f 2) (f 3)
  have hflip (x y : V) : r ![x, y, y, x] = -r ![x, y, x, y] := by
    linarith [hr.antisymm_last x y x y]
  simp only [toLinearMap₄_apply, hflip] at hpol
  have hpair (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l)
      (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
      (s₁ s₂ : ℝ) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) :
      4 * a ≤ r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] ∧
        r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] ≤ 4 * b := by
    have hs₁_norm : ‖s₁ • f j‖ = 1 := by rcases hs₁ with rfl | rfl <;> simp [hf.1 j]
    have hs₂_norm : ‖s₂ • f l‖ = 1 := by rcases hs₂ with rfl | rfl <;> simp [hf.1 l]
    have horth := orthonormal_inv_sqrt_two_add (hf.1 i) hs₁_norm (hf.1 k) hs₂_norm
      (by simp [real_inner_smul_right, hf.2 hij]) (by simp [real_inner_smul_right, hf.2 hkl])
      (hf.2 hik) (by simp [real_inner_smul_right, hf.2 hil])
      (by simp [real_inner_smul_left, hf.2 hjk])
      (by simp [real_inner_smul_left, real_inner_smul_right, hf.2 hjl])
    have hmem (p q : Fin 4) (s : ℝ) : (√2)⁻¹ • (f p + s • f q) ∈ Submodule.span ℝ (range f) :=
      Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨p, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)))
    have hbds := hsec _ _ (hmem i j s₁) (hmem k l s₂) horth
    have hsq : ((√2)⁻¹ : ℝ) * (√2)⁻¹ = 1 / 2 := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]
    rw [r.apply_smul_first, r.apply_smul_second, r.apply_smul_third, r.apply_smul_fourth,
      show (√2)⁻¹ * ((√2)⁻¹ * ((√2)⁻¹ * ((√2)⁻¹ *
          r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l]))) =
        (1 / 4 : ℝ) * r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] by
        linear_combination (2 * ((√2)⁻¹ * (√2)⁻¹) + 1) *
          r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] * hsq / 2] at hbds
    exact ⟨by linarith [hbds.1], by linarith [hbds.2]⟩
  have bp (s₁ s₂ : ℝ) (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) := And.intro
    (hpair 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s₁ s₂ h₁ h₂)
    (hpair 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s₁ s₂ h₁ h₂)
  obtain ⟨b1, b5⟩ := bp 1 1 (.inl rfl) (.inl rfl)
  obtain ⟨b2, b6⟩ := bp 1 (-1) (.inl rfl) (.inr rfl)
  obtain ⟨b3, b7⟩ := bp (-1) 1 (.inr rfl) (.inl rfl)
  obtain ⟨b4, b8⟩ := bp (-1) (-1) (.inr rfl) (.inr rfl)
  simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at b1 b2 b3 b4 b5 b6 b7 b8
  rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- **Berger's mixed-component estimate.** If every orthonormal two-frame in `V` has sectional
curvature in `[a, b]`, then `|r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a)` for every orthonormal
four-frame `f`. -/
theorem IsAlgebraicCurvature.abs_apply_orthonormal_le {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {f : Fin 4 → V} (hf : Orthonormal ℝ f) {a b : ℝ}
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b) :
    |r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a) :=
  hr.abs_apply_orthonormal_le_of_span hf fun u v _ _ huv ↦ hsec u v huv

/-- Berger's estimate in terms of `sectionalMin r` and `sectionalMax r`:
`|r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (sectionalMax r - sectionalMin r)` on every orthonormal
four-frame `f`. -/
theorem IsAlgebraicCurvature.abs_apply_orthonormal_le_sectionalMax_sub_sectionalMin
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) {f : Fin 4 → V} (hf : Orthonormal ℝ f) :
    |r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (sectionalMax r - sectionalMin r) :=
  hr.abs_apply_orthonormal_le hf fun _ _ huv ↦
    ⟨sectionalMin_le_of_orthonormal r huv, le_sectionalMax_of_orthonormal r huv⟩

/-- **Quantitative lower bound on `pic2Expression` from sectional bounds.** If every orthonormal
two-frame has sectional curvature in `[a, b]`, then for every orthonormal four-frame `f` and all
real scalars `l, m`:
`min a ((4 * a - b) / 3) * (1 + l ^ 2) * (1 + m ^ 2) ≤ pic2Expression r f l m`. -/
theorem IsAlgebraicCurvature.le_pic2Expression_of_sectional_mem_Icc {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {a b : ℝ}
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b)
    {f : Fin 4 → V} (hf : Orthonormal ℝ f) (l m : ℝ) :
    min a ((4 * a - b) / 3) * (1 + l ^ 2) * (1 + m ^ 2) ≤ pic2Expression r f l m := by
  have hp (i j : Fin 4) (hij : i ≠ j) : Orthonormal ℝ ![f i, f j] := by
    refine ⟨fun k ↦ by fin_cases k <;> exact hf.1 _, fun {k₁ k₂} hk ↦ ?_⟩
    fin_cases k₁ <;> fin_cases k₂ <;> first
      | exact absurd rfl hk | exact hf.2 hij | exact hf.2 hij.symm
  have hcross : -(4 / 3) * (b - a) * |l * m| ≤ -2 * l * m * r ![f 0, f 1, f 2, f 3] := by
    have hprod : |(l * m) * r ![f 0, f 1, f 2, f 3]| ≤ |l * m| * ((2 / 3) * (b - a)) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr.abs_apply_orthonormal_le hf hsec)
        (abs_nonneg _)
    linarith [(abs_le.1 hprod).2]
  have hdiag : a * (1 + l ^ 2) * (1 + m ^ 2) ≤
      r ![f 0, f 2, f 0, f 2] + l ^ 2 * r ![f 0, f 3, f 0, f 3] +
        m ^ 2 * r ![f 1, f 2, f 1, f 2] + l ^ 2 * m ^ 2 * r ![f 1, f 3, f 1, f 3] := by
    nlinarith [(hsec (f 0) (f 2) (hp 0 2 (by decide))).1,
      mul_le_mul_of_nonneg_left (hsec (f 0) (f 3) (hp 0 3 (by decide))).1 (sq_nonneg l),
      mul_le_mul_of_nonneg_left (hsec (f 1) (f 2) (hp 1 2 (by decide))).1 (sq_nonneg m),
      mul_le_mul_of_nonneg_left (hsec (f 1) (f 3) (hp 1 3 (by decide))).1
        (mul_nonneg (sq_nonneg l) (sq_nonneg m))]
  have hamgm : 4 * |l * m| ≤ (1 + l ^ 2) * (1 + m ^ 2) := by
    nlinarith [sq_abs l, sq_abs m, abs_mul l m, sq_nonneg (1 - |l * m|), sq_nonneg (|l| - |m|)]
  have hab : 0 ≤ b - a := by
    linarith [(hsec (f 0) (f 2) (hp 0 2 (by decide))).1, (hsec (f 0) (f 2) (hp 0 2 (by decide))).2]
  have hpen := mul_le_mul_of_nonneg_left hamgm (by positivity : 0 ≤ (b - a) / 3)
  have hstep := mul_le_mul_of_nonneg_right (min_le_right a ((4 * a - b) / 3))
    (by positivity : 0 ≤ (1 + l ^ 2) * (1 + m ^ 2))
  rw [pic2Expression_def]; nlinarith

/-- **Weak quarter pinching gives PIC2.** If every orthonormal two-frame has sectional curvature in
`[a, b]` with `0 ≤ a` and `b ≤ 4 * a`, then `IsPIC2FourFrame r`. -/
theorem IsAlgebraicCurvature.isPIC2FourFrame_of_weak_quarterPinching {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {a b : ℝ} (ha : 0 ≤ a) (hab : b ≤ 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b) :
    IsPIC2FourFrame r := by
  rw [isPIC2FourFrame_def]; intro f hf l _ m _
  exact (mul_nonneg (mul_nonneg (le_min ha (by linarith)) (by positivity)) (by positivity)).trans
    (hr.le_pic2Expression_of_sectional_mem_Icc hsec hf l m)

/-- **Strict pointwise quarter pinching gives strict PIC2** (Brendle–Schoen). If every sectional
curvature of an algebraic curvature tensor `r` lies in `[a, b]` with `0 < a` and `b < 4 * a`, then
`0 < pic2Expression r.1 f l m` for every orthonormal four-frame `f` and all parameters
`l, m ∈ [-1, 1]`. -/
theorem strict_quarterPinching_isPIC2 (r : algebraicCurvatureSubmodule V) (a b : ℝ)
    (ha : 0 < a) (hab : b < 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r.1 ![u, v, u, v] ∧ r.1 ![u, v, u, v] ≤ b) :
    ∀ f : Fin 4 → V, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1,
      ∀ m ∈ Icc (-1 : ℝ) 1, 0 < pic2Expression r.1 f l m := fun f hf l _ m _ ↦
  (mul_pos (mul_pos (lt_min ha (by linarith)) (by positivity)) (by positivity)).trans_le
    ((IsAlgebraicCurvature.of_mem r).le_pic2Expression_of_sectional_mem_Icc hsec hf l m)

/-- Strict quarter pinching with constants `0 < a` and `b < 4 * a` puts `r` in the interior of the
PIC2 cone in `algebraicCurvatureSubmodule V` (with uniform margin `min a ((4 * a - b) / 3)`). -/
theorem mem_interior_isPIC2FourFrame_of_sectional_mem_Icc (r : algebraicCurvatureSubmodule V)
    {a b : ℝ} (ha : 0 < a) (hab : b < 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r.1 ![u, v, u, v] ∧ r.1 ![u, v, u, v] ≤ b) :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  have hmin : 0 < min a ((4 * a - b) / 3) := lt_min ha (by linarith)
  refine mem_interior_isPIC2FourFrame_of_exists_pos_le hmin fun f hf l _ m _ ↦ ?_
  refine (le_mul_of_one_le_right hmin.le
    (show 1 ≤ (1 + l ^ 2) * (1 + m ^ 2) by nlinarith [sq_nonneg l, sq_nonneg m])).trans ?_
  simpa only [mul_assoc] using
    (IsAlgebraicCurvature.of_mem r).le_pic2Expression_of_sectional_mem_Icc hsec hf l m

/-- When `4 ≤ finrank ℝ V`, every algebraic curvature tensor in `IsPIC2FourFrame` has nonnegative
sectional numerators `0 ≤ r ![u, v, u, v]` on all pairs `(u, v)`. -/
theorem IsPIC2FourFrame.apply_self_nonneg {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (hpic : IsPIC2FourFrame r) (hn : 4 ≤ Module.finrank ℝ V) (u v : V) :
    0 ≤ r ![u, v, u, v] := by
  by_cases huv : LinearIndependent ℝ ![u, v]
  · obtain ⟨e₀, e₁, horth, -, -, heq⟩ := hr.exists_orthonormal_apply_self_eq_det_gram_mul huv
    obtain ⟨f, hf, rfl, rfl⟩ := horth.exists_fin_four_extension hn
    have h0 := (isPIC2FourFrame_def _).1 hpic f hf 0 (by norm_num) 0 (by norm_num)
    rw [pic2Expression_zero_zero] at h0; rw [heq]
    exact mul_nonneg (Matrix.posDef_gram_of_linearIndependent huv).det_pos.le h0
  · have := LinearMap.apply_apply_apply_apply_eq_zero_of_not_linearIndependent
      (T := r.toLinearMap₄) two_ne_zero
      (fun a b c d ↦ by simpa only [toLinearMap₄_apply] using hr.antisymm_first a b c d) huv
    simp only [toLinearMap₄_apply] at this; linarith [hr.antisymm_last u v u v]

end InnerProductSpace

/-! ### Finite-dimensional attainment and Fubini–Study sharpness -/

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- In dimension at least two, `sectionalMin r` is attained at an orthonormal pair `(u, v)`. -/
theorem exists_orthonormal_eq_sectionalMin (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ∃ u v : V, Orthonormal ℝ ![u, v] ∧ r ![u, v, u, v] = sectionalMin r := by
  have hKne : {u : Fin 2 → V | Orthonormal ℝ u}.Nonempty :=
    (nonempty_setOf_orthonormal_iff (ι := Fin 2) (V := V)).2 (by simpa using hn)
  have hcont : Continuous fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1] :=
    r.cont.comp (continuous_pi fun k ↦ by fin_cases k <;> exact continuous_apply _)
  obtain ⟨u, hu, hmin⟩ := isCompact_setOf_orthonormal.exists_isMinOn hKne hcont.continuousOn
  have hu_eq : ![u 0, u 1] = u := by funext i; fin_cases i <;> rfl
  refine ⟨u 0, u 1, by rwa [hu_eq],
    le_antisymm ?_ (sectionalMin_le_of_orthonormal r (by rwa [hu_eq]))⟩
  refine le_csInf (hKne.image _) ?_; rintro _ ⟨w, hw, rfl⟩; exact isMinOn_iff.1 hmin w hw

/-- In dimension at least two, `sectionalMax r` is attained at an orthonormal pair `(u, v)`. -/
theorem exists_orthonormal_eq_sectionalMax (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ∃ u v : V, Orthonormal ℝ ![u, v] ∧ r ![u, v, u, v] = sectionalMax r := by
  obtain ⟨u, v, huv, heq⟩ := exists_orthonormal_eq_sectionalMin hn (-r)
  exact ⟨u, v, huv, by simpa using neg_inj.2 heq⟩

/-- In dimension at least two, `sectionalMin r ≤ sectionalMax r`. -/
theorem sectionalMin_le_sectionalMax (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    sectionalMin r ≤ sectionalMax r := by
  obtain ⟨u, v, huv, hmin⟩ := exists_orthonormal_eq_sectionalMin hn r
  exact hmin ▸ le_sectionalMax_of_orthonormal r huv

/-- Unquantified pointwise strict quarter pinching on all linearly independent pairs in a space of
dimension at least two implies `0 < sectionalMin r.1`, `sectionalMax r.1 < 4 * sectionalMin r.1`,
and places `r` in the interior of the PIC2 cone. -/
theorem mem_interior_isPIC2FourFrame_of_quarterPinched (hn : 2 ≤ Module.finrank ℝ V)
    (r : algebraicCurvatureSubmodule V)
    (hpinch : ∀ u v u' v' : V, LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
      0 < r.1 ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det ∧
        r.1 ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det <
          4 * (r.1 ![u', v', u', v'] / (Matrix.gram ℝ ![u', v']).det)) :
    0 < sectionalMin r.1 ∧ sectionalMax r.1 < 4 * sectionalMin r.1 ∧
      r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  obtain ⟨u₀, v₀, h₀, hmin⟩ := exists_orthonormal_eq_sectionalMin hn r.1
  obtain ⟨u₁, v₁, h₁, hmax⟩ := exists_orthonormal_eq_sectionalMax hn r.1
  have hp := hpinch u₁ v₁ u₀ v₀ h₁.linearIndependent h₀.linearIndependent
  have hp₀ := (hpinch u₀ v₀ u₀ v₀ h₀.linearIndependent h₀.linearIndependent).1
  rw [Matrix.gram_eq_one_iff_orthonormal.2 h₀, Matrix.gram_eq_one_iff_orthonormal.2 h₁,
    Matrix.det_one, div_one, div_one, hmin, hmax] at hp
  rw [Matrix.gram_eq_one_iff_orthonormal.2 h₀, Matrix.det_one, div_one, hmin] at hp₀
  exact ⟨hp₀, hp.2, mem_interior_isPIC2FourFrame_of_sectional_mem_Icc r hp₀ hp.2
    fun _ _ huv ↦ ⟨sectionalMin_le_of_orthonormal r.1 huv, le_sectionalMax_of_orthonormal r.1 huv⟩⟩

/-! ### Constant holomorphic sectional curvature (Fubini–Study) and sharpness -/

/-- The constant-holomorphic-sectional-curvature (Fubini–Study) four-tensor attached to an almost
complex structure `J` on `V`, normalized to holomorphic sectional curvature `4` (sectional
curvatures in `[1, 4]` when `J` is orthogonal):
`r(u, v, z, w) = ⟪u, z⟫ ⟪v, w⟫ - ⟪u, w⟫ ⟪v, z⟫ + ⟪J u, z⟫ ⟪J v, w⟫`
`- ⟪J u, w⟫ ⟪J v, z⟫ + 2 ⟪J u, v⟫ ⟪J z, w⟫`. -/
def fubiniStudy (J : AlmostComplexStructure V) : FourTensor V :=
  ofLinearMap₄ <| LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.mk₂ ℝ
      (fun z w ↦ ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ +
        ⟪J u, z⟫_ℝ * ⟪J v, w⟫_ℝ - ⟪J u, w⟫_ℝ * ⟪J v, z⟫_ℝ + 2 * ⟪J u, v⟫_ℝ * ⟪J z, w⟫_ℝ)
      (fun _ _ _ ↦ by simp [inner_add_right, inner_add_left, map_add]; ring)
      (fun _ _ _ ↦ by simp [real_inner_smul_right, real_inner_smul_left, map_smul]; ring)
      (fun _ _ _ ↦ by simp [inner_add_right]; ring)
      (fun _ _ _ ↦ by simp [real_inner_smul_right]; ring))
    (fun _ _ _ ↦ by ext; simp [inner_add_left, map_add]; ring)
    (fun _ _ _ ↦ by ext; simp [real_inner_smul_left, map_smul]; ring)
    (fun _ _ _ ↦ by ext; simp [inner_add_left, inner_add_right, map_add]; ring)
    (fun _ _ _ ↦ by ext; simp [real_inner_smul_left, real_inner_smul_right, map_smul]; ring)

/-- Evaluation of the Fubini–Study four-tensor. -/
@[simp]
theorem fubiniStudy_apply (J : AlmostComplexStructure V) (u v z w : V) :
    fubiniStudy J ![u, v, z, w] =
      ⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ +
        ⟪J u, z⟫_ℝ * ⟪J v, w⟫_ℝ - ⟪J u, w⟫_ℝ * ⟪J v, z⟫_ℝ +
        2 * ⟪J u, v⟫_ℝ * ⟪J z, w⟫_ℝ := by simp [fubiniStudy]

/-- For an orthogonal almost complex structure `J`, `fubiniStudy J` is an algebraic curvature
tensor. -/
theorem isAlgebraicCurvature_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) :
    IsAlgebraicCurvature (fubiniStudy J) := by
  have hω (x y : V) : ⟪J x, y⟫_ℝ = -⟪J y, x⟫_ℝ := by
    have h := hJ (J x) y; rw [J.apply_apply, inner_neg_left, real_inner_comm (J y) x] at h; linarith
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [fubiniStudy_apply]
  · rw [hω v u]; ring
  · rw [hω w z]; ring
  · rw [real_inner_comm u z, real_inner_comm v w, real_inner_comm v z, real_inner_comm u w,
      hω z u, hω w v, hω z v, hω w u]; ring
  · rw [real_inner_comm u z, real_inner_comm u v, real_inner_comm v z, hω v u, hω z u, hω z v]
    ring

/-- On a pair `(u, v)`, `fubiniStudy J ![u, v, u, v] = ‖u‖² ‖v‖² - ⟪u, v⟫² + 3 ⟪J u, v⟫²`. -/
theorem fubiniStudy_apply_self {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) (u v : V) :
    fubiniStudy J ![u, v, u, v] = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 + 3 * ⟪J u, v⟫_ℝ ^ 2 := by
  have hω : ⟪J v, u⟫_ℝ = -⟪J u, v⟫_ℝ := by
    have h := hJ (J v) u; rw [J.apply_apply, inner_neg_left, real_inner_comm (J u) v] at h; linarith
  rw [fubiniStudy_apply, J.inner_apply_self hJ u, J.inner_apply_self hJ v, hω,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm u v]; ring

/-- On an orthonormal pair `(u, v)`, the sectional curvature of `fubiniStudy J` equals
`1 + 3 ⟪J u, v⟫²` and lies in `[1, 4]`. -/
theorem fubiniStudy_sectional_mem_Icc {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) {u v : V} (huv : Orthonormal ℝ ![u, v]) :
    1 ≤ fubiniStudy J ![u, v, u, v] ∧ fubiniStudy J ![u, v, u, v] ≤ 4 := by
  have hu : ‖u‖ = 1 := huv.1 0
  have hv : ‖v‖ = 1 := huv.1 1
  have huv0 : ⟪u, v⟫_ℝ = 0 := huv.2 (by decide : (0 : Fin 2) ≠ 1)
  rw [fubiniStudy_apply_self hJ, hu, hv, huv0]
  have hcs : |⟪J u, v⟫_ℝ| ≤ 1 := by
    simpa only [J.norm_apply hJ, hu, hv, mul_one] using abs_real_inner_le_norm (J u) v
  have hsq : ⟪J u, v⟫_ℝ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ⟪J u, v⟫_ℝ]
  exact ⟨by nlinarith [sq_nonneg ⟪J u, v⟫_ℝ], by linarith⟩

/-- On any holomorphic unit pair `(u, J u)` (`‖u‖ = 1`), `fubiniStudy J` attains the upper
sectional curvature `4`. -/
theorem fubiniStudy_apply_holomorphic {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) {u : V} (hu : ‖u‖ = 1) :
    Orthonormal ℝ ![u, J u] ∧ fubiniStudy J ![u, J u, u, J u] = 4 := by
  have h0 : ⟪u, J u⟫_ℝ = 0 := by rw [real_inner_comm, J.inner_apply_self hJ]
  refine ⟨⟨fun i ↦ by fin_cases i <;> simp [hu, J.norm_apply hJ], fun {i j} hij ↦ ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij | exact h0 | exact J.inner_apply_self hJ u
  · rw [fubiniStudy_apply_self hJ, hu, J.norm_apply hJ, h0, real_inner_self_eq_norm_sq,
      J.norm_apply hJ, hu]; norm_num

/-- **Sharpness of Berger's bound.** On a unitary orthonormal four-frame `![X, J X, Y, J Y]`,
`fubiniStudy J ![X, J X, Y, J Y] = 2 = (2 / 3) * (4 - 1)` and
`pic2Expression (fubiniStudy J) ![X, J X, Y, J Y] 1 1 = 0`. -/
theorem fubiniStudy_apply_unitary {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) {X Y : V}
    (hf : Orthonormal ℝ ![X, J X, Y, J Y]) :
    fubiniStudy J ![X, J X, Y, J Y] = 2 ∧
      pic2Expression (fubiniStudy J) ![X, J X, Y, J Y] 1 1 = 0 := by
  have hX : ‖X‖ = 1 := hf.1 0
  have hY : ‖Y‖ = 1 := hf.1 2
  have hXY : ⟪X, Y⟫_ℝ = 0 := hf.2 (by decide : (0 : Fin 4) ≠ 2)
  have hXJY : ⟪X, J Y⟫_ℝ = 0 := hf.2 (by decide : (0 : Fin 4) ≠ 3)
  have hJXY : ⟪J X, Y⟫_ℝ = 0 := hf.2 (by decide : (1 : Fin 4) ≠ 2)
  have hJXJY : ⟪J X, J Y⟫_ℝ = 0 := hf.2 (by decide : (1 : Fin 4) ≠ 3)
  have hmix : fubiniStudy J ![X, J X, Y, J Y] = 2 := by
    rw [fubiniStudy_apply]
    simp only [J.apply_apply, hXY, hXJY, hJXY, hJXJY, inner_neg_left,
      real_inner_self_eq_norm_sq, J.norm_apply hJ, hX, hY]; ring
  refine ⟨hmix, ?_⟩
  rw [pic2Expression_def]; dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [hmix, fubiniStudy_apply_self hJ X Y, fubiniStudy_apply_self hJ X (J Y),
    fubiniStudy_apply_self hJ (J X) Y, fubiniStudy_apply_self hJ (J X) (J Y)]
  simp only [J.apply_apply, J.norm_apply hJ, hX, hY, hXY, hXJY, hJXY, hJXJY, inner_neg_left]; ring

/-- The Fubini–Study curvature tensor of an orthogonal almost complex structure lies in the PIC2
cone (`1 ≤ K ≤ 4 = 4 * 1`). -/
theorem isPIC2FourFrame_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) :
    IsPIC2FourFrame (fubiniStudy J) :=
  (isAlgebraicCurvature_fubiniStudy hJ).isPIC2FourFrame_of_weak_quarterPinching
    zero_le_one (by norm_num) (fun _ _ huv ↦ fubiniStudy_sectional_mem_Icc hJ huv)

/-- **Weak quarter pinching does not imply PIC2 interior.** On any even-dimensional real inner
product space of dimension at least four, the Fubini–Study curvature tensor of an orthogonal almost
complex structure `J` has sectional curvatures in `[1, 4]` and lies in `IsPIC2FourFrame`, but does
not lie in `interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}`. -/
theorem not_mem_interior_isPIC2FourFrame_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) (hEven : Even (Module.finrank ℝ V))
    (hn : 4 ≤ Module.finrank ℝ V) :
    (⟨fubiniStudy J, mem_algebraicCurvatureSubmodule.2 (isAlgebraicCurvature_fubiniStudy hJ)⟩ :
       algebraicCurvatureSubmodule V) ∉
      interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  obtain ⟨k, hk⟩ := hEven
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) k (by omega)
  let idx : Fin 4 ↪ Fin (2 * k) := Fin.castLEEmb (by omega)
  let f : Fin 4 → V := fun i ↦ b (idx i)
  have hf : Orthonormal ℝ f := b.orthonormal.comp idx idx.injective
  have hf1 : f 1 = J (f 0) := hb ⟨0, by omega⟩
  have hf3 : f 3 = J (f 2) := hb ⟨1, by omega⟩
  have hf_eq : f = ![f 0, J (f 0), f 2, J (f 2)] := by funext i; fin_cases i <;> simp [hf1, hf3]
  rw [hf_eq] at hf
  intro hint
  have hpos := (mem_interior_isPIC2FourFrame_iff_forall_pos.1 hint)
    ![f 0, J (f 0), f 2, J (f 2)] hf 1 (by norm_num) 1 (by norm_num)
  linarith [(fubiniStudy_apply_unitary hJ hf).2]

/-- Concrete four-dimensional boundary witness on `EuclideanSpace ℝ (Fin 4)`: there exists an
algebraic curvature tensor with sectional curvatures in `[1, 4]` that lies in `IsPIC2FourFrame` but
not in the interior of the PIC2 cone. -/
theorem exists_isPIC2FourFrame_not_mem_interior_fin_four :
    ∃ r : algebraicCurvatureSubmodule (EuclideanSpace ℝ (Fin 4)),
      IsPIC2FourFrame r.1 ∧
        (∀ u v, Orthonormal ℝ ![u, v] → 1 ≤ r.1 ![u, v, u, v] ∧ r.1 ![u, v, u, v] ≤ 4) ∧
        r ∉ interior
          {q : algebraicCurvatureSubmodule (EuclideanSpace ℝ (Fin 4)) | IsPIC2FourFrame q.1} := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by simp
  obtain ⟨J, hJnorm⟩ := AlmostComplexStructure.exists_forall_norm_apply_eq
    (V := EuclideanSpace ℝ (Fin 4)) ⟨2, by omega⟩
  have hJ : ∀ u v : EuclideanSpace ℝ (Fin 4), ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ := fun u v ↦ by
    have h1 := norm_add_sq_real (J u) (J v)
    rw [← J.apply_add, hJnorm, hJnorm, hJnorm] at h1; linarith [norm_add_sq_real u v]
  exact ⟨⟨fubiniStudy J, mem_algebraicCurvatureSubmodule.2 (isAlgebraicCurvature_fubiniStudy hJ)⟩,
    isPIC2FourFrame_fubiniStudy hJ, fun _ _ huv ↦ fubiniStudy_sectional_mem_Icc hJ huv,
    not_mem_interior_isPIC2FourFrame_fubiniStudy hJ ⟨2, by omega⟩ (by omega)⟩

end FiniteDimensional

end TauCeti.FourTensor
