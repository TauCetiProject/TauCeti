/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Isotropic
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Sectional
public import TauCeti.Geometry.Symplectic.AlmostComplex
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Compact
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.Geometry.Symplectic.Finrank
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
`b < 4 a`) gives strict positivity of `pic2Expression` and places `r` in
`interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}` (which coincides with the
interior of the `PIC2` cone when `4 ≤ Module.finrank ℝ V` and equals `Set.univ` vacuously when
`Module.finrank ℝ V < 4`).

Both Berger's constant `2 / 3` and the strict inequality `b < 4 a` are sharp: for an almost complex
structure `J` preserving the inner product (`∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ`), the Fubini–Study
four-tensor `fubiniStudy J` has sectional curvatures in `[1, 4]`, satisfies
`fubiniStudy J ![X, J X, Y, J Y] = 2` on every unitary orthonormal four-frame, lies in
`IsPIC2FourFrame`, and vanishes on `pic2Expression` at `l = m = 1`, so in dimension at least four
it lies outside the interior of the `PIC2` cone.

## Main definitions

* `TauCeti.FourTensor.fubiniStudy`: the Fubini–Study four-tensor attached to an almost complex
  structure `J`; when `J` preserves the inner product (`∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ`), it is an
  algebraic curvature tensor of constant holomorphic sectional curvature `4`.

## Main statements

* `TauCeti.FourTensor.IsAlgebraicCurvature.abs_apply_orthonormal_le`: Berger's `2 / 3` estimate.
* `TauCeti.FourTensor.IsAlgebraicCurvature.pic2Expression_pos_of_strict_quarterPinching`,
  `TauCeti.FourTensor.sectionalMin_pos_of_quarterPinched`,
  `TauCeti.FourTensor.sectionalMax_lt_four_mul_sectionalMin_of_quarterPinched`, and
  `TauCeti.FourTensor.mem_interior_isPIC2FourFrame_of_quarterPinched`.
* `TauCeti.FourTensor.IsPIC2FourFrame.apply_self_nonneg`: nonnegativity of sectional numerators in
  dimension at least four.
* `TauCeti.FourTensor.fubiniStudy_apply_unitary`, `TauCeti.FourTensor.isPIC2FourFrame_fubiniStudy`,
  `TauCeti.FourTensor.notMem_interior_isPIC2FourFrame_fubiniStudy`, and
  `TauCeti.FourTensor.exists_isPIC2FourFrame_notMem_interior_fin_four`.

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
open scoped InnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

/-! ### Berger's mixed-component estimate and strict quarter pinching -/

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem inv_sqrt_two_pow_four : ((√2)⁻¹ : ℝ) ^ 4 = 1 / 4 := by
  have hsq : ((√2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]
  calc ((√2)⁻¹ : ℝ) ^ 4 = (((√2)⁻¹ : ℝ) ^ 2) ^ 2 := by ring
    _ = 1 / 4 := by rw [hsq]; norm_num

/-- Rescaling a pair `(f i + s₁ • f j, f k + s₂ • f l)` (for distinct `i, j, k, l` and signs
`s₁, s₂ ∈ {1, -1}`) by `(√2)⁻¹` produces an orthonormal pair in `span(range f)`, so sectional
bounds `[a, b]` on `span(range f)` scale to `[4 * a, 4 * b]` on the unnormalized pair. -/
private theorem apply_add_smul_self_mem_Icc_of_span {r : FourTensor V} {f : Fin 4 → V}
    (hf : Orthonormal ℝ f) {a b : ℝ}
    (hsec : ∀ u v : V, u ∈ Submodule.span ℝ (range f) → v ∈ Submodule.span ℝ (range f) →
      Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b)
    {i j k l : Fin 4} (hinj : Function.Injective ![i, j, k, l])
    {s₁ s₂ : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) :
    4 * a ≤ r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] ∧
      r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] ≤ 4 * b := by
  have hperm : (f ∘ ![i, j, k, l]) = ![f i, f j, f k, f l] := by
    funext t; fin_cases t <;> rfl
  have hf4 : Orthonormal ℝ ![f i, f j, f k, f l] := hperm ▸ hf.comp ![i, j, k, l] hinj
  have hfs : Orthonormal ℝ ![f i, s₁ • f j, f k, s₂ • f l] :=
    hf4.orthonormal_of_forall_eq_or_eq_neg fun t ↦ by
      fin_cases t
      · exact .inl rfl
      · exact hs₁.imp (fun h ↦ by simp [h]) (fun h ↦ by simp [h])
      · exact .inl rfl
      · exact hs₂.imp (fun h ↦ by simp [h]) (fun h ↦ by simp [h])
  have horth : Orthonormal ℝ ![(√2)⁻¹ • (f i + s₁ • f j), (√2)⁻¹ • (f k + s₂ • f l)] :=
    hfs.inv_sqrt_two_add_pair
  have hmem (p q : Fin 4) (s : ℝ) : (√2)⁻¹ • (f p + s • f q) ∈ Submodule.span ℝ (range f) :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨p, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)))
  have hbds := hsec _ _ (hmem i j s₁) (hmem k l s₂) horth
  rw [r.apply_smul_first, r.apply_smul_second, r.apply_smul_third, r.apply_smul_fourth,
    show (√2)⁻¹ * ((√2)⁻¹ * ((√2)⁻¹ * ((√2)⁻¹ *
        r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l]))) =
      ((√2)⁻¹ : ℝ) ^ 4 *
        r ![f i + s₁ • f j, f k + s₂ • f l, f i + s₁ • f j, f k + s₂ • f l] by ring,
    inv_sqrt_two_pow_four] at hbds
  exact ⟨by linarith [hbds.1], by linarith [hbds.2]⟩

/-- **Berger's mixed-component estimate (localized to `span(f)`).** For an algebraic curvature
tensor `r` and an orthonormal four-frame `f`, if `a ≤ r ![u, v, u, v] ≤ b` on every orthonormal pair
`(u, v)` in `span(range f)`, then `|r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a)`. -/
theorem IsAlgebraicCurvature.abs_apply_orthonormal_le_of_span {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {f : Fin 4 → V} (hf : Orthonormal ℝ f) {a b : ℝ}
    (hsec : ∀ u v : V, u ∈ Submodule.span ℝ (range f) → v ∈ Submodule.span ℝ (range f) →
      Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b) :
    |r ![f 0, f 1, f 2, f 3]| ≤ (2 / 3) * (b - a) := by
  -- Step 1: express `24 * r ![f 0, f 1, f 2, f 3]` as a signed sum of eight sectional numerators
  -- on the pairs `(f 0 ± f 3, f 1 ± f 2)` and `(f 1 ± f 3, f 0 ± f 2)`.
  have hpol := LinearMap.twentyFour_mul_apply_eq_of_cyclic_eq_zero (T := toLinearMap₄ r)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.antisymm_first u v z w)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.antisymm_last u v z w)
    (fun u v z w ↦ by simpa only [toLinearMap₄_apply] using hr.cyclic_eq_zero u v z w)
    (f 0) (f 1) (f 2) (f 3)
  have hflip (x y : V) : r ![x, y, y, x] = -r ![x, y, x, y] := by
    linarith [hr.antisymm_last x y x y]
  simp only [toLinearMap₄_apply, hflip] at hpol
  -- Step 2: bound each of the eight unnormalized sectional numerators in `[4 * a, 4 * b]`.
  have hinj₁ : Function.Injective (![0, 3, 1, 2] : Fin 4 → Fin 4) := by decide
  have hinj₂ : Function.Injective (![1, 3, 0, 2] : Fin 4 → Fin 4) := by decide
  have bp (s₁ s₂ : ℝ) (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) := And.intro
    (apply_add_smul_self_mem_Icc_of_span hf hsec hinj₁ h₁ h₂)
    (apply_add_smul_self_mem_Icc_of_span hf hsec hinj₂ h₁ h₂)
  obtain ⟨b1, b5⟩ := bp 1 1 (.inl rfl) (.inl rfl)
  obtain ⟨b2, b6⟩ := bp 1 (-1) (.inl rfl) (.inr rfl)
  obtain ⟨b3, b7⟩ := bp (-1) 1 (.inr rfl) (.inl rfl)
  obtain ⟨b4, b8⟩ := bp (-1) (-1) (.inr rfl) (.inr rfl)
  simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at b1 b2 b3 b4 b5 b6 b7 b8
  -- Step 3: four terms enter `hpol` with sign `+1` and four with sign `-1`, giving
  -- `± 24 * r ![f 0, f 1, f 2, f 3] ≤ 16 * (b - a)`.
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
  have hcross : -(4 / 3) * (b - a) * |l * m| ≤ -2 * l * m * r ![f 0, f 1, f 2, f 3] := by
    have hprod : |(l * m) * r ![f 0, f 1, f 2, f 3]| ≤ |l * m| * ((2 / 3) * (b - a)) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr.abs_apply_orthonormal_le hf hsec)
        (abs_nonneg _)
    linarith [(abs_le.1 hprod).2]
  have h02 := hsec (f 0) (f 2) (hf.pair (by decide))
  have hdiag : a * (1 + l ^ 2) * (1 + m ^ 2) ≤
      r ![f 0, f 2, f 0, f 2] + l ^ 2 * r ![f 0, f 3, f 0, f 3] +
        m ^ 2 * r ![f 1, f 2, f 1, f 2] + l ^ 2 * m ^ 2 * r ![f 1, f 3, f 1, f 3] := by
    nlinarith [h02.1,
      mul_le_mul_of_nonneg_left (hsec (f 0) (f 3) (hf.pair (by decide))).1 (sq_nonneg l),
      mul_le_mul_of_nonneg_left (hsec (f 1) (f 2) (hf.pair (by decide))).1 (sq_nonneg m),
      mul_le_mul_of_nonneg_left (hsec (f 1) (f 3) (hf.pair (by decide))).1
        (mul_nonneg (sq_nonneg l) (sq_nonneg m))]
  have hamgm : 4 * |l * m| ≤ (1 + l ^ 2) * (1 + m ^ 2) := by
    nlinarith [sq_abs l, sq_abs m, abs_mul l m, sq_nonneg (1 - |l * m|), sq_nonneg (|l| - |m|)]
  have hab : 0 ≤ b - a := by linarith [h02.1, h02.2]
  have hpen := mul_le_mul_of_nonneg_left hamgm (by positivity : 0 ≤ (b - a) / 3)
  have hstep := mul_le_mul_of_nonneg_right (min_le_right a ((4 * a - b) / 3))
    (by positivity : 0 ≤ (1 + l ^ 2) * (1 + m ^ 2))
  rw [pic2Expression_def]; nlinarith

/-- **Weak quarter pinching gives `PIC2`.** If every orthonormal two-frame has sectional curvature
in `[a, b]` with `0 ≤ a` and `b ≤ 4 * a`, then `IsPIC2FourFrame r`. -/
theorem IsAlgebraicCurvature.isPIC2FourFrame_of_weak_quarterPinching {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {a b : ℝ} (ha : 0 ≤ a) (hab : b ≤ 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b) :
    IsPIC2FourFrame r := by
  rw [isPIC2FourFrame_def]; intro f hf l _ m _
  exact (mul_nonneg (mul_nonneg (le_min ha (by linarith)) (by positivity)) (by positivity)).trans
    (hr.le_pic2Expression_of_sectional_mem_Icc hsec hf l m)

/-- **Strict pointwise quarter pinching gives strict `PIC2`** (Brendle–Schoen). If every orthonormal
two-frame of an algebraic curvature tensor `r` has sectional curvature in `[a, b]` with `0 < a` and
`b < 4 * a`, then `0 < pic2Expression r f l m` for every orthonormal four-frame `f` and all real
scalars `l, m`. -/
theorem IsAlgebraicCurvature.pic2Expression_pos_of_strict_quarterPinching {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {a b : ℝ} (ha : 0 < a) (hab : b < 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r ![u, v, u, v] ∧ r ![u, v, u, v] ≤ b)
    {f : Fin 4 → V} (hf : Orthonormal ℝ f) (l m : ℝ) :
    0 < pic2Expression r f l m :=
  (mul_pos (mul_pos (lt_min ha (by linarith)) (by positivity)) (by positivity)).trans_le
    (hr.le_pic2Expression_of_sectional_mem_Icc hsec hf l m)

/-- Strict quarter pinching with constants `0 < a` and `b < 4 * a` puts `r` in
`interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}` (with uniform margin
`min a ((4 * a - b) / 3)`; this coincides with the interior of the `PIC2` cone when
`4 ≤ Module.finrank ℝ V` and holds vacuously when `Module.finrank ℝ V < 4`). -/
theorem mem_interior_isPIC2FourFrame_of_sectional_mem_Icc (r : algebraicCurvatureSubmodule V)
    {a b : ℝ} (ha : 0 < a) (hab : b < 4 * a)
    (hsec : ∀ u v : V, Orthonormal ℝ ![u, v] → a ≤ r.1 ![u, v, u, v] ∧ r.1 ![u, v, u, v] ≤ b) :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  have hmin : 0 < min a ((4 * a - b) / 3) := lt_min ha (by linarith)
  refine mem_interior_isPIC2FourFrame_of_exists_pos_le hmin fun f hf l _ m _ ↦ ?_
  refine (le_mul_of_one_le_right hmin.le
    (show 1 ≤ (1 + l ^ 2) * (1 + m ^ 2) by nlinarith [sq_nonneg l, sq_nonneg m])).trans ?_
  simpa only [mul_assoc] using
    (mem_algebraicCurvatureSubmodule.1 r.2).le_pic2Expression_of_sectional_mem_Icc hsec hf l m

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
  · simp [hr.apply_self_eq_zero_of_not_linearIndependent huv]

end InnerProductSpace

/-! ### Finite-dimensional quarter pinching and Fubini–Study sharpness -/

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- In dimension at least two, pointwise positivity of `r ![u, v, u, v] / det(Gram(u, v))` on
linearly independent pairs implies `0 < sectionalMin r`. -/
theorem sectionalMin_pos_of_quarterPinched (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V)
    (hpos : ∀ u v : V, LinearIndependent ℝ ![u, v] →
      0 < r ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det) :
    0 < sectionalMin r := by
  obtain ⟨u₀, v₀, h₀, hmin⟩ := exists_orthonormal_eq_sectionalMin hn r
  have hp₀ := hpos u₀ v₀ h₀.linearIndependent
  rwa [Matrix.gram_eq_one_iff_orthonormal.2 h₀, Matrix.det_one, div_one, hmin] at hp₀

/-- In dimension at least two, unquantified pointwise strict quarter pinching on linearly
independent pairs implies `sectionalMax r < 4 * sectionalMin r`. -/
theorem sectionalMax_lt_four_mul_sectionalMin_of_quarterPinched
    (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V)
    (hpinch : ∀ u v u' v' : V, LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
      r ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det <
        4 * (r ![u', v', u', v'] / (Matrix.gram ℝ ![u', v']).det)) :
    sectionalMax r < 4 * sectionalMin r := by
  obtain ⟨u₀, v₀, h₀, hmin⟩ := exists_orthonormal_eq_sectionalMin hn r
  obtain ⟨u₁, v₁, h₁, hmax⟩ := exists_orthonormal_eq_sectionalMax hn r
  have hp := hpinch u₁ v₁ u₀ v₀ h₁.linearIndependent h₀.linearIndependent
  rwa [Matrix.gram_eq_one_iff_orthonormal.2 h₀, Matrix.gram_eq_one_iff_orthonormal.2 h₁,
    Matrix.det_one, div_one, div_one, hmin, hmax] at hp

/-- Unquantified pointwise strict quarter pinching on all linearly independent pairs places `r` in
`interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}`. When
`4 ≤ Module.finrank ℝ V`, this is membership in the interior of the `PIC2` cone; when
`Module.finrank ℝ V < 4`, no orthonormal four-frame exists in `V` and the target set (together with
its interior) is all of `algebraicCurvatureSubmodule V`. -/
theorem mem_interior_isPIC2FourFrame_of_quarterPinched (r : algebraicCurvatureSubmodule V)
    (hpinch : ∀ u v u' v' : V, LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
      0 < r.1 ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det ∧
        r.1 ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det <
          4 * (r.1 ![u', v', u', v'] / (Matrix.gram ℝ ![u', v']).det)) :
    r ∈ interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  by_cases hn4 : 4 ≤ Module.finrank ℝ V
  · have hn2 : 2 ≤ Module.finrank ℝ V := by omega
    have hpos := sectionalMin_pos_of_quarterPinched hn2 r.1 fun u v huv ↦
      (hpinch u v u v huv huv).1
    have hlt := sectionalMax_lt_four_mul_sectionalMin_of_quarterPinched hn2 r.1
      fun u v u' v' huv huv' ↦ (hpinch u v u' v' huv huv').2
    exact mem_interior_isPIC2FourFrame_of_sectional_mem_Icc r hpos hlt fun _ _ huv ↦
      ⟨sectionalMin_le_of_orthonormal r.1 huv, le_sectionalMax_of_orthonormal r.1 huv⟩
  · rw [mem_interior_isPIC2FourFrame_iff_forall_pos]
    intro f hf
    have hcard := hf.linearIndependent.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard; omega

/-! ### Constant holomorphic sectional curvature (Fubini–Study) and sharpness -/

/-- The Fubini–Study four-tensor attached to an almost complex structure `J` on `V`, defined by
`r(u, v, z, w) = ⟪u, z⟫ ⟪v, w⟫ - ⟪u, w⟫ ⟪v, z⟫ + ⟪J u, z⟫ ⟪J v, w⟫`
`- ⟪J u, w⟫ ⟪J v, z⟫ + 2 ⟪J u, v⟫ ⟪J z, w⟫`. When `J` preserves the inner product
(`∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ`), `fubiniStudy J` is an algebraic curvature tensor of constant
holomorphic sectional curvature `4` (with sectional curvatures in `[1, 4]`). -/
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

/-- For an almost complex structure `J` preserving the inner product, `fubiniStudy J` is an
algebraic curvature tensor. -/
theorem isAlgebraicCurvature_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) :
    IsAlgebraicCurvature (fubiniStudy J) := by
  have hω (x y : V) : ⟪J x, y⟫_ℝ = -⟪J y, x⟫_ℝ := by
    simpa only [innerₗ_apply_apply, real_inner_comm x (J y)] using
      J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hJ x y
  refine ⟨fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_, fun u v z w ↦ ?_⟩ <;>
    simp only [fubiniStudy_apply]
  · rw [hω v u]; ring
  · rw [hω w z]; ring
  · rw [real_inner_comm u z, real_inner_comm v w, real_inner_comm v z, real_inner_comm u w,
      hω z u, hω w v, hω z v, hω w u]; ring
  · rw [real_inner_comm u z, real_inner_comm u v, real_inner_comm v z, hω v u, hω z u, hω z v]
    ring

/-- On a pair `(u, v)` with orthogonal `J`,
`fubiniStudy J ![u, v, u, v] = ‖u‖² ‖v‖² - ⟪u, v⟫² + 3 ⟪J u, v⟫²`. -/
theorem fubiniStudy_apply_self {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) (u v : V) :
    fubiniStudy J ![u, v, u, v] = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 + 3 * ⟪J u, v⟫_ℝ ^ 2 := by
  have hω : ⟪J v, u⟫_ℝ = -⟪J u, v⟫_ℝ := by
    simpa only [innerₗ_apply_apply, real_inner_comm v (J u)] using
      J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hJ v u
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
  refine ⟨by simp [hu, J.norm_apply hJ, h0], ?_⟩
  rw [fubiniStudy_apply_self hJ, hu, J.norm_apply hJ, h0, real_inner_self_eq_norm_sq,
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

/-- The Fubini–Study curvature tensor of an orthogonal almost complex structure lies in the `PIC2`
cone (`1 ≤ K ≤ 4 = 4 * 1`). -/
theorem isPIC2FourFrame_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) :
    IsPIC2FourFrame (fubiniStudy J) :=
  (isAlgebraicCurvature_fubiniStudy hJ).isPIC2FourFrame_of_weak_quarterPinching
    zero_le_one (by norm_num) (fun _ _ huv ↦ fubiniStudy_sectional_mem_Icc hJ huv)

/-- **Weak quarter pinching does not imply `PIC2` interior.** On a real inner product space of
dimension at least four equipped with an orthogonal almost complex structure `J`, `fubiniStudy J`
does not lie in `interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1}` (see
`fubiniStudy_sectional_mem_Icc` and `isPIC2FourFrame_fubiniStudy` for its `[1, 4]` sectional bounds
and `IsPIC2FourFrame` membership). -/
theorem notMem_interior_isPIC2FourFrame_fubiniStudy {J : AlmostComplexStructure V}
    (hJ : ∀ u v, ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ) (hn : 4 ≤ Module.finrank ℝ V) :
    (⟨fubiniStudy J, mem_algebraicCurvatureSubmodule.2 (isAlgebraicCurvature_fubiniStudy hJ)⟩ :
       algebraicCurvatureSubmodule V) ∉
      interior {q : algebraicCurvatureSubmodule V | IsPIC2FourFrame q.1} := by
  obtain ⟨k, hk⟩ := J.even_finrank_real
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
not in the interior of the `PIC2` cone. -/
theorem exists_isPIC2FourFrame_notMem_interior_fin_four :
    ∃ r : algebraicCurvatureSubmodule (EuclideanSpace ℝ (Fin 4)),
      IsPIC2FourFrame r.1 ∧
        (∀ u v, Orthonormal ℝ ![u, v] → 1 ≤ r.1 ![u, v, u, v] ∧ r.1 ![u, v, u, v] ≤ 4) ∧
        r ∉ interior
          {q : algebraicCurvatureSubmodule (EuclideanSpace ℝ (Fin 4)) | IsPIC2FourFrame q.1} := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by simp
  obtain ⟨J, hJnorm⟩ := AlmostComplexStructure.exists_forall_norm_apply_eq
    (V := EuclideanSpace ℝ (Fin 4)) ⟨2, by omega⟩
  have hJ : ∀ u v : EuclideanSpace ℝ (Fin 4), ⟪J u, J v⟫_ℝ = ⟪u, v⟫_ℝ :=
    ({ J.toLinearMap with norm_map' := hJnorm } : _ →ₗᵢ[ℝ] _).inner_map_map
  exact ⟨⟨fubiniStudy J, mem_algebraicCurvatureSubmodule.2 (isAlgebraicCurvature_fubiniStudy hJ)⟩,
    isPIC2FourFrame_fubiniStudy hJ, fun _ _ huv ↦ fubiniStudy_sectional_mem_Icc hJ huv,
    notMem_interior_isPIC2FourFrame_fubiniStudy hJ (by omega)⟩

end FiniteDimensional

end TauCeti.FourTensor
