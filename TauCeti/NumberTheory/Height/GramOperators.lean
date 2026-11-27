/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.ChainRatio
public import TauCeti.NumberTheory.Height.FamilyOverPairs

/-!
# Heights of Gram determinant ratios

When the Gram operators of a reference map and a family of comparison maps factor into
ordered products, the height of the Gram determinant ratio is bounded by the sum of the
heights of the individual determinant ratios and the dimension-weighted height of the scalar
ratio. The comparison maps may have different codomains. In the theta-lift application the
factors are Rallis operators, and the individual Gram determinants are computed on other
spaces with the same determinant factors up to a common scale.

The height budget is that of `New.Data.heightLe_chainDeterminant_one_div` in
`grh/src/New/Determinant/Twist/LongForms.lean` of lsernau/grh-lean (revision `72fead1`).
The determinant comparison uses `LinearMap.normDet_sq_div_eq_pow_mul_prod`.
-/

public section

namespace TauCeti.PrimePadicIso

/-- Bound the height of the ratio of squared norm determinants, with the reference map `f₀`
in the numerator. The Gram operators are scalar multiples of the ordered products of
`A₀` and `A`. The single-factor determinants `Z₀ j` and `Z j ι` include the same nonzero
normalization `a j`, which cancels from their quotient. The normalizations and the scalar
norms are real numbers; the ratios in the height bounds are embedded in `ℂ`. No
injectivity assumptions are needed for the inequality with totalized division. -/
theorem HeightLe.normDet_sq_div_of_inner_map_map_eq
    {B : ℝ} {c₀ : ℂ} {c : PrimePadicIso → ℂ}
    (hscalar : HeightLe (fun ι ↦ (‖c₀ / c ι‖ : ℂ)) B)
    {U V₀ : Type*} {V : PrimePadicIso → Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀]
    [∀ ι, NormedAddCommGroup (V ι)] [∀ ι, InnerProductSpace ℂ (V ι)]
    (f₀ : U →ₗ[ℂ] V₀) (f : ∀ ι, U →ₗ[ℂ] V ι) {m : ℕ}
    {A₀ : Fin m → Module.End ℂ U} {A : PrimePadicIso → Fin m → Module.End ℂ U}
    {a Z₀ : Fin m → ℝ} {Z : Fin m → PrimePadicIso → ℝ}
    (hf₀ : ∀ x y, inner ℂ (f₀ x) (f₀ y) = c₀ * inner ℂ x ((List.ofFn A₀).prod y))
    (hf : ∀ ι x y, inner ℂ (f ι x) (f ι y) = c ι * inner ℂ x ((List.ofFn (A ι)).prod y))
    (ha : ∀ j, a j ≠ 0)
    (hZ₀ : ∀ j, Z₀ j = a j * ‖(A₀ j).det‖)
    (hZ : ∀ j ι, Z j ι = a j * ‖(A ι j).det‖)
    {C : Fin m → ℝ}
    (hfactor : ∀ j, HeightLe (fun ι ↦ ((Z₀ j / Z j ι : ℝ) : ℂ)) (C j)) :
    HeightLe (fun ι ↦ ((f₀.normDet ^ 2 / (f ι).normDet ^ 2 : ℝ) : ℂ))
      ((Module.finrank ℂ U : ℝ) * B + ∑ j, C j) := by
  have hratio (ι : PrimePadicIso) :
      f₀.normDet ^ 2 / (f ι).normDet ^ 2 =
        ‖c₀ / c ι‖ ^ Module.finrank ℂ U * ∏ j, Z₀ j / Z j ι := by
    rw [Fin.prod_univ_def]
    refine f₀.normDet_sq_div_eq_pow_mul_prod (f ι) (List.finRange m) ?_ ?_
      (fun j _ ↦ ha j) (fun j _ ↦ hZ₀ j) (fun j _ ↦ hZ j ι)
    · simpa only [List.ofFn_eq_map] using hf₀
    · simpa only [List.ofFn_eq_map] using hf ι
  have hprod := HeightLe.prod (s := Finset.univ) (fun j _ ↦ hfactor j)
  convert (hscalar.pow (Module.finrank ℂ U)).mul hprod using 1
  funext ι
  rw [hratio]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod, Pi.mul_apply,
    Pi.pow_apply, Finset.prod_apply]

end TauCeti.PrimePadicIso
