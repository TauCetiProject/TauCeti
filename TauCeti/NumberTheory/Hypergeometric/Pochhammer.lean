/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Hypergeometric.Dictionary
public import TauCeti.NumberTheory.Hypergeometric.GammaVector
public import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# The factorial ratio of a cyclotomic datum

For parameters in `(0, 1]`, the quotient of rising factorials giving the degree-`n`
hypergeometric series coefficient equals `M⁻ⁿ ∏ₘ ((mn)!)^γ(m)`. The normalization `M`
comes from clearing the denominator in each grid of fractions `1/m, …, m/m`.
Möbius inversion on divisors separates these grids into primitive parameter classes.

## References

* F. Beukers, H. Cohen and A. Mellit, *Finite hypergeometric functions*,
  Pure Appl. Math. Q. 11 (2015), §1.
-/

public section

namespace TauCeti.Hypergeometric.CyclotomicData

/-- The Pochhammer quotient of a cyclotomic datum is the factorial ratio
with exponents `γ(m)`, scaled by `M⁻ⁿ` (Beukers–Cohen–Mellit, §1). -/
theorem prod_ascPochhammer_div_eq_mul_prod_factorial (D : CyclotomicData) (n : ℕ) :
    (D.toParameters.α.map fun a ↦ (ascPochhammer ℚ n).eval (rep a)).prod /
        (D.toParameters.β.map fun b ↦ (ascPochhammer ℚ n).eval (rep b)).prod =
      D.gammaScale ^ (-(n : ℤ)) *
        ∏ m ∈ D.gammaSupport, ((m * n).factorial : ℚ) ^ D.gamma m := by
  let w (x : AddCircle (1 : ℚ)) := (ascPochhammer ℚ n).eval (rep x)
  let f (a : ℕ) := ((primitiveClasses {a}).map w).prod
  have hprod (S : Multiset ℕ) : ((primitiveClasses S).map w).prod = (S.map f).prod := by
    induction S using Multiset.induction_on with
    | empty => simp
    | cons a S ih => simp [primitiveClasses_cons, Multiset.map_add, ih, f]
  have hf (a : ℕ) : 0 < f a := Multiset.prod_pos fun q hq ↦ by
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.1 hq
    exact ascPochhammer_pos n _ (rep_pos x)
  have hgrid (m : ℕ) :
      ∏ d ∈ m.divisors, f d = ((m * n).factorial : ℚ) / (m : ℚ) ^ (m * n) := by
    rw [Finset.prod_eq_multiset_prod, ← hprod]
    have heval := congrArg (fun S : Multiset ℚ ↦ (S.map (ascPochhammer ℚ n).eval).prod)
      (map_rep_primitiveClasses_divisors m)
    simp only [Multiset.map_map, Function.comp_def] at heval
    exact heval.trans (by simpa [mul_comm n m, Finset.prod_eq_multiset_prod] using
      prod_ascPochhammer_eval_div (1 : ℚ) m n)
  -- Positivity lets us apply the gamma product formula in the group of rational units.
  let u (a : ℕ) : ℚˣ := Units.mk0 (f a) (hf a).ne'
  have hγ := congrArg (Units.val : ℚˣ → ℚ) (D.prod_map_div_prod_map_eq_prod_zpow_gamma u)
  simp only [Units.val_div_eq_div_val, Units.coe_prod, Units.val_zpow_eq_zpow_val] at hγ
  rw [← Units.coeHom_apply, ← Units.coeHom_apply (D.B.map u).prod,
    map_multiset_prod, map_multiset_prod] at hγ
  simp only [Multiset.map_map, Function.comp_def, Units.coeHom_apply, u, Units.val_mk0] at hγ
  rw [toParameters_α, toParameters_β, hprod, hprod, hγ]
  simp_rw [hgrid, div_zpow, Finset.prod_div_distrib]
  rw [gammaScale_def, ← Finset.prod_zpow, div_eq_inv_mul, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun m _ ↦ ?_
  rw [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_mul]
  push_cast
  ring_nf

end TauCeti.Hypergeometric.CyclotomicData
