/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ConfigurationSpace.EulerExponent
public import TauCeti.RingTheory.Polynomial.Monic.EulerProduct
import TauCeti.RingTheory.PowerSeries.Binomial
import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# The squarefree Euler product in terms of signed Euler exponents

For a finite field of cardinality `q`, the series weighting monic squarefree polynomials
by `(-(-1)^n N)^k`, where `k` counts irreducible factors, equals the coefficientwise product
of `(1 - q X^r)^(-e_r(n,N))`. In each degree this gives a polynomial in the field cardinality.
The product is the arithmetic input to the configuration space calculation in Lemma 7.4 of
T. Browning and W. Sawin, *A geometric version of the circle method*, Ann. of Math. 191 (2020).
-/

public section

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti

/-- For a field of cardinality `q`, the generating series with weight `-(-1)^n N`
per irreducible factor is the coefficientwise product of `(1 - q X^r)^(-e_r(n,N))`. -/
theorem hasProd_eulerExponent_weightedSquarefreeSeries
    (F : Type*) [Field F] [DecidableEq F] [Finite F] (n N : ℕ) :
    HasProd (fun r : ℕ+ ↦ expand r r.ne_zero
      (rescale (Nat.card F : ℤ) ↑(invOneSubPow ℤ 1 ^ eulerExponent n N r)))
      (weightedSquarefreeSeries F (-((-1 : ℤ) ^ n * N))) := by
  let P := {p : Polynomial F // p.Monic ∧ Irreducible p}
  let d : P → ℕ+ := fun p ↦ ⟨_, p.property.2.natDegree_pos⟩
  let a : P × ℕ+ → ℕ+ := fun p ↦ d p.1 * p.2
  let f : ℕ+ → ℤ⟦X⟧ := fun r ↦ ↑(invOneSubPow ℤ 1 ^ eulerExponent n N r)
  have hfinite (m : ℕ) : {p | (a p : ℕ) ≤ m}.Finite := by
    refine ((finite_monicIrreducible_natDegree_le F m).prod
      ((Set.finite_Iic m).preimage Subtype.val_injective.injOn)).subset ?_
    intro p h
    rcases p with ⟨p, r⟩
    have hmul : (d p : ℕ) * (r : ℕ) ≤ m := h
    exact ⟨(Nat.le_mul_of_pos_right _ (PNat.pos r)).trans hmul,
      (Nat.le_mul_of_pos_left _ (d p).pos).trans hmul⟩
  have hdouble := multipliable_expand (m := a) hfinite (f := fun p ↦ f p.2)
    (fun p ↦ constantCoeff_invOneSubPow_zpow (R := ℤ) _)
  have hcont (r : ℕ+) : Continuous (fun g : ℤ⟦X⟧ ↦ expand r r.ne_zero g) := by
    simpa only [expand_apply, subst_def] using
      (MvPowerSeries.continuous_subst (R := ℤ)
        (PowerSeries.HasSubst.X_pow (R := ℤ) r.ne_zero).const)
  -- Grouping by the prime gives the signed Euler factorization at its degree.
  have hrow (p : P) :
      HasProd (fun r : ℕ+ ↦ expand (a (p, r)) (a (p, r)).ne_zero (f r))
        (1 + C (-((-1 : ℤ) ^ n * N)) * X ^ (p : Polynomial F).natDegree) := by
    have h := (hasProd_eulerExponent n N).map (expand (d p) (d p).ne_zero) (hcont (d p))
    have he (r : ℕ+) :
        expand (a (p, r)) (a (p, r)).ne_zero (f r) =
          expand (d p) (d p).ne_zero (expand r r.ne_zero (f r)) :=
      expand_mul (d p) (d p).ne_zero r r.ne_zero (f r)
    have hvalue : expand (d p) (d p).ne_zero (1 - C ((-1) ^ n * (N : ℤ)) * X) =
        1 + C (-((-1 : ℤ) ^ n * N)) * X ^ (p : Polynomial F).natDegree := by
      rw [map_sub, map_one, map_mul, expand_C, expand_X, map_neg, neg_mul, sub_eq_add_neg]
      rfl
    exact hvalue ▸ h.congr_fun he
  have hweighted := hasProd_weightedSquarefreeSeries F (-((-1 : ℤ) ^ n * N))
  have hmain := (hdouble.hasProd.prod_fiberwise hrow).unique hweighted
  -- Grouping by the second index gives the ordinary Euler product at `X^r`.
  have hcol (r : ℕ+) :
      HasProd (fun p : P ↦ expand (a (p, r)) (a (p, r)).ne_zero (f r))
        (expand r r.ne_zero (rescale (Nat.card F : ℤ) (f r))) := by
    have h := (hasProd_expand_invOneSubPow_monicIrreducible (F := F) (eulerExponent n N r)).map
      (expand r r.ne_zero) (hcont r)
    have he (p : P) :
        expand (a (p, r)) (a (p, r)).ne_zero (f r) =
          expand r r.ne_zero (expand (d p) (d p).ne_zero (f r)) := by
      calc
        _ = expand (r * d p : ℕ+) (r * d p).ne_zero (f r) :=
          congrArg (fun s : ℕ+ ↦ expand s s.ne_zero (f r)) (mul_comm (d p) r)
        _ = _ := expand_mul r r.ne_zero (d p) (d p).ne_zero (f r)
    exact h.congr_fun he
  have hswapProd := (Equiv.prodComm ℕ+ P).hasProd_iff.mpr hdouble.hasProd
  rw [← hmain]
  exact hswapProd.prod_fiberwise hcol

/-- The coefficient of degree `m` in the squarefree Euler product with indeterminate field
cardinality `Q`. This is a polynomial in `Q` over the integers. -/
noncomputable def weightedSquarefreeCountPolynomial (n N m : ℕ) : Polynomial ℤ :=
  coeff m (∏ k ∈ range m, expand (k + 1) k.succ_ne_zero
    (rescale Polynomial.X (PowerSeries.map (Int.castRingHom (Polynomial ℤ))
      ↑(invOneSubPow ℤ 1 ^ eulerExponent n N (k + 1)))))

/-- The degree-`m` count polynomial uses the Euler factors of indices `1` through `m`. -/
theorem weightedSquarefreeCountPolynomial_eq_coeff_prod (n N m : ℕ) :
    weightedSquarefreeCountPolynomial n N m =
      coeff m (∏ k ∈ range m, expand (k + 1) k.succ_ne_zero
        (rescale Polynomial.X (PowerSeries.map (Int.castRingHom (Polynomial ℤ))
          ↑(invOneSubPow ℤ 1 ^ eulerExponent n N (k + 1))))) :=
  (rfl)

/-- In degree zero the squarefree count polynomial is `1`. -/
@[simp]
theorem weightedSquarefreeCountPolynomial_zero (n N : ℕ) :
    weightedSquarefreeCountPolynomial n N 0 = 1 := by
  simp [weightedSquarefreeCountPolynomial_eq_coeff_prod]

/-- Evaluating the squarefree count polynomial at the cardinality of a finite field gives
the weighted count of its monic squarefree polynomials of that degree. -/
theorem eval_weightedSquarefreeCountPolynomial
    (F : Type*) [Field F] [DecidableEq F] [Finite F] (n N m : ℕ) :
    (weightedSquarefreeCountPolynomial n N m).eval (Nat.card F : ℤ) =
      coeff m (weightedSquarefreeSeries F (-((-1 : ℤ) ^ n * N))) := by
  let q : ℤ := Nat.card F
  let ev : Polynomial ℤ →+* ℤ := Polynomial.evalRingHom q
  let f : ℕ → ℤ⟦X⟧ := fun k ↦
    rescale q ↑(invOneSubPow ℤ 1 ^ eulerExponent n N (k + 1))
  let degree : ℕ → ℕ+ := fun k ↦ ⟨k + 1, k.succ_pos⟩
  have hprod : HasProd (fun k : ℕ ↦ expand (degree k) (degree k).ne_zero (f k))
      (weightedSquarefreeSeries F (-((-1 : ℤ) ^ n * N))) :=
    Equiv.pnatEquivNat.symm.hasProd_iff.mpr
      (hasProd_eulerExponent_weightedSquarefreeSeries F n N)
  have hfinite (d : ℕ) : {k | (degree k : ℕ) ≤ d}.Finite :=
    (Set.finite_Iic d).subset fun _ hk ↦ Nat.le_of_succ_le hk
  have hconst (k : ℕ) : constantCoeff (f k) = 1 := by
    simp [f, constantCoeff_invOneSubPow_zpow]
  rw [← hprod.tprod_eq, coeff_tprod_expand (m := degree) hfinite hconst
    (s := range m) (fun k hk ↦ mem_range.mpr (Nat.lt_of_succ_le hk))]
  have hev : ev.comp (Int.castRingHom (Polynomial ℤ)) = RingHom.id ℤ := Subsingleton.elim _ _
  have hmap (k : ℕ) :
      PowerSeries.map ev (expand (k + 1) k.succ_ne_zero
        (rescale Polynomial.X (PowerSeries.map (Int.castRingHom (Polynomial ℤ))
          ↑(invOneSubPow ℤ 1 ^ eulerExponent n N (k + 1))))) =
        expand (degree k) (degree k).ne_zero (f k) := by
    rw [map_expand, ← rescale_map,
      ← RingHom.comp_apply (PowerSeries.map ev)
        (PowerSeries.map (Int.castRingHom (Polynomial ℤ))), ← PowerSeries.map_comp, hev,
      PowerSeries.map_id]
    simp [ev, f, degree]
  have h_eval (p : Polynomial ℤ) : p.eval (Nat.card F : ℤ) = ev p := rfl
  rw [h_eval, weightedSquarefreeCountPolynomial_eq_coeff_prod, ← coeff_map, map_prod]
  simp only [hmap]

end TauCeti
