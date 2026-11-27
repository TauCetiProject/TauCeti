/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo.Nondegenerate
public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Weight

/-!
# Examples: four-twist weights of square-zero tori and the labels of orbit tori

In Taubes's count of embedded pseudoholomorphic curves in a symplectic four-manifold, an embedded
square-zero torus with label `(σ, i)` enters with multiplicity `m` weighted by the `m`-th
coefficient of the local series `f_(σ, i)` (`TauCeti.torusWeightSeries`), and a family of
pairwise disjoint tori on the homology ray of a class `A₀` is counted by the coefficients of the
product of their local series, each evaluated at `t ^ m` for a torus of class `m A₀`
(`TauCeti.configurationCount_eq_coeff_rayTorusWeightSeries`). This file tests these definitions
on explicit families, in the integral homology `H = ℤ` of a ray with `A₀ = 1`, where the count
of a finite family of tori is a coefficient of the product of their substituted local series
(`configurationCount_univ_eq_coeff_prod_expand`).

* **The local series.** The first coefficients of `f_(+,2)`, `f_(+,3)` and `f_(-,3)` are
  `1, 1, -1, -1, 1, 1`, `1, 1, -2, -2, 2, 2` and `1, -1, 3, -3, 5, -5`
  (`coeff_torusWeightSeries_true_two_range` and its companions). A torus of label `(+, 0)`, with
  `f_(+,0) = 1 / (1 - t)`, has weight `1` with every multiplicity (`torusWeight_true_zero`): the
  weight is a power-series coefficient, not the coefficient `1 / m` of the orbit logarithm, which
  is not an integer at `m = 2`.
* **One torus.** The count of a single torus `T` of class `A₀` in the class `j A₀` is its weight
  `w_(σ, i)(j)` (`configurationCount_unit`). A torus of label `(-, 0)` has series `1 - t`, so it
  contributes `-1` in its own class and nothing in its multiples
  (`configurationCount_unit_false_zero`), and a torus of label `(+, 1)`, with series `1 + t`,
  contributes `1` in its own class and nothing in its multiples
  (`configurationCount_unit_true_one`).
* **Two disjoint tori of label `(+, 0)`.** Their count in the class `k A₀` is `k + 1`
  (`configurationCount_two_tori`), the coefficient of `t ^ k` in `f_(+,0) ^ 2 = 1 / (1 - t) ^ 2`.
  This is the value `k + 1` of McDuff's Lemma 5.1 for the two section tori of `S² × T²`. In the
  class `2 A₀` the three distributions `(2, 0)`, `(1, 1)`, `(0, 2)` each have weight one, so the
  count is `3` (`configurationCount_two_tori_two`), while adding the two local series instead of
  multiplying them would give `2` (`coeff_two_torusWeightSeries_true_zero_add`).
* **A ray with a torus in a multiple class.** A torus `T` of class `A₀` and label `(+, 0)`
  together with a torus `T'` of class `2 A₀` and label `(+, 1)` have the ray series
  `f_(+,0)(t) f_(+,1)(t ^ 2) = (1 + t ^ 2) / (1 - t) = 1 + t + 2 t ^ 2 + 2 t ^ 3 + ⋯`, so the
  count is `1` in the classes `0` and `A₀` and `2` in every class `j A₀` with `j ≥ 2`
  (`configurationCount_ray`). In the class `A₀` only `T` contributes; without the substitution
  `t ↦ t ^ 2` the product `f_(+,0)(t) f_(+,1)(t)` has coefficient `2` in degree one
  (`coeff_one_torusWeightSeries_true_zero_mul_true_one`) and would credit `T'` to the class `A₀`.
* **Orbit tori.** For the orbit torus of a periodic orbit of an area-preserving surface map, with
  linearized return map `P` of determinant one, the label read off from the signs of
  `det (1 - P)` and `det (1 + P)` makes the local series satisfy
  `t f' = f ∑_{k ≥ 1} sgn det (1 - P ^ k) t ^ k`
  (`TauCeti.X_mul_derivative_torusWeightSeries_of_det_eq_one`). For the rotation
  `R_θ = Matrix.SpecialLinearGroup.rotation θ` through an angle `θ ∉ 2πℚ`, an elliptic return
  map all of whose iterates are nondegenerate, `det (1 - R_θ ^ k) = 2 - 2 cos (k θ) > 0` for
  every `k ≥ 1` (`Matrix.SpecialLinearGroup.det_one_sub_rotation_pow`,
  `Matrix.SpecialLinearGroup.det_one_sub_rotation_pow_pos`). So the signs sum to `t / (1 - t)`
  (`mk_sign_det_one_sub_rotation_pow`) and the label is `(+, 0)`, with series `1 / (1 - t)`
  (`torusWeightSeries_label_rotation`). For a negative hyperbolic `P` (`trace P < -2`) the sign
  of `det (1 - P ^ k)` is `(-1) ^ (k + 1)` (`Matrix.sign_det_one_sub_pow_of_trace_lt_neg_two`),
  the signs sum to `t / (1 + t)` (`TauCeti.mk_sign_det_one_sub_pow_of_trace_lt_neg_two`) and the
  label is `(+, 1)`, with series `1 + t` (`torusWeightSeries_label_of_trace_lt_neg_two`).

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, in *Gauge theory and
  symplectic geometry*, NATO ASI Series C 488, Kluwer, 1997, Lemma 5.1 and §5.2.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127--158, Lemma 3.2.
-/

public section

noncomputable section

open PowerSeries Matrix
open Matrix.SpecialLinearGroup (rotation det_one_add_rotation det_one_sub_rotation_pow_pos)
open scoped Real MatrixGroups

namespace TauCeti.Examples.TorusWeight

open TauCeti

/-! ### The local series -/

/-- The first coefficients of `f_(+,2) = (1 + t) / (1 + t ^ 2)` are `1, 1, -1, -1, 1, 1`. -/
theorem coeff_torusWeightSeries_true_two_range :
    (List.range 6).map (fun m ↦ coeff m (torusWeightSeries true 2)) = [1, 1, -1, -1, 1, 1] := by
  simp [List.range_succ]

/-- The first coefficients of `f_(+,3) = (1 + t) (1 - t ^ 2) / (1 + t ^ 2)` are
`1, 1, -2, -2, 2, 2`. -/
theorem coeff_torusWeightSeries_true_three_range :
    (List.range 6).map (fun m ↦ coeff m (torusWeightSeries true 3)) = [1, 1, -2, -2, 2, 2] := by
  simp [List.range_succ]

/-- The first coefficients of `f_(-,3) = (1 + t ^ 2) / ((1 + t) (1 - t ^ 2))` are
`1, -1, 3, -3, 5, -5`. -/
theorem coeff_torusWeightSeries_false_three_range :
    (List.range 6).map (fun m ↦ coeff m (torusWeightSeries false 3)) =
      [1, -1, 3, -3, 5, -5] := by
  simp [List.range_succ]

/-- A torus of label `(+, 0)` has weight `1` with every multiplicity, since
`f_(+,0) = 1 / (1 - t) = ∑ t ^ m`. -/
theorem torusWeight_true_zero (m : ℕ) : torusWeight true 0 m = 1 := by
  simp [torusWeightSeries_true_zero]

/-! ### Weighted counts on a ray

The tori lie on the ray of the class `A₀ = 1` of `H = ℤ`, and two distinct tori are compatible,
that is disjoint. -/

/-- **A finite family of tori on the ray.** For pairwise compatible tori indexed by a finite
type, the torus `c` having class `m c • A₀` and label `(σ c, i c)`, the count in the class `j A₀`
is the coefficient of `t ^ j` in `∏_c f_(σ c, i c)(t ^ m c)`. -/
theorem configurationCount_univ_eq_coeff_prod_expand {ι : Type*} [Fintype ι] {r : ι → ι → Prop}
    (hr : (Set.univ : Set ι).Pairwise r) (m : ι → ℕ+) (σ : ι → Bool) (i : ι → Fin 4) (j : ℕ) :
    configurationCount r (fun c ↦ ((m c : ℕ) : ℤ)) (fun c ↦ torusWeight (σ c) (i c)) Set.univ
        (j : ℤ) =
      coeff j (∏ c, expand (m c) (m c).ne_zero (torusWeightSeries (σ c) (i c))) := by
  rw [← nsmul_one, configurationCount_eq_coeff_rayTorusWeightSeries hr
    (fun _ _ ↦ (nsmul_one _).symm) (fun a b h ↦ by simpa using h) (fun _ _ ↦ rfl)
    (s := Finset.univ) (by simp) (fun _ _ _ ↦ Finset.mem_univ _), rayTorusWeightSeries_def]

/-- **One torus.** The count of a single torus of class `A₀` and label `(σ, i)` in the class
`j A₀` is its weight `w_(σ, i)(j)`. -/
theorem configurationCount_unit (σ : Bool) (i : Fin 4) (j : ℕ) :
    configurationCount (fun _ _ : Unit ↦ True) (fun _ ↦ (1 : ℤ)) (fun _ ↦ torusWeight σ i)
      Set.univ (j : ℤ) = torusWeight σ i j := by
  simpa [torusWeight_def] using configurationCount_univ_eq_coeff_prod_expand
    (r := fun _ _ : Unit ↦ True) (fun _ _ _ _ _ ↦ trivial) (fun _ ↦ 1) (fun _ ↦ σ) (fun _ ↦ i) j

/-- A torus of label `(-, 0)`, with series `f_(-,0) = 1 - t`, contributes `-1` in its own class
and nothing in its multiples. -/
theorem configurationCount_unit_false_zero (j : ℕ) :
    configurationCount (fun _ _ : Unit ↦ True) (fun _ ↦ (1 : ℤ)) (fun _ ↦ torusWeight false 0)
      Set.univ (j : ℤ) = if j = 0 then 1 else if j = 1 then -1 else 0 := by
  rw [configurationCount_unit, torusWeight_def, torusWeightSeries_false_zero]
  rcases j with _ | _ | j <;> simp [coeff_X]

/-- A torus of label `(+, 1)`, with series `f_(+,1) = 1 + t`, contributes `1` in its own class
and nothing in its multiples. -/
theorem configurationCount_unit_true_one (j : ℕ) :
    configurationCount (fun _ _ : Unit ↦ True) (fun _ ↦ (1 : ℤ)) (fun _ ↦ torusWeight true 1)
      Set.univ (j : ℤ) = if j ≤ 1 then 1 else 0 := by
  rw [configurationCount_unit, torusWeight_def, torusWeightSeries_true_one]
  rcases j with _ | _ | j <;> simp [coeff_X]

/-- **Two disjoint tori of label `(+, 0)`.** Two disjoint tori of class `A₀` and label `(+, 0)`
have count `k + 1` in the class `k A₀`: the coefficient of `t ^ k` in
`f_(+,0) ^ 2 = 1 / (1 - t) ^ 2`, one for each distribution `(a, k - a)` of the multiplicity. -/
theorem configurationCount_two_tori (k : ℕ) :
    configurationCount (fun c d : Fin 2 ↦ c ≠ d) (fun _ ↦ (1 : ℤ)) (fun _ ↦ torusWeight true 0)
      Set.univ (k : ℤ) = k + 1 := by
  have h := configurationCount_univ_eq_coeff_prod_expand (r := fun c d : Fin 2 ↦ c ≠ d)
    (fun _ _ _ _ h ↦ h) (fun _ ↦ 1) (fun _ ↦ true) (fun _ ↦ 0) k
  simp only [PNat.val_ofNat, Nat.cast_one, expand_one_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, torusWeightSeries_true_zero, mk_one_pow_eq_mk_choose_add, coeff_mk,
    Nat.choose_one_right] at h
  rw [h]
  push_cast
  ring

/-- In the class `2 A₀` the two disjoint tori of label `(+, 0)` have count `3`: the distributions
`(2, 0)`, `(1, 1)` and `(0, 2)` of the multiplicity each have weight one. -/
theorem configurationCount_two_tori_two :
    configurationCount (fun c d : Fin 2 ↦ c ≠ d) (fun _ ↦ (1 : ℤ)) (fun _ ↦ torusWeight true 0)
      Set.univ 2 = 3 := by
  exact_mod_cast configurationCount_two_tori 2

/-- Adding the local series of two tori of label `(+, 0)`, instead of multiplying them, would give
`2` in degree two, not the count `3` of `configurationCount_two_tori_two`. -/
theorem coeff_two_torusWeightSeries_true_zero_add :
    coeff 2 (torusWeightSeries true 0 + torusWeightSeries true 0) = 2 := by
  simp [torusWeightSeries_true_zero]

/-- **A ray with a torus in a multiple class.** A torus `T` of class `A₀` and label `(+, 0)` and a
disjoint torus `T'` of class `2 A₀` and label `(+, 1)` have the ray series
`f_(+,0)(t) f_(+,1)(t ^ 2) = (1 + t ^ 2) / (1 - t)`, so their count is `1` in the classes `0` and
`A₀`, and `2` in every class `j A₀` with `j ≥ 2`. -/
theorem configurationCount_ray (j : ℕ) :
    configurationCount (fun c d : Fin 2 ↦ c ≠ d) (fun c ↦ (((![1, 2] : Fin 2 → ℕ+) c : ℕ) : ℤ))
      (fun c ↦ torusWeight true (![0, 1] c)) Set.univ (j : ℤ) = if j ≤ 1 then 1 else 2 := by
  rw [configurationCount_univ_eq_coeff_prod_expand (r := fun c d : Fin 2 ↦ c ≠ d)
    (fun _ _ _ _ h ↦ h) ![1, 2] (fun _ ↦ true) ![0, 1] j, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PNat.val_ofNat, expand_one_apply,
    torusWeightSeries_true_zero, torusWeightSeries_true_one, map_add, map_one, expand_X]
  rw [mul_add, mul_one, map_add, coeff_mk, coeff_mul_X_pow']
  split_ifs with h₁ h₂ h₂ <;> first | omega | simp

/-- Without the substitution `t ↦ t ^ 2`, the product `f_(+,0)(t) f_(+,1)(t)` has coefficient `2`
in degree one, and would credit the torus of class `2 A₀` to the class `A₀`. -/
theorem coeff_one_torusWeightSeries_true_zero_mul_true_one :
    coeff 1 (torusWeightSeries true 0 * torusWeightSeries true 1) = 2 := by
  simp [torusWeightSeries_true_zero, torusWeightSeries_true_one, mul_add, coeff_succ_mul_X]

/-! ### The labels of orbit tori

The return map of a periodic orbit of an area-preserving surface map is a `2 × 2` matrix `P` of
determinant one, and the label of its orbit torus is read off from the signs of `det (1 - P)` and
`det (1 + P)`, as in `TauCeti.X_mul_derivative_torusWeightSeries_of_det_eq_one`. -/

/-- For an angle `θ ∉ 2πℚ` all the signs `sgn det (1 - R_θ ^ k)`, `k ≥ 1`, are positive, so they
sum to `∑_{k ≥ 1} t ^ k = t / (1 - t)`. -/
theorem mk_sign_det_one_sub_rotation_pow {θ : ℝ} (hθ : ∀ q : ℚ, θ ≠ 2 * π * q) :
    (mk fun k ↦ if k = 0 then 0 else
      (SignType.sign (1 - (rotation θ : Matrix (Fin 2) (Fin 2) ℝ) ^ k).det : ℤ)) = X * mk 1 :=
  mk_sign_det_one_sub_pow_of_forall_pos fun _ hk ↦ det_one_sub_rotation_pow_pos hθ hk

/-- **A rotation by an angle `θ ∉ 2πℚ` gives label `(+, 0)`.** For such `θ`, the label read off
from the rotation `R_θ` is `(+, 0)`: `det (1 - R_θ) > 0` and `det (1 + R_θ) ≥ 0`. Its local series
is `f_(+,0) = 1 / (1 - t)`, and by `mk_sign_det_one_sub_rotation_pow` the identity
`t f' = f ∑_{k ≥ 1} sgn det (1 - R_θ ^ k) t ^ k` of
`TauCeti.X_mul_derivative_torusWeightSeries_of_det_eq_one` reads `t f' / f = t / (1 - t)`. -/
theorem torusWeightSeries_label_rotation {θ : ℝ} (hθ : ∀ q : ℚ, θ ≠ 2 * π * q) :
    torusWeightSeries (decide (0 < (1 - (rotation θ : Matrix (Fin 2) (Fin 2) ℝ)).det))
        (if (1 + (rotation θ : Matrix (Fin 2) (Fin 2) ℝ)).det < 0 then 1 else 0) = mk 1 := by
  have h₁ : 0 < (1 - (rotation θ : Matrix (Fin 2) (Fin 2) ℝ)).det := by
    simpa using det_one_sub_rotation_pow_pos hθ one_ne_zero
  have h₂ : ¬ (1 + (rotation θ : Matrix (Fin 2) (Fin 2) ℝ)).det < 0 := by
    rw [det_one_add_rotation, not_lt]
    linarith [Real.neg_one_le_cos θ]
  rw [decide_eq_true h₁, ite_eq_right h₂, torusWeightSeries_true_zero]

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {P : Matrix (Fin 2) (Fin 2) R}

/-- **A negative hyperbolic orbit torus has label `(+, 1)`.** For `P` of determinant one with
`trace P < -2`, the label read off from `P` is `(+, 1)`: `det (1 - P) = 2 - trace P > 0` and
`det (1 + P) = 2 + trace P < 0`. Its local series is `f_(+,1) = 1 + t`. -/
theorem torusWeightSeries_label_of_trace_lt_neg_two (hdet : P.det = 1) (htr : P.trace < -2) :
    torusWeightSeries (decide (0 < (1 - P).det)) (if (1 + P).det < 0 then 1 else 0) = 1 + X := by
  have h₁ : 0 < (1 - P).det := by
    rw [det_one_sub_eq_two_sub_trace_of_det_eq_one hdet]
    linarith
  have h₂ : (1 + P).det < 0 := by
    rw [det_one_add_eq_two_add_trace_of_det_eq_one hdet]
    linarith
  rw [decide_eq_true h₁, ite_eq_left h₂, torusWeightSeries_true_one]

end TauCeti.Examples.TorusWeight
