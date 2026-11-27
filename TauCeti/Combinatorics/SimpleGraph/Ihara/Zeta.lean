/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Hashimoto
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Zeta

/-!
# The Ihara zeta function of a finite simple graph

The Ihara zeta function of a graph counts its closed non-backtracking walks the way the zeta
function of a variety over a finite field counts its points. Writing `N_m` for the number of closed
walks of length `m` that never step back along the dart they arrived on, including across the
closing step, each counted with its starting vertex
(`SimpleGraph.closedNonBacktrackingCount`), it is the power series

`ζ(u) = exp (∑ₘ N_m uᵐ / m)`

with rational coefficients. The exponent has constant term `N₀ / 0 = 0`, so the exponential is
the composition of power series.

The **determinant formula** `ζ(u) det (1 - u B) = 1`, for `B` the Hashimoto matrix of the graph,
shows that `ζ` is the reciprocal of a polynomial with integer coefficients and constant term `1`.
It follows from the trace formula `tr Bᵐ = N_m` for `m ≥ 1`
(`SimpleGraph.trace_hashimotoMatrix_pow`) and the trace–determinant formula
`exp (∑ₘ tr (Bᵐ) uᵐ / m) det (1 - u B) = 1` (`Matrix.subst_exp_mul_charpolyRev`). In particular
the coefficients of `ζ` are integers, those of the inverse of `det (1 - u B)` over `ℤ`.

The definition typechecks for every simple graph, but it is the Ihara zeta function only when
every `N_m` is finite, for example for a finite graph: `N_m` is a `Nat.card`, which is `0` for an
infinite set of walks. The determinant formula holds for every finite simple graph, with no
connectivity or degree hypothesis.

## Main definitions

* `SimpleGraph.iharaZeta G`: the Ihara zeta function `exp (∑ₘ N_m uᵐ / m)` in `ℚ⟦X⟧`.

## Main results

* `SimpleGraph.logOf_iharaZeta`: the logarithm of `ζ` is the walk-count series `∑ₘ N_m uᵐ / m`;
  together with `SimpleGraph.constantCoeff_iharaZeta` this determines `ζ` (`PowerSeries.logOf_inj`).
* `SimpleGraph.iharaZeta_mul_charpolyRev`: **the determinant formula** `ζ(u) det (1 - u B) = 1`.
* `SimpleGraph.iharaZeta_eq_inv_charpolyRev`: `ζ(u) = det (1 - u B)⁻¹`.
* `SimpleGraph.iharaZeta_eq_map_invOfUnit`: `ζ` is the image in `ℚ⟦X⟧` of the inverse in `ℤ⟦X⟧`
  of the integer polynomial `det (1 - u B)`, so its coefficients are integers.

## References

* Y. Ihara, *On discrete subgroups of the two by two projective linear group over p-adic fields*,
  J. Math. Soc. Japan 18 (1966), 219–235.
* K. Hashimoto, *Zeta functions of finite graphs and representations of p-adic groups*, in
  Automorphic Forms and Geometry of Arithmetic Varieties, Adv. Stud. Pure Math. 15 (1989), 211–280.
* A. Terras, *Zeta Functions of Graphs: A Stroll through the Garden*, Cambridge Studies in Advanced
  Mathematics 128, Cambridge University Press, 2011: the zeta function as the exponential of the
  walk-count series, and its determinant formula `ζ(u) = det (1 - u W₁)⁻¹` for the edge adjacency
  matrix `W₁`.
-/

public section

open Matrix PowerSeries

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The *Ihara zeta function* `ζ(u) = exp (∑ₘ N_m uᵐ / m)` of a simple graph, a power series with
rational coefficients. Here `N_m` is the number of closed non-backtracking walks of length `m`,
each counted with its starting vertex (`SimpleGraph.closedNonBacktrackingCount`); the term of
degree `0` of the exponent is `N₀ / 0 = 0`. -/
noncomputable def iharaZeta : ℚ⟦X⟧ :=
  (exp ℚ).subst (PowerSeries.mk fun m ↦ (G.closedNonBacktrackingCount m : ℚ) / m)

theorem iharaZeta_def :
    G.iharaZeta =
      (exp ℚ).subst (PowerSeries.mk fun m ↦ (G.closedNonBacktrackingCount m : ℚ) / m) :=
  (rfl)

/-- The Ihara zeta function has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_iharaZeta : constantCoeff G.iharaZeta = 1 :=
  constantCoeff_subst_exp (by simp)

/-- The logarithm of the Ihara zeta function is the walk-count series `∑ₘ N_m uᵐ / m`. -/
@[simp]
theorem logOf_iharaZeta :
    logOf G.iharaZeta = PowerSeries.mk fun m ↦ (G.closedNonBacktrackingCount m : ℚ) / m :=
  logOf_subst_exp (by simp)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- By the trace formula, the walk-count series `∑ₘ N_m uᵐ / m` is the series
`∑ₘ tr (Bᵐ) uᵐ / m` of the Hashimoto matrix `B`; both vanish in degree `0`. -/
private theorem mk_closedNonBacktrackingCount_div_eq :
    (PowerSeries.mk fun m ↦ (G.closedNonBacktrackingCount m : ℚ) / m) =
      PowerSeries.mk fun m ↦ (m : ℚ)⁻¹ • (G.hashimotoMatrix ℚ ^ m).trace := by
  ext m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [coeff_mk, coeff_mk, trace_hashimotoMatrix_pow hm, smul_eq_mul, div_eq_inv_mul]

/-- **The determinant formula** for the Ihara zeta function: `ζ(u) det (1 - u B) = 1` in `ℚ⟦u⟧`,
where `B` is the Hashimoto matrix of the graph. -/
theorem iharaZeta_mul_charpolyRev :
    G.iharaZeta * ((G.hashimotoMatrix ℚ).charpolyRev : ℚ⟦X⟧) = 1 := by
  rw [iharaZeta_def, mk_closedNonBacktrackingCount_div_eq]
  exact subst_exp_mul_charpolyRev _

/-- The Ihara zeta function is the reciprocal `ζ(u) = det (1 - u B)⁻¹` of the polynomial
`det (1 - u B)`, where `B` is the Hashimoto matrix of the graph. -/
theorem iharaZeta_eq_inv_charpolyRev :
    G.iharaZeta = ((G.hashimotoMatrix ℚ).charpolyRev : ℚ⟦X⟧)⁻¹ :=
  (eq_inv_iff_mul_eq_one (by rw [constantCoeff_coe_charpolyRev]; exact one_ne_zero)).2
    G.iharaZeta_mul_charpolyRev

/-- The Ihara zeta function has integer coefficients: it is the image in `ℚ⟦u⟧` of the inverse in
`ℤ⟦u⟧` of `det (1 - u B)`, an integer polynomial with constant term `1`, where `B` is the
Hashimoto matrix of the graph. -/
theorem iharaZeta_eq_map_invOfUnit :
    G.iharaZeta = map (Int.castRingHom ℚ)
      (invOfUnit ((G.hashimotoMatrix ℤ).charpolyRev : ℤ⟦X⟧) 1) := by
  have h := congrArg (map (Int.castRingHom ℚ))
    (mul_invOfUnit ((G.hashimotoMatrix ℤ).charpolyRev : ℤ⟦X⟧) 1
      (by rw [constantCoeff_coe_charpolyRev, Units.val_one]))
  rw [map_mul, map_one, ← Polynomial.polynomial_map_coe, ← charpolyRev_map,
    hashimotoMatrix_map _ (map_zero _) (map_one _)] at h
  exact left_inv_eq_right_inv G.iharaZeta_mul_charpolyRev h

end SimpleGraph
