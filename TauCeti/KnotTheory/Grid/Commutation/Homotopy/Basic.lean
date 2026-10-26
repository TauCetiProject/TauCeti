/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Hexagon
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Basic

/-!
# The homotopy equation of a grid commutation

Let `C` be a validated column commutation of a grid diagram `G`, write `G'` for the commuted
diagram `G.swapColumns C.column (finRotate n C.column)`, `∂` for the unblocked differential of
`G`, `Φ : GC⁻(G) → GC⁻(G')` for the commutation map `GridDiagram.commutationMap` of `C`,
`Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of the reverse data `C.reverse`, and
`H : GC⁻(G) → GC⁻(G)` for the hexagon-counting map `GridDiagram.commutationHomotopy`. Over `𝔽₂`,
commutation invariance rests on the homotopy equation

  `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ`.

This file writes that equation as a finite identity between matrix coefficients.

Both `Φ` and `Ψ` are semilinear over the renaming of the variables by the swap of the two commuted
columns. That swap is an involution, so the round trip `Ψ ∘ Φ` is linear over the polynomial ring
(`GridDiagram.reverse_commutationMap_commutationMap_smul`), like `∂` and `H`, and the equation holds
on all chains as soon as it holds on the grid-state generators. On a generator `x`, the coefficient
of `∂ (H x) + H (∂ x)` at `z` is a sum over intermediate states of products of rectangle and hexagon
coefficients, and that of `Ψ (Φ x)` is a sum of products of pentagon coefficients, the first one
renamed into the variables of `G`.

Every term is then a product, over the squares covered by a two-step domain, of one per-square
weight in the variables of `G`: the variable of the square's column at an `O`-marking of `G` and
`1` elsewhere. This is `GridDiagram.OMonomial_eq_prod_coveredSquares` for rectangles,
`GridDiagram.hexagonWeight_eq_prod_coveredSquares` and its initial version for hexagons,
`GridDiagram.rename_pentagonWeight` and its initial version for the pentagons of `Φ`, and
`GridDiagram.pentagonWeight_reverse` and its initial version for the pentagons of `Ψ`, whose
squares are read in `G` by exchanging the two commuted columns. Comparing the weights of two
two-step domains thus reduces to comparing the multisets of squares they cover.

## Main results

* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_single_apply`,
  `TauCeti.GridDiagram.commutationHomotopy_unblockedDifferential_single_apply` and
  `TauCeti.GridDiagram.reverse_commutationMap_commutationMap_single_apply`: the matrix coefficients
  of `∂ ∘ H`, `H ∘ ∂` and `Ψ ∘ Φ`.
* `TauCeti.GridDiagram.reverse_commutationMap_commutationMap_smul`: the round trip `Ψ ∘ Φ` is
  linear over the polynomial ring.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff`: the homotopy
  equation holds on every chain exactly when, for all grid states `x` and `z`, the rectangle and
  hexagon coefficient products from `x` to `z` sum to `δ_{xz}` plus the pentagon coefficient
  products.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  (R : Type*) [CommSemiring R]

local notation "b" => finRotate n C.column

/-- On a grid-state generator, the coefficient of the unblocked differential after the
commutation homotopy is the sum over intermediate states of the commutation hexagon coefficient
times the rectangle coefficient. -/
theorem unblockedDifferential_commutationHomotopy_single_apply (x z : GridState n) :
    G.unblockedDifferential R (G.commutationHomotopy R C (Finsupp.single x 1)) z =
      ∑ y : GridState n,
        G.commutationHexagonCoefficient R C x y * G.unblockedCoefficient R y z := by
  rw [unblockedDifferential_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp_rw [commutationHomotopy_single_apply]

/-- On a grid-state generator, the coefficient of the commutation homotopy after the unblocked
differential is the sum over intermediate states of the rectangle coefficient times the
commutation hexagon coefficient. -/
theorem commutationHomotopy_unblockedDifferential_single_apply (x z : GridState n) :
    G.commutationHomotopy R C (G.unblockedDifferential R (Finsupp.single x 1)) z =
      ∑ y : GridState n,
        G.unblockedCoefficient R x y * G.commutationHexagonCoefficient R C y z := by
  rw [commutationHomotopy_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp [commutationHexagonCoefficient_def]

/-- On a grid-state generator, the coefficient of the round trip `Ψ ∘ Φ` through the commuted
diagram is the sum over intermediate states of the commutation pentagon coefficient of `Φ`,
renamed by the column swap, times that of the reverse commutation map `Ψ`. -/
theorem reverse_commutationMap_commutationMap_single_apply (x z : GridState n) :
    (G.swapColumns C.column b).commutationMap R C.reverse
        (G.commutationMap R C (Finsupp.single x 1)) z =
      ∑ y : GridState n,
        rename (Equiv.swap C.column b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns C.column b).commutationPentagonCoefficient R C.reverse y z := by
  rw [commutationMap_apply_apply, Finsupp.sum_fintype _ _ fun _ => by simp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [commutationMap_single_apply, ColumnCommutationData.reverse_column,
    commutationPentagonCoefficient_def (G.swapColumns C.column b)]

/-- The round trip `Ψ ∘ Φ` through the commuted diagram is linear over the polynomial ring: the
commutation map and its reverse are semilinear over the same renaming of the variables by the
swap of the two commuted columns, and that renaming is an involution. -/
@[simp]
theorem reverse_commutationMap_commutationMap_smul (p : MvPolynomial (Fin n) R)
    (c : GridChainMinus R n) :
    (G.swapColumns C.column b).commutationMap R C.reverse (G.commutationMap R C (p • c)) =
      p • (G.swapColumns C.column b).commutationMap R C.reverse (G.commutationMap R C c) := by
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
  congr 1
  simp only [AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, renameEquiv_apply, rename_rename,
    ColumnCommutationData.reverse_column]
  rw [← Equiv.coe_trans, Equiv.swap_swap, Equiv.coe_refl, rename_id_apply]

/-- The homotopy equation `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ` of a column commutation holds on every
chain exactly when, for all grid states `x` and `z`, the products of rectangle and hexagon
coefficients through intermediate states, in both orders, sum to the Kronecker delta of `x` and
`z` plus the products of the coefficients of the commutation map, renamed by the column swap, and
of its reverse. -/
theorem unblockedDifferential_commutationHomotopy_add_eq_iff :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.commutationHomotopy R C c) +
          G.commutationHomotopy R C (G.unblockedDifferential R c) =
        c + (G.swapColumns C.column b).commutationMap R C.reverse (G.commutationMap R C c)) ↔
      ∀ x z : GridState n,
        ∑ y : GridState n,
            (G.commutationHexagonCoefficient R C x y * G.unblockedCoefficient R y z +
              G.unblockedCoefficient R x y * G.commutationHexagonCoefficient R C y z) =
          (if x = z then 1 else 0) +
            ∑ y : GridState n,
              rename (Equiv.swap C.column b) (G.commutationPentagonCoefficient R C x y) *
                (G.swapColumns C.column b).commutationPentagonCoefficient R C.reverse y z := by
  simp_rw [Finset.sum_add_distrib, ← unblockedDifferential_commutationHomotopy_single_apply,
    ← commutationHomotopy_unblockedDifferential_single_apply,
    ← reverse_commutationMap_commutationMap_single_apply, ← Finsupp.single_apply,
    ← Finsupp.add_apply, ← Finsupp.ext_iff]
  refine ⟨fun h x => h _, fun h c => ?_⟩
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, add_zero]
  | add c d hc hd =>
    rw [map_add, map_add, map_add, map_add, map_add, add_add_add_comm, hc, hd, map_add,
      add_add_add_comm]
  | single x p =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul, ← smul_add, h,
      reverse_commutationMap_commutationMap_smul, smul_add]

end TauCeti.GridDiagram
