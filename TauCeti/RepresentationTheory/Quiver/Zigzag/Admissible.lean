/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Relations

/-!
# The zigzag relation ideal is admissible

Let `R` be the arrow ideal of the path algebra of the doubled quiver of a finite simple graph `G`.
The uniform zigzag relation ideal is squeezed between `R ^ 3` and `R ^ 2`: every uniform relator
is a combination of paths of length at least two, and every path of length at least three is
itself a relator. So the zigzag ideal is an admissible ideal, and the zigzag relation quotient is a
bound quiver algebra in the sense of `TauCeti.IsAdmissibleIdeal`, for every finite simple graph.

The lower bound is what makes the image of the arrow ideal cube-zero: whenever the quadratic
relators already lie in `R ^ 3` (as happens for the one-edge graph `A₂`, where they all vanish),
the zigzag ideal is exactly `R ^ 3`.

## Main results

* `TauCeti.arrowIdeal_pow_three_le_zigzagIdeal`: `R ^ 3` lies in the zigzag ideal.
* `TauCeti.zigzagIdeal_le_arrowIdeal_sq`: the zigzag ideal lies in `R ^ 2`.
* `TauCeti.isAdmissibleIdeal_zigzagIdeal`: the zigzag ideal is admissible.
* `TauCeti.zigzagIdeal_eq_arrowIdeal_pow_three`: if every quadratic relator lies in `R ^ 3`, the
  zigzag ideal is `R ^ 3`.

## References

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, for the zigzag
relations, and Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative
Algebras I*, Ch. II.2, for admissible ideals.
-/

public section

namespace TauCeti

open PathAlgebra

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- **Every path of length at least three is a zigzag relation**: the cube of the arrow ideal of
the doubled path algebra lies in the uniform zigzag ideal. -/
theorem arrowIdeal_pow_three_le_zigzagIdeal :
    arrowIdeal k (DoubledQuiver G) ^ 3 ≤ (zigzagIdeal k G).asIdeal := by
  intro f hf
  rw [mem_arrowIdeal_pow, mem_pathSpan_iff] at hf
  rw [← (pathAlgebraBasis k (DoubledQuiver G)).linearCombination_repr f,
    Finsupp.linearCombination_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun x hx => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_left _ _ ?_
  simp only [coe_pathAlgebraBasis, TwoSidedIdeal.mem_asIdeal]
  exact mem_zigzagIdeal_of_isZigzagRelator k G (.long_path x (hf x hx))

/-- A uniform zigzag relator lies in the square of the arrow ideal. -/
theorem IsZigzagRelator.mem_arrowIdeal_sq {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) : x ∈ arrowIdeal k (DoubledQuiver G) ^ 2 := by
  have hpath : ∀ y : Quiver.TotalPath (DoubledQuiver G), 2 ≤ y.2.2.length →
      (ofPath y : pathAlgebra k (DoubledQuiver G)) ∈ arrowIdeal k (DoubledQuiver G) ^ 2 :=
    fun y hy => Ideal.pow_le_pow_right hy (ofPath_mem_arrowIdeal_pow y)
  induction hx with
  | quadratic h =>
    induction h with
    | nonreturn p hp _ => exact hpath ⟨_, _, p⟩ hp.ge
    | equal_backtracks p q hp hq => exact sub_mem (hpath ⟨_, _, p⟩ hp.ge) (hpath ⟨_, _, q⟩ hq.ge)
  | long_path y hy => exact hpath y (by omega)

/-- **Every zigzag relation has length at least two**: the uniform zigzag ideal lies in the square
of the arrow ideal of the doubled path algebra. -/
theorem zigzagIdeal_le_arrowIdeal_sq :
    (zigzagIdeal k G).asIdeal ≤ arrowIdeal k (DoubledQuiver G) ^ 2 := by
  rw [← Ideal.asIdeal_toTwoSided (arrowIdeal k (DoubledQuiver G) ^ 2)]
  refine TwoSidedIdeal.asIdeal.monotone ?_
  rw [zigzagIdeal_eq_span, TwoSidedIdeal.span_le]
  intro x hx
  rw [SetLike.mem_coe, Ideal.mem_toTwoSided]
  exact IsZigzagRelator.mem_arrowIdeal_sq k G hx

/-- **The zigzag relation ideal is admissible**, so the zigzag relation quotient of every finite
simple graph is a bound quiver algebra of its doubled quiver. -/
theorem isAdmissibleIdeal_zigzagIdeal : IsAdmissibleIdeal (zigzagIdeal k G).asIdeal where
  exists_arrowIdeal_pow_le := ⟨3, arrowIdeal_pow_three_le_zigzagIdeal k G⟩
  le_arrowIdeal_sq := zigzagIdeal_le_arrowIdeal_sq k G

/-- **The arrow-ideal-cube-zero presentation.** When every quadratic zigzag relator is a
combination of paths of length at least three, the uniform zigzag ideal is exactly the cube of the
arrow ideal. -/
theorem zigzagIdeal_eq_arrowIdeal_pow_three
    (h : ∀ x, IsQuadraticZigzagRelator k G x → x ∈ arrowIdeal k (DoubledQuiver G) ^ 3) :
    (zigzagIdeal k G).asIdeal = arrowIdeal k (DoubledQuiver G) ^ 3 := by
  refine le_antisymm ?_ (arrowIdeal_pow_three_le_zigzagIdeal k G)
  rw [← Ideal.asIdeal_toTwoSided (arrowIdeal k (DoubledQuiver G) ^ 3)]
  refine TwoSidedIdeal.asIdeal.monotone ?_
  rw [zigzagIdeal_eq_span, TwoSidedIdeal.span_le]
  intro x hx
  rw [SetLike.mem_coe, Ideal.mem_toTwoSided]
  induction hx with
  | quadratic hq => exact h _ hq
  | long_path y hy => exact Ideal.pow_le_pow_right hy (ofPath_mem_arrowIdeal_pow y)

end TauCeti
