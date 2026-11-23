/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.AffinePoint.Basic
public import TauCeti.Topology.Algebra.PointTopology.Basic

/-!
# The monomial-embedding topology is the evaluation topology

The complex points `ℂ[S] →ₐ[ℂ] ℂ` of an affine semigroup `S` carry two topologies: the
monomial-embedding topology `TauCeti.Toric.affinePointTopology`, induced by evaluation on a
finite generating family of `S`, and the evaluation topology `TauCeti.PointTopology.topology`,
in which every evaluation `x ↦ x a` is continuous. This file shows that they agree: every
element of the semigroup algebra is a finite combination of monomials.

## Main declarations

* `TauCeti.Toric.affinePointTopology_eq_pointTopology`: on the complex points of an affine
  semigroup, the monomial-embedding topology is the evaluation topology.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
-/

public section

open Multiplicative

namespace TauCeti.Toric

variable {S : Type*} [AddCommMonoid S] {r : ℕ}

/-- On the complex points of an affine semigroup, the topology induced by evaluation on a
finite generating family is the evaluation topology of `TauCeti.PointTopology`, in which every
evaluation `x ↦ x a` is continuous. -/
theorem affinePointTopology_eq_pointTopology (g : AddGeneratingFamily S r) :
    affinePointTopology g = PointTopology.topology := by
  refine le_antisymm ?_ ?_
  · let _ := affinePointTopology g
    rw [← continuous_id_iff_le]
    exact PointTopology.continuous_iff.2 (continuous_eval_const g)
  · let _ := PointTopology.topology (k := ℂ) (A := MonoidAlgebra ℂ (Multiplicative S)) (R := ℂ)
    rw [← continuous_id_iff_le]
    exact (continuous_iff_forall_continuous_apply_single g id).2 fun s ↦
      PointTopology.continuous_eval _

end TauCeti.Toric
