/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.CrossProduct
public import TauCeti.Algebra.Lie.E6.Minuscule.SeedCoordinates

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.TorusCentralizer.Basic

/-!
# The doubled type-E6 weight torus and its maximality on field-valued points

Over every commutative ring, the weight-torus points of the doubled type-`E₆` minuscule carrier
are exactly the carrier points whose matrices are diagonal in the weight basis of
`V(ϖ₁) ⊕ V(ϖ₆)`. One inclusion is the shape of the torus. For the other, a diagonal carrier point
preserves the cross product built from the invariant cubic form, so its diagonal entries are
multiplicative along every nonzero structure constant of that product; so are the values of a
torus character on the weights, and a function multiplicative along the product is determined by
its values at six weights forming a basis of the weight lattice.

Over an infinite field the centralizer of the weight torus consists of the diagonal carrier
points, by `TauCeti.E6DoubledMinuscule.centralizer_range_weightTorusPoints_eq_comap_diagonalTorus`.
The weight torus is therefore its own centralizer, and hence maximal among commutative subgroups
of the carrier points.

These statements concern points of the explicit carrier. Maximality of the weight torus as a
closed subgroup scheme, and any identification of the carrier with the pinned simply connected
group scheme of type `E₆`, are not asserted here.

## Main results

* `TauCeti.E6DoubledMinuscule.mem_range_weightTorusPoints_iff_isDiag`: over every commutative
  ring, a carrier point lies in the weight torus exactly when its matrix is diagonal.
* `TauCeti.E6DoubledMinuscule.range_weightTorusPoints_eq_comap_diagonalTorus`: the same statement
  as an equality of subgroups.
* `TauCeti.E6DoubledMinuscule.centralizer_range_weightTorusPoints_eq_range`: over an infinite
  field, the weight torus is its own centralizer in the carrier points.
* `TauCeti.E6DoubledMinuscule.eq_range_weightTorusPoints_of_le_of_isMulCommutative`: over an
  infinite field, the weight torus is maximal among commutative subgroups of the carrier points.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §§16.1 and 26.2.
* The organization follows `TauCeti.Algebra.Lie.D4.Tripled.MaximalTorus`.
-/

public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open TauCeti.DynkinType

universe v

/-- **Over every commutative ring, a point of the doubled carrier lies in the weight torus exactly
when its matrix is diagonal** in the weight basis. -/
theorem mem_range_weightTorusPoints_iff_isDiag {A : Type v} [CommRing A] (g : points A) :
    g ∈ (weightTorusPoints A).range ↔
      ((g : Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A).IsDiag := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · intro hg
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp (mem_diagonalTorus_iff.mpr hg)
    have htmem : diagGL t ∈ points A := ht ▸ g.property
    let τ : Fin 27 → Aˣ := fun a => t (matrixIndexEquiv (.inl a))
    let s := E6Minuscule.torusParameterOfSeedValues τ
    -- The carrier point `diagGL t` and the torus point at `s` both preserve the cross product,
    -- whose nonzero structure constants are `±1`, so their diagonal entries are multiplicative
    -- along it.
    have hunit {k i j : Fin 54} (h : crossProductMatrix k i j ≠ 0) :
        IsUnit (algebraMap ℤ A (crossProductMatrix k i j)) :=
      (Int.isUnit_iff.mpr <| by
        rcases crossProductMatrix_apply_eq_neg_one_or_eq_zero_or_eq_one k i j with hc | hc | hc <;>
          simp_all).map _
    have hpt := preserves_crossProductMatrix_of_mem_points htmem
    rw [diagGL_coe] at hpt
    have hps := preserves_crossProductMatrix_weightTorusPoints A s
    rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
      diagGL_coe] at hps
    have hchar : (fun a => torusCharacter s (matrixWeight a)) = t := by
      refine eq_of_eq_mul_of_crossProductMatrix_ne_zero
        (fun k i j h => Units.ext ?_) (fun k i j h => Units.ext ?_) ?_
      · rw [Units.val_mul]
        exact ConstantMultiplication.eq_mul_of_preserves_diagonal _ hps (hunit h)
      · rw [Units.val_mul]
        exact ConstantMultiplication.eq_mul_of_preserves_diagonal _ hpt (hunit h)
      simpa only [matrixWeight_apply, Equiv.symm_apply_apply,
        e6DoubledMinusculeWeight_inl] using
        E6Minuscule.torusCharacter_torusParameterOfSeedValues τ
    refine ⟨s, Subtype.ext ?_⟩
    rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, hchar, ht]

/-- **Over every commutative ring, the weight torus of the doubled carrier consists of all
diagonal carrier points.** -/
theorem range_weightTorusPoints_eq_comap_diagonalTorus (A : Type v) [CommRing A] :
    (weightTorusPoints A).range = (diagonalTorus A 54).comap (points A).subtype := by
  ext g
  rw [mem_range_weightTorusPoints_iff_isDiag, Subgroup.mem_comap, Subgroup.subtype_apply,
    mem_diagonalTorus_iff]

variable (k : Type*) [Field k] [Infinite k]

/-- **Over an infinite field, the weight torus of the doubled carrier is its own centralizer** in
the carrier points. -/
theorem centralizer_range_weightTorusPoints_eq_range :
    Subgroup.centralizer ((weightTorusPoints k).range : Set (points k)) =
      (weightTorusPoints k).range := by
  rw [MonoidHom.coe_range, centralizer_range_weightTorusPoints_eq_comap_diagonalTorus,
    range_weightTorusPoints_eq_comap_diagonalTorus]

/-- **Over an infinite field, the weight torus of the doubled carrier is maximal among commutative
subgroups of the carrier points.** -/
theorem eq_range_weightTorusPoints_of_le_of_isMulCommutative (H : Subgroup (points k))
    [IsMulCommutative H] (hle : (weightTorusPoints k).range ≤ H) :
    H = (weightTorusPoints k).range :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative
    (centralizer_range_weightTorusPoints_eq_range k) hle

end TauCeti.E6DoubledMinuscule
