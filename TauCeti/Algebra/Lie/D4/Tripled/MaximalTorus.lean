/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.TorusCentralizer
public import TauCeti.Algebra.Lie.D4.Tripled.TrialityProduct

/-!
# The tripled type-D₄ weight torus and its maximality on field-valued points

Over every commutative ring, the weight-torus points of the tripled type-`D₄` carrier are exactly
the carrier points whose matrices are diagonal in the weight basis of `8ᵥ ⊕ 8ₛ ⊕ 8꜀`. One inclusion
is the shape of the torus. For the other, a diagonal carrier point preserves the triality product,
so its diagonal entries are multiplicative along every nonzero structure constant of that product;
so are the values of a torus character on the weights, and a function multiplicative along the
product is determined by its values at four weights forming a basis of the weight lattice.

Over an infinite field the centralizer of the weight torus consists of the diagonal carrier points,
by `TauCeti.D4Tripled.centralizer_range_weightTorusPoints_eq_comap_diagonalTorus`. The weight torus
is therefore its own centralizer, and hence maximal among commutative subgroups of the carrier
points.

These statements concern points of the explicit carrier. Maximality of the weight torus as a
closed subgroup scheme, and any identification of the carrier with the pinned simply connected
group scheme of type `D₄`, are not asserted here.

## Main results

* `TauCeti.D4Tripled.mem_range_weightTorusPoints_iff_isDiag`: over every commutative ring, a carrier
  point lies in the weight torus exactly when its matrix is diagonal.
* `TauCeti.D4Tripled.range_weightTorusPoints_eq_comap_diagonalTorus`: the same statement as an
  equality of subgroups.
* `TauCeti.D4Tripled.centralizer_range_weightTorusPoints_eq_range`: over an infinite field, the
  weight torus is its own centralizer in the carrier points.
* `TauCeti.D4Tripled.eq_range_weightTorusPoints_of_le_of_isMulCommutative`: over an infinite field,
  the weight torus is maximal among commutative subgroups of the carrier points.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §§16.1 and 26.2.
* The organization follows `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.MaximalTorus`.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

universe v

/-- The diagonal entries of a diagonal carrier point are multiplicative along the triality
product. -/
private theorem eq_mul_of_diagGL_mem_points {A : Type v} [CommRing A] {t : Fin 24 → Aˣ}
    (ht : diagGL t ∈ points A) {k i j : Fin 24} (h : trialityProductMatrix k i j ≠ 0) :
    t i = t k * t j := by
  have hpres := preserves_trialityProductMatrix_of_mem_points ht
  rw [diagGL_coe, ConstantMultiplication.preserves_diagonal_iff] at hpres
  have hkij := hpres k i j
  apply Units.ext
  rw [Units.val_mul]
  rcases trialityProductMatrix_apply_eq_neg_one_or_eq_zero_or_eq_one k i j with hc | hc | hc
  · rw [hc] at hkij
    simpa using hkij
  · exact absurd hc h
  · rw [hc] at hkij
    simpa using hkij

/-- The values of a torus character on the tripled weights are multiplicative along the triality
product, which is homogeneous for the weights. -/
private theorem torusCharacter_eq_mul {A : Type v} [CommRing A] (s : Fin 4 → Aˣ) {k i j : Fin 24}
    (h : trialityProductMatrix k i j ≠ 0) :
    torusCharacter s (d4TripledWeight i) =
      torusCharacter s (d4TripledWeight k) * torusCharacter s (d4TripledWeight j) := by
  by_contra hne
  refine h (trialityProductMatrix_apply_eq_zero_of_weight_ne fun hw => hne ?_)
  rw [hw, torusCharacter_add]

/-- **Over every commutative ring, a point of the tripled carrier lies in the weight torus exactly
when its matrix is diagonal** in the weight basis. -/
theorem mem_range_weightTorusPoints_iff_isDiag {A : Type v} [CommRing A] (g : points A) :
    g ∈ (weightTorusPoints A).range ↔
      ((g : Matrix.GeneralLinearGroup (Fin 24) A) : Matrix (Fin 24) (Fin 24) A).IsDiag := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · intro hg
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp (mem_diagonalTorus_iff.mpr hg)
    have htmem : diagGL t ∈ points A := ht ▸ g.property
    -- The torus parameter is read off at the four indices whose weights are `ϖ₁`, `ϖ₂ - ϖ₁`,
    -- `ϖ₃` and `ϖ₄`.
    let s : Fin 4 → Aˣ := ![t 0, t 0 * t 1, t 8, t 16]
    have hchar : (fun a => torusCharacter s (d4TripledWeight a)) = t := by
      refine eq_of_eq_mul_of_trialityProductMatrix_ne_zero
        (fun k i j h => torusCharacter_eq_mul s h)
        (fun k i j h => eq_mul_of_diagGL_mem_points htmem h) ?_ ?_ ?_ ?_ <;>
        simp [s, torusCharacter_def, Fin.prod_univ_four, d4TripledWeight_one]
    refine ⟨s, Subtype.ext ?_⟩
    rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, hchar, ht]

/-- **Over every commutative ring, the weight torus of the tripled carrier consists of all
diagonal carrier points.** -/
theorem range_weightTorusPoints_eq_comap_diagonalTorus (A : Type v) [CommRing A] :
    (weightTorusPoints A).range = (diagonalTorus A 24).comap (points A).subtype := by
  ext g
  rw [mem_range_weightTorusPoints_iff_isDiag, Subgroup.mem_comap, Subgroup.subtype_apply,
    mem_diagonalTorus_iff]

variable (k : Type*) [Field k] [Infinite k]

/-- **Over an infinite field, the weight torus of the tripled carrier is its own centralizer** in
the carrier points. -/
theorem centralizer_range_weightTorusPoints_eq_range :
    Subgroup.centralizer ((weightTorusPoints k).range : Set (points k)) =
      (weightTorusPoints k).range := by
  rw [MonoidHom.coe_range, centralizer_range_weightTorusPoints_eq_comap_diagonalTorus,
    range_weightTorusPoints_eq_comap_diagonalTorus]

/-- **Over an infinite field, the weight torus of the tripled carrier is maximal among commutative
subgroups of the carrier points.** -/
theorem eq_range_weightTorusPoints_of_le_of_isMulCommutative (H : Subgroup (points k))
    [IsMulCommutative H] (hle : (weightTorusPoints k).range ≤ H) :
    H = (weightTorusPoints k).range :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative
    (centralizer_range_weightTorusPoints_eq_range k) hle

end TauCeti.D4Tripled
