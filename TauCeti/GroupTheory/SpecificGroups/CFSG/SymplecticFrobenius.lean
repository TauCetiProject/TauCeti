/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup
public import TauCeti.GroupTheory.SpecificGroups.CFSG.FieldCoordinates
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# The finite-field descent of the symplectic group

Let `d` be a valid Lie-type index, so that `d.Closure` is the algebraic closure of the prime field
of characteristic `d.characteristic` and `d.fieldOrder = d.characteristic ^ d.fieldExponent` is the
order of the field of definition attached to the index. This file identifies the points of the
symplectic group `TauCeti.GLSymplecticFin m` over the closure that are fixed by the entrywise
`d.fieldOrder`-power Frobenius with the symplectic group `Sp_{2m}(𝔽_q)` over Mathlib's
`GaloisField d.characteristic d.fieldExponent`.

The characterization is entrywise. A symplectic matrix over the closure is fixed by the entrywise
Frobenius exactly when each of its entries satisfies `x ^ d.fieldOrder = x`, which by
`Matrix.GeneralLinearGroup.mem_range_map_galoisFieldEmbedding_iff` says that it is the image of an
invertible matrix over the finite field. That finite-field matrix is again symplectic, because the
entrywise coefficient embedding is injective and carries the alternating form `JFin m` to itself.
So the fixed subgroup of the entrywise Frobenius is the range of the coefficient embedding of the
finite symplectic group, and the embedding restricts to an isomorphism onto it.

The results hold for every `m`, so they apply to any family whose carrier is identified with a
symplectic matrix group over the closure, such as the type-`C` carrier. Composing with
`TauCeti.GLSymplecticFin.mulEquivGLSymplectic` and `TauCeti.GLSymplectic.mulEquivSymplecticGroup`
reaches Mathlib's `Matrix.symplecticGroup (Fin m) (GaloisField _ _)`.

## Main definition

* `TauCeti.ValidLieTypeIndex.symplecticEquivFrobeniusFixedPoints`: the isomorphism between the
  finite symplectic group and the Frobenius fixed points of the symplectic group over the closure.

## Main results

* `TauCeti.ValidLieTypeIndex.symplectic_mem_range_galoisFieldEmbedding_iff` and
  `TauCeti.ValidLieTypeIndex.symplectic_mem_fixedSubgroup_frobenius_iff`: the two entrywise
  characterizations of the finite-field points.
* `TauCeti.ValidLieTypeIndex.symplectic_range_galoisFieldEmbedding_eq_fixedSubgroup`: the range of
  the coefficient embedding is the fixed subgroup of the entrywise Frobenius.
* `TauCeti.ValidLieTypeIndex.finite_fixedSubgroup_symplectic`: that fixed subgroup is finite.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§1.2 and 11.3, where the symplectic group over
  `𝔽_q` is the group of Frobenius fixed points of the symplectic group over the closure.

The organization follows `TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialLinearFrobenius`, the same
descent for the special linear group.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.ValidLieTypeIndex

variable (d : ValidLieTypeIndex) {m : ℕ}

/-- A symplectic matrix over the closure has finite-field coordinates exactly when every entry is
fixed by the `q`-power Frobenius. -/
theorem symplectic_mem_range_galoisFieldEmbedding_iff (g : GLSymplecticFin m d.Closure) :
    g ∈ (GLSymplecticFin.map m _ d.galoisFieldEmbedding).range ↔
      ∀ i j, ((g : GL (Fin (m + m)) d.Closure) i j) ^ d.fieldOrder =
        (g : GL (Fin (m + m)) d.Closure) i j := by
  rw [← Matrix.GeneralLinearGroup.mem_range_map_galoisFieldEmbedding_iff]
  constructor
  · rintro ⟨g₀, rfl⟩
    exact ⟨g₀, (GLSymplecticFin.coe_map m _ d.galoisFieldEmbedding g₀).symm⟩
  · rintro ⟨g₀, hg₀⟩
    have hmat : (g₀ : Matrix (Fin (m + m)) (Fin (m + m)) _).map d.galoisFieldEmbedding =
        (g : GL (Fin (m + m)) d.Closure) := by
      ext i j
      rw [Matrix.map_apply, ← hg₀, Matrix.GeneralLinearGroup.map_apply]
    -- The finite-field preimage is symplectic: the coefficient embedding is injective on matrices
    -- and carries the alternating form `JFin m` to itself.
    have hsymp : g₀ ∈ GLSymplecticFin m (GaloisField d.characteristic d.fieldExponent) := by
      rw [GLSymplecticFin.mem_iff]
      apply Matrix.map_injective d.galoisFieldEmbedding.injective
      dsimp only
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hmat, JFin_map]
      exact GLSymplecticFin.mem_iff.mp g.2
    exact ⟨⟨g₀, hsymp⟩, Subtype.ext ((GLSymplecticFin.coe_map m _ _ _).trans hg₀)⟩

/-- A symplectic matrix over the closure is fixed by the entrywise `q`-power Frobenius exactly when
every entry is. -/
theorem symplectic_mem_fixedSubgroup_frobenius_iff (g : GLSymplecticFin m d.Closure) :
    g ∈ fixedSubgroup (GLSymplecticFin.map m d.Closure
      (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) ↔
      ∀ i j, ((g : GL (Fin (m + m)) d.Closure) i j) ^ d.fieldOrder =
        (g : GL (Fin (m + m)) d.Closure) i j := by
  rw [mem_fixedSubgroup, Subtype.ext_iff, GLSymplecticFin.coe_map, Units.ext_iff,
    ← Matrix.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def,
    d.fieldOrder_eq_characteristic_pow]

/-- The range of the coefficient embedding of the symplectic group is the fixed subgroup of the
entrywise `q`-power Frobenius. -/
theorem symplectic_range_galoisFieldEmbedding_eq_fixedSubgroup :
    (GLSymplecticFin.map m _ d.galoisFieldEmbedding).range =
      fixedSubgroup (GLSymplecticFin.map m d.Closure
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) := by
  ext g
  rw [symplectic_mem_range_galoisFieldEmbedding_iff,
    symplectic_mem_fixedSubgroup_frobenius_iff]

variable (m)

/-- **The finite symplectic group is the group of Frobenius fixed points of the symplectic group
over the closure.** The entrywise coefficient extension is injective and its range is that fixed
subgroup, so it restricts to an isomorphism onto the fixed points. -/
def symplecticEquivFrobeniusFixedPoints :
    GLSymplecticFin m (GaloisField d.characteristic d.fieldExponent) ≃*
      fixedSubgroup (GLSymplecticFin.map m d.Closure
        (iterateFrobenius d.Closure d.characteristic d.fieldExponent)) :=
  (MonoidHom.ofInjective (GLSymplecticFin.map_injective d.galoisFieldEmbedding.injective)).trans
    (MulEquiv.subgroupCongr (symplectic_range_galoisFieldEmbedding_eq_fixedSubgroup d))

/-- The isomorphism to the Frobenius fixed points is the entrywise extension of coefficients along
the finite-field embedding. -/
@[simp]
theorem coe_symplecticEquivFrobeniusFixedPoints
    (g : GLSymplecticFin m (GaloisField d.characteristic d.fieldExponent)) :
    ((symplecticEquivFrobeniusFixedPoints d m g : GLSymplecticFin m d.Closure) :
      GL (Fin (m + m)) d.Closure) =
      Matrix.GeneralLinearGroup.map d.galoisFieldEmbedding
        (g : GL (Fin (m + m)) (GaloisField d.characteristic d.fieldExponent)) := by
  simp [symplecticEquivFrobeniusFixedPoints, MonoidHom.ofInjective_apply]

/-- The Frobenius fixed points of a symplectic group over the closure are finite: they are the
image of the finite symplectic group over the field of definition. -/
instance finite_fixedSubgroup_symplectic :
    Finite (fixedSubgroup (GLSymplecticFin.map m d.Closure
      (iterateFrobenius d.Closure d.characteristic d.fieldExponent))) :=
  Finite.of_equiv (GLSymplecticFin m (GaloisField d.characteristic d.fieldExponent))
    (symplecticEquivFrobeniusFixedPoints d m).toEquiv

end TauCeti.ValidLieTypeIndex

end
