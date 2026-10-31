/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialLinearFrobenius
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.GraphAutomorphism

/-!
# The finite-field descent of the graph-twisted Frobenius of the special linear group

Let `d` be a valid Lie-type index with characteristic `p` and field order `q = p ^ e`, and let
`θ` be the signed reverse-inverse-transpose automorphism
`Matrix.SpecialLinearGroup.typeAGraphAutomorphism` of `SL_{r+1}`. The graph-twisted Frobenius
`g ↦ θ (g ^ (q))` of `SL_{r+1}` over the algebraic closure `d.Closure` is the standard Steinberg
map of the unitary groups `²A_r(q)`. This file identifies its fixed points with a group of
matrices over the field of `q²` elements: the points of `SL_{r+1}(𝔽_{q²})` fixed by the same
formula, with `x ↦ x ^ q` now the involutive field automorphism of `𝔽_{q²}`. This finite fixed
subgroup is the standard matrix model of the special unitary group `SU_{r+1}(q)`, the description
of the twisted groups of type `A` in Carter's *Simple Groups of Lie Type*, §§13.1 and 14.1.

A point fixed by the twisted Frobenius over the closure is fixed by its square, the entrywise
`q²`-power Frobenius, because `θ` is an involution commuting with entrywise ring maps. So its
entries lie in the subfield with `q²` elements, which is the image of the chosen embedding
`TauCeti.ValidLieTypeIndex.extensionGaloisFieldEmbedding d 2`, and the coefficient extension
along that embedding is an isomorphism from the finite fixed subgroup onto the fixed subgroup
over the closure.

By `TauCeti.typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq`, the finite fixed
subgroup consists of the determinant-one matrices `g` with `(g ^ (q))ᵀ * Q * g = Q`, where `Q` is
the signed reversal matrix: the isometries of determinant one of the sesquilinear form of Gram
matrix `Q` relative to `x ↦ x ^ q` (`mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff`). Since
`Qᵀ = (-1) ^ r • Q`, this form is Hermitian for even `r` or in characteristic two, and
skew-Hermitian otherwise.

The field with `q²` elements and its embedding come from `CFSG/Frobenius.lean`, and the entrywise
description of the special linear matrices with coordinates in it from
`CFSG/SpecialLinearFrobenius.lean`. The square relation for the twisted Frobenius is
`Matrix.SpecialLinearGroup.typeAGraphAutomorphism_comp_map_comp_self`.

## Main definitions

* `TauCeti.ValidLieTypeIndex.galoisFieldTwistedFrobenius`: the graph-twisted `q`-power Frobenius of
  `SL_{r+1}(𝔽_{q²})`.
* `TauCeti.ValidLieTypeIndex.specialUnitaryEquivFrobeniusFixedPoints`: the isomorphism between
  its fixed subgroup and the fixed subgroup of the graph-twisted Frobenius over the closure.

## Main results

* `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff`: the finite fixed
  points are the isometries of determinant one of the form of Gram matrix `Q`.
* `TauCeti.ValidLieTypeIndex.specialLinear_map_extensionGaloisFieldEmbedding_fixedSubgroup`: the
  coefficient extension carries the finite fixed subgroup onto the fixed subgroup over the closure.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), §§13.1 and 14.1.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.ValidLieTypeIndex

variable {d : ValidLieTypeIndex}

/-! ### The graph-twisted Frobenius over the field with `q²` elements -/

variable (d) in
/-- **The graph-twisted `q`-power Frobenius of `SL_{r+1}(𝔽_{q²})`**, `g ↦ θ (g ^ (q))`, with `θ`
the signed reverse-inverse-transpose automorphism and `x ↦ x ^ q` the involutive automorphism of
the field with `q²` elements. Its fixed subgroup is the special unitary group `SU_{r+1}(q)` of the
form described in `mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff`. -/
def galoisFieldTwistedFrobenius (r : ℕ) :
    SpecialLinearGroup (Fin (r + 1)) (GaloisField d.characteristic (d.fieldExponent * 2)) →*
      SpecialLinearGroup (Fin (r + 1)) (GaloisField d.characteristic (d.fieldExponent * 2)) :=
  (SpecialLinearGroup.typeAGraphAutomorphism r _).toMonoidHom.comp
    (SpecialLinearGroup.map
      (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
        d.fieldExponent))

/-- The graph-twisted Frobenius applies signed reverse inverse transpose to the entrywise
`q`-th power. -/
theorem galoisFieldTwistedFrobenius_apply (r : ℕ)
    (g : SpecialLinearGroup (Fin (r + 1))
      (GaloisField d.characteristic (d.fieldExponent * 2))) :
    d.galoisFieldTwistedFrobenius r g =
      SpecialLinearGroup.typeAGraphAutomorphism r _
        (SpecialLinearGroup.map
          (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
            d.characteristic d.fieldExponent) g) :=
  (rfl)

/-- **The fixed points of the graph-twisted Frobenius are special unitary matrices.** A matrix
`g` of `SL_{r+1}(𝔽_{q²})` is fixed exactly when `(g ^ (q))ᵀ * Q * g = Q`, with `Q` the signed
reversal matrix: `g` preserves the sesquilinear form of Gram matrix `Q` relative to `x ↦ x ^ q`.
-/
theorem mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff (r : ℕ)
    (g : SpecialLinearGroup (Fin (r + 1))
      (GaloisField d.characteristic (d.fieldExponent * 2))) :
    g ∈ fixedSubgroup (d.galoisFieldTwistedFrobenius r) ↔
      ((g : Matrix (Fin (r + 1)) (Fin (r + 1))
            (GaloisField d.characteristic (d.fieldExponent * 2))).map (· ^ d.fieldOrder))ᵀ *
          (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
            Matrix (Fin (r + 1)) (Fin (r + 1))
              (GaloisField d.characteristic (d.fieldExponent * 2))) * g =
        (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
          Matrix (Fin (r + 1)) (Fin (r + 1))
            (GaloisField d.characteristic (d.fieldExponent * 2))) := by
  have hσ : ⇑(iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
      d.characteristic d.fieldExponent) = (· ^ d.fieldOrder) :=
    funext fun x ↦ by rw [iterateFrobenius_def, d.fieldOrder_eq_characteristic_pow]
  rw [mem_fixedSubgroup, galoisFieldTwistedFrobenius_apply,
    ← SpecialLinearGroup.toGL_injective.eq_iff, SpecialLinearGroup.toGL_typeAGraphAutomorphism,
    typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq,
    SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hσ]

/-! ### Descent to the closure -/

/-- The coefficient extension along the embedding of the field with `q²` elements intertwines
the finite graph-twisted Frobenius with the graph-twisted Frobenius over the closure. -/
private theorem specialLinear_map_extensionGaloisFieldEmbedding_comp (r : ℕ) :
    (SpecialLinearGroup.map (n := Fin (r + 1))
        (d.extensionGaloisFieldEmbedding 2 two_ne_zero)).comp (d.galoisFieldTwistedFrobenius r) =
      ((SpecialLinearGroup.typeAGraphAutomorphism r d.Closure : _ →* _).comp
        (SpecialLinearGroup.map
          (iterateFrobenius d.Closure d.characteristic d.fieldExponent))).comp
        (SpecialLinearGroup.map (d.extensionGaloisFieldEmbedding 2 two_ne_zero)) := by
  refine MonoidHom.ext fun g ↦ ?_
  simp only [MonoidHom.comp_apply, galoisFieldTwistedFrobenius_apply, MonoidHom.coe_ofClass,
    SpecialLinearGroup.map_typeAGraphAutomorphism]
  rw [← MonoidHom.comp_apply (SpecialLinearGroup.map _), SpecialLinearGroup.map_comp,
    (d.extensionGaloisFieldEmbedding 2 two_ne_zero).iterateFrobenius_comm d.characteristic
      d.fieldExponent,
    ← SpecialLinearGroup.map_comp, MonoidHom.comp_apply]

/-- A special linear matrix over the closure fixed by the graph-twisted Frobenius is fixed by its
square, the entrywise `q²`-power map, so it has coordinates in the field with `q²` elements. -/
private theorem fixedSubgroup_le_range_extensionGaloisFieldEmbedding (r : ℕ) :
    fixedSubgroup ((SpecialLinearGroup.typeAGraphAutomorphism r d.Closure : _ →* _).comp
        (SpecialLinearGroup.map
          (iterateFrobenius d.Closure d.characteristic d.fieldExponent))) ≤
      (SpecialLinearGroup.map (n := Fin (r + 1))
        (d.extensionGaloisFieldEmbedding 2 two_ne_zero)).range := by
  intro g hg
  -- The square of the twisted Frobenius is the entrywise `q²`-power Frobenius.
  have hg₂ : g ∈ fixedSubgroup (SpecialLinearGroup.map
      (iterateFrobenius d.Closure d.characteristic (d.fieldExponent * 2))) := by
    rw [mul_two, iterateFrobenius_add,
      ← SpecialLinearGroup.typeAGraphAutomorphism_comp_map_comp_self]
    exact fixedSubgroup_le_fixedSubgroup_pow _ 2 hg
  rw [mem_fixedSubgroup] at hg₂
  rw [specialLinear_mem_range_extensionGaloisFieldEmbedding_iff]
  intro i j
  have h := congrArg (fun x : SpecialLinearGroup (Fin (r + 1)) d.Closure ↦ x i j) hg₂
  simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    iterateFrobenius_def, pow_mul, ← d.fieldOrder_eq_characteristic_pow] using h

/-- **The coefficient extension carries the finite fixed subgroup onto the fixed subgroup over
the closure.** The image of the points of `SL_{r+1}(𝔽_{q²})` fixed by the finite graph-twisted
Frobenius is exactly the group of points of `SL_{r+1}` over the closure fixed by
`g ↦ θ (g ^ (q))`. -/
theorem specialLinear_map_extensionGaloisFieldEmbedding_fixedSubgroup (r : ℕ) :
    (fixedSubgroup (d.galoisFieldTwistedFrobenius r)).map
        (SpecialLinearGroup.map (d.extensionGaloisFieldEmbedding 2 two_ne_zero)) =
      fixedSubgroup ((SpecialLinearGroup.typeAGraphAutomorphism r d.Closure : _ →* _).comp
        (SpecialLinearGroup.map
          (iterateFrobenius d.Closure d.characteristic d.fieldExponent))) := by
  rw [MonoidHom.map_fixedSubgroup_of_injective _
      (specialLinear_map_extensionGaloisFieldEmbedding_comp r)
      (SpecialLinearGroup.map_injective (RingHom.injective _)),
    inf_eq_right]
  exact fixedSubgroup_le_range_extensionGaloisFieldEmbedding r

variable (d) in
/-- **The finite special unitary group is the group of fixed points of the graph-twisted Frobenius
of `SL_{r+1}` over the closure.** The coefficient extension along the embedding of the field with
`q²` elements restricts to an isomorphism between the two fixed subgroups. -/
def specialUnitaryEquivFrobeniusFixedPoints (r : ℕ) :
    fixedSubgroup (d.galoisFieldTwistedFrobenius r) ≃*
      fixedSubgroup ((SpecialLinearGroup.typeAGraphAutomorphism r d.Closure :
          SpecialLinearGroup (Fin (r + 1)) d.Closure →*
            SpecialLinearGroup (Fin (r + 1)) d.Closure).comp
        (SpecialLinearGroup.map
          (iterateFrobenius d.Closure d.characteristic d.fieldExponent))) :=
  ((fixedSubgroup (d.galoisFieldTwistedFrobenius r)).equivMapOfInjective _
      (SpecialLinearGroup.map_injective (RingHom.injective _))).trans
    (MulEquiv.subgroupCongr (specialLinear_map_extensionGaloisFieldEmbedding_fixedSubgroup r))

/-- The isomorphism with the fixed points over the closure is the entrywise extension of
coefficients along the embedding of the field with `q²` elements. -/
@[simp]
theorem coe_specialUnitaryEquivFrobeniusFixedPoints (r : ℕ)
    (g : fixedSubgroup (d.galoisFieldTwistedFrobenius r)) :
    (((d.specialUnitaryEquivFrobeniusFixedPoints r g : SpecialLinearGroup (Fin (r + 1))
        d.Closure)) : Matrix (Fin (r + 1)) (Fin (r + 1)) d.Closure) =
      (g : Matrix (Fin (r + 1)) (Fin (r + 1)) _).map
        (d.extensionGaloisFieldEmbedding 2 two_ne_zero) := (rfl)

end TauCeti.ValidLieTypeIndex

end
