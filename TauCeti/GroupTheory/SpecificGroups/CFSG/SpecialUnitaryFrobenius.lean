/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialLinearFrobenius
public import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.GraphAutomorphism
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic

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
skew-Hermitian otherwise. It is `TauCeti.ValidLieTypeIndex.unitaryForm`, Mathlib's sesquilinear map
`Matrix.toLinearMapₛₗ₂'` of Gram matrix `Q`, and `SU_{r+1}(q)` preserves it.

The field with `q²` elements and its embedding come from `CFSG/Frobenius.lean`, and the entrywise
description of the special linear matrices with coordinates in it from
`CFSG/SpecialLinearFrobenius.lean`. The square relation for the twisted Frobenius is
`Matrix.SpecialLinearGroup.typeAGraphAutomorphism_comp_map_comp_self`.

## Main definitions

* `TauCeti.ValidLieTypeIndex.galoisFieldTwistedFrobenius`: the graph-twisted `q`-power Frobenius of
  `SL_{r+1}(𝔽_{q²})`.
* `TauCeti.ValidLieTypeIndex.unitaryForm`: the form `B(x, y) = σ(x)ᵀ Q y` of `SU_{r+1}(q)`, with
  `σ : x ↦ x ^ q`.
* `TauCeti.ValidLieTypeIndex.specialUnitaryEquivFrobeniusFixedPoints`: the isomorphism between
  its fixed subgroup and the fixed subgroup of the graph-twisted Frobenius over the closure.

## Main results

* `TauCeti.ValidLieTypeIndex.coe_iterateFrobenius_galoisField`: the `q`-power Frobenius of the
  field with `q²` elements is `x ↦ x ^ q`.
* `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff`: the finite fixed
  points are the isometries of determinant one of the form of Gram matrix `Q`.
* `TauCeti.ValidLieTypeIndex.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup`:
  the same statement as an equality with the special isometry group `Matrix.specialIsometryGroup`.
* `TauCeti.ValidLieTypeIndex.unitaryForm_apply`: the form is the dot product `σ(x) ⬝ᵥ (Q y)`.
* `TauCeti.ValidLieTypeIndex.unitaryForm_smul_left`: semilinearity in the first argument,
  `B(c x, y) = c ^ q B(x, y)`.
* `TauCeti.ValidLieTypeIndex.unitaryForm_swap`: the form is `(-1) ^ r`-Hermitian.
* `TauCeti.ValidLieTypeIndex.unitaryForm_mulVec_mulVec`: `SU_{r+1}(q)` preserves the form.
* `TauCeti.ValidLieTypeIndex.unitaryForm_single_single`: the coordinate vectors off the middle
  coordinate are isotropic.
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

/-- The `q`-power Frobenius of the field with `q²` elements, which the graph-twisted Frobenius
applies entrywise, is `x ↦ x ^ q`. -/
@[simp]
theorem coe_iterateFrobenius_galoisField :
    ⇑(iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
      d.fieldExponent) = (· ^ d.fieldOrder) :=
  funext fun x ↦ by rw [iterateFrobenius_def, d.fieldOrder_eq_characteristic_pow]

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
  rw [mem_fixedSubgroup, galoisFieldTwistedFrobenius_apply,
    ← SpecialLinearGroup.toGL_injective.eq_iff, SpecialLinearGroup.toGL_typeAGraphAutomorphism,
    typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq,
    SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_iterateFrobenius_galoisField]

/-- **The finite special unitary group is a special isometry group.** The fixed points of the
graph-twisted Frobenius of `SL_{r+1}(𝔽_{q²})` are the special isometries of the sesquilinear form
of Gram matrix `Q` relative to the involution `x ↦ x ^ q`, with `Q` the signed reversal matrix.
Since `Qᵀ = (-1) ^ r • Q` (`TauCeti.transpose_typeAGraphConjugator`), this form is
`(-1) ^ r`-Hermitian. -/
theorem fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup (r : ℕ) :
    fixedSubgroup (d.galoisFieldTwistedFrobenius r) =
      (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
          Matrix (Fin (r + 1)) (Fin (r + 1))
            (GaloisField d.characteristic (d.fieldExponent * 2))).specialIsometryGroup
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
          d.fieldExponent) := by
  ext g
  rw [mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff, Matrix.mem_specialIsometryGroup_iff,
    coe_iterateFrobenius_galoisField]

/-! ### The unitary form -/

section UnitaryForm

variable {r : ℕ}

/-- The `q`-power Frobenius `σ` of the field with `q²` elements is an involution, an instance of
`TauCeti.FiniteField.iterateFrobenius_involutive`. -/
theorem involutive_iterateFrobenius_galoisField :
    Function.Involutive (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
      d.characteristic d.fieldExponent) :=
  FiniteField.iterateFrobenius_involutive
    (GaloisField.card _ _ (Nat.mul_ne_zero d.fieldExponent_pos.ne' two_ne_zero))

/-- The entries `0` and `±1` of the signed reversal matrix `Q` are fixed by `σ`. -/
private theorem map_typeAGraphConjugator_galoisField :
    (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _).map
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
          d.fieldExponent) =
      (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _) := by
  have hmap := congrArg Units.val (map_typeAGraphConjugator
    (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
      d.fieldExponent) r)
  rwa [Units.coe_map, MonoidHom.coe_ofClass, RingHom.mapMatrix_apply] at hmap

/-- The `σ`-sesquilinear form of Gram matrix `Q` is `(-1) ^ r`-Hermitian: `σ(Q)ᵀ = (-1) ^ r • Q`,
with `σ` the `q`-power Frobenius and `Q` the signed reversal matrix. -/
theorem transpose_map_typeAGraphConjugator_galoisField :
    ((typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _).map
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
          d.fieldExponent))ᵀ =
      (-1 : GaloisField d.characteristic (d.fieldExponent * 2)) ^ r •
        (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) _) := by
  rw [map_typeAGraphConjugator_galoisField, transpose_typeAGraphConjugator]

variable (d r) in
/-- **The form of the special unitary group** `SU_{r+1}(q)`: the sesquilinear form
`B(x, y) = σ(x)ᵀ Q y` on `𝔽_{q²} ^ (r + 1)`, with `σ : x ↦ x ^ q` and `Q` the signed reversal
matrix, as Mathlib's sesquilinear map `Matrix.toLinearMapₛₗ₂'` of Gram matrix `Q`. It is
`σ`-semilinear in `x` and linear in `y`, and `B(y, x) = (-1) ^ r σ(B(x, y))`
(`TauCeti.ValidLieTypeIndex.unitaryForm_swap`). -/
def unitaryForm :
    (Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2))
      →ₛₗ[iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
        d.fieldExponent]
      (Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2))
        →ₗ[GaloisField d.characteristic (d.fieldExponent * 2)]
        GaloisField d.characteristic (d.fieldExponent * 2) :=
  toLinearMapₛₗ₂' (GaloisField d.characteristic (d.fieldExponent * 2))
    (iterateFrobenius _ d.characteristic d.fieldExponent) (RingHom.id _)
    (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (GaloisField d.characteristic (d.fieldExponent * 2)))

/-- The form is the dot product `B(x, y) = σ(x) ⬝ᵥ (Q y)`. -/
theorem unitaryForm_apply
    (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r x y =
      (iterateFrobenius _ d.characteristic d.fieldExponent ∘ x) ⬝ᵥ
        ((typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ y) := by
  simp only [unitaryForm, toLinearMapₛₗ₂'_apply, dotProduct, mulVec, Finset.mul_sum,
    Function.comp_apply, RingHom.id_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **The form is `(-1) ^ r`-Hermitian**: `B(y, x) = (-1) ^ r B(x, y) ^ q`. -/
theorem unitaryForm_swap (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r y x = (-1) ^ r * unitaryForm d r x y ^ d.fieldOrder := by
  have hσ := apply_comp_dotProduct_mulVec involutive_iterateFrobenius_galoisField
    transpose_map_typeAGraphConjugator_galoisField x y
  rw [← unitaryForm_apply, ← unitaryForm_apply, coe_iterateFrobenius_galoisField] at hσ
  beta_reduce at hσ
  rw [hσ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- An element `g` of `SU_{r+1}(q)` satisfies `σ(g)ᵀ Q g = Q`, with `σ` the `q`-power Frobenius:
`mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff` with `σ` in place of `x ↦ x ^ q`. -/
theorem transpose_map_mul_mul_self_of_mem
    (g : fixedSubgroup (d.galoisFieldTwistedFrobenius r)) :
    ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _).map
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
          d.fieldExponent))ᵀ *
        (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) _) * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) =
      (typeAGraphConjugator r (GaloisField d.characteristic (d.fieldExponent * 2)) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) _) := by
  rw [coe_iterateFrobenius_galoisField, ← mem_fixedSubgroup_galoisFieldTwistedFrobenius_iff]
  exact g.2

/-- **The special unitary group preserves its form**: `B(g x, g y) = B(x, y)` for every `g` in
`SU_{r+1}(q)`. -/
@[simp]
theorem unitaryForm_mulVec_mulVec (g : fixedSubgroup (d.galoisFieldTwistedFrobenius r))
    (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ x)
        ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) _) *ᵥ y) =
      unitaryForm d r x y := by
  rw [unitaryForm_apply, unitaryForm_apply]
  exact comp_mulVec_dotProduct_mulVec_mulVec (transpose_map_mul_mul_self_of_mem g) x y

/-- The form is semilinear in its first argument: `B(c x, y) = c ^ q B(x, y)`. -/
theorem unitaryForm_smul_left (c : GaloisField d.characteristic (d.fieldExponent * 2))
    (x y : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2)) :
    unitaryForm d r (c • x) y = c ^ d.fieldOrder * unitaryForm d r x y := by
  rw [LinearMap.map_smulₛₗ₂, coe_iterateFrobenius_galoisField, smul_eq_mul]

/-- **Isotropic coordinate vectors.** The coordinate vector `eᵢ` is isotropic for the form
`B(x, y) = σ(x)ᵀ Q y` unless `i` is the middle coordinate `i = r - i`: the entry `Qᵢᵢ` vanishes off
the anti-diagonal. -/
theorem unitaryForm_single_single {i : Fin (r + 1)} (hi : i ≠ i.rev) :
    unitaryForm d r (Pi.single i 1) (Pi.single i 1) = 0 := by
  rw [unitaryForm, toLinearMapₛₗ₂'_single, typeAGraphConjugator_apply]
  simp only [hi, ↓reduceIte]

end UnitaryForm

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
