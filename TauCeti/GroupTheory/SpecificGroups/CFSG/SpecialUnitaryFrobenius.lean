/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.FixedSubgroup
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

## Main definitions

* `TauCeti.ValidLieTypeIndex.extensionGaloisFieldEmbedding`: a chosen embedding of the field
  `GaloisField p (e * k)` with `q ^ k` elements into the closure.
* `TauCeti.ValidLieTypeIndex.galoisFieldTwistedFrobenius`: the graph-twisted `q`-power Frobenius of
  `SL_{r+1}(𝔽_{q²})`.
* `TauCeti.ValidLieTypeIndex.specialUnitaryEquivFrobeniusFixedPoints`: the isomorphism between
  its fixed subgroup and the fixed subgroup of the graph-twisted Frobenius over the closure.

## Main results

* `TauCeti.ValidLieTypeIndex.mem_range_extensionGaloisFieldEmbedding_iff`: the image of the
  embedding is the set of solutions of `x ^ (q ^ k) = x`.
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

variable (d : ValidLieTypeIndex)

/-! ### The field with `q ^ k` elements inside the closure -/

/-- **A chosen embedding of the field with `q ^ k` elements into the closure**, for `k ≠ 0`: an
isomorphism from Mathlib's `GaloisField p (e * k)` onto the subfield of the closure fixed by the
`q ^ k`-power Frobenius, followed by the inclusion. A graph-twisted family is realized over the
field with `q ^ k` elements for `k` the order of its diagram automorphism. As for
`TauCeti.ValidLieTypeIndex.galoisFieldEmbedding`, there is no canonical choice, and only its image
matters. -/
def extensionGaloisFieldEmbedding (k : ℕ) (hk : k ≠ 0) :
    GaloisField d.characteristic (d.fieldExponent * k) →+* d.Closure :=
  (frobeniusFixedSubfield d.Closure d.characteristic (d.fieldExponent * k)).subtype.comp
    (Classical.choice (nonempty_frobeniusFixedSubfield_ringEquiv_galoisField d.Closure
      d.characteristic (d.fieldExponent * k)
      (mul_ne_zero d.fieldExponent_pos.ne' hk))).symm.toRingHom

variable {d}

/-- An element of the closure lies in the image of the chosen embedding of the field with `q ^ k`
elements exactly when it is fixed by the `q ^ k`-power map.

This is not a `simp` lemma: `RingHom.mem_range` already unfolds the left-hand side into an
existential, so it is not in `simp`-normal form. -/
theorem mem_range_extensionGaloisFieldEmbedding_iff {k : ℕ} (hk : k ≠ 0) {x : d.Closure} :
    x ∈ (d.extensionGaloisFieldEmbedding k hk).range ↔ x ^ d.fieldOrder ^ k = x := by
  rw [d.fieldOrder_eq_characteristic_pow, ← pow_mul, ← mem_frobeniusFixedSubfield]
  constructor
  · rintro ⟨y, rfl⟩
    exact SetLike.coe_mem _
  · intro hx
    obtain ⟨y, hy⟩ := (Classical.choice (nonempty_frobeniusFixedSubfield_ringEquiv_galoisField
      d.Closure d.characteristic (d.fieldExponent * k)
      (mul_ne_zero d.fieldExponent_pos.ne' hk))).symm.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

/-- A special linear matrix over the closure has coordinates in the field with `q ^ k` elements
exactly when every entry is fixed by the `q ^ k`-power map. -/
theorem specialLinear_mem_range_extensionGaloisFieldEmbedding_iff
    {k : ℕ} (hk : k ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SpecialLinearGroup ι d.Closure) :
    g ∈ (SpecialLinearGroup.map (n := ι) (d.extensionGaloisFieldEmbedding k hk)).range ↔
      ∀ i j, (g i j) ^ d.fieldOrder ^ k = g i j := by
  constructor
  · rintro ⟨g₀, rfl⟩ i j
    exact (mem_range_extensionGaloisFieldEmbedding_iff hk).mp ⟨g₀ i j, rfl⟩
  · intro hg
    choose A hA using fun i j ↦ (mem_range_extensionGaloisFieldEmbedding_iff hk).mpr (hg i j)
    have hmap : (Matrix.of A).map (d.extensionGaloisFieldEmbedding k hk) = g :=
      Matrix.ext hA
    have hdet : (Matrix.of A).det = 1 := by
      apply (d.extensionGaloisFieldEmbedding k hk).injective
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, g.property, map_one]
    exact ⟨⟨Matrix.of A, hdet⟩, Subtype.ext hmap⟩

/-- The coefficient extension of special linear groups along the embedding of the field with
`q ^ k` elements is injective. -/
theorem specialLinear_map_extensionGaloisFieldEmbedding_injective
    {k : ℕ} (hk : k ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective
      (SpecialLinearGroup.map (n := ι) (d.extensionGaloisFieldEmbedding k hk)) :=
  fun _ _ h ↦ Subtype.ext (Matrix.map_injective (RingHom.injective _) (congrArg Subtype.val h))

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
  have hσ : (d.extensionGaloisFieldEmbedding 2 two_ne_zero).comp
        (iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2)) d.characteristic
          d.fieldExponent) =
      (iterateFrobenius d.Closure d.characteristic d.fieldExponent).comp
        (d.extensionGaloisFieldEmbedding 2 two_ne_zero) :=
    RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
  refine MonoidHom.ext fun g ↦ ?_
  simp only [MonoidHom.comp_apply, galoisFieldTwistedFrobenius_apply, MonoidHom.coe_ofClass,
    SpecialLinearGroup.map_typeAGraphAutomorphism]
  rw [← MonoidHom.comp_apply (SpecialLinearGroup.map _), SpecialLinearGroup.map_comp, hσ,
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
  set φ := SpecialLinearGroup.map (n := Fin (r + 1))
    (iterateFrobenius d.Closure d.characteristic d.fieldExponent)
  set θ := SpecialLinearGroup.typeAGraphAutomorphism r d.Closure
  have hg' : θ (φ g) = g := mem_fixedSubgroup.mp hg
  -- `θ` is an involution commuting with `φ`, so `φ (φ g) = θ (φ g) = g`.
  have hφφ : φ (φ g) = g := by
    have h := congrArg (fun x ↦ θ (φ x)) hg'
    simp only [φ, θ, SpecialLinearGroup.map_typeAGraphAutomorphism,
      SpecialLinearGroup.typeAGraphAutomorphism_typeAGraphAutomorphism] at h
    exact h.trans hg'
  rw [specialLinear_mem_range_extensionGaloisFieldEmbedding_iff]
  intro i j
  have h := congrArg (fun x : SpecialLinearGroup (Fin (r + 1)) d.Closure ↦ x i j) hφφ
  simp only [φ, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    iterateFrobenius_def, ← pow_mul, ← d.fieldOrder_eq_characteristic_pow] at h
  rwa [sq]

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
      (specialLinear_map_extensionGaloisFieldEmbedding_injective two_ne_zero),
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
      (specialLinear_map_extensionGaloisFieldEmbedding_injective two_ne_zero)).trans
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
