/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Transporting infinite and real places along an isomorphism of fields

A ring isomorphism `e : K ≃+* L` of fields pushes infinite places forward by pulling back along
`e.symm`, giving a bijection `NumberField.InfinitePlace.equivOfRingEquiv e` between
`InfinitePlace K` and `InfinitePlace L`. Because `e` is an isomorphism, this bijection preserves
real and complex places, multiplicities, and the canonical real embeddings at real places, and
restricts to a bijection `NumberField.InfinitePlace.realEquivOfRingEquiv e` between the subtypes of
real places.

Both constructions are functorial in `e` and require no number-field hypothesis on `K` or `L`. In
particular, they identify the infinite and real places of a field with those of any isomorphic copy
in another universe, such as `Shrink K`.

## Main definitions

* `NumberField.InfinitePlace.equivOfRingEquiv`: the bijection `InfinitePlace K ≃ InfinitePlace L`
  induced by `e : K ≃+* L`.
* `NumberField.InfinitePlace.realEquivOfRingEquiv`: the induced bijection
  `{w : InfinitePlace K // w.IsReal} ≃ {w : InfinitePlace L // w.IsReal}` on real places.

## Main results

* `NumberField.InfinitePlace.equivOfRingEquiv_apply`,
  `NumberField.InfinitePlace.equivOfRingEquiv_mk`: evaluation of the transported place and
  compatibility with `InfinitePlace.mk`.
* `NumberField.InfinitePlace.equivOfRingEquiv_refl_apply`,
  `NumberField.InfinitePlace.equivOfRingEquiv_refl`,
  `NumberField.InfinitePlace.equivOfRingEquiv_symm`,
  `NumberField.InfinitePlace.equivOfRingEquiv_trans_apply`,
  `NumberField.InfinitePlace.equivOfRingEquiv_trans`: functoriality on elements and as bundled
  bijections.
* `NumberField.InfinitePlace.isReal_equivOfRingEquiv_iff`,
  `NumberField.InfinitePlace.isComplex_equivOfRingEquiv_iff`,
  `NumberField.InfinitePlace.mult_equivOfRingEquiv`: preservation of realness, complexity, and
  multiplicity.
* `NumberField.InfinitePlace.embedding_of_isReal_equivOfRingEquiv`: the real embedding of the
  transported place is the real embedding of the original place composed with `e.symm`.
* `NumberField.InfinitePlace.realEquivOfRingEquiv_refl_apply`,
  `NumberField.InfinitePlace.realEquivOfRingEquiv_refl`,
  `NumberField.InfinitePlace.realEquivOfRingEquiv_symm`,
  `NumberField.InfinitePlace.realEquivOfRingEquiv_trans_apply`,
  `NumberField.InfinitePlace.realEquivOfRingEquiv_trans`: functoriality of `realEquivOfRingEquiv`.
-/

public section

namespace NumberField.InfinitePlace

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- The bijection between the infinite places of two fields induced by a ring isomorphism
`e : K ≃+* L`, sending `w` to `w.comap e.symm`. -/
def equivOfRingEquiv (e : K ≃+* L) : InfinitePlace K ≃ InfinitePlace L where
  toFun w := w.comap (e.symm : L →+* K)
  invFun w := w.comap (e : K →+* L)
  left_inv w := by
    dsimp only
    rw [← comap_comp]
    convert w.comap_id
    ext x
    exact e.symm_apply_apply x
  right_inv w := by
    dsimp only
    rw [← comap_comp]
    convert w.comap_id
    ext x
    exact e.apply_symm_apply x

-- Not `@[simp]`: unfolding `equivOfRingEquiv` to `comap` would take the `equivOfRingEquiv_*`
-- lemmas out of simp normal form.
/-- `equivOfRingEquiv e` sends an infinite place `w` to `w.comap e.symm`. -/
theorem equivOfRingEquiv_eq_comap (e : K ≃+* L) (w : InfinitePlace K) :
    equivOfRingEquiv e w = w.comap (e.symm : L →+* K) :=
  (rfl)

/-- Evaluating `equivOfRingEquiv e w` at `x : L` evaluates `w` at `e.symm x`. -/
@[simp]
theorem equivOfRingEquiv_apply (e : K ≃+* L) (w : InfinitePlace K) (x : L) :
    equivOfRingEquiv e w x = w (e.symm x) := by
  rw [equivOfRingEquiv_eq_comap, comap_apply, RingHom.coe_coe]

/-- Transporting the infinite place of a complex embedding `φ : K →+* ℂ` along `e : K ≃+* L` gives
the infinite place of `φ ∘ e.symm`. -/
@[simp]
theorem equivOfRingEquiv_mk (e : K ≃+* L) (φ : K →+* ℂ) :
    equivOfRingEquiv e (mk φ) = mk (φ.comp (e.symm : L →+* K)) := by
  rw [equivOfRingEquiv_eq_comap, comap_mk]

/-- The identity ring isomorphism induces the identity on infinite places. -/
@[simp]
theorem equivOfRingEquiv_refl_apply (w : InfinitePlace K) :
    equivOfRingEquiv (RingEquiv.refl K) w = w :=
  w.comap_id

-- Not `@[simp]`: `equivOfRingEquiv_refl_apply` is the simp form.
/-- The identity ring isomorphism induces `Equiv.refl` on `InfinitePlace K`. -/
theorem equivOfRingEquiv_refl :
    equivOfRingEquiv (RingEquiv.refl K) = Equiv.refl (InfinitePlace K) :=
  Equiv.ext equivOfRingEquiv_refl_apply

/-- Inverting the ring isomorphism inverts the induced bijection of infinite places. -/
@[simp]
theorem equivOfRingEquiv_symm (e : K ≃+* L) :
    (equivOfRingEquiv e).symm = equivOfRingEquiv e.symm :=
  Equiv.ext fun _ ↦ rfl

/-- Transporting an infinite place along `e` and then `e'` is transporting along `e.trans e'`. -/
@[simp]
theorem equivOfRingEquiv_trans_apply (e : K ≃+* L) (e' : L ≃+* M) (w : InfinitePlace K) :
    equivOfRingEquiv e' (equivOfRingEquiv e w) = equivOfRingEquiv (e.trans e') w := by
  rw [equivOfRingEquiv_eq_comap, equivOfRingEquiv_eq_comap, equivOfRingEquiv_eq_comap, ← comap_comp]
  rfl

-- Not `@[simp]`: `equivOfRingEquiv_trans_apply` is the simp form, rewriting in the opposite
-- direction.
/-- Transporting infinite places commutes with composing ring isomorphisms. -/
theorem equivOfRingEquiv_trans (e : K ≃+* L) (e' : L ≃+* M) :
    equivOfRingEquiv (e.trans e') = (equivOfRingEquiv e).trans (equivOfRingEquiv e') :=
  Equiv.ext fun w ↦ (equivOfRingEquiv_trans_apply e e' w).symm

/-- Transport along a ring isomorphism preserves realness of infinite places. -/
@[simp]
theorem isReal_equivOfRingEquiv_iff (e : K ≃+* L) (w : InfinitePlace K) :
    (equivOfRingEquiv e w).IsReal ↔ w.IsReal := by
  rw [equivOfRingEquiv_eq_comap]
  exact isReal_comap_iff e.symm

/-- Transport along a ring isomorphism preserves complexity of infinite places. -/
@[simp]
theorem isComplex_equivOfRingEquiv_iff (e : K ≃+* L) (w : InfinitePlace K) :
    (equivOfRingEquiv e w).IsComplex ↔ w.IsComplex := by
  rw [← not_isReal_iff_isComplex, ← not_isReal_iff_isComplex, isReal_equivOfRingEquiv_iff]

/-- Transport along a ring isomorphism preserves the multiplicity of an infinite place. -/
@[simp]
theorem mult_equivOfRingEquiv (e : K ≃+* L) (w : InfinitePlace K) :
    (equivOfRingEquiv e w).mult = w.mult := by
  by_cases hw : w.IsReal <;> simp [mult, hw]

/-- The real embedding of a real place transported along `e : K ≃+* L` is the real embedding of the
original place composed with `e.symm`. -/
@[simp]
theorem embedding_of_isReal_equivOfRingEquiv (e : K ≃+* L) {w : InfinitePlace K}
    (hw : (equivOfRingEquiv e w).IsReal) :
    embedding_of_isReal hw =
      (embedding_of_isReal ((isReal_equivOfRingEquiv_iff e w).mp hw)).comp (e.symm : L →+* K) :=
  embedding_of_isReal_comap (e.symm : L →+* K) ((isReal_equivOfRingEquiv_iff e w).mp hw)

/-- The bijection between the real places of two fields induced by a ring isomorphism
`e : K ≃+* L`. -/
def realEquivOfRingEquiv (e : K ≃+* L) :
    {w : InfinitePlace K // w.IsReal} ≃ {w : InfinitePlace L // w.IsReal} :=
  (equivOfRingEquiv e).subtypeEquiv fun w ↦ (isReal_equivOfRingEquiv_iff e w).symm

/-- The underlying infinite place of `realEquivOfRingEquiv e w` is `equivOfRingEquiv e w`. -/
@[simp]
theorem coe_realEquivOfRingEquiv (e : K ≃+* L) (w : {w : InfinitePlace K // w.IsReal}) :
    (realEquivOfRingEquiv e w : InfinitePlace L) = equivOfRingEquiv e w :=
  (rfl)

/-- The identity ring isomorphism induces the identity on real places. -/
@[simp]
theorem realEquivOfRingEquiv_refl_apply (w : {w : InfinitePlace K // w.IsReal}) :
    realEquivOfRingEquiv (RingEquiv.refl K) w = w :=
  Subtype.ext (equivOfRingEquiv_refl_apply w.1)

-- Not `@[simp]`: `realEquivOfRingEquiv_refl_apply` is the simp form.
/-- The identity ring isomorphism induces `Equiv.refl` on the real places of `K`. -/
theorem realEquivOfRingEquiv_refl :
    realEquivOfRingEquiv (RingEquiv.refl K) = Equiv.refl {w : InfinitePlace K // w.IsReal} :=
  Equiv.ext realEquivOfRingEquiv_refl_apply

/-- Inverting the ring isomorphism inverts the induced bijection of real places. -/
@[simp]
theorem realEquivOfRingEquiv_symm (e : K ≃+* L) :
    (realEquivOfRingEquiv e).symm = realEquivOfRingEquiv e.symm :=
  Equiv.ext fun w ↦ Subtype.ext <| by
    rw [coe_realEquivOfRingEquiv, ← equivOfRingEquiv_symm]
    rfl

/-- Transporting a real place along `e` and then `e'` is transporting along `e.trans e'`. -/
@[simp]
theorem realEquivOfRingEquiv_trans_apply (e : K ≃+* L) (e' : L ≃+* M)
    (w : {w : InfinitePlace K // w.IsReal}) :
    realEquivOfRingEquiv e' (realEquivOfRingEquiv e w) = realEquivOfRingEquiv (e.trans e') w :=
  Subtype.ext (equivOfRingEquiv_trans_apply e e' w.1)

-- Not `@[simp]`: `realEquivOfRingEquiv_trans_apply` is the simp form, rewriting in the opposite
-- direction.
/-- Transporting real places commutes with composing ring isomorphisms. -/
theorem realEquivOfRingEquiv_trans (e : K ≃+* L) (e' : L ≃+* M) :
    realEquivOfRingEquiv (e.trans e') =
      (realEquivOfRingEquiv e).trans (realEquivOfRingEquiv e') :=
  Equiv.ext fun w ↦ (realEquivOfRingEquiv_trans_apply e e' w).symm

end NumberField.InfinitePlace
