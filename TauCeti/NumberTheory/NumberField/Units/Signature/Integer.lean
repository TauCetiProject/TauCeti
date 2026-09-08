/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Ring.Units
public import TauCeti.NumberTheory.NumberField.Units.Signature.Surjective

/-!
# The total sign homomorphism of a number field, valued in `ℤˣ`

`NumberField.fieldUnitSignature` records the sign of a field unit of `K` at each real place as a
class in `ℝˣ ⧸ Units.posSubgroup ℝ`.  Transporting each of those classes along the sign isomorphism
`Units.signEquiv` gives the same data in the concrete two-element group `ℤˣ`:

```text
signHom : Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℤˣ).
```

This is the archimedean half of a multiplicative congruence in group-theoretic form: `x` is
totally positive exactly when `signHom x = 1`.  There is no second sign homomorphism here — this is
`NumberField.fieldUnitSignature` read in `ℤˣ`, and the two are interchangeable through
`Units.signEquiv`.

Surjectivity of `signHom` is not formal — it is weak approximation at the real places, and is
inherited from `NumberField.fieldUnitSignature_surjective`.  The composite
`(𝓞 K)ˣ → Kˣ → ({w // w.IsReal} → ℤˣ)` need *not* be surjective, and its failure to be so is
exactly the obstruction that separates the narrow class group from the wide one; nothing here
asserts otherwise.

## Main definitions

* `TauCeti.GlobalNumberFields.signHom`: the total sign homomorphism, valued in `ℤˣ`.

## Main results

* `TauCeti.GlobalNumberFields.signHom_apply_eq_one_iff` and
  `TauCeti.GlobalNumberFields.signHom_apply_eq_neg_one_iff`: the two possible signs, read off as
  positivity and negativity of the real embedding.
* `TauCeti.GlobalNumberFields.signHom_eq_one_iff`: an element lies in the kernel exactly when it
  is totally positive.
* `TauCeti.GlobalNumberFields.signHom_surjective`: every pattern of signs at the real places is
  realized by a field unit of `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K]

/-- **The total sign homomorphism of a number field**: the signs of a field unit of `K` at all of
the real places at once, valued in the product of copies of `ℤˣ` indexed by those places.

It is `NumberField.fieldUnitSignature` with each component read through the sign isomorphism
`Units.signEquiv`, so it carries exactly the same information.

The domain is `Kˣ` rather than `K`, so that every value really is a sign: a formulation on `K`
would have to invent a sign for `0`. -/
noncomputable def signHom : Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℤˣ) :=
  (MulEquiv.piCongrRight fun _ : {w : InfinitePlace K // w.IsReal} =>
    Units.signEquiv ℝ).toMonoidHom.comp fieldUnitSignature

/-- Componentwise evaluation of the total sign homomorphism. -/
@[simp] theorem signHom_apply (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = Units.signEquiv ℝ (fieldUnitSignature x w) := (rfl)

/-- **A sign is `1` exactly at a positive element.** -/
theorem signHom_apply_eq_one_iff (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = 1 ↔ 0 < embedding_of_isReal w.2 (x : K) := by
  rw [signHom_apply, fieldUnitSignature_apply, Units.signEquiv_mk_eq_one_iff]
  simp

/-- **A sign is `-1` exactly at a negative element.** -/
theorem signHom_apply_eq_neg_one_iff (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = -1 ↔ embedding_of_isReal w.2 (x : K) < 0 := by
  rw [signHom_apply, fieldUnitSignature_apply, Units.signEquiv_mk_eq_neg_one_iff]
  simp

/-- **The kernel of the total sign homomorphism is the totally positive elements.** -/
@[simp] theorem signHom_eq_one_iff (x : Kˣ) : signHom x = 1 ↔ IsTotallyPositive (x : K) := by
  rw [← fieldUnitSignature_eq_one_iff, funext_iff, funext_iff]
  exact forall_congr' fun w => by
    rw [Pi.one_apply, Pi.one_apply, signHom_apply,
      map_eq_one_iff _ (Units.signEquiv ℝ).injective]

/-- **The total sign homomorphism is surjective on `Kˣ`.**  Every pattern of signs at the real
places of `K` is realized by an element of `Kˣ`.

This is `NumberField.fieldUnitSignature_surjective` read in `ℤˣ`.  Surjectivity fails in general
after restricting along `(𝓞 K)ˣ → Kˣ`, and that failure is the obstruction which separates the
narrow class group of `K` from the wide one; nothing here bears on the restricted map. -/
theorem signHom_surjective [NumberField K] : Function.Surjective (signHom (K := K)) := fun s => by
  exact (MulEquiv.piCongrRight fun _ : {w : InfinitePlace K // w.IsReal} =>
    Units.signEquiv ℝ).surjective.comp NumberField.fieldUnitSignature_surjective s

end TauCeti.GlobalNumberFields
