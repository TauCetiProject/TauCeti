/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Transporting ideals of a ring of integers along an isomorphism of fields

An isomorphism of fields `e : K ≃+* L` restricts to `NumberField.RingOfIntegers.mapRingEquiv e`
between the rings of integers, and pulling ideals back along it identifies the ideals of `𝓞 L`
with those of `𝓞 K`.  This file records that this identification is functorial and reflects the
zero ideal, which is what a construction transported along `e` needs in order to be well defined
on nonzero ideals.

## Main results

* `NumberField.RingOfIntegers.mapRingEquiv_refl_apply`,
  `NumberField.RingOfIntegers.mapRingEquiv_trans_apply`: functoriality on elements.
* `Ideal.comap_mapRingEquiv_refl`, `Ideal.comap_mapRingEquiv_trans`: functoriality on ideals.
* `Ideal.comap_mapRingEquiv_eq_bot_iff`: the pullback is the zero ideal only for the zero ideal.
-/

public section

namespace NumberField.RingOfIntegers

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- The identity isomorphism of fields restricts to the identity on integers. -/
@[simp]
theorem mapRingEquiv_refl_apply (x : 𝓞 K) : mapRingEquiv (RingEquiv.refl K) x = x :=
  RingOfIntegers.ext rfl

/-- Restricting to integers is compatible with composing isomorphisms of fields. -/
@[simp]
theorem mapRingEquiv_trans_apply (e : K ≃+* L) (e' : L ≃+* M) (x : 𝓞 K) :
    mapRingEquiv e' (mapRingEquiv e x) = mapRingEquiv (e.trans e') x :=
  RingOfIntegers.ext rfl

end NumberField.RingOfIntegers

namespace Ideal

open NumberField

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- Pulling back along the identity isomorphism is the identity on ideals. -/
@[simp]
theorem comap_mapRingEquiv_refl (I : Ideal (𝓞 K)) :
    Ideal.comap (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)) I = I := by
  ext x
  rw [Ideal.mem_comap, RingOfIntegers.mapRingEquiv_refl_apply]

/-- Pulling back along `e` and then `e'` is pulling back along `e.trans e'`. -/
@[simp]
theorem comap_mapRingEquiv_trans (I : Ideal (𝓞 M)) (e : K ≃+* L) (e' : L ≃+* M) :
    Ideal.comap (RingOfIntegers.mapRingEquiv e)
        (Ideal.comap (RingOfIntegers.mapRingEquiv e') I) =
      Ideal.comap (RingOfIntegers.mapRingEquiv (e.trans e')) I :=
  (Ideal.comap_comap (RingOfIntegers.mapRingEquiv e : 𝓞 K →+* 𝓞 L)
    (RingOfIntegers.mapRingEquiv e' : 𝓞 L →+* 𝓞 M)).trans
    (congrArg (Ideal.comap · I) (RingHom.ext (RingOfIntegers.mapRingEquiv_trans_apply e e')))

/-- The pullback of an ideal along an isomorphism of fields is the zero ideal exactly when the
ideal is.  This is what keeps a transported construction on the nonzero ideals. -/
@[simp]
theorem comap_mapRingEquiv_eq_bot_iff (I : Ideal (𝓞 L)) (e : K ≃+* L) :
    Ideal.comap (RingOfIntegers.mapRingEquiv e) I = ⊥ ↔ I = ⊥ := by
  rw [← Ideal.map_symm]
  exact Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).symm.injective

end Ideal
