/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Over

/-!
# Transporting ideals of a ring of integers along an isomorphism of fields

An isomorphism of fields `e : K ≃+* L` restricts to `NumberField.RingOfIntegers.mapRingEquiv e`
between the rings of integers, and pulling ideals back along it identifies the ideals of `𝓞 L`
with those of `𝓞 K`.  This file records that this identification is functorial and reflects the
zero ideal, which is what a construction transported along `e` needs in order to be well defined
on nonzero ideals. If `e` carries a subfield `A` of `K` onto a subfield `B` of `L`, it also
restricts to an isomorphism `𝓞 A ≃+* 𝓞 B` compatible with `mapRingEquiv e`, along which the ideal
of `𝓞 A` under an ideal of `𝓞 K` is carried to the ideal of `𝓞 B` under its image.

## Main results

* `NumberField.RingOfIntegers.mapAlgHom_apply`, `NumberField.RingOfIntegers.mapAlgHom_injective`:
  evaluation and injectivity of `mapAlgHom`.
* `NumberField.RingOfIntegers.mapRingEquiv_refl_apply`,
  `NumberField.RingOfIntegers.mapRingEquiv_trans_apply`: functoriality on elements.
* `NumberField.RingOfIntegers.mapRingEquiv_refl`, `NumberField.RingOfIntegers.mapRingEquiv_symm`,
  `NumberField.RingOfIntegers.mapRingEquiv_trans`: the same functoriality for the bundled
  isomorphisms, including inverses.
* `NumberField.RingOfIntegers.ringEquivOfRingEquiv_mapRingEquiv`: extending `mapRingEquiv e` from
  the rings of integers back to their fraction fields recovers `e`.
* `NumberField.RingOfIntegers.subfieldMapRingEquiv`: the isomorphism `𝓞 A ≃+* 𝓞 B` induced by `e`
  when it carries a subfield `A` onto a subfield `B`, with
  `NumberField.RingOfIntegers.algebraMap_subfieldMapRingEquiv` (compatibility with
  `mapRingEquiv e`) and `NumberField.RingOfIntegers.subfieldMapRingEquiv_symm`.
* `Ideal.under_map_mapRingEquiv`: the ideal of `𝓞 B` under the image of `P` is the image of the
  ideal of `𝓞 A` under `P`.
* `Ideal.comap_mapRingEquiv_refl`, `Ideal.comap_mapRingEquiv_trans`: functoriality on ideals.
* `Ideal.comap_mapRingEquiv_eq_bot_iff`: the pullback is the zero ideal only for the zero ideal.
-/

public section

namespace NumberField.RingOfIntegers

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- Restricting an algebra homomorphism `f : K →ₐ[k] L` to rings of integers acts as `f` on
underlying field elements. -/
@[simp]
theorem mapAlgHom_apply {k F : Type*} [Field k] [Algebra k K] [Algebra k L]
    [FunLike F K L] [AlgHomClass F k K L] (f : F) (x : 𝓞 K) :
    (mapAlgHom f x : L) = f (x : K) :=
  (rfl)

/-- Restricting an algebra homomorphism of fields to rings of integers yields an injective map. -/
theorem mapAlgHom_injective {k F : Type*} [Field k] [Algebra k K] [Algebra k L]
    [FunLike F K L] [AlgHomClass F k K L] (f : F) :
    Function.Injective (mapAlgHom f) :=
  fun _ _ h ↦ RingOfIntegers.ext <| (RingHomClass.toRingHom f).injective <| by
    simpa only [RingOfIntegers.ext_iff, mapAlgHom_apply, RingHom.coe_coe] using h

/-- The identity isomorphism of fields restricts to the identity on integers. -/
@[simp]
theorem mapRingEquiv_refl_apply (x : 𝓞 K) : mapRingEquiv (RingEquiv.refl K) x = x :=
  RingOfIntegers.ext rfl

/-- Restricting to integers is compatible with composing isomorphisms of fields. -/
@[simp]
theorem mapRingEquiv_trans_apply (e : K ≃+* L) (e' : L ≃+* M) (x : 𝓞 K) :
    mapRingEquiv e' (mapRingEquiv e x) = mapRingEquiv (e.trans e') x :=
  RingOfIntegers.ext rfl

/-- The identity isomorphism of fields restricts to the identity isomorphism of the ring of
integers. This is not a simp lemma: `mapRingEquiv_refl_apply` is the simp form, and rewriting the
bundled isomorphism would take `Ideal.comap_mapRingEquiv_refl` out of simp normal form. -/
theorem mapRingEquiv_refl : mapRingEquiv (RingEquiv.refl K) = RingEquiv.refl (𝓞 K) :=
  RingEquiv.ext mapRingEquiv_refl_apply

/-- Restricting to integers commutes with inverting an isomorphism of fields. -/
@[simp]
theorem mapRingEquiv_symm (e : K ≃+* L) : (mapRingEquiv e).symm = mapRingEquiv e.symm :=
  RingEquiv.ext fun _ ↦ RingOfIntegers.ext rfl

/-- Restricting to integers is compatible with composing isomorphisms of fields, as bundled
isomorphisms. This is not a simp lemma: `mapRingEquiv_trans_apply` is the simp form, which
rewrites in the opposite direction. -/
theorem mapRingEquiv_trans (e : K ≃+* L) (e' : L ≃+* M) :
    mapRingEquiv (e.trans e') = (mapRingEquiv e).trans (mapRingEquiv e') :=
  RingEquiv.ext fun x ↦ (mapRingEquiv_trans_apply e e' x).symm

/-- Extending `mapRingEquiv e` from the rings of integers back to their fraction fields recovers
`e`. -/
@[simp]
theorem ringEquivOfRingEquiv_mapRingEquiv [IsFractionRing (𝓞 K) K] [IsFractionRing (𝓞 L) L]
    (e : K ≃+* L) :
    IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) (mapRingEquiv e) = e := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) ?_
  ext x
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := K) (L := L) (mapRingEquiv e) x

/-- The isomorphism of rings of integers of subfields `A` of `K` and `B` of `L` induced by an
isomorphism `e : K ≃+* L` carrying `A` onto `B`. -/
noncomputable def subfieldMapRingEquiv (e : K ≃+* L) {A : Subfield K} {B : Subfield L}
    (h : A.map (e : K →+* L) = B) : 𝓞 A ≃+* 𝓞 B :=
  mapRingEquiv <| e.restrict A B fun x ↦ by
    rw [← h, Subfield.mem_map]
    exact ⟨fun hx ↦ ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ ↦ e.injective hyx ▸ hy⟩

/-- `subfieldMapRingEquiv e h` acts as `e` on underlying field elements. -/
@[simp]
theorem subfieldMapRingEquiv_apply (e : K ≃+* L) {A : Subfield K} {B : Subfield L}
    (h : A.map (e : K →+* L) = B) (x : 𝓞 A) :
    ((subfieldMapRingEquiv e h x : B) : L) = e ((x : A) : K) :=
  (rfl)

/-- `subfieldMapRingEquiv e h` is compatible with `mapRingEquiv e` along the inclusions of the
rings of integers of the subfields. -/
@[simp]
theorem algebraMap_subfieldMapRingEquiv (e : K ≃+* L) {A : Subfield K} {B : Subfield L}
    (h : A.map (e : K →+* L) = B) (x : 𝓞 A) :
    algebraMap (𝓞 B) (𝓞 L) (subfieldMapRingEquiv e h x) =
      mapRingEquiv e (algebraMap (𝓞 A) (𝓞 K) x) :=
  (rfl)

/-- The inverse of `subfieldMapRingEquiv e h` is the same construction for `e.symm`. -/
theorem subfieldMapRingEquiv_symm (e : K ≃+* L) {A : Subfield K} {B : Subfield L}
    (h : A.map (e : K →+* L) = B) (h' : B.map (e.symm : L →+* K) = A) :
    (subfieldMapRingEquiv e h).symm = subfieldMapRingEquiv e.symm h' :=
  RingEquiv.ext fun _ ↦ RingOfIntegers.ext rfl

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

/-- If `e : K ≃+* L` carries a subfield `A` onto a subfield `B`, the ideal of `𝓞 B` under the
image of an ideal `P` of `𝓞 K` is the image of the ideal of `𝓞 A` under `P`. -/
theorem under_map_mapRingEquiv (e : K ≃+* L) {A : Subfield K} {B : Subfield L}
    (h : A.map (e : K →+* L) = B) (P : Ideal (𝓞 K)) :
    (P.map (RingOfIntegers.mapRingEquiv e)).under (𝓞 B) =
      (P.under (𝓞 A)).map (RingOfIntegers.subfieldMapRingEquiv e h) := by
  ext y
  obtain ⟨x, rfl⟩ := (RingOfIntegers.subfieldMapRingEquiv e h).surjective y
  rw [Ideal.apply_mem_of_equiv_iff, Ideal.mem_under, Ideal.mem_under,
    RingOfIntegers.algebraMap_subfieldMapRingEquiv, Ideal.apply_mem_of_equiv_iff]

end Ideal
