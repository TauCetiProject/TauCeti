/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field
import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.HilbertTower
import TauCeti.NumberTheory.NumberField.Global.Ideles.IdealExtension
import TauCeti.RingTheory.ClassGroup.Extension

/-!
# The Principal Ideal Theorem

Every ideal of the ring of integers `𝓞 K` of a number field `K` becomes principal in the ring of
integers of the Hilbert class field `hilbertClassField K` (`isPrincipal_map_hilbertClassField`).
Equivalently, extension of ideals induces the trivial homomorphism
`ClassGroup (𝓞 K) →* ClassGroup (𝓞 (hilbertClassField K))`
(`extendedHom_hilbertClassField_eq_one`).

## Proof outline

Let `H = hilbertClassField K`, and let `H₂ = hilbertClassFieldOver K H` be the Hilbert class field
of `H` realized inside `SeparableClosure K`.

1. Because `H / K` is Galois and unramified at all finite and infinite places, `H₂ / K` is also
   finite, Galois, and everywhere unramified (`isGalois_hilbertClassFieldOver`,
   `isUnramifiedAt_hilbertClassFieldOver`, `isUnramifiedAtInfinitePlaces_hilbertClassFieldOver`),
   and its maximal abelian subextension over `K` is `H`.
2. Applying the class-formation principal ideal theorem (Artin–Furtwängler transfer) to the tower
   `K ⊆ H ⊆ H₂` (`ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois`) shows that every
   idele class of `K`, extended to `H`, lies in the idele-class norm group `N_{H₂/H}(C_{H₂})`.
3. By global class field theory over `H`, that norm group is the trivial-modulus ray subgroup of
   `H` (`range_ideleClassNormMap_rayClassFieldOver`), so every extended idele class lies in
   `raySubgroup (Modulus.one H)` (`ideleClassExtension_hilbertClassField_mem_raySubgroup`).
4. Reading the trivial-modulus ray-class quotient on class groups
   (`extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup`) yields
   `ClassGroup.extendedHom (𝓞 K) (𝓞 H) = 1`, and factoring through `K`-embeddings gives
   principalization of both integral and fractional ideals in `hilbertClassField K` and in every
   number-field extension admitting a `K`-embedding of `hilbertClassField K` (in particular, all
   ray class fields, the narrow Hilbert class field, and all ring class fields).

## Main results

* `TauCeti.ClassFieldTheory.ideleClassExtension_hilbertClassField_mem_raySubgroup`: every extended
  idele class in `hilbertClassField K` lies in the trivial-modulus ray subgroup.
* `TauCeti.ClassFieldTheory.extendedHom_hilbertClassField_eq_one`,
  `TauCeti.ClassFieldTheory.extendedHom_eq_one_of_algHom_hilbertClassField`,
  `TauCeti.ClassFieldTheory.extendedHom_rayClassField_eq_one`,
  `TauCeti.ClassFieldTheory.extendedHom_narrowHilbertClassField_eq_one`,
  `TauCeti.ClassFieldTheory.extendedHom_ringClassField_eq_one`: ideal-class extension is trivial
  into the Hilbert class field and any field into which it embeds over `K`.
* `TauCeti.ClassFieldTheory.isPrincipal_map_hilbertClassField`: **the principal ideal theorem** —
  every ideal of `𝓞 K` becomes principal in `𝓞 (hilbertClassField K)`.
* `TauCeti.ClassFieldTheory.isPrincipal_map_of_algHom_hilbertClassField`,
  `TauCeti.ClassFieldTheory.isPrincipal_map_rayClassField`,
  `TauCeti.ClassFieldTheory.isPrincipal_map_narrowHilbertClassField`,
  `TauCeti.ClassFieldTheory.isPrincipal_map_ringClassField`: principalization of ideals in any
  extension receiving `hilbertClassField K`, and in ray, narrow Hilbert, and ring class fields.
* `TauCeti.ClassFieldTheory.isPrincipal_extendedHom_of_algHom_hilbertClassField`,
  `TauCeti.ClassFieldTheory.isPrincipal_extendedHom_hilbertClassField`,
  `TauCeti.ClassFieldTheory.isPrincipal_extendedHom_rayClassField`,
  `TauCeti.ClassFieldTheory.isPrincipal_extendedHom_narrowHilbertClassField`,
  `TauCeti.ClassFieldTheory.isPrincipal_extendedHom_ringClassField`: principalization of extended
  fractional ideals.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII, §4.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, Theorem 3.17.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §7, Theorem 7.6.
-/

public section

open IntermediateField IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

/-! ### Idelic and class-group forms -/

/-- **Idelic form of the principal ideal theorem.** Every idele class of a number field `K`,
extended to its Hilbert class field `H`, belongs to the trivial-modulus ray subgroup of `H`. -/
theorem ideleClassExtension_hilbertClassField_mem_raySubgroup (K : Type) [Field K] [NumberField K]
    (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      raySubgroup (Modulus.one (hilbertClassField K)) := by
  let H := hilbertClassField K
  let H₂ := hilbertClassFieldOver K H
  let _ : Algebra H H₂ :=
    (IntermediateField.inclusion (le_rayClassFieldOver H (Modulus.one H))).toRingHom.toAlgebra
  have : IsScalarTower H H₂ (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  rw [← range_ideleClassNormMap_rayClassFieldOver K (Modulus.one H)]
  exact ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois H₂
    (isUnramifiedAt_hilbertClassFieldOver K H (isUnramifiedAt_hilbertClassField K)) c

-- Not `@[simp]`: `hilbertClassField K` is an `abbrev` for `rayClassField (Modulus.one K)`, so
-- `extendedHom_rayClassField_eq_one` already simplifies this left-hand side.
/-- **Class-group form of the principal ideal theorem.** Extension of ideals from `𝓞 K` to the ring
of integers of `hilbertClassField K` induces the trivial homomorphism on ideal class groups. -/
theorem extendedHom_hilbertClassField_eq_one (K : Type) [Field K] [NumberField K] :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (hilbertClassField K)) = 1 :=
  extendedHom_eq_one_iff_forall_ideleClassExtension_mem_raySubgroup.mpr
    (ideleClassExtension_hilbertClassField_mem_raySubgroup K)

/-- **Ideal classes principalize in any field receiving `hilbertClassField K`.** If a field `L`
(in any universe) admits a `K`-algebra homomorphism from `hilbertClassField K`, then
`ClassGroup.extendedHom (𝓞 K) (𝓞 L) = 1`. -/
theorem extendedHom_eq_one_of_algHom_hilbertClassField {K : Type} [Field K] [NumberField K]
    {L : Type*} [Field L] [Algebra K L] (ι : hilbertClassField K →ₐ[K] L) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 L) = 1 := by
  have hι : Function.Injective (RingOfIntegers.mapAlgHom ι) :=
    fun _ _ h ↦ RingOfIntegers.ext (ι.injective (congrArg Subtype.val h))
  rw [← ClassGroup.extendedHom_eq_map_comp_extendedHom (RingOfIntegers.mapAlgHom ι) hι,
    extendedHom_hilbertClassField_eq_one K, MonoidHom.comp_one]

/-- Ideal classes of `𝓞 K` become trivial in every ray class field of `K` (including the ordinary
and narrow Hilbert class fields). -/
@[simp]
theorem extendedHom_rayClassField_eq_one {K : Type} [Field K] [NumberField K] (𝔪 : Modulus K) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (rayClassField 𝔪)) = 1 :=
  extendedHom_eq_one_of_algHom_hilbertClassField
    (IntermediateField.inclusion (hilbertClassField_le_rayClassField 𝔪))

-- Not `@[simp]`: `narrowHilbertClassField K` is an `abbrev` for `rayClassField (narrowModulus K)`,
-- so `extendedHom_rayClassField_eq_one` already simplifies this left-hand side.
/-- Ideal classes of `𝓞 K` become trivial in the narrow Hilbert class field of `K`. -/
theorem extendedHom_narrowHilbertClassField_eq_one (K : Type) [Field K] [NumberField K] :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (narrowHilbertClassField K)) = 1 :=
  extendedHom_rayClassField_eq_one (narrowModulus K)

/-- Ideal classes of `𝓞 K` become trivial in the ring class field of every order `O` of `K`. -/
@[simp]
theorem extendedHom_ringClassField_eq_one {K : Type} [Field K] [NumberField K]
    (O : NumberFieldOrder K) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 (ringClassField O)) = 1 :=
  extendedHom_eq_one_of_algHom_hilbertClassField
    (IntermediateField.inclusion (hilbertClassField_le_ringClassField O))

/-! ### Principalization of integral and fractional ideals -/

/-- Every ideal of `𝓞 K` becomes principal in `𝓞 L` for any number field `L` admitting a
`K`-algebra homomorphism from `hilbertClassField K`. -/
theorem isPrincipal_map_of_algHom_hilbertClassField {K : Type} [Field K] [NumberField K]
    {L : Type*} [Field L] [NumberField L] [Algebra K L] (ι : hilbertClassField K →ₐ[K] L)
    (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal :=
  (ClassGroup.extendedHom_eq_one_iff_forall_isPrincipal (𝓞 K) (𝓞 L)).mp
    (extendedHom_eq_one_of_algHom_hilbertClassField ι) I

/-- **The Principal Ideal Theorem** (Artin–Furtwängler): every ideal of `𝓞 K` becomes principal in
the ring of integers of the Hilbert class field of `K`. -/
theorem isPrincipal_map_hilbertClassField (K : Type) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (hilbertClassField K)))).IsPrincipal :=
  isPrincipal_map_of_algHom_hilbertClassField (AlgHom.id K (hilbertClassField K)) I

/-- Every ideal of `𝓞 K` becomes principal in the ring of integers of any ray class field of
`K`. -/
theorem isPrincipal_map_rayClassField {K : Type} [Field K] [NumberField K] (𝔪 : Modulus K)
    (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (rayClassField 𝔪)))).IsPrincipal :=
  isPrincipal_map_of_algHom_hilbertClassField
    (IntermediateField.inclusion (hilbertClassField_le_rayClassField 𝔪)) I

/-- Every ideal of `𝓞 K` becomes principal in the ring of integers of the narrow Hilbert class
field of `K`. -/
theorem isPrincipal_map_narrowHilbertClassField (K : Type) [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (narrowHilbertClassField K)))).IsPrincipal :=
  isPrincipal_map_rayClassField (narrowModulus K) I

/-- Every ideal of `𝓞 K` becomes principal in the ring of integers of the ring class field of any
order `O` of `K`. -/
theorem isPrincipal_map_ringClassField {K : Type} [Field K] [NumberField K]
    (O : NumberFieldOrder K) (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 (ringClassField O)))).IsPrincipal :=
  isPrincipal_map_of_algHom_hilbertClassField
    (IntermediateField.inclusion (hilbertClassField_le_ringClassField O)) I

/-- Every fractional ideal of `𝓞 K` extends to a principal `𝓞 L`-submodule of `L` for any number
field `L` admitting a `K`-algebra homomorphism from `hilbertClassField K`. -/
theorem isPrincipal_extendedHom_of_algHom_hilbertClassField {K : Type} [Field K] [NumberField K]
    {L : Type*} [Field L] [NumberField L] [Algebra K L] (ι : hilbertClassField K →ₐ[K] L)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    (FractionalIdeal.extendedHom L (𝓞 L) I : Submodule (𝓞 L) L).IsPrincipal :=
  (ClassGroup.extendedHom_eq_one_iff_forall_fractionalIdeal_isPrincipal (𝓞 K) (𝓞 L) K L).mp
    (extendedHom_eq_one_of_algHom_hilbertClassField ι) I

/-- Every fractional ideal of `𝓞 K` extends to a principal fractional ideal over the ring of
integers of `hilbertClassField K`. -/
theorem isPrincipal_extendedHom_hilbertClassField (K : Type) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    (FractionalIdeal.extendedHom (hilbertClassField K) (𝓞 (hilbertClassField K)) I :
      Submodule (𝓞 (hilbertClassField K)) (hilbertClassField K)).IsPrincipal :=
  isPrincipal_extendedHom_of_algHom_hilbertClassField (AlgHom.id K (hilbertClassField K)) I

/-- Every fractional ideal of `𝓞 K` extends to a principal fractional ideal over the ring of
integers of any ray class field of `K`. -/
theorem isPrincipal_extendedHom_rayClassField {K : Type} [Field K] [NumberField K] (𝔪 : Modulus K)
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    (FractionalIdeal.extendedHom (rayClassField 𝔪) (𝓞 (rayClassField 𝔪)) I :
      Submodule (𝓞 (rayClassField 𝔪)) (rayClassField 𝔪)).IsPrincipal :=
  isPrincipal_extendedHom_of_algHom_hilbertClassField
    (IntermediateField.inclusion (hilbertClassField_le_rayClassField 𝔪)) I

/-- Every fractional ideal of `𝓞 K` extends to a principal fractional ideal over the ring of
integers of `narrowHilbertClassField K`. -/
theorem isPrincipal_extendedHom_narrowHilbertClassField (K : Type) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    (FractionalIdeal.extendedHom (narrowHilbertClassField K) (𝓞 (narrowHilbertClassField K)) I :
      Submodule (𝓞 (narrowHilbertClassField K)) (narrowHilbertClassField K)).IsPrincipal :=
  isPrincipal_extendedHom_rayClassField (narrowModulus K) I

/-- Every fractional ideal of `𝓞 K` extends to a principal fractional ideal over the ring of
integers of the ring class field of any order `O` of `K`. -/
theorem isPrincipal_extendedHom_ringClassField {K : Type} [Field K] [NumberField K]
    (O : NumberFieldOrder K) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (FractionalIdeal.extendedHom (ringClassField O) (𝓞 (ringClassField O)) I :
      Submodule (𝓞 (ringClassField O)) (ringClassField O)).IsPrincipal :=
  isPrincipal_extendedHom_of_algHom_hilbertClassField
    (IntermediateField.inclusion (hilbertClassField_le_ringClassField O)) I

end TauCeti.ClassFieldTheory

end
