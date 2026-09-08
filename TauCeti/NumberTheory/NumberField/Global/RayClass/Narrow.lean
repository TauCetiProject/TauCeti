/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.TotallyComplex

/-!
# The narrow class group as the ray class group of the narrow modulus

The modulus `narrowModulus K` has unit finite part and every real place, so congruence to one
modulo it is total positivity and nothing else.  Its ray class group is therefore the narrow class
group `Cl⁺(K)`, which `TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic` builds directly as
the invertible fractional ideals of `𝓞 K` modulo the principal ones with a totally positive
generator.

This file supplies that identification as a named equivalence — the two groups are quotients of
different carriers, so they are not definitionally equal — and uses it to read the ray-class
transition map from the narrow modulus down to the trivial modulus as the forgetful surjection
`Cl⁺(K) → Cl(K)`.  Its kernel is the group of narrow ray classes of principal fractional ideals,
which is killed by `2`; over a totally complex field that kernel is trivial, so there the narrow
modulus imposes nothing at all.

## Main definitions

* `TauCeti.GlobalNumberFields.narrowEquivNarrowClassGroup`: the ray class group of the narrow
  modulus is the narrow class group.
* `TauCeti.GlobalNumberFields.narrowRayClassPrincipal`: the narrow ray class of a principal
  fractional ideal, as a homomorphism out of `Kˣ`.
* `TauCeti.GlobalNumberFields.classMapNarrowModulusEquiv`: over a totally complex field, the
  transition map to the trivial modulus as an isomorphism.

## Main results

* `TauCeti.GlobalNumberFields.congruenceSubgroup_narrowModulus` and
  `TauCeti.GlobalNumberFields.mem_ray_narrowModulus_iff`: the elements congruent to one modulo the
  narrow modulus are the totally positive units, and its ray consists of the principal fractional
  ideals with a totally positive generator.
* `TauCeti.GlobalNumberFields.toClassGroup_narrowEquiv`: the transition map to the trivial modulus
  is the forgetful map `Cl⁺(K) → Cl(K)`, read through the identifications at both ends.
* `TauCeti.GlobalNumberFields.classMap_narrowModulus_surjective` and
  `TauCeti.GlobalNumberFields.ker_classMap_narrowModulus`: exactness of
  `Kˣ → Cl⁺(K) → Cl(K) → 1` in ray-class form.
* `TauCeti.GlobalNumberFields.narrowRayClassPrincipal_sq`: that kernel is an elementary abelian
  `2`-group.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The elements of `Kˣ` congruent to one modulo the narrow modulus are the totally positive
ones.**  The finite part of `narrowModulus K` is the unit ideal, so only the sign conditions
survive, and they are imposed at every real place. -/
@[simp] theorem congruenceSubgroup_narrowModulus :
    congruenceSubgroup (narrowModulus K) = (totallyPositiveUnits : Subgroup Kˣ) := by
  ext x
  rw [mem_congruenceSubgroup, isCongrOne_narrowModulus_iff, mem_totallyPositiveUnits]

/-- **The ray of the narrow modulus consists of the principal fractional ideals with a totally
positive generator**, that is, of the ideals of `narrowPrincipalSubgroup K`. -/
theorem mem_ray_narrowModulus_iff {I : idealsPrimeTo (narrowModulus K)} :
    I ∈ ray (narrowModulus K) ↔
      (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ narrowPrincipalSubgroup K := by
  rw [mem_ray_iff, mem_narrowPrincipalSubgroup]
  exact exists_congr fun _ ↦ and_congr_left' isCongrOne_narrowModulus_iff

/-- The narrow class of an invertible fractional ideal prime to the narrow modulus, as a
homomorphism out of the ray class group: the forward half of `narrowEquivNarrowClassGroup`. -/
private noncomputable def toNarrowClassGroup :
    RayClassGroup (narrowModulus K) →* NarrowClassGroup K :=
  rayClassLift
    (NarrowClassGroup.mk.comp
      (idealsPrimeToEquiv (narrowModulus_support (K := K))).toMonoidHom)
    fun J hJ ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, NarrowClassGroup.mk_eq_one_iff,
        MulEquiv.coe_toMonoidHom, idealsPrimeToEquiv_apply]
      exact mem_ray_narrowModulus_iff.mp hJ

/-- The narrow ray class of an invertible fractional ideal, as a homomorphism out of the narrow
class group: the backward half of `narrowEquivNarrowClassGroup`. -/
private noncomputable def ofNarrowClassGroup :
    NarrowClassGroup K →* RayClassGroup (narrowModulus K) :=
  NarrowClassGroup.lift
    ((rayClassMk (narrowModulus K)).comp
      (idealsPrimeToEquiv (narrowModulus_support (K := K))).symm.toMonoidHom)
    fun I hI ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, rayClassMk_eq_one_iff,
        mem_ray_narrowModulus_iff, MulEquiv.coe_toMonoidHom, idealsPrimeToEquiv_symm_apply]
      exact hI

/-- **The ray class group of the narrow modulus is the narrow class group.**  This is a named
equivalence, not a definitional equality: the ray class group is a quotient of the fractional
ideals prime to the empty set of primes, and the narrow class group is a quotient of all invertible
fractional ideals. -/
noncomputable def narrowEquivNarrowClassGroup :
    RayClassGroup (narrowModulus K) ≃* NarrowClassGroup K where
  toFun := toNarrowClassGroup
  invFun := ofNarrowClassGroup
  map_mul' := map_mul toNarrowClassGroup
  left_inv c := by
    obtain ⟨I, rfl⟩ := rayClassMk_surjective (narrowModulus K) c
    simp only [toNarrowClassGroup, ofNarrowClassGroup, rayClassLift_rayClassMk,
      MonoidHom.comp_apply, NarrowClassGroup.lift_mk, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
  right_inv C := by
    obtain ⟨I, rfl⟩ := NarrowClassGroup.mk_surjective C
    simp only [toNarrowClassGroup, ofNarrowClassGroup, NarrowClassGroup.lift_mk,
      MonoidHom.comp_apply, rayClassLift_rayClassMk, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]

/-- **The identification carries a narrow ray class to the narrow class of the same fractional
ideal.** -/
@[simp] theorem narrowEquivNarrowClassGroup_rayClassMk (I : idealsPrimeTo (narrowModulus K)) :
    narrowEquivNarrowClassGroup (rayClassMk (narrowModulus K) I) =
      NarrowClassGroup.mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  simp only [narrowEquivNarrowClassGroup, MulEquiv.coe_mk, Equiv.coe_fn_mk, toNarrowClassGroup,
    rayClassLift_rayClassMk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    idealsPrimeToEquiv_apply]

/-- The inverse identification carries the narrow class of a fractional ideal back to its narrow
ray class. -/
@[simp] theorem narrowEquivNarrowClassGroup_symm_mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    narrowEquivNarrowClassGroup.symm (NarrowClassGroup.mk I) =
      rayClassMk (narrowModulus K)
        ((idealsPrimeToEquiv (narrowModulus_support (K := K))).symm I) :=
  (MulEquiv.symm_apply_eq _).mpr <| by
    rw [narrowEquivNarrowClassGroup_rayClassMk, idealsPrimeToEquiv_symm_apply]

/-! ### The transition map to the trivial modulus -/

/-- **The transition map from the narrow modulus to the trivial modulus is the forgetful surjection
`Cl⁺(K) → Cl(K)`**, read through the identifications at both ends. -/
@[simp] theorem toClassGroup_narrowEquiv (c : RayClassGroup (narrowModulus K)) :
    NarrowClassGroup.toClassGroup (narrowEquivNarrowClassGroup c) =
      oneEquivClassGroup (classMap (Modulus.one_dvd (narrowModulus K)) c) := by
  obtain ⟨I, rfl⟩ := rayClassMk_surjective (narrowModulus K) c
  rw [narrowEquivNarrowClassGroup_rayClassMk, NarrowClassGroup.toClassGroup_mk,
    classMap_rayClassMk, oneEquivClassGroup_rayClassMk,
    NumberFieldArithmetic.coe_idealsAwayInclusion]

/-- **The transition map from the narrow ray class group onto the ordinary class group is
surjective.** -/
theorem classMap_narrowModulus_surjective :
    Function.Surjective (classMap (Modulus.one_dvd (narrowModulus K))) := by
  intro c
  obtain ⟨C, hC⟩ := NarrowClassGroup.toClassGroup_surjective (oneEquivClassGroup c)
  refine ⟨narrowEquivNarrowClassGroup.symm C, oneEquivClassGroup.injective ?_⟩
  rw [← toClassGroup_narrowEquiv, MulEquiv.apply_symm_apply, hC]

/-! ### Narrow ray classes of principal ideals -/

/-- **The narrow ray class of a principal fractional ideal.**  The finite part of the narrow
modulus is the unit ideal, so every principal fractional ideal is prime to it and this is defined
on all of `Kˣ`. -/
noncomputable def narrowRayClassPrincipal : Kˣ →* RayClassGroup (narrowModulus K) :=
  (rayClassMk (narrowModulus K)).comp
    ((idealsPrimeToEquiv (narrowModulus_support (K := K))).symm.toMonoidHom.comp
      (toPrincipalIdeal (𝓞 K) K))

/-- The identification carries the narrow ray class of a principal ideal to its narrow principal
class. -/
@[simp] theorem narrowEquivNarrowClassGroup_narrowRayClassPrincipal (x : Kˣ) :
    narrowEquivNarrowClassGroup (narrowRayClassPrincipal x) =
      NarrowClassGroup.mkPrincipal x := by
  simp only [narrowRayClassPrincipal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    narrowEquivNarrowClassGroup_rayClassMk, idealsPrimeToEquiv_symm_apply,
    NarrowClassGroup.mkPrincipal_apply]

/-- **A totally positive generator makes the narrow ray class of a principal ideal trivial.** -/
theorem narrowRayClassPrincipal_eq_one_of_isTotallyPositive {x : Kˣ}
    (hx : IsTotallyPositive (x : K)) : narrowRayClassPrincipal (K := K) x = 1 := by
  simp only [narrowRayClassPrincipal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    rayClassMk_eq_one_iff, mem_ray_narrowModulus_iff, idealsPrimeToEquiv_symm_apply,
    mem_narrowPrincipalSubgroup]
  exact ⟨x, hx, rfl⟩

/-- **The narrow ray class of a principal ideal is `2`-torsion**, since the square of any generator
is totally positive. -/
@[simp] theorem narrowRayClassPrincipal_sq (x : Kˣ) :
    narrowRayClassPrincipal (K := K) x ^ 2 = 1 :=
  narrowEquivNarrowClassGroup.injective <| by
    rw [map_pow, narrowEquivNarrowClassGroup_narrowRayClassPrincipal, map_one,
      NarrowClassGroup.mkPrincipal_sq]

/-- **Exactness at the narrow ray class group** of `Kˣ → Cl⁺(K) → Cl(K) → 1`: the kernel of the
transition map to the trivial modulus is exactly the group of narrow ray classes of principal
fractional ideals. -/
theorem ker_classMap_narrowModulus :
    MonoidHom.ker (classMap (Modulus.one_dvd (narrowModulus K))) =
      (narrowRayClassPrincipal (K := K)).range := by
  ext c
  rw [MonoidHom.mem_range, MonoidHom.mem_ker,
    ← EmbeddingLike.map_eq_one_iff (f := oneEquivClassGroup (K := K)),
    ← toClassGroup_narrowEquiv, ← MonoidHom.mem_ker, NarrowClassGroup.toClassGroup_ker,
    MonoidHom.mem_range]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, narrowEquivNarrowClassGroup.injective ?_⟩,
    fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩⟩
  · rw [narrowEquivNarrowClassGroup_narrowRayClassPrincipal, hx]
  · rw [← hx, narrowEquivNarrowClassGroup_narrowRayClassPrincipal]

/-! ### Totally complex fields -/

/-- **Over a totally complex field the transition map to the trivial modulus is injective**: the
positivity conditions of the narrow modulus are vacuous, so every principal fractional ideal
already has a totally positive generator. -/
theorem classMap_narrowModulus_injective [IsTotallyComplex K] :
    Function.Injective (classMap (Modulus.one_dvd (narrowModulus K))) := fun c d h ↦
  narrowEquivNarrowClassGroup.injective <| NarrowClassGroup.toClassGroup_injective <| by
    rw [toClassGroup_narrowEquiv, toClassGroup_narrowEquiv, h]

/-- **Over a totally complex field the narrow modulus imposes no condition**: its ray class group
is the ray class group of the trivial modulus, hence the ordinary class group. -/
noncomputable def classMapNarrowModulusEquiv [IsTotallyComplex K] :
    RayClassGroup (narrowModulus K) ≃* RayClassGroup (Modulus.one K) :=
  MulEquiv.ofBijective (classMap (Modulus.one_dvd (narrowModulus K)))
    ⟨classMap_narrowModulus_injective, classMap_narrowModulus_surjective⟩

@[simp] theorem classMapNarrowModulusEquiv_apply [IsTotallyComplex K]
    (c : RayClassGroup (narrowModulus K)) :
    classMapNarrowModulusEquiv c = classMap (Modulus.one_dvd (narrowModulus K)) c := (rfl)

end TauCeti.GlobalNumberFields
