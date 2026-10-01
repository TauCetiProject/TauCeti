/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite

import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# Hecke characters

A **Hecke character** of a number field `K` is a continuous homomorphism from the idele class
group `C_K = 𝔸_K^× / K^×` to `ℂˣ`.  Hecke characters are the characters whose L-functions
generalize Dirichlet L-functions to number fields.

Every ray class character of a modulus `𝔪` defines a Hecke character by pullback along the
surjection `rayClassQuotient 𝔪 : C_K → Cl_𝔪`; the pullback is continuous because the kernel of
`rayClassQuotient 𝔪` is the open ray subgroup.  The pullback is injective, and its image consists
exactly of the Hecke characters that are trivial on `raySubgroup 𝔪`.  Pullbacks along different
moduli are compatible with the change-of-modulus map `RayClassCharacter.induced`, and every
Hecke character coming from a ray class character has finite order.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter`: continuous homomorphisms from the idele class
  group to `ℂˣ`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.ofRayClassCharacter`: the Hecke character obtained
  from a ray class character by pullback along `rayClassQuotient`.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.ofRayClassCharacter_injective`: distinct ray class
  characters give distinct Hecke characters.
* `TauCeti.GlobalNumberFields.HeckeCharacter.mem_range_ofRayClassCharacter_iff`: a Hecke
  character comes from a ray class character of `𝔪` exactly when it is trivial on
  `raySubgroup 𝔪`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.mem_range_ofRayClassCharacter_gcd`: the moduli from
  which a Hecke character comes are closed under greatest common divisors.
* `TauCeti.GlobalNumberFields.HeckeCharacter.ofRayClassCharacter_induced`: the pullback is
  unchanged when a ray class character is induced to a larger modulus.
* `TauCeti.GlobalNumberFields.RayClassCharacter.exists_induced_eq_iff_mem_range`: induction from a
  divisor is equivalent to membership of the corresponding Hecke-character pullback range.
* `TauCeti.GlobalNumberFields.HeckeCharacter.isFiniteOrder_ofRayClassCharacter`: Hecke characters
  coming from ray class characters have finite order.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1, and Chapter VII, §6.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- A **Hecke character** of `K`: a continuous homomorphism from the idele class group of `K` to
the complex units.  Hecke characters form a commutative group under pointwise multiplication. -/
abbrev HeckeCharacter := ContinuousMonoidHom (IdeleClassGroup (𝓞 K) K) ℂˣ

variable {K}

namespace HeckeCharacter

variable {𝔪 𝔫 : Modulus K}

/-- A Hecke character has **finite order** when it has finite order as an element of the
commutative group of continuous idele-class characters. -/
abbrev IsFiniteOrder (χ : HeckeCharacter K) : Prop := IsOfFinOrder χ

/-- A Hecke character has finite order exactly when all of its values have a common positive
exponent equal to one. -/
theorem isFiniteOrder_iff (χ : HeckeCharacter K) :
    χ.IsFiniteOrder ↔ ∃ n, 0 < n ∧ ∀ c, χ c ^ n = 1 :=
  ContinuousMonoidHom.isOfFinOrder_iff_exists_pow_apply_eq_one χ

/-- A pulled-back ray class character kills the ray subgroup. -/
private theorem raySubgroup_le_ker_comp_rayClassQuotient (χ : RayClassCharacter 𝔪) :
    raySubgroup 𝔪 ≤ (χ.comp (rayClassQuotient 𝔪)).ker := by
  rw [← ker_rayClassQuotient]
  exact fun c hc ↦ by simp [(MonoidHom.mem_ker).1 hc]

/-- **The Hecke character of a ray class character**: the pullback of a character of the ray
class group of `𝔪` along `rayClassQuotient 𝔪`.  It is continuous because it is trivial on the
open subgroup `raySubgroup 𝔪`. -/
def ofRayClassCharacter (𝔪 : Modulus K) : RayClassCharacter 𝔪 →* HeckeCharacter K where
  toFun χ :=
    { toMonoidHom := χ.comp (rayClassQuotient 𝔪)
      continuous_toFun := by
        exact MonoidHom.continuous_of_isOpen_ker _
          (Subgroup.isOpen_mono (raySubgroup_le_ker_comp_rayClassQuotient χ)
            (isOpen_raySubgroup 𝔪)) }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The Hecke character of a ray class character is its value at the ray class. -/
@[simp]
theorem ofRayClassCharacter_apply (χ : RayClassCharacter 𝔪) (c : IdeleClassGroup (𝓞 K) K) :
    ofRayClassCharacter 𝔪 χ c = χ (rayClassQuotient 𝔪 c) :=
  (rfl)

/-- The underlying homomorphism of the Hecke character of a ray class character is the composite
with `rayClassQuotient 𝔪`. -/
@[simp]
theorem toMonoidHom_ofRayClassCharacter (χ : RayClassCharacter 𝔪) :
    (↑(ofRayClassCharacter 𝔪 χ) :
      IdeleClassGroup (𝓞 K) K →* ℂˣ) = χ.comp (rayClassQuotient 𝔪) :=
  (rfl)

/-- **Pullback of ray class characters is injective**, because `rayClassQuotient 𝔪` is
surjective. -/
theorem ofRayClassCharacter_injective (𝔪 : Modulus K) :
    Function.Injective (ofRayClassCharacter 𝔪) := by
  intro χ ψ h
  refine MonoidHom.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := rayClassQuotient_surjective 𝔪 c
  simpa using DFunLike.congr_fun h x

/-- The Hecke character of a ray class character is trivial exactly when the ray class character
is trivial. -/
@[simp]
theorem ofRayClassCharacter_eq_one_iff {χ : RayClassCharacter 𝔪} :
    ofRayClassCharacter 𝔪 χ = 1 ↔ χ = 1 :=
  (ofRayClassCharacter_injective 𝔪).eq_iff' (map_one _)

/-- The Hecke character of a ray class character of `𝔪` is trivial on the ray subgroup of `𝔪`. -/
theorem ofRayClassCharacter_apply_eq_one_of_mem_raySubgroup (χ : RayClassCharacter 𝔪)
    {c : IdeleClassGroup (𝓞 K) K}
    (hc : c ∈ raySubgroup 𝔪) : ofRayClassCharacter 𝔪 χ c = 1 := by
  exact MonoidHom.mem_ker.mp (raySubgroup_le_ker_comp_rayClassQuotient χ hc)

/-- **The image of pullback from the ray class group of `𝔪`.**  A Hecke character comes from a
ray class character of `𝔪` exactly when it is trivial on `raySubgroup 𝔪`. -/
theorem mem_range_ofRayClassCharacter_iff {χ : HeckeCharacter K} :
    χ ∈ (ofRayClassCharacter 𝔪).range ↔
      raySubgroup 𝔪 ≤ (χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).ker := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩ c hc
    exact ofRayClassCharacter_apply_eq_one_of_mem_raySubgroup ψ hc
  · rw [← ker_rayClassQuotient] at h
    refine ⟨(rayClassQuotient 𝔪).liftOfSurjective (rayClassQuotient_surjective 𝔪)
      ⟨(χ : IdeleClassGroup (𝓞 K) K →* ℂˣ), h⟩,
      ContinuousMonoidHom.ext fun c ↦ ?_⟩
    rw [ofRayClassCharacter_apply]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c

/-- **The moduli from which a Hecke character comes are closed under greatest common divisors.**
A Hecke character trivial on the ray subgroups of `𝔪` and of `𝔫` is trivial on the subgroup they
generate, which is the ray subgroup of `𝔪.gcd 𝔫`. -/
theorem mem_range_ofRayClassCharacter_gcd {χ : HeckeCharacter K}
    (h𝔪 : χ ∈ (ofRayClassCharacter 𝔪).range) (h𝔫 : χ ∈ (ofRayClassCharacter 𝔫).range) :
    χ ∈ (ofRayClassCharacter (𝔪.gcd 𝔫)).range := by
  rw [mem_range_ofRayClassCharacter_iff] at h𝔪 h𝔫 ⊢
  rw [raySubgroup_gcd]
  exact sup_le h𝔪 h𝔫

/-- **Pullback is compatible with change of modulus**: for `𝔪 ∣ 𝔫`, inducing a ray class
character of `𝔪` to `𝔫` and then pulling back gives the same Hecke character as pulling back
directly from `𝔪`. -/
@[simp]
theorem ofRayClassCharacter_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) :
    ofRayClassCharacter 𝔫 (RayClassCharacter.induced h χ) = ofRayClassCharacter 𝔪 χ :=
  ContinuousMonoidHom.ext fun c ↦ by simp

/-- The Hecke characters coming from ray class characters of `𝔪` also come from ray class
characters of every multiple of `𝔪`. -/
theorem range_ofRayClassCharacter_le (h : 𝔪 ∣ 𝔫) :
    (ofRayClassCharacter 𝔪).range ≤ (ofRayClassCharacter 𝔫).range := by
  rintro _ ⟨χ, rfl⟩
  exact ⟨RayClassCharacter.induced h χ, ofRayClassCharacter_induced h χ⟩

/-- **Hecke characters coming from ray class characters have finite order**, since the ray class
group is finite. -/
theorem isFiniteOrder_ofRayClassCharacter (χ : RayClassCharacter 𝔪) :
    (ofRayClassCharacter 𝔪 χ).IsFiniteOrder :=
  (ofRayClassCharacter 𝔪).isOfFinOrder (isOfFinOrder_of_finite χ)

end HeckeCharacter

namespace RayClassCharacter

variable {𝔪 𝔫 : Modulus K}

/-- A ray class character of `𝔪` is induced from a divisor `𝔫` of `𝔪` exactly when its Hecke
character comes from a ray class character of `𝔫`. -/
theorem exists_induced_eq_iff_mem_range (h : 𝔫 ∣ 𝔪) (η : RayClassCharacter 𝔪) :
    (∃ ψ : RayClassCharacter 𝔫, ψ.induced h = η) ↔
      HeckeCharacter.ofRayClassCharacter 𝔪 η ∈ (HeckeCharacter.ofRayClassCharacter 𝔫).range := by
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨ψ, (HeckeCharacter.ofRayClassCharacter_induced h ψ).symm⟩
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ, HeckeCharacter.ofRayClassCharacter_injective 𝔪 ?_⟩
    rw [HeckeCharacter.ofRayClassCharacter_induced, hψ]

end RayClassCharacter

end TauCeti.GlobalNumberFields
