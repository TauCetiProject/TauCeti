/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.SubgroupConductor.Rat

import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Surjective
import TauCeti.NumberTheory.NumberField.Global.Cyclotomic.RayClass

/-!
# The conductor of a cyclotomic extension

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`. Its Artin map
`cyclotomicArtin K F m` factors through the ray class group of the admissible modulus
`cyclotomicModulus K m`, with finite part `(m)` and every real place. The **conductor** of `F / K`
is the least modulus through which the Artin map factors: the conductor `rayClassConductor` of the
kernel of `cyclotomicArtin K F m` in the sense of Global Number Fields. It divides
`cyclotomicModulus K m`, and it is the least common multiple of the conductors of the ray class
characters `χ ∘ cyclotomicArtin K F m` for the characters `χ` of `Gal(F/K)`.

Over `ℚ` the Artin map is injective, and the conductor of `ℚ(ζ_m)/ℚ` is:

* the trivial modulus for `m ≤ 2`, where `ℚ(ζ_m) = ℚ`;
* `(m)·∞` for `m > 2` with `m` not `2` modulo `4`;
* `(m / 2)·∞` for `m > 2` with `m` equal to `2` modulo `4`, where `ℚ(ζ_m) = ℚ(ζ_{m/2})`.

## Main definitions

* `NumberField.Chebotarev.cyclotomicConductor`: the conductor of `K(μ_m) / K`.

## Main results

* `NumberField.Chebotarev.cyclotomicArtin_rat_injective`: the Artin map over `ℚ` is injective.
* `NumberField.Chebotarev.cyclotomicConductor_dvd`: the conductor divides
  `cyclotomicModulus K m`.
* `NumberField.Chebotarev.cyclotomicConductor_dvd_iff`: for `𝔫 ∣ cyclotomicModulus K m`, the
  conductor divides `𝔫` exactly when the Artin map factors through `RayClassGroup 𝔫`.
* `NumberField.Chebotarev.cyclotomicConductor_dvd_iff_forall_conductor_dvd`: the conductor
  divides `𝔫` exactly when the conductor of every Galois character, read on ray classes, does.
* `NumberField.Chebotarev.cyclotomicConductor_rat_of_le_two`,
  `NumberField.Chebotarev.cyclotomicConductor_rat`, and
  `NumberField.Chebotarev.cyclotomicConductor_rat_of_mod_four_eq_two`: the conductor of
  `ℚ(ζ_m)/ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6 and Chapter VII, §6.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace NumberField.Chebotarev

open TauCeti.GlobalNumberFields Subgroup

section Conductor

variable (K : Type*) [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

/-- **The conductor of a cyclotomic extension.** For `F = K(μ_m)`, the least modulus through which
the Artin map `cyclotomicArtin K F m` factors (`cyclotomicConductor_dvd_iff`): the conductor of the
kernel of the Artin map. It divides `cyclotomicModulus K m` (`cyclotomicConductor_dvd`). -/
noncomputable def cyclotomicConductor : Modulus K :=
  rayClassConductor (cyclotomicArtin K F m).ker

/-- The cyclotomic conductor is the ray class conductor of the kernel of the Artin map. -/
theorem cyclotomicConductor_def :
    cyclotomicConductor K F m = (cyclotomicArtin K F m).ker.rayClassConductor := (rfl)

/-- The conductor of `K(μ_m) / K` divides the cyclotomic modulus `(m)` times the real places. -/
theorem cyclotomicConductor_dvd : cyclotomicConductor K F m ∣ cyclotomicModulus K m :=
  rayClassConductor_dvd _

variable {K F m}

/-- **The conductor is the least modulus through which the Artin map factors.** For a divisor
`𝔫` of `cyclotomicModulus K m`, the conductor of `K(μ_m) / K` divides `𝔫` exactly when the Artin
map factors through the transition map to the ray class group of `𝔫`. -/
theorem cyclotomicConductor_dvd_iff {𝔫 : Modulus K} (h : 𝔫 ∣ cyclotomicModulus K m) :
    cyclotomicConductor K F m ∣ 𝔫 ↔
      ∃ φ : RayClassGroup 𝔫 →* (F ≃ₐ[K] F), φ.comp (classMap h) = cyclotomicArtin K F m := by
  rw [cyclotomicConductor, rayClassConductor_dvd_iff h]
  refine ⟨fun hker ↦ ⟨(classMap h).liftOfSurjective (classMap_surjective h) ⟨_, hker⟩,
    MonoidHom.ext fun c ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.liftOfRightInverse_comp_apply]⟩, ?_⟩
  rintro ⟨φ, hφ⟩ c hc
  rw [MonoidHom.mem_ker, ← hφ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hc, map_one]

/-- **The conductor is the least common multiple of the conductors of the Galois characters.**
The conductor of `K(μ_m) / K` divides `𝔫` exactly when, for every character `χ` of `Gal(F/K)`, the
conductor of the ray class character `χ ∘ cyclotomicArtin K F m` divides `𝔫`. -/
theorem cyclotomicConductor_dvd_iff_forall_conductor_dvd {𝔫 : Modulus K} :
    cyclotomicConductor K F m ∣ 𝔫 ↔
      ∀ χ : (F ≃ₐ[K] F) →* ℂˣ,
        RayClassCharacter.conductor (χ.comp (cyclotomicArtin K F m)) ∣ 𝔫 := by
  rw [cyclotomicConductor, rayClassConductor_dvd_iff_forall_conductor_dvd]
  refine ⟨fun h χ ↦ h _ fun c hc ↦ by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hc, map_one], fun h η hη ↦ ?_⟩
  -- A ray class character trivial on the kernel of the surjective Artin map factors through it.
  have hη' : (MonoidHom.liftOfSurjective (cyclotomicArtin K F m)
      (cyclotomicArtin_surjective K F m) ⟨η, hη⟩).comp (cyclotomicArtin K F m) = η :=
    MonoidHom.ext fun c ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.liftOfRightInverse_comp_apply]
  exact hη' ▸ h _

/-- The conductor of every Galois character of `K(μ_m) / K`, read on ray classes, divides the
conductor of `K(μ_m) / K`. -/
theorem conductor_comp_cyclotomicArtin_dvd (χ : (F ≃ₐ[K] F) →* ℂˣ) :
    RayClassCharacter.conductor (χ.comp (cyclotomicArtin K F m)) ∣ cyclotomicConductor K F m :=
  cyclotomicConductor_dvd_iff_forall_conductor_dvd.mp (Modulus.dvd_refl _) χ

end Conductor

section Rat

variable (m : ℕ) [NeZero m]

/-- Over `ℚ`, the cyclotomic modulus of level `m` is `(m)·∞`. -/
@[simp] theorem cyclotomicModulus_rat : cyclotomicModulus ℚ m = ratModulus m (NeZero.ne m) :=
  Modulus.ext (by rw [cyclotomicModulus_finitePart, ratModulus_finitePart]) <| Finset.ext fun w ↦
    ⟨fun _ ↦ by
      rw [ratModulus_infinitePart, Finset.mem_singleton]
      exact Subtype.ext (Subsingleton.elim _ _),
    fun _ ↦ mem_cyclotomicModulus_infinitePart ℚ m w⟩

variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F] [IsGalois ℚ F]
  {m}

/-- The cyclotomic Artin map over `ℚ` is injective. -/
theorem cyclotomicArtin_rat_injective : Function.Injective (cyclotomicArtin ℚ F m) := by
  -- Abstract the modulus so its equality transports both the map and its unramifiedness input.
  have key (𝔪 : Modulus ℚ) (h𝔪 : 𝔪 = ratModulus m (NeZero.ne m))
      (φ : RayClassGroup 𝔪 →* (F ≃ₐ[ℚ] F))
      (hunram : ∀ (v : HeightOneSpectrum (𝓞 ℚ)), v ∉ 𝔪.support →
        ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
          Algebra.IsUnramifiedAt (𝓞 ℚ) Q)
      (hcomp : φ.comp (rayClassMk 𝔪) = TauCeti.NumberFieldArithmetic.artinHomAway
        (IsCyclotomicExtension.isMulCommutative {m} ℚ F).is_comm.comm 𝔪.support hunram) :
      Function.Injective φ := by
    subst 𝔪
    have heq : φ = (ratModulusEquivGal m F).toMonoidHom := by
      apply MonoidHom.ext
      intro c
      obtain ⟨I, rfl⟩ := rayClassMk_surjective (ratModulus m (NeZero.ne m)) c
      exact DFunLike.congr_fun (hcomp.trans (ratModulusEquivGal_comp_rayClassMk m F).symm) I
    rw [heq]
    exact (ratModulusEquivGal m F).injective
  exact key _ (cyclotomicModulus_rat m) _ _ (cyclotomicArtin_comp_rayClassMk (K := ℚ) F m)

-- Over `ℚ` the conductor is that of the trivial subgroup of the ray class group of `(m)·∞`.
private theorem cyclotomicConductor_rat_eq :
    cyclotomicConductor ℚ F m =
      rayClassConductor (⊥ : Subgroup (RayClassGroup (ratModulus m (NeZero.ne m)))) := by
  rw [cyclotomicConductor, (MonoidHom.ker_eq_bot_iff _).mpr (cyclotomicArtin_rat_injective F)]
  have key : ∀ 𝔪 : Modulus ℚ, 𝔪 = ratModulus m (NeZero.ne m) →
      rayClassConductor (⊥ : Subgroup (RayClassGroup 𝔪)) =
        rayClassConductor (⊥ : Subgroup (RayClassGroup (ratModulus m (NeZero.ne m)))) := by
    rintro _ rfl
    rfl
  exact key _ (cyclotomicModulus_rat m)

/-- **The conductor of `ℚ(ζ_m)/ℚ` for `m ≤ 2` is trivial**: then `ℚ(ζ_m) = ℚ`. -/
@[simp] theorem cyclotomicConductor_rat_of_le_two (hm : m ≤ 2) :
    cyclotomicConductor ℚ F m = Modulus.one ℚ := by
  rw [cyclotomicConductor_rat_eq, rayClassConductor_bot_ratModulus_of_le_two hm]

/-- **The conductor of `ℚ(ζ_m)/ℚ` is `(m)·∞`** for `m > 2` not equal to `2` modulo `4`. -/
@[simp] theorem cyclotomicConductor_rat (h2 : 2 < m) (h4 : m % 4 ≠ 2) :
    cyclotomicConductor ℚ F m = ratModulus m (NeZero.ne m) := by
  rw [cyclotomicConductor_rat_eq, rayClassConductor_bot_ratModulus h2 h4]

/-- **The conductor of `ℚ(ζ_m)/ℚ` is `(m / 2)·∞`** for `m > 2` equal to `2` modulo `4`: then
`ℚ(ζ_m) = ℚ(ζ_{m/2})` with `m / 2` odd. -/
@[simp] theorem cyclotomicConductor_rat_of_mod_four_eq_two (h2 : 2 < m) (h4 : m % 4 = 2) :
    cyclotomicConductor ℚ F m = ratModulus (m / 2) (by omega) := by
  rw [cyclotomicConductor_rat_eq, rayClassConductor_bot_ratModulus_of_mod_four_eq_two h2 h4]

end Rat

end NumberField.Chebotarev
