/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Weight
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Ideal.ArtinMap
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Cyclotomic Galois characters as ray class characters

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`, and let `𝔪` be the
modulus of `K` with finite part `(m)` and every real place in its infinite part. This file
provides the Artin map of the abelian extension `F / K` as a homomorphism from the ray class group
of `𝔪` to `Gal(F/K)`. It sends the ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.

Composing with it, every character `χ` of `Gal(F/K)` gives a ray class character of `𝔪`, and on
the integral ideals prime to `m` the ideal weight `galoisCharacterWeight χ` of `χ` agrees with that
ray class character.

## Main definitions

* `NumberField.Chebotarev.cyclotomicModulus`: the modulus of `K` with finite part `(m)` and
  every real place in its infinite part.
* `NumberField.Chebotarev.cyclotomicArtin`: the Artin map
  `RayClassGroup (cyclotomicModulus K m) →* (F ≃ₐ[K] F)`.

## Main results

* `NumberField.Chebotarev.cyclotomicArtin_idealClass_of_isArithFrobAt`: the Artin map sends the
  ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.
* `MonoidHom.galoisCharacterWeight_eq_onIdeals_cyclotomicArtin`: on the integral ideals prime to
  `m`, the ideal weight of a character `χ` of `Gal(F/K)` is the ray class character
  `χ ∘ cyclotomicArtin`.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace NumberField.Chebotarev

open TauCeti.GlobalNumberFields TauCeti.NumberFieldArithmetic

section Modulus

variable (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m]

/-- **The cyclotomic modulus** of level `m`: finite part the ideal `(m)` of `𝓞 K`, and every real
place of `K` in the infinite part. The Artin map of `K(μ_m) / K` factors through its ray class
group (`cyclotomicArtin`). The definition does not unfold outside this file; use
`cyclotomicModulus_finitePart`, `mem_cyclotomicModulus_infinitePart` and
`mem_cyclotomicModulus_support_iff`. -/
noncomputable def cyclotomicModulus : Modulus K where
  finitePart := Ideal.span {(m : 𝓞 K)}
  finitePart_ne_bot := Ideal.span_singleton_eq_bot.not.mpr (NeZero.ne _)
  infinitePart := (narrowModulus K).infinitePart

/-- The finite part of the cyclotomic modulus of level `m` is the principal ideal `(m)`. -/
@[simp] theorem cyclotomicModulus_finitePart :
    (cyclotomicModulus K m).finitePart = Ideal.span {(m : 𝓞 K)} := (rfl)

/-- Every real place of `K` lies in the infinite part of the cyclotomic modulus. -/
@[simp] theorem mem_cyclotomicModulus_infinitePart (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ (cyclotomicModulus K m).infinitePart := mem_narrowModulus_infinitePart w

variable {K m}

/-- A prime lies in the support of the cyclotomic modulus exactly when it divides `m`. -/
theorem mem_cyclotomicModulus_support_iff {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ (cyclotomicModulus K m).support ↔ (m : 𝓞 K) ∈ v.asIdeal := by
  rw [Modulus.mem_support_iff, cyclotomicModulus_finitePart, Ideal.dvd_span_singleton]

/-- A height-one prime is prime to the cyclotomic modulus exactly when it does not divide `m`. -/
theorem asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff {v : HeightOneSpectrum (𝓞 K)} :
    v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m) ↔ (m : 𝓞 K) ∉ v.asIdeal :=
  Modulus.mem_integralIdealsPrimeTo.trans <|
    (Modulus.isCoprimeTo_iff.trans Ideal.isPrimeTo_iff.symm).trans <|
      Ideal.isPrimeTo_asIdeal_iff.trans mem_cyclotomicModulus_support_iff.not

end Modulus

section Auxiliary

variable {K : Type*} [Field K] [NumberField K]

-- A nonzero integer congruent to one modulo `(m)` generates an ideal prime to the cyclotomic
-- modulus.
private theorem span_singleton_mem_integralIdealsPrimeTo_cyclotomicModulus {m : ℕ} [NeZero m]
    {c : 𝓞 K} (hc0 : c ≠ 0) (hc : c - 1 ∈ Ideal.span {(m : 𝓞 K)}) :
    Ideal.span {c} ∈ integralIdealsPrimeTo (cyclotomicModulus K m) := by
  refine mem_integralIdealsAway_iff.mpr
    ⟨Ideal.span_singleton_eq_bot.not.mpr hc0, fun v hv hvc ↦ v.asIdeal.one_notMem ?_⟩
  simpa using sub_mem (Ideal.dvd_span_singleton.mp hvc) <|
    (Ideal.span_singleton_le_iff_mem _).mpr (mem_cyclotomicModulus_support_iff.mp hv) hc

end Auxiliary

section Cyclotomic

/-- For `F = K(μ_m)`, every prime of `𝓞 F` above a prime `v` of `𝓞 K` outside the support of
`cyclotomicModulus K m` (that is, with `(m : 𝓞 K) ∉ v.asIdeal`) is unramified over `𝓞 K`. -/
theorem isUnramifiedAt_of_notMem_cyclotomicModulus_support {K : Type*} [Field K] [NumberField K]
    (F : Type*) [Field F] [NumberField F] [Algebra K F] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ (cyclotomicModulus K m).support) (Q : Ideal (𝓞 F))
    [Q.IsPrime] [Q.LiesOver v.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  rw [mem_cyclotomicModulus_support_iff] at hv
  by_contra hQ
  -- a ramified `Q` divides the different, which contains `m`
  refine hv ((Ideal.mem_of_liesOver Q v.asIdeal _).mpr ?_)
  simpa using Ideal.le_of_dvd (dvd_differentIdeal_iff.mpr hQ)
    (IsCyclotomicExtension.natCast_mem_differentIdeal K F m)

variable {K : Type*} [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- The Artin map of `F / K` on the fractional ideals prime to `m`.
private noncomputable def cyclotomicArtinAway :
    idealsPrimeTo (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  artinHomAway (IsCyclotomicExtension.isMulCommutative {m} K F).is_comm.comm
    (cyclotomicModulus K m).support fun _ hv Q _ _ ↦
      isUnramifiedAt_of_notMem_cyclotomicModulus_support F m hv Q

-- The Artin map of `F / K` on the integral ideals prime to `m`.
private noncomputable def cyclotomicArtinIntegral :
    integralIdealsPrimeTo (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  artinHomAwayIntegral (IsCyclotomicExtension.isMulCommutative {m} K F).is_comm.comm
    (cyclotomicModulus K m).support fun _ hv Q _ _ ↦
      isUnramifiedAt_of_notMem_cyclotomicModulus_support F m hv Q

-- The integral Artin map is the fractional one read on the ideals the integral ones generate.
private theorem cyclotomicArtinIntegral_apply (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    cyclotomicArtinIntegral F m I =
      cyclotomicArtinAway F m (integralIdealsAwayHom (cyclotomicModulus K m).support I) :=
  artinHomAwayIntegral_apply _ _ _ I

-- At a prime not dividing `m`, the integral Artin map is the Frobenius.
private theorem cyclotomicArtinIntegral_of_isArithFrobAt (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m)) (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal] {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    cyclotomicArtinIntegral F m ⟨v.asIdeal, hv⟩ = σ :=
  artinHomAwayIntegral_apply_prime _ _ _ v
    (mem_cyclotomicModulus_support_iff.not.mpr
      (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv)) hv Q σ hσ

-- The cyclotomic character of the integral Artin map is the absolute norm.
private theorem autToPow_cyclotomicArtinIntegral {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    (hζ.autToPow K (cyclotomicArtinIntegral F m I) : ZMod m) =
      Ideal.absNorm (I : Ideal (𝓞 K)) := by
  let f : integralIdealsPrimeTo (cyclotomicModulus K m) →* ZMod m :=
    (Units.coeHom (ZMod m)).comp ((hζ.autToPow K).comp (cyclotomicArtinIntegral F m))
  let g : integralIdealsPrimeTo (cyclotomicModulus K m) →* ZMod m :=
    (Nat.castRingHom (ZMod m)).toMonoidHom.comp
      ((Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ).toMonoidHom.comp
        (integralIdealsPrimeTo (cyclotomicModulus K m)).subtype)
  have hfg : f = g := integralIdealsAway_hom_ext fun v hv ↦ by
    obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 F)))
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    simp [f, g, cyclotomicArtinIntegral_of_isArithFrobAt F m v hv Q hσ, hσ.autToPow_eq_absNorm hζ v
      (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv) Q]
  exact DFunLike.congr_fun hfg I

-- The Artin map of `F / K` kills the ray of the cyclotomic modulus.
private theorem ray_le_ker_cyclotomicArtinAway :
    ray (cyclotomicModulus K m) ≤ (cyclotomicArtinAway F m).ker := by
  -- For `x ≡ 1 mod 𝔪` the ideal `(x)` has absolute norm `≡ 1 mod m`, and the Artin automorphism
  -- acts on `μ_m` by the absolute norm.
  intro J hJ
  obtain ⟨x, hx, hxJ⟩ := mem_ray_iff.mp hJ
  rw [MonoidHom.mem_ker]
  have hζ := IsCyclotomicExtension.zeta_spec m K F
  refine hζ.autToPow_injective K ?_
  rw [map_one]
  rcases eq_or_ne m 1 with rfl | hm1
  · exact Subsingleton.elim _ _
  -- Write `x = a / b` with `a ≡ b ≡ 1 mod m`.
  obtain ⟨a, b, ha, hb, hab⟩ := hx.exists_sub_one_mem_and_algebraMap_eq_mul
  rw [cyclotomicModulus_finitePart] at ha hb
  have hne0 {c : 𝓞 K} (hc : c - 1 ∈ Ideal.span {(m : 𝓞 K)}) : c ≠ 0 := fun h ↦
    hm1 (Ideal.span_singleton_natCast_eq_top_iff.mp
      ((Ideal.eq_top_iff_one _).mpr (by simpa [h] using neg_mem hc)))
  have hIa := span_singleton_mem_integralIdealsPrimeTo_cyclotomicModulus (hne0 ha) ha
  have hIb := span_singleton_mem_integralIdealsPrimeTo_cyclotomicModulus (hne0 hb) hb
  -- In `idealsPrimeTo`, `(a) = (x) * (b)`.
  have hsplit : integralIdealsAwayHom _ ⟨Ideal.span {a}, hIa⟩ =
      J * integralIdealsAwayHom _ ⟨Ideal.span {b}, hIb⟩ := by
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, coe_integralIdealsAwayHom, coe_integralIdealsAwayHom,
      ← hxJ, coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      hab, mul_comm]
  -- Hence the cyclotomic character of `(x)` is trivial once those of `(a)` and `(b)` agree.
  refine (mul_eq_right (b := hζ.autToPow K (cyclotomicArtinIntegral F m ⟨_, hIb⟩))).mp ?_
  rw [cyclotomicArtinIntegral_apply, ← map_mul, ← map_mul, ← hsplit, Units.ext_iff,
    ← cyclotomicArtinIntegral_apply, ← cyclotomicArtinIntegral_apply,
    autToPow_cyclotomicArtinIntegral F m hζ, autToPow_cyclotomicArtinIntegral F m hζ]
  -- They do: `a ≡ b` modulo `m`, and `N(a) = N(b) N(x)` with `N(x) > 0` as `x` is totally
  -- positive, so `N(a) N(b) = N(b) ^ 2 N(x) ≥ 0`.
  have hNab : ((Algebra.norm ℤ a : ℤ) : ℚ) = (Algebra.norm ℤ b : ℤ) * Algebra.norm ℚ (x : K) := by
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int, ← map_mul]
    exact congrArg _ hab
  have hsign : (0 : ℚ) ≤ (Algebra.norm ℤ a : ℤ) * (Algebra.norm ℤ b : ℤ) := by
    rw [hNab, mul_right_comm]
    exact mul_nonneg (mul_self_nonneg _) (norm_pos_of_isTotallyPositive x.ne_zero
      (isTotallyPositive_iff.mpr fun w hw ↦
        hx.pos (mem_cyclotomicModulus_infinitePart K m ⟨w, hw⟩))).le
  exact Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem (mod_cast hsign)
    (by simpa using sub_mem ha hb)

variable (K) in
/-- **The Artin map of a cyclotomic extension on the ray class group.** For `F = K(μ_m)` the
Artin map of the abelian extension `F / K` on the fractional ideals prime to `m` is trivial on the
ray of `cyclotomicModulus K m`, and so factors through its ray class group. The definition does
not unfold outside this file; it sends the ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`
(`cyclotomicArtin_idealClass_of_isArithFrobAt`). -/
noncomputable def cyclotomicArtin : RayClassGroup (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  rayClassLift (cyclotomicArtinAway F m) (ray_le_ker_cyclotomicArtinAway F m)

-- On the ray class of an integral ideal, `cyclotomicArtin` is the integral Artin map.
private theorem cyclotomicArtin_idealClass (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    cyclotomicArtin K F m (idealClass _ I) = cyclotomicArtinIntegral F m I := by
  rw [idealClass_apply, cyclotomicArtin, rayClassLift_rayClassMk, cyclotomicArtinIntegral_apply]

/-- **The Artin map sends the ray class of a prime to its Frobenius.** At a height-one prime `𝔭`
not dividing `m`, every arithmetic Frobenius at every prime of `𝓞 F` above `𝔭` is the image of
the ray class of `𝔭`. -/
theorem cyclotomicArtin_idealClass_of_isArithFrobAt (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : 𝔭.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m)) (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver 𝔭.asIdeal] {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    cyclotomicArtin K F m (idealClass _ ⟨𝔭.asIdeal, h𝔭⟩) = σ := by
  rw [cyclotomicArtin_idealClass, cyclotomicArtinIntegral_of_isArithFrobAt F m 𝔭 h𝔭 Q hσ]

end Cyclotomic

end NumberField.Chebotarev

namespace MonoidHom

open TauCeti.GlobalNumberFields TauCeti.NumberFieldArithmetic NumberField.Chebotarev
open scoped IsMulCommutative

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- At a prime `v ∤ m`, the ideal weight of `χ` is `χ` of the Artin image of the ray class of `v`.
private theorem galoisCharacterWeight_asIdeal_eq_cyclotomicArtin (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m)) :
    galoisCharacterWeight (L := F) χ v.asIdeal =
      (χ (cyclotomicArtin K F m (idealClass _ ⟨v.asIdeal, hv⟩)) : ℂ) := by
  have hur : ∀ (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q _ _ ↦
    isUnramifiedAt_of_notMem_cyclotomicModulus_support F m
      (mem_cyclotomicModulus_support_iff.not.mpr
        (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv)) Q
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 F)))
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  -- `Gal(F/K)` is abelian, so the Artin symbol at `v` is the singleton class of `σ`
  rw [galoisCharacterWeight_apply_of_unramified χ v hur,
    cyclotomicArtin_idealClass_of_isArithFrobAt F m v hv Q hσ,
    isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ((Quotient.out_eq _).trans
      (artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q σ hσ)))]

/-- **The ideal weight of a cyclotomic Galois character is a ray class character.** For a
character `χ` of `Gal(F/K)` with `F = K(μ_m)`, the ideal weight `galoisCharacterWeight χ` agrees,
on the integral ideals prime to `m`, with the ray class character `χ ∘ cyclotomicArtin K F m` of
`cyclotomicModulus K m`. -/
theorem galoisCharacterWeight_eq_onIdeals_cyclotomicArtin (χ : (F ≃ₐ[K] F) →* ℂˣ)
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    galoisCharacterWeight (L := F) χ (I : Ideal (𝓞 K)) =
      (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)) I : ℂ) := by
  -- both sides are multiplicative in `I`, and they agree on the primes `v ∤ m`
  let f : integralIdealsPrimeTo (cyclotomicModulus K m) →* ℂ :=
    (galoisCharacterWeight (L := F) χ).toMonoidWithZeroHom.toMonoidHom.comp
      (integralIdealsPrimeTo (cyclotomicModulus K m)).subtype
  let g : integralIdealsPrimeTo (cyclotomicModulus K m) →* ℂ :=
    (Units.coeHom ℂ).comp (RayClassCharacter.onIdeals (χ.comp (cyclotomicArtin K F m)))
  have hfg : f = g := integralIdealsAway_hom_ext fun v hv ↦ by
    simpa [f, g] using galoisCharacterWeight_asIdeal_eq_cyclotomicArtin χ v hv
  exact DFunLike.congr_fun hfg I

end MonoidHom
