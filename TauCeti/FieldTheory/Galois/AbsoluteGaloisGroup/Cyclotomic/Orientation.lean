/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP
public import TauCeti.NumberTheory.Padics.PrincipalUnits
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# The cyclotomic orientation of the maximal pro-`p` Galois group

Let `K` be a field containing a primitive `p`-th root of unity `ζ`. Every `σ` in the absolute
Galois group fixes `ζ`, and the cyclotomic character reduced modulo `p` records the exponent `j`
with `σ ζ = ζ ^ j`. Hence every value of `localCyclotomicCharacter p K` is a principal unit
`≡ 1 mod p`, and the image of the character is a pro-`p` subgroup of `ℤ_pˣ`. A continuous
homomorphism to the profinite pro-`p` group `1 + pℤ_p` kills the pro-`p` kernel of the absolute
Galois group, so the character descends to its maximal pro-`p` quotient `G_K(p)`.

The descended character `cyclotomicOrientation p K hmu : G_K(p) →* ℤ_pˣ` is the arithmetic
orientation of `G_K(p)`, the character to compare with the canonical character of `G_K(p)` when
it is a Demushkin group. It takes the roots-of-unity witness `hmu` as an explicit argument, and no
unconditional descent of the full character is provided: for odd `p` and `K = ℚ_p` the character
reduced modulo `p` maps the absolute Galois group onto `(ℤ/pℤ)ˣ`, a nontrivial group of order
prime to `p`, so it does not factor through any pro-`p` group.

## Main definitions

* `TauCeti.cyclotomicOrientation p K hmu`: the cyclotomic character descended to
  `absoluteGaloisGroupProP p K`.

## Main results

* `TauCeti.localCyclotomicCharacter_mem_unitsPrincipal_one`: if `μ_p ⊆ K`, the cyclotomic
  character takes values in `1 + pℤ_p`.
* `TauCeti.isProP_range_localCyclotomicCharacter`: if `μ_p ⊆ K`, the image of the cyclotomic
  character is pro-`p`.
* `TauCeti.proPKernel_le_ker_localCyclotomicCharacter`: if `μ_p ⊆ K`, the pro-`p` kernel of the
  absolute Galois group lies in the kernel of the cyclotomic character.
* `TauCeti.cyclotomicOrientation_mk`, `TauCeti.cyclotomicOrientation_continuous`,
  `TauCeti.cyclotomicOrientation_range`: the orientation agrees with the character on classes,
  is continuous, and has the same image as the character.
-/

public section

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]

/-- If `K` contains a primitive `p`-th root of unity, every value of the cyclotomic character of
`K` is a principal unit `≡ 1 mod p`: an automorphism fixing a primitive `p`-th root of unity acts
on the `p`-th roots of unity by the exponent `1`. -/
theorem localCyclotomicCharacter_mem_unitsPrincipal_one (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (σ : Field.absoluteGaloisGroup K) : localCyclotomicCharacter p K σ ∈ unitsPrincipal p 1 := by
  obtain ⟨ζ, hζ⟩ := hmu
  -- A primitive `p`-th root of unity in `K` forces `p ≠ 0` in `K`, so the algebraic closure has
  -- all `p`-power roots of unity and Mathlib's defining equation of the character applies.
  have := hζ.neZero'
  have hξ : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) ζ) p :=
    hζ.map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hspec := cyclotomicCharacter.spec p (n := 1) σ.toRingEquiv
    (algebraMap K (AlgebraicClosure K) ζ) (by rw [pow_one, hξ.pow_eq_one])
  have hmod := ((hξ.isOfFinOrder hp.out.ne_zero).pow_eq_pow_iff_modEq).mp
    (((pow_one _).trans (σ.commutes ζ).symm).trans hspec)
  rw [← hξ.eq_orderOf] at hmod
  rw [mem_unitsPrincipal_iff_toZModPow, localCyclotomicCharacter_apply]
  set c := PadicInt.toZModPow 1 (cyclotomicCharacter (AlgebraicClosure K) p σ.toRingEquiv : ℤ_[p])
  rw [← ZMod.natCast_zmod_val c, ← Nat.cast_one (R := ZMod (p ^ 1)), ZMod.natCast_eq_natCast_iff]
  simpa using hmod.symm

variable (p K) in
/-- If `K` contains a primitive `p`-th root of unity, the image of the cyclotomic character of
`K` lies in the principal unit group `1 + pℤ_p`. -/
theorem range_localCyclotomicCharacter_le_unitsPrincipal_one
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    (localCyclotomicCharacter p K).range ≤ unitsPrincipal p 1 := by
  rintro _ ⟨σ, rfl⟩
  exact localCyclotomicCharacter_mem_unitsPrincipal_one hmu σ

variable (p K) in
/-- If `K` contains a primitive `p`-th root of unity, the image of the cyclotomic character of
`K` is a pro-`p` subgroup of `ℤ_pˣ`. -/
theorem isProP_range_localCyclotomicCharacter (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    IsProP p (localCyclotomicCharacter p K).range :=
  (isProP_iff_le_unitsPrincipal_one _).mpr
    (range_localCyclotomicCharacter_le_unitsPrincipal_one p K hmu)

variable (p K) in
/-- If `K` contains a primitive `p`-th root of unity, the pro-`p` kernel of the absolute Galois
group of `K` lies in the kernel of the cyclotomic character. -/
theorem proPKernel_le_ker_localCyclotomicCharacter (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    proPKernel p (Field.absoluteGaloisGroup K) ≤ (localCyclotomicCharacter p K).ker := by
  -- Corestrict the character to the profinite pro-`p` group `1 + pℤ_p`.
  let χ₁ := (localCyclotomicCharacter p K).codRestrict (unitsPrincipal p 1)
    (localCyclotomicCharacter_mem_unitsPrincipal_one hmu)
  have hχ₁ : Continuous χ₁ :=
    (localCyclotomicCharacter_continuous p K).subtype_mk
      (localCyclotomicCharacter_mem_unitsPrincipal_one hmu)
  rw [← MonoidHom.ker_codRestrict _ _ (localCyclotomicCharacter_mem_unitsPrincipal_one hmu)]
  exact proPKernel_le_ker (isProP_unitsPrincipal p one_pos) χ₁ hχ₁

variable (p K) in
/-- The **cyclotomic orientation** of the maximal pro-`p` Galois group: when `K` contains a
primitive `p`-th root of unity, the cyclotomic character `localCyclotomicCharacter p K` descends
to `absoluteGaloisGroupProP p K`. -/
noncomputable def cyclotomicOrientation (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    absoluteGaloisGroupProP p K →* ℤ_[p]ˣ :=
  (ContinuousMonoidHom.quotientLift _
    ⟨localCyclotomicCharacter p K, localCyclotomicCharacter_continuous p K⟩
    (proPKernel_le_ker_localCyclotomicCharacter p K hmu)).toMonoidHom

/-- The cyclotomic orientation of the class of `g` is the cyclotomic character of `g`. -/
@[simp]
theorem cyclotomicOrientation_mk (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (g : Field.absoluteGaloisGroup K) :
    cyclotomicOrientation p K hmu (QuotientGroup.mk g) = localCyclotomicCharacter p K g :=
  ContinuousMonoidHom.quotientLift_mk _ _ _ g

/-- The cyclotomic orientation restricts to the cyclotomic character along the quotient map. -/
@[simp]
theorem cyclotomicOrientation_comp_mk (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    (cyclotomicOrientation p K hmu).comp
        (maximalProPQuotient.mk p (Field.absoluteGaloisGroup K)) =
      localCyclotomicCharacter p K :=
  congrArg ContinuousMonoidHom.toMonoidHom
    (ContinuousMonoidHom.quotientLift_comp_quotientMk _ _
      (proPKernel_le_ker_localCyclotomicCharacter p K hmu))

/-- The cyclotomic orientation is continuous for the quotient topology on the maximal pro-`p`
Galois group. -/
theorem cyclotomicOrientation_continuous (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Continuous (cyclotomicOrientation p K hmu) :=
  (ContinuousMonoidHom.quotientLift _ _
    (proPKernel_le_ker_localCyclotomicCharacter p K hmu)).continuous

/-- The cyclotomic orientation and the cyclotomic character have the same image in `ℤ_pˣ`,
because the quotient map onto the maximal pro-`p` Galois group is surjective. -/
@[simp]
theorem cyclotomicOrientation_range (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    (cyclotomicOrientation p K hmu).range = (localCyclotomicCharacter p K).range := by
  rw [← cyclotomicOrientation_comp_mk hmu, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (maximalProPQuotient.mk_surjective p _),
    ← MonoidHom.range_eq_map]

end TauCeti
