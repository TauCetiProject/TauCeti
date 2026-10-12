/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Pro-`ℓ` subgroups of the absolute Galois group fix the `ℓ`-th roots of unity

Let `K` be a field and `ℓ` a prime invertible in `K`. The absolute Galois group `G_K = Gal(Kˢ/K)`
acts on the `ℓ`-th roots of unity `μ_ℓ(Kˢ)`, a group of order `ℓ`, through the cyclotomic
character `G_K → (ℤ/ℓ)ˣ`. A pro-`ℓ` subgroup `P` of `G_K` has an `ℓ`-group as image in the group
`(ℤ/ℓ)ˣ` of order `ℓ - 1`, so `P` acts trivially on `μ_ℓ`
(`TauCeti.smul_kummerCoeff_eq_self_of_isProP`). In particular a Sylow pro-`ℓ` subgroup of `G_K`
fixes `μ_ℓ`, so `μ_ℓ` is a trivial coefficient module of order `ℓ` for it; this is how the
`ℓ`-cohomological dimension of `G_K` is computed on `μ_ℓ`.

## Main results

* `TauCeti.smul_kummerCoeff_eq_self_of_isProP`: a pro-`ℓ` subgroup of `G_K` fixes `μ_ℓ(Kˢ)`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.3, proof of Prop. 12.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **A pro-`ℓ` subgroup of `G_K` fixes the `ℓ`-th roots of unity**, for a prime `ℓ` invertible in
`K`: its image under the cyclotomic character `G_K → (ℤ/ℓ)ˣ` is an `ℓ`-group in a group of order
`ℓ - 1`, hence trivial. -/
theorem smul_kummerCoeff_eq_self_of_isProP (hℓ : IsUnit (ℓ : K))
    {P : Subgroup (AbsoluteGaloisGroup K)} (hP : IsProP ℓ P) (g : P) (x : KummerCoeff K ℓ) :
    g • x = x := by
  have : NeZero (ℓ : K) := ⟨hℓ.ne_zero⟩
  have hℓ1 : (1 : ZMod ℓ).val = 1 := ZMod.val_one ℓ
  set L := SeparableClosure K
  have hcard := HasEnoughRootsOfUnity.natCard_rootsOfUnity L ℓ
  let χ := modularCyclotomicCharacter L hcard
  let ρ := MulSemiringAction.toRingAut (AbsoluteGaloisGroup K) L
  let f : P →* (ZMod ℓ)ˣ := (χ.comp ρ).comp P.subtype
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L ℓ
  have hζu := hζ.isUnit_unit (Fact.out : ℓ.Prime).ne_zero
  -- an automorphism fixing `ζ` fixes every `ℓ`-th root of unity, so has trivial character
  have hker : IsOpen (f.ker : Set P) := by
    refine Subgroup.isOpen_mono (H₁ := (MulAction.stabilizer (AbsoluteGaloisGroup K) ζ).comap
      P.subtype) (fun g hg => ?_) ((stabilizer_isOpen_of_isIntegral ζ).preimage
        continuous_subtype_val)
    rw [MonoidHom.mem_ker]
    refine Units.ext (modularCyclotomicCharacter.unique L hcard (ρ g) (c := 1) fun t ht => ?_).symm
    obtain ⟨i, -, rfl⟩ := hζu.eq_pow_of_mem_rootsOfUnity ht
    have hg' : (g : AbsoluteGaloisGroup K) ζ = ζ := by
      rw [← AlgEquiv.smul_def]
      exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_comap.1 hg)
    rw [hℓ1, pow_one, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]
    exact congrArg (· ^ i) hg'
  -- the character is trivial on `P`
  have hf : ∀ g, f g = 1 := fun g => by
    obtain ⟨k, hk⟩ := hP.isPGroup_range f hker ⟨f g, g, rfl⟩
    have h₁ : f g ^ ℓ ^ k = 1 := congrArg Subtype.val hk
    have h₂ : f g ^ (ℓ - 1) = 1 := by
      rw [← ZMod.card_units ℓ]
      exact pow_card_eq_one
    have hcop : (ℓ ^ k).Coprime (ℓ - 1) :=
      Nat.Coprime.pow_left _ ((Nat.coprime_self_sub_right (Fact.out : ℓ.Prime).one_le).2
        (Nat.coprime_one_right _))
    have h : f g ^ Nat.gcd (ℓ ^ k) (ℓ - 1) = 1 := pow_gcd_eq_one.2 ⟨h₁, h₂⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  -- unfolding `f` and the two compositions, `f g` is `χ (ρ g)`
  have hχ : χ (ρ g) = 1 := by simpa only [f, MonoidHom.comp_apply, Subgroup.coe_subtype] using hf g
  refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
  have h := modularCyclotomicCharacter.spec L hcard (ρ g) x.toMul.2
  rw [hχ, Units.val_one, hℓ1, pow_one] at h
  -- `MulSemiringAction.toRingAut` is the action of `g` on `Kˢ`, which is evaluation
  have hρ : ∀ y, ρ g y = (g : AbsoluteGaloisGroup K) y := fun y => AlgEquiv.smul_def _ y
  rw [hρ] at h
  simpa [Additive.toMul_smul, rootsOfUnity.coe_smul, Subgroup.smul_def, AlgEquiv.smul_units_def]
    using h

end TauCeti
