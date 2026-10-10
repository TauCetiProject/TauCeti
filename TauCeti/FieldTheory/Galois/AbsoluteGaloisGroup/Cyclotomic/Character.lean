/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# The cyclotomic character of an absolute Galois group

The character `localCyclotomicCharacter p K` records the action of
`Field.absoluteGaloisGroup K` on roots of unity of `p`-power order in an algebraic closure.
It is Mathlib's cyclotomic character restricted from ring automorphisms to the Galois group.
The pointwise equation fixes this choice of character for later arithmetic comparisons.
Two elements whose characters agree modulo `p ^ n` act alike on the `p ^ n`-th roots of unity
(`apply_eq_apply_of_toZModPow_localCyclotomicCharacter_eq`); in particular an element whose
character is `1` modulo `p ^ n` fixes them
(`apply_eq_self_of_toZModPow_localCyclotomicCharacter_eq_one`), and powers `g ^ i` and `g ^ j` with
`i ≡ j` modulo `φ(p ^ n)` act alike on them (`apply_pow_eq_apply_pow_of_modEq_totient`).
Its bundled form `continuousLocalCyclotomicCharacter p K` is the continuous homomorphism that the
twisted coefficients `TauCeti.ZModTwist` and the prescription property
`TauCeti.HasPrescriptionProperty` take. It factors through the topological abelianization as
`abelianizedLocalCyclotomicCharacter p K`, which is how it is evaluated on Artin symbols.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]

/-- The `p`-adic cyclotomic character on the absolute Galois group of `K`. -/
noncomputable def localCyclotomicCharacter :
    Field.absoluteGaloisGroup K →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure K) p).comp
    (MulSemiringAction.toRingAut Gal(AlgebraicClosure K/K) (AlgebraicClosure K))

/-- The local character is Mathlib's cyclotomic character evaluated on the underlying
ring automorphism. -/
@[simp]
theorem localCyclotomicCharacter_apply (σ : Field.absoluteGaloisGroup K) :
    localCyclotomicCharacter p K σ =
      cyclotomicCharacter (AlgebraicClosure K) p σ.toRingEquiv :=
  (rfl)

variable {p K} in
/-- Two elements of `Field.absoluteGaloisGroup K` whose cyclotomic characters agree modulo `p ^ n`
agree on the `p ^ n`-th roots of unity. -/
theorem apply_eq_apply_of_toZModPow_localCyclotomicCharacter_eq
    [∀ i, HasEnoughRootsOfUnity (AlgebraicClosure K) (p ^ i)]
    {σ₁ σ₂ : Field.absoluteGaloisGroup K} {n : ℕ}
    (h : PadicInt.toZModPow n (localCyclotomicCharacter p K σ₁ : ℤ_[p]) =
      PadicInt.toZModPow n (localCyclotomicCharacter p K σ₂ : ℤ_[p]))
    {z : AlgebraicClosure K} (hz : z ^ p ^ n = 1) :
    DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ₁ z =
      DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ₂ z := by
  rw [localCyclotomicCharacter_apply, localCyclotomicCharacter_apply] at h
  exact (cyclotomicCharacter.spec p σ₁.toRingEquiv z hz).trans
    (h ▸ (cyclotomicCharacter.spec p σ₂.toRingEquiv z hz).symm)

variable {p K} in
/-- An element of `Field.absoluteGaloisGroup K` whose cyclotomic character is `1` modulo `p ^ n`
fixes the `p ^ n`-th roots of unity. -/
theorem apply_eq_self_of_toZModPow_localCyclotomicCharacter_eq_one
    [∀ i, HasEnoughRootsOfUnity (AlgebraicClosure K) (p ^ i)]
    {σ : Field.absoluteGaloisGroup K} {n : ℕ}
    (h : PadicInt.toZModPow n (localCyclotomicCharacter p K σ : ℤ_[p]) = 1)
    {z : AlgebraicClosure K} (hz : z ^ p ^ n = 1) :
    DFunLike.coe (F := Gal(AlgebraicClosure K/K)) σ z = z :=
  apply_eq_apply_of_toZModPow_localCyclotomicCharacter_eq (σ₂ := 1)
    (by rw [h, map_one, Units.val_one, map_one]) hz

variable {p K} in
/-- Powers of `g ∈ Field.absoluteGaloisGroup K` whose exponents agree modulo `φ(p ^ n)` agree on
the `p ^ n`-th roots of unity, because `(ℤ/p^n)ˣ` has order `φ(p ^ n)`. -/
theorem apply_pow_eq_apply_pow_of_modEq_totient
    [∀ i, HasEnoughRootsOfUnity (AlgebraicClosure K) (p ^ i)]
    (g : Field.absoluteGaloisGroup K) {n i j : ℕ}
    (hij : i ≡ j [MOD (p ^ n).totient]) {z : AlgebraicClosure K} (hz : z ^ p ^ n = 1) :
    DFunLike.coe (F := Gal(AlgebraicClosure K/K)) (g ^ i) z =
      DFunLike.coe (F := Gal(AlgebraicClosure K/K)) (g ^ j) z := by
  refine apply_eq_apply_of_toZModPow_localCyclotomicCharacter_eq ?_ hz
  set v := Units.map (PadicInt.toZModPow n).toMonoidHom (localCyclotomicCharacter p K g)
  have h : v ^ i = v ^ j := by
    rw [pow_eq_pow_mod i (ZMod.pow_totient v), pow_eq_pow_mod j (ZMod.pow_totient v), hij]
  rw [map_pow, map_pow]
  simpa [v] using congrArg Units.val h

/-- The cyclotomic character is continuous for the Krull topology on the absolute
Galois group and the `p`-adic topology on the units. -/
theorem localCyclotomicCharacter_continuous :
    Continuous (localCyclotomicCharacter p K) := by
  exact cyclotomicCharacter.continuous p K (AlgebraicClosure K)

/-- The `p`-adic cyclotomic character on the absolute Galois group of `K`, as a continuous
homomorphism. -/
noncomputable def continuousLocalCyclotomicCharacter :
    Field.absoluteGaloisGroup K →ₜ* ℤ_[p]ˣ :=
  ⟨localCyclotomicCharacter p K, localCyclotomicCharacter_continuous p K⟩

/-- The bundled continuous character takes the values of the cyclotomic character. -/
@[simp]
theorem continuousLocalCyclotomicCharacter_apply (σ : Field.absoluteGaloisGroup K) :
    continuousLocalCyclotomicCharacter p K σ = localCyclotomicCharacter p K σ :=
  (rfl)

/-- The `p`-adic cyclotomic character on the topological abelianization of the absolute Galois
group of `K`, through which the cyclotomic character factors since `ℤ_[p]ˣ` is commutative. -/
noncomputable def abelianizedLocalCyclotomicCharacter :
    Field.absoluteGaloisGroupAbelianization K →ₜ* ℤ_[p]ˣ :=
  TopologicalAbelianization.lift (continuousLocalCyclotomicCharacter p K)

/-- On the class of `σ`, the abelianized cyclotomic character is the cyclotomic character
of `σ`. -/
@[simp]
theorem abelianizedLocalCyclotomicCharacter_mk (σ : Field.absoluteGaloisGroup K) :
    abelianizedLocalCyclotomicCharacter p K (σ : Field.absoluteGaloisGroupAbelianization K) =
      localCyclotomicCharacter p K σ :=
  TopologicalAbelianization.lift_mk _ σ

end TauCeti
