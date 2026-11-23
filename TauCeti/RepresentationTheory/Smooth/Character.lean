/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# Smooth characters and twists of smooth representations

Let `G` be a topological group and `A` a monoid. A character `χ : G →* Aˣ` is *smooth*
(`TauCeti.IsSmoothCharacter χ`) when its kernel is open. For a group with separately continuous
multiplication this says equivalently that `χ` contains an open subgroup in its kernel, that `χ` is
locally constant, that `χ` is continuous for the discrete topology on `Aˣ`, and, when `A` is a
commutative semiring, that the rank-one representation `A(χ)` (`Representation.ofLinearCharacter
χ`) is smooth. For instance an unramified character `x ↦ t ^ v(x)` of the multiplicative group of
a nonarchimedean local field is smooth. Smooth characters with values in a commutative monoid form
a subgroup of the character group, and they pull back along continuous homomorphisms. Twisting a
representation by a smooth character (`Representation.charTwist`) preserves and reflects
smoothness.

## Main definitions

* `TauCeti.IsSmoothCharacter χ`: the kernel of `χ : G →* Aˣ` is open.

## Main results

* `TauCeti.isSmoothCharacter_iff_isSmooth`: `χ` is smooth exactly when `A(χ)` is.
* `TauCeti.isSmoothCharacter_iff_continuous_of_discreteTopology` and
  `TauCeti.isSmoothCharacter_iff_continuous`: `χ` is smooth exactly when it is continuous for a
  discrete topology on `Aˣ`.
* `TauCeti.isSmoothCharacter_iff_exists_openSubgroup`,
  `TauCeti.isSmoothCharacter_iff_isLocallyConstant`: `χ` is smooth exactly when its kernel contains
  an open subgroup, exactly when it is locally constant.
* `TauCeti.IsSmoothCharacter.mul`, `TauCeti.IsSmoothCharacter.inv`,
  `TauCeti.isSmoothCharacter_one`, `TauCeti.IsSmoothCharacter.div`,
  `TauCeti.IsSmoothCharacter.pow`, `TauCeti.IsSmoothCharacter.zpow`: smooth characters form a
  subgroup, which contains every character of a discrete group
  (`TauCeti.isSmoothCharacter_of_discreteTopology`).
* `TauCeti.IsSmoothCharacter.comp`, `TauCeti.IsSmoothCharacter.unitsMap`: smooth characters pull
  back along continuous homomorphisms and push forward along maps of coefficients.
* `TauCeti.IsSmoothCharacter.isSmooth_charTwist`,
  `TauCeti.IsSmoothCharacter.isSmooth_charTwist_iff`: the twist of a representation by a smooth
  character is smooth exactly when the representation is.

## References

* I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n, F) where F is a
  non-archimedean local field*, Russian Math. Surveys 31:3 (1976), Ch. I §1, 1.19, p. 11, and
  Ch. I §2, 2.25(c), p. 23.
-/

public section

open Representation

namespace TauCeti

variable {A G : Type*} [Group G] [TopologicalSpace G]

section Monoid

variable [Monoid A]

/-- A character `χ : G →* Aˣ` of a topological group is *smooth* when its kernel is open. -/
def IsSmoothCharacter (χ : G →* Aˣ) : Prop :=
  IsOpen (χ.ker : Set G)

/-- A character is smooth when its kernel is open. -/
theorem isSmoothCharacter_iff {χ : G →* Aˣ} : IsSmoothCharacter χ ↔ IsOpen (χ.ker : Set G) :=
  Iff.rfl

/-- The trivial character is smooth. -/
@[simp]
theorem isSmoothCharacter_one : IsSmoothCharacter (1 : G →* Aˣ) := by
  simp [isSmoothCharacter_iff, MonoidHom.ker_one]

/-- Every character of a discrete group is smooth. -/
theorem isSmoothCharacter_of_discreteTopology [DiscreteTopology G] (χ : G →* Aˣ) :
    IsSmoothCharacter χ :=
  isSmoothCharacter_iff.2 (isOpen_discrete _)

/-- A smooth character pulls back to a smooth character along a continuous homomorphism. -/
theorem IsSmoothCharacter.comp {H : Type*} [Group H] [TopologicalSpace H] {χ : G →* Aˣ}
    (hχ : IsSmoothCharacter χ) {f : H →* G} (hf : Continuous f) :
    IsSmoothCharacter (χ.comp f) := by
  rw [isSmoothCharacter_iff, ← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact (isSmoothCharacter_iff.1 hχ).preimage hf

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul G]

/-- A character is smooth exactly when it is continuous for a discrete topology on `Aˣ`. -/
theorem isSmoothCharacter_iff_continuous_of_discreteTopology [TopologicalSpace Aˣ]
    [DiscreteTopology Aˣ] {χ : G →* Aˣ} : IsSmoothCharacter χ ↔ Continuous χ :=
  (MonoidHom.continuous_iff_isOpen_ker χ).symm

/-- A character is smooth exactly when it is continuous for the discrete topology on `Aˣ`. -/
theorem isSmoothCharacter_iff_continuous {χ : G →* Aˣ} :
    IsSmoothCharacter χ ↔ @Continuous G Aˣ _ ⊥ χ := by
  let _ : TopologicalSpace Aˣ := ⊥
  have : DiscreteTopology Aˣ := ⟨rfl⟩
  exact isSmoothCharacter_iff_continuous_of_discreteTopology

/-- A character is smooth exactly when its kernel contains an open subgroup. -/
theorem isSmoothCharacter_iff_exists_openSubgroup {χ : G →* Aˣ} :
    IsSmoothCharacter χ ↔ ∃ U : OpenSubgroup G, (U : Subgroup G) ≤ χ.ker :=
  ⟨fun h ↦ ⟨⟨χ.ker, isSmoothCharacter_iff.1 h⟩, le_rfl⟩, fun ⟨U, hU⟩ ↦
    isSmoothCharacter_iff.2 (Subgroup.isOpen_mono hU U.isOpen)⟩

/-- A character is smooth exactly when it is locally constant. -/
theorem isSmoothCharacter_iff_isLocallyConstant {χ : G →* Aˣ} :
    IsSmoothCharacter χ ↔ IsLocallyConstant (χ : G → Aˣ) :=
  ⟨fun h ↦ χ.isLocallyConstant_of_isOpen_ker (isSmoothCharacter_iff.1 h), fun h ↦
    isSmoothCharacter_iff.2 (by rw [MonoidHom.coe_ker]; exact h {1})⟩

/-- The pushforward of a smooth character along a homomorphism of coefficient monoids is smooth. -/
theorem IsSmoothCharacter.unitsMap {B : Type*} [Monoid B] {χ : G →* Aˣ}
    (hχ : IsSmoothCharacter χ) (φ : A →* B) : IsSmoothCharacter ((Units.map φ).comp χ) :=
  isSmoothCharacter_iff.2 <| Subgroup.isOpen_mono
    (fun g hg ↦ by simp [MonoidHom.mem_ker.1 hg]) (isSmoothCharacter_iff.1 hχ)

end SeparatelyContinuousMul

end Monoid

section CommMonoid

variable [CommMonoid A]

/-- The inverse of a character is smooth exactly when the character is. -/
@[simp]
theorem isSmoothCharacter_inv_iff {χ : G →* Aˣ} : IsSmoothCharacter χ⁻¹ ↔ IsSmoothCharacter χ := by
  rw [isSmoothCharacter_iff, isSmoothCharacter_iff, MonoidHom.ker_inv]

/-- The inverse of a smooth character is smooth. -/
theorem IsSmoothCharacter.inv {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) :
    IsSmoothCharacter χ⁻¹ :=
  isSmoothCharacter_inv_iff.2 hχ

variable [SeparatelyContinuousMul G]

/-- The product of two smooth characters is smooth. -/
theorem IsSmoothCharacter.mul {χ ψ : G →* Aˣ} (hχ : IsSmoothCharacter χ)
    (hψ : IsSmoothCharacter ψ) : IsSmoothCharacter (χ * ψ) := by
  rw [isSmoothCharacter_iff] at hχ hψ ⊢
  refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ ψ.ker) (fun g hg ↦ ?_)
    (by rw [Subgroup.coe_inf]; exact hχ.inter hψ)
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
  simp [hg.1, hg.2]

/-- The quotient of two smooth characters is smooth. -/
theorem IsSmoothCharacter.div {χ ψ : G →* Aˣ} (hχ : IsSmoothCharacter χ)
    (hψ : IsSmoothCharacter ψ) : IsSmoothCharacter (χ / ψ) := by
  rw [div_eq_mul_inv]
  exact hχ.mul hψ.inv

/-- A natural power of a smooth character is smooth. -/
theorem IsSmoothCharacter.pow {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) (n : ℕ) :
    IsSmoothCharacter (χ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact ih.mul hχ

/-- An integer power of a smooth character is smooth. -/
theorem IsSmoothCharacter.zpow {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) (n : ℤ) :
    IsSmoothCharacter (χ ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hχ.pow n
  | negSucc n => rw [zpow_negSucc]; exact (hχ.pow (n + 1)).inv

end CommMonoid

section Representation

variable {V : Type*} [CommSemiring A] [SeparatelyContinuousMul G] [AddCommMonoid V] [Module A V]

/-- A character is smooth exactly when its rank-one representation `A(χ)` is smooth. -/
theorem isSmoothCharacter_iff_isSmooth {χ : G →* Aˣ} :
    IsSmoothCharacter χ ↔ IsSmooth (ofLinearCharacter χ) := by
  refine ⟨fun h ↦ ⟨fun x ↦ Subgroup.isOpen_mono (ker_le_stabilizer_ofLinearCharacter χ x)
    (isSmoothCharacter_iff.1 h)⟩, fun h ↦ ?_⟩
  rw [isSmoothCharacter_iff, ← stabilizer_ofLinearCharacter_one]
  exact IsSmooth.isOpen_stabilizer 1

/-- The twist of a smooth representation by a smooth character is smooth. -/
theorem IsSmoothCharacter.isSmooth_charTwist {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ)
    (ρ : Representation A G V) [IsSmooth ρ] : IsSmooth (charTwist χ ρ) := by
  refine ⟨fun v ↦ Subgroup.isOpen_mono (ker_inf_stabilizer_le_stabilizer_charTwist χ ρ v) ?_⟩
  rw [Subgroup.coe_inf]
  exact (isSmoothCharacter_iff.1 hχ).inter (IsSmooth.isOpen_stabilizer v)

/-- Twisting by a smooth character preserves and reflects smoothness. -/
theorem IsSmoothCharacter.isSmooth_charTwist_iff {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ)
    (ρ : Representation A G V) : IsSmooth (charTwist χ ρ) ↔ IsSmooth ρ := by
  refine ⟨fun h ↦ ?_, fun _ ↦ hχ.isSmooth_charTwist ρ⟩
  have := hχ.inv.isSmooth_charTwist (charTwist χ ρ)
  rwa [charTwist_charTwist, show χ⁻¹ * χ = 1 by ext; simp, charTwist_one] at this

end Representation

end TauCeti
