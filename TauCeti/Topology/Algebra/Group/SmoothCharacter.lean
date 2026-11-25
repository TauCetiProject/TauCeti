/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# Smooth characters

Let `G` be a topological group and `A` a monoid. A character `χ : G →* Aˣ` is *smooth*
(`TauCeti.IsSmoothCharacter χ`) when its kernel is open. For a group with separately continuous
multiplication this says equivalently that `χ` contains an open subgroup in its kernel, that `χ` is
locally constant, and that `χ` is continuous for the discrete topology on `Aˣ`. For instance an
unramified character `x ↦ t ^ v(x)` of the multiplicative group of a nonarchimedean local field is
smooth. Smooth characters pull back along continuous homomorphisms. For a group with separately
continuous multiplication, smooth characters with values in a commutative monoid form a subgroup of
the character group, and they push forward along maps of coefficients.

The representation-theoretic side, the rank-one representation of a smooth character and twists
by smooth characters, is in `TauCeti.RepresentationTheory.Smooth.Character`.

## Main definitions

* `TauCeti.IsSmoothCharacter χ`: the kernel of `χ : G →* Aˣ` is open.

## Main results

The results below other than `TauCeti.IsSmoothCharacter.comp`, `TauCeti.IsSmoothCharacter.inv`,
`TauCeti.isSmoothCharacter_inv_iff`, `TauCeti.isSmoothCharacter_one`,
`TauCeti.isSmoothCharacter_of_discreteTopology` and
`TauCeti.IsSmoothCharacter.isOpen_singleton_one_of_injective` assume `SeparatelyContinuousMul G`.

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
* `TauCeti.IsSmoothCharacter.isOpen_singleton_one_of_injective`: a group with an injective smooth
  character is discrete, that is `{1}` is open.

## References

* I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n, F) where F is a
  non-archimedean local field*, Russian Math. Surveys 31:3 (1976), Ch. I §1, 1.19, p. 11.
-/

public section

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
@[simp]
theorem isSmoothCharacter_of_discreteTopology [DiscreteTopology G] (χ : G →* Aˣ) :
    IsSmoothCharacter χ :=
  isSmoothCharacter_iff.2 (isOpen_discrete _)

/-- A smooth character pulls back to a smooth character along a continuous homomorphism. -/
theorem IsSmoothCharacter.comp {H : Type*} [Group H] [TopologicalSpace H] {χ : G →* Aˣ}
    (hχ : IsSmoothCharacter χ) {f : H →* G} (hf : Continuous f) :
    IsSmoothCharacter (χ.comp f) := by
  rw [isSmoothCharacter_iff, ← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact (isSmoothCharacter_iff.1 hχ).preimage hf

/-- An injective smooth character has kernel `{1}`, so `{1}` is open. -/
theorem IsSmoothCharacter.isOpen_singleton_one_of_injective {χ : G →* Aˣ}
    (hχ : IsSmoothCharacter χ) (hinj : Function.Injective χ) : IsOpen ({1} : Set G) := by
  rwa [isSmoothCharacter_iff, (MonoidHom.ker_eq_bot_iff χ).mpr hinj, Subgroup.coe_bot] at hχ

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
  have : DiscreteTopology Aˣ := discreteTopology_bot _
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
    isSmoothCharacter_iff.2 (by rw [MonoidHom.coe_ker]; exact h.isOpen_fiber 1)⟩

/-- The pushforward of a smooth character along a homomorphism of coefficient monoids is smooth. -/
theorem IsSmoothCharacter.unitsMap {B : Type*} [Monoid B] {χ : G →* Aˣ}
    (hχ : IsSmoothCharacter χ) (φ : A →* B) : IsSmoothCharacter ((Units.map φ).comp χ) :=
  isSmoothCharacter_iff_isLocallyConstant.2
    ((isSmoothCharacter_iff_isLocallyConstant.1 hχ).comp (Units.map φ))

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
    (hψ : IsSmoothCharacter ψ) : IsSmoothCharacter (χ * ψ) :=
  isSmoothCharacter_iff_isLocallyConstant.2
    ((isSmoothCharacter_iff_isLocallyConstant.1 hχ).mul
      (isSmoothCharacter_iff_isLocallyConstant.1 hψ))

/-- The quotient of two smooth characters is smooth. -/
theorem IsSmoothCharacter.div {χ ψ : G →* Aˣ} (hχ : IsSmoothCharacter χ)
    (hψ : IsSmoothCharacter ψ) : IsSmoothCharacter (χ / ψ) := by
  rw [div_eq_mul_inv]
  exact hχ.mul hψ.inv

/-- A natural power of a smooth character is smooth. -/
theorem IsSmoothCharacter.pow {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) (n : ℕ) :
    IsSmoothCharacter (χ ^ n) :=
  isSmoothCharacter_iff_isLocallyConstant.2
    ((isSmoothCharacter_iff_isLocallyConstant.1 hχ).comp fun a ↦ a ^ n)

/-- An integer power of a smooth character is smooth. -/
theorem IsSmoothCharacter.zpow {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) (n : ℤ) :
    IsSmoothCharacter (χ ^ n) :=
  isSmoothCharacter_iff_isLocallyConstant.2
    ((isSmoothCharacter_iff_isLocallyConstant.1 hχ).comp fun a ↦ a ^ n)

end CommMonoid

end TauCeti
