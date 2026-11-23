/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RepresentationTheory.Smooth.Basic

/-!
# Smooth characters and twists of smooth representations

Let `G` be a topological group and `A` a commutative ring. A character `χ : G →* Aˣ` is *smooth*
(`TauCeti.IsSmoothCharacter χ`) when its kernel is open. Equivalently, the rank-one representation
`A(χ)` (`Representation.ofLinearCharacter χ`) is smooth, and, for a group with separately
continuous multiplication, `χ` is continuous for the discrete topology on `Aˣ`. For instance an
unramified character `x ↦ t ^ v(x)` of the multiplicative group of a nonarchimedean local field is
smooth. Smooth characters are closed under products and inverses. Twisting a smooth
representation by a smooth character (`Representation.charTwist`) gives a smooth representation,
and does not change the invariants of a subgroup on which the character is trivial.

## Main definitions

* `TauCeti.IsSmoothCharacter χ`: the kernel of `χ : G →* Aˣ` is open.

## Main results

* `TauCeti.isSmoothCharacter_iff_isSmooth`: `χ` is smooth exactly when `A(χ)` is.
* `TauCeti.isSmoothCharacter_iff_continuous`: `χ` is smooth exactly when it is continuous for the
  discrete topology on `Aˣ`.
* `TauCeti.IsSmoothCharacter.mul`, `TauCeti.IsSmoothCharacter.inv`,
  `TauCeti.isSmoothCharacter_one`: smooth characters form a subgroup, which contains every
  character of a discrete group (`TauCeti.isSmoothCharacter_of_discreteTopology`).
* `TauCeti.IsSmoothCharacter.isSmooth_charTwist`: the twist of a smooth representation by a smooth
  character is smooth.
* `TauCeti.invariants_charTwist_comp_subtype`: on a subgroup inside the kernel of `χ`, twisting by
  `χ` does not change the invariants.

## References

* I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n, F) where F is a
  non-archimedean local field*, Russian Math. Surveys 31:3 (1976), Ch. I §1, 1.19, p. 11, and
  Ch. I §2, 2.25(c), p. 23.
-/

public section

open Representation

namespace TauCeti

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G]
  [AddCommGroup V] [Module A V]

/-- A character `χ : G →* Aˣ` of a topological group is *smooth* when its kernel is open. -/
def IsSmoothCharacter (χ : G →* Aˣ) : Prop :=
  IsOpen (χ.ker : Set G)

/-- A character is smooth when its kernel is open. -/
theorem isSmoothCharacter_iff {χ : G →* Aˣ} : IsSmoothCharacter χ ↔ IsOpen (χ.ker : Set G) :=
  Iff.rfl

omit [TopologicalSpace G] in
/-- The stabilizer of `1` in the rank-one representation `A(χ)` is the kernel of `χ`. -/
private theorem stabilizer_ofLinearCharacter_one (χ : G →* Aˣ) :
    (ofLinearCharacter χ).stabilizer 1 = χ.ker := by
  ext g
  simp [mem_stabilizer, Units.val_eq_one]

omit [TopologicalSpace G] in
/-- The kernel of `χ` fixes every vector of `A(χ)`. -/
private theorem ker_le_stabilizer_ofLinearCharacter (χ : G →* Aˣ) (x : A) :
    χ.ker ≤ (ofLinearCharacter χ).stabilizer x := fun g hg ↦ by
  simp [mem_stabilizer, MonoidHom.mem_ker.1 hg]

/-- A character is smooth exactly when its rank-one representation `A(χ)` is smooth. -/
theorem isSmoothCharacter_iff_isSmooth [SeparatelyContinuousMul G] {χ : G →* Aˣ} :
    IsSmoothCharacter χ ↔ IsSmooth (ofLinearCharacter χ) := by
  refine ⟨fun h ↦ ⟨fun x ↦ Subgroup.isOpen_mono (ker_le_stabilizer_ofLinearCharacter χ x) h⟩,
    fun h ↦ ?_⟩
  rw [isSmoothCharacter_iff, ← stabilizer_ofLinearCharacter_one]
  exact IsSmooth.isOpen_stabilizer 1

/-- A character is smooth exactly when it is continuous for the discrete topology on `Aˣ`. -/
theorem isSmoothCharacter_iff_continuous [SeparatelyContinuousMul G] {χ : G →* Aˣ} :
    IsSmoothCharacter χ ↔ @Continuous G Aˣ _ ⊥ χ := by
  let _ : TopologicalSpace Aˣ := ⊥
  have : DiscreteTopology Aˣ := ⟨rfl⟩
  refine ⟨fun h ↦ continuous_def.2 fun s _ ↦ isOpen_iff_forall_mem_open.2 fun g hg ↦
    ⟨(g⁻¹ * ·) ⁻¹' χ.ker, fun x hx ↦ ?_,
      h.preimage SeparatelyContinuousMul.continuous_const_mul, by simp⟩, fun h ↦ ?_⟩
  · have hgx : χ g = χ x := inv_mul_eq_one.1 (by simpa using hx)
    rw [Set.mem_preimage, ← hgx]
    exact hg
  · exact (isOpen_discrete ({1} : Set Aˣ)).preimage h

/-- The trivial character is smooth. -/
theorem isSmoothCharacter_one : IsSmoothCharacter (1 : G →* Aˣ) := by
  simp [isSmoothCharacter_iff, MonoidHom.ker_one]

/-- Every character of a discrete group is smooth. -/
theorem isSmoothCharacter_of_discreteTopology [DiscreteTopology G] (χ : G →* Aˣ) :
    IsSmoothCharacter χ :=
  isOpen_discrete _

/-- The product of two smooth characters is smooth. -/
theorem IsSmoothCharacter.mul [SeparatelyContinuousMul G] {χ ψ : G →* Aˣ}
    (hχ : IsSmoothCharacter χ) (hψ : IsSmoothCharacter ψ) : IsSmoothCharacter (χ * ψ) := by
  have h : IsOpen ((χ.ker ⊓ ψ.ker : Subgroup G) : Set G) := hχ.inter hψ
  exact Subgroup.isOpen_mono (fun g (hg : g ∈ χ.ker ⊓ ψ.ker) ↦ by
    simp [MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2]) h

/-- The inverse of a smooth character is smooth. -/
theorem IsSmoothCharacter.inv {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) :
    IsSmoothCharacter χ⁻¹ := by
  have : χ⁻¹.ker = χ.ker := by
    ext g
    simp
  rwa [isSmoothCharacter_iff, this]

/-- The twist of a smooth representation by a smooth character is smooth. -/
theorem IsSmoothCharacter.isSmooth_charTwist [SeparatelyContinuousMul G] {χ : G →* Aˣ}
    (hχ : IsSmoothCharacter χ) (ρ : Representation A G V) [IsSmooth ρ] :
    IsSmooth (charTwist χ ρ) := by
  refine ⟨fun v ↦ ?_⟩
  have h : IsOpen ((χ.ker ⊓ ρ.stabilizer v : Subgroup G) : Set G) :=
    hχ.inter (IsSmooth.isOpen_stabilizer v)
  exact Subgroup.isOpen_mono (fun g (hg : g ∈ χ.ker ⊓ ρ.stabilizer v) ↦ by
    simp [mem_stabilizer, MonoidHom.mem_ker.1 hg.1, mem_stabilizer.1 hg.2]) h

omit [TopologicalSpace G] in
/-- On a subgroup inside the kernel of `χ`, twisting by `χ` does not change the invariants. -/
theorem invariants_charTwist_comp_subtype (χ : G →* Aˣ) (ρ : Representation A G V)
    {U : Subgroup G} (hU : U ≤ χ.ker) :
    invariants ((charTwist χ ρ).comp U.subtype) = invariants (ρ.comp U.subtype) := by
  ext v
  simp [mem_invariants, MonoidHom.mem_ker.1 (hU _)]

end TauCeti
