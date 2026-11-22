/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.TFAE
public import TauCeti.Algebra.AddCircle
public import TauCeti.RingTheory.LocalRing.Socle

import Mathlib.RingTheory.Flat.Tensor
import TauCeti.Algebra.Module.CharacterModule

/-!
# Matlis generators of a finite commutative ring

For a commutative ring `R`, the character module `E_R = Hom_ℤ(R, ℚ/ℤ)` is an `R`-module through
`(r • χ) s = χ (r s)`. A character `χ` is a **Matlis generator** when its kernel contains no nonzero
ideal of `R`. Since the kernel of `r ↦ r • χ` is an ideal on which `χ` vanishes, and every ideal on
which `χ` vanishes lies in that kernel, this says exactly that `r ↦ r • χ` is injective.

When `R` is finite, `E_R` has as many elements as `R`, so a Matlis generator makes `r ↦ r • χ` an
isomorphism `R ≃ E_R` of `R`-modules, and any two Matlis generators differ by a unique unit of `R`.
Since `R` is flat over itself, `E_R` is an injective `R`-module, so a finite ring with a Matlis
generator is self-injective. For a finite local ring the converse holds, and both properties are
equivalent to the simplicity of the socle, the ideal of elements killed by the maximal ideal: a
character that does not vanish at a nonzero socle element is a Matlis generator when the socle is
simple, because every nonzero ideal contains the whole socle.

For a finite self-injective coefficient ring `R` of residue characteristic `p`, the characters land
in `ℚ_p/ℤ_p`, and a Matlis generator `λ` is the trace that turns the additive Cartier dual
`Hom_ℤ(A, ℚ_p/ℤ_p)` of a finite `R`-module `A` into its `R`-linear dual `Hom_R(A, R)`. This is the
comparison through which Burns, Sakamoto and Sano state Poitou–Tate duality and Selmer sequences
`R`-linearly over arbitrary finite self-injective coefficient rings.

## Main definitions

* `CharacterModule.IsMatlisGenerator`: no nonzero ideal lies in the kernel of the character.
* `CharacterModule.IsMatlisGenerator.linearEquiv`: over a finite ring, the isomorphism
  `R ≃ₗ[R] CharacterModule R`, `r ↦ r • χ`, given by a Matlis generator `χ`.

## Main results

* `CharacterModule.isMatlisGenerator_iff_injective`: `χ` is a Matlis generator exactly when
  `r ↦ r • χ` is injective; over a finite ring, `CharacterModule.isMatlisGenerator_iff_bijective`
  upgrades this to bijectivity.
* `CharacterModule.IsMatlisGenerator.existsUnique_units_smul_eq` and
  `CharacterModule.IsMatlisGenerator.isMatlisGenerator_iff`: over a finite ring, the Matlis
  generators are the unit multiples of one of them, and the unit is unique.
* `CharacterModule.IsMatlisGenerator.moduleInjective`: a finite ring with a Matlis generator is
  self-injective.
* `CharacterModule.exists_isMatlisGenerator_of_isSimpleModule`: an artinian local ring with a
  simple socle has a Matlis generator.
* `CharacterModule.tfae_exists_isMatlisGenerator`: for a finite local ring, having a Matlis
  generator, being self-injective and having a simple socle are equivalent.
* `CharacterModule.isMatlisGenerator_toRatAddCircle`: `k ↦ k / n` is a Matlis generator of
  `ℤ/n`, while the zero character is never one (`CharacterModule.not_isMatlisGenerator_zero`).

## References

* D. Burns, R. Sakamoto and T. Sano, *On the theory of higher rank Euler, Kolyvagin and Stark
  systems, II*, arXiv:1805.08448v1, §3.1.
* T. Y. Lam, *Lectures on modules and rings*, Graduate Texts in Mathematics 189, Springer, 1999,
  §3D, §15A and Theorem 15.27.
* The Stacks project, Proposition 47.7.8, Tag 08Z9.
-/

public section

namespace CharacterModule

open IsLocalRing TauCeti.IsLocalRing Submodule

variable {R : Type*} [CommRing R]

/-- A character `χ : R → ℚ/ℤ` of a commutative ring is a **Matlis generator** when the only ideal
of `R` contained in its kernel is the zero ideal. Equivalently (`isMatlisGenerator_iff_injective`),
`r ↦ r • χ` embeds `R` in its character module. -/
def IsMatlisGenerator (χ : CharacterModule R) : Prop :=
  ∀ I : Ideal R, (∀ x ∈ I, χ x = 0) → I = ⊥

variable {χ ψ : CharacterModule R}

theorem isMatlisGenerator_def :
    χ.IsMatlisGenerator ↔ ∀ I : Ideal R, (∀ x ∈ I, χ x = 0) → I = ⊥ :=
  Iff.rfl

/-- A Matlis generator kills no nonzero ideal. -/
theorem IsMatlisGenerator.eq_bot (hχ : χ.IsMatlisGenerator) {I : Ideal R}
    (hI : ∀ x ∈ I, χ x = 0) : I = ⊥ :=
  hχ I hI

/-- A character is a Matlis generator exactly when `r ↦ r • χ` is injective: the kernel of this map
is an ideal on which `χ` vanishes, and it contains every such ideal. -/
theorem isMatlisGenerator_iff_injective :
    χ.IsMatlisGenerator ↔
      Function.Injective (LinearMap.toSpanSingleton R (CharacterModule R) χ) := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun h r hr ↦ ?_, fun h I hI ↦ (Submodule.eq_bot_iff I).mpr fun r hr ↦ h r ?_⟩
  · -- the principal ideal `(r)` lies in the kernel of `χ`
    refine Ideal.span_singleton_eq_bot.mp (h _ fun x hx ↦ ?_)
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    calc χ (s * r) = LinearMap.toSpanSingleton R _ χ r s := by simp [mul_comm]
      _ = 0 := by rw [hr, TauCeti.CharacterModule.zero_apply]
  · ext s
    rw [LinearMap.toSpanSingleton_apply, smul_apply, TauCeti.CharacterModule.zero_apply]
    exact hI _ (I.mul_mem_right s hr)

/-- An injective character is a Matlis generator. -/
theorem IsMatlisGenerator.of_injective (h : Function.Injective χ) : χ.IsMatlisGenerator :=
  fun I hI ↦ (Submodule.eq_bot_iff I).mpr fun x hx ↦ h (by rw [hI x hx, map_zero])

/-- The zero character of a nonzero ring is not a Matlis generator: it kills the unit ideal. -/
theorem not_isMatlisGenerator_zero [Nontrivial R] :
    ¬ (0 : CharacterModule R).IsMatlisGenerator :=
  fun h ↦ top_ne_bot (h ⊤ fun x _ ↦ TauCeti.CharacterModule.zero_apply x)

/-- A unit multiple of a Matlis generator is a Matlis generator. -/
theorem IsMatlisGenerator.units_smul (hχ : χ.IsMatlisGenerator) (u : Rˣ) :
    ((u : R) • χ).IsMatlisGenerator := by
  rw [isMatlisGenerator_iff_injective] at hχ ⊢
  refine fun r s hrs ↦ (Units.mul_left_inj u).mp (hχ ?_)
  simpa [mul_smul] using hrs

section Finite

variable [Finite R]

/-- Over a finite ring, a character is a Matlis generator exactly when `r ↦ r • χ` is bijective,
since the character module of `R` has as many elements as `R`. -/
theorem isMatlisGenerator_iff_bijective :
    χ.IsMatlisGenerator ↔
      Function.Bijective (LinearMap.toSpanSingleton R (CharacterModule R) χ) :=
  isMatlisGenerator_iff_injective.trans
    ⟨fun h ↦ h.bijective_of_nat_card_le (TauCeti.natCard_characterModule R).le, (·.1)⟩

/-- The isomorphism `R ≃ₗ[R] CharacterModule R`, `r ↦ r • χ`, given by a Matlis generator `χ` of a
finite ring. -/
noncomputable def IsMatlisGenerator.linearEquiv (hχ : χ.IsMatlisGenerator) :
    R ≃ₗ[R] CharacterModule R :=
  LinearEquiv.ofBijective _ (isMatlisGenerator_iff_bijective.mp hχ)

@[simp]
theorem IsMatlisGenerator.linearEquiv_apply (hχ : χ.IsMatlisGenerator) (r : R) :
    hχ.linearEquiv r = r • χ :=
  (rfl)

/-- The inverse of `linearEquiv` sends the Matlis generator to `1`; with `map_smul` this computes
it on every `r • χ`. -/
@[simp]
theorem IsMatlisGenerator.linearEquiv_symm_apply_self (hχ : χ.IsMatlisGenerator) :
    hχ.linearEquiv.symm χ = 1 :=
  hχ.linearEquiv.symm_apply_eq.mpr (one_smul R χ).symm

theorem IsMatlisGenerator.linearEquiv_symm_apply_smul (hχ : χ.IsMatlisGenerator) (r : R) :
    hχ.linearEquiv.symm (r • χ) = r := by
  simp

/-- **Uniqueness of Matlis generators.** Over a finite ring, any two Matlis generators differ by a
unique unit. -/
theorem IsMatlisGenerator.existsUnique_units_smul_eq (hχ : χ.IsMatlisGenerator)
    (hψ : ψ.IsMatlisGenerator) : ∃! u : Rˣ, (u : R) • χ = ψ := by
  obtain ⟨r, hr⟩ := hχ.linearEquiv.surjective ψ
  obtain ⟨s, hs⟩ := hψ.linearEquiv.surjective χ
  simp only [linearEquiv_apply] at hr hs
  -- `χ = s • ψ = (s * r) • χ`, so `s * r = 1`
  have hsr : s * r = 1 := hχ.linearEquiv.injective (by simp [mul_smul, hr, hs])
  refine ⟨(IsUnit.of_mul_eq_one_right s hsr).unit, hr, fun u hu ↦ ?_⟩
  exact Units.ext (hχ.linearEquiv.injective (by simp [hu, hr]))

/-- Over a finite ring, the Matlis generators are exactly the unit multiples of a given one. -/
theorem IsMatlisGenerator.isMatlisGenerator_iff (hχ : χ.IsMatlisGenerator) :
    ψ.IsMatlisGenerator ↔ ∃ u : Rˣ, (u : R) • χ = ψ :=
  ⟨fun hψ ↦ (hχ.existsUnique_units_smul_eq hψ).exists, fun ⟨u, hu⟩ ↦ hu ▸ hχ.units_smul u⟩

/-- **A finite ring with a Matlis generator is self-injective**: it is isomorphic to its character
module, which is injective because `R` is flat over itself. -/
theorem IsMatlisGenerator.moduleInjective (hχ : χ.IsMatlisGenerator) : Module.Injective R R := by
  have hE : Module.Injective R (CharacterModule R) :=
    Module.Flat.iff_characterModule_injective.mp inferInstance
  exact Module.Baer.injective ((Module.Baer.of_injective hE).of_equiv hχ.linearEquiv.symm)

end Finite

/-- **An artinian local ring with a simple socle has a Matlis generator**: any character which does
not vanish at a nonzero element of the socle. Every nonzero ideal meets the socle, hence contains
it, so no nonzero ideal lies in the kernel of such a character. -/
theorem exists_isMatlisGenerator_of_isSimpleModule [IsLocalRing R] [IsArtinianRing R]
    (h : IsSimpleModule R (torsionBySet R R (maximalIdeal R))) :
    ∃ χ : CharacterModule R, χ.IsMatlisGenerator := by
  rw [isSimpleModule_iff_isAtom] at h
  obtain ⟨s, hs, hs0⟩ := exists_mem_ne_zero_of_ne_bot h.1
  obtain ⟨χ, hχ⟩ := exists_character_apply_ne_zero_of_ne_zero hs0
  refine ⟨χ, fun I hI ↦ by_contra fun hI0 ↦ hχ (hI s ?_)⟩
  have hle := h.le_iff.mp (inf_le_right : I ⊓ torsionBySet R R (maximalIdeal R) ≤ _)
  exact ((hle.resolve_left (inf_torsionBySet_maximalIdeal_ne_bot hI0)).ge hs).1

/-- **Matlis generators of a finite local ring.** For a finite local ring `R` the following are
equivalent: `R` has a Matlis generator; `R` is self-injective; the socle of `R` is simple, that is,
one-dimensional over the residue field. -/
theorem tfae_exists_isMatlisGenerator [Finite R] [IsLocalRing R] :
    List.TFAE [∃ χ : CharacterModule R, χ.IsMatlisGenerator, Module.Injective R R,
      IsSimpleModule R (torsionBySet R R (maximalIdeal R))] := by
  have : IsArtinianRing R := isArtinian_of_finite
  tfae_have 1 → 2 := fun ⟨_, hχ⟩ ↦ hχ.moduleInjective
  tfae_have 2 → 3 := fun _ ↦ isSimpleModule_torsionBySet_maximalIdeal_of_injective
  tfae_have 3 → 1 := exists_isMatlisGenerator_of_isSimpleModule
  tfae_finish

/-- The character `k ↦ k / n` of `ℤ/n` is a Matlis generator. -/
theorem isMatlisGenerator_toRatAddCircle (n : ℕ) [NeZero n] :
    IsMatlisGenerator (R := ZMod n) (ZMod.toRatAddCircle n) :=
  .of_injective (ZMod.toRatAddCircle_injective n)

end CharacterModule
