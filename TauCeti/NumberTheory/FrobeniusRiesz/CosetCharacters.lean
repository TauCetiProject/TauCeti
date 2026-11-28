/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.Duality
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.MulChar.Lemmas

/-!
# Coset characters of a primitive cyclic family

The primitive pullbacks of the powers of a character `ψ` on a cyclotomic quotient can be read
as characters on `A / ker(ψ|_A)`, provided restriction to `A` preserves the order of `ψ`.
In particular, this applies when `A` is the common kernel of two independent auxiliary
quadratic twists. The identification supplies the characters and the quotient size for
Fourier comparison with a prescribed distribution of tops on the cosets.

The interpretation of the kept characters on the quotient follows Levent Alpöge's
`Formalism.HC.Level.ofSub` and `UpperTheory.Comparison₂.tops_sum` in his
[formalization of the Riemann hypothesis for Dirichlet L-functions][alpoege].

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open TauCeti

namespace MonoidHom

variable {N : ℕ} [NeZero N] {G : Type*} [CommGroup G]

/-- Identify the primitive cyclic family of a pullback with the characters of the coset
quotient of `A`. The order condition ensures that distinct powers remain distinct on `A`. -/
noncomputable def cyclicFamilyEquivCosetCharacters (f : (ZMod N)ˣ →* G)
    (hf : Function.Surjective f) (ψ : G →* ℂˣ) (A : Subgroup G)
    (horder : orderOf (ψ.comp A.subtype) = orderOf ψ) :
    ↥(PrimitiveDirichletCharacter.of (MulChar.equivToUnitHom.symm (ψ.comp f))).cyclicFamily ≃
      ((A ⧸ ψ.ker.subgroupOf A) →* ℂˣ) := by
  letI : Finite G := Finite.of_surjective f hf
  let P (χ : G →* ℂˣ) := PrimitiveDirichletCharacter.of (MulChar.equivToUnitHom.symm (χ.comp f))
  let e : Subgroup.zpowers ψ ≃ ↥(P ψ).cyclicFamily :=
    Equiv.ofBijective (fun χ ↦ ⟨P χ.val,
      (PrimitiveDirichletCharacter.of_ofUnitHom_comp_mem_cyclicFamily_iff f hf ψ χ.val).2 χ.prop⟩)
      ⟨fun χ η h ↦ Subtype.ext (MulChar.ofUnitHom_comp_injective hf
        (PrimitiveDirichletCharacter.of_injective (congrArg Subtype.val h))),
        fun ⟨κ, hκ⟩ ↦ by
          obtain ⟨m, hm⟩ := PrimitiveDirichletCharacter.mem_cyclicFamily_iff_exists_zpow.mp hκ
          refine ⟨⟨ψ ^ m, Subgroup.zpow_mem_zpowers ψ m⟩, Subtype.ext ?_⟩
          have hp : (ψ ^ m).comp f = (ψ.comp f) ^ m := MonoidHom.ext fun x ↦ by simp
          rw [← PrimitiveDirichletCharacter.of_zpow] at hm
          simpa only [P, hp, ← MulChar.ofUnitHom_eq, MulChar.ofUnitHom_zpow] using hm⟩
  exact e.symm.trans (ψ.zpowersEquivCosetCharacters A horder).toEquiv

/-- The coset character of a kept primitive pullback has the same value on a representative as
its original character on the host. -/
@[simp] theorem cyclicFamilyEquivCosetCharacters_apply_mk (f : (ZMod N)ˣ →* G)
    (hf : Function.Surjective f) (ψ : G →* ℂˣ) (A : Subgroup G)
    (horder : orderOf (ψ.comp A.subtype) = orderOf ψ) (χ : Subgroup.zpowers ψ) (t : A) :
    f.cyclicFamilyEquivCosetCharacters hf ψ A horder
      ⟨PrimitiveDirichletCharacter.of (MulChar.equivToUnitHom.symm (χ.val.comp f)),
        (PrimitiveDirichletCharacter.of_ofUnitHom_comp_mem_cyclicFamily_iff f hf ψ χ.val).2 χ.prop⟩
      (t : A ⧸ ψ.ker.subgroupOf A) = χ.val t := by
  let : Finite G := Finite.of_surjective f hf
  simp only [cyclicFamilyEquivCosetCharacters, Equiv.trans_apply]
  -- Match the primitive pullback explicitly with the forward map of `Equiv.ofBijective`.
  erw [Equiv.ofBijective_symm_apply_apply]
  exact ψ.zpowersEquivCosetCharacters_apply_mk A horder χ t

/-- The trivial coset character corresponds exactly to the trivial primitive character. -/
@[simp] theorem cyclicFamilyEquivCosetCharacters_apply_eq_one_iff (f : (ZMod N)ˣ →* G)
    (hf : Function.Surjective f) (ψ : G →* ℂˣ) (A : Subgroup G)
    (horder : orderOf (ψ.comp A.subtype) = orderOf ψ)
    (κ : ↥(PrimitiveDirichletCharacter.of (MulChar.equivToUnitHom.symm (ψ.comp f))).cyclicFamily) :
    f.cyclicFamilyEquivCosetCharacters hf ψ A horder κ = 1 ↔ κ.val = 1 := by
  let χ : Subgroup.zpowers ψ := 1
  let P (η : G →* ℂˣ) := PrimitiveDirichletCharacter.of (MulChar.equivToUnitHom.symm (η.comp f))
  let e := f.cyclicFamilyEquivCosetCharacters hf ψ A horder
  let κ₁ : ↥(P ψ).cyclicFamily := ⟨P χ.val,
    (PrimitiveDirichletCharacter.of_ofUnitHom_comp_mem_cyclicFamily_iff f hf ψ χ.val).2 χ.prop⟩
  have hκ₁ : κ₁.val = 1 :=
    (PrimitiveDirichletCharacter.of_ofUnitHom_comp_eq_one_iff hf).2 rfl
  have he₁ : e κ₁ = 1 := by
    apply MonoidHom.ext
    intro y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ y
    simpa only [e, κ₁, P, χ, QuotientGroup.mk'_apply, Subgroup.coe_one, MonoidHom.one_apply] using
      f.cyclicFamilyEquivCosetCharacters_apply_mk hf ψ A horder χ t
  rw [← he₁, e.injective.eq_iff, Subtype.ext_iff, hκ₁]

/-- The quotient of the top group has as many cosets as there are primitive characters in the
cyclic family. -/
theorem natCard_cosetQuotient_eq_card_cyclicFamily (f : (ZMod N)ˣ →* G)
    (hf : Function.Surjective f) (ψ : G →* ℂˣ) (A : Subgroup G)
    (horder : orderOf (ψ.comp A.subtype) = orderOf ψ) :
    Nat.card (A ⧸ ψ.ker.subgroupOf A) =
      (PrimitiveDirichletCharacter.of
        (MulChar.equivToUnitHom.symm (ψ.comp f))).cyclicFamily.card := by
  let : Finite G := Finite.of_surjective f hf
  rw [← CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (A ⧸ ψ.ker.subgroupOf A) ℂ,
    ← Nat.card_congr (f.cyclicFamilyEquivCosetCharacters hf ψ A horder),
    Nat.card_eq_fintype_card, Fintype.card_coe]

end MonoidHom
