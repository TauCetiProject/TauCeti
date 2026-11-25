/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Automorphism
public import TauCeti.RepresentationTheory.CharacterTable.Gallagher
public import TauCeti.RepresentationTheory.CharacterTable.Glauberman.CanonicalExtension.Basic

/-!
# Gallagher's correspondence over a semidirect product

Let a finite group `S` act on a finite group `Γ` through `φ`, and let `ψ` be an irreducible
character of `Γ ⋊[φ] S` restricting to an irreducible character `χ` of `Γ`. Applied with
`N = Γ` (the range of `inl`) and `G = Γ ⋊[φ] S`, whose quotient by `Γ` is `S` through `rightHom`,
Gallagher's correspondence says that `β ↦ (g ↦ ψ g · β g.right)` is a bijection from the
irreducible characters of `S` onto the irreducible characters of `Γ ⋊[φ] S` lying over `χ`
(`TauCeti.gallagher_bijOn_semidirectProduct`). For the canonical extension `ψ` of `χ` this
describes `Irr(Γ ⋊ S | χ)` as `{ψ β : β ∈ Irr(S)}`
(`TauCeti.IsCanonicalExtension.gallagher_bijOn`).

## Main results

* `TauCeti.gallagher_bijOn_semidirectProduct`: Gallagher's correspondence
  `Irr(S) ≃ Irr(Γ ⋊ S | χ)` for an irreducible extension `ψ` of `χ`.
* `TauCeti.IsCanonicalExtension.gallagher_bijOn`: the same for the canonical extension.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
  Canad. J. Math. 20 (1968), 1465–1488, Theorem 2 (c), p. 1470.
-/

public section

open SemidirectProduct

namespace TauCeti

variable {k Γ S : Type*} [Group Γ] [Group S] {φ : S →* MulAut Γ}

/-- The character of the subgroup `Γ` of `Γ ⋊[φ] S` given by a function `χ` on `Γ`, read through
the isomorphism of `Γ` with the range of `inl`. -/
noncomputable def semidirectProductLeftCharacter (φ : S →* MulAut Γ) (χ : Γ → k) :
    (inl : Γ →* Γ ⋊[φ] S).range → k :=
  χ ∘ (MonoidHom.ofInjective inl_injective).symm

/-- At `inl x`, the character of the subgroup `Γ` takes the value `χ x`. -/
@[simp]
theorem semidirectProductLeftCharacter_inl (χ : Γ → k) (x : Γ) :
    semidirectProductLeftCharacter (S := S) φ χ ⟨inl x, x, rfl⟩ = χ x := by
  simp only [semidirectProductLeftCharacter, Function.comp_apply]
  congr 1
  exact (MulEquiv.symm_apply_eq _).2 (Subtype.ext (MonoidHom.ofInjective_apply _).symm)

variable [Field k] [IsAlgClosed k] [CharZero k] [Finite Γ] [Finite S]

/-- **Gallagher's correspondence over a semidirect product.** If an irreducible character `ψ` of
`Γ ⋊[φ] S` restricts to an irreducible character `χ` of `Γ`, then `β ↦ (g ↦ ψ g · β g.right)` is
a bijection from the irreducible characters of `S` onto the irreducible characters of `Γ ⋊[φ] S`
lying over `χ`. -/
theorem gallagher_bijOn_semidirectProduct {χ : Γ → k} {ψ : Γ ⋊[φ] S → k}
    (hψ : ψ ∈ irreducibleCharacters k (Γ ⋊[φ] S)) (hχ : χ ∈ irreducibleCharacters k Γ)
    (hres : ψ ∘ inl = χ) :
    Set.BijOn (fun (β : S → k) (g : Γ ⋊[φ] S) => ψ g * β g.right) (irreducibleCharacters k S)
      (irreducibleCharactersOver k (inl : Γ →* Γ ⋊[φ] S).range
        (semidirectProductLeftCharacter φ χ)) := by
  let N := (inl : Γ →* Γ ⋊[φ] S).range
  have : N.Normal := by
    simp only [N, range_inl_eq_ker_rightHom]
    infer_instance
  let e : Γ ≃* N := MonoidHom.ofInjective inl_injective
  let q : (Γ ⋊[φ] S) ⧸ N ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq range_inl_eq_ker_rightHom).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ rightHom_surjective)
  have hq (g : Γ ⋊[φ] S) : q g = g.right := rfl
  have hθ : semidirectProductLeftCharacter φ χ ∈ irreducibleCharacters k N :=
    e.symm.comp_mem_irreducibleCharacters_iff.2 hχ
  have hres' (n : N) : ψ n = semidirectProductLeftCharacter φ χ n := by
    obtain ⟨_, x, rfl⟩ := n
    rw [semidirectProductLeftCharacter_inl, ← hres, Function.comp_apply]
  have hq' : Set.BijOn (fun β : S → k => β ∘ q) (irreducibleCharacters k S)
      (irreducibleCharacters k ((Γ ⋊[φ] S) ⧸ N)) := by
    refine ⟨fun β hβ => q.comp_mem_irreducibleCharacters_iff.2 hβ,
      fun β _ β' _ h => ?_, fun β hβ => ⟨β ∘ q.symm, ?_, ?_⟩⟩
    · funext s
      simpa using congrFun h (q.symm s)
    · rw [← q.symm.comp_mem_irreducibleCharacters_iff.symm]
      simpa [Function.comp_assoc] using hβ
    · funext x
      simp
  convert (gallagher_bijOn hψ hθ hres').comp hq' using 1
  funext β g
  simp only [Function.comp_apply, hq]

/-- **Gallagher's correspondence for the canonical extension.** If `ψ` is the canonical extension
of an irreducible character `χ` of `Γ`, the irreducible characters of `Γ ⋊[φ] S` lying over `χ`
are the products `ψ · β` for `β` an irreducible character of `S`, each obtained once. -/
theorem IsCanonicalExtension.gallagher_bijOn {χ : Γ → k} {ψ : Γ ⋊[φ] S → k}
    (h : IsCanonicalExtension φ χ ψ) (hχ : χ ∈ irreducibleCharacters k Γ) :
    Set.BijOn (fun (β : S → k) (g : Γ ⋊[φ] S) => ψ g * β g.right) (irreducibleCharacters k S)
      (irreducibleCharactersOver k (inl : Γ →* Γ ⋊[φ] S).range
        (semidirectProductLeftCharacter φ χ)) :=
  gallagher_bijOn_semidirectProduct (isCanonicalExtension_iff.1 h).1 hχ
    (isCanonicalExtension_iff.1 h).2.1

end TauCeti
