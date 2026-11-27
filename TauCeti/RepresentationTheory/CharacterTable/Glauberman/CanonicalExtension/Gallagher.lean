/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Gallagher
public import TauCeti.RepresentationTheory.CharacterTable.Glauberman.CanonicalExtension.Basic

/-!
# Gallagher's correspondence for the canonical extension

Let a finite group `S` act on a finite group `Γ` through `φ`, and let `ψ` be the canonical
extension to `Γ ⋊[φ] S` of an irreducible character `χ` of `Γ`. Gallagher's correspondence over a
semidirect product (`TauCeti.gallagher_bijOn_semidirectProduct`) then describes `Irr(Γ ⋊ S | χ)`
as `{ψ β : β ∈ Irr(S)}`, each obtained once (`TauCeti.IsCanonicalExtension.gallagher_bijOn`).

## Main results

* `TauCeti.IsCanonicalExtension.gallagher_bijOn`: Gallagher's correspondence
  `Irr(S) ≃ Irr(Γ ⋊ S | χ)`, `β ↦ ψ β`, for the canonical extension `ψ` of `χ`.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
  Canad. J. Math. 20 (1968), 1465–1488, Theorem 2 (c), p. 1470.
-/

public section

open SemidirectProduct

namespace TauCeti

variable {k Γ S : Type*} [Group Γ] [Group S] {φ : S →* MulAut Γ}
  [Field k] [IsAlgClosed k] [CharZero k] [Finite Γ] [Finite S]

/-- **Gallagher's correspondence for the canonical extension.** If `ψ` is the canonical extension
of an irreducible character `χ` of `Γ`, the irreducible characters of `Γ ⋊[φ] S` lying over `χ`
are the products `ψ · β` for `β` an irreducible character of `S`, each obtained once. -/
theorem IsCanonicalExtension.gallagher_bijOn {χ : Γ → k} {ψ : Γ ⋊[φ] S → k}
    (h : IsCanonicalExtension φ χ ψ) (hχ : χ ∈ irreducibleCharacters k Γ) :
    Set.BijOn (fun (β : S → k) (g : Γ ⋊[φ] S) => ψ g * β g.right) (irreducibleCharacters k S)
      (irreducibleCharactersOver k (rightHom : Γ ⋊[φ] S →* S).ker
        (χ ∘ mulEquivKerRightHom.symm)) :=
  gallagher_bijOn_semidirectProduct (isCanonicalExtension_iff.1 h).1 hχ
    (isCanonicalExtension_iff.1 h).2.1

end TauCeti
