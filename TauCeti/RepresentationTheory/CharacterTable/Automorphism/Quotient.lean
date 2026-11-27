/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Automorphism

/-!
# The quotient action on irreducible characters

Conjugation on the irreducible characters of a normal subgroup factors through the quotient:
inner automorphisms fix every character. This allows orbit counts on irreducible characters
to use the order of the quotient rather than that of the ambient group.
-/

public section

namespace TauCeti

variable {k G : Type*} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- A quotient element acts on irreducible characters by precomposing with inverse conjugation
by any lift. -/
instance instMulActionQuotientIrreducibleCharacters :
    MulAction (G ⧸ N) (irreducibleCharacters k N) :=
  MulAction.ofEndHom (QuotientGroup.lift N
    ((MulAction.toEndHom : MulAut N →* Function.End (irreducibleCharacters k N)).comp
      MulAut.conjNormal) fun g hg ↦ by
      rw [MonoidHom.mem_ker]
      funext θ
      obtain ⟨d, ρ, _, hρ⟩ := mem_irreducibleCharacters_iff.mp θ.property
      apply Subtype.ext
      funext n
      -- `toEndHom` evaluates to the original action; the identity endomorphism evaluates to `θ`.
      change ((MulAut.conjNormal (H := N) g • θ : irreducibleCharacters k N) : N → k) n =
        (θ : N → k) n
      simp only [MulAut.smul_irreducibleCharacters_apply, ← map_inv, ← hρ]
      have hconj := MulAut.conjNormal_val (h := (⟨g⁻¹, N.inv_mem hg⟩ : N))
      rw [hconj]
      exact ρ.char_conj n ⟨g⁻¹, N.inv_mem hg⟩)

/-- A lift acts on the irreducible characters by inverse conjugation. -/
@[simp]
theorem quotient_smul_irreducibleCharacters_apply (g : G) (θ : irreducibleCharacters k N) (n : N) :
    (((g : G ⧸ N) • θ : irreducibleCharacters k N) : N → k) n =
      (θ : N → k) ((MulAut.conjNormal g)⁻¹ n) := (rfl)

/-- An irreducible character is fixed by the quotient action exactly when it is stable under
conjugation by every lift. -/
theorem mem_fixedPoints_quotient_irreducibleCharacters_iff {θ : irreducibleCharacters k N} :
    θ ∈ MulAction.fixedPoints (G ⧸ N) (irreducibleCharacters k N) ↔
      ∀ (g : G) (n : N), (θ : N → k) (MulAut.conjNormal g n) = θ.val n := by
  rw [MulAction.mem_fixedPoints]
  refine ⟨fun h g n ↦ ?_, fun h q ↦ ?_⟩
  · have h' := congrArg (fun t : irreducibleCharacters k N ↦ (t : N → k) n)
      (h ((g⁻¹ : G) : G ⧸ N))
    rwa [quotient_smul_irreducibleCharacters_apply, map_inv, inv_inv] at h'
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    apply Subtype.ext
    funext n
    rw [QuotientGroup.mk'_apply, quotient_smul_irreducibleCharacters_apply, ← map_inv]
    exact h g⁻¹ n

end TauCeti
