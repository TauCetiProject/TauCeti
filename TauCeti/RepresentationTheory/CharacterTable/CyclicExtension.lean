/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.RepresentationTheory.Character.Basic
import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Cyclic

/-!
# Irreducible character extensions across cyclic quotients

Over an algebraically closed field of characteristic zero, an irreducible character of a finite
normal subgroup extends across a cyclic quotient exactly when it is fixed by conjugation by a lift
of a generator. In prime index any element outside the subgroup serves as such a lift.
This supplies an initial extension for Gallagher's correspondence.

The split prime-index case is also a statement in Levent Alpöge's Lean development
<https://github.com/leanprover-community/riemann-hypothesis>
(`GlobalTheory.T.exists_semidirect_character_ext_of_stable`).
-/

public section

namespace TauCeti

open CategoryTheory

variable {k G : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group G]
  {N : Subgroup G} [N.Normal] [Finite N]

/-- An irreducible character extends across a cyclic quotient exactly when it is invariant
under conjugation by a lift of a generator. -/
theorem exists_irreducibleCharacter_extension_iff {x : G}
    (hx : Subgroup.zpowers (QuotientGroup.mk' N x) = ⊤) {θ : N → k}
    (hθ : θ ∈ irreducibleCharacters k N) :
    (∃ χ ∈ irreducibleCharacters k G, χ ∘ N.subtype = θ) ↔ θ ∘ MulAut.conjNormal x = θ := by
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    obtain ⟨d, ρ, -, rfl⟩ := mem_irreducibleCharacters_iff.mp hχ
    funext n
    exact ρ.char_conj n x
  · intro hstable
    obtain ⟨d, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.mp hθ
    let A := FDRep.of ρ
    have hAρ : A.ρ = ρ := FDRep.of_ρ' ρ
    have : Simple A := (FDRep.simple_iff_isIrreducible A).2 (hAρ.symm ▸ hρ)
    have hxi : x⁻¹ ∈ inertia A := mem_inertia_iff_forall_char_conj_eq.mpr (fun n ↦ by
      simpa [A, ← MulAut.conjNormal_apply] using congrFun hstable n)
    let q := QuotientGroup.mk' N
    have htop : (inertia A).map q = ⊤ := by
      apply top_unique
      rw [← hx, ← Subgroup.zpowers_inv, Subgroup.zpowers_le, ← map_inv]
      exact ⟨x⁻¹, hxi, rfl⟩
    have hi : inertia A = ⊤ := by
      rw [← Subgroup.comap_map_eq_self (f := q) (H := inertia A)
        ((QuotientGroup.ker_mk' N).le.trans (le_inertia A)), htop, Subgroup.comap_top]
    have : IsCyclic (G ⧸ N) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨q x, hx⟩
    obtain ⟨σ, hσ⟩ := A.exists_extension_of_isCyclic_quotient hi
    have : Representation.IsIrreducible (σ.comp N.subtype) := (hσ.trans hAρ).symm ▸ hρ
    have : σ.IsIrreducible := Representation.IsIrreducible.of_comp N.subtype
    exact ⟨σ.character, character_mem_irreducibleCharacters σ,
      (σ.character_comp N.subtype).symm.trans (congrArg Representation.character (hσ.trans hAρ))⟩

/-- In prime index, invariance under any one element outside the normal subgroup is enough
for an irreducible character to extend. -/
theorem exists_irreducibleCharacter_extension_of_index_prime (hp : N.index.Prime)
    {x : G} (hx : x ∉ N) {θ : N → k} (hθ : θ ∈ irreducibleCharacters k N)
    (hstable : θ ∘ MulAut.conjNormal x = θ) :
    ∃ χ ∈ irreducibleCharacters k G, χ ∘ N.subtype = θ := by
  have : Fact N.index.Prime := ⟨hp⟩
  have hne : QuotientGroup.mk' N x ≠ 1 := fun h ↦ hx ((QuotientGroup.eq_one_iff x).mp h)
  exact (exists_irreducibleCharacter_extension_iff
    (zpowers_eq_top_of_prime_card N.index_eq_card.symm hne) hθ).mpr hstable

end TauCeti
