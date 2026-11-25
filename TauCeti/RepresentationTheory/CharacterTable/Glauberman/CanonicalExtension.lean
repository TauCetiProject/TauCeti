/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Degree.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Determined
public import TauCeti.RepresentationTheory.CharacterTable.Glauberman.NormalizedExtension
public import TauCeti.RepresentationTheory.CharacterTable.Table
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Glauberman's canonical extension

Let a finite group `S` act on a finite group `Γ` by automorphisms through `φ : S →* MulAut Γ`,
with `|Γ|` and `|S|` coprime, and let `k` be an algebraically closed field of characteristic zero.
For an irreducible character `χ` of `Γ` invariant under `S` (`χ (φ s g) = χ g`), there is exactly
one irreducible character `χ̂` of `Γ ⋊[φ] S` restricting to `χ` on `Γ` that is the character of a
representation on which every element of `S` acts with determinant `1`
(`TauCeti.existsUnique_canonicalExtension`). This is the **canonical extension** of `χ`
(Glauberman 1968, Theorem 2 (a), p. 1470). No solvability of `S` is assumed, and finiteness of `S`
is not used: `|S|` is read as `Nat.card S`.

The route: `χ(1)` divides `|Γ|` (`Representation.finrank_dvd_card`), so it is coprime to `|S|`;
invariance of `χ` makes a representation affording `χ` equivalent to each of its twists by `S`
(`Representation.nonempty_equiv_of_character_eq`); Schur's lemma makes its equivariant
endomorphisms scalars. Gallagher's normalized extension
(`Representation.existsUnique_semidirectProduct_extension_det_eq_one`) then gives the extension.
For uniqueness, any representation of `Γ ⋊[φ] S` with the same restriction to `Γ` and determinant
`1` on `S` is conjugated, along an equivalence of the restrictions, to one restricting to the same
representation of `Γ`, with the same determinants on `S` and the same character.

The extension is irreducible because its restriction to `Γ` is
(`Representation.IsIrreducible.of_comp`).

## Main results

* `TauCeti.IsCanonicalExtension`: `ψ` is a canonical extension of `χ`.
* `TauCeti.existsUnique_canonicalExtension`: existence and uniqueness of the canonical extension.
* `TauCeti.isCanonicalExtension_one`, `TauCeti.IsCanonicalExtension.eq_one`: the canonical
  extension of the trivial character is trivial.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
  Canad. J. Math. 20 (1968), 1465–1488, Theorem 2 (a), p. 1470.
-/

public section

open Module SemidirectProduct

namespace TauCeti

section Predicate

variable {k Γ S : Type*} [Field k] [Group Γ] [Group S] {φ : S →* MulAut Γ}

variable (φ) in
/-- `ψ` is a **canonical extension** of `χ : Γ → k` to `Γ ⋊[φ] S`: an irreducible character with
`ψ ∘ inl = χ` that is the character of a representation on `Fin n → k` on which every element of
`S` acts with determinant `1` (Glauberman 1968, Theorem 2 (a), p. 1470). -/
def IsCanonicalExtension (χ : Γ → k) (ψ : Γ ⋊[φ] S → k) : Prop :=
  ψ ∈ irreducibleCharacters k (Γ ⋊[φ] S) ∧ ψ ∘ inl = χ ∧
    ∃ (n : ℕ) (ρ : Representation k (Γ ⋊[φ] S) (Fin n → k)),
      ρ.character = ψ ∧ ∀ s, (ρ (inr s)).det = 1

/-- Unfolding `TauCeti.IsCanonicalExtension`. -/
theorem isCanonicalExtension_iff {χ : Γ → k} {ψ : Γ ⋊[φ] S → k} :
    IsCanonicalExtension φ χ ψ ↔ ψ ∈ irreducibleCharacters k (Γ ⋊[φ] S) ∧ ψ ∘ inl = χ ∧
      ∃ (n : ℕ) (ρ : Representation k (Γ ⋊[φ] S) (Fin n → k)),
        ρ.character = ψ ∧ ∀ s, (ρ (inr s)).det = 1 :=
  Iff.rfl

/-- **The canonical extension of the trivial character is trivial**: the trivial representation
of `Γ ⋊[φ] S` has determinant `1` everywhere. -/
theorem isCanonicalExtension_one : IsCanonicalExtension φ (fun _ : Γ => (1 : k)) fun _ => 1 := by
  have hchar : (Representation.trivial k (Γ ⋊[φ] S) (Fin 1 → k)).character = fun _ => 1 :=
    funext fun _ => by
      rw [Representation.char_trivial, Module.finrank_fin_fun, Nat.cast_one]
  refine ⟨one_mem_irreducibleCharacters, rfl, 1, Representation.trivial k _ _, hchar, fun _ => ?_⟩
  exact LinearMap.det_id

end Predicate

variable {k Γ S : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group Γ] [Group S] [Finite Γ]
  {φ : S →* MulAut Γ}

/-- **Glauberman's canonical extension.** Let a finite group `S` act on a finite group `Γ` through
`φ`, with `|Γ|` and `|S|` coprime, and let `χ` be an irreducible character of `Γ` over an
algebraically closed field of characteristic zero with `χ (φ s g) = χ g`. There is exactly one
irreducible character `χ̂` of `Γ ⋊[φ] S` with `χ̂ ∘ inl = χ` that is the character of a
representation `ρ` with `det ρ(inr s) = 1` for every `s ∈ S` (Glauberman 1968, Theorem 2 (a),
p. 1470). -/
theorem existsUnique_canonicalExtension (hcop : (Nat.card Γ).Coprime (Nat.card S)) {χ : Γ → k}
    (hχ : χ ∈ irreducibleCharacters k Γ) (hinv : ∀ s g, χ (φ s g) = χ g) :
    ∃! ψ : Γ ⋊[φ] S → k, IsCanonicalExtension φ χ ψ := by
  obtain ⟨n, ρ₀, hirr, rfl⟩ := mem_irreducibleCharacters_iff.1 hχ
  have := hirr
  have hscalar : ∀ f : Module.End k (Fin n → k), (∀ g, Commute f (ρ₀ g)) →
      ∃ c : k, f = algebraMap k (Module.End k (Fin n → k)) c := fun f hf => by
    obtain ⟨c, hc⟩ := Representation.IsIrreducible.exists_forall_apply_eq_smul f
      fun g v => LinearMap.congr_fun (hf g).eq v
    exact ⟨c, LinearMap.ext fun v => by rw [hc, Module.algebraMap_end_apply]⟩
  have hcop' : (Nat.card S).Coprime (finrank k (Fin n → k)) :=
    (hcop.coprime_dvd_left ρ₀.finrank_dvd_card).symm
  have htwist (s : S) : Nonempty (ρ₀.Equiv (ρ₀.comp (φ s).toMonoidHom)) :=
    Representation.nonempty_equiv_of_character_eq _ _ (funext fun g => (hinv s g).symm)
  obtain ⟨ρ', hinl, hdet⟩ :=
    Representation.exists_semidirectProduct_extension_det_eq_one hscalar hcop' htwist
  have hcomp : ρ'.comp (inl : Γ →* Γ ⋊[φ] S) = ρ₀ := MonoidHom.ext hinl
  refine ⟨ρ'.character, ⟨mem_irreducibleCharacters_iff.2 ⟨n, ρ', ?_, rfl⟩, ?_, n, ρ', rfl, hdet⟩,
    ?_⟩
  · have : Representation.IsIrreducible (ρ'.comp (inl : Γ →* Γ ⋊[φ] S)) := hcomp ▸ hirr
    exact Representation.IsIrreducible.of_comp inl
  · funext g
    simp only [Function.comp_apply, Representation.character, hinl]
  · rintro ψ ⟨-, hψ, m, ρ₁, rfl, hdet₁⟩
    -- Conjugate `ρ₁` along an equivalence of its restriction to `Γ` with `ρ₀`.
    have hc : Representation.character (ρ₁.comp (inl : Γ →* Γ ⋊[φ] S)) = ρ₀.character := by
      funext g
      simpa only [Representation.character, MonoidHom.coe_comp, Function.comp_apply] using
        congrFun hψ g
    obtain ⟨E⟩ := Representation.nonempty_equiv_of_character_eq _ _ hc
    let ρ₂ : Representation k (Γ ⋊[φ] S) (Fin n → k) :=
      (MonoidHom.ofClass (E.toLinearEquiv.conjAlgEquiv k)).comp ρ₁
    have hρ₂ (x : Γ ⋊[φ] S) : ρ₂ x = E.toLinearEquiv.conj (ρ₁ x) := by
      rw [MonoidHom.comp_apply, MonoidHom.coe_ofClass, LinearEquiv.conjAlgEquiv_apply,
        LinearEquiv.conj_apply, LinearMap.comp_assoc]
    have h₂inl (g : Γ) : ρ₂ (inl g) = ρ₀ g := by
      rw [hρ₂, ← E.conj_apply_self g, MonoidHom.comp_apply]
    have h₂det (s : S) : (ρ₂ (inr s)).det = 1 := by
      rw [hρ₂, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, hdet₁]
    have h₂ := Representation.semidirectProduct_extension_det_eq_one_unique hscalar hcop'
      h₂inl hinl h₂det hdet
    funext x
    rw [Representation.character, Representation.character, ← h₂, hρ₂,
      LinearMap.trace_conj']

/-- A canonical extension of the trivial character is the trivial character. -/
theorem IsCanonicalExtension.eq_one (hcop : (Nat.card Γ).Coprime (Nat.card S))
    {ψ : Γ ⋊[φ] S → k} (hψ : IsCanonicalExtension φ (fun _ : Γ => (1 : k)) ψ) :
    ψ = fun _ => 1 :=
  (existsUnique_canonicalExtension hcop one_mem_irreducibleCharacters fun _ _ => rfl).unique hψ
    isCanonicalExtension_one

end TauCeti
