/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Automorphism
public import TauCeti.RepresentationTheory.CharacterTable.Degree.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Determined
public import TauCeti.RepresentationTheory.CharacterTable.Glauberman.NormalizedExtension
public import TauCeti.RepresentationTheory.CharacterTable.Table
public import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Charpoly

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
* `TauCeti.isCanonicalExtension_one_left`: for the trivial action, the canonical extension of `χ`
  is `x ↦ χ x.left`.
* `TauCeti.det_inr_eq_one_iff_exists_det_pow_eq_one`,
  `TauCeti.isCanonicalExtension_iff_exists_det_pow_eq_one`: for `|Γ|` and `|S|` coprime, the
  determinant of a representation of `Γ ⋊[φ] S` is trivial on `S` exactly when its order is coprime
  to `|S|`, so the canonical extension can equally be normalised by the order of its determinant.
* `TauCeti.IsCanonicalExtension.det_inr_eq_one`: over a field of characteristic zero, every
  representation affording a canonical extension has determinant `1` on `S`.
* `TauCeti.IsCanonicalExtension.comp_map`, `TauCeti.IsCanonicalExtension.eq_comp_map`: the
  canonical extension for a subgroup `T ≤ S`, or more generally along `T →* S`, is the restriction
  of the canonical extension for `S`.
* `TauCeti.IsCanonicalExtension.comp_mulEquiv_symm`: an isomorphism of semidirect products
  mapping `Γ` onto `Γ'` and `S` onto `S'` carries canonical extensions to canonical extensions.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
  Canad. J. Math. 20 (1968), 1465–1488, Theorem 2 (a), p. 1470, and the note after it, p. 1471.
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

/-- **Trivial action**: for the trivial action, `Γ ⋊[1] S ≅ Γ × S`, and the canonical extension of
an irreducible character `χ` of `Γ` is `χ × 1_S`, read through the first coordinate. -/
theorem isCanonicalExtension_one_left {χ : Γ → k} (hχ : χ ∈ irreducibleCharacters k Γ) :
    IsCanonicalExtension (1 : S →* MulAut Γ) χ fun x => χ x.left := by
  obtain ⟨n, ρ, -, rfl⟩ := mem_irreducibleCharacters_iff.1 hχ
  let π : Γ ⋊[(1 : S →* MulAut Γ)] S →* Γ := (MonoidHom.fst Γ S).comp mulEquivProd.toMonoidHom
  have hπ : Function.Surjective π := fun g => ⟨inl g, rfl⟩
  refine isCanonicalExtension_iff.2
    ⟨π.comp_mem_irreducibleCharacters hπ hχ, rfl, n, ρ.comp π, rfl, fun s => ?_⟩
  have hπs : π (inr s) = 1 := by simp [π]
  rw [MonoidHom.comp_apply, hπs, map_one, map_one]

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
  · rw [← Representation.character_comp, hcomp]
  · rintro ψ ⟨-, hψ, m, ρ₁, rfl, hdet₁⟩
    -- Conjugate `ρ₁` along an equivalence of its restriction to `Γ` with `ρ₀`.
    have hc : Representation.character (ρ₁.comp (inl : Γ →* Γ ⋊[φ] S)) = ρ₀.character := by
      rw [Representation.character_comp, hψ]
    obtain ⟨E⟩ := Representation.nonempty_equiv_of_character_eq _ _ hc
    let ρ₂ : Representation k (Γ ⋊[φ] S) (Fin n → k) :=
      (MonoidHom.ofClass (E.toLinearEquiv.conjAlgEquiv k)).comp ρ₁
    have hρ₂ (x : Γ ⋊[φ] S) : ρ₂ x = E.toLinearEquiv.conj (ρ₁ x) := by
      rw [MonoidHom.comp_apply, MonoidHom.coe_ofClass, LinearEquiv.conjAlgEquiv_apply,
        LinearEquiv.conj_apply, LinearMap.comp_assoc]
    have h₂inl (g : Γ) : ρ₂ (inl g) = ρ₀ g := by
      rw [hρ₂, ← E.conj_apply_self g, MonoidHom.comp_apply]
    have E₂ : ρ₁.Equiv ρ₂ := .mk E.toLinearEquiv fun x => by
      rw [hρ₂, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.comp_assoc,
        LinearEquiv.symm_comp, LinearMap.comp_id]
    have h₂det (s : S) : (ρ₂ (inr s)).det = 1 := by
      rw [← E₂.det_apply_eq, hdet₁]
    have h₂ := Representation.semidirectProduct_extension_det_eq_one_unique hscalar hcop'
      h₂inl hinl h₂det hdet
    rw [← h₂]
    exact Representation.char_iso E₂

/-- A canonical extension of the trivial character is the trivial character. -/
theorem IsCanonicalExtension.eq_one (hcop : (Nat.card Γ).Coprime (Nat.card S))
    {ψ : Γ ⋊[φ] S → k} (hψ : IsCanonicalExtension φ (fun _ : Γ => (1 : k)) ψ) :
    ψ = fun _ => 1 :=
  (existsUnique_canonicalExtension hcop one_mem_irreducibleCharacters fun _ _ => rfl).unique hψ
    isCanonicalExtension_one

section Determinant

variable {k Γ S V : Type*} [Field k] [Group Γ] [Group S] [AddCommGroup V] [Module k V]
  {φ : S →* MulAut Γ}

/-- **Two normalisations of the determinant.** For `|Γ|` and `|S|` coprime, a representation of
`Γ ⋊[φ] S` has determinant `1` on every element of `S` exactly when its determinant has order
coprime to `|S|`, that is, when some power `m` coprime to `|S|` of the determinant is trivial
(Glauberman 1968, note after Theorem 2, p. 1471). -/
theorem det_inr_eq_one_iff_exists_det_pow_eq_one (hcop : (Nat.card Γ).Coprime (Nat.card S))
    (ρ : Representation k (Γ ⋊[φ] S) V) :
    (∀ s, (ρ (inr s)).det = 1) ↔
      ∃ m : ℕ, m.Coprime (Nat.card S) ∧ ∀ x, (ρ x).det ^ m = 1 := by
  let δ : Γ ⋊[φ] S →* k := LinearMap.det.comp (ρ : Γ ⋊[φ] S →* Module.End k V)
  have hδ (x : Γ ⋊[φ] S) : δ x = (ρ x).det := rfl
  constructor
  · refine fun h => ⟨Nat.card Γ, hcop, fun x => ?_⟩
    rw [← hδ, ← inl_left_mul_inr_right x, map_mul, hδ (inr _), h, mul_one, ← map_pow, ← map_pow,
      pow_card_eq_one', map_one, map_one]
  · rintro ⟨m, hm, h⟩ s
    rw [← hδ]
    refine (pow_eq_one_iff_of_coprime hm).1 ⟨?_, ?_⟩
    · exact h _
    · rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]

/-- **The canonical extension, normalised by the order of the determinant**: for `|Γ|` and `|S|`
coprime, `ψ` is the canonical extension of `χ` exactly when it is an irreducible character
extending `χ`, afforded by a representation whose determinant has order coprime to `|S|`
(Glauberman 1968, Theorem 2 (a), p. 1470, and the note after it, p. 1471). -/
theorem isCanonicalExtension_iff_exists_det_pow_eq_one
    (hcop : (Nat.card Γ).Coprime (Nat.card S)) {χ : Γ → k} {ψ : Γ ⋊[φ] S → k} :
    IsCanonicalExtension φ χ ψ ↔ ψ ∈ irreducibleCharacters k (Γ ⋊[φ] S) ∧ ψ ∘ inl = χ ∧
      ∃ (n : ℕ) (ρ : Representation k (Γ ⋊[φ] S) (Fin n → k)), ρ.character = ψ ∧
        ∃ m : ℕ, m.Coprime (Nat.card S) ∧ ∀ x, (ρ x).det ^ m = 1 := by
  simp only [isCanonicalExtension_iff, det_inr_eq_one_iff_exists_det_pow_eq_one hcop]

end Determinant

section Transport

variable {k Γ S : Type*} [Field k] [Group Γ] [Group S] {φ : S →* MulAut Γ}

/-- A character with a canonical extension is invariant under the action of `S`: it is the
restriction of a character of `Γ ⋊[φ] S`, a class function, and `inl (φ s g)` is conjugate to
`inl g`. -/
theorem IsCanonicalExtension.apply_aut {χ : Γ → k} {ψ : Γ ⋊[φ] S → k}
    (h : IsCanonicalExtension φ χ ψ) (s : S) (g : Γ) : χ (φ s g) = χ g := by
  obtain ⟨-, rfl, n, ρ, rfl, -⟩ := h
  rw [Function.comp_apply, Function.comp_apply, inl_aut, map_inv, Representation.char_conj]

/-- **Canonical extensions transport along isomorphisms of semidirect products.** If
`α : Γ ⋊[φ] S ≃* Γ' ⋊[φ'] S'` restricts to `β : Γ ≃* Γ'` on `Γ` and maps `S` onto `S'`, then the
canonical extension of `χ ∘ β⁻¹` is `ψ ∘ α⁻¹`. For `Γ' = Γ`, `S' = S` this is the behaviour of the
canonical extension under automorphisms of `Γ ⋊[φ] S` preserving `Γ` and `S`. -/
theorem IsCanonicalExtension.comp_mulEquiv_symm {Γ' S' : Type*} [Group Γ'] [Group S']
    {φ' : S' →* MulAut Γ'} {χ : Γ → k} {ψ : Γ ⋊[φ] S → k} (h : IsCanonicalExtension φ χ ψ)
    (α : Γ ⋊[φ] S ≃* Γ' ⋊[φ'] S') (β : Γ ≃* Γ') (hβ : ∀ g, α (inl g) = inl (β g))
    (hS : ∀ s', ∃ s, α (inr s) = inr s') :
    IsCanonicalExtension φ' (χ ∘ β.symm) (ψ ∘ α.symm) := by
  obtain ⟨hirr, hinl, n, ρ, hρ, hdet⟩ := h
  have hβ' (g' : Γ') : α.symm (inl g') = inl (β.symm g') := by
    rw [MulEquiv.symm_apply_eq, hβ, MulEquiv.apply_symm_apply]
  refine ⟨α.symm.comp_mem_irreducibleCharacters_iff.2 hirr, ?_, n,
    ρ.comp α.symm.toMonoidHom, by rw [Representation.character_comp, hρ, MulEquiv.coe_toMonoidHom],
    fun s' => ?_⟩
  · funext g'
    simp only [Function.comp_apply, hβ', ← hinl]
  · obtain ⟨s, hs⟩ := hS s'
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hs, MulEquiv.symm_apply_apply, hdet]

variable [CharZero k] [Finite Γ]

/-- **Restriction of the canonical extension.** For a homomorphism `f : T →* S`, in particular
the inclusion of a subgroup, the restriction of the canonical extension of `χ` along
`Γ ⋊[φ ∘ f] T →* Γ ⋊[φ] S` is the canonical extension of `χ` for the action of `T`. -/
theorem IsCanonicalExtension.comp_map {T : Type*} [Group T] (f : T →* S) {χ : Γ → k}
    (hχ : χ ∈ irreducibleCharacters k Γ) {ψ : Γ ⋊[φ] S → k} (h : IsCanonicalExtension φ χ ψ) :
    IsCanonicalExtension (φ.comp f) χ
      (ψ ∘ SemidirectProduct.map (MonoidHom.id Γ) f fun _ => rfl) := by
  obtain ⟨-, hinl, n, ρ, rfl, hdet⟩ := h
  let ι : Γ ⋊[φ.comp f] T →* Γ ⋊[φ] S := SemidirectProduct.map (MonoidHom.id Γ) f fun _ => rfl
  have hι : ι.comp inl = inl := by ext <;> simp [ι]
  have hc : Representation.character (ρ.comp ι) ∘ inl = χ := by
    rw [Representation.character_comp, Function.comp_assoc, ← MonoidHom.coe_comp, hι, hinl]
  have hirr : Representation.IsIrreducible (ρ.comp ι) :=
    Representation.isIrreducible_of_character_comp_mem_irreducibleCharacters (ρ.comp ι) inl
      (hc ▸ hχ)
  refine ⟨character_mem_irreducibleCharacters (ρ.comp ι), hc, n, ρ.comp ι, rfl, fun t => ?_⟩
  simpa [ι] using hdet (f t)

/-- **Every representation affording the canonical extension has determinant `1` on `S`**, not
only the one witnessing `TauCeti.IsCanonicalExtension`: over a field of characteristic zero,
representations of the finite group `Γ ⋊[φ] S` with the same character are equivalent, and
equivalent representations have the same determinants. -/
theorem IsCanonicalExtension.det_inr_eq_one [Finite S] {χ : Γ → k} {ψ : Γ ⋊[φ] S → k}
    (h : IsCanonicalExtension φ χ ψ) {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k (Γ ⋊[φ] S) V) (hρ : ρ.character = ψ) (s : S) :
    (ρ (inr s)).det = 1 := by
  have : Finite (Γ ⋊[φ] S) := Finite.of_equiv _ equivProd.symm
  obtain ⟨-, -, m, ρ', hρ', hdet⟩ := h
  obtain ⟨E⟩ := Representation.nonempty_equiv_of_character_eq ρ' ρ (hρ'.trans hρ.symm)
  rw [← E.det_apply_eq, hdet]

end Transport

section Uniqueness

variable {k Γ S : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group Γ] [Group S] [Finite Γ]
  {φ : S →* MulAut Γ}

/-- **The canonical extension for a subgroup is the restriction.** For `f : T →* S` with `|Γ|`
and `|T|` coprime, in particular for the inclusion of a subgroup `T ≤ S`, the canonical extension
of `χ` for the action of `T` is the restriction of the canonical extension `ψ` for `S` along
`Γ ⋊[φ ∘ f] T →* Γ ⋊[φ] S`. -/
theorem IsCanonicalExtension.eq_comp_map {T : Type*} [Group T] (f : T →* S)
    (hcop : (Nat.card Γ).Coprime (Nat.card T)) {χ : Γ → k}
    (hχ : χ ∈ irreducibleCharacters k Γ) {ψ : Γ ⋊[φ] S → k} (h : IsCanonicalExtension φ χ ψ)
    {ψ' : Γ ⋊[φ.comp f] T → k} (h' : IsCanonicalExtension (φ.comp f) χ ψ') :
    ψ' = ψ ∘ SemidirectProduct.map (MonoidHom.id Γ) f fun _ => rfl :=
  (existsUnique_canonicalExtension hcop hχ h'.apply_aut).unique h' (h.comp_map f hχ)

end Uniqueness

end TauCeti
