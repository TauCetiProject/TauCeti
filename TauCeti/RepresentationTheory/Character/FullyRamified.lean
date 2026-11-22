/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Character
public import TauCeti.RepresentationTheory.FunLeft
import TauCeti.RepresentationTheory.Character.Basic
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.LinearCharacter.Eigenspace

/-!
# Fully ramified characters

Let `J` be a finite group, `H ≤ J` a subgroup containing every commutator `g x g⁻¹ x⁻¹`, and
`θ : H →* kˣ` a character of `H`. Suppose that the commutator pairing `(g, x) ↦ θ(g x g⁻¹ x⁻¹)`
is nondegenerate modulo `H`: every `g ∉ H` has some `x` with `θ(g x g⁻¹ x⁻¹) ≠ 1`. Over an
algebraically closed field of characteristic zero, the irreducible representations `η` of `J` on
which `H` acts through the scalars `θ` are then controlled entirely by `θ`:

* the character of `η` is `dim η · θ` on `H` and vanishes off `H`;
* `(dim η)² = [J : H]`;
* any two such representations are equivalent;
* every finite-dimensional representation on which `H` acts by `θ` is `η`-isotypic, in the sense
  that its dimension is `dim η` times the dimension of its space of intertwiners from `η`.

This is the situation in which `θ` is called *fully ramified* with respect to `J / H`. The
quotient `H / ker θ` may be cyclic of
any order, so no exponent or special-isomorphism hypothesis enters. The finite Stone–von Neumann
theorem is the case of a Heisenberg group `J = H(V)` over a finite field, with `H` its centre and
`θ` a nontrivial additive character; the quaternion group `Q₈`, with `H = {±1}` and `θ(-1) = -1`,
is another, with `η` its two-dimensional representation. Such representations are the Heisenberg
representations from which types of `p`-adic groups are built.

The vanishing off `H` holds in any representation on which a commutator acts by a nontrivial
scalar (`Representation.character_eq_zero_of_commutator_apply_eq_smul`): conjugating `g` by `x`
multiplies `ρ g` by that scalar while preserving the trace. The rest is orthogonality of
characters, since the character pairing only sees `H`.

When `H` is normal and `θ` is invariant under conjugation by `J`, such an `η` exists, without the
commutator hypotheses: the `θ`-eigenspace of `H` in the regular representation is stable under
`J`, nonzero, and contains an irreducible subrepresentation
(`TauCeti.exists_subrepresentation_isIrreducible_forall_apply_eq_smul`).

## Main statements

* `Representation.character_eq_zero_of_commutator_apply_eq_smul`: a commutator `g x g⁻¹ x⁻¹`
  acting by a scalar `a ≠ 1` forces the character to vanish at `g`.
* `Representation.character_coe_eq_finrank_mul`: on `H` the character is `dim · θ`.
* `Representation.character_eq_zero_of_notMem`: off `H` the character vanishes.
* `Representation.sum_character_mul_character_inv`: the character pairing of two such
  representations is `|H| · dim · dim'`.
* `Representation.finrank_sq_eq_index`: an irreducible such representation has
  `(dim η)² = [J : H]`.
* `Representation.nonempty_equiv_of_forall_apply_eq_smul`: two irreducible such representations
  are equivalent.
* `Representation.finrank_eq_finrank_mul_finrank_intertwiningMap`: a finite-dimensional
  representation on which `H` acts by `θ` has dimension `dim η · dim Hom_J(η, σ)`.
* `TauCeti.exists_subrepresentation_isIrreducible_forall_apply_eq_smul`: for normal `H` and
  invariant `θ`, an irreducible representation on which `H` acts by `θ` exists.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6, for fully ramified characters.
* S. Stevens, *The supercuspidal representations of p-adic classical groups*, Invent. Math. 172
  (2008), Proposition 3.5.
* J. Fintzen, *Types for tame p-adic groups*, Ann. of Math. 193 (2021), Lemmas 7.7 and 7.8.
-/

public section

open Module

namespace Representation

variable {k J E E' : Type*} [Field k] [Group J] [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

/-- **A commutator acting by a nontrivial scalar kills the character.** If the commutator
`g x g⁻¹ x⁻¹` acts on `E` as multiplication by a scalar `a ≠ 1`, then the character of `ρ`
vanishes at `g`. No finiteness of `J` or of `E` is needed. -/
theorem character_eq_zero_of_commutator_apply_eq_smul (ρ : Representation k J E) {g x : J}
    {a : k} (ha : a ≠ 1) (h : ∀ v, ρ (g * x * g⁻¹ * x⁻¹) v = a • v) : ρ.character g = 0 := by
  have hc : ρ (g * x * g⁻¹ * x⁻¹) = a • (1 : Module.End k E) :=
    LinearMap.ext fun v => (h v).trans (by simp)
  have key : ρ.character g = a * ρ.character g :=
    calc ρ.character g = ρ.character (g * x * g⁻¹ * x⁻¹ * (x * g * x⁻¹)) := by
          congr 1
          group
      _ = a * ρ.character (x * g * x⁻¹) := by
          rw [character, map_mul, hc, smul_mul_assoc, one_mul, map_smul, smul_eq_mul, character]
      _ = a * ρ.character g := by rw [char_conj]
  have h1 : (1 - a) * ρ.character g = 0 := by linear_combination key
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm ha))

variable {H : Subgroup J} {θ : H →* kˣ}

/-- **On `H` the character is `dim · θ`.** If every `h ∈ H` acts on `E` as multiplication by
`θ h`, the character of `ρ` at `h` is `dim E · θ h`. When `E` is not finite-dimensional both
sides are `0`. -/
theorem character_coe_eq_finrank_mul (ρ : Representation k J E)
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ) (h : H) :
    ρ.character h = finrank k E * θ h := by
  by_cases hE : FiniteDimensional k E
  · have hh : ρ h = (θ h : k) • (1 : Module.End k E) := LinearMap.ext fun ξ => by simp [hρ]
    rw [character, hh, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]
  · simp [character_eq_zero_of_not_finite ρ hE, finrank_of_not_finite hE]

/-- **Off `H` the character vanishes.** Let `H` contain every commutator, and let `θ` be a
character of `H` whose commutator pairing is nondegenerate modulo `H`: each `g ∉ H` has some `x`
with `θ(g x g⁻¹ x⁻¹) ≠ 1`. Then any representation on which `H` acts by `θ` has character `0`
outside `H`. -/
theorem character_eq_zero_of_notMem (ρ : Representation k J E)
    (hcomm : ∀ g x : J, g * x * g⁻¹ * x⁻¹ ∈ H)
    (hnd : ∀ g : J, g ∉ H → ∃ x : J, θ ⟨g * x * g⁻¹ * x⁻¹, hcomm g x⟩ ≠ 1)
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ) {g : J} (hg : g ∉ H) :
    ρ.character g = 0 := by
  obtain ⟨x, hx⟩ := hnd g hg
  exact ρ.character_eq_zero_of_commutator_apply_eq_smul (mt Units.val_eq_one.1 hx)
    (hρ ⟨_, hcomm g x⟩)

/-- **The character pairing only sees `H`.** Under the hypotheses of
`Representation.character_eq_zero_of_notMem`, for two representations `ρ` and `σ` on which `H`
acts by `θ`, the unnormalised character pairing `∑_g χ_ρ(g) χ_σ(g⁻¹)` is `|H| · dim E · dim E'`. -/
theorem sum_character_mul_character_inv [Fintype J] (ρ : Representation k J E)
    (σ : Representation k J E') (hcomm : ∀ g x : J, g * x * g⁻¹ * x⁻¹ ∈ H)
    (hnd : ∀ g : J, g ∉ H → ∃ x : J, θ ⟨g * x * g⁻¹ * x⁻¹, hcomm g x⟩ ≠ 1)
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ)
    (hσ : ∀ (h : H) (ξ : E'), σ h ξ = (θ h : k) • ξ) :
    ∑ g : J, ρ.character g * σ.character g⁻¹ =
      Nat.card H * (finrank k E * finrank k E' : k) := by
  classical
  calc ∑ g : J, ρ.character g * σ.character g⁻¹
      = ∑ g ∈ Finset.univ.filter (· ∈ H), ρ.character g * σ.character g⁻¹ :=
        (Finset.sum_subset (Finset.subset_univ _) fun g _ hg => by
          rw [character_eq_zero_of_notMem ρ hcomm hnd hρ (by simpa using hg), zero_mul]).symm
    _ = ∑ h : H, ρ.character h * σ.character (h : J)⁻¹ :=
        Finset.sum_subtype _ (fun g => by simp) _
    _ = ∑ _h : H, (finrank k E * finrank k E' : k) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        have hθ : (θ h : k) ≠ 0 := (θ h).ne_zero
        rw [← Subgroup.coe_inv, character_coe_eq_finrank_mul ρ hρ,
          character_coe_eq_finrank_mul σ hσ, map_inv, Units.val_inv_eq_inv_val]
        field_simp
    _ = Nat.card H * (finrank k E * finrank k E' : k) := by
        simp [Nat.card_eq_fintype_card]

/-- **`(dim η)² = [J : H]`.** Over an algebraically closed field of characteristic zero, an
irreducible representation of the finite group `J` on which `H` acts by a character `θ` with
nondegenerate commutator pairing modulo `H` has dimension `d` with `d² = [J : H]`. -/
theorem finrank_sq_eq_index [Finite J] [IsAlgClosed k] [CharZero k] (ρ : Representation k J E)
    [ρ.IsIrreducible] (hcomm : ∀ g x : J, g * x * g⁻¹ * x⁻¹ ∈ H)
    (hnd : ∀ g : J, g ∉ H → ∃ x : J, θ ⟨g * x * g⁻¹ * x⁻¹, hcomm g x⟩ ≠ 1)
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ) :
    finrank k E ^ 2 = H.index := by
  have := Fintype.ofFinite J
  have hJ : (Nat.card J : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : Invertible (Nat.card J : k) := invertibleOfNonzero hJ
  have h1 := char_orthonormal ρ ρ
  rw [ite_eq_left ⟨Equiv.refl ρ⟩, sum_character_mul_character_inv ρ ρ hcomm hnd hρ hρ] at h1
  have h2 : Nat.card H * finrank k E ^ 2 = Nat.card H * H.index := by
    rw [H.card_mul_index]
    have h3 : (Nat.card H * finrank k E ^ 2 : k) = Nat.card J := by
      field_simp at h1
      linear_combination h1
    exact_mod_cast h3
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2

/-- **Uniqueness of the fully ramified representation.** Over an algebraically closed field of
characteristic zero, two irreducible representations of the finite group `J` on which `H` acts by
the same character `θ`, with nondegenerate commutator pairing modulo `H`, are equivalent. -/
theorem nonempty_equiv_of_forall_apply_eq_smul [Finite J] [IsAlgClosed k] [CharZero k]
    (ρ : Representation k J E) [ρ.IsIrreducible] (σ : Representation k J E') [σ.IsIrreducible]
    (hcomm : ∀ g x : J, g * x * g⁻¹ * x⁻¹ ∈ H)
    (hnd : ∀ g : J, g ∉ H → ∃ x : J, θ ⟨g * x * g⁻¹ * x⁻¹, hcomm g x⟩ ≠ 1)
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ)
    (hσ : ∀ (h : H) (ξ : E'), σ h ξ = (θ h : k) • ξ) :
    Nonempty (ρ.Equiv σ) := by
  have := Fintype.ofFinite J
  have hJ : (Nat.card J : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : Invertible (Nat.card J : k) := invertibleOfNonzero hJ
  have := ρ.asModuleEquiv.finiteDimensional
  have := σ.asModuleEquiv.finiteDimensional
  have h1 := char_orthonormal σ ρ
  rw [sum_character_mul_character_inv σ ρ hcomm hnd hσ hρ] at h1
  by_contra hne
  rw [ite_eq_right hne] at h1
  have hH : (Nat.card H : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hE := (inferInstance : ρ.IsIrreducible).natCast_finrank_ne_zero
  have hE' := (inferInstance : σ.IsIrreducible).natCast_finrank_ne_zero
  simp [hH, hE, hE'] at h1

/-- **Representations on which `H` acts by `θ` are isotypic.** Under the hypotheses of
`Representation.finrank_sq_eq_index`, let `ρ` be irreducible and `σ` finite-dimensional, both
with `H` acting by `θ`. Then `dim σ = dim ρ · dim Hom_J(ρ, σ)`, the dimension count of `σ`
being a sum of copies of `ρ`. -/
theorem finrank_eq_finrank_mul_finrank_intertwiningMap [Finite J] [IsAlgClosed k] [CharZero k]
    (ρ : Representation k J E) [ρ.IsIrreducible] (σ : Representation k J E')
    [FiniteDimensional k E'] (hcomm : ∀ g x : J, g * x * g⁻¹ * x⁻¹ ∈ H)
    (hnd : ∀ g : J, g ∉ H → ∃ x : J, θ ⟨g * x * g⁻¹ * x⁻¹, hcomm g x⟩ ≠ 1)
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ)
    (hσ : ∀ (h : H) (ξ : E'), σ h ξ = (θ h : k) • ξ) :
    finrank k E' = finrank k E * finrank k (IntertwiningMap ρ σ) := by
  have := Fintype.ofFinite J
  have hJ : (Nat.card J : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : Invertible (Nat.card J : k) := invertibleOfNonzero hJ
  have := ρ.asModuleEquiv.finiteDimensional
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  rw [sum_character_mul_character_inv σ ρ hcomm hnd hσ hρ] at h1
  have h2 : Nat.card H * (finrank k E' * finrank k E) =
      Nat.card J * finrank k (IntertwiningMap ρ σ) := by
    have h3 : (Nat.card H * (finrank k E' * finrank k E) : k) =
        Nat.card J * finrank k (IntertwiningMap ρ σ) := by
      field_simp at h1
      linear_combination h1
    exact_mod_cast h3
  rw [← H.card_mul_index, ← finrank_sq_eq_index ρ hcomm hnd hρ] at h2
  have hpos : 0 < Nat.card H * finrank k E :=
    Nat.mul_pos Nat.card_pos (inferInstance : ρ.IsIrreducible).finrank_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by linear_combination h2)

end Representation

namespace TauCeti

open Representation

/-- **Existence of a representation on which `H` acts by an invariant character.** Let `H` be a
normal subgroup of a finite group `J` and `θ` a character of `H` invariant under conjugation by
`J`. Then the representation of `J` on functions `J → k` by left translation has an irreducible
subrepresentation on which `H` acts by `θ`. No hypothesis on the commutators or on the field
is needed. -/
theorem exists_subrepresentation_isIrreducible_forall_apply_eq_smul (k : Type*) [Field k]
    {J : Type*} [Group J] [Finite J] {H : Subgroup J} [hH : H.Normal] (θ : H →* kˣ)
    (hinv : ∀ (g : J) (h : H), θ ⟨g * h * g⁻¹, hH.conj_mem h h.property g⟩ = θ h) :
    ∃ σ : Subrepresentation ((trivial k J k).funLeft J), σ.toRepresentation.IsIrreducible ∧
      ∀ (h : H) (ξ : σ.toSubmodule), σ.toRepresentation h ξ = (θ h : k) • ξ := by
  classical
  have := Fintype.ofFinite J
  set ρ := (trivial k J k).funLeft J
  -- The `θ`-eigenspace of `H` is stable under `J`.
  have hstab (g : J) ⦃ξ : J → k⦄ (hξ : ξ ∈ charEigenspace (ρ.comp H.subtype) θ) :
      ρ g ξ ∈ charEigenspace (ρ.comp H.subtype) θ := by
    rw [mem_charEigenspace_iff] at hξ ⊢
    intro h
    let h' : H := ⟨g⁻¹ * h * g⁻¹⁻¹, hH.conj_mem h h.property g⁻¹⟩
    have hconj : (h : J) * g = g * h' := by
      simp only [h', inv_inv]
      group
    have hξ' := hξ h'
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at hξ' ⊢
    rw [← mul_apply_eq_comp, ← map_mul, hconj, map_mul, mul_apply_eq_comp, hξ', map_smul,
      hinv]
  let S : Subrepresentation ρ := ⟨charEigenspace (ρ.comp H.subtype) θ, hstab⟩
  -- It contains the nonzero vector `∑_h θ(h)⁻¹ δ_h`.
  have hS : S ≠ ⊥ := by
    intro hS
    have hmem : charSum (ρ.comp H.subtype) θ (Pi.single 1 1) ∈ S :=
      charSum_apply_mem _ _ _
    rw [hS] at hmem
    have h0 := congrFun ((Submodule.mem_bot k).1 hmem) 1
    simp [charSum_apply, ρ, Pi.single_apply] at h0
  obtain ⟨τ, hτS, hτ⟩ := exists_isAtom_le hS
  refine ⟨τ, isIrreducible_toRepresentation_of_isAtom hτ, fun h ξ => ?_⟩
  have hξ := (mem_charEigenspace_iff _ _).1 (hτS ξ.property) h
  exact Subtype.ext hξ

end TauCeti
