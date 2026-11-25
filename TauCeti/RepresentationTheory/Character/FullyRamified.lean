/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Character
import TauCeti.RepresentationTheory.Character.Basic
import TauCeti.RepresentationTheory.Irreducible

/-!
# Fully ramified characters

Let `J` be a finite group, `H ≤ J` a subgroup containing every commutator `g x g⁻¹ x⁻¹`, and
`θ : H →* kˣ` a character of `H`. Suppose that the commutator pairing `(g, x) ↦ θ(g x g⁻¹ x⁻¹)`
is nondegenerate modulo `H`: every `g ∉ H` has some `x` with `θ(g x g⁻¹ x⁻¹) ≠ 1`
(`MonoidHom.IsFullyRamified`). Over an
algebraically closed field of characteristic zero, the irreducible representations `η` of `J` on
which `H` acts through the scalars `θ` are then controlled entirely by `θ`:

* the character of `η` is `dim η · θ` on `H` and vanishes off `H`;
* `(dim η)² = [J : H]`;
* any two such representations are equivalent (this needs only characteristic zero);
* every finite-dimensional representation on which `H` acts by `θ` is `η`-isotypic, in the sense
  that its dimension is `dim η` times the dimension of its space of intertwiners from `η`.

This is the situation in which `θ` is called *fully ramified* with respect to `J / H`. The
quotient `H / ker θ` may be cyclic of
any order, so no exponent or special-isomorphism hypothesis enters. The finite Stone–von Neumann
theorem is the case of a Heisenberg group `J = H(V)` over a finite field, with `H` its centre and
`θ` a nontrivial additive character; the quaternion group `Q₈`, with `H = {±1}` and `θ(-1) = -1`,
is another, with `η` its two-dimensional representation. Such representations are the Heisenberg
representations from which types of `p`-adic groups are built.

On `H` the character is `dim · θ`, as for any element acting by a scalar
(`Representation.character_eq_finrank_mul_of_apply_eq_smul`). The vanishing off `H` holds in any
representation on which a commutator acts by a nontrivial scalar
(`Representation.character_eq_zero_of_commutator_apply_eq_smul`). The rest follows from
the intertwiner count `[J : H] · dim Hom_J(ρ, σ) = dim ρ · dim σ`, a consequence of character
orthogonality since the character pairing only sees `H`.

When `H` is normal and `θ` is invariant under conjugation by `J`, such an `η` exists, without the
commutator hypotheses (`Representation.exists_subrepresentation_isIrreducible_forall_apply_eq_smul`
in `TauCeti.RepresentationTheory.LinearCharacter.NormalSubgroup`).

## Main statements

* `MonoidHom.IsFullyRamified`: `H` contains the commutators and the commutator pairing of `θ` is
  nondegenerate modulo `H`.
* `MonoidHom.IsFullyRamified.normal`: `H` is normal in `J`.
* `MonoidHom.IsFullyRamified.character_eq_zero_of_notMem`: off `H` the character vanishes.
* `MonoidHom.IsFullyRamified.sum_character_mul_character_inv`: the character pairing of two such
  representations is `|H| · dim · dim'`.
* `MonoidHom.IsFullyRamified.index_mul_finrank_intertwiningMap`: for two finite-dimensional such
  representations, `[J : H] · dim Hom_J(ρ, σ) = dim ρ · dim σ`.
* `MonoidHom.IsFullyRamified.finrank_sq_eq_index`: an irreducible such representation has
  `(dim η)² = [J : H]`.
* `MonoidHom.IsFullyRamified.nonempty_equiv`: two irreducible such representations are
  equivalent.
* `MonoidHom.IsFullyRamified.finrank_eq_finrank_mul_finrank_intertwiningMap`: a
  finite-dimensional representation on which `H` acts by `θ` has dimension
  `dim η · dim Hom_J(η, σ)`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6, for fully ramified characters.
* S. Stevens, *The supercuspidal representations of p-adic classical groups*, Invent. Math. 172
  (2008), Proposition 3.5.
* J. Fintzen, *Types for tame p-adic groups*, Ann. of Math. 193 (2021), Lemmas 7.7 and 7.8.
-/

public section

open Module Representation

namespace MonoidHom

variable {k J E E' : Type*} [Field k] [Group J] [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E'] {H : Subgroup J}

/-- **Fully ramified characters.** A character `θ` of a subgroup `H ≤ J` is fully ramified with
respect to `J / H` when `H` contains every commutator `g x g⁻¹ x⁻¹` and the commutator pairing
`(g, x) ↦ θ(g x g⁻¹ x⁻¹)` is nondegenerate modulo `H`: every `g ∉ H` has some `x` with
`θ(g x g⁻¹ x⁻¹) ≠ 1`. -/
structure IsFullyRamified (θ : H →* kˣ) : Prop where
  /-- Every commutator lies in `H`. -/
  commutator_mem (g x : J) : g * x * g⁻¹ * x⁻¹ ∈ H
  /-- The commutator pairing is nondegenerate modulo `H`. -/
  exists_ne_one (g : J) (hg : g ∉ H) : ∃ x : J, θ ⟨g * x * g⁻¹ * x⁻¹, commutator_mem g x⟩ ≠ 1

namespace IsFullyRamified

variable {θ : H →* kˣ}

/-- **`H` is normal.** A subgroup containing every commutator is normal, since
`g h g⁻¹ = (g h g⁻¹ h⁻¹) h`. This is a theorem rather than an instance, as the instance search
cannot find `hθ`. -/
theorem normal (hθ : θ.IsFullyRamified) : H.Normal where
  conj_mem h hh g := by simpa using H.mul_mem (hθ.commutator_mem g h) hh

/-- **Off `H` the character vanishes.** If `θ` is fully ramified, any representation on which `H`
acts by `θ` has character `0` outside `H`. -/
theorem character_eq_zero_of_notMem (hθ : θ.IsFullyRamified) (ρ : Representation k J E)
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ) {g : J} (hg : g ∉ H) :
    ρ.character g = 0 := by
  obtain ⟨x, hx⟩ := hθ.exists_ne_one g hg
  exact Representation.character_eq_zero_of_commutator_apply_eq_smul ρ (mt Units.val_eq_one.1 hx)
    (hρ ⟨_, hθ.commutator_mem g x⟩)

/-- **The character pairing only sees `H`.** If `θ` is fully ramified, then for two
representations `ρ` and `σ` on which `H` acts by `θ`, the unnormalised character pairing
`∑_g χ_ρ(g) χ_σ(g⁻¹)` is `|H| · dim E · dim E'`. -/
theorem sum_character_mul_character_inv [Fintype J] (hθ : θ.IsFullyRamified)
    (ρ : Representation k J E) (σ : Representation k J E')
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ)
    (hσ : ∀ (h : H) (ξ : E'), σ h ξ = (θ h : k) • ξ) :
    ∑ g : J, ρ.character g * σ.character g⁻¹ =
      Nat.card H * (finrank k E * finrank k E' : k) := by
  classical
  calc ∑ g : J, ρ.character g * σ.character g⁻¹
      = ∑ g ∈ Finset.univ.filter (· ∈ H), ρ.character g * σ.character g⁻¹ :=
        (Finset.sum_subset (Finset.subset_univ _) fun g _ hg => by
          rw [hθ.character_eq_zero_of_notMem ρ hρ (by simpa using hg), zero_mul]).symm
    _ = ∑ h : H, ρ.character h * σ.character (h : J)⁻¹ :=
        Finset.sum_subtype _ (fun g => by simp) _
    _ = ∑ _h : H, (finrank k E * finrank k E' : k) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        have hθh : (θ h : k) ≠ 0 := (θ h).ne_zero
        rw [← Subgroup.coe_inv, ρ.character_eq_finrank_mul_of_apply_eq_smul (hρ h),
          σ.character_eq_finrank_mul_of_apply_eq_smul (hσ h⁻¹), map_inv, Units.val_inv_eq_inv_val]
        field_simp
    _ = Nat.card H * (finrank k E * finrank k E' : k) := by
        simp [Nat.card_eq_fintype_card]

/-- **The intertwiner count.** If `θ` is fully ramified, then for two finite-dimensional
representations `ρ` and `σ` of the finite group `J` over a field of characteristic zero on which
`H` acts by `θ`, `[J : H] · dim Hom_J(ρ, σ) = dim E · dim E'`. -/
theorem index_mul_finrank_intertwiningMap [Finite J] [CharZero k] (hθ : θ.IsFullyRamified)
    (ρ : Representation k J E) (σ : Representation k J E') [FiniteDimensional k E]
    [FiniteDimensional k E'] (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ)
    (hσ : ∀ (h : H) (ξ : E'), σ h ξ = (θ h : k) • ξ) :
    H.index * finrank k (IntertwiningMap ρ σ) = finrank k E * finrank k E' := by
  have := Fintype.ofFinite J
  have : Invertible (Nat.card J : k) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have h := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  rw [hθ.sum_character_mul_character_inv σ ρ hσ hρ, ← H.card_mul_index, Nat.cast_mul] at h
  have hH : (Nat.card H : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hI : (H.index : k) ≠ 0 := Nat.cast_ne_zero.2 H.index_ne_zero_of_finite
  -- `h : (|H| [J : H])⁻¹ (|H| dim E' dim E) = dim Hom_J(ρ, σ)`; cancel `|H|`, then `[J : H]`.
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ hH, inv_mul_eq_iff_eq_mul₀ hI] at h
  exact_mod_cast h.symm.trans (mul_comm _ _)

/-- **`(dim η)² = [J : H]`.** If `θ` is fully ramified, then over an algebraically closed field of
characteristic zero, an irreducible representation of the finite group `J` on which `H` acts by
`θ` has dimension `d` with `d² = [J : H]`. -/
theorem finrank_sq_eq_index [Finite J] [IsAlgClosed k] [CharZero k] (hθ : θ.IsFullyRamified)
    (ρ : Representation k J E) [ρ.IsIrreducible] (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ) :
    finrank k E ^ 2 = H.index := by
  have := ρ.asModuleEquiv.finiteDimensional
  simpa [sq] using (hθ.index_mul_finrank_intertwiningMap ρ ρ hρ hρ).symm

/-- **Uniqueness of the fully ramified representation.** If `θ` is fully ramified, then over a
field of characteristic zero, two irreducible representations of the finite group `J` on which `H`
acts by `θ` are equivalent. -/
theorem nonempty_equiv [Finite J] [CharZero k] (hθ : θ.IsFullyRamified)
    (ρ : Representation k J E) [ρ.IsIrreducible] (σ : Representation k J E') [σ.IsIrreducible]
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ)
    (hσ : ∀ (h : H) (ξ : E'), σ h ξ = (θ h : k) • ξ) :
    Nonempty (ρ.Equiv σ) := by
  have := ρ.asModuleEquiv.finiteDimensional
  have := σ.asModuleEquiv.finiteDimensional
  by_contra hne
  have : IsEmpty (ρ.Equiv σ) := not_nonempty_iff.1 hne
  have h := hθ.index_mul_finrank_intertwiningMap ρ σ hρ hσ
  rw [finrank_zero_of_subsingleton, mul_zero] at h
  exact (Nat.mul_pos (inferInstance : ρ.IsIrreducible).finrank_pos
    (inferInstance : σ.IsIrreducible).finrank_pos).ne h

/-- **Representations on which `H` acts by `θ` are isotypic.** Let `θ` be fully ramified, let `k`
be algebraically closed of characteristic zero, and let `ρ` be irreducible and `σ`
finite-dimensional, both with `H` acting by `θ`. Then `dim σ = dim ρ · dim Hom_J(ρ, σ)`, the
dimension count of `σ` being a sum of copies of `ρ`. -/
theorem finrank_eq_finrank_mul_finrank_intertwiningMap [Finite J] [IsAlgClosed k] [CharZero k]
    (hθ : θ.IsFullyRamified) (ρ : Representation k J E) [ρ.IsIrreducible]
    (σ : Representation k J E') [FiniteDimensional k E']
    (hρ : ∀ (h : H) (ξ : E), ρ h ξ = (θ h : k) • ξ)
    (hσ : ∀ (h : H) (ξ : E'), σ h ξ = (θ h : k) • ξ) :
    finrank k E' = finrank k E * finrank k (IntertwiningMap ρ σ) := by
  have := ρ.asModuleEquiv.finiteDimensional
  have h := hθ.index_mul_finrank_intertwiningMap ρ σ hρ hσ
  rw [← hθ.finrank_sq_eq_index ρ hρ, sq, mul_assoc] at h
  exact (Nat.eq_of_mul_eq_mul_left (inferInstance : ρ.IsIrreducible).finrank_pos h).symm

end IsFullyRamified

end MonoidHom
