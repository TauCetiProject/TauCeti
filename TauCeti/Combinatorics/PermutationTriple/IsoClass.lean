/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Decidable

/-!
# Connected permutation triples and their isomorphism classes

A connected permutation triple is a permutation triple whose monodromy group acts transitively on
the sheets, and two connected triples are isomorphic when they are related by a simultaneous
relabeling of the sheets. This file introduces the connected triples as a carrier, their
isomorphism classes as the quotient by the relabeling action, and the finset of connected triples
that make up a class. Since connectedness is decidable, the carrier is a computable `Fintype`, and
since equality of classes reduces to a search through the finitely many relabelings, so is the
quotient.

## Main definitions

* `TauCeti.ConnectedTriple`: a permutation triple together with connectedness.
* `TauCeti.ConnectedIsoClass`: connected triples modulo simultaneous relabeling.
* `TauCeti.ConnectedIsoClass.orbitFinset`: the connected triples in a class, as a finset.

## Main results

* `TauCeti.ConnectedIsoClass.mk_eq_mk_iff_exists_smul`,
  `TauCeti.ConnectedIsoClass.mk_eq_mk_iff_equivalent`: two connected triples have the same class
  exactly when a relabeling carries one onto the other, that is, when the underlying permutation
  triples are isomorphic.
* `TauCeti.ConnectedIsoClass.mem_orbitFinset`, `TauCeti.ConnectedIsoClass.coe_orbitFinset`: the
  finset of a class consists of the connected triples of that class, and is the class's orbit
  `MulAction.orbitRel.Quotient.orbit`.
* `TauCeti.ConnectedIsoClass.orbitFinset_injective`: distinct classes have distinct finsets.
-/

open Equiv MulAction

public section

namespace TauCeti

/-- A connected permutation triple of degree `n`. -/
abbrev ConnectedTriple (n : ℕ) : Type :=
  {t : PermutationTriple n // t.IsConnected}

namespace ConnectedTriple

variable {n : ℕ}

/-- Relabeling a connected triple simultaneously conjugates its three permutations. -/
instance : MulAction (Perm (Fin n)) (ConnectedTriple n) where
  smul τ t := ⟨τ • t.1, (PermutationTriple.isConnected_smul_iff τ t.1).2 t.2⟩
  one_smul t := Subtype.ext (one_smul _ t.1)
  mul_smul τ υ t := Subtype.ext (mul_smul τ υ t.1)

instance : DecidableEq (ConnectedTriple n) := inferInstance

@[simp]
theorem coe_smul (τ : Perm (Fin n)) (t : ConnectedTriple n) :
    ((τ • t : ConnectedTriple n) : PermutationTriple n) = τ • (t : PermutationTriple n) :=
  (rfl)

end ConnectedTriple

/-- Isomorphism classes of connected permutation triples of degree `n`. -/
@[expose] def ConnectedIsoClass (n : ℕ) : Type :=
  MulAction.orbitRel.Quotient (Perm (Fin n)) (ConnectedTriple n)

namespace ConnectedIsoClass

variable {n : ℕ}

/-- The isomorphism class of a connected triple. -/
@[expose] def mk (t : ConnectedTriple n) : ConnectedIsoClass n :=
  Quotient.mk'' t

/-- Two connected triples determine the same isomorphism class exactly when they are related by
simultaneous relabeling. -/
@[simp]
theorem mk_eq_mk_iff {t t' : ConnectedTriple n} :
    mk t = mk t' ↔ MulAction.orbitRel (Perm (Fin n)) (ConnectedTriple n) t t' :=
  Quotient.eq''

/-- Two connected triples determine the same isomorphism class exactly when some relabeling
carries the second onto the first. -/
theorem mk_eq_mk_iff_exists_smul {t t' : ConnectedTriple n} :
    mk t = mk t' ↔ ∃ τ : Perm (Fin n), τ • t' = t := by
  rw [mk_eq_mk_iff, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

theorem mk_surjective : Function.Surjective (mk : ConnectedTriple n → ConnectedIsoClass n) :=
  Quotient.mk''_surjective

/-- Two connected triples determine the same isomorphism class exactly when the underlying
permutation triples are isomorphic. -/
theorem mk_eq_mk_iff_equivalent {t t' : ConnectedTriple n} :
    mk t = mk t' ↔ PermutationTriple.Equivalent (t : PermutationTriple n) t' := by
  rw [mk_eq_mk_iff_exists_smul, PermutationTriple.equivalent_iff_exists_smul_eq]
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ⁻¹, by simp⟩
  · rintro ⟨τ, h⟩
    exact ⟨τ⁻¹, Subtype.ext (by rw [ConnectedTriple.coe_smul, ← h, inv_smul_smul])⟩

/-- Equality of isomorphism classes is decidable: on representatives, decide isomorphism of the
underlying permutation triples. -/
instance : DecidableEq (ConnectedIsoClass n) := fun c c' =>
  Quotient.recOnSubsingleton₂ c c' fun t t' =>
    decidable_of_iff (PermutationTriple.Equivalent (t : PermutationTriple n) t')
      mk_eq_mk_iff_equivalent.symm

instance : Fintype (ConnectedIsoClass n) := Fintype.ofSurjective mk mk_surjective

/-! ### The connected triples of a class, as a finset -/

/-- The connected triples in an isomorphism class, as a finset: the relabeling orbit of any
representative. -/
@[expose] def orbitFinset (c : ConnectedIsoClass n) : Finset (ConnectedTriple n) :=
  Quotient.liftOn' c (fun t => (Finset.univ : Finset (Perm (Fin n))).image (· • t))
    fun t t' h => by
    have horbit : ∀ u, u ∈ orbit (Perm (Fin n)) t ↔ u ∈ orbit (Perm (Fin n)) t' := fun u => by
      rw [MulAction.orbit_eq_iff.2 h]
    ext u
    simpa [MulAction.mem_orbit_iff] using horbit u

@[simp]
theorem orbitFinset_mk (t : ConnectedTriple n) :
    (mk t).orbitFinset = (Finset.univ : Finset (Perm (Fin n))).image (· • t) :=
  (rfl)

/-- A connected triple lies in the finset of a class exactly when the class is its own. -/
@[simp]
theorem mem_orbitFinset {t : ConnectedTriple n} {c : ConnectedIsoClass n} :
    t ∈ c.orbitFinset ↔ mk t = c := by
  obtain ⟨t', rfl⟩ := mk_surjective c
  rw [orbitFinset_mk, mk_eq_mk_iff_exists_smul]
  simp

/-- The finset of a class is the class's orbit, `MulAction.orbitRel.Quotient.orbit`. -/
@[simp]
theorem coe_orbitFinset (c : ConnectedIsoClass n) :
    (c.orbitFinset : Set (ConnectedTriple n)) = MulAction.orbitRel.Quotient.orbit c := by
  obtain ⟨t, rfl⟩ := mk_surjective c
  rw [orbitFinset_mk, mk, MulAction.orbitRel.Quotient.orbit_mk]
  ext u
  simp [MulAction.mem_orbit_iff]

/-- Distinct isomorphism classes have distinct finsets of connected triples. -/
theorem orbitFinset_injective :
    Function.Injective (orbitFinset : ConnectedIsoClass n → Finset (ConnectedTriple n)) :=
  fun c c' h => MulAction.orbitRel.Quotient.orbit_injective (by rw [← coe_orbitFinset, h,
    coe_orbitFinset])

end ConnectedIsoClass

end TauCeti
