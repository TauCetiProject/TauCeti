/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Decidable
public import TauCeti.Algebra.GroupAction.DiagonalOrbits

/-!
# Connected permutation triples and their isomorphism classes

A connected permutation triple is a permutation triple whose monodromy group acts transitively on
the sheets, and two connected triples are isomorphic when they are related by a simultaneous
relabeling of the sheets. This file introduces the connected triples as a carrier, their
isomorphism classes as the quotient by the relabeling action, and the finset of connected triples
that make up a class. Since connectedness is decidable, the carrier is a computable `Fintype`, and
since equality of classes reduces to a search through the finitely many relabelings, so is the
quotient.

Finally, it introduces connected triples with a marked label modulo the diagonal relabeling action,
which moves the label along with the triple. They are the combinatorial invariant of a pointed cover
of the thrice-punctured sphere, as isomorphism classes of connected triples are of a cover.

## Main definitions

* `TauCeti.ConnectedTriple`: a permutation triple together with connectedness.
* `TauCeti.ConnectedIsoClass`: connected triples modulo simultaneous relabeling.
* `TauCeti.PermutationTriple.IsoClass.IsConnected`: connectedness of an ordinary triple class.
* `TauCeti.ConnectedIsoClass.forget`: inclusion into the isomorphism classes of all triples.
* `TauCeti.ConnectedIsoClass.orbitFinset`: the connected triples in a class, as a finset.
* `TauCeti.MarkedIsoClass`: connected triples with a marked label, modulo the diagonal relabeling
  action `τ • (t, i) = (τ • t, τ i)`, and `TauCeti.MarkedIsoClass.forget`, which forgets the label.

## Main results

* `TauCeti.ConnectedIsoClass.equivSubtype`: connected classes are exactly the connected elements
  of the quotient of all triples, using Mathlib's `Equiv.subtypeQuotientEquivQuotientSubtype`.
* `TauCeti.ConnectedIsoClass.forget_injective`: forgetting connectedness preserves distinct classes.
* `TauCeti.ConnectedIsoClass.mk_eq_mk_iff_exists_smul`,
  `TauCeti.ConnectedIsoClass.mk_eq_mk_iff_equivalent`: two connected triples have the same class
  exactly when a relabeling carries one onto the other, that is, when the underlying permutation
  triples are isomorphic.
* `TauCeti.ConnectedIsoClass.mem_orbitFinset`, `TauCeti.ConnectedIsoClass.coe_orbitFinset`: the
  finset of a class consists of the connected triples of that class, and is the class's orbit
  `MulAction.orbitRel.Quotient.orbit`.
* `TauCeti.ConnectedIsoClass.orbitFinset_injective`: distinct classes have distinct finsets.
* `TauCeti.MarkedIsoClass.mk_eq_mk_iff_exists_smul`: two marked connected triples have the same
  class exactly when a relabeling carries one triple onto the other and its label onto the other
  label.
* `TauCeti.MarkedIsoClass.stabilizerEquiv`: fixing a label identifies marked classes with
  connected triples modulo permutations stabilizing that label.
-/

open Equiv MulAction

public section

namespace TauCeti

namespace PermutationTriple.IsoClass

variable {n : ℕ}

/-- Connectedness of any representative of an isomorphism class of triples. -/
def IsConnected : PermutationTriple.IsoClass n → Prop :=
  lift PermutationTriple.IsConnected fun t t' h => by
    obtain ⟨τ, rfl⟩ := PermutationTriple.equivalent_iff_exists_smul_eq.mp h
    exact propext (PermutationTriple.isConnected_smul_iff τ t).symm

/-- A triple class is connected exactly when its representative is connected. -/
@[simp]
theorem isConnected_mk (t : PermutationTriple n) :
    (mk t).IsConnected ↔ t.IsConnected := by
  rw [IsConnected, lift_mk]

end PermutationTriple.IsoClass

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

/-- Connected isomorphism classes are exactly the connected elements of the quotient of all
permutation triples. -/
def equivSubtype (n : ℕ) :
    ConnectedIsoClass n ≃ {c : PermutationTriple.IsoClass n // c.IsConnected} :=
  (Equiv.subtypeQuotientEquivQuotientSubtype PermutationTriple.IsConnected
    PermutationTriple.IsoClass.IsConnected
    (fun t => by
      simpa only [PermutationTriple.IsoClass.quotient_mk] using
        (PermutationTriple.IsoClass.isConnected_mk t).symm)
    (fun t t' => by
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
        Subtype.ext_iff, ConnectedTriple.coe_smul])).symm

/-- The connected class of a representative corresponds to its ordinary class together with
the induced connectedness proof. -/
@[simp]
theorem equivSubtype_mk (t : ConnectedTriple n) :
    equivSubtype n (mk t) = ⟨PermutationTriple.IsoClass.mk t.1,
      (PermutationTriple.IsoClass.isConnected_mk t.1).2 t.2⟩ := by
  apply Subtype.ext
  dsimp only
  rw [← PermutationTriple.IsoClass.quotient_mk]
  exact congrArg Subtype.val
    (Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk
      (s₁ := MulAction.orbitRel (Perm (Fin n)) (PermutationTriple n))
      (s₂ := MulAction.orbitRel (Perm (Fin n)) (ConnectedTriple n)) _ _ _ _ t)

/-- The isomorphism class of a connected triple, viewed among all permutation triples. -/
def forget (c : ConnectedIsoClass n) : PermutationTriple.IsoClass n :=
  (equivSubtype n c).1

/-- Forgetting connectedness sends a connected representative to its ordinary triple class. -/
@[simp]
theorem forget_mk (t : ConnectedTriple n) :
    (mk t).forget = PermutationTriple.IsoClass.mk t.1 :=
  congrArg Subtype.val (equivSubtype_mk t)

/-- Recovering a connected quotient class from a connected representative of an ordinary class. -/
@[simp]
theorem equivSubtype_symm_mk (t : PermutationTriple n)
    (h : (PermutationTriple.IsoClass.mk t).IsConnected) :
    (equivSubtype n).symm ⟨PermutationTriple.IsoClass.mk t, h⟩ =
      mk ⟨t, (PermutationTriple.IsoClass.isConnected_mk t).1 h⟩ := by
  apply (equivSubtype n).injective
  simp

/-- Forgetting connectedness does not identify distinct isomorphism classes. -/
theorem forget_injective : Function.Injective (forget : ConnectedIsoClass n → _) :=
  fun _ _ h => (equivSubtype n).injective (Subtype.ext h)

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

/-- Connected permutation triples of degree `n` with a marked label, modulo the diagonal relabeling
action `τ • (t, i) = (τ • t, τ i)`: the relabeling moves the label along with the triple.
Quotienting by the stabilizer of the label instead would never identify pairs with different
labels. -/
def MarkedIsoClass (n : ℕ) : Type :=
  MulAction.orbitRel.Quotient (Perm (Fin n)) (ConnectedTriple n × Fin n)

namespace MarkedIsoClass

variable {n : ℕ}

/-- The class of a connected triple with the marked label `i`. -/
def mk (t : ConnectedTriple n) (i : Fin n) : MarkedIsoClass n :=
  Quotient.mk'' (t, i)

/-- Two marked connected triples determine the same class exactly when they are related by the
diagonal relabeling action. -/
@[simp]
theorem mk_eq_mk_iff {t t' : ConnectedTriple n} {i i' : Fin n} :
    mk t i = mk t' i' ↔
      MulAction.orbitRel (Perm (Fin n)) (ConnectedTriple n × Fin n) (t, i) (t', i') :=
  Quotient.eq''

/-- Two marked connected triples have the same class exactly when some relabeling carries the
second triple onto the first and the second label onto the first. -/
theorem mk_eq_mk_iff_exists_smul {t t' : ConnectedTriple n} {i i' : Fin n} :
    mk t i = mk t' i' ↔ ∃ τ : Perm (Fin n), τ • t' = t ∧ τ i' = i := by
  rw [mk_eq_mk_iff, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  simp [Prod.ext_iff, Perm.smul_def]

/-- Relabeling a marked triple, label included, does not change its class. -/
@[simp]
theorem mk_smul (τ : Perm (Fin n)) (t : ConnectedTriple n) (i : Fin n) :
    mk (τ • t) (τ i) = mk t i :=
  mk_eq_mk_iff_exists_smul.2 ⟨τ, rfl, rfl⟩

theorem mk_surjective (c : MarkedIsoClass n) :
    ∃ (t : ConnectedTriple n) (i : Fin n), mk t i = c :=
  Quotient.inductionOn' c fun ti => ⟨ti.1, ti.2, rfl⟩

/-- Forgetting the marked label of a class. -/
def forget : MarkedIsoClass n → ConnectedIsoClass n :=
  Quotient.map' Prod.fst fun _ _ ⟨τ, hτ⟩ => ⟨τ, congrArg Prod.fst hτ⟩

@[simp]
theorem forget_mk (t : ConnectedTriple n) (i : Fin n) :
    (mk t i).forget = ConnectedIsoClass.mk t :=
  (rfl)

/-- Fixing any label identifies its stabilizer-orbit quotient with marked triple classes.
For positive degree, `i = 0` gives the fixed-zero-label description. -/
noncomputable def stabilizerEquiv (i : Fin n) :
    MulAction.orbitRel.Quotient (MulAction.stabilizer (Perm (Fin n)) i) (ConnectedTriple n) ≃
      MarkedIsoClass n :=
  TauCeti.MulAction.orbitRelQuotientStabilizerEquiv
    (G := Perm (Fin n)) (X := ConnectedTriple n) i

/-- The stabilizer orbit of a triple is sent to its class marked at the fixed label. -/
@[simp]
theorem stabilizerEquiv_mk (i : Fin n) (t : ConnectedTriple n) :
    stabilizerEquiv i (Quotient.mk'' t) = mk t i := by
  exact TauCeti.MulAction.orbitRelQuotientStabilizerEquiv_mk
    (G := Perm (Fin n)) i t

/-- A class already marked at the fixed label is sent back to the stabilizer orbit of its
triple. -/
@[simp]
theorem stabilizerEquiv_symm_mk (i : Fin n) (t : ConnectedTriple n) :
    (stabilizerEquiv i).symm (mk t i) = Quotient.mk'' t := by
  rw [← stabilizerEquiv_mk i t, Equiv.symm_apply_apply]

/-- Moving a marked label back to the fixed label also applies the inverse permutation to
its triple. -/
@[simp]
theorem stabilizerEquiv_symm_mk_apply (i : Fin n) (t : ConnectedTriple n)
    (τ : Perm (Fin n)) :
    (stabilizerEquiv i).symm (mk t (τ i)) = Quotient.mk'' (τ⁻¹ • t) := by
  rw [stabilizerEquiv, mk]
  exact TauCeti.MulAction.orbitRelQuotientStabilizerEquiv_symm_mk_smul
    (G := Perm (Fin n)) i t τ

end MarkedIsoClass

end TauCeti
