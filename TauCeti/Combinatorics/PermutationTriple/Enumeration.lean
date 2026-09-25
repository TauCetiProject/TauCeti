/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.IsoClass

/-!
# Enumeration of connected permutation triples

Connectedness of a permutation triple is decidable, so the connected triples of a given degree
form a computable finset, and so do their isomorphism classes, each class listed as the finset of
connected triples it contains — the relabeling orbit, not a chosen representative. This file
records both finsets and identifies their members and cardinalities with the corresponding types,
and then establishes the number of isomorphism classes of connected triples — equivalently, of
connected dessins d'enfants with a given number of edges — in degrees one to three:

```text
degree               1   2   3
connected classes    1   3   7
```

The three degree-two classes are the double cover of the sphere branched at two of the three
branch points, one class for each choice of the unbranched point. The seven degree-three classes
are the cyclic cover `z ↦ z³` in its three orderings of the branch points (monodromy `C₃`, one
branch point unramified), the `S₃`-cover `TauCeti.PermutationTriple.s3Triple` in its three
orderings (monodromy `S₃`), and the genus-one cover with a three-cycle at every branch point
(monodromy `C₃`).

## Main definitions

* `TauCeti.connectedTriples n`: the connected permutation triples of degree `n`, as a finset.
* `TauCeti.isoClasses n`: their isomorphism classes, as the finset of relabeling orbits.

## Main results

* `TauCeti.mem_connectedTriples`, `TauCeti.mem_isoClasses`: the members of the two finsets are
  exactly the connected triples, and exactly the relabeling orbits of connected triples.
* `TauCeti.existsUnique_mem_isoClasses`: every connected triple lies in exactly one member of
  `TauCeti.isoClasses n`, so the listed orbits partition the connected triples.
* `TauCeti.card_connectedTriples`, `TauCeti.card_isoClasses`: the two finsets have the
  cardinalities of `TauCeti.ConnectedTriple n` and `TauCeti.ConnectedIsoClass n`.
* `TauCeti.ConnectedIsoClass.card_one`, `TauCeti.ConnectedIsoClass.card_two`,
  `TauCeti.ConnectedIsoClass.card_three`: the number of isomorphism classes of connected
  permutation triples of degree one, two, and three.
-/

open Equiv

public section

namespace TauCeti

variable {n : ℕ}

/-- The connected permutation triples of degree `n`, as a finset. -/
@[expose] def connectedTriples (n : ℕ) : Finset (PermutationTriple n) :=
  Finset.univ.filter PermutationTriple.IsConnected

/-- The members of `TauCeti.connectedTriples n` are exactly the connected permutation triples of
degree `n`. -/
@[simp]
theorem mem_connectedTriples {t : PermutationTriple n} :
    t ∈ connectedTriples n ↔ t.IsConnected := by
  simp [connectedTriples]

/-- The finset of connected triples of degree `n` has the cardinality of the type
`TauCeti.ConnectedTriple n`. -/
theorem card_connectedTriples : (connectedTriples n).card = Fintype.card (ConnectedTriple n) :=
  (Fintype.card_subtype _).symm

/-- The isomorphism classes of connected permutation triples of degree `n`, as the finset of
relabeling orbits: each class is listed as the finset of connected triples it contains. -/
@[expose] def isoClasses (n : ℕ) : Finset (Finset (ConnectedTriple n)) :=
  Finset.univ.image ConnectedIsoClass.orbitFinset

/-- The members of `TauCeti.isoClasses n` are exactly the relabeling orbits of connected
triples. -/
@[simp]
theorem mem_isoClasses {s : Finset (ConnectedTriple n)} :
    s ∈ isoClasses n ↔
      ∃ t : ConnectedTriple n, (Finset.univ : Finset (Perm (Fin n))).image (· • t) = s := by
  simp only [isoClasses, Finset.mem_image, Finset.mem_univ, true_and,
    ConnectedIsoClass.mk_surjective.exists, ConnectedIsoClass.orbitFinset_mk]

/-- Every connected triple lies in exactly one of the listed relabeling orbits: the members of
`TauCeti.isoClasses n` partition the connected triples of degree `n`. -/
theorem existsUnique_mem_isoClasses (t : ConnectedTriple n) :
    ∃! s, s ∈ isoClasses n ∧ t ∈ s := by
  refine ⟨(ConnectedIsoClass.mk t).orbitFinset,
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ConnectedIsoClass.mem_orbitFinset.2 rfl⟩,
    fun s ⟨hs, ht⟩ => ?_⟩
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hs
  rw [ConnectedIsoClass.mem_orbitFinset.1 ht]

/-- The finset of isomorphism classes of degree `n` has the cardinality of the type
`TauCeti.ConnectedIsoClass n`. -/
theorem card_isoClasses : (isoClasses n).card = Fintype.card (ConnectedIsoClass n) := by
  rw [isoClasses, Finset.card_image_of_injective _ ConnectedIsoClass.orbitFinset_injective,
    Finset.card_univ]

namespace ConnectedIsoClass

/-- There is one isomorphism class of connected permutation triples of degree one. -/
theorem card_one : Fintype.card (ConnectedIsoClass 1) = 1 := by decide

/-- There are three isomorphism classes of connected permutation triples of degree two. -/
theorem card_two : Fintype.card (ConnectedIsoClass 2) = 3 := by decide

/-- There are seven isomorphism classes of connected permutation triples of degree three. -/
theorem card_three : Fintype.card (ConnectedIsoClass 3) = 7 := by decide +kernel

end ConnectedIsoClass

end TauCeti
