/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Topology

/-!
# Finite cylinders, the query code and the size of the coding space

The configurations taking prescribed values on a finite set of atoms form a **finite cylinder**.
Finite cylinders are clopen and form a basis of the topology of the coding space.

When each arity has countably many relation symbols, the atoms over `ℕ` are countable, and
reading a configuration along `Encodable.decode` for `Encodable.ofCountable` gives its **query
code**, a sequence of Booleans padded with `false` where decoding fails. The query code is a
closed embedding of the coding space into Cantor space `ℕ → Bool`. The decoder need not be
injective on the indices where it succeeds, so the range is the set of sequences that are `false`
where decoding fails and agree at any two indices decoding to the same atom.

On a countably infinite carrier, a language with countably many relation symbols of each arity,
one of them of positive arity, has exactly continuum many configurations.

See Gao, *Invariant Descriptive Set Theory*, for these spaces of structures.

## Main definitions

* `TauCeti.RelationalConfiguration.cylinder`: the configurations agreeing with a given function
  on a finite set of atoms;
* `TauCeti.RelationalConfiguration.queryCode`: the coordinates of a configuration on `ℕ` read
  along the decoder of `Encodable.ofCountable`, padded with `false`.

## Main results

* `TauCeti.RelationalConfiguration.isTopologicalBasis_cylinder`: the finite cylinders form a
  basis of clopen sets (`isClopen_cylinder`);
* `TauCeti.RelationalConfiguration.isClosedEmbedding_queryCode`: the query code is a closed
  embedding into Cantor space, with range `range_queryCode`;
* `TauCeti.RelationalConfiguration.mk_eq_continuum`: on a countably infinite carrier, with a
  relation symbol of positive arity, there are continuum many configurations.
-/

public section

open Topology TopologicalSpace

namespace TauCeti.RelationalConfiguration

variable {L : FirstOrder.Language} {V : Type*}

/-! ### Finite cylinders -/

/-- The **finite cylinder** of the configurations agreeing with `f` on the finite set `s` of
atoms. -/
def cylinder (s : Finset (Atom L V)) (f : Atom L V → Bool) : Set (RelationalConfiguration L V) :=
  {c | ∀ a ∈ s, c.eval a = f a}

@[simp]
theorem mem_cylinder {s : Finset (Atom L V)} {f : Atom L V → Bool}
    {c : RelationalConfiguration L V} : c ∈ cylinder s f ↔ ∀ a ∈ s, c.eval a = f a := Iff.rfl

/-- A finite cylinder is clopen: a finite intersection of clopen one-atom cylinders. -/
theorem isClopen_cylinder (s : Finset (Atom L V)) (f : Atom L V → Bool) :
    IsClopen (cylinder s f) := by
  have h : cylinder s f = ⋂ a ∈ s, {c : RelationalConfiguration L V | c.eval a = f a} := by
    ext c
    simp
  rw [h]
  exact isClopen_biInter_finset fun a _ => isClopen_setOf_eval a (f a)

/-- A finite cylinder is measurable. -/
theorem measurableSet_cylinder (s : Finset (Atom L V)) (f : Atom L V → Bool) :
    MeasurableSet (cylinder s f) := by
  have h : cylinder s f = ⋂ a ∈ s, {c : RelationalConfiguration L V | c.eval a = f a} := by
    ext c
    simp
  rw [h]
  exact s.measurableSet_biInter fun a _ => measurableSet_setOf_eval a (f a)

/-- A configuration lies in the finite cylinder of its own values on any finite set of atoms. -/
theorem mem_cylinder_eval (s : Finset (Atom L V)) (c : RelationalConfiguration L V) :
    c ∈ cylinder s c.eval :=
  fun _ _ => rfl

/-- The finite cylinders form a basis of the topology of the coding space. -/
theorem isTopologicalBasis_cylinder :
    IsTopologicalBasis
      (Set.range fun p : Finset (Atom L V) × (Atom L V → Bool) => cylinder p.1 p.2) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun c U hc hU => ?_
  · rintro _ ⟨⟨s, f⟩, rfl⟩
    exact (isClopen_cylinder s f).isOpen
  · obtain ⟨I, u, hu, hIU⟩ :=
      isOpen_pi_iff.1 (show IsOpen (X := Atom L V → Bool) U from hU) c hc
    refine ⟨_, ⟨⟨I, c.eval⟩, rfl⟩, mem_cylinder_eval I c, fun d hd => hIU fun a ha => ?_⟩
    have h := hd a ha
    simp only [eval_def] at h
    rw [h]
    exact (hu a ha).2

/-! ### The query code -/

section QueryCode

variable [∀ n, Countable (L.Relations n)]

/-- The **query code** of a configuration on `ℕ`: at `n`, the value of the atom that the decoder of
`Encodable.ofCountable` returns at `n`, and `false` where decoding fails. It embeds the coding space
into Cantor space (`isClosedEmbedding_queryCode`). -/
noncomputable def queryCode (c : RelationalConfiguration L ℕ) : ℕ → Bool :=
  letI : Encodable (Atom L ℕ) := Encodable.ofCountable _
  fun n => (Encodable.decode n : Option (Atom L ℕ)).elim false c.eval

/-- The query code reads, at `n`, the atom decoded at `n`, and is `false` where decoding fails. -/
theorem queryCode_apply (c : RelationalConfiguration L ℕ) (n : ℕ) :
    queryCode c n =
      (@Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n).elim false c.eval := (rfl)

/-- The query code reads the atom `a` at its index `Encodable.encode a`. -/
@[simp]
theorem queryCode_encode (c : RelationalConfiguration L ℕ) (a : Atom L ℕ) :
    queryCode c (@Encodable.encode (Atom L ℕ) (Encodable.ofCountable _) a) = c.eval a := by
  let : Encodable (Atom L ℕ) := Encodable.ofCountable _
  rw [queryCode_apply, Encodable.encodek]
  rfl

/-- The query code is `false` at the indices where decoding fails. -/
theorem queryCode_of_decode_eq_none (c : RelationalConfiguration L ℕ) {n : ℕ}
    (hn : @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n = none) :
    queryCode c n = false := by
  rw [queryCode_apply, hn]
  rfl

/-- The query code is `c.eval a` at an index decoding to `a`. -/
theorem queryCode_of_decode_eq_some (c : RelationalConfiguration L ℕ) {n : ℕ} {a : Atom L ℕ}
    (hn : @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n = some a) :
    queryCode c n = c.eval a := by
  rw [queryCode_apply, hn]
  rfl

/-- The query code is continuous: each coordinate reads one atom or is constantly `false`. -/
@[fun_prop]
theorem continuous_queryCode : Continuous (queryCode (L := L)) := by
  refine continuous_pi fun n => ?_
  cases h : @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n with
  | none => simpa only [queryCode_of_decode_eq_none _ h] using continuous_const
  | some a => simpa only [queryCode_of_decode_eq_some _ h] using continuous_eval a

/-- The query code is injective: it reads every atom. -/
theorem queryCode_injective : Function.Injective (queryCode (L := L)) :=
  fun c d h => ext fun a => by
    rw [← queryCode_encode c a, ← queryCode_encode d a, h]

/-- **The query code is a closed embedding** of the coding space into Cantor space. -/
theorem isClosedEmbedding_queryCode : IsClosedEmbedding (queryCode (L := L)) :=
  continuous_queryCode.isClosedEmbedding queryCode_injective

/-- The range of the query code: the sequences that are `false` where decoding fails and agree at
any two indices decoding to the same atom. -/
theorem range_queryCode :
    Set.range (queryCode (L := L)) =
      {x : ℕ → Bool |
        (∀ n, @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n = none → x n = false) ∧
          ∀ m n, @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) m =
            @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n → x m = x n} := by
  let : Encodable (Atom L ℕ) := Encodable.ofCountable _
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun n hn => queryCode_of_decode_eq_none c hn, fun m n hmn => ?_⟩
    rw [queryCode_apply, queryCode_apply, hmn]
  · rintro ⟨hnone, hsame⟩
    refine ⟨mk fun a => x (Encodable.encode a), funext fun n => ?_⟩
    cases h : (Encodable.decode n : Option (Atom L ℕ)) with
    | none => rw [queryCode_of_decode_eq_none _ h, hnone n h]
    | some a =>
      rw [queryCode_of_decode_eq_some _ h, eval_mk]
      exact hsame _ _ ((Encodable.encodek a).trans h.symm)

end QueryCode

/-! ### Cardinality -/

/-- On an infinite carrier, a relation symbol of positive arity gives infinitely many atoms. -/
theorem Atom.infinite_of_relations [Infinite V] {n : ℕ} (hn : n ≠ 0) (R : L.Relations n) :
    Infinite (Atom L V) :=
  Infinite.of_injective (fun v : V => atom R fun _ => v) fun _ _ h =>
    congrFun (atom_inj.1 h).2 ⟨0, Nat.pos_of_ne_zero hn⟩

/-- **There are continuum many configurations** on a countably infinite carrier in a language
with countably many relation symbols of each arity, one of them of positive arity. -/
theorem mk_eq_continuum (L : FirstOrder.Language) (V : Type*)
    [∀ n, Countable (L.Relations n)] [Countable V] [Infinite V] {n : ℕ} (hn : n ≠ 0)
    (R : L.Relations n) :
    Cardinal.mk (RelationalConfiguration L V) = Cardinal.continuum := by
  refine (mk_le_continuum L V).antisymm ?_
  have := Atom.infinite_of_relations (V := V) hn R
  rw [RelationalConfiguration, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.lift_ofNat,
    ← Cardinal.two_power_aleph0]
  exact Cardinal.power_le_power_left two_ne_zero
    (by simp)

end TauCeti.RelationalConfiguration
