/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Normalizer

/-!
# The generating triples of a passport

A passport records a reference monodromy subgroup `P.G` together with the three ordered full cycle
types of the generating triples it contains. For a passport of nonzero degree whose reference
subgroup is pretransitive — the first two conjuncts of `TauCeti.PassportSpec.IsAdmissible` — the
number of isomorphism classes in the passport is the number of `P.G`-generating triples of `S_n`
with those cycle data, counted up to the action of the normalizer of `P.G`, which is
`TauCeti.PassportSpec.passportSize_eq_card_generatingTripleOrbits`; the count itself, that of the
generating triples before the normalizer action, needs no such hypothesis. This file names that
finite set of generating triples and gives its cardinality.

## The classes of a cycle type

One `S_n`-cycle type can meet several `G`-classes, and can meet none, so a count of the members of
`G` with a prescribed cycle type is a sum over `G`-classes rather than a single class size. That
index set is `TauCeti.Subgroup.classesOfFullCycleType`, in
`TauCeti/GroupTheory/Perm/ConjClass.lean`, for a group of permutations in general;
`TauCeti.Subgroup.mem_iUnionClassesOfFullCycleType` there identifies the union of those classes,
the set `TauCeti.Subgroup.iUnionClassesOfFullCycleType`, with the elements of the group of that
cycle type.

## The generating triples of a passport

`TauCeti.PassportSpec.generatingTriples` is the set of product-one triples of permutations whose
first two entries generate `P.G` and whose three cycle types are those of `P`: the generating
triples of the passport, as triples of permutations. The product-one relation makes the third
entry a function of the first two
(`TauCeti.PermutationTriple.ofTwo_σinf_eq_of_product_eq_one`), so
`TauCeti.PassportSpec.generatingTriplesEquiv` is the elimination rule identifying that finite set
with `TauCeti.PassportSpec.GeneratingTriple`, the two maps being computed by
`TauCeti.PassportSpec.generatingTriplesEquiv_apply` and
`TauCeti.PassportSpec.generatingTriplesEquiv_symm_apply`, and
`TauCeti.PassportSpec.card_generatingTriples` reads the size of the passport's generating triples
off it. This is the finite set that a sum over triples of classes counts, and that the normalizer
of `P.G` acts on.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5 (constellations, and the size of a passport).
* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, ANTS XIII,
  The Open Book Series 2 (2019), 375–392, §2 (the normalizer formulation of a passport).
-/

open Equiv MulAction

public section

namespace TauCeti

namespace PassportSpec

variable {n : ℕ}

/-! ## The generating triples of a passport -/

open scoped Classical in
/-- The product-one triples of `S_n` of the three cycle types recorded by `P` whose first two
entries generate the reference subgroup: the generating triples of the passport, as triples of
permutations.

The third entry is forced by the product-one relation, so each of these is a
`TauCeti.PermutationTriple`. -/
noncomputable def generatingTriples (P : PassportSpec n) :
    Finset (Perm (Fin n) × Perm (Fin n) × Perm (Fin n)) :=
  {p ∈ Finset.univ |
    p.2.2 * p.2.1 * p.1 = 1 ∧ Subgroup.closure {p.1, p.2.1} = P.G ∧
      ((p.1.fullCycleType, p.2.1.fullCycleType, p.2.2.fullCycleType) =
        (P.lam0, P.lam1, P.laminf))}

@[simp]
theorem mem_generatingTriples {P : PassportSpec n}
    {p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n)} :
    p ∈ P.generatingTriples ↔
      p.2.2 * p.2.1 * p.1 = 1 ∧ Subgroup.closure {p.1, p.2.1} = P.G ∧
        ((p.1.fullCycleType, p.2.1.fullCycleType, p.2.2.fullCycleType) =
          (P.lam0, P.lam1, P.laminf)) := by
  simp [generatingTriples]

/-- The generating triples of a passport, as product-one triples of permutations: the elimination
rule for `TauCeti.PassportSpec.generatingTriples`, and the source of the counting below. Its two
maps are computed by `TauCeti.PassportSpec.generatingTriplesEquiv_apply` and
`TauCeti.PassportSpec.generatingTriplesEquiv_symm_apply`. -/
noncomputable def generatingTriplesEquiv (P : PassportSpec n) :
    P.GeneratingTriple ≃ {p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n) //
      p ∈ P.generatingTriples} := by
  let toF : P.GeneratingTriple →
      {p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n) // p ∈ P.generatingTriples} :=
    fun g => ⟨(g.1.σ0, g.1.σ1, g.1.σinf), by
    refine mem_generatingTriples.2 ⟨g.1.product_eq_one, ?_, ?_⟩
    · rw [PermutationTriple.closure_pair_eq_monodromyGroup, g.2.monodromyGroup_eq]
    · have h := g.2.cycleData_eq
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simpa only [PermutationTriple.cycleData_σ0, Equiv.Perm.fullCycleType_def] using
          congrArg Prod.fst h
      · simpa only [PermutationTriple.cycleData_σ1, Equiv.Perm.fullCycleType_def] using
          congrArg (fun t => t.2.1) h
      · simpa only [PermutationTriple.cycleData_σinf, Equiv.Perm.fullCycleType_def] using
          congrArg (fun t => t.2.2) h⟩
  let invF : {p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n) //
      p ∈ P.generatingTriples} → P.GeneratingTriple :=
    fun q => ⟨PermutationTriple.ofTwo q.1.1 q.1.2.1, by
    rw [PassportSpec.isGeneratingTriple_iff]
    obtain ⟨hprod, hgen, hcyc⟩ := mem_generatingTriples.1 q.property
    have h0 : q.1.1.fullCycleType = P.lam0 := by simpa using congrArg Prod.fst hcyc
    have h1 : q.1.2.1.fullCycleType = P.lam1 := by simpa using congrArg (fun t => t.2.1) hcyc
    have hinf : q.1.2.2.fullCycleType = P.laminf := by simpa using congrArg (fun t => t.2.2) hcyc
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← PermutationTriple.closure_pair_eq_monodromyGroup, PermutationTriple.ofTwo_σ0,
        PermutationTriple.ofTwo_σ1]
      exact hgen
    · rw [PermutationTriple.cycleData_σ0, PermutationTriple.ofTwo_σ0,
        ← Equiv.Perm.fullCycleType_def]
      exact h0
    · rw [PermutationTriple.cycleData_σ1, PermutationTriple.ofTwo_σ1,
        ← Equiv.Perm.fullCycleType_def]
      exact h1
    · rw [PermutationTriple.cycleData_σinf,
        PermutationTriple.ofTwo_σinf_eq_of_product_eq_one q.1 hprod,
        ← Equiv.Perm.fullCycleType_def]
      exact hinf⟩
  refine { toFun := toF, invFun := invF, left_inv := ?_, right_inv := ?_ }
  · intro g
    apply Subtype.ext
    dsimp only [invF, toF]
    exact PermutationTriple.ext_of_two
      (t := PermutationTriple.ofTwo g.1.σ0 g.1.σ1) (t' := g.1) rfl rfl
  · intro q
    obtain ⟨hprod, -, -⟩ := mem_generatingTriples.1 q.property
    have h' : q.1.2.2 * (q.1.2.1 * q.1.1) = 1 := by simpa only [mul_assoc] using hprod
    apply Subtype.ext
    dsimp only [invF, toF]
    rw [PermutationTriple.ofTwo_σ0, PermutationTriple.ofTwo_σ1,
      PermutationTriple.ofTwo_σinf_eq_of_product_eq_one q.1 h']

/-- The triple of permutations that `TauCeti.PassportSpec.generatingTriplesEquiv` attaches to a
generating triple of `P` is the triple of its three components. -/
@[simp]
theorem generatingTriplesEquiv_apply (P : PassportSpec n) (g : P.GeneratingTriple) :
    (P.generatingTriplesEquiv g : Perm (Fin n) × Perm (Fin n) × Perm (Fin n)) =
      (g.1.σ0, g.1.σ1, g.1.σinf) := (rfl)

/-- The generating triple that `TauCeti.PassportSpec.generatingTriplesEquiv` attaches to a
product-one triple of `S_n` is the triple with the same first two components. -/
@[simp]
theorem generatingTriplesEquiv_symm_apply (P : PassportSpec n)
    (p : {q : Perm (Fin n) × Perm (Fin n) × Perm (Fin n) // q ∈ P.generatingTriples}) :
    (P.generatingTriplesEquiv.symm p : PermutationTriple n) =
      PermutationTriple.ofTwo p.1.1 p.1.2.1 := (rfl)

/-- The number of generating triples of a passport, computed on the generating triples of `S_n`. -/
theorem card_generatingTriples (P : PassportSpec n) :
    Nat.card (P.GeneratingTriple) = P.generatingTriples.card := by
  rw [Nat.card_congr (generatingTriplesEquiv P), Nat.card_eq_fintype_card, Fintype.card_coe]



end PassportSpec

end TauCeti
