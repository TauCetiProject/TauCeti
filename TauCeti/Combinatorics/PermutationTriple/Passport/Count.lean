/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import TauCeti.Algebra.Group.Subgroup.Finite
public import TauCeti.Combinatorics.PermutationTriple.Passport.Normalizer
public import TauCeti.GroupTheory.Perm.Centralizer

/-!
# Passport sizes from generating counts

A passport records a reference monodromy subgroup `P.G` together with the three ordered full cycle
types of the generating triples it contains. The number of isomorphism classes in the passport is
the number of `P.G`-generating triples of `S_n` with those cycle data, counted up to the action of
the normalizer of `P.G`. This file makes that count into a formula.

## The classes of a cycle type

One `S_n`-cycle type can meet several `G`-classes, and can meet none, so a count of the members of
`G` with a prescribed cycle type is a sum over `G`-classes rather than a single class size.
`TauCeti.PassportSpec.cycleTypeClasses` names that finite index set, and
`TauCeti.PassportSpec.mem_iUnion_cycleTypeClasses` identifies the union of those classes
with the elements of `P.G` of that cycle type.

## The generating triples of a passport

`TauCeti.PassportSpec.generatingTriples` is the set of product-one triples of permutations whose
first two entries generate `P.G` and whose three cycle types are those of `P`: the generating
triples of the passport, as triples of permutations. The product-one relation makes the third
entry a function of the first two
(`TauCeti.PassportSpec.ofTwo_σinf_of_productOne`), so
`TauCeti.PassportSpec.generatingTriplesEquiv` is the elimination rule identifying that finite set
with `TauCeti.PassportSpec.GeneratingTriple`, and
`TauCeti.PassportSpec.card_generatingTriples` reads the size of the passport's generating triples
off it. This is the finite set that the class-triple sum counts, and that the normalizer acts on.

## Orbits

Relabelling a generating triple of a passport must normalise the reference subgroup, so the
isomorphism classes of a passport are the orbits of the normalizer of `P.G` on these triples. An
element of the normalizer stabilising a generating triple centralises the group that the triple
generates (`TauCeti.Subgroup.eq_one_of_mem_centralizer_of_apply_eq`, and hence
`TauCeti.Subgroup.centralizer_stabilizer_eq_bot`), which is what makes every stabiliser equal
to the centralizer; Burnside's lemma then turns the count above into the passport size. The
centralizer on the right is itself bounded by the degree, by
`TauCeti.Subgroup.card_centralizer_dvd`.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5 (constellations, and the size of a passport).
* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, ANTS XIII,
  The Open Book Series 2 (2019), 375–392, §2 (the normalizer formulation of a passport).
-/

open Equiv MulAction

attribute [local instance] Subgroup.fintypeOfFinite

public section

namespace TauCeti

namespace PassportSpec

variable {n : ℕ}

/-! ## The conjugacy classes of a cycle type -/

open scoped Classical in
/-- The conjugacy classes of the reference subgroup `P.G` whose members have full cycle type `mu`.

One `S_n`-cycle type can meet several `G`-classes, and can meet none, so the elements of `P.G` of
a prescribed cycle type are counted by a sum over this index set rather than by one class size. -/
noncomputable def cycleTypeClasses (P : PassportSpec n) (mu : Multiset ℕ) :
    Finset (ConjClasses P.G) :=
  {C ∈ (Finset.univ : Finset (ConjClasses P.G)) | ∃ g : P.G, ConjClasses.mk g = C ∧
    (g : Equiv.Perm (Fin n)).fullCycleType = mu}

@[simp]
theorem mem_cycleTypeClasses {P : PassportSpec n} {mu : Multiset ℕ} {C : ConjClasses P.G} :
    C ∈ P.cycleTypeClasses mu ↔
      ∃ g : P.G, ConjClasses.mk g = C ∧ (g : Equiv.Perm (Fin n)).fullCycleType = mu := by
  simp [cycleTypeClasses]

/-- **The elements of `P.G` of full cycle type `mu` are the members of its classes of that type.**
One cycle type can meet several classes, and this says that the union of the classes recorded by
`TauCeti.PassportSpec.cycleTypeClasses` is exactly the finite set of elements of that type. -/
theorem mem_iUnion_cycleTypeClasses (P : PassportSpec n) (mu : Multiset ℕ) (g : P.G) :
    (g : Equiv.Perm (Fin n)).fullCycleType = mu ↔
      g ∈ ⋃ C ∈ P.cycleTypeClasses mu, C.carrier := by
  constructor
  · intro hg
    refine Set.mem_iUnion.2 ⟨ConjClasses.mk g, ?_⟩
    refine Set.mem_iUnion.2 ⟨mem_cycleTypeClasses.2 ⟨g, rfl, hg⟩, ?_⟩
    exact ConjClasses.mem_carrier_iff_mk_eq.2 rfl
  · intro hg
    have hg' : ∃ C : ConjClasses P.G, g ∈ ⋃ (_h : C ∈ P.cycleTypeClasses mu), C.carrier :=
      Set.mem_iUnion.1 hg
    obtain ⟨C, hgC⟩ := hg'
    have hgC' : ∃ (_h : C ∈ P.cycleTypeClasses mu), g ∈ C.carrier := Set.mem_iUnion.1 hgC
    obtain ⟨hCs, hgCs⟩ := hgC'
    obtain ⟨c, hmk, hc⟩ := mem_cycleTypeClasses.1 hCs
    have hgmk : ConjClasses.mk g = C := ConjClasses.mem_carrier_iff_mk_eq.1 hgCs
    have hconj : IsConj (g : Equiv.Perm (Fin n)) (c : Equiv.Perm (Fin n)) := by
      obtain ⟨u, hu⟩ := (ConjClasses.mk_eq_mk_iff_isConj.1 (hgmk.trans hmk.symm) : IsConj g c)
      rw [isConj_iff]
      refine ⟨(u : Equiv.Perm (Fin n)), ?_⟩
      have hval : (u : Equiv.Perm (Fin n)) * (g : Equiv.Perm (Fin n)) =
          (c : Equiv.Perm (Fin n)) * (u : Equiv.Perm (Fin n)) := by
        simpa only [Subgroup.coe_mul] using congrArg Subtype.val hu
      rw [hval, mul_assoc, mul_inv_cancel, mul_one]
    calc (g : Equiv.Perm (Fin n)).fullCycleType = (c : Equiv.Perm (Fin n)).fullCycleType :=
        Equiv.Perm.fullCycleType_eq_of_isConj hconj
      _ = mu := hc

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

/-- The third entry of a product-one triple of permutations is the third component of the
corresponding permutation triple, the product-one relation determining it. -/
theorem ofTwo_σinf_of_productOne (p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n))
    (h : p.2.2 * p.2.1 * p.1 = 1) : (PermutationTriple.ofTwo p.1 p.2.1).σinf = p.2.2 := by
  have h' : p.2.2 * (p.2.1 * p.1) = 1 := by simpa only [mul_assoc] using h
  rw [PermutationTriple.ofTwo_σinf, eq_inv_of_mul_eq_one_right h', inv_inv]

/-- The generating triples of a passport, as product-one triples of permutations: the elimination
rule for `TauCeti.PassportSpec.generatingTriples`, and the source of the counting below. -/
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
    · rw [PermutationTriple.cycleData_σinf, ofTwo_σinf_of_productOne q.1 hprod,
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
      ofTwo_σinf_of_productOne q.1 h']

/-- The number of generating triples of a passport, computed on the generating triples of `S_n`. -/
theorem card_generatingTriples (P : PassportSpec n) :
    Nat.card (P.GeneratingTriple) = P.generatingTriples.card := by
  rw [Nat.card_congr (generatingTriplesEquiv P), Nat.card_eq_fintype_card, Fintype.card_coe]



end PassportSpec

end TauCeti
