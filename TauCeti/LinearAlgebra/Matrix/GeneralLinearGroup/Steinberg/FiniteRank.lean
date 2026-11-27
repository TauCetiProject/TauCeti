/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.UniversalCentralExtension

/-!
# The finite-word presentation of the Steinberg group `Stₙ(R)`

For an associative unital ring `R` and a natural number `n`, this file presents the finite-rank
Steinberg group on root letters `x_{ij}(a)`, one for each triple `(i, j, a)` with `i ≠ j` in
`Fin n` and `a : R`, subject to the four relator families

* additivity: `x_{ij}(a) x_{ij}(b) = x_{ij}(a + b)`;
* distant commutation: `⁅x_{ij}(a), x_{kl}(b)⁆ = 1` for `j ≠ k` and `i ≠ l`;
* the forward commutator relation: `⁅x_{ij}(a), x_{jk}(b)⁆ = x_{ik}(a * b)` for pairwise distinct
  `i, j, k`;
* the reverse commutator relation: `⁅x_{ij}(a), x_{ki}(b)⁆ = x_{kj}(-(b * a))` for pairwise
  distinct `i, j, k`.

Nothing is imposed on opposite roots `x_{ij}(a)`, `x_{ji}(b)`. Commutators are
`⁅g, h⁆ = g h g⁻¹ h⁻¹`, and the orders `a * b` and `b * a` matter because `R` need not be
commutative.

The group `TauCeti.IndexedSteinbergGroup (Fin n) R` is presented without the reverse family. The
reverse relation follows from the forward one by exchanging the two inputs of the commutator and
inverting, so the two presentations define the same group: the generator-preserving homomorphisms
in both directions are mutually inverse (`TauCeti.Steinberg.FiniteRank.equivIndexedSteinbergGroup`),
for every `n`. This identification is compatible with coefficient homomorphisms, with index
embeddings `Fin m ↪ Fin n` and with the projection to `GLₙ(R)`, whose image is the elementary
subgroup `Eₙ(R)`. Through it, the Kervaire–Steinberg lifting theorem for
`TauCeti.IndexedSteinbergGroup` shows that, for `n ≥ 5`, every central extension of the
finite-word group `Stₙ(R)` splits by a unique homomorphic section. This does not say that the
kernel of `Stₙ(R) → Eₙ(R)` is central.

## Main definitions

* `TauCeti.Steinberg.Root`: root triples `(i, j, a)` with `i ≠ j`.
* `TauCeti.Steinberg.rootWord`: the free-group letter of a root triple.
* `TauCeti.Steinberg.relators`: the four relator families listed above.
* `TauCeti.Steinberg.FiniteRank`: the finite-word Steinberg group `Stₙ(R)`, presented by
  `TauCeti.Steinberg.relators`.
* `TauCeti.Steinberg.FiniteRank.x`: the generator `x_{ij}(a)`.
* `TauCeti.Steinberg.FiniteRank.lift`: the universal property, which only needs additivity,
  distant commutation and the forward commutator relation in the target.
* `TauCeti.Steinberg.FiniteRank.equivIndexedSteinbergGroup`: the isomorphism
  `Stₙ(R) ≃* TauCeti.IndexedSteinbergGroup (Fin n) R` fixing every generator `x_{ij}(a)`.
* `TauCeti.Steinberg.FiniteRank.map`, `TauCeti.Steinberg.FiniteRank.mapIndex`,
  `TauCeti.Steinberg.FiniteRank.toGL`: functoriality in the ring and along index embeddings, and
  the projection to `GLₙ(R)`.

## Main results

* `TauCeti.Steinberg.FiniteRank.x_add`, `TauCeti.Steinberg.FiniteRank.commute_x`,
  `TauCeti.Steinberg.FiniteRank.commutatorElement_x`,
  `TauCeti.Steinberg.FiniteRank.commutatorElement_x_reverse`: the defining relations.
* `TauCeti.Steinberg.FiniteRank.equivIndexedSteinbergGroup_map`,
  `TauCeti.Steinberg.FiniteRank.equivIndexedSteinbergGroup_mapIndex`,
  `TauCeti.IndexedSteinbergGroup.toGL_equivIndexedSteinbergGroup`: the identification commutes
  with coefficient homomorphisms, index embeddings and the projection to `GLₙ(R)`.
* `TauCeti.Steinberg.FiniteRank.toGL_map`, `TauCeti.Steinberg.FiniteRank.toGL_mapIndex`: the
  projection to `GLₙ(R)` intertwines `map f` with entrywise scalar change and `mapIndex e` with
  extension by the identity `e.extendGL R`.
* `TauCeti.Steinberg.FiniteRank.range_toGL`: the image of `Stₙ(R)` in `GLₙ(R)` is `Eₙ(R)`.
* `TauCeti.Steinberg.FiniteRank.existsUnique_comp_eq_of_five_le`,
  `TauCeti.Steinberg.FiniteRank.isUniversalCentralExtension_id_of_five_le`: for `n ≥ 5`, every
  homomorphism out of `Stₙ(R)` lifts uniquely through every central extension of its target, so
  every central extension of `Stₙ(R)` has a unique homomorphic section.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definition 5.1 and Theorem 5.5.1.
-/

public section

noncomputable section

open scoped commutatorElement

namespace TauCeti

namespace Steinberg

variable (R : Type*) [Ring R] (n : ℕ)

/-- Root triples `(i, j, a)` with distinct indices `i ≠ j` in `Fin n` and a coefficient `a : R`:
the letters of the finite-word Steinberg presentation. -/
abbrev Root : Type _ :=
  {g : Fin n × Fin n × R // g.1 ≠ g.2.1}

variable {R n}

/-- The free-group letter `x_{ij}(a)` of the root triple `(i, j, a)`. -/
def rootWord (i j : Fin n) (hij : i ≠ j) (a : R) : FreeGroup (Root R n) :=
  FreeGroup.of ⟨(i, j, a), hij⟩

variable (R n)

/-- The relators of the finite-word Steinberg presentation: additivity
`x_{ij}(a) x_{ij}(b) x_{ij}(a + b)⁻¹`, distant commutators `⁅x_{ij}(a), x_{kl}(b)⁆` with `j ≠ k`
and `i ≠ l`, the forward commutator relators `⁅x_{ij}(a), x_{jk}(b)⁆ x_{ik}(a * b)⁻¹` and the
reverse commutator relators `⁅x_{ij}(a), x_{ki}(b)⁆ x_{kj}(-b * a)⁻¹`. No relator involves a pair
of opposite roots. -/
def relators : Set (FreeGroup (Root R n)) :=
  {w | (∃ (i j : Fin n) (hij : i ≠ j) (a b : R),
      w = rootWord i j hij a * rootWord i j hij b * (rootWord i j hij (a + b))⁻¹) ∨
    (∃ (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) (a b : R),
      j ≠ k ∧ i ≠ l ∧ w = ⁅rootWord i j hij a, rootWord k l hkl b⁆) ∨
    (∃ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      w = ⁅rootWord i j hij a, rootWord j k hjk b⁆ * (rootWord i k hik (a * b))⁻¹) ∨
    (∃ (i j k : Fin n) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : R),
      w = ⁅rootWord i j hij a, rootWord k i hki b⁆ * (rootWord k j hkj (-b * a))⁻¹)}

variable {R n} in
/-- Membership in `TauCeti.Steinberg.relators`: a word is a relator iff it is an additivity,
distant-commutation, forward commutator or reverse commutator relator. -/
theorem mem_relators_iff {w : FreeGroup (Root R n)} :
    w ∈ relators R n ↔
      (∃ (i j : Fin n) (hij : i ≠ j) (a b : R),
        w = rootWord i j hij a * rootWord i j hij b * (rootWord i j hij (a + b))⁻¹) ∨
      (∃ (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) (a b : R),
        j ≠ k ∧ i ≠ l ∧ w = ⁅rootWord i j hij a, rootWord k l hkl b⁆) ∨
      (∃ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
        w = ⁅rootWord i j hij a, rootWord j k hjk b⁆ * (rootWord i k hik (a * b))⁻¹) ∨
      (∃ (i j k : Fin n) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : R),
        w = ⁅rootWord i j hij a, rootWord k i hki b⁆ * (rootWord k j hkj (-b * a))⁻¹) :=
  Iff.rfl

/-- The **finite-word Steinberg group** `Stₙ(R)`: the group presented by the root letters
`x_{ij}(a)` (`i ≠ j` in `Fin n`, `a : R`) and `TauCeti.Steinberg.relators R n`. It is isomorphic to
`TauCeti.IndexedSteinbergGroup (Fin n) R` by a generator-preserving isomorphism
(`TauCeti.Steinberg.FiniteRank.equivIndexedSteinbergGroup`). -/
abbrev FiniteRank : Type _ :=
  PresentedGroup (relators R n)

namespace FiniteRank

variable {R n} {S T : Type*} [Ring S] [Ring T]

/-- The generator `x_{ij}(a)` of `Stₙ(R)`, the class of the root letter `rootWord i j hij a`. -/
def x {i j : Fin n} (hij : i ≠ j) (a : R) : FiniteRank R n :=
  PresentedGroup.of ⟨(i, j, a), hij⟩

/-- Each presentation generator `PresentedGroup.of g` is the generator `x` of its root triple. -/
@[simp]
theorem of_eq_x (g : Root R n) : (PresentedGroup.of g : FiniteRank R n) = x g.property g.val.2.2 :=
  (rfl)

/-- The class of the root letter `rootWord i j hij a` is the generator `x_{ij}(a)`. -/
@[simp]
theorem mk_rootWord {i j : Fin n} (hij : i ≠ j) (a : R) :
    PresentedGroup.mk (relators R n) (rootWord i j hij a) = x hij a :=
  (rfl)

private theorem mk_of (g : Root R n) :
    PresentedGroup.mk (relators R n) (FreeGroup.of g) = x g.property g.val.2.2 :=
  (rfl)

/-! ### The defining relations -/

/-- Additivity of the generators in the coefficient: `x_{ij}(a + b) = x_{ij}(a) x_{ij}(b)`. -/
@[simp]
theorem x_add {i j : Fin n} (hij : i ≠ j) (a b : R) : x hij (a + b) = x hij a * x hij b := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators R n)
    (Or.inl ⟨i, j, hij, a, b, rfl⟩)
  simpa only [map_mul, mk_rootWord] using h.symm

/-- Generators at non-chaining index pairs (`j ≠ k` and `l ≠ i`) commute. -/
theorem commute_x {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (a b : R) : Commute (x hij a) (x hkl b) := by
  have h := PresentedGroup.one_of_mem (rels := relators R n)
    (Or.inr (Or.inl ⟨i, j, k, l, hij, hkl, a, b, hjk, hli.symm, rfl⟩))
  rwa [map_commutatorElement, mk_rootWord, mk_rootWord, commutatorElement_eq_one_iff_commute] at h

/-- **The forward commutator relation**: `⁅x_{ij}(a), x_{jk}(b)⁆ = x_{ik}(a * b)` for pairwise
distinct `i, j, k`. -/
theorem commutatorElement_x {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅x hij a, x hjk b⁆ = x hik (a * b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators R n)
    (Or.inr (Or.inr (Or.inl ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩)))
  rwa [map_commutatorElement, mk_rootWord, mk_rootWord, mk_rootWord] at h

/-- **The reverse commutator relation**: `⁅x_{ij}(a), x_{ki}(b)⁆ = x_{kj}(-(b * a))` for pairwise
distinct `i, j, k`. -/
theorem commutatorElement_x_reverse {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (a b : R) : ⁅x hij a, x hki b⁆ = x hkj (-(b * a)) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relators R n)
    (Or.inr (Or.inr (Or.inr ⟨i, j, k, hij, hki, hkj, a, b, rfl⟩)))
  rwa [map_commutatorElement, mk_rootWord, mk_rootWord, mk_rootWord, neg_mul] at h

/-- The generator with coefficient zero is the identity. -/
@[simp]
theorem x_zero {i j : Fin n} (hij : i ≠ j) : x hij (0 : R) = 1 :=
  mul_left_cancel (a := x hij 0) (by rw [← x_add, add_zero, mul_one])

/-- Inverting a generator negates its coefficient. -/
@[simp]
theorem x_inv {i j : Fin n} (hij : i ≠ j) (a : R) : (x hij a)⁻¹ = x hij (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [← x_add, add_neg_cancel, x_zero])

/-! ### Generation and the universal property -/

/-- Generator induction on `Stₙ(R)`: a predicate holding at `1` and at every generator
`x_{ij}(a)`, and closed under multiplication, holds for all elements (inverses of generators are
generators by `x_inv`). -/
@[elab_as_elim]
theorem induction_on {motive : FiniteRank R n → Prop} (z : FiniteRank R n) (one : motive 1)
    (x : ∀ ⦃i j : Fin n⦄ (hij : i ≠ j) (a : R), motive (FiniteRank.x hij a))
    (mul : ∀ a b, motive a → motive b → motive (a * b)) : motive z := by
  induction z using PresentedGroup.induction_on with | H w =>
  induction w using FreeGroup.induction_on with
  | one => simpa only [map_one] using one
  | of g => simpa only [mk_of] using x g.property g.val.2.2
  | inv_of g _ => simpa only [map_inv, mk_of, x_inv] using x g.property (-g.val.2.2)
  | mul w₁ w₂ ih₁ ih₂ => simpa only [map_mul] using mul _ _ ih₁ ih₂

/-- Two homomorphisms out of `Stₙ(R)` agree when they agree on every generator `x_{ij}(a)`. -/
@[ext]
theorem hom_ext {G : Type*} [MulOneClass G] {φ ψ : FiniteRank R n →* G}
    (h : ∀ ⦃i j : Fin n⦄ (hij : i ≠ j) (a : R), φ (x hij a) = ψ (x hij a)) : φ = ψ := by
  refine MonoidHom.ext fun z ↦ ?_
  induction z using FiniteRank.induction_on with
  | one => rw [map_one, map_one]
  | x hij a => exact h hij a
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]

private theorem lift_rels {G : Type*} [Group G] (f : ∀ ⦃i j : Fin n⦄, i ≠ j → R → G)
    (hadd : ∀ ⦃i j : Fin n⦄ (hij : i ≠ j) (a b : R), f hij (a + b) = f hij a * f hij b)
    (hcomm : ∀ ⦃i j k l : Fin n⦄ (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      ∀ a b : R, Commute (f hij a) (f hkl b))
    (hchain : ∀ ⦃i j k : Fin n⦄ (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f hij a, f hjk b⁆ = f hik (a * b)) :
    ∀ w ∈ relators R n, FreeGroup.lift (fun g : Root R n ↦ f g.property g.val.2.2) w = 1 := by
  rintro w (⟨i, j, hij, a, b, rfl⟩ | ⟨i, j, k, l, hij, hkl, a, b, hjk, hil, rfl⟩ |
    ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩ | ⟨i, j, k, hij, hki, hkj, a, b, rfl⟩) <;>
    simp only [rootWord, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
  · rw [hadd, mul_inv_cancel]
  · exact commutatorElement_eq_one_iff_commute.mpr (hcomm hij hkl hjk hil.symm a b)
  · rw [hchain hij hjk hik, mul_inv_cancel]
  · -- The reverse relation is the inverse of the forward relation with the inputs exchanged.
    have h0 : f hkj 0 = 1 := by simpa using (hadd hkj 0 0).symm
    rw [← commutatorElement_inv, hchain hki hij hkj, ← mul_inv_rev, ← hadd, neg_mul,
      neg_add_cancel, h0, inv_one]

/-- **Universal property of `Stₙ(R)`**: a family of elements `f hij a` of a group satisfying
additivity, distant commutation and the forward commutator relation extends to a homomorphism
`Stₙ(R) →* G` sending `x_{ij}(a)` to `f hij a`. The reverse commutator relation holds
automatically in the target, so it is not a hypothesis. -/
def lift {G : Type*} [Group G] (f : ∀ ⦃i j : Fin n⦄, i ≠ j → R → G)
    (hadd : ∀ ⦃i j : Fin n⦄ (hij : i ≠ j) (a b : R), f hij (a + b) = f hij a * f hij b)
    (hcomm : ∀ ⦃i j k l : Fin n⦄ (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      ∀ a b : R, Commute (f hij a) (f hkl b))
    (hchain : ∀ ⦃i j k : Fin n⦄ (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f hij a, f hjk b⁆ = f hik (a * b)) :
    FiniteRank R n →* G :=
  PresentedGroup.toGroup (lift_rels f hadd hcomm hchain)

@[simp]
theorem lift_x {G : Type*} [Group G] (f : ∀ ⦃i j : Fin n⦄, i ≠ j → R → G)
    (hadd : ∀ ⦃i j : Fin n⦄ (hij : i ≠ j) (a b : R), f hij (a + b) = f hij a * f hij b)
    (hcomm : ∀ ⦃i j k l : Fin n⦄ (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      ∀ a b : R, Commute (f hij a) (f hkl b))
    (hchain : ∀ ⦃i j k : Fin n⦄ (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f hij a, f hjk b⁆ = f hik (a * b))
    {i j : Fin n} (hij : i ≠ j) (a : R) :
    lift f hadd hcomm hchain (x hij a) = f hij a :=
  PresentedGroup.toGroup.of _

/-! ### Identification with `IndexedSteinbergGroup (Fin n) R` -/

/-- **The finite-word presentation is the Steinberg group `Stₙ(R)`**: the generator-preserving
homomorphisms between `Stₙ(R)` and `TauCeti.IndexedSteinbergGroup (Fin n) R`, sending `x_{ij}(a)`
to `x_{ij}(a)` in both directions, are mutually inverse. In particular the reverse commutator
relators are consequences of the other relators. -/
def equivIndexedSteinbergGroup : FiniteRank R n ≃* IndexedSteinbergGroup (Fin n) R :=
  MonoidHom.toMulEquiv
    (lift (fun _ _ hij a ↦ IndexedSteinbergGroup.x hij a) (fun _ _ ↦ IndexedSteinbergGroup.x_add)
      (fun _ _ _ _ ↦ IndexedSteinbergGroup.commute_x)
      (fun _ _ _ ↦ IndexedSteinbergGroup.commutatorElement_x))
    (IndexedSteinbergGroup.lift (fun _ _ hij a ↦ x hij a) (fun _ _ ↦ x_add)
      (fun _ _ _ _ ↦ commute_x) (fun _ _ _ ↦ commutatorElement_x))
    (by ext; simp) (by ext; simp)

@[simp]
theorem equivIndexedSteinbergGroup_x {i j : Fin n} (hij : i ≠ j) (a : R) :
    equivIndexedSteinbergGroup (x hij a) = IndexedSteinbergGroup.x hij a := by
  simp [equivIndexedSteinbergGroup]

@[simp]
theorem equivIndexedSteinbergGroup_symm_x {i j : Fin n} (hij : i ≠ j) (a : R) :
    equivIndexedSteinbergGroup.symm (IndexedSteinbergGroup.x hij a) = x hij a := by
  simp [equivIndexedSteinbergGroup]

/-! ### Functoriality in the ring and along index embeddings -/

/-- The homomorphism `Stₙ(R) →* Stₙ(S)` induced by a ring homomorphism `f : R →+* S`, sending
`x_{ij}(a)` to `x_{ij}(f a)`. -/
def map (f : R →+* S) : FiniteRank R n →* FiniteRank S n :=
  lift (fun _ _ hij a ↦ x hij (f a)) (fun _ _ hij a b ↦ by rw [map_add, x_add])
    (fun _ _ _ _ hij hkl hjk hli a b ↦ commute_x hij hkl hjk hli (f a) (f b))
    (fun _ _ _ hij hjk hik a b ↦ by rw [commutatorElement_x hij hjk hik, map_mul])

@[simp]
theorem map_x (f : R →+* S) {i j : Fin n} (hij : i ≠ j) (a : R) :
    map f (x hij a) = x hij (f a) :=
  lift_x _ _ _ _ hij a

@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (FiniteRank R n) := by
  ext
  simp

/-- `TauCeti.Steinberg.FiniteRank.map` is functorial in ring homomorphisms. -/
theorem map_comp (g : S →+* T) (f : R →+* S) :
    map (n := n) (g.comp f) = (map g).comp (map f) := by
  ext
  simp

/-- Elementwise form of `TauCeti.Steinberg.FiniteRank.map_comp`. -/
@[simp]
theorem map_map (g : S →+* T) (f : R →+* S) (z : FiniteRank R n) :
    map g (map f z) = map (g.comp f) z :=
  DFunLike.congr_fun (map_comp g f).symm z

/-- The identification with `TauCeti.IndexedSteinbergGroup (Fin n)` commutes with coefficient
homomorphisms. -/
@[simp]
theorem equivIndexedSteinbergGroup_map (f : R →+* S) (z : FiniteRank R n) :
    equivIndexedSteinbergGroup (map f z) =
      IndexedSteinbergGroup.map f (equivIndexedSteinbergGroup z) := by
  induction z using FiniteRank.induction_on with
  | one => simp
  | x hij a => simp
  | mul a b ha hb => simp [ha, hb]

/-- The homomorphism `Stₘ(R) →* Stₙ(R)` induced by an embedding of indices `e : Fin m ↪ Fin n`,
sending `x_{ij}(a)` to `x_{e(i), e(j)}(a)`. -/
def mapIndex {m : ℕ} (e : Fin m ↪ Fin n) : FiniteRank R m →* FiniteRank R n :=
  lift (fun _ _ hij a ↦ x (e.injective.ne hij) a) (fun _ _ hij ↦ x_add (e.injective.ne hij))
    (fun _ _ _ _ hij hkl hjk hli ↦
      commute_x (e.injective.ne hij) (e.injective.ne hkl) (e.injective.ne hjk)
        (e.injective.ne hli))
    (fun _ _ _ hij hjk hik ↦
      commutatorElement_x (e.injective.ne hij) (e.injective.ne hjk) (e.injective.ne hik))

@[simp]
theorem mapIndex_x {m : ℕ} (e : Fin m ↪ Fin n) {i j : Fin m} (hij : i ≠ j) (a : R) :
    mapIndex e (x hij a) = x (e.injective.ne hij) a :=
  lift_x _ _ _ _ hij a

@[simp]
theorem mapIndex_refl :
    mapIndex (Function.Embedding.refl (Fin n)) = MonoidHom.id (FiniteRank R n) := by
  ext
  simp

/-- `TauCeti.Steinberg.FiniteRank.mapIndex` is functorial in index embeddings. -/
theorem mapIndex_trans {l m : ℕ} (e₁ : Fin l ↪ Fin m) (e₂ : Fin m ↪ Fin n) :
    mapIndex (R := R) (e₁.trans e₂) = (mapIndex e₂).comp (mapIndex e₁) := by
  ext
  simp

/-- Elementwise form of `TauCeti.Steinberg.FiniteRank.mapIndex_trans`. -/
@[simp]
theorem mapIndex_mapIndex {l m : ℕ} (e₁ : Fin l ↪ Fin m) (e₂ : Fin m ↪ Fin n)
    (z : FiniteRank R l) : mapIndex e₂ (mapIndex e₁ z) = mapIndex (e₁.trans e₂) z :=
  DFunLike.congr_fun (mapIndex_trans e₁ e₂).symm z

/-- The identification with `TauCeti.IndexedSteinbergGroup (Fin n)` commutes with the maps
induced by index embeddings. -/
@[simp]
theorem equivIndexedSteinbergGroup_mapIndex {m : ℕ} (e : Fin m ↪ Fin n) (z : FiniteRank R m) :
    equivIndexedSteinbergGroup (mapIndex e z) =
      IndexedSteinbergGroup.mapIndex e (equivIndexedSteinbergGroup z) := by
  induction z using FiniteRank.induction_on with
  | one => simp
  | x hij a => simp
  | mul a b ha hb => simp [ha, hb]

/-! ### Projection to `GLₙ(R)` -/

/-- The canonical homomorphism `Stₙ(R) →* GLₙ(R)` sending `x_{ij}(a)` to the elementary
transvection `TauCeti.transvectionUnit hij a = 1 + a E_{ij}`. -/
def toGL : FiniteRank R n →* GL (Fin n) R :=
  lift (fun _ _ hij a ↦ transvectionUnit hij a) (fun _ _ ↦ transvectionUnit_add)
    (fun _ _ _ _ ↦ commute_transvectionUnit) (fun _ _ _ ↦ commutatorElement_transvectionUnit)

@[simp]
theorem toGL_x {i j : Fin n} (hij : i ≠ j) (a : R) : toGL (x hij a) = transvectionUnit hij a :=
  lift_x _ _ _ _ hij a

/-- The projection `Stₙ(R) →* GLₙ(R)` intertwines `TauCeti.Steinberg.FiniteRank.map` with entrywise
scalar change. -/
theorem toGL_comp_map (f : R →+* S) :
    (toGL (R := S) (n := n)).comp (map f) =
      (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom).comp toGL := by
  ext i j hij a
  simp [RingHom.unitsMap_mapMatrix_transvectionUnit]

/-- The projection `Stₙ(R) →* GLₙ(R)` is natural in ring homomorphisms. -/
@[simp]
theorem toGL_map (f : R →+* S) (z : FiniteRank R n) :
    toGL (map f z) = Units.map (f.mapMatrix (m := Fin n)).toMonoidHom (toGL z) :=
  DFunLike.congr_fun (toGL_comp_map f) z

/-- Along an index embedding `e : Fin m ↪ Fin n`, the projection to `GLₙ(R)` intertwines
`TauCeti.Steinberg.FiniteRank.mapIndex e` with extension by the identity `e.extendGL R`. -/
theorem toGL_comp_mapIndex {m : ℕ} (e : Fin m ↪ Fin n) :
    (toGL (R := R) (n := n)).comp (mapIndex e) = (e.extendGL R).comp toGL :=
  hom_ext fun i j hij a ↦ by simp

/-- Along an index embedding `e : Fin m ↪ Fin n`, `toGL` sends the image of `z` under
`mapIndex e` to the extension of `toGL z` by the identity. -/
theorem toGL_mapIndex {m : ℕ} (e : Fin m ↪ Fin n) (z : FiniteRank R m) :
    toGL (mapIndex e z) = e.extendGL R (toGL z) :=
  DFunLike.congr_fun (toGL_comp_mapIndex e) z

end FiniteRank

end Steinberg

namespace IndexedSteinbergGroup

open Steinberg

variable {R : Type*} [Ring R] {n : ℕ}

/-- The identification of `Stₙ(R)` with `TauCeti.IndexedSteinbergGroup (Fin n) R` commutes with
the projections to `GLₙ(R)`. -/
@[simp]
theorem toGL_equivIndexedSteinbergGroup (z : FiniteRank R n) :
    toGL (FiniteRank.equivIndexedSteinbergGroup z) = FiniteRank.toGL z := by
  induction z using FiniteRank.induction_on with
  | one => simp
  | x hij a => simp
  | mul a b ha hb => simp [ha, hb]

end IndexedSteinbergGroup

namespace Steinberg

namespace FiniteRank

variable {R : Type*} [Ring R] {n : ℕ}

/-- The image of `Stₙ(R)` in `GLₙ(R)` is the elementary subgroup `Eₙ(R)`. -/
theorem range_toGL : (toGL (R := R) (n := n)).range = elementarySubgroup (Fin n) R := by
  rw [← IndexedSteinbergGroup.range_toGL]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨equivIndexedSteinbergGroup z, IndexedSteinbergGroup.toGL_equivIndexedSteinbergGroup z⟩
  · rintro ⟨y, rfl⟩
    refine ⟨equivIndexedSteinbergGroup.symm y, ?_⟩
    rw [← IndexedSteinbergGroup.toGL_equivIndexedSteinbergGroup, MulEquiv.apply_symm_apply]

/-! ### Central extensions in rank at least five -/

section Universal

universe v

variable {G E : Type*} [Group G] [Group E]

/-- **Lifting through central extensions in rank at least five.** For `n ≥ 5`, every homomorphism
`φ : Stₙ(R) →* G` lifts uniquely along every homomorphism `q : E →* G` whose range contains that of
`φ` and whose kernel is central. -/
theorem existsUnique_comp_eq_of_five_le (hn : 5 ≤ n) {φ : FiniteRank R n →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E) :
    ∃! ψ : FiniteRank R n →* E, q.comp ψ = φ := by
  -- Transport the lifting problem to `IndexedSteinbergGroup (Fin n) R` along the identification.
  let e : FiniteRank R n ≃* IndexedSteinbergGroup (Fin n) R := equivIndexedSteinbergGroup
  have hrange : (φ.comp (e.symm : IndexedSteinbergGroup (Fin n) R →* _)).range ≤ q.range := by
    rwa [MonoidHom.range_comp, MulEquiv.range_eq_top, ← MonoidHom.range_eq_map]
  obtain ⟨ψ, hψ, huniq⟩ := IndexedSteinbergGroup.existsUnique_comp_eq_of_five_le_card
    (by simpa using hn) hrange hq_ker
  refine ⟨ψ.comp e, MonoidHom.ext fun z ↦ ?_, fun χ (hχ : q.comp χ = φ) ↦ MonoidHom.ext fun z ↦ ?_⟩
  · simpa using DFunLike.congr_fun hψ (e z)
  · have h := huniq (χ.comp e.symm) (by rw [← hχ, MonoidHom.comp_assoc])
    simpa using DFunLike.congr_fun h (e z)

variable (R) in
/-- **Central extensions of `Stₙ(R)` split for `n ≥ 5`.** The identity of `Stₙ(R)` is a universal
central extension (in any universe `v`): every central extension `q : Y →* Stₙ(R)` has a unique
homomorphic section `σ` with `q ∘ σ = id`. This does not assert that the kernel of
`Stₙ(R) →* Eₙ(R)` is central. -/
theorem isUniversalCentralExtension_id_of_five_le (hn : 5 ≤ n) :
    (MonoidHom.id (FiniteRank R n)).IsUniversalCentralExtension.{v} where
  isCentralExtension := ⟨Function.surjective_id, by simp⟩
  existsUnique_comp_eq _ _ _ hq := existsUnique_comp_eq_of_five_le hn
    (MonoidHom.range_eq_top.mpr hq.surjective ▸ le_top) hq.ker_le_center

end Universal

end FiniteRank

end Steinberg

end TauCeti
