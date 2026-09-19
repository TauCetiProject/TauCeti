/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# The Frobenius kernel, its size, and the free action of the complement on it

The **Frobenius kernel** of a subgroup `H` of `G` is the identity together with the elements of `G`
lying in no conjugate of `H`,

`frobeniusKernel H = {1} ∪ (G ∖ ⋃_g g H g⁻¹)`.

That union of conjugates is Mathlib's `Group.conjugatesOfSet (H : Set G)`, the set of elements
conjugate to an element of `H`.

Frobenius's theorem says that when `G` is finite and `H` is a Frobenius complement — proper,
nontrivial, and meeting each of its distinct conjugates trivially
(`TauCeti.IsFrobeniusComplement`) — this set is a normal subgroup, and that is not elementary: the
known proofs go through the character theory of `G`. What *is* elementary, and is what this file
proves, is everything about the kernel except its closure under multiplication: it contains the
identity, it is closed under inversion and under conjugation, it meets every conjugate of `H` only
in the identity, and — the counting statement the divisibility results below rest on — for a
finite `G` it has exactly `|G : H|` elements.

The count is the inclusion-exclusion that gives Frobenius's theorem its shape, and it is really a
statement about a trivial-intersection *set* `S` for `H` (`TauCeti.IsTISet`): the conjugates
`g S g⁻¹` are pairwise disjoint for distinct cosets `g H` and depend only on the coset, so the
elements they cover are indexed bijectively by the pairs (a coset of `H`, an element of `S`) and
number `|G : H| · |S|`. That is `TauCeti.IsTISet.ncard_conjugatesOfSet`, proved alongside
`TauCeti.IsTISet` itself in `TauCeti/GroupTheory/TrivialIntersection.lean`. The complement of the
kernel is the set of conjugates of the nonidentity elements of `H`, which for a
trivial-intersection subgroup is such a set (`TauCeti.IsTISubgroup.isTISet_diff_one`), and the
count specializes to `TauCeti.IsTISubgroup.ncard_compl_frobeniusKernel`, the `Set.ncard` identity
`((frobeniusKernel H)ᶜ).ncard = |G : H| · (|H| - 1)`. That identity holds for any `G`, finite or
not, but for an infinite `G` it does not in general represent a count of elements: an infinite side
reads as the junk value `0` that `Set.ncard` and `Subgroup.index` take on infinite arguments. A
degenerate case can of course still be a genuine count — for `H = ⊥` the kernel is everything and
its complement is honestly empty — but nothing outside the finite case says so. For a finite `G`
there are indeed `|G : H| · (|H| - 1)` elements outside the kernel, and the remaining
`|G| - |G : H| · (|H| - 1) = |G : H|` elements are the kernel, and the rest is arithmetic.

Together with normality the count is exactly what makes the kernel a *complement*:
`TauCeti.IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel` says that, for a finite `G`, a
subgroup whose carrier is the Frobenius kernel is automatically a complement to `H`, so once
Frobenius's theorem supplies the subgroup, the semidirect decomposition `G = N ⋊ H` is free.
Nothing here asserts that a subgroup with that carrier exists.

The count has an arithmetic refinement, proved here as well: the conjugation action of `H` on the
nonidentity part of the kernel is **free** (`TauCeti.IsTISubgroup.stabilizer_eq_bot`, with
`TauCeti.IsTISubgroup.isCancelSMul` its typeclass form), and freeness against the `|G : H| - 1`
nonidentity kernel elements gives

`|H| ∣ |G : H| - 1`

(`TauCeti.IsTISubgroup.card_dvd_index_sub_one`), whence also `|H|` and `|G : H|` are coprime
(`TauCeti.IsTISubgroup.coprime_card_index`) and, for a proper `H`, `|H| < |G : H|`
(`TauCeti.IsTISubgroup.card_lt_index`).  When Frobenius's theorem supplies the kernel as a
subgroup `N` of order `|G : H|`, these are the classical statements that `|H|` divides `|N| - 1`
and that a Frobenius complement and a Frobenius kernel have coprime orders.  Freeness has a second
reading, bounding the centralizers the other way round: the centralizer of a nonidentity element
of the kernel is contained in the kernel
(`TauCeti.IsTISubgroup.centralizer_singleton_subset_frobeniusKernel`).

The last section runs the recognition in the other direction.  A semidirect decomposition
`G = N ⋊ H` in which `H` acts on `N` with no nonidentity fixed points forces `H` to be a
trivial-intersection subgroup (`TauCeti.isTISubgroup_of_isComplement'_of_fixedPointFree`), and
then the given `N` is already the Frobenius kernel
(`TauCeti.IsTISubgroup.coe_eq_frobeniusKernel_of_isComplement'`) -- the inclusion
`N ⊆ frobeniusKernel H` needs only normality and disjointness, and the count above turns it into
an equality.  Nothing there is character theory: it is what a concrete Frobenius group is checked
against once Frobenius's theorem has produced its kernel abstractly.

No subgroup hypothesis beyond `TauCeti.IsTISubgroup` is needed for the count once `G` is finite, and
the two degenerate cases are honest instances rather than exclusions:
`frobeniusKernel ⊤ = {1}` has one element and `⊤` has index `1`, while `frobeniusKernel ⊥` is
everything and `⊥` has index `|G|`.

## Main definitions

* `TauCeti.frobeniusKernel`: the identity together with the elements in no conjugate of `H`.

## Main results

* `TauCeti.mem_frobeniusKernel`: membership, elementwise.
* `TauCeti.inv_mem_frobeniusKernel_iff` and `TauCeti.conj_mem_frobeniusKernel_iff`: the kernel is
  closed under inversion and invariant under conjugation, for every subgroup `H`.
* `TauCeti.frobeniusKernel_inter_conj_smul_eq_singleton` and
  `TauCeti.frobeniusKernel_inter_eq_singleton`: the kernel meets every conjugate of `H`, and in
  particular `H` itself, exactly in the identity.
* `TauCeti.IsTISubgroup.ncard_compl_frobeniusKernel`: the `Set.ncard` identity
  `((frobeniusKernel H)ᶜ).ncard = |G : H| · (|H| - 1)`, which for a finite `G` counts the elements
  *outside* the kernel — the nonidentity elements of the conjugates of `H`, each counted once — and
  for an infinite `G` reads `0 = 0`.
* `TauCeti.IsTISubgroup.ncard_frobeniusKernel` and
  `TauCeti.IsTISubgroup.natCard_frobeniusKernel`: **for a finite `G` the kernel has `|G : H|`
  elements.**
* `TauCeti.IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel`: for a finite `G`, a subgroup
  whose carrier is the kernel is a complement to `H`.
* `TauCeti.IsTISubgroup.conj_ne_self_of_mem_frobeniusKernel`,
  `TauCeti.IsTISubgroup.stabilizer_eq_bot` and `TauCeti.IsTISubgroup.isCancelSMul`: a nonidentity
  element of `H` commutes with no nonidentity element of the kernel, so the conjugation action of
  `H` on the nonidentity part of the kernel is **free**.
* `TauCeti.IsTISubgroup.mem_frobeniusKernel_of_conj_eq_self` and
  `TauCeti.IsTISubgroup.centralizer_singleton_subset_frobeniusKernel`: the centralizer of a
  nonidentity element of the kernel is contained in the kernel.
* `TauCeti.IsTISubgroup.card_dvd_index_sub_one`: **`|H| ∣ |G : H| - 1`** for a finite `G`, with
  `TauCeti.IsTISubgroup.coprime_card_index` the coprimality and
  `TauCeti.IsTISubgroup.card_lt_index` the strict inequality `|H| < |G : H|` it implies.
* `TauCeti.isTISubgroup_of_isComplement'_of_fixedPointFree`: **a complement to a normal subgroup
  on which it acts without nonidentity fixed points is a trivial-intersection subgroup**, with
  `TauCeti.isFrobeniusComplement_of_isComplement'_of_fixedPointFree` its bundled form for a proper
  nontrivial `H`.
* `TauCeti.coe_subset_frobeniusKernel` and
  `TauCeti.IsTISubgroup.coe_eq_frobeniusKernel_of_isComplement'`: **a normal complement meeting
  `H` trivially lies in the Frobenius kernel, and for a finite `G` it *is* the Frobenius
  kernel** when `H` is a trivial-intersection subgroup.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 7, Section 7B.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 8 (`frobeniusKernel`, "a set of size `|G : H|`", and `frobeniusKernel_isComplement'`).
-/

public section

namespace TauCeti

open scoped Pointwise

variable {G : Type*} [Group G] {H : Subgroup G}

/-- **The Frobenius kernel** of a subgroup: the identity together with the elements of `G` lying in
no conjugate of `H`, the conjugates being collected by `Group.conjugatesOfSet`.  For a Frobenius
complement `H` of a finite group this set is a normal subgroup of `G`, but that is Frobenius's
theorem and needs character theory; as a *set* it is available for any `H`, and
`TauCeti.mem_frobeniusKernel` is the elementwise description everything below uses. -/
def frobeniusKernel (H : Subgroup G) : Set G :=
  {1} ∪ (Group.conjugatesOfSet (H : Set G))ᶜ

/-- The Frobenius kernel is the identity together with the complement of the set of conjugates of
elements of `H`, by definition. -/
theorem frobeniusKernel_def (H : Subgroup G) :
    frobeniusKernel H = {1} ∪ (Group.conjugatesOfSet (H : Set G))ᶜ := (rfl)

/-- **Membership in the Frobenius kernel**: an element is the identity, or no conjugate of it lands
in `H`. -/
theorem mem_frobeniusKernel {y : G} :
    y ∈ frobeniusKernel H ↔ y = 1 ∨ ∀ x : G, x⁻¹ * y * x ∉ H := by
  have key : y ∈ Group.conjugatesOfSet (H : Set G) ↔ ∃ x : G, x⁻¹ * y * x ∈ H := by
    rw [Group.mem_conjugatesOfSet_iff]
    constructor
    · rintro ⟨a, ha, hc⟩
      obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      have hcancel : c⁻¹ * (c * a * c⁻¹) * c = a := by group
      refine ⟨c, ?_⟩
      rw [hcancel]
      exact ha
    · rintro ⟨x, hx⟩
      have hcancel : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      exact ⟨x⁻¹ * y * x, hx, isConj_iff.2 ⟨x, hcancel⟩⟩
  simp only [frobeniusKernel_def, Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff, key,
    not_exists]

/-- Being outside the Frobenius kernel means being a nonidentity element of some conjugate of
`H`. -/
@[simp]
theorem notMem_frobeniusKernel_iff {y : G} :
    y ∉ frobeniusKernel H ↔ y ≠ 1 ∧ ∃ x : G, x⁻¹ * y * x ∈ H := by
  rw [mem_frobeniusKernel]
  push Not
  rfl

@[simp]
theorem one_mem_frobeniusKernel : (1 : G) ∈ frobeniusKernel H :=
  mem_frobeniusKernel.2 (Or.inl rfl)

/-- The Frobenius kernel is closed under inversion: `x⁻¹ y⁻¹ x` is the inverse of `x⁻¹ y x`, and a
subgroup contains an element exactly when it contains its inverse. -/
@[simp]
theorem inv_mem_frobeniusKernel_iff {y : G} :
    y⁻¹ ∈ frobeniusKernel H ↔ y ∈ frobeniusKernel H := by
  simp only [mem_frobeniusKernel, inv_eq_one]
  refine or_congr Iff.rfl (forall_congr' fun x => not_congr ?_)
  have hinv : x⁻¹ * y⁻¹ * x = (x⁻¹ * y * x)⁻¹ := by group
  rw [hinv, H.inv_mem_iff]

/-- The Frobenius kernel is invariant under conjugation: it is the identity together with the
complement of a conjugation-closed set, and `Group.conj_mem_conjugatesOfSet` is that closure.  This
is the half of normality that costs nothing; closure under multiplication is Frobenius's theorem. -/
@[simp]
theorem conj_mem_frobeniusKernel_iff {y g : G} :
    g * y * g⁻¹ ∈ frobeniusKernel H ↔ y ∈ frobeniusKernel H := by
  simp only [frobeniusKernel_def, Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff,
    conj_eq_one_iff]
  refine or_congr Iff.rfl (not_congr ⟨fun h => ?_, Group.conj_mem_conjugatesOfSet⟩)
  have hcancel : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  exact hcancel ▸ Group.conj_mem_conjugatesOfSet h

/-- **The Frobenius kernel meets each conjugate of `H` exactly in the identity.**  A nonidentity
element of `g H g⁻¹` lies in a conjugate of `H`, so it is outside the kernel. -/
@[simp]
theorem frobeniusKernel_inter_conj_smul_eq_singleton (g : G) :
    frobeniusKernel H ∩ MulAut.conj g • (H : Set G) = {1} := by
  have key : ∀ y : G, y ∈ MulAut.conj g • (H : Set G) ↔ g⁻¹ * y * g ∈ H := fun y => by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · rcases mem_frobeniusKernel.1 hy.1 with h1 | h
    · exact h1
    · exact absurd ((key y).1 hy.2) (h g)
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨one_mem_frobeniusKernel, (key 1).2 (by simp)⟩

/-- **The Frobenius kernel meets `H` exactly in the identity**, the case `g = 1` of
`TauCeti.frobeniusKernel_inter_conj_smul_eq_singleton`. -/
@[simp]
theorem frobeniusKernel_inter_eq_singleton : frobeniusKernel H ∩ (H : Set G) = {1} := by
  simpa using frobeniusKernel_inter_conj_smul_eq_singleton (H := H) 1

/-- The Frobenius kernel of the whole group is trivial: every element lies in `⊤`. -/
@[simp]
theorem frobeniusKernel_top : frobeniusKernel (⊤ : Subgroup G) = {1} := by
  ext y
  simp [mem_frobeniusKernel]

/-- The Frobenius kernel of the trivial subgroup is everything: no conjugate of a nonidentity
element is the identity. -/
@[simp]
theorem frobeniusKernel_bot : frobeniusKernel (⊥ : Subgroup G) = Set.univ := by
  ext y
  simp only [mem_frobeniusKernel, Set.mem_univ, iff_true, Subgroup.mem_bot]
  refine (eq_or_ne y 1).imp id fun hy x hx => hy ?_
  -- `conj_eq_one_iff` is stated for `a * y * a⁻¹`, so the conjugator is exhibited as `x⁻¹`.
  have hconj : x⁻¹ * y * x = x⁻¹ * y * (x⁻¹)⁻¹ := by group
  exact conj_eq_one_iff.1 (hconj ▸ hx)

/-! ### Counting the kernel -/

/-- The complement of the Frobenius kernel is the set of conjugates of the nonidentity elements of
`H`: lying outside the kernel means being a nonidentity element of some conjugate of `H`, and
conjugation fixes the identity. -/
private theorem compl_frobeniusKernel (H : Subgroup G) :
    (frobeniusKernel H)ᶜ = Group.conjugatesOfSet ((H : Set G) \ {1}) := by
  ext y
  simp only [Set.mem_compl_iff, notMem_frobeniusKernel_iff, Group.mem_conjugatesOfSet_iff,
    Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff, ne_eq]
  constructor
  · rintro ⟨hy1, x, hx⟩
    refine ⟨x⁻¹ * y * x, ⟨hx, ?_⟩, isConj_iff.2 ⟨x, by group⟩⟩
    -- `conj_eq_one_iff` is stated for `a * y * a⁻¹`, so the conjugator is exhibited as `x⁻¹`.
    have hconj : x⁻¹ * y * x = x⁻¹ * y * (x⁻¹)⁻¹ := by group
    rw [hconj, conj_eq_one_iff]
    exact hy1
  · rintro ⟨a, ⟨haH, ha1⟩, hconj⟩
    obtain ⟨x, rfl⟩ := isConj_iff.1 hconj
    refine ⟨fun h => ha1 (conj_eq_one_iff.1 h), x, ?_⟩
    have hcancel : x⁻¹ * (x * a * x⁻¹) * x = a := by group
    rw [hcancel]
    exact haH

/-- **The complement of the Frobenius kernel has `Set.ncard` equal to `|G : H| · (|H| - 1)`.**  For
a trivial-intersection subgroup the elements outside the kernel are exactly the conjugates of the
nonidentity elements of `H`, which `TauCeti.IsTISet.ncard_conjugatesOfSet` counts as `|G : H|`
times the `|H| - 1` elements of `H` that are conjugated.  No finiteness is assumed — but this is an
`ncard` identity, which for an infinite `G` need not be an element count: an infinite side reads as
the junk value `0` that `Set.ncard` and `Subgroup.index` take on infinite arguments, even though a
degenerate case may still be a genuine count (for `H = ⊥` the complement of the kernel is honestly
empty).  The count that is guaranteed to be one is
`TauCeti.IsTISubgroup.ncard_frobeniusKernel`, stated for a finite `G`. -/
theorem IsTISubgroup.ncard_compl_frobeniusKernel (hH : IsTISubgroup H) :
    ((frobeniusKernel H)ᶜ).ncard = H.index * (Nat.card H - 1) := by
  have hcoe : (H : Set G).ncard = Nat.card H := (Nat.card_coe_set_eq (H : Set G)).symm
  rw [compl_frobeniusKernel, hH.isTISet_diff_one.ncard_conjugatesOfSet,
    Set.ncard_sdiff_singleton_of_mem H.one_mem, hcoe]

/-- **The Frobenius kernel of a trivial-intersection subgroup of a finite group has `|G : H|`
elements.**  The conjugates of `H` cover `|G : H| · (|H| - 1)` nonidentity elements between them,
and `|G| = |G : H| · |H|`, so `|G : H|` elements are left over. -/
theorem IsTISubgroup.ncard_frobeniusKernel [Finite G] (hH : IsTISubgroup H) :
    (frobeniusKernel H).ncard = H.index := by
  obtain ⟨m, hm⟩ : ∃ m, Nat.card H = m + 1 := ⟨Nat.card H - 1, by
    have := Nat.card_pos (α := H)
    omega⟩
  have hcard := H.index_mul_card
  rw [hm, Nat.mul_add, Nat.mul_one] at hcard
  -- `Set.ncard_compl_of_ncard_eq_add` reads the count of the kernel off the count of its
  -- complement, once `compl_compl` presents the kernel as that complement.
  rw [← compl_compl (frobeniusKernel H)]
  refine Set.ncard_compl_of_ncard_eq_add _ ?_
  rw [hH.ncard_compl_frobeniusKernel, hm, Nat.add_sub_cancel]
  omega

/-- The Frobenius kernel of a trivial-intersection subgroup of a finite group has `|G : H|`
elements, read as the cardinality of its coercion to a type. -/
theorem IsTISubgroup.natCard_frobeniusKernel [Finite G] (hH : IsTISubgroup H) :
    Nat.card (frobeniusKernel H) = H.index :=
  (Nat.card_coe_set_eq _).trans hH.ncard_frobeniusKernel

/-- **A subgroup of a finite group carried by the Frobenius kernel is a complement to `H`.**
Frobenius's theorem provides such a subgroup for a Frobenius complement; that it is a complement is
then pure counting, the kernel having `|G : H|` elements and meeting `H` only in the identity.
Nothing here asserts that such a subgroup exists. -/
theorem IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel [Finite G] (hH : IsTISubgroup H)
    {N : Subgroup G} (hN : (N : Set G) = frobeniusKernel H) : N.IsComplement' H := by
  have hcard : Nat.card N * Nat.card H = Nat.card G := by
    have hcardN : Nat.card N = Nat.card (frobeniusKernel H) := Nat.card_congr (Set.equivOfEq hN)
    rw [hcardN, hH.natCard_frobeniusKernel]
    exact H.index_mul_card
  refine Subgroup.isComplement'_of_card_mul_and_disjoint hcard (Subgroup.disjoint_def.2 ?_)
  intro y hyN hyH
  have hmem : y ∈ frobeniusKernel H ∩ (H : Set G) :=
    ⟨hN ▸ SetLike.mem_coe.2 hyN, SetLike.mem_coe.2 hyH⟩
  rwa [frobeniusKernel_inter_eq_singleton, Set.mem_singleton_iff] at hmem

/-! ### The free conjugation action on the nonidentity part of the kernel -/

/-- Conjugation carries a nonidentity element of the Frobenius kernel to another one: the kernel
is conjugation-invariant, and only the identity is conjugate to the identity. -/
theorem conj_mem_frobeniusKernel_sdiff_singleton (g : G) {y : G}
    (hy : y ∈ frobeniusKernel H \ {1}) : g * y * g⁻¹ ∈ frobeniusKernel H \ {1} := by
  refine ⟨conj_mem_frobeniusKernel_iff.2 hy.1, fun h => hy.2 ?_⟩
  rw [Set.mem_singleton_iff] at h ⊢
  exact conj_eq_one_iff.1 h

/-- **Conjugation by an element of `H`, as a scalar action on the nonidentity part of the
Frobenius kernel.**  This instance records only the underlying map; that it is an action is the
`MulAction` instance below. -/
instance : SMul H ↥(frobeniusKernel H \ {1}) where
  smul h y := ⟨(h : G) * y * (h : G)⁻¹, conj_mem_frobeniusKernel_sdiff_singleton (h : G) y.2⟩

@[simp]
theorem coe_smul_frobeniusKernel_sdiff_singleton (h : H) (y : ↥(frobeniusKernel H \ {1})) :
    ((h • y : ↥(frobeniusKernel H \ {1})) : G) = (h : G) * (y : G) * (h : G)⁻¹ :=
  (rfl)

/-- **`H` acts on the nonidentity part of its Frobenius kernel by conjugation.**  Freeness of this
action is `TauCeti.IsTISubgroup.stabilizer_eq_bot`, and it is what forces `|H|` to divide
`|G : H| - 1`. -/
instance : MulAction H ↥(frobeniusKernel H \ {1}) where
  one_smul y := Subtype.ext (by simp)
  mul_smul h₁ h₂ y := Subtype.ext (by
    simp only [coe_smul_frobeniusKernel_sdiff_singleton, Subgroup.coe_mul, mul_inv_rev]
    group)

/-- **A nonidentity element of a trivial-intersection subgroup commutes with no nonidentity
element of its Frobenius kernel**, in conjugation form.  Both the freeness of the conjugation
action (`TauCeti.IsTISubgroup.stabilizer_eq_bot`) and the centralizer bound on the kernel side
(`TauCeti.IsTISubgroup.centralizer_singleton_subset_frobeniusKernel`) are readings of it. -/
theorem IsTISubgroup.conj_ne_self_of_mem_frobeniusKernel (hH : IsTISubgroup H) {h y : G}
    (hh : h ∈ H) (hh1 : h ≠ 1) (hy : y ∈ frobeniusKernel H) (hy1 : y ≠ 1) :
    h * y * h⁻¹ ≠ y := by
  intro hconj
  have hyh : h * y = y * h := by
    calc h * y = h * y * h⁻¹ * h := by group
      _ = y * h := by rw [hconj]
  have hcomm : y * h * y⁻¹ = h := by
    rw [← hyh]
    group
  have hmem : y ∈ frobeniusKernel H ∩ (H : Set G) :=
    ⟨hy, hH.mem_of_conj_eq_self hh hh1 hcomm⟩
  rw [frobeniusKernel_inter_eq_singleton, Set.mem_singleton_iff] at hmem
  exact hy1 hmem

/-- **The conjugation action of a trivial-intersection subgroup on the nonidentity part of its
Frobenius kernel is free**: every stabilizer is trivial.  This is the hypothesis the orbit
counting in `TauCeti.IsTISubgroup.card_dvd_index_sub_one` consumes. -/
theorem IsTISubgroup.stabilizer_eq_bot (hH : IsTISubgroup H)
    (y : ↥(frobeniusKernel H \ {1})) : MulAction.stabilizer H y = ⊥ := by
  refine eq_bot_iff.2 fun h hh => ?_
  rw [MulAction.mem_stabilizer_iff] at hh
  rw [Subgroup.mem_bot]
  by_contra hh1
  have hconj : (h : G) * (y : G) * (h : G)⁻¹ = (y : G) := by
    rw [← coe_smul_frobeniusKernel_sdiff_singleton, hh]
  refine hH.conj_ne_self_of_mem_frobeniusKernel h.2 ?_ y.2.1 ?_ hconj
  · simpa using hh1
  · simpa using y.2.2

/-- **The conjugation action of a trivial-intersection subgroup on the nonidentity part of its
Frobenius kernel is cancellative**, the typeclass form of
`TauCeti.IsTISubgroup.stabilizer_eq_bot`, for the generic results that take freeness as an
instance.  It cannot itself be an instance, since freeness holds only under the hypothesis
`hH`. -/
theorem IsTISubgroup.isCancelSMul (hH : IsTISubgroup H) :
    IsCancelSMul H ↥(frobeniusKernel H \ {1}) :=
  isCancelSMul_iff_stabilizer_eq_bot.2 hH.stabilizer_eq_bot

/-- **An element commuting with a nonidentity element of the Frobenius kernel lies in the
kernel**, the mirror on the kernel side of `TauCeti.IsTISubgroup.mem_of_conj_eq_self`.  Its
inclusion form is `TauCeti.IsTISubgroup.centralizer_singleton_subset_frobeniusKernel`. -/
theorem IsTISubgroup.mem_frobeniusKernel_of_conj_eq_self (hH : IsTISubgroup H) {g y : G}
    (hy : y ∈ frobeniusKernel H) (hy1 : y ≠ 1) (hgy : g * y * g⁻¹ = y) :
    g ∈ frobeniusKernel H := by
  by_contra hg
  rw [notMem_frobeniusKernel_iff] at hg
  obtain ⟨hg1, x, hx⟩ := hg
  -- `conj_mem_frobeniusKernel_iff` and `conj_eq_one_iff` are stated for `a * z * a⁻¹`, so the
  -- conjugator `x⁻¹` has to be exhibited as an inverse.
  have hinv : ∀ z : G, x⁻¹ * z * x = x⁻¹ * z * (x⁻¹)⁻¹ := fun z => by group
  have hz : x⁻¹ * y * x ∈ frobeniusKernel H := by
    rw [hinv]
    exact conj_mem_frobeniusKernel_iff.2 hy
  have hz1 : x⁻¹ * y * x ≠ 1 := fun h0 =>
    hy1 (conj_eq_one_iff.1 ((hinv y).symm.trans h0))
  have hx1 : x⁻¹ * g * x ≠ 1 := fun h0 =>
    hg1 (conj_eq_one_iff.1 ((hinv g).symm.trans h0))
  refine hH.conj_ne_self_of_mem_frobeniusKernel hx hx1 hz hz1 ?_
  calc x⁻¹ * g * x * (x⁻¹ * y * x) * (x⁻¹ * g * x)⁻¹
      = x⁻¹ * (g * y * g⁻¹) * x := by group
    _ = x⁻¹ * y * x := by rw [hgy]

/-- **The centralizer of a nonidentity element of the Frobenius kernel is contained in the
kernel**, the inclusion form of `TauCeti.IsTISubgroup.mem_frobeniusKernel_of_conj_eq_self`. -/
theorem IsTISubgroup.centralizer_singleton_subset_frobeniusKernel (hH : IsTISubgroup H) {y : G}
    (hy : y ∈ frobeniusKernel H) (hy1 : y ≠ 1) :
    (Subgroup.centralizer {y} : Set G) ⊆ frobeniusKernel H := by
  intro g hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
  refine hH.mem_frobeniusKernel_of_conj_eq_self hy hy1 ?_
  rw [hg]
  group

/-! ### The order of the complement divides the size of the kernel minus one -/

/-- **The order of a trivial-intersection subgroup of a finite group divides `|G : H| - 1`.**  For
a Frobenius complement `H`, Frobenius's theorem makes the kernel a subgroup `N` of order `|G : H|`,
so this is the classical `|H| ∣ |N| - 1`
(`TauCeti.card_dvd_card_frobeniusKernelSubgroup_sub_one`). -/
theorem IsTISubgroup.card_dvd_index_sub_one [Finite G] (hH : IsTISubgroup H) :
    Nat.card H ∣ H.index - 1 := by
  have hcard : Nat.card ↥(frobeniusKernel H \ {1}) = H.index - 1 := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem one_mem_frobeniusKernel,
      hH.ncard_frobeniusKernel]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, Nat.card ↥(frobeniusKernel H \ {1}) = q * Nat.card H :=
    ⟨_, (Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hH.stabilizer_eq_bot)).trans
      (Nat.card_prod _ _)⟩
  rw [← hcard, hq]
  exact dvd_mul_left _ _

/-- **The order of a trivial-intersection subgroup of a finite group is coprime to its index**, an
immediate consequence of `TauCeti.IsTISubgroup.card_dvd_index_sub_one`.  For a Frobenius group it
says that the complement and the kernel have coprime orders
(`TauCeti.coprime_card_card_frobeniusKernelSubgroup`). -/
theorem IsTISubgroup.coprime_card_index [Finite G] (hH : IsTISubgroup H) :
    Nat.Coprime (Nat.card H) H.index := by
  have hsplit : H.index = 1 + (H.index - 1) := by
    have : 0 < H.index := Nat.pos_of_ne_zero H.index_ne_zero_of_finite
    omega
  rw [hsplit]
  exact (Nat.coprime_add_iff_left hH.card_dvd_index_sub_one).2 (Nat.coprime_one_right _)

/-- **A proper trivial-intersection subgroup of a finite group is smaller than its index**,
`|H| < |G : H|`, another immediate consequence of
`TauCeti.IsTISubgroup.card_dvd_index_sub_one`.  Properness is needed: for `H = ⊤` the index is `1`
and the inequality reverses.  For a Frobenius group it says that the complement is smaller than
the kernel (`TauCeti.card_lt_card_frobeniusKernelSubgroup`). -/
theorem IsTISubgroup.card_lt_index [Finite G] (hH : IsTISubgroup H) (hne : H ≠ ⊤) :
    Nat.card H < H.index := by
  have hne1 : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hpos : 0 < H.index := Nat.pos_of_ne_zero H.index_ne_zero_of_finite
  have hle := Nat.le_of_dvd (by omega) hH.card_dvd_index_sub_one
  omega

/-! ### Recognizing the kernel from a semidirect decomposition -/

section Semidirect

variable {N : Subgroup G}

/-- **A normal subgroup meeting `H` trivially lies in the Frobenius kernel of `H`.**  Every
conjugate of such a subgroup is itself, so a nonidentity element of it is conjugated into `H` by
nothing at all.  No finiteness and no complement hypothesis: this inclusion is the easy half of
`TauCeti.IsTISubgroup.coe_eq_frobeniusKernel_of_isComplement'`. -/
theorem coe_subset_frobeniusKernel [N.Normal] (hdisj : Disjoint N H) :
    (N : Set G) ⊆ frobeniusKernel H := by
  intro y hy
  rw [SetLike.mem_coe] at hy
  rw [mem_frobeniusKernel]
  by_cases h1 : y = 1
  · exact Or.inl h1
  refine Or.inr fun x hx => h1 ?_
  have hmem : x⁻¹ * y * x ∈ N := by
    have hrw : x⁻¹ * y * x = x⁻¹ * y * (x⁻¹)⁻¹ := by group
    rw [hrw]
    exact ‹N.Normal›.conj_mem y hy x⁻¹
  have hone : x⁻¹ * y * x = 1 := Subgroup.disjoint_def.mp hdisj hmem hx
  calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    _ = 1 := by rw [hone, mul_one, mul_inv_cancel]

/-- **The Frobenius kernel of a normal complement to a trivial-intersection subgroup is that
complement itself.**  The inclusion `N ⊆ frobeniusKernel H` is
`TauCeti.coe_subset_frobeniusKernel`, and the two sides have the same number of elements:
`|N| = |G : H|` because `N` is a complement, and the kernel has `|G : H|` elements by
`TauCeti.IsTISubgroup.ncard_frobeniusKernel`.

This is what identifies the kernel that Frobenius's theorem constructs from the character theory
of `G` with the normal complement a semidirect decomposition `G = N ⋊ H` hands over directly; a
fixed-point-free action of `H` on `N` supplies the trivial-intersection hypothesis through
`TauCeti.isTISubgroup_of_isComplement'_of_fixedPointFree`, and the subgroup-level statement is
`TauCeti.frobeniusKernelSubgroup_eq_of_isComplement'`. -/
theorem IsTISubgroup.coe_eq_frobeniusKernel_of_isComplement' [Finite G] [N.Normal]
    (hH : IsTISubgroup H) (hNH : N.IsComplement' H) :
    (N : Set G) = frobeniusKernel H := by
  have hcoe : (N : Set G).ncard = Nat.card N := (Nat.card_coe_set_eq (N : Set G)).symm
  refine Set.eq_of_subset_of_ncard_le (coe_subset_frobeniusKernel hNH.disjoint) ?_ (Set.toFinite _)
  rw [hH.ncard_frobeniusKernel, hcoe, hNH.index_eq_card]

end Semidirect

end TauCeti
