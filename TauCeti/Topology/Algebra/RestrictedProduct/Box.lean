/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Bases

/-!
# Coordinate boxes and the open-box basis of a restricted product

For a restricted product `Πʳ i, [R i, A i]_[𝓕]` and a family of subsets `C : ∀ i, Set (R i)`, the
coordinate box `RestrictedProduct.box C` is `{x | ∀ i, x i ∈ C i}`, the preimage of `Set.univ.pi C`
under the coercion to the full product. Coordinate boxes supply the canonical neighbourhood basis
and explicit π-systems needed to establish second countability, Borel σ-algebra generation, and
restricted Haar measure constructions on adelic and local-global restricted products.

This file develops the set-theoretic, algebraic, closedness, compactness, and openness API of
coordinate boxes without extraneous openness assumptions on `A i`. In particular, it proves a
sufficient condition (`isOpenEmbedding_inclusion_principal_of_forall_mem`) for a cofinite
principal-stage inclusion to be an open embedding that requires openness of `A i` only on the
constrained index set `S` (allowing restricted products with cofinitely open reference sets to be
covered by open stages), and shows that over the cofinite filter the open cofinitely-`A i` boxes
form a neighbourhood basis and a topological basis whenever `A i` is open for cofinitely many `i`.

The eventual openness and compactness arguments for coordinate boxes generalize those in
`TauCeti/Topology/Algebra/RestrictedProduct/Basic.lean`, which adapts them from the FLT project
(`ImperialCollegeLondon/FLT`, file `TopologicalSpace.lean`, source commit
`bc2fe8ff7396469a16c2a6d51d6117f5825d93a0`, FLT PR #1088, Apache 2.0), whose source file credits
Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun, and Pietro
Monticone.

## Main definitions

* `RestrictedProduct.box`: the coordinate box `{x | ∀ i, x i ∈ C i}` in `Πʳ i, [R i, A i]_[𝓕]`.
* `RestrictedProduct.openBoxes`: the family of boxes `box C` in `Πʳ i, [R i, A i]` with every
  `C i` open and `C i = A i` for cofinitely many `i`.

## Main statements

* `RestrictedProduct.isOpenEmbedding_inclusion_principal_of_forall_mem`: for cofinite `S`, the
  inclusion of `Πʳ i, [R i, A i]_[𝓟 S]` into `Πʳ i, [R i, A i]` is an open embedding as soon as
  `A i` is open for every `i ∈ S`.
* `RestrictedProduct.isOpen_box` and `RestrictedProduct.isCompact_box`: `box C` is open in
  `Πʳ i, [R i, A i]` when every `C i` is open and `A i ⊆ C i` cofinitely, and compact in
  `Πʳ i, [R i, A i]_[𝓕]` when every `C i` is compact and `C i ⊆ A i` `𝓕`-eventually, with no
  openness assumption on `A i`.
* `RestrictedProduct.hasBasis_nhds_open_box` and `RestrictedProduct.isTopologicalBasis_openBoxes`:
  when `A i` is open for cofinitely many `i`, the open cofinitely-`A i` boxes form a neighbourhood
  basis at every point and a topological basis of `Πʳ i, [R i, A i]`.

## References

* N. Bourbaki, *General Topology*.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Lemma 3.63.
* A. Weil, *Basic Number Theory*.
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

section SetTheory

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)} {𝓕 : Filter ι}

/-- The coordinate box `{x | ∀ i, x i ∈ C i}` in a restricted product `Πʳ i, [R i, A i]_[𝓕]`,
cut out by a family of subsets `C : ∀ i, Set (R i)`. -/
def box (C : ∀ i, Set (R i)) : Set (Πʳ i, [R i, A i]_[𝓕]) :=
  {x | ∀ i, x i ∈ C i}

/-- Unfolding `box C` as `{x | ∀ i, x i ∈ C i}`. -/
theorem box_def (C : ∀ i, Set (R i)) :
    (box C : Set (Πʳ i, [R i, A i]_[𝓕])) = {x | ∀ i, x i ∈ C i} :=
  (rfl)

/-- Membership in `box C` means every coordinate lies in the corresponding factor `C i`. -/
@[simp, grind =]
theorem mem_box {C : ∀ i, Set (R i)} {x : Πʳ i, [R i, A i]_[𝓕]} :
    x ∈ box C ↔ ∀ i, x i ∈ C i :=
  Iff.rfl

/-- `box C` is the preimage of `Set.univ.pi C` under coercion to the full product. -/
@[simp]
theorem preimage_coe_univ_pi (C : ∀ i, Set (R i)) :
    ((↑) : Πʳ i, [R i, A i]_[𝓕] → Π i, R i) ⁻¹' univ.pi C = box C := by
  ext x
  simp

/-- `box C` is the intersection of the single-coordinate preimages of `C i`. -/
theorem box_eq_iInter (C : ∀ i, Set (R i)) :
    (box C : Set (Πʳ i, [R i, A i]_[𝓕])) = ⋂ i, (fun x ↦ x i) ⁻¹' C i := by
  ext x
  simp

/-- The box whose factors are all `Set.univ` is the whole restricted product. -/
@[simp]
theorem box_univ :
    (box (fun i ↦ (univ : Set (R i))) : Set (Πʳ i, [R i, A i]_[𝓕])) = univ := by
  ext x
  simp

/-- A box with an empty factor is empty. -/
theorem box_eq_empty_of_eq_empty {C : ∀ i, Set (R i)} {i : ι} (hi : C i = ∅) :
    (box C : Set (Πʳ j, [R j, A j]_[𝓕])) = ∅ := by
  ext x
  simp only [mem_box, mem_empty_iff_false, iff_false, not_forall]
  exact ⟨i, by simp [hi]⟩

/-- A box in `Πʳ i, [R i, A i]_[𝓕]` is nonempty if and only if every factor `C i` is nonempty and
`C i ∩ A i` is nonempty for `𝓕`-eventually all `i`. -/
theorem nonempty_box_iff {C : ∀ i, Set (R i)} :
    (box C : Set (Πʳ i, [R i, A i]_[𝓕])).Nonempty ↔
      (∀ i, (C i).Nonempty) ∧ ∀ᶠ i in 𝓕, (C i ∩ A i).Nonempty := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun i ↦ ⟨x i, hx i⟩, x.2.mono fun i hi ↦ ⟨x i, hx i, hi⟩⟩
  · rintro ⟨hC, hCA⟩
    choose f hf using hC
    choose g hgC hgA using fun i (hi : (C i ∩ A i).Nonempty) ↦ hi
    let x : Π i, R i := fun i ↦ if hi : (C i ∩ A i).Nonempty then g i hi else f i
    have hxA : ∀ᶠ i in 𝓕, x i ∈ A i := hCA.mono fun i hi ↦ by
      simp only [x, hi, ↓reduceDIte]
      exact hgA i hi
    refine ⟨RestrictedProduct.mk x hxA, mem_box.mpr fun i ↦ ?_⟩
    rw [mk_apply]
    by_cases hi : (C i ∩ A i).Nonempty <;> simp [x, hi, hgC, hf]

/-- When `C i ⊆ A i` for `𝓕`-eventually all `i`, `box C` is nonempty if and only if every factor
`C i` is nonempty. -/
theorem nonempty_box_iff_of_eventually_subset {C : ∀ i, Set (R i)}
    (hCA : ∀ᶠ i in 𝓕, C i ⊆ A i) :
    (box C : Set (Πʳ i, [R i, A i]_[𝓕])).Nonempty ↔ ∀ i, (C i).Nonempty := by
  rw [nonempty_box_iff, and_iff_left_iff_imp]
  intro hC
  exact hCA.mono fun i hi ↦ (hC i).mono (subset_inter Subset.rfl hi)

/-- When `C i ⊆ A i` for `𝓕`-eventually all `i`, `box C` is empty if and only if some factor `C i`
is empty. -/
theorem box_eq_empty_iff_of_eventually_subset {C : ∀ i, Set (R i)}
    (hCA : ∀ᶠ i in 𝓕, C i ⊆ A i) :
    (box C : Set (Πʳ i, [R i, A i]_[𝓕])) = ∅ ↔ ∃ i, C i = ∅ := by
  rw [← not_nonempty_iff_eq_empty, nonempty_box_iff_of_eventually_subset hCA, not_forall]
  simp [not_nonempty_iff_eq_empty]

/-- Coordinatewise inclusion of factor families gives inclusion of boxes. -/
@[gcongr]
theorem box_mono {C D : ∀ i, Set (R i)} (h : ∀ i, C i ⊆ D i) :
    (box C : Set (Πʳ i, [R i, A i]_[𝓕])) ⊆ box D :=
  fun _ hx i ↦ h i (hx i)

/-- The intersection of two boxes is the box of coordinatewise intersections. -/
@[simp]
theorem box_inter (C D : ∀ i, Set (R i)) :
    (box (fun i ↦ C i ∩ D i) : Set (Πʳ i, [R i, A i]_[𝓕])) = box C ∩ box D := by
  ext x
  exact forall_and

/-- An arbitrary indexed intersection of boxes is the box of coordinatewise intersections. -/
theorem box_iInter {κ : Sort*} (C : κ → ∀ i, Set (R i)) :
    (box (fun i ↦ ⋂ k, C k i) : Set (Πʳ i, [R i, A i]_[𝓕])) = ⋂ k, box (C k) := by
  ext x
  simp only [mem_box, mem_iInter]
  exact forall_comm

/-- Pulling `box C` back along `inclusion R A h` (`h : 𝓕 ≤ 𝓖`) gives `box C` at the coarser
filter `𝓖`. -/
@[simp]
theorem preimage_inclusion_box {𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) (C : ∀ i, Set (R i)) :
    inclusion R A h ⁻¹' box C = box C := by
  ext x
  simp

/-- Pulling `box E` back along `RestrictedProduct.map φ hφ` gives the box of coordinatewise
preimages `φ i ⁻¹' E i`. -/
@[simp]
theorem preimage_map_box {S : ι → Type*} {B : ∀ i, Set (S i)} (φ : ∀ i, R i → S i)
    (hφ : ∀ᶠ i in 𝓕, MapsTo (φ i) (A i) (B i)) (E : ∀ i, Set (S i)) :
    RestrictedProduct.map φ hφ ⁻¹' box E = box (fun i ↦ φ i ⁻¹' E i) := by
  ext x
  simp

/-- Pulling `box C` back along `structureMap` gives the product of `(↑) ⁻¹' C i` in `Π i, A i`. -/
@[simp]
theorem preimage_structureMap_box (C : ∀ i, Set (R i)) :
    structureMap R A 𝓕 ⁻¹' box C = univ.pi fun i ↦ ((↑) : A i → R i) ⁻¹' C i := by
  ext x
  simp

/-- The range of `structureMap` is the integral box `box A`. -/
theorem range_structureMap_eq_box :
    range (structureMap R A 𝓕) = box A :=
  range_structureMap R A

/-- The range of the top-level inclusion `Πʳ i, [R i, A i]_[⊤] → Πʳ i, [R i, A i]_[𝓕]`, which is
the principal stage of `Set.univ` (empty exceptional set), equals the integral box `box A`. -/
theorem range_inclusion_top_eq_box :
    range (inclusion R A (le_top : 𝓕 ≤ ⊤)) = box A := by
  rw [range_inclusion]
  simp [box]

/-- For a principal filter `𝓟 S` with `𝓕 ≤ 𝓟 S`, the range of `inclusion R A hS` is the box with
factor `A i` on `S` and `Set.univ` outside `S`. -/
theorem range_inclusion_principal_eq_box (S : Set ι) [DecidablePred (· ∈ S)] (hS : 𝓕 ≤ 𝓟 S) :
    range (inclusion R A hS) = box (fun i ↦ if i ∈ S then A i else univ) := by
  ext x
  rw [range_inclusion, mem_ofPred_eq, eventually_principal, mem_box]
  refine ⟨fun h i ↦ ?_, fun h i hi ↦ ?_⟩
  · split_ifs with hi
    · exact h i hi
    · exact mem_univ _
  · simpa [hi] using h i

end SetTheory

section Algebra

variable {ι : Type*} {G : ι → Type*} {S : ι → Type*} [∀ i, SetLike (S i) (G i)]
variable {B : ∀ i, S i} {𝓕 : Filter ι}

/-- Preimage of a box under left multiplication in a restricted product is the box of coordinatewise
left-multiplication preimages. -/
@[to_additive (attr := simp)
  /-- Preimage of a box under left addition in a restricted product is the box of coordinatewise
  left-addition preimages. -/]
theorem preimage_mul_left_box [∀ i, Mul (G i)] [∀ i, MulMemClass (S i) (G i)]
    (g : Πʳ i, [G i, B i]_[𝓕]) (C : ∀ i, Set (G i)) :
    (g * ·) ⁻¹' box C = box (fun i ↦ (g i * ·) ⁻¹' C i) := by
  ext x
  simp

/-- Preimage of a box under right multiplication in a restricted product is the box of
coordinatewise right-multiplication preimages. -/
@[to_additive (attr := simp)
  /-- Preimage of a box under right addition in a restricted product is the box of coordinatewise
  right-addition preimages. -/]
theorem preimage_mul_right_box [∀ i, Mul (G i)] [∀ i, MulMemClass (S i) (G i)]
    (g : Πʳ i, [G i, B i]_[𝓕]) (C : ∀ i, Set (G i)) :
    (· * g) ⁻¹' box C = box (fun i ↦ (· * g i) ⁻¹' C i) := by
  ext x
  simp

/-- Preimage of a box under inversion in a restricted product is the box of coordinatewise
inversion preimages. -/
@[to_additive
  /-- Preimage of a box under negation in a restricted product is the box of coordinatewise
  negation preimages. -/]
theorem preimage_inv_box [∀ i, Inv (G i)] [∀ i, InvMemClass (S i) (G i)] (C : ∀ i, Set (G i)) :
    Inv.inv ⁻¹' (box C : Set (Πʳ i, [G i, B i]_[𝓕])) = box (fun i ↦ Inv.inv ⁻¹' C i) := by
  ext x
  simp

/-- Preimage of a box under scalar action in a restricted product is the box of coordinatewise
scalar-action preimages. -/
@[to_additive (attr := simp)
  /-- Preimage of a box under additive action in a restricted product is the box of coordinatewise
  additive-action preimages. -/]
theorem preimage_smul_box {M : Type*} [∀ i, SMul M (G i)] [∀ i, SMulMemClass (S i) M (G i)]
    (m : M) (C : ∀ i, Set (G i)) :
    (m • ·) ⁻¹' (box C : Set (Πʳ i, [G i, B i]_[𝓕])) = box (fun i ↦ (m • ·) ⁻¹' C i) := by
  ext x
  simp

end Algebra

section Topology

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- A coordinate box with closed factors is closed in `Πʳ i, [R i, A i]_[𝓕]` for every filter `𝓕`
and arbitrary reference sets `A i`. -/
theorem isClosed_box {𝓕 : Filter ι} {C : ∀ i, Set (R i)} (hC : ∀ i, IsClosed (C i)) :
    IsClosed (box C : Set (Πʳ i, [R i, A i]_[𝓕])) := by
  rw [box_eq_iInter]
  exact isClosed_iInter fun i ↦ (hC i).preimage (continuous_eval i)

/-- A coordinate box `box C` in `Πʳ i, [R i, A i]_[𝓕]` with compact factors `C i` satisfying
`C i ⊆ A i` `𝓕`-eventually is compact, with no openness assumption on `A i`. -/
theorem isCompact_box {𝓕 : Filter ι} {C : ∀ i, Set (R i)} (hC : ∀ i, IsCompact (C i))
    (hCA : ∀ᶠ i in 𝓕, C i ⊆ A i) :
    IsCompact (box C : Set (Πʳ i, [R i, A i]_[𝓕])) := by
  let S : Set ι := {i | C i ⊆ A i}
  have hS : 𝓕 ≤ 𝓟 S := le_principal_iff.mpr hCA
  have hK : IsCompact (((↑) : Πʳ i, [R i, A i]_[𝓟 S] → Π i, R i) ⁻¹' univ.pi C) := by
    refine isEmbedding_coe_of_principal.isCompact_preimage' (isCompact_univ_pi hC) ?_
    rw [range_coe_principal]
    exact fun x hx i hi ↦ hi (hx i trivial)
  convert hK.image (continuous_inclusion hS) using 1
  ext x
  simp only [mem_box, mem_image, preimage_coe_univ_pi]
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨x', rfl⟩ := exists_inclusion_eq_of_eventually R A hS
      (eventually_principal.mpr fun i hi ↦ hi (hx i))
    exact ⟨x', fun i ↦ by simpa [inclusion_apply] using hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    simpa [inclusion_apply] using hy i

/-- On a cofinite principal stage `Πʳ i, [R i, A i]_[𝓟 S]`, a box `box C` with open factors `C i`
satisfying `A i ⊆ C i` cofinitely is open, with no openness assumption on `A i`. -/
theorem isOpen_box_of_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S) {C : ∀ i, Set (R i)}
    (hC : ∀ i, IsOpen (C i)) (hAC : ∀ᶠ i in cofinite, A i ⊆ C i) :
    IsOpen (box C : Set (Πʳ i, [R i, A i]_[𝓟 S])) := by
  have hfin : ({i | A i ⊆ C i} ∩ S)ᶜ.Finite := mem_cofinite.mp (hAC.and (le_principal_iff.mp hS))
  convert (isOpen_set_pi hfin fun i _ ↦ hC i).preimage continuous_coe using 1
  ext x
  simp only [mem_box, mem_preimage, Set.mem_pi]
  refine ⟨fun hx i _ ↦ hx i, fun hx i ↦ ?_⟩
  by_cases hi : i ∈ {j | A j ⊆ C j} ∩ S
  · exact hi.1 (x.2 hi.2)
  · exact hx i hi

/-- A box `box C` in `Πʳ i, [R i, A i]` with open factors `C i` satisfying `A i ⊆ C i` cofinitely
is open, with no openness assumption on `A i`. -/
theorem isOpen_box {C : ∀ i, Set (R i)} (hC : ∀ i, IsOpen (C i))
    (hAC : ∀ᶠ i in cofinite, A i ⊆ C i) :
    IsOpen (box C : Set (Πʳ i, [R i, A i])) := by
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  exact fun _ hS ↦ isOpen_box_of_principal hS hC hAC

/-- A box `box C` in `Πʳ i, [R i, A i]` with open factors `C i` satisfying `C i = A i` cofinitely
is open. -/
theorem isOpen_box_of_eventually_eq {C : ∀ i, Set (R i)} (hC : ∀ i, IsOpen (C i))
    (hCA : ∀ᶠ i in cofinite, C i = A i) :
    IsOpen (box C : Set (Πʳ i, [R i, A i])) :=
  isOpen_box hC (hCA.mono fun _ h ↦ h.symm.subset)

/-- For a cofinite set `S`, the inclusion of `Πʳ i, [R i, A i]_[𝓟 S]` into `Πʳ i, [R i, A i]` is an
open embedding whenever `A i` is open for every `i ∈ S`; openness outside `S` is not needed. -/
theorem isOpenEmbedding_inclusion_principal_of_forall_mem {S : Set ι} (hS : cofinite ≤ 𝓟 S)
    (hA : ∀ i ∈ S, IsOpen (A i)) :
    IsOpenEmbedding (inclusion R A hS) where
  toIsEmbedding := isEmbedding_inclusion_principal hS
  isOpen_range := by
    classical
    rw [range_inclusion_principal_eq_box S hS]
    refine isOpen_box (fun i ↦ ?_) (.of_forall fun i ↦ ?_)
    · split_ifs with hi
      · exact hA i hi
      · exact isOpen_univ
    · split_ifs <;> simp

variable (R A) in
/-- The family of open coordinate boxes `box C` in `Πʳ i, [R i, A i]` whose factors `C i` are open
and satisfy `C i = A i` for cofinitely many `i`. -/
def openBoxes : Set (Set (Πʳ i, [R i, A i])) :=
  {s | ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧ s = box C}

variable (R A) in
/-- Unfolding `openBoxes R A` as the set of coordinate boxes with open factors cofinitely equal to
`A i`. -/
theorem openBoxes_def :
    openBoxes R A =
      {s | ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧ s = box C} :=
  (rfl)

/-- Membership in `openBoxes R A` means being `box C` for open `C i` cofinitely equal to `A i`. -/
@[simp, grind =]
theorem mem_openBoxes_iff {s : Set (Πʳ i, [R i, A i])} :
    s ∈ openBoxes R A ↔
      ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧ s = box C :=
  Iff.rfl

/-- A coordinate box `box C` with open factors cofinitely equal to `A i` belongs to
`openBoxes R A`. -/
theorem box_mem_openBoxes {C : ∀ i, Set (R i)} (hC : ∀ i, IsOpen (C i))
    (hCA : ∀ᶠ i in cofinite, C i = A i) :
    (box C : Set (Πʳ i, [R i, A i])) ∈ openBoxes R A :=
  ⟨C, hC, hCA, rfl⟩

/-- Every set in `openBoxes R A` is open in `Πʳ i, [R i, A i]`. -/
theorem isOpen_of_mem_openBoxes {s : Set (Πʳ i, [R i, A i])} (hs : s ∈ openBoxes R A) :
    IsOpen s := by
  rcases hs with ⟨C, hC, hCA, rfl⟩
  exact isOpen_box_of_eventually_eq hC hCA

/-- `openBoxes R A` is closed under binary intersections. -/
theorem inter_mem_openBoxes {s t : Set (Πʳ i, [R i, A i])}
    (hs : s ∈ openBoxes R A) (ht : t ∈ openBoxes R A) :
    s ∩ t ∈ openBoxes R A := by
  rcases hs with ⟨C, hC, hCA, rfl⟩
  rcases ht with ⟨D, hD, hDA, rfl⟩
  refine ⟨fun i ↦ C i ∩ D i, fun i ↦ (hC i).inter (hD i), ?_, (box_inter C D).symm⟩
  exact (hCA.and hDA).mono fun i ⟨hiC, hiD⟩ ↦ by simp [hiC, hiD]

/-- When `A i` is open for cofinitely many `i`, every open neighbourhood of `x` in
`Πʳ i, [R i, A i]` contains an open cofinitely-`A i` box around `x`. -/
theorem exists_open_box_subset_of_isOpen (hA : ∀ᶠ i in cofinite, IsOpen (A i))
    {x : Πʳ i, [R i, A i]} {U : Set (Πʳ i, [R i, A i])} (hx : x ∈ U) (hU : IsOpen U) :
    ∃ C : ∀ i, Set (R i), (∀ i, x i ∈ C i) ∧ (∀ i, IsOpen (C i)) ∧
      (∀ᶠ i in cofinite, C i = A i) ∧ box C ⊆ U := by
  classical
  obtain ⟨S, hS, hxS, hAS⟩ :
      ∃ S : Set ι, cofinite ≤ 𝓟 S ∧ (∀ i ∈ S, x i ∈ A i) ∧ ∀ i ∈ S, IsOpen (A i) :=
    ⟨{i | x i ∈ A i ∧ IsOpen (A i)}, le_principal_iff.mpr (x.2.and hA),
      fun _ hi ↦ hi.1, fun _ hi ↦ hi.2⟩
  obtain ⟨x', rfl⟩ := exists_inclusion_eq_of_eventually R A hS (eventually_principal.mpr hxS)
  have hV : IsOpen (inclusion R A hS ⁻¹' U) := hU.preimage (continuous_inclusion hS)
  obtain ⟨W, hWopen, hWx⟩ := isEmbedding_coe_of_principal.isOpen_iff.mp hV
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hWopen x' (by rw [← mem_preimage, hWx]; exact hx)
  let C : ∀ i, Set (R i) := fun i ↦
    (if i ∈ I then u i else univ) ∩ (if i ∈ S then A i else univ)
  refine ⟨C, fun i ↦ ⟨?_, ?_⟩, fun i ↦ IsOpen.inter ?_ ?_, ?_, fun y hy ↦ ?_⟩
  · split_ifs with hiI
    · simpa [inclusion_apply] using (hu i hiI).2
    · exact mem_univ _
  · split_ifs with hiS
    · exact hxS i hiS
    · exact mem_univ _
  · split_ifs with hiI
    · exact (hu i hiI).1
    · exact isOpen_univ
  · split_ifs with hiS
    · exact hAS i hiS
    · exact isOpen_univ
  · have hfin : (S \ (I : Set ι))ᶜ.Finite := by
      rw [compl_sdiff]
      exact I.finite_toSet.union (mem_cofinite.mp (le_principal_iff.mp hS))
    refine mem_cofinite.mpr (hfin.subset fun i hi ⟨hiS, hiI⟩ ↦ hi ?_)
    rw [Finset.mem_coe] at hiI
    simp [C, hiI, hiS]
  · obtain ⟨y', rfl⟩ := exists_inclusion_eq_of_eventually R A hS
      (eventually_principal.mpr fun i hiS ↦ by simpa [C, hiS] using (hy i).2)
    have hyW : (y' : Π i, R i) ∈ W := hIu fun i hiI ↦ by
      simpa [C, Finset.mem_coe.mp hiI, inclusion_apply] using (hy i).1
    have hyV : y' ∈ inclusion R A hS ⁻¹' U := by rw [← hWx]; exact hyW
    exact hyV

/-- When `A i` is open for cofinitely many `i`, the open boxes `box C` around `x` with
`C i = A i` cofinitely form a basis of the neighbourhood filter `𝓝 x` in `Πʳ i, [R i, A i]`. -/
theorem hasBasis_nhds_open_box (hA : ∀ᶠ i in cofinite, IsOpen (A i)) (x : Πʳ i, [R i, A i]) :
    (𝓝 x).HasBasis
      (fun C : ∀ i, Set (R i) ↦ (∀ i, x i ∈ C i) ∧ (∀ i, IsOpen (C i)) ∧
        ∀ᶠ i in cofinite, C i = A i)
      box := by
  refine (nhds_basis_opens x).to_hasBasis' ?_ ?_
  · rintro U ⟨hxU, hU⟩
    obtain ⟨C, hxC, hC, hCA, hCU⟩ := exists_open_box_subset_of_isOpen hA hxU hU
    exact ⟨C, ⟨hxC, hC, hCA⟩, hCU⟩
  · rintro C ⟨hxC, hC, hCA⟩
    exact (isOpen_box_of_eventually_eq hC hCA).mem_nhds hxC

/-- When `A i` is open for cofinitely many `i`, `openBoxes R A` is a topological basis of
`Πʳ i, [R i, A i]`. -/
theorem isTopologicalBasis_openBoxes (hA : ∀ᶠ i in cofinite, IsOpen (A i)) :
    TopologicalSpace.IsTopologicalBasis (openBoxes R A) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    (fun _ hs ↦ isOpen_of_mem_openBoxes hs) fun x U hxU hU ↦ ?_
  obtain ⟨C, hxC, hC, hCA, hCU⟩ := exists_open_box_subset_of_isOpen hA hxU hU
  exact ⟨box C, box_mem_openBoxes hC hCA, hxC, hCU⟩

end Topology

end RestrictedProduct
