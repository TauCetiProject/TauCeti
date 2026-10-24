/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Refinement
public import TauCeti.Combinatorics.Hypergraph.Polyad.Subpolyad
import Mathlib.Data.Fintype.BigOperators

/-!
# Refinement along subpolyad witnesses

A finite family of subpolyads can be resolved by refining only the pair palette: record
membership in each of its three selected pair graphs, in both orientations. The original
vertex partition and pair colors are retained. Every selected subpolyad support then becomes
an exact union of refined polyad supports, rather than merely being approximated by such a union.
The same holds simultaneously for unions of the selected supports.

This is the combinatorial refinement step in the hypergraph energy-increment argument: the
subpolyads witnessing failure of top regularity must be unions of atoms of the new skeleton.
For `m` selected subpolyads the new palette has `card κ * 2^(6*m)` colors, independently of the
number of host vertices. The construction also works for overlapping or repeated vertex cells
and for directed pair graphs.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the refinement along irregularity witnesses.
-/

public section

open Finset

namespace TauCeti.PairSkeleton3

universe u v w

variable {κ : Type u} {V : Type v} {ι : Type w} [Fintype V] [DecidableEq V] (S : PairSkeleton3 κ V)
  (P : ι → Polyad3 S) (Q : ∀ i, Subpolyad3 (P i))

/-- Refine a lower skeleton to distinguish the three pair graphs of every selected subpolyad,
in both orientations. The test index `(i, 0)`, `(i, 1)`, `(i, 2)` denotes respectively the
zero-one, zero-two, and one-two pair graph of `Q i`. -/
noncomputable def refineSubpolyads :
    PairSkeleton3 (κ × ((ι × Fin 3) → Bool) × ((ι × Fin 3) → Bool)) V :=
  S.refinePairSets fun a ↦ ![(Q a.1).pair₀₁, (Q a.1).pair₀₂, (Q a.1).pair₁₂] a.2

/-- The refined skeleton records the three selected pair graphs of each subpolyad. -/
theorem refineSubpolyads_def : S.refineSubpolyads P Q =
    S.refinePairSets (fun a ↦ ![(Q a.1).pair₀₁, (Q a.1).pair₀₂, (Q a.1).pair₁₂] a.2) := (rfl)

/-- Refining along subpolyads preserves the vertex partition, hence also its equitability. -/
@[simp]
theorem refineSubpolyads_vertexPart :
    (S.refineSubpolyads P Q).vertexPart = S.vertexPart := by
  rw [refineSubpolyads_def, refinePairSets_vertexPart]

/-- The original pair color is the first coordinate of the refined one. -/
@[simp]
theorem refineSubpolyads_color_fst (p : {p : V × V // p.1 ≠ p.2}) :
    ((S.refineSubpolyads P Q).pairColors.color p).1 = S.pairColors.color p := by
  rw [refineSubpolyads_def, refinePairSets_color_fst]

/-- Each selected subpolyad has constant membership on every refined polyad. -/
theorem mem_support_iff_of_refineSubpolyads_eq
    {x y : {x : Fin 3 → V // Function.Injective x}}
    (h : Polyad3.ofTriple (S.refineSubpolyads P Q) x =
      Polyad3.ofTriple (S.refineSubpolyads P Q) y) (i : ι) :
    x ∈ (Q i).support ↔ y ∈ (Q i).support := by
  have h₀₁ := congrArg Polyad3.color₀₁ h
  have h₀₂ := congrArg Polyad3.color₀₂ h
  have h₁₂ := congrArg Polyad3.color₁₂ h
  simp only [Polyad3.ofTriple_color₀₁, Polyad3.ofTriple_color₀₂,
    Polyad3.ofTriple_color₁₂, refineSubpolyads_def] at h₀₁ h₀₂ h₁₂
  have e₀₁ := S.mem_test_iff_of_refinePairSets_color_eq _ h₀₁ (i, 0)
  have e₀₂ := S.mem_test_iff_of_refinePairSets_color_eq _ h₀₂ (i, 1)
  have e₁₂ := S.mem_test_iff_of_refinePairSets_color_eq _ h₁₂ (i, 2)
  simpa only [Subpolyad3.mem_support_iff_coordPair_mem, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] using and_congr e₀₁ (and_congr e₀₂ e₁₂)

open Classical in
/-- A selected subpolyad support is exactly the disjoint union of the refined polyads met by
its triples. Distinct polyads have disjoint supports, including when vertex cells repeat. -/
theorem support_eq_biUnion_refineSubpolyads (i : ι) :
    (Q i).support = ((Q i).support.image (Polyad3.ofTriple (S.refineSubpolyads P Q))).biUnion
      Polyad3.support := by
  classical
  ext x
  constructor
  · intro hx
    exact mem_biUnion.2 ⟨_, mem_image_of_mem _ hx, Polyad3.mem_support_ofTriple x⟩
  · intro hx
    obtain ⟨R, hR, hxR⟩ := mem_biUnion.1 hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hR
    exact (S.mem_support_iff_of_refineSubpolyads_eq P Q
      (Polyad3.mem_support_iff_eq_ofTriple.1 hxR).symm i).2 hy

open Classical in
/-- Any union of selected subpolyad supports is a union of refined polyads, using the same
single refinement for the entire family. -/
theorem biUnion_support_eq_biUnion_refineSubpolyads (I : Finset ι) :
    I.biUnion (fun i ↦ (Q i).support) =
      ((I.biUnion fun i ↦ (Q i).support).image
        (Polyad3.ofTriple (S.refineSubpolyads P Q))).biUnion Polyad3.support := by
  classical
  rw [Finset.biUnion_image, Finset.biUnion_biUnion]
  simp_rw [← S.support_eq_biUnion_refineSubpolyads P Q]

open Classical in
/-- Resolve a finite family of subpolyads by a bounded coherent refinement. The new pair
palette projects to the old one, its reversal respects that projection, and each selected
support is exactly a union of new polyad supports. Neither the vertex partition nor the
palette bound depends on the sizes of the selected supports. -/
theorem exists_bounded_refinement_subpolyads [Fintype κ] [Fintype ι] :
    ∃ (κ' : Type (max u w)) (_ : Fintype κ') (T : PairSkeleton3 κ' V) (π : κ' → κ),
      Fintype.card κ' ≤ Fintype.card κ * 2 ^ (6 * Fintype.card ι) ∧
      T.vertexPart = S.vertexPart ∧
      (∀ p, π (T.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (T.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      ∀ i, ∃ A : Finset (Polyad3 T), (Q i).support = A.biUnion Polyad3.support := by
  classical
  refine ⟨κ × ((ι × Fin 3) → Bool) × ((ι × Fin 3) → Bool), inferInstance,
    S.refineSubpolyads P Q, Prod.fst, ?_, S.refineSubpolyads_vertexPart P Q,
    S.refineSubpolyads_color_fst P Q, ?_, fun i ↦ ⟨_, S.support_eq_biUnion_refineSubpolyads P Q i⟩⟩
  · simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      ← pow_add]
    exact le_of_eq (congrArg (fun n ↦ Fintype.card κ * 2 ^ n) (by omega))
  · intro c
    rw [refineSubpolyads_def, refinePairSets_pairColors, PairColorSystem.refine_rev]

end TauCeti.PairSkeleton3
